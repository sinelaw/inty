// Inty playground.
//
// The web app runs the same Analysis the editor LSP uses (compiled to
// WASM from inty-lsp). We feed it the source on every change, then
// render inlay hints and hover tooltips from its responses.

import init, { Analysis } from './pkg/inty.js';
import { EXAMPLES, findExample, DEFAULT_EXAMPLE_ID } from './examples.js';

let wasmReady = false;
let inputEditor = null;
let analysis = null;
let charToByteTable = null;

let checkTimeout = null;
const DEBOUNCE_MS = 200;

let inlayBookmarks = [];
let errorMarks = [];
let lastHoverKey = null;
let hintsEnabled = localStorage.getItem('inty.hints') !== 'off';

// Which example is currently loaded — null when the editor holds a
// custom snippet (after edits or when loaded from a shared #hash).
let activeExampleId = null;
// Suppress URL rewriting during programmatic setValue.
let suppressDirty = false;

const SIDEBAR_KEY = 'inty.sidebar';
const ONBOARDED_KEY = 'inty.onboarded';
const MOBILE_BREAKPOINT = 768;

// ---- URL hash sync ----------------------------------------------------

function encodeToHash(code) {
    try {
        const bytes = new TextEncoder().encode(code);
        const binary = String.fromCharCode(...bytes);
        return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
    } catch (_) {
        return null;
    }
}

function decodeFromHash(hash) {
    try {
        let base64 = hash.replace(/-/g, '+').replace(/_/g, '/');
        while (base64.length % 4) base64 += '=';
        const binary = atob(base64);
        const bytes = new Uint8Array(binary.length);
        for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
        return new TextDecoder().decode(bytes);
    } catch (_) {
        return null;
    }
}

function setUrlHash(code) {
    const enc = encodeToHash(code);
    if (!enc) return;
    // A shared snippet wins over any ?ex= param — clear it.
    const url = new URL(window.location.href);
    url.searchParams.delete('ex');
    url.hash = '#' + enc;
    history.replaceState(null, '', url.toString());
}

function getCodeFromUrl() {
    const hash = window.location.hash.slice(1);
    return hash ? decodeFromHash(hash) : null;
}

function getExampleIdFromUrl() {
    const params = new URLSearchParams(window.location.search);
    return params.get('ex');
}

function setUrlExample(id) {
    const url = new URL(window.location.href);
    if (id) url.searchParams.set('ex', id);
    else url.searchParams.delete('ex');
    url.hash = '';
    history.replaceState(null, '', url.toString());
}

// ---- UTF-16 (JS) <-> UTF-8 (Rust) offset mapping ---------------------
//
// CodeMirror works in UTF-16 code units; the Rust side returns and
// expects UTF-8 byte offsets. Build one map per source snapshot.

function buildOffsetTable(source) {
    const len = source.length;
    const c2b = new Int32Array(len + 1);
    let byte = 0;
    for (let i = 0; i < len; i++) {
        c2b[i] = byte;
        const code = source.charCodeAt(i);
        if (code < 0x80) byte += 1;
        else if (code < 0x800) byte += 2;
        else if (code >= 0xd800 && code <= 0xdbff) byte += 4; // high surrogate
        else if (code >= 0xdc00 && code <= 0xdfff) byte += 0; // low surrogate (counted with high)
        else byte += 3;
    }
    c2b[len] = byte;
    return c2b;
}

function charToByte(charOffset) {
    if (!charToByteTable) return charOffset;
    const idx = Math.max(0, Math.min(charOffset, charToByteTable.length - 1));
    return charToByteTable[idx];
}

function byteToChar(byteOffset) {
    if (!charToByteTable) return byteOffset;
    let lo = 0;
    let hi = charToByteTable.length - 1;
    while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (charToByteTable[mid] < byteOffset) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

// ---- DOM -------------------------------------------------------------

const statusEl = document.getElementById('status');
const errorPanel = document.getElementById('error-panel');
const errorContent = document.getElementById('error-content');
const errorSummary = document.getElementById('error-summary');
const closeErrorsBtn = document.getElementById('close-errors');
const tooltipEl = document.getElementById('hover-tooltip');
const shareBtn = document.getElementById('share-btn');
const hintsBtn = document.getElementById('hints-btn');
const sidebarEl = document.getElementById('sidebar');
const sidebarToggleBtn = document.getElementById('sidebar-toggle');
const sidebarScrim = document.getElementById('sidebar-scrim');
const treeEl = document.getElementById('tree');
const exampleStatusDot = document.getElementById('example-status');
const exampleBlurbEl = document.getElementById('example-blurb');

// ---- Init ------------------------------------------------------------

async function initialize() {
    renderTree();
    setupSidebar();

    try {
        await init();
        wasmReady = true;
        statusEl.textContent = 'ready';
        statusEl.classList.add('ready');

        inputEditor = CodeMirror.fromTextArea(
            document.getElementById('input-editor'),
            {
                mode: 'javascript',
                theme: 'dracula',
                lineNumbers: true,
                matchBrackets: true,
                autoCloseBrackets: true,
                indentUnit: 4,
                tabSize: 4,
                indentWithTabs: false,
            },
        );

        // Resolve initial content. Precedence: shared snippet (#hash)
        // > example query (?ex=) > default example.
        const urlCode = getCodeFromUrl();
        if (urlCode) {
            loadCustomCode(urlCode);
        } else {
            const id = getExampleIdFromUrl();
            const found = id ? findExample(id) : null;
            const target = found || findExample(DEFAULT_EXAMPLE_ID);
            if (target) {
                loadExample(target.item.id, { updateUrl: !!id });
            } else {
                loadCustomCode('');
            }
        }

        inputEditor.on('change', onEditorChange);

        setupHover();
        runCheck();
        // After the first render settles, run the onboarding tour
        // exactly once per visitor — see playOnboarding().
        requestAnimationFrame(() => requestAnimationFrame(maybePlayOnboarding));
    } catch (e) {
        console.error('Failed to initialize WASM:', e);
        statusEl.textContent = 'failed';
        statusEl.classList.add('error');
    }
}

// ---- Editor content swapping ----------------------------------------

function setEditorContent(code) {
    if (!inputEditor) return;
    suppressDirty = true;
    inputEditor.setValue(code);
    // Drop the synthetic "load" edit so the first Ctrl+Z doesn't
    // wipe the editor back to empty.
    inputEditor.clearHistory();
    suppressDirty = false;
}

function loadExample(id, { updateUrl = true } = {}) {
    const found = findExample(id);
    if (!found) return;
    activeExampleId = id;
    setEditorContent(found.item.code);
    if (updateUrl) setUrlExample(id);
    updateActiveTreeItem();
    updateExampleStatus(found);
    runCheck();
    // Auto-close the overlay sidebar after picking, on mobile.
    if (window.innerWidth <= MOBILE_BREAKPOINT) setSidebarOpen(false);
}

function loadCustomCode(code) {
    activeExampleId = null;
    setEditorContent(code);
    updateActiveTreeItem();
    updateExampleStatus(null);
}

function onEditorChange() {
    if (suppressDirty) {
        scheduleCheck();
        return;
    }
    // A real user edit. If we were displaying a named example, the
    // editor is now off-script — drop the link but keep the example
    // highlighted as "based on".
    scheduleCheck();
}

function scheduleCheck() {
    clearTimeout(checkTimeout);
    checkTimeout = setTimeout(runCheck, DEBOUNCE_MS);
}

function runCheck() {
    if (!wasmReady) return;
    const source = inputEditor.getValue();

    if (analysis) {
        analysis.free();
        analysis = null;
    }
    charToByteTable = buildOffsetTable(source);

    if (!source.trim()) {
        clearInlayHints();
        clearEditorErrors();
        hideErrors();
        return;
    }

    analysis = new Analysis(source);
    const errors = analysis.errors();

    if (errors.length === 0) {
        renderInlayHints(source);
        clearEditorErrors();
        hideErrors();
    } else {
        clearInlayHints();
        showErrors(errors, source);
    }
}

// ---- Inlay hints -----------------------------------------------------

function renderInlayHints(source) {
    clearInlayHints();
    if (!analysis || !hintsEnabled) return;

    const totalBytes = charToByte(source.length);
    const hints = analysis.inlay_hints(0, totalBytes);

    for (const hint of hints) {
        const charOffset = byteToChar(hint.after_byte);
        const pos = inputEditor.posFromIndex(charOffset);
        const widget = document.createElement('span');
        widget.className = 'inlay-hint';
        // `label` may include a leading space (CLI-friendly) — the
        // pill chrome provides its own padding so strip it here.
        widget.textContent = hint.label.replace(/^\s+/, '');
        const bm = inputEditor.setBookmark(pos, {
            widget,
            insertLeft: false,
            handleMouseEvents: false,
        });
        inlayBookmarks.push(bm);
    }
}

function clearInlayHints() {
    inlayBookmarks.forEach((b) => b.clear());
    inlayBookmarks = [];
}

// ---- Hover -----------------------------------------------------------

function setupHover() {
    const wrapper = inputEditor.getWrapperElement();
    wrapper.addEventListener('mousemove', onHoverMove);
    wrapper.addEventListener('mouseleave', hideHover);
    document.addEventListener('scroll', hideHover, true);
}

function onHoverMove(e) {
    if (!analysis) {
        hideHover();
        return;
    }
    const pos = inputEditor.coordsChar(
        { left: e.clientX, top: e.clientY },
        'window',
    );
    const charOffset = inputEditor.indexFromPos(pos);
    const byteOffset = charToByte(charOffset);
    const hover = analysis.hover(byteOffset);
    if (!hover) {
        hideHover();
        return;
    }

    const key = `${hover.start}:${hover.end}:${hover.type_str}`;
    if (key !== lastHoverKey) {
        tooltipEl.innerHTML =
            `<span class="tooltip-name">${escapeHtml(hover.name)}</span>` +
            `<span class="tooltip-type">: ${escapeHtml(hover.type_str)}</span>`;
        lastHoverKey = key;
    }
    tooltipEl.classList.add('visible');

    let left = e.clientX + 14;
    let top = e.clientY + 18;
    const w = tooltipEl.offsetWidth;
    const h = tooltipEl.offsetHeight;
    if (left + w > window.innerWidth - 12) left = window.innerWidth - w - 12;
    if (top + h > window.innerHeight - 12) top = e.clientY - h - 10;
    tooltipEl.style.left = left + 'px';
    tooltipEl.style.top = top + 'px';
}

function hideHover() {
    tooltipEl.classList.remove('visible');
    lastHoverKey = null;
}

// ---- Errors ----------------------------------------------------------

function showErrors(errors, source) {
    errorContent.innerHTML = '';
    errorSummary.textContent = `${errors.length} error${errors.length === 1 ? '' : 's'}`;

    errors.forEach((error) => {
        const item = document.createElement('div');
        item.className = 'error-item';
        const startChar = byteToChar(error.start);
        const loc = offsetToLineCol(source, startChar);
        item.innerHTML =
            `<div class="message">${escapeHtml(error.message)}</div>` +
            `<div class="location">Line ${loc.line}, Column ${loc.column}</div>`;
        item.addEventListener('click', () => {
            inputEditor.setCursor({ line: loc.line - 1, ch: loc.column - 1 });
            inputEditor.focus();
        });
        errorContent.appendChild(item);
    });

    errorPanel.classList.add('visible');
    markEditorErrors(errors);
}

function hideErrors() {
    errorPanel.classList.remove('visible');
}

function offsetToLineCol(source, charOffset) {
    let line = 1;
    let column = 1;
    for (let i = 0; i < charOffset && i < source.length; i++) {
        if (source[i] === '\n') {
            line++;
            column = 1;
        } else {
            column++;
        }
    }
    return { line, column };
}

function markEditorErrors(errors) {
    clearEditorErrors();
    errors.forEach((error) => {
        const startPos = inputEditor.posFromIndex(byteToChar(error.start));
        const endPos = inputEditor.posFromIndex(byteToChar(error.end));
        errorMarks.push(
            inputEditor.markText(startPos, endPos, { className: 'error-underline' }),
        );
    });
}

function clearEditorErrors() {
    errorMarks.forEach((m) => m.clear());
    errorMarks = [];
}

// ---- Misc ------------------------------------------------------------

function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

closeErrorsBtn.addEventListener('click', hideErrors);

function reflectHintsBtn() {
    hintsBtn.classList.toggle('off', !hintsEnabled);
    hintsBtn.textContent = hintsEnabled ? 'Hints on' : 'Hints off';
}

hintsBtn.addEventListener('click', () => {
    hintsEnabled = !hintsEnabled;
    localStorage.setItem('inty.hints', hintsEnabled ? 'on' : 'off');
    reflectHintsBtn();
    if (hintsEnabled) {
        renderInlayHints(inputEditor.getValue());
    } else {
        clearInlayHints();
    }
});
reflectHintsBtn();

shareBtn.addEventListener('click', async () => {
    const code = inputEditor.getValue();
    setUrlHash(code);
    let label = 'Link copied';
    try {
        await navigator.clipboard.writeText(window.location.href);
    } catch (_) {
        label = 'Link in URL';
    }
    flashShareLabel(label);
});

function flashShareLabel(text) {
    const original = shareBtn.dataset.label || shareBtn.textContent;
    shareBtn.dataset.label = original;
    shareBtn.textContent = text;
    shareBtn.classList.add('copied');
    clearTimeout(flashShareLabel._t);
    flashShareLabel._t = setTimeout(() => {
        shareBtn.textContent = original;
        shareBtn.classList.remove('copied');
    }, 1600);
}

document.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        runCheck();
    }
});

window.addEventListener('hashchange', () => {
    const urlCode = getCodeFromUrl();
    if (urlCode && inputEditor && urlCode !== inputEditor.getValue()) {
        loadCustomCode(urlCode);
        runCheck();
    }
});

window.addEventListener('popstate', () => {
    const id = getExampleIdFromUrl();
    if (id && id !== activeExampleId) {
        loadExample(id, { updateUrl: false });
    }
});

// ---- Sidebar / examples ---------------------------------------------

function renderTree() {
    if (!treeEl) return;
    const openSections = readOpenSections();
    treeEl.innerHTML = '';

    EXAMPLES.forEach((section, idx) => {
        const sectionEl = document.createElement('div');
        sectionEl.className = 'tree-section';
        sectionEl.dataset.sectionId = section.id;
        // Open by default; remember closed state across reloads.
        if (openSections[section.id] !== false) {
            sectionEl.classList.add('open');
        }

        const folderGlyph = section.id === 'ts-misses' ? '⚠' : '▦';
        const header = document.createElement('button');
        header.className = 'tree-section-header';
        header.type = 'button';
        header.setAttribute('aria-expanded', 'true');
        header.innerHTML =
            `<span class="tree-chevron" aria-hidden="true"></span>` +
            `<span class="tree-section-icon" aria-hidden="true">${folderGlyph}</span>` +
            `<span class="tree-section-label">${escapeHtml(section.label)}</span>` +
            `<span class="tree-section-count">${section.items.length}</span>`;

        header.addEventListener('click', () => {
            sectionEl.classList.toggle('open');
            const open = sectionEl.classList.contains('open');
            header.setAttribute('aria-expanded', String(open));
            writeOpenSection(section.id, open);
        });
        sectionEl.appendChild(header);

        const children = document.createElement('div');
        children.className = 'tree-children';
        section.items.forEach((item) => {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.className = 'tree-item';
            btn.dataset.exampleId = item.id;
            btn.title = item.blurb || item.label;
            btn.innerHTML =
                `<svg class="tree-item-icon" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true">` +
                `<path d="M3 2.5h6.5L13 6v7.5H3z"/><path d="M9.25 2.5V6H13"/>` +
                `</svg>` +
                `<span class="tree-item-label">${escapeHtml(item.label)}</span>`;
            btn.addEventListener('click', () => loadExample(item.id));
            children.appendChild(btn);
        });
        sectionEl.appendChild(children);
        treeEl.appendChild(sectionEl);
    });
}

function readOpenSections() {
    try {
        return JSON.parse(localStorage.getItem('inty.sections') || '{}') || {};
    } catch {
        return {};
    }
}

function writeOpenSection(id, open) {
    const s = readOpenSections();
    s[id] = open;
    try { localStorage.setItem('inty.sections', JSON.stringify(s)); } catch {}
}

function updateActiveTreeItem() {
    if (!treeEl) return;
    treeEl.querySelectorAll('.tree-item').forEach((el) => {
        const active = el.dataset.exampleId === activeExampleId;
        el.classList.toggle('active', active);
        if (active) {
            // Expand the section containing this item.
            const section = el.closest('.tree-section');
            if (section && !section.classList.contains('open')) {
                section.classList.add('open');
                const header = section.querySelector('.tree-section-header');
                if (header) header.setAttribute('aria-expanded', 'true');
            }
            // Scroll into view if needed.
            el.scrollIntoView({ block: 'nearest' });
        }
    });
}

function updateExampleStatus(found) {
    if (!exampleBlurbEl || !exampleStatusDot) return;
    if (found) {
        exampleStatusDot.classList.add('active');
        exampleBlurbEl.textContent = found.item.blurb || found.item.label;
        exampleBlurbEl.title = found.item.blurb || found.item.label;
    } else {
        exampleStatusDot.classList.remove('active');
        exampleBlurbEl.textContent = 'Custom snippet';
        exampleBlurbEl.title = 'Editing a custom snippet';
    }
}

function setupSidebar() {
    if (!sidebarToggleBtn || !sidebarEl) return;

    const stored = localStorage.getItem(SIDEBAR_KEY);
    // Default: open on desktop, closed on mobile.
    const startOpen = stored == null
        ? window.innerWidth > MOBILE_BREAKPOINT
        : stored === 'open';
    setSidebarOpen(startOpen, { persist: false });

    sidebarToggleBtn.addEventListener('click', () => {
        const open = sidebarEl.classList.contains('collapsed');
        setSidebarOpen(open);
    });
    if (sidebarScrim) {
        sidebarScrim.addEventListener('click', () => setSidebarOpen(false));
    }
}

function setSidebarOpen(open, { persist = true } = {}) {
    if (!sidebarEl) return;
    sidebarEl.classList.toggle('collapsed', !open);
    sidebarToggleBtn.setAttribute('aria-pressed', String(open));
    sidebarToggleBtn.classList.toggle('off', !open);
    const mobile = window.innerWidth <= MOBILE_BREAKPOINT;
    if (sidebarScrim) {
        if (mobile && open) {
            sidebarScrim.hidden = false;
            requestAnimationFrame(() => sidebarScrim.classList.add('visible'));
        } else {
            sidebarScrim.classList.remove('visible');
            setTimeout(() => { if (!sidebarScrim.classList.contains('visible')) sidebarScrim.hidden = true; }, 200);
        }
    }
    if (persist) {
        try { localStorage.setItem(SIDEBAR_KEY, open ? 'open' : 'closed'); } catch {}
    }
    // CodeMirror needs a kick so its viewport recalculates after the
    // editor pane width changes.
    if (inputEditor) {
        setTimeout(() => inputEditor.refresh(), 240);
    }
}

// ---- Onboarding tour ------------------------------------------------
//
// First-time visitors get a guided demo: a fake cursor drifts to the
// "Hints on" toggle and clicks it twice, so they watch the inferred
// types disappear (revealing plain JavaScript) and then reappear.
// The point — the types are not in the code; inty added them.

function maybePlayOnboarding() {
    // Skip when the visitor arrived via a deep link — they came to see
    // *that* snippet/example, not a generic tour.
    if (window.location.hash || window.location.search) return;

    try {
        if (localStorage.getItem(ONBOARDED_KEY) === 'yes') return;
    } catch (_) { /* private mode — still show */ }

    // Skip on very small screens; the toggle and cursor compete for
    // space and the demo lands awkwardly.
    if (window.innerWidth < 480) {
        try { localStorage.setItem(ONBOARDED_KEY, 'yes'); } catch (_) {}
        return;
    }
    if (!hintsBtn || !hintsEnabled) return;

    playOnboarding();
}

function playOnboarding() {
    try { localStorage.setItem(ONBOARDED_KEY, 'yes'); } catch (_) {}

    const cursor = document.getElementById('demo-cursor');
    const captionEl = document.getElementById('demo-cursor-caption');
    if (!cursor || !captionEl) return;

    let aborted = false;
    const cleanup = () => {
        aborted = true;
        cursor.classList.remove('visible', 'clicking', 'flip-caption');
        captionEl.classList.remove('visible');
        cursor.removeEventListener('transitionend', noop);
        document.removeEventListener('keydown', abort, true);
        document.removeEventListener('mousedown', abort, true);
        document.removeEventListener('touchstart', abort, true);
    };
    const abort = () => cleanup();
    function noop() {}
    document.addEventListener('keydown', abort, true);
    document.addEventListener('mousedown', abort, true);
    document.addEventListener('touchstart', abort, true);

    const setCaption = (html) => {
        captionEl.innerHTML = html;
    };
    const moveTo = (x, y) => {
        cursor.style.transform = `translate(${x}px, ${y}px)`;
        // Flip caption to the cursor's other side near the right edge.
        cursor.classList.toggle('flip-caption', x > window.innerWidth - 260);
    };
    const click = () => {
        cursor.classList.add('clicking');
        setTimeout(() => cursor.classList.remove('clicking'), 560);
    };

    const target = hintsBtn.getBoundingClientRect();
    const targetX = target.left + target.width / 2 - 8;
    const targetY = target.top + target.height / 2 - 4;

    // Start a bit inside the editor so the path crosses the code.
    const startX = Math.min(window.innerWidth * 0.45, targetX - 280);
    const startY = Math.min(window.innerHeight * 0.55, targetY + 200);

    moveTo(startX, startY);
    setCaption(
        '<span class="muted">These</span> ' +
        '<span class="accent">: Number</span>, ' +
        '<span class="accent">: String</span> ' +
        '<span class="muted">aren\'t in your code —</span>'
    );

    // Tiny defer to let the initial transform paint before animating.
    setTimeout(() => {
        if (aborted) return;
        cursor.classList.add('visible');
        captionEl.classList.add('visible');

        // Move to the Hints button.
        setTimeout(() => {
            if (aborted) return;
            moveTo(targetX, targetY);

            setTimeout(() => {
                if (aborted) return;
                // First click — hints OFF, plain JS revealed.
                click();
                hintsBtn.click();
                setCaption(
                    '<span class="muted">…</span> ' +
                    '<span class="accent">inty added them.</span>'
                );

                setTimeout(() => {
                    if (aborted) return;
                    // Second click — hints back ON.
                    click();
                    hintsBtn.click();
                    setCaption(
                        '<span class="muted">Hover any binding to inspect its type.</span>'
                    );

                    setTimeout(() => {
                        if (aborted) return;
                        captionEl.classList.remove('visible');
                        // Drift off-screen on the right.
                        moveTo(targetX + 80, targetY + 120);
                        cursor.classList.remove('visible');
                        setTimeout(cleanup, 500);
                    }, 2200);
                }, 1700);
            }, 950);
        }, 80);
    }, 30);
}

initialize();
