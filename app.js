// Inty playground.
//
// The web app runs the same Analysis the editor LSP uses (compiled to
// WASM from inty-lsp). We feed it the source on every change, then
// render inlay hints and hover tooltips from its responses.

import init, { Analysis } from './pkg/inty.js';

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
    if (enc) history.replaceState(null, '', '#' + enc);
}

function getCodeFromUrl() {
    const hash = window.location.hash.slice(1);
    return hash ? decodeFromHash(hash) : null;
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

// ---- Example code ----------------------------------------------------

const EXAMPLE_CODE = `// Inty — full type inference for plain JavaScript.
// Hover any binding to see its inferred type.

// Overloaded \`+\` — works for any addable type
function add(x, y) { return x + y; }
var n = add(1, 2);

// Generics — id<a>(a) => a
function id(x) { return x; }
var a = id(42);
var b = id("hello");

// Structural typing — any object with a \`name\` field works
function getName(obj) { return obj.name; }
var person = getName({ name: "Alice", age: 30 });
var dog    = getName({ name: "Rover", breed: "Labrador" });

// Method chaining — builder-style \`this\`
var counter = {
    n: 0,
    inc: function() { this.n = this.n + 1; return this; }
};
var v = counter.inc().inc().n;

// Union types from branches
function tag(c) { return c ? 42 : "err"; }

// Tagged unions — narrowed by the discriminator
/** function area(s: {kind: "circle", r: Number}
                 | {kind: "square", s: Number}) => Number */
function area(shape) {
    if (shape.kind === "circle") { return shape.r; }
    else                         { return shape.s; }
}

// Try a type error:
// var bad = add("hello", 42);
`;

// ---- DOM -------------------------------------------------------------

const statusEl = document.getElementById('status');
const errorPanel = document.getElementById('error-panel');
const errorContent = document.getElementById('error-content');
const errorSummary = document.getElementById('error-summary');
const closeErrorsBtn = document.getElementById('close-errors');
const tooltipEl = document.getElementById('hover-tooltip');
const shareBtn = document.getElementById('share-btn');
const hintsBtn = document.getElementById('hints-btn');

// ---- Init ------------------------------------------------------------

async function initialize() {
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

        const urlCode = getCodeFromUrl();
        inputEditor.setValue(urlCode || EXAMPLE_CODE);
        // Drop the synthetic "load" edit so the first Ctrl+Z doesn't
        // wipe the editor back to empty.
        inputEditor.clearHistory();

        inputEditor.on('change', scheduleCheck);

        setupHover();
        runCheck();
    } catch (e) {
        console.error('Failed to initialize WASM:', e);
        statusEl.textContent = 'failed';
        statusEl.classList.add('error');
    }
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
        // `label` already includes its prefix (`: T` or `-> Ret`).
        widget.textContent = hint.label;
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
        inputEditor.setValue(urlCode);
        inputEditor.clearHistory();
        runCheck();
    }
});

initialize();
