// Headless-browser smoke test for the deployed playground.
//
// Loads the page, waits for WASM to come up, then for every entry in
// examples/playground/manifest.json:
//   1. clicks the sidebar button
//   2. waits for the editor content to swap to that example's source
//   3. waits for the type checker to run (debounced)
//   4. asserts the error-panel visibility matches the manifest's `expect`
//
// Also exercises one marker-enabled example via the URL #hash channel
// to prove that uncommenting the trigger line does produce errors in
// the live playground, not just in the Rust test.

import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const { chromium } = require('/opt/node22/lib/node_modules/playwright');

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '..');
const PLAYGROUND_DIR = resolve(ROOT, 'examples', 'playground');
const MANIFEST = JSON.parse(
  readFileSync(resolve(PLAYGROUND_DIR, 'manifest.json'), 'utf8'),
);

const BASE_URL = process.env.PLAYGROUND_URL || 'http://localhost:8080';
const TIMEOUT = 15_000;

function encodeHash(code) {
  // Matches encodeToHash in web/app.js.
  const b64 = Buffer.from(code, 'utf8').toString('base64');
  return b64.replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function enableMarkers(src) {
  // Mirrors crates/inty/tests/web_examples.rs::enable_markers — used
  // here to build the "triggered" variant of an example for the URL
  // hash. Returns null if the file has no markers.
  const lines = src.split('\n');
  const out = [];
  let inBlock = false;
  let found = false;
  for (const raw of lines) {
    const trimmed = raw.trim();
    if (trimmed.startsWith('//') && trimmed.includes('error-begin')) {
      inBlock = true; found = true; continue;
    }
    if (trimmed.startsWith('//') && trimmed.includes('error-end')) {
      inBlock = false; continue;
    }
    if (inBlock) { out.push(uncomment(raw)); continue; }
    if (trimmed.startsWith('//') && trimmed.replace(/\s+$/, '').endsWith('// error!')) {
      found = true; out.push(uncomment(raw)); continue;
    }
    out.push(raw);
  }
  return found ? out.join('\n') : null;
}

function uncomment(line) {
  const m = line.match(/^(\s*)\/\/ ?(.*)$/);
  return m ? m[1] + m[2] : line;
}

async function readExampleSource(sectionId, itemId) {
  const path = resolve(PLAYGROUND_DIR, sectionId, `${itemId}.js`);
  return readFileSync(path, 'utf8');
}

async function waitForCheck(page) {
  // runCheck() runs synchronously after setEditorContent(), but it's
  // debounced behind a 200ms timer on edit. Settle a bit longer to
  // catch the post-load run and any rendering.
  await page.waitForTimeout(450);
}

async function statusReady(page) {
  await page.waitForFunction(
    () => document.getElementById('status')?.classList.contains('ready'),
    null,
    { timeout: TIMEOUT },
  );
}

async function errorPanelVisible(page) {
  return page.evaluate(() =>
    document.getElementById('error-panel')?.classList.contains('visible') ?? false,
  );
}

async function errorSummary(page) {
  return page.evaluate(() => {
    const el = document.getElementById('error-summary');
    return el ? el.textContent : null;
  });
}

async function activeExampleLabel(page) {
  return page.evaluate(() => {
    const el = document.querySelector('.tree-item.active .tree-item-label');
    return el ? el.textContent : null;
  });
}

async function main() {
  const failures = [];

  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext();

  // The deployed page pulls CodeMirror from cdnjs.cloudflare.com,
  // which our sandbox blocks. Intercept the well-known URLs and
  // serve local copies extracted from the npm tarball.
  const CDN_LOCAL = process.env.CDN_LOCAL || '/tmp/inty-test-web/codemirror';
  const cdnMap = {
    'codemirror.min.js':         `${CDN_LOCAL}/codemirror.min.js`,
    'codemirror.min.css':        `${CDN_LOCAL}/codemirror.min.css`,
    'mode/javascript/javascript.min.js': `${CDN_LOCAL}/javascript.min.js`,
    'addon/edit/matchbrackets.min.js':   `${CDN_LOCAL}/matchbrackets.min.js`,
    'addon/edit/closebrackets.min.js':   `${CDN_LOCAL}/closebrackets.min.js`,
    'theme/dracula.min.css':     `${CDN_LOCAL}/dracula.min.css`,
  };
  await context.route('https://cdnjs.cloudflare.com/**', async (route, request) => {
    const url = request.url();
    for (const [needle, file] of Object.entries(cdnMap)) {
      if (url.endsWith(needle)) {
        const body = readFileSync(file);
        const contentType = file.endsWith('.css') ? 'text/css' : 'application/javascript';
        return route.fulfill({ status: 200, contentType, body });
      }
    }
    return route.abort();
  });
  // Block Cloudflare Analytics — non-essential and also unreachable.
  await context.route('https://static.cloudflareinsights.com/**', (route) => route.abort());

  const page = await context.newPage();

  page.on('pageerror', (err) => {
    failures.push(`page error: ${err.message}`);
  });
  page.on('console', (msg) => {
    if (msg.type() !== 'error') return;
    const text = msg.text();
    // Cloudflare Analytics is intentionally aborted by our route
    // handler — its console error is expected, not a regression.
    if (text.includes('Failed to load resource: net::ERR_FAILED')) return;
    failures.push(`console error: ${text}`);
  });

  await page.goto(BASE_URL, { waitUntil: 'domcontentloaded', timeout: TIMEOUT });
  await statusReady(page);
  console.log(`[ok] WASM ready at ${BASE_URL}`);

  // The page boots with the default example loaded — drain that.
  await waitForCheck(page);

  for (const section of MANIFEST.sections) {
    for (const item of section.items) {
      const selector = `button.tree-item[data-example-id="${item.id}"]`;
      await page.locator(selector).click();
      await waitForCheck(page);

      const label = await activeExampleLabel(page);
      if (label !== item.label) {
        failures.push(
          `${section.id}/${item.id}: active-item label is ${JSON.stringify(label)}, expected ${JSON.stringify(item.label)}`,
        );
      }

      const visible = await errorPanelVisible(page);
      const summary = await errorSummary(page);
      const want = item.expect; // "ok" | "error"
      const got = visible ? 'error' : 'ok';
      if (want !== got) {
        const firstError = await page.evaluate(() => {
          const el = document.querySelector('#error-content .message');
          return el ? el.textContent : null;
        });
        failures.push(
          `${section.id}/${item.id}: expect=${want}, panel says ${got} (summary=${summary}; first=${JSON.stringify(firstError)})`,
        );
      } else {
        console.log(`[ok] ${section.id}/${item.id}: ${got}${got === 'error' ? ` (${summary})` : ''}`);
      }
    }
  }

  // Marker-enabled probe via URL hash. Pick the overloading example
  // (features/overloading) which passes as-written and errors with the
  // marker enabled. This proves end-to-end that the hash → editor →
  // analysis path agrees with the Rust test.
  const src = await readExampleSource('features', 'overloading');
  const enabled = enableMarkers(src);
  if (!enabled) {
    failures.push('marker probe: features/overloading has no markers — convention drift?');
  } else {
    const hash = encodeHash(enabled);
    await page.goto(`${BASE_URL}#${hash}`, { waitUntil: 'domcontentloaded', timeout: TIMEOUT });
    await statusReady(page);
    await waitForCheck(page);
    const visible = await errorPanelVisible(page);
    if (!visible) {
      failures.push('marker probe (features/overloading enabled): expected errors, panel hidden');
    } else {
      console.log(`[ok] marker probe (features/overloading): errors visible (${await errorSummary(page)})`);
    }
  }

  await browser.close();

  if (failures.length) {
    console.error(`\n${failures.length} failure(s):`);
    for (const f of failures) console.error(`  - ${f}`);
    process.exit(1);
  }
  console.log(`\nAll ${MANIFEST.sections.reduce((n, s) => n + s.items.length, 0)} examples agree with the manifest.`);
}

main().catch((err) => {
  console.error('fatal:', err);
  process.exit(1);
});
