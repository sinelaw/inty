// md2html: convert Markdown to HTML.
//
//   md2html [input.md | -] [-o output.html] [-s | --standalone]
//
// Reads a file (or stdin), writes HTML to stdout (or the -o file). With
// --standalone, wraps the result in a full HTML document titled after
// the first heading.
//
// Supported Markdown, roughly CommonMark / GitHub-flavoured:
// - blocks: ATX and setext headings, paragraphs, fenced code blocks
//   with an info string, block quotes, nested ordered and unordered
//   lists (tight and loose), thematic breaks, GFM tables with column
//   alignment;
// - inline: code spans, strong and emphasis (`*`/`_`), links, images,
//   autolinks, backslash escapes, hard line breaks, HTML escaping.
//
// Plain JavaScript: runs as-is under Node or Bun, and inty type-checks
// it and translates it into Go (`inty go md2html.js`) that produces
// byte-identical output.

import { readFileSync, writeFileSync } from "node:fs";
import process from "node:process";

// ---- characters -------------------------------------------------------------

function isBlankChar(c) {
  return c === 32 || c === 9;
}

function isDigit(c) {
  return c >= 48 && c <= 57;
}

function isAlnum(c) {
  return isDigit(c) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

// ASCII punctuation: the characters a backslash can escape.
function isPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}

function isBlank(line) {
  for (let i = 0; i < line.length; i++) {
    if (!isBlankChar(line.charCodeAt(i))) return false;
  }
  return true;
}

// Width of the leading whitespace (a tab counts as 4 columns).
function indentOf(line) {
  let n = 0;
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c === 32) n += 1;
    else if (c === 9) n += 4;
    else return n;
  }
  return n;
}

// `line` with `cols` columns of leading whitespace removed.
function dedent(line, cols) {
  let i = 0;
  let n = 0;
  while (i < line.length && n < cols) {
    const c = line.charCodeAt(i);
    if (c === 32) n += 1;
    else if (c === 9) n += 4;
    else break;
    i++;
  }
  return line.slice(i);
}

function escapeHtml(s) {
  let start = 0;
  let out = "";
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = "";
    if (c === 38) rep = "&amp;";
    else if (c === 60) rep = "&lt;";
    else if (c === 62) rep = "&gt;";
    else if (c === 34) rep = "&quot;";
    if (rep !== "") {
      out = out + s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  if (start === 0) return s;
  return out + s.slice(start);
}

// ---- inline ----------------------------------------------------------------

// The length of the run of backticks at `i`.
function backtickRun(s, i) {
  let run = 0;
  while (i + run < s.length && s.charCodeAt(i + run) === 96) run++;
  return run;
}

// The start of the backtick run that closes the code span opened by the
// `run` backticks at `i` (a run of exactly the same length), or -1.
function codeSpanClose(s, i, run) {
  const fence = s.slice(i, i + run);
  let close = s.indexOf(fence, i + run);
  while (close >= 0 && backtickRun(s, close) !== run) {
    close = s.indexOf(fence, close + backtickRun(s, close));
  }
  return close;
}

// The index of the delimiter run `d` that closes emphasis whose content
// starts at `start` (and isn't empty): not preceded by whitespace, and
// (for `_`) not followed by a letter or digit. Code spans and escaped
// characters don't count. -1 if there is none.
function closingDelim(s, d, start) {
  let j = start;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === 92) {
      j += 2;
    } else if (c === 96) {
      const run = backtickRun(s, j);
      const close = codeSpanClose(s, j, run);
      j = close >= 0 ? close + run : j + run;
    } else if (s.startsWith(d, j)) {
      const before = s.charCodeAt(j - 1);
      const end = j + d.length;
      const afterOk = end >= s.length || d.charCodeAt(0) !== 95 || !isAlnum(s.charCodeAt(end));
      // A single `*` must not be half of a `**`.
      const single = d.length === 1 && end < s.length && s.charCodeAt(end) === d.charCodeAt(0);
      if (j > start && !isBlankChar(before) && before !== 10 && afterOk && !single) return j;
      j += single ? 2 : 1;
    } else {
      j++;
    }
  }
  return -1;
}

// The index of the `]` matching the `[` at `open`, or -1.
function closingBracket(s, open) {
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 92) i++;
    else if (c === 91) depth++;
    else if (c === 93) {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function inline(s) {
  const out = [];
  const n = s.length;
  let text = 0; // start of the pending run of plain text
  let i = 0;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === 92 && i + 1 < n && isPunct(s.charCodeAt(i + 1))) {
      // Backslash escape.
      out.push(escapeHtml(s.slice(text, i)));
      out.push(escapeHtml(s.slice(i + 1, i + 2)));
      i += 2;
      text = i;
    } else if (c === 92 && i + 1 < n && s.charCodeAt(i + 1) === 10) {
      // Backslash hard line break.
      out.push(escapeHtml(s.slice(text, i)));
      out.push("<br />\n");
      i += 2;
      text = i;
    } else if (c === 10) {
      // Two or more trailing spaces: hard line break.
      let k = i;
      while (k > text && s.charCodeAt(k - 1) === 32) k--;
      if (i - k >= 2) {
        out.push(escapeHtml(s.slice(text, k)));
        out.push("<br />\n");
        text = i + 1;
      }
      i++;
    } else if (c === 96) {
      // Code span: a run of backticks closed by a run of the same length.
      const run = backtickRun(s, i);
      const close = codeSpanClose(s, i, run);
      if (close >= 0) {
        out.push(escapeHtml(s.slice(text, i)));
        let code = s.slice(i + run, close).replaceAll("\n", " ");
        if (code.length >= 2 && code.startsWith(" ") && code.endsWith(" ") && !isBlank(code)) {
          code = code.slice(1, code.length - 1);
        }
        out.push("<code>" + escapeHtml(code) + "</code>");
        i = close + run;
        text = i;
      } else {
        i += run;
      }
    } else if (c === 42 || c === 95) {
      // Emphasis (`*x*`, `_x_`) and strong (`**x**`, `__x__`).
      let run = 1;
      while (i + run < n && s.charCodeAt(i + run) === c) run++;
      const strong = run >= 2;
      const d = strong ? s.slice(i, i + 2) : s.slice(i, i + 1);
      const after = i + d.length;
      const opens =
        after < n &&
        !isBlankChar(s.charCodeAt(after)) &&
        s.charCodeAt(after) !== 10 &&
        (c === 42 || i === 0 || !isAlnum(s.charCodeAt(i - 1)));
      const close = opens ? closingDelim(s, d, after) : -1;
      if (close >= 0) {
        out.push(escapeHtml(s.slice(text, i)));
        const tag = strong ? "strong" : "em";
        out.push("<" + tag + ">" + inline(s.slice(after, close)) + "</" + tag + ">");
        i = close + d.length;
        text = i;
      } else {
        i += run;
      }
    } else if (c === 126 && i + 1 < n && s.charCodeAt(i + 1) === 126) {
      // Strikethrough `~~x~~` (GitHub).
      const opens = i + 2 < n && !isBlankChar(s.charCodeAt(i + 2));
      const close = opens ? closingDelim(s, "~~", i + 2) : -1;
      if (close >= 0) {
        out.push(escapeHtml(s.slice(text, i)));
        out.push("<s>" + inline(s.slice(i + 2, close)) + "</s>");
        i = close + 2;
        text = i;
      } else {
        i += 2;
      }
    } else if (c === 91 || (c === 33 && i + 1 < n && s.charCodeAt(i + 1) === 91)) {
      // Link `[text](url)` or image `![alt](src)`.
      const image = c === 33;
      const open = image ? i + 1 : i;
      const close = closingBracket(s, open);
      const paren = close >= 0 && close + 1 < n && s.charCodeAt(close + 1) === 40;
      const end = paren ? s.indexOf(")", close + 2) : -1;
      if (end >= 0) {
        out.push(escapeHtml(s.slice(text, i)));
        const label = s.slice(open + 1, close);
        let dest = s.slice(close + 2, end).trim();
        let title = "";
        const sp = dest.indexOf(" \"");
        if (sp >= 0 && dest.endsWith("\"")) {
          title = dest.slice(sp + 2, dest.length - 1);
          dest = dest.slice(0, sp).trim();
        }
        if (dest.startsWith("<") && dest.endsWith(">")) dest = dest.slice(1, dest.length - 1);
        const titleAttr = title === "" ? "" : " title=\"" + escapeHtml(title) + "\"";
        if (image) {
          out.push("<img src=\"" + escapeHtml(dest) + "\" alt=\"" + escapeHtml(label) + "\"" + titleAttr + " />");
        } else {
          out.push("<a href=\"" + escapeHtml(dest) + "\"" + titleAttr + ">" + inline(label) + "</a>");
        }
        i = end + 1;
        text = i;
      } else {
        i += image ? 2 : 1;
      }
    } else if (c === 60 && (s.startsWith("http://", i + 1) || s.startsWith("https://", i + 1))) {
      // Autolink `<https://…>`.
      const end = s.indexOf(">", i);
      const space = s.indexOf(" ", i);
      if (space < 0 || space > end) {
        const url = escapeHtml(s.slice(i + 1, end));
        out.push(escapeHtml(s.slice(text, i)));
        out.push("<a href=\"" + url + "\">" + url + "</a>");
        i = end + 1;
        text = i;
      } else {
        i++;
      }
    } else {
      i++;
    }
  }
  out.push(escapeHtml(s.slice(text, n)));
  return out.join("");
}

// ---- blocks ----------------------------------------------------------------

// `#`-heading level of a (dedented) line, or 0.
function headingLevel(t) {
  let n = 0;
  while (n < t.length && t.charCodeAt(n) === 35) n++;
  if (n === 0 || n > 6) return 0;
  if (n < t.length && !isBlankChar(t.charCodeAt(n))) return 0;
  return n;
}

function headingText(t, level) {
  let s = t.slice(level).trim();
  // An optional closing run of `#`s.
  let k = s.length;
  while (k > 0 && s.charCodeAt(k - 1) === 35) k--;
  if (k === 0) return "";
  if (k < s.length && isBlankChar(s.charCodeAt(k - 1))) s = s.slice(0, k).trim();
  return s;
}

// A thematic break: three or more `-`, `*` or `_`, optionally spaced.
function isRule(t) {
  let mark = 0;
  let count = 0;
  for (let i = 0; i < t.length; i++) {
    const c = t.charCodeAt(i);
    if (isBlankChar(c)) continue;
    if (c !== 45 && c !== 42 && c !== 95) return false;
    if (mark !== 0 && c !== mark) return false;
    mark = c;
    count++;
  }
  return count >= 3;
}

// The opening of a fenced code block: the fence character (backtick or
// tilde) repeated at least three times.
function fenceLength(t) {
  const c = t.charCodeAt(0);
  if (c !== 96 && c !== 126) return 0;
  let n = 0;
  while (n < t.length && t.charCodeAt(n) === c) n++;
  if (n < 3) return 0;
  if (c === 96 && t.indexOf("`", n) >= 0) return 0;
  return n;
}

// A list item marker at the start of a (dedented) line.
function listMarker(t) {
  const none = { ok: false, ordered: false, start: 0, width: 0, delim: 0 };
  const c = t.charCodeAt(0);
  if (c === 45 || c === 42 || c === 43) {
    if (t.length === 1) return { ok: true, ordered: false, start: 0, width: 2, delim: c };
    if (!isBlankChar(t.charCodeAt(1))) return none;
    return { ok: true, ordered: false, start: 0, width: 2, delim: c };
  }
  let n = 0;
  let value = 0;
  while (n < t.length && n < 9 && isDigit(t.charCodeAt(n))) {
    value = value * 10 + (t.charCodeAt(n) - 48);
    n++;
  }
  if (n === 0 || n >= t.length) return none;
  const d = t.charCodeAt(n);
  if (d !== 46 && d !== 41) return none;
  if (n + 1 < t.length && !isBlankChar(t.charCodeAt(n + 1))) return none;
  return { ok: true, ordered: true, start: value, width: n + 2, delim: d };
}

// Split a table row into its cells.
function tableCells(t) {
  let s = t.trim();
  if (s.startsWith("|")) s = s.slice(1);
  if (s.endsWith("|") && !s.endsWith("\\|")) s = s.slice(0, s.length - 1);
  const cells = [];
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 92) i++;
    else if (c === 124) {
      cells.push(s.slice(start, i).trim().replaceAll("\\|", "|"));
      start = i + 1;
    }
  }
  cells.push(s.slice(start).trim().replaceAll("\\|", "|"));
  return cells;
}

// Column alignments from a table's delimiter row, or [] if `t` isn't one.
function tableAligns(t) {
  if (t.indexOf("-") < 0) return [];
  const cells = tableCells(t);
  const aligns = [];
  for (const cell of cells) {
    let dashes = 0;
    for (let i = 0; i < cell.length; i++) {
      const c = cell.charCodeAt(i);
      if (c === 45) dashes++;
      else if (c !== 58) return [];
    }
    if (dashes === 0) return [];
    const left = cell.startsWith(":");
    const right = cell.endsWith(":");
    if (left && right) aligns.push("center");
    else if (right) aligns.push("right");
    else if (left) aligns.push("left");
    else aligns.push("");
  }
  return aligns;
}

function tableRow(cells, aligns, tag, out) {
  out.push("<tr>\n");
  for (let i = 0; i < aligns.length; i++) {
    const text = i < cells.length ? inline(cells[i]) : "";
    const style = aligns[i] === "" ? "" : " style=\"text-align:" + aligns[i] + "\"";
    out.push("<" + tag + style + ">" + text + "</" + tag + ">\n");
  }
  out.push("</tr>\n");
}

// Whether `t` (dedented) starts a block that interrupts a paragraph.
function interrupts(t) {
  if (headingLevel(t) > 0 || isRule(t) || fenceLength(t) > 0 || t.startsWith(">")) return true;
  const m = listMarker(t);
  return m.ok && t.length > m.width - 1 && (!m.ordered || m.start === 1);
}

// Marks a tight list item's paragraph text in `renderBlocks`' output, for
// the list item around it (and removed there).
const TIGHT = "\u0001";

// Render `lines` as HTML blocks onto `out`. In a tight list item,
// paragraphs are emitted without `<p>` tags (marked with TIGHT).
function renderBlocks(lines, tight, out) {
  const n = lines.length;
  let i = 0;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) {
      i++;
      continue;
    }
    const ind = indentOf(line);
    const t = dedent(line, ind);

    // Indented code block.
    if (ind >= 4) {
      const code = [];
      while (i < n && (indentOf(lines[i]) >= 4 || isBlank(lines[i]))) {
        code.push(dedent(lines[i], 4));
        i++;
      }
      while (code.length > 0 && isBlank(code[code.length - 1])) code.pop();
      out.push("<pre><code>" + escapeHtml(code.join("\n")) + "\n</code></pre>\n");
      continue;
    }

    // Fenced code block.
    const fence = fenceLength(t);
    if (fence > 0) {
      const mark = t.slice(0, fence);
      const lang = t.slice(fence).trim();
      const code = [];
      i++;
      while (i < n) {
        const u = dedent(lines[i], ind);
        const v = u.trim();
        if (v.startsWith(mark) && fenceLength(v) >= fence && v.slice(fenceLength(v)).trim() === "") {
          i++;
          break;
        }
        code.push(u);
        i++;
      }
      const cls = lang === "" ? "" : " class=\"language-" + escapeHtml(lang.split(" ")[0]) + "\"";
      const body = code.length === 0 ? "" : escapeHtml(code.join("\n")) + "\n";
      out.push("<pre><code" + cls + ">" + body + "</code></pre>\n");
      continue;
    }

    // ATX heading.
    const level = headingLevel(t);
    if (level > 0) {
      const h = "h" + String(level);
      out.push("<" + h + ">" + inline(headingText(t, level)) + "</" + h + ">\n");
      i++;
      continue;
    }

    // Thematic break (checked before lists: `* * *` is a rule).
    if (isRule(t)) {
      out.push("<hr />\n");
      i++;
      continue;
    }

    // Block quote.
    if (t.startsWith(">")) {
      const inner = [];
      while (i < n && !isBlank(lines[i])) {
        const u = dedent(lines[i], indentOf(lines[i]));
        if (u.startsWith(">")) {
          inner.push(u.startsWith("> ") ? u.slice(2) : u.slice(1));
        } else if (inner.length > 0 && !interrupts(u)) {
          inner.push(u); // lazy continuation
        } else {
          break;
        }
        i++;
      }
      out.push("<blockquote>\n");
      renderBlocks(inner, false, out);
      out.push("</blockquote>\n");
      continue;
    }

    // List.
    const m = listMarker(t);
    if (m.ok) {
      const tag = m.ordered ? "ol" : "ul";
      const items = [];
      let loose = false;
      while (i < n) {
        const first = lines[i];
        const fi = indentOf(first);
        const ft = dedent(first, fi);
        const fm = listMarker(ft);
        if (fi !== ind || !fm.ok || fm.ordered !== m.ordered || fm.delim !== m.delim || isRule(ft)) break;
        const contentCol = fi + fm.width;
        const item = [ft.slice(fm.width)];
        i++;
        let sawBlank = false;
        while (i < n) {
          const u = lines[i];
          if (isBlank(u)) {
            sawBlank = true;
            item.push("");
            i++;
            continue;
          }
          const ui = indentOf(u);
          if (ui >= contentCol) {
            if (sawBlank) loose = true;
            item.push(dedent(u, contentCol));
            sawBlank = false;
            i++;
            continue;
          }
          const ut = dedent(u, ui);
          // The list's next item, or a list at the same level ending it.
          if (listMarker(ut).ok) break;
          if (!sawBlank && !interrupts(ut) && !isBlank(item[item.length - 1])) {
            item.push(ut); // lazy continuation of the item's paragraph
            i++;
            continue;
          }
          break;
        }
        // Blank lines between items make the list loose.
        while (item.length > 1 && isBlank(item[item.length - 1])) item.pop();
        if (sawBlank && i < n) {
          const next = lines[i];
          const nm = listMarker(dedent(next, indentOf(next)));
          if (indentOf(next) === ind && nm.ok && nm.ordered === m.ordered && nm.delim === m.delim) loose = true;
        }
        items.push(item);
      }
      const startAttr = m.ordered && m.start !== 1 ? " start=\"" + String(m.start) + "\"" : "";
      out.push("<" + tag + startAttr + ">\n");
      for (const item of items) {
        const inner = [];
        renderBlocks(item, !loose, inner);
        if (inner.length === 0) {
          out.push("<li></li>\n");
          continue;
        }
        // A tight item's text sits directly in the <li>; a block starts
        // on a new line.
        const firstText = inner[0].startsWith(TIGHT);
        const lastText = inner[inner.length - 1].startsWith(TIGHT);
        let body = inner.map((c) => (c.startsWith(TIGHT) ? c.slice(1) : c)).join("");
        if (lastText) body = body.slice(0, body.length - 1);
        out.push("<li>" + (firstText ? "" : "\n") + body + "</li>\n");
      }
      out.push("</" + tag + ">\n");
      continue;
    }

    // Table: a header row followed by a delimiter row.
    if (t.indexOf("|") >= 0 && i + 1 < n) {
      const aligns = tableAligns(lines[i + 1]);
      const header = tableCells(t);
      if (aligns.length > 0 && aligns.length === header.length) {
        out.push("<table>\n<thead>\n");
        tableRow(header, aligns, "th", out);
        out.push("</thead>\n");
        i += 2;
        if (i < n && !isBlank(lines[i])) {
          out.push("<tbody>\n");
          while (i < n && !isBlank(lines[i]) && !interrupts(dedent(lines[i], indentOf(lines[i])))) {
            tableRow(tableCells(lines[i]), aligns, "td", out);
            i++;
          }
          out.push("</tbody>\n");
        }
        out.push("</table>\n");
        continue;
      }
    }

    // Paragraph, possibly turned into a setext heading by an
    // underline of `=` or `-`.
    const para = [t];
    i++;
    let setext = 0;
    while (i < n && !isBlank(lines[i])) {
      const u = dedent(lines[i], indentOf(lines[i]));
      const v = u.trim();
      if (v.length > 0 && (v.charCodeAt(0) === 61 || v.charCodeAt(0) === 45)) {
        let k = 0;
        while (k < v.length && v.charCodeAt(k) === v.charCodeAt(0)) k++;
        if (k === v.length) {
          setext = v.charCodeAt(0) === 61 ? 1 : 2;
          i++;
          break;
        }
      }
      if (interrupts(u)) break;
      para.push(u);
      i++;
    }
    const text = inline(para.join("\n").trimEnd());
    if (setext > 0) {
      const h = "h" + String(setext);
      out.push("<" + h + ">" + text + "</" + h + ">\n");
    } else if (tight) {
      out.push(TIGHT + text + "\n");
    } else {
      out.push("<p>" + text + "</p>\n");
    }
  }
}

// The document title for --standalone: the text of the first heading in
// the rendered `html` (already escaped), without its inline tags.
function titleOf(html) {
  let open = html.indexOf("<h");
  while (open >= 0 && open + 3 < html.length) {
    // `<h1>` … `<h6>`, not `<hr />`.
    const level = html.charCodeAt(open + 2);
    if (level >= 49 && level <= 54 && html.charCodeAt(open + 3) === 62) {
      const inner = html.slice(open + 4, html.indexOf("</h", open));
      const text = [];
      let inTag = false;
      for (let i = 0; i < inner.length; i++) {
        const c = inner.charCodeAt(i);
        if (c === 60) inTag = true;
        else if (c === 62) inTag = false;
        else if (!inTag) text.push(inner.slice(i, i + 1));
      }
      return text.join("");
    }
    open = html.indexOf("<h", open + 2);
  }
  return "Document";
}

function markdownToHtml(src) {
  const lines = src.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (l.endsWith("\r")) lines[i] = l.slice(0, l.length - 1);
  }
  const out = [];
  renderBlocks(lines, false, out);
  return out.join("");
}

// ---- command line ------------------------------------------------------------

function usage() {
  process.stderr.write("usage: md2html [input.md | -] [-o output.html] [-s | --standalone]\n");
}

const args = process.argv.slice(2);
let input = "-";
let output = "";
let standalone = false;
let a = 0;
while (a < args.length) {
  const arg = args[a];
  if (arg === "-o" && a + 1 < args.length) {
    output = args[a + 1];
    a += 2;
  } else if (arg === "-s" || arg === "--standalone") {
    standalone = true;
    a++;
  } else if (arg === "-h" || arg === "--help") {
    usage();
    process.exit(0);
  } else if (arg.startsWith("-") && arg !== "-") {
    process.stderr.write("md2html: unknown option " + arg + "\n");
    usage();
    process.exit(2);
  } else {
    input = arg;
    a++;
  }
}

const src = readFileSync(input === "-" ? "/dev/stdin" : input, "utf8");
let html = markdownToHtml(src);
if (standalone) {
  const title = titleOf(html);
  html =
    "<!DOCTYPE html>\n<html>\n<head>\n<meta charset=\"utf-8\">\n<title>" +
    title +
    "</title>\n</head>\n<body>\n" +
    html +
    "</body>\n</html>\n";
}
if (output === "") process.stdout.write(html);
else writeFileSync(output, html);
