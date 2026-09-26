// fastdiff: diff two text files with fast-diff (diff-match-patch).
//
//   fastdiff old.txt new.txt [--cleanup]
//
// Prints a summary line and then one line per diff operation: `=`
// (equal), `-` (deleted from old) or `+` (inserted in new), followed by
// the text as a JSON string literal. `--cleanup` applies
// diff_cleanupSemantic, as `diff(old, new, undefined, true)` does.
//
// ---- Provenance and license -------------------------------------------------
//
// The diff algorithm below is a port of fast-diff 1.3.0
// (https://github.com/jhchen/fast-diff, npm `fast-diff`, file `diff.js`),
// which is itself a modified subset of Neil Fraser's Diff Match and Patch:
//
//   Diff Match and Patch
//   Copyright 2006 Google Inc.
//   http://code.google.com/p/google-diff-match-patch/
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//
// This file is a modified version (Apache-2.0 section 4(b)). The upstream
// function names, control flow and comments are kept; the changes are
// only those needed to fit the subset of JavaScript that inty type-checks
// and its Go backend translates:
//
// 1. A diff is an array of `{ op, text }` records (built by `mk`) instead
//    of `[op, text]` tuples: mixed-type tuples are not supported. `d[0]` /
//    `d[1]` become `d.op` / `d.text`; the op values (-1, 0, 1) are the same.
// 2. `diff_main` takes all its parameters explicitly (default / optional
//    parameters are not supported): the internal recursive calls pass
//    `false` for `cleanup` and `fix_unicode` where upstream omits them.
// 3. The `cursor_pos` parameter and `find_cursor_edit_diff`,
//    `make_edit_splice` and `remove_empty_tuples` (the cursor-aware fast
//    path Quill uses for single keystrokes) are dropped: the CLI never
//    passes a cursor, so upstream never reaches them here. The exported
//    `diff(text1, text2, cursor_pos, cleanup)` is `diff(text1, text2,
//    cleanup)`, still passing fix_unicode = true to diff_main.
// 4. `diff_halfMatch_` / `diff_halfMatchI_` return [] instead of `null` for
//    "no half-match", and callers test `.length`. The `best_*` / `text*_a`
//    strings start as "" instead of undefined (they are only read once a
//    match was found).
// 5. `lastequality` in `diff_cleanupSemantic` is "" instead of `null` when
//    there is none, and `lastequality && ...` is `lastequality !== "" &&
//    ...` (inty requires both operands of `&&` to have one type; both
//    tests are false exactly for null and "").
// 6. Upstream decrements `equalitiesLength` below zero when it eliminates
//    the only equality on its stack, and then writes and reads
//    `equalities[-1]`, `equalities[-2]`, ...: ordinary properties of a JS
//    array. `stackGet` / `stackSet` keep negative indices in a second
//    array, so the port does exactly the same (the Go runtime would panic
//    on a negative index instead).
// 7. The regular expressions in `diff_cleanupSemanticScore_` (regex
//    literals are not supported) become equivalent character tests:
//    `/[^a-zA-Z0-9]/`, `/\s/` (ASCII whitespace: space, \t \n \v \f \r),
//    `/[\r\n]/`, `/\n\r?\n$/` and `/^\r?\n\r?\n/`. In JS `\s` also matches
//    non-ASCII spaces (U+00A0, U+2028, ...); see the ASCII note below.
// 8. `new Array(v_length)` filled with -1 by a loop becomes
//    `new Array(v_length).fill(-1)` (inty types `new Array(n)` only
//    together with its `fill`: alone, its holes read as undefined).
// 9. `a.concat(b, c)` becomes `a.concat(b).concat(c)` (concat takes one
//    array).
// 10. `var` becomes `let` / `const`. Upstream re-declares `var x1`,
//    `var k2_offset`, ... in sibling loop bodies, which become separate
//    blocks, and `case DIFF_EQUAL:` gets a block for its declarations.
//    `==` / `!=` between two strings or two numbers becomes `===` / `!==`
//    (same result for operands of one type).
// 11. The surrogate-pair helpers (`is_surrogate_pair_start`, ...) are kept,
//    but read characters through `charCodeOrNaN`: upstream's
//    `str.charCodeAt(-1)` or `"".charCodeAt(0)` is NaN, which compares
//    false, while the Go translation would panic. Likewise upstream's
//    `diffs[k] && ...` with k = -1 becomes `k >= 0 && ...`.
// 12. `/** function f(...) => ... */` and `/** type Diff = ... */` comments
//    give inty the types of the helpers that only index into their
//    arguments, so they get one concrete Go type each instead of a
//    row-polymorphic one. They are comments: JavaScript ignores them.
//
// Nothing else changes: fast-diff has no timeout in `diff_bisect_`
// (unlike diff-match-patch), and neither does the port.
//
// ASCII note: the Go translation treats strings as byte strings, while JS
// strings are UTF-16. For ASCII input the two agree exactly (and the
// surrogate-pair fix-ups never fire). For non-ASCII input the Go binary
// diffs bytes, so op boundaries (and the \uXXXX rendering) can differ.
//
// Plain JavaScript: runs as-is under Node or Bun, and inty type-checks
// it and translates it into Go (`inty go fastdiff.js`) that produces
// byte-identical output.

import { readFileSync } from "node:fs";
import process from "node:process";

/**
 * The data structure representing a diff is an array of records:
 * [{op: DIFF_DELETE, text: 'Hello'}, {op: DIFF_INSERT, text: 'Goodbye'},
 *  {op: DIFF_EQUAL, text: ' world.'}]
 * which means: delete 'Hello', add 'Goodbye' and keep ' world.'
 */
const DIFF_DELETE = -1;
const DIFF_INSERT = 1;
const DIFF_EQUAL = 0;

/** type Diff = {op: Number, text: String} */

function mk(op, text) {
  return { op: op, text: text };
}

/**
 * Find the differences between two texts.  Simplifies the problem by stripping
 * any common prefix or suffix off the texts before diffing.
 * @param {string} text1 Old string to be diffed.
 * @param {string} text2 New string to be diffed.
 * @param {boolean} cleanup Apply semantic cleanup before returning.
 * @param {boolean} _fix_unicode Normalize to a unicode-correct diff.
 * @return {Array} Array of diff records.
 */
function diff_main(text1, text2, cleanup, _fix_unicode) {
  // Check for equality
  if (text1 === text2) {
    if (text1) {
      return [mk(DIFF_EQUAL, text1)];
    }
    return [];
  }

  // Trim off common prefix (speedup).
  let commonlength = diff_commonPrefix(text1, text2);
  const commonprefix = text1.substring(0, commonlength);
  text1 = text1.substring(commonlength);
  text2 = text2.substring(commonlength);

  // Trim off common suffix (speedup).
  commonlength = diff_commonSuffix(text1, text2);
  const commonsuffix = text1.substring(text1.length - commonlength);
  text1 = text1.substring(0, text1.length - commonlength);
  text2 = text2.substring(0, text2.length - commonlength);

  // Compute the diff on the middle block.
  const diffs = diff_compute_(text1, text2);

  // Restore the prefix and suffix.
  if (commonprefix) {
    diffs.unshift(mk(DIFF_EQUAL, commonprefix));
  }
  if (commonsuffix) {
    diffs.push(mk(DIFF_EQUAL, commonsuffix));
  }
  diff_cleanupMerge(diffs, _fix_unicode);
  if (cleanup) {
    diff_cleanupSemantic(diffs);
  }
  return diffs;
}

/**
 * Find the differences between two texts.  Assumes that the texts do not
 * have any common prefix or suffix.
 * @param {string} text1 Old string to be diffed.
 * @param {string} text2 New string to be diffed.
 * @return {Array} Array of diff records.
 */
function diff_compute_(text1, text2) {
  if (!text1) {
    // Just add some text (speedup).
    return [mk(DIFF_INSERT, text2)];
  }

  if (!text2) {
    // Just delete some text (speedup).
    return [mk(DIFF_DELETE, text1)];
  }

  const longtext = text1.length > text2.length ? text1 : text2;
  const shorttext = text1.length > text2.length ? text2 : text1;
  const i = longtext.indexOf(shorttext);
  if (i !== -1) {
    // Shorter text is inside the longer text (speedup).
    const diffs = [
      mk(DIFF_INSERT, longtext.substring(0, i)),
      mk(DIFF_EQUAL, shorttext),
      mk(DIFF_INSERT, longtext.substring(i + shorttext.length)),
    ];
    // Swap insertions for deletions if diff is reversed.
    if (text1.length > text2.length) {
      diffs[0].op = diffs[2].op = DIFF_DELETE;
    }
    return diffs;
  }

  if (shorttext.length === 1) {
    // Single character string.
    // After the previous speedup, the character can't be an equality.
    return [mk(DIFF_DELETE, text1), mk(DIFF_INSERT, text2)];
  }

  // Check to see if the problem can be split in two.
  const hm = diff_halfMatch_(text1, text2);
  if (hm.length > 0) {
    // A half-match was found, sort out the return data.
    const text1_a = hm[0];
    const text1_b = hm[1];
    const text2_a = hm[2];
    const text2_b = hm[3];
    const mid_common = hm[4];
    // Send both pairs off for separate processing.
    const diffs_a = diff_main(text1_a, text2_a, false, false);
    const diffs_b = diff_main(text1_b, text2_b, false, false);
    // Merge the results.
    return diffs_a.concat([mk(DIFF_EQUAL, mid_common)]).concat(diffs_b);
  }

  return diff_bisect_(text1, text2);
}

/**
 * Find the 'middle snake' of a diff, split the problem in two
 * and return the recursively constructed diff.
 * See Myers 1986 paper: An O(ND) Difference Algorithm and Its Variations.
 * @param {string} text1 Old string to be diffed.
 * @param {string} text2 New string to be diffed.
 * @return {Array} Array of diff records.
 * @private
 */
function diff_bisect_(text1, text2) {
  // Cache the text lengths to prevent multiple calls.
  const text1_length = text1.length;
  const text2_length = text2.length;
  const max_d = Math.ceil((text1_length + text2_length) / 2);
  const v_offset = max_d;
  const v_length = 2 * max_d;
  // Setting all elements to -1 is faster in Chrome & Firefox than mixing
  // integers and undefined.
  const v1 = new Array(v_length).fill(-1);
  const v2 = new Array(v_length).fill(-1);
  v1[v_offset + 1] = 0;
  v2[v_offset + 1] = 0;
  const delta = text1_length - text2_length;
  // If the total number of characters is odd, then the front path will collide
  // with the reverse path.
  const front = delta % 2 !== 0;
  // Offsets for start and end of k loop.
  // Prevents mapping of space beyond the grid.
  let k1start = 0;
  let k1end = 0;
  let k2start = 0;
  let k2end = 0;
  for (let d = 0; d < max_d; d++) {
    // Walk the front path one step.
    for (let k1 = -d + k1start; k1 <= d - k1end; k1 += 2) {
      const k1_offset = v_offset + k1;
      let x1 = 0;
      if (k1 === -d || (k1 !== d && v1[k1_offset - 1] < v1[k1_offset + 1])) {
        x1 = v1[k1_offset + 1];
      } else {
        x1 = v1[k1_offset - 1] + 1;
      }
      let y1 = x1 - k1;
      while (
        x1 < text1_length &&
        y1 < text2_length &&
        text1.charAt(x1) === text2.charAt(y1)
      ) {
        x1++;
        y1++;
      }
      v1[k1_offset] = x1;
      if (x1 > text1_length) {
        // Ran off the right of the graph.
        k1end += 2;
      } else if (y1 > text2_length) {
        // Ran off the bottom of the graph.
        k1start += 2;
      } else if (front) {
        const k2_offset = v_offset + delta - k1;
        if (k2_offset >= 0 && k2_offset < v_length && v2[k2_offset] !== -1) {
          // Mirror x2 onto top-left coordinate system.
          const x2 = text1_length - v2[k2_offset];
          if (x1 >= x2) {
            // Overlap detected.
            return diff_bisectSplit_(text1, text2, x1, y1);
          }
        }
      }
    }

    // Walk the reverse path one step.
    for (let k2 = -d + k2start; k2 <= d - k2end; k2 += 2) {
      const k2_offset = v_offset + k2;
      let x2 = 0;
      if (k2 === -d || (k2 !== d && v2[k2_offset - 1] < v2[k2_offset + 1])) {
        x2 = v2[k2_offset + 1];
      } else {
        x2 = v2[k2_offset - 1] + 1;
      }
      let y2 = x2 - k2;
      while (
        x2 < text1_length &&
        y2 < text2_length &&
        text1.charAt(text1_length - x2 - 1) ===
          text2.charAt(text2_length - y2 - 1)
      ) {
        x2++;
        y2++;
      }
      v2[k2_offset] = x2;
      if (x2 > text1_length) {
        // Ran off the left of the graph.
        k2end += 2;
      } else if (y2 > text2_length) {
        // Ran off the top of the graph.
        k2start += 2;
      } else if (!front) {
        const k1_offset = v_offset + delta - k2;
        if (k1_offset >= 0 && k1_offset < v_length && v1[k1_offset] !== -1) {
          const x1 = v1[k1_offset];
          const y1 = v_offset + x1 - k1_offset;
          // Mirror x2 onto top-left coordinate system.
          x2 = text1_length - x2;
          if (x1 >= x2) {
            // Overlap detected.
            return diff_bisectSplit_(text1, text2, x1, y1);
          }
        }
      }
    }
  }
  // Diff took too long and hit the deadline or
  // number of diffs equals number of characters, no commonality at all.
  return [mk(DIFF_DELETE, text1), mk(DIFF_INSERT, text2)];
}

/**
 * Given the location of the 'middle snake', split the diff in two parts
 * and recurse.
 * @param {string} text1 Old string to be diffed.
 * @param {string} text2 New string to be diffed.
 * @param {number} x Index of split point in text1.
 * @param {number} y Index of split point in text2.
 * @return {Array} Array of diff records.
 */
function diff_bisectSplit_(text1, text2, x, y) {
  const text1a = text1.substring(0, x);
  const text2a = text2.substring(0, y);
  const text1b = text1.substring(x);
  const text2b = text2.substring(y);

  // Compute both diffs serially.
  const diffs = diff_main(text1a, text2a, false, false);
  const diffsb = diff_main(text1b, text2b, false, false);

  return diffs.concat(diffsb);
}

/**
 * Determine the common prefix of two strings.
 * @param {string} text1 First string.
 * @param {string} text2 Second string.
 * @return {number} The number of characters common to the start of each
 *     string.
 */
/** function diff_commonPrefix(String, String) => Number */
function diff_commonPrefix(text1, text2) {
  // Quick check for common null cases.
  if (!text1 || !text2 || text1.charAt(0) !== text2.charAt(0)) {
    return 0;
  }
  // Binary search.
  // Performance analysis: http://neil.fraser.name/news/2007/10/09/
  let pointermin = 0;
  let pointermax = Math.min(text1.length, text2.length);
  let pointermid = pointermax;
  let pointerstart = 0;
  while (pointermin < pointermid) {
    if (
      text1.substring(pointerstart, pointermid) ===
      text2.substring(pointerstart, pointermid)
    ) {
      pointermin = pointermid;
      pointerstart = pointermin;
    } else {
      pointermax = pointermid;
    }
    pointermid = Math.floor((pointermax - pointermin) / 2 + pointermin);
  }

  if (is_surrogate_pair_start(charCodeOrNaN(text1, pointermid - 1))) {
    pointermid--;
  }

  return pointermid;
}

/**
 * Determine if the suffix of one string is the prefix of another.
 * @param {string} text1 First string.
 * @param {string} text2 Second string.
 * @return {number} The number of characters common to the end of the first
 *     string and the start of the second string.
 * @private
 */
/** function diff_commonOverlap_(String, String) => Number */
function diff_commonOverlap_(text1, text2) {
  // Cache the text lengths to prevent multiple calls.
  const text1_length = text1.length;
  const text2_length = text2.length;
  // Eliminate the null case.
  if (text1_length === 0 || text2_length === 0) {
    return 0;
  }
  // Truncate the longer string.
  if (text1_length > text2_length) {
    text1 = text1.substring(text1_length - text2_length);
  } else if (text1_length < text2_length) {
    text2 = text2.substring(0, text1_length);
  }
  const text_length = Math.min(text1_length, text2_length);
  // Quick check for the worst case.
  if (text1 === text2) {
    return text_length;
  }

  // Start by looking for a single character match
  // and increase length until no match is found.
  // Performance analysis: http://neil.fraser.name/news/2010/11/04/
  let best = 0;
  let length = 1;
  while (true) {
    const pattern = text1.substring(text_length - length);
    const found = text2.indexOf(pattern);
    if (found === -1) {
      return best;
    }
    length += found;
    if (
      found === 0 ||
      text1.substring(text_length - length) === text2.substring(0, length)
    ) {
      best = length;
      length++;
    }
  }
}

/**
 * Determine the common suffix of two strings.
 * @param {string} text1 First string.
 * @param {string} text2 Second string.
 * @return {number} The number of characters common to the end of each string.
 */
/** function diff_commonSuffix(String, String) => Number */
function diff_commonSuffix(text1, text2) {
  // Quick check for common null cases.
  if (!text1 || !text2 || text1.slice(-1) !== text2.slice(-1)) {
    return 0;
  }
  // Binary search.
  // Performance analysis: http://neil.fraser.name/news/2007/10/09/
  let pointermin = 0;
  let pointermax = Math.min(text1.length, text2.length);
  let pointermid = pointermax;
  let pointerend = 0;
  while (pointermin < pointermid) {
    if (
      text1.substring(text1.length - pointermid, text1.length - pointerend) ===
      text2.substring(text2.length - pointermid, text2.length - pointerend)
    ) {
      pointermin = pointermid;
      pointerend = pointermin;
    } else {
      pointermax = pointermid;
    }
    pointermid = Math.floor((pointermax - pointermin) / 2 + pointermin);
  }

  if (is_surrogate_pair_end(charCodeOrNaN(text1, text1.length - pointermid))) {
    pointermid--;
  }

  return pointermid;
}

/**
 * Do the two texts share a substring which is at least half the length of the
 * longer text?
 * This speedup can produce non-minimal diffs.
 * @param {string} text1 First string.
 * @param {string} text2 Second string.
 * @return {Array.<string>} Five element Array, containing the prefix of
 *     text1, the suffix of text1, the prefix of text2, the suffix of
 *     text2 and the common middle.  Or [] if there was no match.
 */
/** function diff_halfMatch_(String, String) => String[] */
function diff_halfMatch_(text1, text2) {
  const longtext = text1.length > text2.length ? text1 : text2;
  const shorttext = text1.length > text2.length ? text2 : text1;
  if (longtext.length < 4 || shorttext.length * 2 < longtext.length) {
    return []; // Pointless.
  }

  /**
   * Does a substring of shorttext exist within longtext such that the substring
   * is at least half the length of longtext?
   * Closure, but does not reference any external variables.
   * @param {string} longtext Longer string.
   * @param {string} shorttext Shorter string.
   * @param {number} i Start index of quarter length substring within longtext.
   * @return {Array.<string>} Five element Array, containing the prefix of
   *     longtext, the suffix of longtext, the prefix of shorttext, the suffix
   *     of shorttext and the common middle.  Or [] if there was no match.
   * @private
   */
  /** function diff_halfMatchI_(String, String, Number) => String[] */
  function diff_halfMatchI_(longtext, shorttext, i) {
    // Start with a 1/4 length substring at position i as a seed.
    const seed = longtext.substring(i, i + Math.floor(longtext.length / 4));
    let j = -1;
    let best_common = "";
    let best_longtext_a = "";
    let best_longtext_b = "";
    let best_shorttext_a = "";
    let best_shorttext_b = "";
    while ((j = shorttext.indexOf(seed, j + 1)) !== -1) {
      const prefixLength = diff_commonPrefix(
        longtext.substring(i),
        shorttext.substring(j)
      );
      const suffixLength = diff_commonSuffix(
        longtext.substring(0, i),
        shorttext.substring(0, j)
      );
      if (best_common.length < suffixLength + prefixLength) {
        best_common =
          shorttext.substring(j - suffixLength, j) +
          shorttext.substring(j, j + prefixLength);
        best_longtext_a = longtext.substring(0, i - suffixLength);
        best_longtext_b = longtext.substring(i + prefixLength);
        best_shorttext_a = shorttext.substring(0, j - suffixLength);
        best_shorttext_b = shorttext.substring(j + prefixLength);
      }
    }
    if (best_common.length * 2 >= longtext.length) {
      return [
        best_longtext_a,
        best_longtext_b,
        best_shorttext_a,
        best_shorttext_b,
        best_common,
      ];
    } else {
      return [];
    }
  }

  // First check if the second quarter is the seed for a half-match.
  const hm1 = diff_halfMatchI_(
    longtext,
    shorttext,
    Math.ceil(longtext.length / 4)
  );
  // Check again based on the third quarter.
  const hm2 = diff_halfMatchI_(
    longtext,
    shorttext,
    Math.ceil(longtext.length / 2)
  );
  let hm = hm1;
  if (hm1.length === 0 && hm2.length === 0) {
    return [];
  } else if (hm2.length === 0) {
    hm = hm1;
  } else if (hm1.length === 0) {
    hm = hm2;
  } else {
    // Both matched.  Select the longest.
    hm = hm1[4].length > hm2[4].length ? hm1 : hm2;
  }

  // A half-match was found, sort out the return data.
  let text1_a = "";
  let text1_b = "";
  let text2_a = "";
  let text2_b = "";
  if (text1.length > text2.length) {
    text1_a = hm[0];
    text1_b = hm[1];
    text2_a = hm[2];
    text2_b = hm[3];
  } else {
    text2_a = hm[0];
    text2_b = hm[1];
    text1_a = hm[2];
    text1_b = hm[3];
  }
  const mid_common = hm[4];
  return [text1_a, text1_b, text2_a, text2_b, mid_common];
}

// `stack[i]` for any integer i, as a JS array read: negative indices are
// ordinary properties, kept in `neg` (i = -1 is neg[0]).
/** function stackGet(Int[], Int[], Int) => Int */
function stackGet(stack, neg, i) {
  return i >= 0 ? stack[i] : neg[-i - 1];
}

// `stack[i] = v` for any integer i (see stackGet).
/** function stackSet(Int[], Int[], Int, Int) => Undefined */
function stackSet(stack, neg, i, v) {
  if (i >= 0) stack[i] = v;
  else neg[-i - 1] = v;
}

/**
 * Reduce the number of edits by eliminating semantically trivial equalities.
 * @param {!Array.<!diff_match_patch.Diff>} diffs Array of diff records.
 */
/** function diff_cleanupSemantic(Diff[]) => Undefined */
function diff_cleanupSemantic(diffs) {
  let changes = false;
  const equalities = []; // Stack of indices where equalities are found.
  // Upstream lets equalitiesLength go negative (it is decremented twice
  // after eliminating the only equality) and then reads and writes
  // equalities[-1], equalities[-2], ...: plain properties of the JS array.
  // They live in equalitiesNeg here (index -i - 1); see stackGet/stackSet.
  const equalitiesNeg = [];
  let equalitiesLength = 0; // Keeping our own length var is faster in JS.
  let lastequality = "";
  // Always equal to diffs[equalities[equalitiesLength - 1]].text
  let pointer = 0; // Index of current position.
  // Number of characters that changed prior to the equality.
  let length_insertions1 = 0;
  let length_deletions1 = 0;
  // Number of characters that changed after the equality.
  let length_insertions2 = 0;
  let length_deletions2 = 0;
  while (pointer < diffs.length) {
    if (diffs[pointer].op === DIFF_EQUAL) {
      // Equality found.
      stackSet(equalities, equalitiesNeg, equalitiesLength++, pointer);
      length_insertions1 = length_insertions2;
      length_deletions1 = length_deletions2;
      length_insertions2 = 0;
      length_deletions2 = 0;
      lastequality = diffs[pointer].text;
    } else {
      // An insertion or deletion.
      if (diffs[pointer].op === DIFF_INSERT) {
        length_insertions2 += diffs[pointer].text.length;
      } else {
        length_deletions2 += diffs[pointer].text.length;
      }
      // Eliminate an equality that is smaller or equal to the edits on both
      // sides of it.
      if (
        lastequality !== "" &&
        lastequality.length <=
          Math.max(length_insertions1, length_deletions1) &&
        lastequality.length <= Math.max(length_insertions2, length_deletions2)
      ) {
        // Duplicate record.
        diffs.splice(
          stackGet(equalities, equalitiesNeg, equalitiesLength - 1),
          0,
          mk(DIFF_DELETE, lastequality)
        );
        // Change second copy to insert.
        diffs[stackGet(equalities, equalitiesNeg, equalitiesLength - 1) + 1].op =
          DIFF_INSERT;
        // Throw away the equality we just deleted.
        equalitiesLength--;
        // Throw away the previous equality (it needs to be reevaluated).
        equalitiesLength--;
        pointer = equalitiesLength > 0 ? equalities[equalitiesLength - 1] : -1;
        length_insertions1 = 0; // Reset the counters.
        length_deletions1 = 0;
        length_insertions2 = 0;
        length_deletions2 = 0;
        lastequality = "";
        changes = true;
      }
    }
    pointer++;
  }

  // Normalize the diff.
  if (changes) {
    diff_cleanupMerge(diffs, false);
  }
  diff_cleanupSemanticLossless(diffs);

  // Find any overlaps between deletions and insertions.
  // e.g: <del>abcxxx</del><ins>xxxdef</ins>
  //   -> <del>abc</del>xxx<ins>def</ins>
  // e.g: <del>xxxabc</del><ins>defxxx</ins>
  //   -> <ins>def</ins>xxx<del>abc</del>
  // Only extract an overlap if it is as big as the edit ahead or behind it.
  pointer = 1;
  while (pointer < diffs.length) {
    if (
      diffs[pointer - 1].op === DIFF_DELETE &&
      diffs[pointer].op === DIFF_INSERT
    ) {
      const deletion = diffs[pointer - 1].text;
      const insertion = diffs[pointer].text;
      const overlap_length1 = diff_commonOverlap_(deletion, insertion);
      const overlap_length2 = diff_commonOverlap_(insertion, deletion);
      if (overlap_length1 >= overlap_length2) {
        if (
          overlap_length1 >= deletion.length / 2 ||
          overlap_length1 >= insertion.length / 2
        ) {
          // Overlap found.  Insert an equality and trim the surrounding edits.
          diffs.splice(
            pointer,
            0,
            mk(DIFF_EQUAL, insertion.substring(0, overlap_length1))
          );
          diffs[pointer - 1].text = deletion.substring(
            0,
            deletion.length - overlap_length1
          );
          diffs[pointer + 1].text = insertion.substring(overlap_length1);
          pointer++;
        }
      } else {
        if (
          overlap_length2 >= deletion.length / 2 ||
          overlap_length2 >= insertion.length / 2
        ) {
          // Reverse overlap found.
          // Insert an equality and swap and trim the surrounding edits.
          diffs.splice(
            pointer,
            0,
            mk(DIFF_EQUAL, deletion.substring(0, overlap_length2))
          );
          diffs[pointer - 1].op = DIFF_INSERT;
          diffs[pointer - 1].text = insertion.substring(
            0,
            insertion.length - overlap_length2
          );
          diffs[pointer + 1].op = DIFF_DELETE;
          diffs[pointer + 1].text = deletion.substring(overlap_length2);
          pointer++;
        }
      }
      pointer++;
    }
    pointer++;
  }
}

// The character classes of upstream's regular expressions
// (nonAlphaNumericRegex_ = /[^a-zA-Z0-9]/, whitespaceRegex_ = /\s/,
// linebreakRegex_ = /[\r\n]/), as tests on a one-character string.
/** function isNonAlphaNumeric(String) => Boolean */
function isNonAlphaNumeric(ch) {
  const c = ch.charCodeAt(0);
  return !((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122));
}

/** function isWhitespace(String) => Boolean */
function isWhitespace(ch) {
  const c = ch.charCodeAt(0);
  return c === 32 || (c >= 9 && c <= 13);
}

/** function isLineBreak(String) => Boolean */
function isLineBreak(ch) {
  return ch === "\r" || ch === "\n";
}

// blanklineEndRegex_ = /\n\r?\n$/
/** function endsWithBlankLine(String) => Boolean */
function endsWithBlankLine(s) {
  return s.endsWith("\n\n") || s.endsWith("\n\r\n");
}

// blanklineStartRegex_ = /^\r?\n\r?\n/
/** function startsWithBlankLine(String) => Boolean */
function startsWithBlankLine(s) {
  return (
    s.startsWith("\n\n") ||
    s.startsWith("\n\r\n") ||
    s.startsWith("\r\n\n") ||
    s.startsWith("\r\n\r\n")
  );
}

/**
 * Look for single edits surrounded on both sides by equalities
 * which can be shifted sideways to align the edit to a word boundary.
 * e.g: The c<ins>at c</ins>ame. -> The <ins>cat </ins>came.
 * @param {!Array.<!diff_match_patch.Diff>} diffs Array of diff records.
 */
/** function diff_cleanupSemanticLossless(Diff[]) => Undefined */
function diff_cleanupSemanticLossless(diffs) {
  /**
   * Given two strings, compute a score representing whether the internal
   * boundary falls on logical boundaries.
   * Scores range from 6 (best) to 0 (worst).
   * Closure, but does not reference any external variables.
   * @param {string} one First string.
   * @param {string} two Second string.
   * @return {number} The score.
   * @private
   */
  /** function diff_cleanupSemanticScore_(String, String) => Number */
  function diff_cleanupSemanticScore_(one, two) {
    if (!one || !two) {
      // Edges are the best.
      return 6;
    }

    // Each port of this function behaves slightly differently due to
    // subtle differences in each language's definition of things like
    // 'whitespace'.  Since this function's purpose is largely cosmetic,
    // the choice has been made to use each language's native features
    // rather than force total conformity.
    const char1 = one.charAt(one.length - 1);
    const char2 = two.charAt(0);
    const nonAlphaNumeric1 = isNonAlphaNumeric(char1);
    const nonAlphaNumeric2 = isNonAlphaNumeric(char2);
    const whitespace1 = nonAlphaNumeric1 && isWhitespace(char1);
    const whitespace2 = nonAlphaNumeric2 && isWhitespace(char2);
    const lineBreak1 = whitespace1 && isLineBreak(char1);
    const lineBreak2 = whitespace2 && isLineBreak(char2);
    const blankLine1 = lineBreak1 && endsWithBlankLine(one);
    const blankLine2 = lineBreak2 && startsWithBlankLine(two);

    if (blankLine1 || blankLine2) {
      // Five points for blank lines.
      return 5;
    } else if (lineBreak1 || lineBreak2) {
      // Four points for line breaks.
      return 4;
    } else if (nonAlphaNumeric1 && !whitespace1 && whitespace2) {
      // Three points for end of sentences.
      return 3;
    } else if (whitespace1 || whitespace2) {
      // Two points for whitespace.
      return 2;
    } else if (nonAlphaNumeric1 || nonAlphaNumeric2) {
      // One point for non-alphanumeric.
      return 1;
    }
    return 0;
  }

  let pointer = 1;
  // Intentionally ignore the first and last element (don't need checking).
  while (pointer < diffs.length - 1) {
    if (
      diffs[pointer - 1].op === DIFF_EQUAL &&
      diffs[pointer + 1].op === DIFF_EQUAL
    ) {
      // This is a single edit surrounded by equalities.
      let equality1 = diffs[pointer - 1].text;
      let edit = diffs[pointer].text;
      let equality2 = diffs[pointer + 1].text;

      // First, shift the edit as far left as possible.
      const commonOffset = diff_commonSuffix(equality1, edit);
      if (commonOffset) {
        const commonString = edit.substring(edit.length - commonOffset);
        equality1 = equality1.substring(0, equality1.length - commonOffset);
        edit = commonString + edit.substring(0, edit.length - commonOffset);
        equality2 = commonString + equality2;
      }

      // Second, step character by character right, looking for the best fit.
      let bestEquality1 = equality1;
      let bestEdit = edit;
      let bestEquality2 = equality2;
      let bestScore =
        diff_cleanupSemanticScore_(equality1, edit) +
        diff_cleanupSemanticScore_(edit, equality2);
      while (edit.charAt(0) === equality2.charAt(0)) {
        equality1 += edit.charAt(0);
        edit = edit.substring(1) + equality2.charAt(0);
        equality2 = equality2.substring(1);
        const score =
          diff_cleanupSemanticScore_(equality1, edit) +
          diff_cleanupSemanticScore_(edit, equality2);
        // The >= encourages trailing rather than leading whitespace on edits.
        if (score >= bestScore) {
          bestScore = score;
          bestEquality1 = equality1;
          bestEdit = edit;
          bestEquality2 = equality2;
        }
      }

      if (diffs[pointer - 1].text !== bestEquality1) {
        // We have an improvement, save it back to the diff.
        if (bestEquality1) {
          diffs[pointer - 1].text = bestEquality1;
        } else {
          diffs.splice(pointer - 1, 1);
          pointer--;
        }
        diffs[pointer].text = bestEdit;
        if (bestEquality2) {
          diffs[pointer + 1].text = bestEquality2;
        } else {
          diffs.splice(pointer + 1, 1);
          pointer--;
        }
      }
    }
    pointer++;
  }
}

/**
 * Reorder and merge like edit sections.  Merge equalities.
 * Any edit section can move as long as it doesn't cross an equality.
 * @param {Array} diffs Array of diff records.
 * @param {boolean} fix_unicode Whether to normalize to a unicode-correct diff
 */
/** function diff_cleanupMerge(Diff[], Boolean) => Undefined */
function diff_cleanupMerge(diffs, fix_unicode) {
  diffs.push(mk(DIFF_EQUAL, "")); // Add a dummy entry at the end.
  let pointer = 0;
  let count_delete = 0;
  let count_insert = 0;
  let text_delete = "";
  let text_insert = "";
  let commonlength = 0;
  while (pointer < diffs.length) {
    if (pointer < diffs.length - 1 && !diffs[pointer].text) {
      diffs.splice(pointer, 1);
      continue;
    }
    switch (diffs[pointer].op) {
      case DIFF_INSERT:
        count_insert++;
        text_insert += diffs[pointer].text;
        pointer++;
        break;
      case DIFF_DELETE:
        count_delete++;
        text_delete += diffs[pointer].text;
        pointer++;
        break;
      case DIFF_EQUAL: {
        let previous_equality = pointer - count_insert - count_delete - 1;
        if (fix_unicode) {
          // prevent splitting of unicode surrogate pairs.  when fix_unicode is true,
          // we assume that the old and new text in the diff are complete and correct
          // unicode-encoded JS strings, but the tuple boundaries may fall between
          // surrogate pairs.  we fix this by shaving off stray surrogates from the end
          // of the previous equality and the beginning of this equality.  this may create
          // empty equalities or a common prefix or suffix.  for example, if AB and AC are
          // emojis, `[[0, 'A'], [-1, 'BA'], [0, 'C']]` would turn into deleting 'ABAC' and
          // inserting 'AC', and then the common suffix 'AC' will be eliminated.  in this
          // particular case, both equalities go away, we absorb any previous inequalities,
          // and we keep scanning for the next equality before rewriting the tuples.
          if (
            previous_equality >= 0 &&
            ends_with_pair_start(diffs[previous_equality].text)
          ) {
            const stray = diffs[previous_equality].text.slice(-1);
            diffs[previous_equality].text = diffs[previous_equality].text.slice(
              0,
              -1
            );
            text_delete = stray + text_delete;
            text_insert = stray + text_insert;
            if (!diffs[previous_equality].text) {
              // emptied out previous equality, so delete it and include previous delete/insert
              diffs.splice(previous_equality, 1);
              pointer--;
              let k = previous_equality - 1;
              if (k >= 0 && diffs[k].op === DIFF_INSERT) {
                count_insert++;
                text_insert = diffs[k].text + text_insert;
                k--;
              }
              if (k >= 0 && diffs[k].op === DIFF_DELETE) {
                count_delete++;
                text_delete = diffs[k].text + text_delete;
                k--;
              }
              previous_equality = k;
            }
          }
          if (starts_with_pair_end(diffs[pointer].text)) {
            const stray = diffs[pointer].text.charAt(0);
            diffs[pointer].text = diffs[pointer].text.slice(1);
            text_delete += stray;
            text_insert += stray;
          }
        }
        if (pointer < diffs.length - 1 && !diffs[pointer].text) {
          // for empty equality not at end, wait for next equality
          diffs.splice(pointer, 1);
          break;
        }
        if (text_delete.length > 0 || text_insert.length > 0) {
          // note that diff_commonPrefix and diff_commonSuffix are unicode-aware
          if (text_delete.length > 0 && text_insert.length > 0) {
            // Factor out any common prefixes.
            commonlength = diff_commonPrefix(text_insert, text_delete);
            if (commonlength !== 0) {
              if (previous_equality >= 0) {
                diffs[previous_equality].text += text_insert.substring(
                  0,
                  commonlength
                );
              } else {
                diffs.splice(
                  0,
                  0,
                  mk(DIFF_EQUAL, text_insert.substring(0, commonlength))
                );
                pointer++;
              }
              text_insert = text_insert.substring(commonlength);
              text_delete = text_delete.substring(commonlength);
            }
            // Factor out any common suffixes.
            commonlength = diff_commonSuffix(text_insert, text_delete);
            if (commonlength !== 0) {
              diffs[pointer].text =
                text_insert.substring(text_insert.length - commonlength) +
                diffs[pointer].text;
              text_insert = text_insert.substring(
                0,
                text_insert.length - commonlength
              );
              text_delete = text_delete.substring(
                0,
                text_delete.length - commonlength
              );
            }
          }
          // Delete the offending records and add the merged ones.
          const n = count_insert + count_delete;
          if (text_delete.length === 0 && text_insert.length === 0) {
            diffs.splice(pointer - n, n);
            pointer = pointer - n;
          } else if (text_delete.length === 0) {
            diffs.splice(pointer - n, n, mk(DIFF_INSERT, text_insert));
            pointer = pointer - n + 1;
          } else if (text_insert.length === 0) {
            diffs.splice(pointer - n, n, mk(DIFF_DELETE, text_delete));
            pointer = pointer - n + 1;
          } else {
            diffs.splice(
              pointer - n,
              n,
              mk(DIFF_DELETE, text_delete),
              mk(DIFF_INSERT, text_insert)
            );
            pointer = pointer - n + 2;
          }
        }
        if (pointer !== 0 && diffs[pointer - 1].op === DIFF_EQUAL) {
          // Merge this equality with the previous one.
          diffs[pointer - 1].text += diffs[pointer].text;
          diffs.splice(pointer, 1);
        } else {
          pointer++;
        }
        count_insert = 0;
        count_delete = 0;
        text_delete = "";
        text_insert = "";
        break;
      }
    }
  }
  if (diffs[diffs.length - 1].text === "") {
    diffs.pop(); // Remove the dummy entry at the end.
  }

  // Second pass: look for single edits surrounded on both sides by equalities
  // which can be shifted sideways to eliminate an equality.
  // e.g: A<ins>BA</ins>C -> <ins>AB</ins>AC
  let changes = false;
  pointer = 1;
  // Intentionally ignore the first and last element (don't need checking).
  while (pointer < diffs.length - 1) {
    if (
      diffs[pointer - 1].op === DIFF_EQUAL &&
      diffs[pointer + 1].op === DIFF_EQUAL
    ) {
      // This is a single edit surrounded by equalities.
      if (
        diffs[pointer].text.substring(
          diffs[pointer].text.length - diffs[pointer - 1].text.length
        ) === diffs[pointer - 1].text
      ) {
        // Shift the edit over the previous equality.
        diffs[pointer].text =
          diffs[pointer - 1].text +
          diffs[pointer].text.substring(
            0,
            diffs[pointer].text.length - diffs[pointer - 1].text.length
          );
        diffs[pointer + 1].text = diffs[pointer - 1].text + diffs[pointer + 1].text;
        diffs.splice(pointer - 1, 1);
        changes = true;
      } else if (
        diffs[pointer].text.substring(0, diffs[pointer + 1].text.length) ===
        diffs[pointer + 1].text
      ) {
        // Shift the edit over the next equality.
        diffs[pointer - 1].text += diffs[pointer + 1].text;
        diffs[pointer].text =
          diffs[pointer].text.substring(diffs[pointer + 1].text.length) +
          diffs[pointer + 1].text;
        diffs.splice(pointer + 1, 1);
        changes = true;
      }
    }
    pointer++;
  }
  // If shifts were made, the diff needs reordering and another shift sweep.
  if (changes) {
    diff_cleanupMerge(diffs, fix_unicode);
  }
}

// `str.charCodeAt(i)`, or NaN when i is out of range (as in JS).
/** function charCodeOrNaN(String, Int) => Number */
function charCodeOrNaN(str, i) {
  if (i < 0 || i >= str.length) {
    return NaN;
  }
  return str.charCodeAt(i);
}

function is_surrogate_pair_start(charCode) {
  return charCode >= 0xd800 && charCode <= 0xdbff;
}

function is_surrogate_pair_end(charCode) {
  return charCode >= 0xdc00 && charCode <= 0xdfff;
}

/** function starts_with_pair_end(String) => Boolean */
function starts_with_pair_end(str) {
  return is_surrogate_pair_end(charCodeOrNaN(str, 0));
}

/** function ends_with_pair_start(String) => Boolean */
function ends_with_pair_start(str) {
  return is_surrogate_pair_start(charCodeOrNaN(str, str.length - 1));
}

// Upstream's exported entry point: fix_unicode only at the top level.
function diff(text1, text2, cleanup) {
  return diff_main(text1, text2, cleanup, true);
}

// ---- CLI ---------------------------------------------------------------------

const HEX = "0123456789abcdef";

// `JSON.stringify(s)` for a string (ASCII input: see the note at the top).
/** function jsonString(String) => String */
function jsonString(s) {
  const out = ['"'];
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c >= 32 && c !== 34 && c !== 92) continue;
    if (start < i) out.push(s.slice(start, i));
    start = i + 1;
    if (c === 34) out.push('\\"');
    else if (c === 92) out.push("\\\\");
    else if (c === 10) out.push("\\n");
    else if (c === 13) out.push("\\r");
    else if (c === 9) out.push("\\t");
    else if (c === 8) out.push("\\b");
    else if (c === 12) out.push("\\f");
    else out.push("\\u00" + HEX.charAt(c >> 4) + HEX.charAt(c & 15));
  }
  if (start < s.length) out.push(s.slice(start));
  out.push('"');
  return out.join("");
}

function usage(msg) {
  if (msg) process.stderr.write("fastdiff: " + msg + "\n");
  process.stderr.write("usage: fastdiff old.txt new.txt [--cleanup]\n");
  process.exit(2);
}

function main() {
  const args = process.argv.slice(2);
  const files = [];
  let cleanup = false;
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === "--cleanup") cleanup = true;
    else if (a.startsWith("-") && a !== "-") usage("unknown option " + a);
    else files.push(a);
  }
  if (files.length !== 2) usage("");
  const text1 = readFileSync(files[0] === "-" ? "/dev/stdin" : files[0], "utf8");
  const text2 = readFileSync(files[1] === "-" ? "/dev/stdin" : files[1], "utf8");
  const diffs = diff(text1, text2, cleanup);

  let equal = 0;
  let deleted = 0;
  let inserted = 0;
  let edits = 0;
  for (let i = 0; i < diffs.length; i++) {
    const d = diffs[i];
    if (d.op === DIFF_EQUAL) equal += d.text.length;
    else {
      edits++;
      if (d.op === DIFF_DELETE) deleted += d.text.length;
      else inserted += d.text.length;
    }
  }
  const out = [
    "ops " + String(diffs.length) + ", edits " + String(edits) +
      ", equal " + String(equal) + ", deleted " + String(deleted) +
      ", inserted " + String(inserted) + "\n",
  ];
  for (let i = 0; i < diffs.length; i++) {
    const d = diffs[i];
    const sign = d.op === DIFF_EQUAL ? "=" : d.op === DIFF_DELETE ? "-" : "+";
    out.push(sign + jsonString(d.text) + "\n");
  }
  process.stdout.write(out.join(""));
}

main();
