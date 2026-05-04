/* tslint:disable */
/* eslint-disable */

export class Analysis {
  free(): void;
  [Symbol.dispose](): void;
  /**
   * Inlay hints in the byte range `[start, end)`. Each hint is
   * `{after_byte, label}` — `label` is the full text to render
   * (already prefixed with `: ` or `-> `).
   */
  inlay_hints(start: number, end: number): any[];
  /**
   * Lex, parse, and infer `source`. Always returns an `Analysis`; on
   * failure `errors()` is non-empty and queries return null/empty.
   */
  constructor(source: string);
  /**
   * Hover at a UTF-8 byte offset. Returns
   * `{name, start, end, type_str}` or `null` if no binding sits
   * under the offset.
   */
  hover(byte_offset: number): any;
  /**
   * Diagnostics as `[{message, start, end}]`. `start`/`end` are
   * UTF-8 byte offsets into the source.
   */
  errors(): any[];
  /**
   * `true` iff the document type-checked without errors.
   */
  readonly ok: boolean;
}

export function init(): void;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
  readonly memory: WebAssembly.Memory;
  readonly __wbg_analysis_free: (a: number, b: number) => void;
  readonly analysis_errors: (a: number) => [number, number];
  readonly analysis_hover: (a: number, b: number) => any;
  readonly analysis_inlay_hints: (a: number, b: number, c: number) => [number, number];
  readonly analysis_new: (a: number, b: number) => number;
  readonly analysis_ok: (a: number) => number;
  readonly init: () => void;
  readonly __wbindgen_malloc: (a: number, b: number) => number;
  readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
  readonly __wbindgen_free: (a: number, b: number, c: number) => void;
  readonly __wbindgen_exn_store: (a: number) => void;
  readonly __externref_table_alloc: () => number;
  readonly __wbindgen_externrefs: WebAssembly.Table;
  readonly __externref_drop_slice: (a: number, b: number) => void;
  readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
* Instantiates the given `module`, which can either be bytes or
* a precompiled `WebAssembly.Module`.
*
* @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
*
* @returns {InitOutput}
*/
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
* If `module_or_path` is {RequestInfo} or {URL}, makes a request and
* for everything else, calls `WebAssembly.instantiate` directly.
*
* @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
*
* @returns {Promise<InitOutput>}
*/
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
