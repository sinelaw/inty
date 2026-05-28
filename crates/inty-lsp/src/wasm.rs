//! WebAssembly bindings around [`crate::Analysis`].
//!
//! The web playground uses these calls instead of running the JSON-RPC
//! LSP loop. Hover and inlay-hint queries hit the same Rust code paths
//! the stdio server uses — only the transport differs.

use wasm_bindgen::prelude::*;

use inty::error::IntyError;
use inty::frontends::Language;

use crate::analysis::{Analysis as RawAnalysis, HoverResult, InlayHintData};

#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
}

/// Opaque handle around an [`Analysis`]. Construct one per source
/// snapshot from JS, then ask it for inlay hints, hovers, and errors.
#[wasm_bindgen]
pub struct Analysis {
    inner: RawAnalysis,
    source: String,
}

fn parse_language(name: Option<String>) -> Language {
    match name.as_deref() {
        Some("python") | Some("py") => Language::Python,
        Some("lua") => Language::Lua,
        _ => Language::JavaScript,
    }
}

#[wasm_bindgen]
impl Analysis {
    /// Lex, parse, and infer `source`. Always returns an `Analysis`; on
    /// failure `errors()` is non-empty and queries return null/empty.
    ///
    /// `language` is `"javascript"` (the default), `"python"`, or
    /// `"lua"`. Unknown values fall back to JavaScript so older callers
    /// keep working.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str, language: Option<String>) -> Analysis {
        let lang = parse_language(language);
        Analysis {
            inner: RawAnalysis::check_lang(source, lang),
            source: source.to_string(),
        }
    }

    /// `true` iff the document type-checked without errors.
    #[wasm_bindgen(getter)]
    pub fn ok(&self) -> bool {
        self.inner.errors.is_empty()
    }

    /// Diagnostics as `[{message, start, end}]`. `start`/`end` are
    /// UTF-8 byte offsets into the source.
    pub fn errors(&self) -> Vec<JsValue> {
        self.inner.errors.iter().map(error_to_js).collect()
    }

    /// Inlay hints in the byte range `[start, end)`. Each hint is
    /// `{after_byte, label}` — `label` is the full text to render
    /// (already prefixed with `: ` or `-> `).
    pub fn inlay_hints(&self, start: usize, end: usize) -> Vec<JsValue> {
        self.inner
            .inlay_hints_in(start, end, &self.source)
            .into_iter()
            .map(inlay_to_js)
            .collect()
    }

    /// Hover at a UTF-8 byte offset. Returns
    /// `{name, start, end, type_str}` or `null` if no binding sits
    /// under the offset.
    pub fn hover(&self, byte_offset: usize) -> JsValue {
        match self.inner.hover_at(byte_offset) {
            Some(h) => hover_to_js(&h),
            None => JsValue::NULL,
        }
    }
}

fn error_to_js(error: &IntyError) -> JsValue {
    let (message, start, end) = match error {
        IntyError::Lex(e) => {
            let s = e.span();
            (e.to_string(), s.start, s.end)
        }
        IntyError::Parse(e) => {
            let s = e.span();
            (e.to_string(), s.start, s.end)
        }
        IntyError::Type(e) => {
            let s = e.span();
            (e.to_string(), s.start, s.end)
        }
    };
    let obj = js_sys::Object::new();
    js_sys::Reflect::set(&obj, &"message".into(), &message.into()).unwrap();
    js_sys::Reflect::set(&obj, &"start".into(), &JsValue::from_f64(start as f64)).unwrap();
    js_sys::Reflect::set(&obj, &"end".into(), &JsValue::from_f64(end as f64)).unwrap();
    obj.into()
}

fn inlay_to_js(hint: InlayHintData) -> JsValue {
    let obj = js_sys::Object::new();
    js_sys::Reflect::set(
        &obj,
        &"after_byte".into(),
        &JsValue::from_f64(hint.after_byte as f64),
    )
    .unwrap();
    js_sys::Reflect::set(&obj, &"label".into(), &hint.label.into()).unwrap();
    obj.into()
}

fn hover_to_js(h: &HoverResult) -> JsValue {
    let obj = js_sys::Object::new();
    js_sys::Reflect::set(&obj, &"name".into(), &h.name.clone().into()).unwrap();
    js_sys::Reflect::set(
        &obj,
        &"start".into(),
        &JsValue::from_f64(h.span.start as f64),
    )
    .unwrap();
    js_sys::Reflect::set(&obj, &"end".into(), &JsValue::from_f64(h.span.end as f64)).unwrap();
    js_sys::Reflect::set(&obj, &"type_str".into(), &h.type_str.clone().into()).unwrap();
    obj.into()
}
