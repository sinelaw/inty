//! Minimal LSP framing: `Content-Length` headers around UTF-8 JSON bodies.

use std::io::{self, BufRead, Write};

use serde_json::Value;

/// Read one LSP message from `reader`. Returns `Ok(None)` on clean EOF
/// before any header bytes; returns `Err` on malformed framing or invalid
/// JSON.
pub fn read_message<R: BufRead>(reader: &mut R) -> io::Result<Option<Value>> {
    let mut content_length: Option<usize> = None;

    loop {
        let mut line = String::new();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            // EOF before/inside header block.
            if content_length.is_none() {
                return Ok(None);
            }
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "EOF inside LSP header block",
            ));
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some(rest) = trimmed
            .strip_prefix("Content-Length:")
            .or_else(|| trimmed.strip_prefix("content-length:"))
        {
            let n: usize = rest.trim().parse().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid Content-Length: {}", e),
                )
            })?;
            content_length = Some(n);
        }
        // All other headers (Content-Type, etc.) are ignored.
    }

    let len = content_length.ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length header")
    })?;

    let mut buf = vec![0u8; len];
    reader.read_exact(&mut buf)?;

    let value: Value = serde_json::from_slice(&buf)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("invalid JSON: {}", e)))?;

    Ok(Some(value))
}

/// Write one LSP message to `writer`, with the required header block, and
/// flush.
pub fn write_message<W: Write>(writer: &mut W, msg: &Value) -> io::Result<()> {
    let body = serde_json::to_vec(msg)?;
    write!(writer, "Content-Length: {}\r\n\r\n", body.len())?;
    writer.write_all(&body)?;
    writer.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn roundtrip_message() {
        let msg = serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "ping"});
        let mut buf = Vec::new();
        write_message(&mut buf, &msg).unwrap();

        let mut cursor = Cursor::new(buf);
        let parsed = read_message(&mut cursor).unwrap().unwrap();
        assert_eq!(parsed, msg);
    }

    #[test]
    fn read_eof_before_headers() {
        let mut cursor = Cursor::new(Vec::<u8>::new());
        assert!(read_message(&mut cursor).unwrap().is_none());
    }

    #[test]
    fn read_handles_lowercase_header() {
        let body = br#"{"jsonrpc":"2.0"}"#;
        let mut input = Vec::new();
        write!(input, "content-length: {}\r\n\r\n", body.len()).unwrap();
        input.extend_from_slice(body);

        let mut cursor = Cursor::new(input);
        let msg = read_message(&mut cursor).unwrap().unwrap();
        assert_eq!(msg["jsonrpc"], "2.0");
    }
}
