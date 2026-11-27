extern crate utf8;
use std::io::{self, BufRead, ErrorKind, Read};

/// A position-preserving read of a single-byte source, interrupted on its second read.
struct Source {
    reads: usize,
}
impl Read for Source {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        self.reads += 1;
        if self.reads == 2 { return Err(ErrorKind::Interrupted.into()); }
        if out.is_empty() { return Ok(0); }
        out[0] = b'x';
        Ok(1)
    }
}
struct Window {
    source: Source,
    preview: [u8; 1],
    consumed: bool,
}
impl BufRead for Window {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.consumed { return Ok(&[]); }
        // Refresh a view of the same byte without advancing the logical cursor.
        let count = self.source.read(&mut self.preview)?;
        Ok(&self.preview[..count])
    }
    fn consume(&mut self, count: usize) {
        assert!(count <= usize::from(!self.consumed));
        if count != 0 { self.consumed = true; }
    }
}
impl Read for Window {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.is_empty() { return Ok(0); }
        let count = self.fill_buf()?.read(out)?;
        self.consume(count);
        Ok(count)
    }
}
fn window() -> Window {
    Window { source: Source { reads: 0 }, preview: [0], consumed: false }
}
fn main() {
    let mut direct = window();
    assert_eq!(direct.fill_buf().unwrap(), b"x");
    assert_eq!(direct.fill_buf().unwrap_err().kind(), ErrorKind::Interrupted);
    assert_eq!(direct.fill_buf().unwrap(), b"x");
    let mut decoder = utf8::BufReadDecoder::new(window());
    match decoder.next_strict() {
        Some(Err(utf8::BufReadDecoderError::Io(e))) => assert_eq!(e.kind(), ErrorKind::Interrupted),
        other => panic!("unexpected {:?}", other)
    }
    // Success reproduces the missing byte on retry.
    assert!(decoder.next_strict().is_none());
}
