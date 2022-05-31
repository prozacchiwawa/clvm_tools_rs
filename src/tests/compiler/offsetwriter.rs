use std::io::Write;
use bytes::BufMut;

use crate::compiler::offsetwriter::{ColumnWriter, ColumnWriterPass};

struct MemWriter<'a> {
    cw: ColumnWriterPass<'a, bytes::buf::Writer<Vec<u8>>>
}

impl<'a> MemWriter<'a> {
    pub fn new(buf: &'a mut bytes::buf::Writer<Vec<u8>>) -> Self {
        MemWriter {
            cw: ColumnWriterPass::new(buf)
        }
    }
}

impl<'a> Write for MemWriter<'a> {
    fn write(&mut self, s: &[u8]) -> Result<usize, std::io::Error> {
        self.cw.write(s)
    }

    fn flush(&mut self) -> Result<(), std::io::Error> {
        self.cw.flush()
    }
}

impl<'a> ColumnWriter for MemWriter<'a> {
    fn get_column(&self) -> usize {
        self.cw.get_column()
    }
    fn current_offset(&self) -> usize {
        self.cw.current_offset()
    }
    fn push_state(&mut self, column: usize) {
        self.cw.push_state(column)
    }
    fn pop_state(&mut self) -> usize {
        self.cw.pop_state()
    }
}

#[test]
fn test_writer() {
    let mut writer = vec![].writer();
    let mut w = MemWriter::new(&mut writer);
    w.write("foo\nbar = ".as_bytes()).expect("should succeed");
    w.push_state(w.get_column());
    w.write("ax\nbx\ncx\n".as_bytes()).expect("!");
    w.pop_state();
    w.write("end\n".as_bytes()).expect("!");
    w.flush().expect("!");
    let buf = writer.into_inner();
    assert_eq!(buf, indoc!{
        "foo
         bar = ax
               bx
               cx
         end
        "}.as_bytes());
}
