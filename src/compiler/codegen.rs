#![allow(dead_code)]

use std::io::Write;

pub type Address = usize;

pub enum MemoryResourceDescriptor {
    StackVariable { address: Address },
    StaticVariable { address: Address },
}

pub trait CodeGeneratorTrait {
    fn produce_preamble(&mut self) -> Result<(), anyhow::Error>;
    fn produce_postamble(&mut self) -> Result<(), anyhow::Error>;
}

pub struct RiscVCodeGen<WriterT: Write> {
    writer: WriterT,
}

impl<WriterT: Write> RiscVCodeGen<WriterT> {
    pub fn new(writer: WriterT) -> Self {
        RiscVCodeGen { writer }
    }
}

impl<WriterT: Write> CodeGeneratorTrait for RiscVCodeGen<WriterT> {
    fn produce_preamble(&mut self) -> Result<(), anyhow::Error> {
        static PREAMBLE_CODE: &[u8] = include_str!("preamble.s").as_bytes();

        self.writer.write(PREAMBLE_CODE)?;

        Ok(())
    }

    fn produce_postamble(&mut self) -> Result<(), anyhow::Error> {
        static POSTAMBLE_CODE: &[u8] = include_str!("postamble.s").as_bytes();

        self.writer.write(POSTAMBLE_CODE)?;

        Ok(())
    }
}
