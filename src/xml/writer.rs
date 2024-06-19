use std::io;

use crate::{Array, Data, Date, Dictionary, Integer, PlistWrite, Uid};

pub(crate) struct XmlWriter<W> {
    sink: W,
    int_buf: itoa::Buffer,
    float_buf: ryu::Buffer,
}

impl<W: io::Write> PlistWrite for XmlWriter<W> {
    fn write_bool(&mut self, boolean: bool) -> io::Result<()> {
        let xml = if boolean { "<true/>" } else { "<false/>" };
        self.sink.write_all(xml.as_bytes())
    }

    fn write_array(&mut self, array: &Array) -> io::Result<()> {
        if !array.is_empty() {
            self.sink.write_all(b"<array>")?;
            array.iter().try_for_each(|value| self.write_value(value))?;
            self.sink.write_all(b"</array>")
        } else {
            self.sink.write_all(b"<array/>")
        }
    }

    fn write_dictionary(&mut self, dict: &Dictionary) -> io::Result<()> {
        if !dict.is_empty() {
            self.sink.write_all(b"<dict>")?;
            dict.iter().try_for_each(|(key, value)| {
                write!(self.sink, "<key>{key}</key>")?;
                self.write_value(value)
            })?;
            self.sink.write_all(b"</dict>")
        } else {
            self.sink.write_all(b"<dict/>")
        }
    }

    fn write_data(&mut self, _data: Data) -> io::Result<()> {
        self.sink.write_all(b"<data>")?;
        todo!("can we handle mismatched encodings without allocating?");
    }

    fn write_date(&mut self, _date: Date) -> io::Result<()> {
        todo!("can we handle dates without allocating?");
    }

    fn write_float(&mut self, float: f64) -> io::Result<()> {
        let float = self.float_buf.format(float);
        write!(self.sink, "<float>{float}</float>")
    }

    fn write_integer(&mut self, int: Integer) -> io::Result<()> {
        let int = self.int_buf.format(int.0);
        write!(self.sink, "<integer>{int}</integer>")
    }

    fn write_real(&mut self, real: f64) -> io::Result<()> {
        let real = self.float_buf.format(real);
        write!(self.sink, "<real>{real}</real>")
    }

    fn write_string(&mut self, string: &str) -> io::Result<()> {
        if !string.is_empty() {
            write!(self.sink, "<string>{string}</string>")
        } else {
            self.sink.write_all(b"<string/>")
        }
    }

    fn write_uid(&mut self, uid: Uid) -> io::Result<()> {
        let uid = self.int_buf.format(uid.0);
        write!(self.sink, "<uid>{uid}</uid>")
    }
}

impl<W: io::Write> From<W> for XmlWriter<W> {
    fn from(writeable: W) -> Self {
        Self {
            sink: writeable,
            int_buf: itoa::Buffer::new(),
            float_buf: ryu::Buffer::new(),
        }
    }
}
