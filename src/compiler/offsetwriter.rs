use std::io::Write;

// An object that facilitates writing text in haskell/TLA+
// indent style.
//
// This means that we need to be able to retrieve the
// current column and do further text output at a specifc
// column.
//
// It also means we need to be able to push a previous
// user's preference while outputting a subordinate
// part of the text and restore it.
//
// Example:
//
// Goober = /\ \A e \in Elevator : /\ \A f \in ElevatorState[e].buttonPressed : /\ \E p \in Person : /\ PersonState[p].location = e     \* Third context
//                                                                                                   /\ PersonState[p].destination = f  \* third context cont'd
//                                 /\ \A p \in Person : /\ \A e \in Elevator : /\ (PersonState[p].location = e /\ ElevatorState[e].floor /= PersonState[p].destination) => /\ ElevatorState[e].direction = GetDirection[ElevatorState[e].floor, PersonState[p].destination]            \* second of first context
//                                 /\ \A c \in ActiveElevatorCalls : PeopleWaiting[c.floor, c.direction] /= {} \* third of first context
//

pub trait ColumnWriter {
    fn get_column(&self) -> usize;
    fn current_offset(&self) -> usize;
    fn push_state(&mut self, column: usize);
    fn pop_state(&mut self) -> usize;
}

pub struct ColumnWriterPass<'a, W> where W: Write {
    w: &'a mut W,
    offset_stack: Vec<usize>,
    current_col: usize
}

impl<'a, W> ColumnWriterPass<'a, W> where W: Write {
    pub fn new(w: &'a mut W) -> Self {
        ColumnWriterPass {
            w: w,
            offset_stack: Vec::new(),
            current_col: 0
        }
    }
}

impl<'a, W> ColumnWriter for ColumnWriterPass<'a, W> where W: Write {
    fn get_column(&self) -> usize { self.current_col }
    fn current_offset(&self) -> usize {
        if self.offset_stack.is_empty() {
            0
        } else {
            self.offset_stack[self.offset_stack.len() - 1]
        }
    }
    fn push_state(&mut self, column: usize) {
        self.offset_stack.push(column);
    }
    fn pop_state(&mut self) -> usize {
        self.offset_stack.pop();
        self.current_offset()
    }
}

impl<'a, W> Write for ColumnWriterPass<'a, W> where W: Write {
    fn write(&mut self, s: &[u8]) -> Result<usize, std::io::Error> {
        let mut towrite = vec![0];
        let mut count = 0;
        let current_offset = self.current_offset();

        for by in s.iter() {
            if *by == '\n' as u8 {
                // After a newline, ensure that we're at the current offset col.
                towrite[0] = *by;
                count += self.w.write(&towrite)?;
                self.current_col = 0;
                continue;
            } else if *by == '\t' as u8 {
                towrite[0] = ' ' as u8;
                count += self.w.write(&towrite)?;
                self.current_col += 1;
                while self.current_col % 8 != 0 {
                    self.current_col += 1;
                    count += self.w.write(&towrite)?;
                }
                continue;
            }

            towrite[0] = ' ' as u8;
            while self.current_col < current_offset {
                self.current_col += 1;
                count += self.w.write(&towrite)?;
            }

            towrite[0] = *by;
            self.current_col += 1;
            count += self.w.write(&towrite)?;
        }

        Ok(count)
    }

    fn flush(&mut self) -> Result<(), std::io::Error> {
        self.w.flush()
    }
}
