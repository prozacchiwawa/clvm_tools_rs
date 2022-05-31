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
    fn getColumn(&self) -> usize;
    fn currentOffset(&self) -> usize;
    fn pushState(&mut self, column: usize);
    fn popState(&mut self) -> usize;
}

pub struct ColumnWriterPass<'a, W> where W: Write {
    w: &'a mut W,
    offsetStack: Vec<usize>,
    currentCol: usize
}

impl<'a, W> ColumnWriterPass<'a, W> where W: Write {
    fn new(w: &'a mut W) -> Self {
        ColumnWriterPass {
            w: w,
            offsetStack: Vec::new(),
            currentCol: 0
        }
    }
}

impl<'a, W> ColumnWriter for ColumnWriterPass<'a, W> where W: Write {
    fn getColumn(&self) -> usize { self.currentCol }
    fn currentOffset(&self) -> usize {
        if self.offsetStack.is_empty() {
            0
        } else {
            self.offsetStack[self.offsetStack.len() - 1]
        }
    }
    fn pushState(&mut self, column: usize) {
        self.offsetStack.push(column);
    }
    fn popState(&mut self) -> usize {
        self.offsetStack.pop();
        self.currentOffset()
    }
}

impl<'a, W> Write for ColumnWriterPass<'a, W> where W: Write {
    fn write(&mut self, s: &[u8]) -> Result<usize, std::io::Error> {
        let mut towrite = vec![0];
        let mut count = 0;
        for by in s.iter() {
            if *by == '\n' as u8 {
                // After a newline, ensure that we're at the current offset col.
                let currentOffset = self.currentOffset();
                towrite[0] = *by;
                self.currentCol = 0;
                count += self.w.write(&towrite)?;
                towrite[0] = ' ' as u8;
                while self.currentCol != currentOffset {
                    self.write(&towrite);
                }
                continue;
            } else if *by == '\t' as u8 {
                towrite[0] = ' ' as u8;
                count += self.write(&towrite)?;
                while self.currentCol % 8 != 0 {
                    count += self.write(&towrite)?;
                }
                continue;
            }

            towrite[0] = *by;
            count += self.w.write(&towrite)?;
        }

        Ok(count)
    }

    fn flush(&mut self) -> Result<(), std::io::Error> {
        self.w.flush()
    }
}
