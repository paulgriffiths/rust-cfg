#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// An entry on the stack
pub struct StackEntry {
    pub state: usize,
    pub value: StackValue,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// A value in a stack entry, containing either a terminal or a parse tree node
pub enum StackValue {
    Terminal(usize),
    Node(usize),
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// An entry in a canonical LR parse table
pub enum TableEntry {
    Goto(usize),
    Shift(usize),
    Reduce(usize),
    Accept,
    Error,
}

pub trait PTable {
    fn action(&self, state: usize, lookahead: usize) -> TableEntry;
    fn eof_index(&self) -> usize;
}
