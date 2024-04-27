/// A stack for an iterative predictive parser automaton
pub struct Stack {
    elements: Vec<StackEntry>,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// An entry on the stack
struct StackEntry {
    parent: Option<usize>,
    value: StackValue,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// A value in a stack entry, containing either a terminal or a parse tree node
pub enum StackValue {
    Terminal(usize),
    NonTerminal(usize),
}

impl Stack {
    /// Creates a new, empty stack
    pub fn new() -> Stack {
        Stack {
            elements: Vec::new(),
        }
    }

    /// Returns true if the stack is empty
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the value at the top of the stack. Panics if the stack is empty.
    pub fn peek(&self) -> StackValue {
        self.elements.last().unwrap().value
    }

    /// Pops the value at the top of the stack and returns the ID of its
    /// parent. Panics if the stack is empty.
    pub fn pop(&mut self) -> Option<usize> {
        self.elements.pop().unwrap().parent
    }

    /// Pushes a terminal onto the stack. Every terminal has a parent.
    pub fn push_terminal(&mut self, parent: usize, terminal: usize) {
        self.elements.push(StackEntry {
            parent: Some(parent),
            value: StackValue::Terminal(terminal),
        });
    }

    /// Pushes a non-terminal onto the stack. All non-terminals except the
    /// first occurrence of the start symbol have a parent.
    pub fn push_non_terminal(&mut self, parent: Option<usize>, non_terminal: usize) {
        self.elements.push(StackEntry {
            parent,
            value: StackValue::NonTerminal(non_terminal),
        });
    }
}
