/// A stack for an LR parser automaton
pub struct Stack {
    elements: Vec<StackEntry>,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// An entry on the stack
struct StackEntry {
    state: usize,
    value: StackValue,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
/// A value in a stack entry, containing either a terminal or a parse tree node
pub enum StackValue {
    Terminal(usize),
    Node(usize),
}

impl Stack {
    /// Creates a new stack, prepopulated with an entry for the (augmented)
    /// start state
    pub fn new() -> Stack {
        // The entry for the (augmented) start state is never actually popped,
        // so any value will do for the node
        Stack {
            elements: Vec::from([StackEntry {
                state: 0,
                value: StackValue::Node(0),
            }]),
        }
    }

    /// Returns the state associated with the entry at the top of the stack
    pub fn peek_state(&self) -> usize {
        self.elements.last().unwrap().state
    }

    /// Pops the value at the top of the stack. Panics if an attempt is made
    /// to pop the (augmented) start state.
    pub fn pop(&mut self) -> StackValue {
        if self.elements.len() == 1 {
            panic!("stack empty");
        }
        self.elements.pop().unwrap().value
    }

    /// Pushes a terminal onto the stack
    pub fn push_terminal(&mut self, state: usize, terminal: usize) {
        self.elements.push(StackEntry {
            state,
            value: StackValue::Terminal(terminal),
        });
    }

    /// Pushes a node onto the stack
    pub fn push_node(&mut self, state: usize, node: usize) {
        self.elements.push(StackEntry {
            state,
            value: StackValue::Node(node),
        });
    }
}
