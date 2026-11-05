//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins where an abstraction of one branch only observes the frozen fields of
//! a shared borrow: matching a branch with the joined context gives it the
//! shared borrows it lacks.

pub enum Node {
    App(u32, u32),
    Arg(u32),
    Name(u32),
    Hole,
}

pub struct Engine<'a> {
    pub nodes: &'a mut Vec<Node>,
    pub names: &'a Vec<String>,
}

impl<'a> Engine<'a> {
    fn node(&self, e: u32) -> &Node {
        &self.nodes[e as usize]
    }

    fn name(&self, n: u32) -> &str {
        &self.names[n as usize]
    }

    pub fn show(&self, e: u32, depth: u32) -> String {
        if depth == 0 {
            return String::new();
        }
        let sub = |e| self.show(e, depth - 1);
        match self.node(e) {
            Node::App(f, a) => format!("({} {})", sub(*f), sub(*a)),
            Node::Arg(a) => sub(*a),
            Node::Name(n) => self.name(*n).to_string(),
            Node::Hole => String::new(),
        }
    }
}
