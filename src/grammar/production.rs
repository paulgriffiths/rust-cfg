use super::symbol::Symbol;
use std::collections::HashSet;

/// A context-free grammar production
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Production {
    pub head: usize,
    pub body: Vec<Symbol>,
}

impl Production {
    /// Returns true if a production is an ϵ-production
    pub fn is_e(&self) -> bool {
        self.body.len() == 1 && matches!(self.body[0], Symbol::Empty)
    }

    /// Returns true if a production is a unit production
    pub fn is_unit(&self) -> bool {
        self.body.len() == 1 && matches!(self.body[0], Symbol::NonTerminal(_))
    }

    /// Returns a vector containing all productions generated by removing all
    /// combinations of nts. For example, if the production is P → 𝛼A𝛽B𝛾 and
    /// nts is {A, B}, then the returned list of productions will be
    /// [P → 𝛼𝛽B𝛾, P → 𝛼A𝛽𝛾, P → 𝛼𝛽𝛾]. If the production is P → A and A is in
    /// nts, then [P → ϵ] is returned, unless P is also in nts, in which case
    /// the empty vector is returned.
    pub fn remove_nullable_non_terminals(&self, nts: &HashSet<usize>) -> Vec<Production> {
        // Algorithm adapted from Sipser (2013) p.109

        // Handle productions which may be of the form P → A
        if self.body.len() == 1 {
            if !nts.contains(&self.head) {
                if let Symbol::NonTerminal(nt) = self.body[0] {
                    if nts.contains(&nt) {
                        return vec![self.to_e()];
                    }
                }
            }

            return Vec::new();
        }

        // Handle productions which cannot be of the form P → A
        let mut prods = vec![self.clone()];

        for (i, symbol) in self.body.iter().enumerate() {
            if let Symbol::NonTerminal(nt) = symbol {
                if nts.contains(nt) {
                    for j in 0..prods.len() {
                        let mut new_prod = prods[j].clone();
                        new_prod.body[i] = Symbol::Empty;
                        prods.push(new_prod);
                    }
                }
            }
        }

        // Remove the ϵs and return all but the source production
        for prod in prods.iter_mut().skip(1) {
            prod.body.retain(|s| *s != Symbol::Empty);
        }

        let n = prods.len();
        prods.into_iter().skip(1).take(n - 1).collect()
    }

    /// Returns a new production with the same head and the body containing
    /// only ϵ.
    pub fn to_e(&self) -> Production {
        Production {
            head: self.head,
            body: vec![Symbol::Empty],
        }
    }

    /// Returns a new production with the same head and the body containing
    /// only ϵ.
    pub fn to_head(&self, head: usize) -> Production {
        Production {
            head,
            body: self.body.clone(),
        }
    }
}
