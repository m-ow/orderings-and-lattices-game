import Game.Levels.LatticeWorld.Level04

World "CompleteLatticeWorld"
Level 1

Title "The Absolute Bottom"

/--
`bot_le` states that the bottom element `⊥` (bot) is less than or equal to any other element `a` in a complete lattice.
In symbols: `⊥ ≤ a`.
Because it is the absolute minimum, it is a lower bound for the entire universe.
-/
TheoremDoc bot_le as "bot_le" in "Complete Lattices"
NewTheorem bot_le

Introduction "
## Complete Lattices

A normal lattice has supremums for any 2 elements. A **Complete Lattice** has supremums and infimums for *every* subset, even infinite ones! (Think of the power set of a type).

Because the empty set `∅` also has a supremum, every complete lattice is guaranteed to have a least element, called `⊥` (bot), and a greatest element, called `⊤` (top). Let's look at `⊥`.
"
variable {L : Type} [CompleteLattice L]
Statement (a : L) : ⊥ ≤ a := by
  Hint "The property that `⊥` is smaller than everything is an axiom. Type `exact bot_le`."
  exact bot_le

Conclusion "Simple, but foundational."
