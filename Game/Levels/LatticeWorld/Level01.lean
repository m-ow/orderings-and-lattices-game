import Game.Levels.PosetWorld.Level03

World "LatticeWorld"
Level 1

Title "Enter the Lattice (Supremum)"

/-- `le_sup_left` says that `a ≤ a ⊔ b`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Lattices"

/-- `le_sup_right` says that `b ≤ a ⊔ b`. -/
TheoremDoc le_sup_right as "le_sup_right" in "Lattices"

/-- `sup_le` says that if `a ≤ c` and `b ≤ c`, then `a ⊔ b ≤ c`. -/
TheoremDoc sup_le as "sup_le" in "Lattices"

NewTheorem le_sup_left le_sup_right sup_le

Introduction "
## Welcome to Lattices
A partial order can be very general. Consider a partial order of subsets of natural numbers containing only four elements:
`a={1}`, `b={2}`, `c={1,2,3}`, and `d={1,2,4}`.
Both `c` and `d` are upper bounds for `{a, b}`, but neither is the *least* upper bound because `c ≰ d` and `d ≰ c`.

A **Lattice** is a partial order where *any* two elements are guaranteed to have a **least upper bound** (Supremum, denoted `⊔`) and a **greatest lower bound** (Infimum, denoted `⊓`).

Here is the Mathlib API for the Supremum of `a` and `b`:
* `le_sup_left`: `a ≤ a ⊔ b`
* `le_sup_right`: `b ≤ a ⊔ b`
* `sup_le`: If `a ≤ c` and `b ≤ c`, then `a ⊔ b ≤ c`

Let's prove that the supremum operation is commutative.
"

variable {L : Type} [Lattice L]

Statement (a b : L) : a ⊔ b = b ⊔ a := by
  Hint "Every Lattice is a Partial Order! To prove two things are equal, start by typing `apply le_antisymm`."
  apply le_antisymm

  Hint "First, show `a ⊔ b ≤ b ⊔ a`. Since the left side is a supremum, use `apply sup_le`."
  apply sup_le

  Hint "Now you need `a ≤ b ⊔ a`. This matches the right-side rule of the supremum! Type `exact le_sup_right`."
  exact le_sup_right

  Hint "And for `b ≤ b ⊔ a`, use the left-side rule. Type `exact le_sup_left`."
  exact le_sup_left

  Hint "Halfway there! Now prove `b ⊔ a ≤ a ⊔ b`. Use `apply sup_le` again."
  apply sup_le

  Hint (hidden := true) "Type `exact le_sup_right`."
  exact le_sup_right

  Hint (hidden := true) "Type `exact le_sup_left`."
  exact le_sup_left

Conclusion "
Beautiful! You just proved that the supremum is commutative using the core axioms of a Lattice.
"
