import Game.Levels.LatticeWorld.Level03

World "LatticeWorld"
Level 4

Title "Sub-distributivity II"

Introduction "
Let's prove the dual sub-distributivity law: `a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c)`.

Notice that the outermost operator on the right side is an infimum (`⊓`). That should tell you exactly how to start!
"

variable {L : Type} [Lattice L] (a b c : L)

Statement : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  Hint "The right side is an infimum. Use `apply le_inf`."
  apply le_inf

  Hint "Goal 1: `a ⊔ (b ⊓ c) ≤ a ⊔ b`. The left side is a supremum. Use `apply sup_le`."
  apply sup_le

  Hint (hidden := true) "Type `exact le_sup_left`."
  exact le_sup_left

  Hint "You need `b ⊓ c ≤ a ⊔ b`. Step through `b`. Type `trans b`."
  trans b

  Hint (hidden := true) "Type `exact inf_le_left`."
  exact inf_le_left

  Hint (hidden := true) "Type `exact le_sup_right`."
  exact le_sup_right

  Hint "Goal 2: `a ⊔ (b ⊓ c) ≤ a ⊔ c`. Type `apply sup_le`."
  apply sup_le

  Hint (hidden := true) "Type `exact le_sup_left`."
  exact le_sup_left

  Hint "Step through `c`. Type `trans c`."
  trans c

  Hint (hidden := true) "Type `exact inf_le_right`."
  exact inf_le_right

  Hint (hidden := true) "Type `exact le_sup_right`."
  exact le_sup_right

Conclusion "
Excellent! You have formally verified both sub-distributivity laws for general lattices.

In some special lattices (like the subsets of a set), these inequalities actually become strict equalities. Those are called *Distributive Lattices*, but that's a story for another time!
"
