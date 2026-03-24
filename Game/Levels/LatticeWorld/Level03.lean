import Game.Levels.LatticeWorld.Level02

World "LatticeWorld"
Level 3

Title "Sub-distributivity I"

Introduction "
In normal arithmetic, multiplication distributes over addition: `p * (q + r) = p * q + p * r`.
In set theory, intersection distributes over union: `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.

However, in a general Lattice, `⊓` DOES NOT always distribute over `⊔`. We only get an inequality, known as **sub-distributivity**.

Let's prove the first half: `(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)`.
*Tip: Look at the outermost operator of your goal to decide your first tactic.*
"

variable {L : Type} [Lattice L] (a b c : L)

Statement : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  Hint "The left side is a supremum (`⊔`). To show a supremum is `≤` something, use `apply sup_le`."
  apply sup_le

  Hint "Now we have two goals. Let's tackle `a ⊓ b ≤ a ⊓ (b ⊔ c)`. The right side is an infimum, so type `apply le_inf`."
  apply le_inf

  Hint "Type `exact inf_le_left`."
  exact inf_le_left

  Hint "You need `a ⊓ b ≤ b ⊔ c`. Step through `b` using `trans b`."
  trans b

  Hint "Type `exact inf_le_right`."
  exact inf_le_right

  Hint "Now `b ≤ b ⊔ c`. That's `exact le_sup_left`."
  exact le_sup_left

  Hint "Second half! `a ⊓ c ≤ a ⊓ (b ⊔ c)`. Type `apply le_inf`."
  apply le_inf

  Hint (hidden := true) "Type `exact inf_le_left`."
  exact inf_le_left

  Hint "Step through `c`. Type `trans c`."
  trans c

  Hint (hidden := true) "Type `exact inf_le_right`."
  exact inf_le_right

  Hint (hidden := true) "Type `exact le_sup_right`."
  exact le_sup_right

Conclusion "
Masterfully done. You are weaving together Supremums and Infimums like a pro.
"
