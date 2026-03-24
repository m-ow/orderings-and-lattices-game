import Game.Levels.LatticeWorld.Level01

World "LatticeWorld"
Level 2

Title "Going Down (The Infimum)"

/-- `inf_le_left` says that `a ⊓ b ≤ a`. -/
TheoremDoc inf_le_left as "inf_le_left" in "Lattices"

/-- `inf_le_right` says that `a ⊓ b ≤ b`. -/
TheoremDoc inf_le_right as "inf_le_right" in "Lattices"

/-- `le_inf` says that if `a ≤ b` and `a ≤ c`, then `a ≤ b ⊓ c`. -/
TheoremDoc le_inf as "le_inf" in "Lattices"

NewTheorem inf_le_left inf_le_right le_inf

Introduction "
Every pair of elements in a lattice also has a **Greatest Lower Bound** or **Infimum**, denoted by `⊓`.

Here is the API for the Infimum:
* `inf_le_left`: `a ⊓ b ≤ a` (It is a lower bound for `a`)
* `inf_le_right`: `a ⊓ b ≤ b` (It is a lower bound for `b`)
* `le_inf`: If `a ≤ b` and `a ≤ c`, then `a ≤ b ⊓ c` (It is the *greatest* lower bound)

Let's prove that the infimum is monotonic: if $b \\le c$, then picking the infimum with $a$ preserves the inequality.
"

variable {L : Type} [Lattice L]

Statement (a b c : L) (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  Hint "You need to show that something is less than or equal to an infimum. Use `apply le_inf`."
  apply le_inf

  Hint "First goal: `a ⊓ b ≤ a`. This is exactly the left rule of the infimum. Type `exact inf_le_left`."
  exact inf_le_left

  Hint "Second goal: `a ⊓ b ≤ c`. You know `a ⊓ b ≤ b` and `b ≤ c` (which is `h`). Let's chain them! Type `trans b`."
  trans b

  Hint "Type `exact inf_le_right`."
  exact inf_le_right

  Hint "And close it with your hypothesis. Type `exact h`."
  exact h

Conclusion "
Great! You used `trans` elegantly to connect the infimum's property with your hypothesis.
"
