import Game.Levels.CompleteLatticeWorld.Level01

World "CompleteLatticeWorld"
Level 2

Title "Hitting Rock Bottom"

/--
`le_bot_iff` states that an element is less than or equal to the bottom element `⊥` if and only if it is exactly `⊥`.
In symbols: `a ≤ ⊥ ↔ a = ⊥`.
Since nothing can be strictly smaller than the absolute minimum, anything claiming to be smaller must be the minimum itself.
-/
TheoremDoc le_bot_iff as "le_bot_iff" in "Complete Lattices"
NewTheorem le_bot_iff

Introduction "
If `⊥` is the absolute bottom, what happens if something claims to be less than or equal to `⊥`?
"
variable {L : Type} [CompleteLattice L]
Statement (a : L) : a ≤ ⊥ ↔ a = ⊥ := by
  Hint "Mathlib provides this exact equivalence. Type `exact le_bot_iff`."
  exact le_bot_iff

Conclusion "Exactly! Nothing can be strictly smaller than the bottom element."
