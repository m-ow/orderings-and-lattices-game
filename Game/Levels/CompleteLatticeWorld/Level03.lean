import Game.Levels.CompleteLatticeWorld.Level02

World "CompleteLatticeWorld"
Level 3

Title "Monotonicity of the Infinite"

/--
`sSup_le_sSup` states that the set supremum operation is monotonic.
If a set `S` is a subset of `T` (`S ⊆ T`), then the supremum of `S` must be less than or equal to the supremum of `T`.
In symbols: `sSup S ≤ sSup T`.
(Adding more elements to a set can only push its upper bound higher, never lower).
-/
TheoremDoc sSup_le_sSup as "sSup_le_sSup" in "Complete Lattices"
NewTheorem sSup_le_sSup

Introduction "
The supremum of a set `S` is denoted `sSup S`.
Just like the regular supremum, the set supremum is monotonic. If a set `S` is a subset of `T`, then the supremum of `S` must be less than or equal to the supremum of `T`.
"
variable {L : Type} [CompleteLattice L]
Statement (S T : Set L) (h : S ⊆ T) : sSup S ≤ sSup T := by
  Hint "Apply the Mathlib theorem for set supremum monotonicity. Type `exact sSup_le_sSup h`."
  exact sSup_le_sSup h

Conclusion "
Flawless victory! You have grasped the mechanics of Complete Lattices and bounds of infinite sets.
Your formalization journey is complete.
"
