import Game.Levels.PosetWorld.Level02

World "PosetWorld"
Level 3

Title "The Cycle (Antisymmetry)"

/--
`apply thm` changes the current goal by applying a theorem backwards.
If the theorem says `A → B` and your goal is `B`, `apply thm` changes your goal to `A`.
-/
TacticDoc apply
NewTactic apply

/-- `le_antisymm` is the proof that if `a ≤ b` and `b ≤ a`, then `a = b`. -/
TheoremDoc le_antisymm as "le_antisymm" in "Orderings"
NewTheorem le_antisymm

Introduction "
Let's combine the axioms. What happens if you have a cycle of inequalities?
Suppose $a \\le b$, $b \\le c$, and $c \\le a$. Can you prove that $a = b$?

To prove equality in a partial order, you must use Antisymmetry, and then use your new knowledge of Transitivity to fill in the missing link.
"
variable {X : Type} [PartialOrder X]

Statement (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  Hint "To prove $a = b$, you need to show $a \\le b$ and $b \\le a$. Type `apply le_antisymm`."
  apply le_antisymm

  Hint "The first goal is $a \\le b$, which you already have! Type `exact hab`."
  exact hab

  Hint "Now you need $b \\le a$. You know $b \\le c$ and $c \\le a$. Time to use the transitivity tactic! Type `trans c`."
  trans c

  Hint "Type `exact hbc`."
  exact hbc

  Hint "Type `exact hca`."
  exact hca

Conclusion "
Fantastic! You successfully combined transitivity and antisymmetry to collapse a cycle into an equality.

You have mastered the basics of Mathlib's `PartialOrder`.
"
