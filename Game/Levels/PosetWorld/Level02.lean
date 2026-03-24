import Game.Levels.PosetWorld.Level01

World "PosetWorld"
Level 2

Title "The Chain of Inequalities"

/--
The `trans` tactic allows you to chain transitive relations like `=`, `≤`, or `<`.
If your goal is `a ≤ c`, typing `trans b` will split it into two goals: `a ≤ b` and `b ≤ c`.
-/
TacticDoc trans
NewTactic trans

/-- `le_trans` states that if `a ≤ b` and `b ≤ c`, then `a ≤ c`. -/
TheoremDoc le_trans as "le_trans" in "Orderings"
NewTheorem le_trans

Introduction "
You can prove transitivity directly using the axiom `le_trans`,
but Mathlib provides a very powerful tactic called `trans`
that makes chaining inequalities much more intuitive.

Let `a, b, c, d` be arbitrary elements of our partial order `X`.
Suppose you have a chain of inequalities.
Let's see how `trans` helps you break the problem down into manageable steps.
"

variable (X : Type) [PartialOrder X]

Statement (a b c d : X) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  Hint "Your goal is `a ≤ d`. You want to step through `c` first. Type `trans c`."
  trans c

  Hint "Lean split the goal! Now you need to prove `a ≤ c`. You can use `trans` again to step through `b`. Type `trans b`."
  trans b

  Hint "Now the goals match your hypotheses perfectly. Type `exact hab`."
  exact hab

  Hint "Type `exact hbc`."
  exact hbc

  Hint "And finally, type `exact hcd`."
  exact hcd

Conclusion "
Excellent! The `trans` tactic is a lifesaver when dealing with chains of inequalities.
"
