import Game.Metadata

World "PosetWorld"
Level 1

Title "Introduction to Partial Orders"

/-- If the goal is a statement `P`, then `exact h` will solve the goal if `h` is a proof of `P`. -/
TacticDoc exact
NewTactic exact

/-- `le_refl a` is the proof that `a ≤ a` for any element `a` in a partial order. -/
TheoremDoc le_refl as "le_refl" in "Orderings"
NewTheorem le_refl

Introduction "
## Partial Order Definition

A *partial order* (or a partially ordered type) is a type `X` equipped with a concept of `≤` satisfying three fundamental axioms:
1. **Reflexivity:** `a ≤ a`
2. **Antisymmetry:** `a ≤ b → b ≤ a → a = b`
3. **Transitivity:** `a ≤ b → b ≤ c → a ≤ c`

Examples of partial orders include the natural numbers, the real numbers, and the type `Set X` of subsets of a type `X` (where `≤` means `⊆`).

Also, note that there is some strange `inst†` text in your objects. This simply means that your objects
are instances of certain classes, for example that X is a partial order.

## Goal for this level

Let's prove the most basic fact: every element is less than or equal to itself.
"

variable (X : Type) [PartialOrder X]

Statement (a : X) : a ≤ a := by
  Hint "Use the reflexivity axiom directly. Type `exact le_refl a`."
  exact le_refl a

Conclusion "Great start! You've used a native Mathlib theorem."
