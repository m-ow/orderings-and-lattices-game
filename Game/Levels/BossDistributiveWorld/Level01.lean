import Game.Levels.LatticeWorld.Level04

namespace LinearAlgebraGame

World "BossDistributiveWorld"
Level 1

Title "The Ultimate Puzzle"

/--
`constructor` splits an equivalence (`↔`) or a conjunction (`∧`) into two separate goals.
For `A ↔ B`, it gives you `A → B` and `B → A`.
-/
TacticDoc constructor

/--
`intro` brings variables and hypotheses from the goal into your local context.
If your goal is `∀ x, P x → Q`, typing `intro x h` gives you `x` and a proof `h : P x`, leaving `Q` as your new goal.
-/
TacticDoc intro

/--
`rw` (rewrite) changes a part of your goal using an equality (`=`) or equivalence (`↔`).
If you have a theorem `thm : x = y`, typing `rw [thm]` replaces `x` with `y` in your goal.
To replace `y` with `x` (rewriting right-to-left), use the left arrow: `rw [← thm]`.
(You can type `←` by typing `\l` or `\leftarrow`).
You can also rewrite using hypotheses from your context.
-/
TacticDoc rw

NewTactic constructor intro rw

/--
`sup_comm` states that the supremum operation is commutative: `a ⊔ b = b ⊔ a`.
The order of the elements does not matter when finding their least upper bound.
-/
TheoremDoc sup_comm as "sup_comm" in "Lattices"

/--
`inf_comm` states that the infimum operation is commutative: `a ⊓ b = b ⊓ a`.
The order of the elements does not matter when finding their greatest lower bound.
-/
TheoremDoc inf_comm as "inf_comm" in "Lattices"

/--
`sup_inf_self` is one of the fundamental **Absorption Laws** in lattice theory.
It states that taking the supremum of `a` and `a ⊓ b` simply returns `a`.
In symbols: `a ⊔ (a ⊓ b) = a`.
(Since `a ⊓ b` is already less than or equal to `a`, adding it to `a` via supremum does nothing).
-/
TheoremDoc sup_inf_self as "sup_inf_self" in "Lattices"

/--
`inf_sup_self` is the dual **Absorption Law**.
It states that taking the infimum of `a` and `a ⊔ b` simply returns `a`.
In symbols: `a ⊓ (a ⊔ b) = a`.
(Since `a ⊔ b` is already greater than or equal to `a`, intersecting it with `a` via infimum just leaves `a`).
-/
TheoremDoc inf_sup_self as "inf_sup_self" in "Lattices"

/--
`sup_assoc` states that the supremum operation is associative:
`(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)`.
You can shift the parentheses when taking the supremum of three or more elements.
-/
TheoremDoc sup_assoc as "sup_assoc" in "Lattices"

/--
`inf_assoc` states that the infimum operation is associative:
`(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)`.
You can shift the parentheses when taking the infimum of three or more elements.
-/
TheoremDoc inf_assoc as "inf_assoc" in "Lattices"

NewTheorem sup_comm inf_comm sup_inf_self inf_sup_self sup_assoc inf_assoc
TheoremTab "Lattices"

Introduction "
You have reached one of the final challenges.

In a general lattice, neither `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)` nor `a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)` holds.
However, there is a beautiful and surprising mathematical truth: **one of these equalities holds if and only if the other one does!**

This is a true boss fight. Grab a piece of paper, plan your strategy, and prove that these two distributive laws are perfectly equivalent.

### New Tactics for the Boss
* **`constructor`**: Since the goal is an `↔` (if and only if), this tactic splits the fight into two phases: Left-to-Right and Right-to-Left.
* **`intro`**: When your goal starts with `∀ a b c, ...` or an implication `A → B`, `intro` pulls those variables and assumptions into your inventory so you can use them.
* **`rw` (rewrite)**: This tactic uses equations to substitute parts of your goal. For example, `rw [sup_comm a b]` replaces `a ⊔ b` with `b ⊔ a`. To use an equation backward, use the left arrow inside the brackets: `rw [← sup_assoc]`.
"

variable {L : Type} [Lattice L]
Statement :
  (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔
  (∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c) := by

  Hint (hidden := true) "Start by splitting the equivalence into two implications. Type `constructor`."
  constructor

  Hint (hidden := true) "Phase 1: Assume the first law and prove the second. Type `intro h a b c` to bring the hypothesis and variables into your context."
  intro h a b c

  Hint (hidden := true) "Instead of messy inequalities, let's use algebra (`rw`). We'll transform the right side using our hypothesis `h`. Type `rw [h (a ⊓ b) a c]`."
  rw [h (a ⊓ b) a c]

  Hint (hidden := true) "Let's apply the absorption law `a ⊔ a ⊓ b = a` to the first bracket. First, swap the terms. Type `rw [sup_comm (a ⊓ b) a]`."
  rw [sup_comm (a ⊓ b) a]

  Hint (hidden := true) "Now absorb! Type `rw [sup_inf_self]`."
  rw [sup_inf_self]

  Hint (hidden := true) "Let's prepare the second bracket to use `h` again. Type `rw [sup_comm (a ⊓ b) c]`."
  rw [sup_comm (a ⊓ b) c]

  Hint (hidden := true) "Now we can apply `h` on the inside. Type `rw [h c a b]`."
  rw [h c a b]

  Hint (hidden := true) "Shift the parentheses using associativity. Type `rw [← inf_assoc]`."
  rw [← inf_assoc]

  Hint (hidden := true) "Commute the inside to set up the next absorption. Type `rw [sup_comm c a]`."
  rw [sup_comm c a]

  Hint (hidden := true) "Apply the other absorption law `a ⊓ (a ⊔ b) = a`. Type `rw [inf_sup_self]`."
  rw [inf_sup_self]

  Hint (hidden := true) "Just one swap left to match the goal! Type `rw [sup_comm c b]`."
  rw [sup_comm c b]

  Hint (hidden := true) "Phase 2! The reverse direction. Type `intro h a b c`."
  intro h a b c

  Hint (hidden := true) "We do the exact same dance, perfectly mirrored. Type `rw [h (a ⊔ b) a c]`."
  rw [h (a ⊔ b) a c]

  Hint (hidden := true) "Type `rw [inf_comm (a ⊔ b) a]`."
  rw [inf_comm (a ⊔ b) a]

  Hint (hidden := true) "Type `rw [inf_sup_self]`."
  rw [inf_sup_self]

  Hint (hidden := true) "Type `rw [inf_comm (a ⊔ b) c]`."
  rw [inf_comm (a ⊔ b) c]

  Hint (hidden := true) "Type `rw [h c a b]`."
  rw [h c a b]

  Hint (hidden := true) "Type `rw [← sup_assoc]`."
  rw [← sup_assoc]

  Hint (hidden := true) "Type `rw [inf_comm c a]`."
  rw [inf_comm c a]

  Hint (hidden := true) "Type `rw [sup_inf_self]`."
  rw [sup_inf_self]

  Hint (hidden := true) "Type `rw [inf_comm c b]`."
  rw [inf_comm c b]

Conclusion "
Incredible! You have conquered the distributive equivalence theorem. You are a true master of Lattices.
"

end LinearAlgebraGame
