import Game.Levels.PosetWorld
import Game.Levels.LatticeWorld
import Game.Levels.BossDistributiveWorld
import Game.Levels.CompleteLatticeWorld

Title "Orderings & Lattices Game"

Introduction "
Welcome to the Orderings & Lattices Game!
This interactive experience bridges the gap between basic logic and abstract algebra.
"

Info "Built with Lean 4 and Mathlib."

Dependency PosetWorld → LatticeWorld
Dependency LatticeWorld → BossDistributiveWorld
Dependency LatticeWorld → CompleteLatticeWorld

MakeGame
