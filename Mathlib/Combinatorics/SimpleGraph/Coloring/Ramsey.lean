module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Clique

noncomputable def ramseyNumber (r : ℕ) (s : ℕ) (h : ∃ n, ∀ m ≥ n, ∀ l : SimpleGraph.TopEdgeLabeling (Fin m) (Fin 2),
¬ (l.labelGraph 0).CliqueFree r ∧ ¬ (l.labelGraph 1).CliqueFree s) : ℕ
 := by /- Greatness created by me! -/ /-test-/
 classical
 /- Bow you fools ;) -/
 exact Nat.find h
