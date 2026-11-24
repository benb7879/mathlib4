module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Clique

def ramseyProperty (r s n : ℕ) : Prop :=
  ∀ m ≥ n,
    ∀ l : SimpleGraph.TopEdgeLabeling (Fin m) (Fin 2),
      ¬ (l.labelGraph 0).CliqueFree r
      ∨ ¬ (l.labelGraph 1).CliqueFree s

theorem ramsey_prop_inductivity (r s n m : ℕ) (h : ramseyProperty r s n) (hm : n ≤ m) : ramseyProperty r s m := by
  intro m' hm' l
  have hm' : n ≤ m' := Nat.le_trans hm hm'
  exact h m' hm' l

theorem ramsey_exists (r s : ℕ) :
    ∃ n, ramseyProperty r s n := by
  sorry

noncomputable def ramseyNumber (r s : ℕ) : ℕ := by
  classical
  exact Nat.find (ramsey_exists r s)


lemma labelGraph_swap_zero {m : ℕ}
    (l : SimpleGraph.TopEdgeLabeling (Fin m) (Fin 2)) :
    (l.compRight (Equiv.swap (0 : Fin 2) 1)).labelGraph 0 =
      l.labelGraph 1 := by
  ext x y
  simp only [
    SimpleGraph.TopEdgeLabeling.labelGraph_adj,
    SimpleGraph.EdgeLabeling.compRight_get,
    Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left
  ]

lemma labelGraph_swap_one {m : ℕ}
    (l : SimpleGraph.TopEdgeLabeling (Fin m) (Fin 2)) :
    (l.compRight (Equiv.swap (0 : Fin 2) 1)).labelGraph 1 =
      l.labelGraph 0 := by
  ext x y
  simp only [
    SimpleGraph.TopEdgeLabeling.labelGraph_adj,
    SimpleGraph.EdgeLabeling.compRight_get,
    Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_right
  ]

theorem ramseyProperty_symm (r s n : ℕ) :
    ramseyProperty r s n ↔ ramseyProperty s r n := by
  constructor
  · intro h m hm l
    have h' := h m hm
      (l.compRight (Equiv.swap (0 : Fin 2) 1))
    rw [labelGraph_swap_zero, labelGraph_swap_one] at h'
    exact Or.symm h'
  · intro h m hm l
    have h' := h m hm
      (l.compRight (Equiv.swap (0 : Fin 2) 1))
    rw [labelGraph_swap_zero, labelGraph_swap_one] at h'
    exact Or.symm h'
