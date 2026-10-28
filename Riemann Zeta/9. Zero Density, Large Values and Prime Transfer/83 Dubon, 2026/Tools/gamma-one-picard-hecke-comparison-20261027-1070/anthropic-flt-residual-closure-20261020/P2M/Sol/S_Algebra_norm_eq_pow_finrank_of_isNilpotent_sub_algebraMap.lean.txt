import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import P2M.Util
namespace P2MW.S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

theorem solution {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]
