import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import P2M.Util
import P2M.Sol.S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

theorem Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap.solution
