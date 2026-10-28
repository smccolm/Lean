import Mathlib.RingTheory.Norm.Basic
import P2M.Util
import P2M.Sol.S_Algebra_norm_of_subsingleton

theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_of_subsingleton.solution
