import Mathlib.RingTheory.Norm.Basic
import P2M.Util
import P2M.Sol.S_Algebra_norm_prod

theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_prod.solution
