import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed

theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K] (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) : ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.solution
