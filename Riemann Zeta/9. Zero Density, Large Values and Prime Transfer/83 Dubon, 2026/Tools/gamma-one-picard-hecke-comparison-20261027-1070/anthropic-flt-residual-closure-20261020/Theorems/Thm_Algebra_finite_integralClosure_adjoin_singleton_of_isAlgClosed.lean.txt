import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed

theorem Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed.solution
