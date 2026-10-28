import Mathlib
import P2M.Util
import P2M.Sol.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center

set_option autoImplicit false
theorem ModularGroup.exists_mulEquiv_freeProduct_quotient_center :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) := by p2m_exact_reverting @_root_.P2MW.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.solution
