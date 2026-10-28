import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero

set_option autoImplicit false

theorem CohCarrier.mem_span_int_of_forall_isOfFinOrder_apply_eq_zero
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (κ : Type) [CommRing κ]
    (x : CohCarrier.H1 N H κ)
    (hx : ∀ γ : ↥(CohCarrier.GammaH N H), IsOfFinOrder γ → x (Additive.ofMul γ) = 0) :
    x ∈ Submodule.span κ (Set.range fun G : CohCarrier.H1 N H ℤ => (Int.castAddHom κ).comp G) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero.solution
