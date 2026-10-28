import Mathlib
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot

set_option autoImplicit false
open ExtCitation
theorem ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) (hg : g ξ = ξ) :
    cycloChar p g = 1 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot.solution
