import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient_j_mem_of_mem

theorem WeierstrassCurve.veluQuotient_j_mem_of_mem {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) (K : S) (T : Finset (F × F))
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K)
    (hT : ∀ P ∈ T, P.1 ∈ K ∧ P.2 ∈ K) (hΔ : (W.veluQuotient T).Δ ≠ 0) :
    haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient T).j ∈ K := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient_j_mem_of_mem.solution
