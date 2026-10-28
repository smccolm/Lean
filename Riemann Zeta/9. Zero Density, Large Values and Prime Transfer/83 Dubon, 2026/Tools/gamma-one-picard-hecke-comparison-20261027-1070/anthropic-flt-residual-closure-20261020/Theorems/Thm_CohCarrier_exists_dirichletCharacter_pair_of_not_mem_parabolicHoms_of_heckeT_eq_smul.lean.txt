import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.DirichletCharacter.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∉ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ M,
      (∀ u : (ZMod M)ˣ, ψ₁ (u : ZMod M) * ψ₂ (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M →
        a ℓ = ψ₁ (ℓ : ZMod M) + (ℓ : ℂ) * ψ₂ (ℓ : ZMod M)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.solution
