import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S₀ : Set ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (x : CohCarrier.H1 N H κ) (hx0 : x ≠ 0)
    (hx : x ∈ Submodule.span κ
      (Set.range fun G : CohCarrier.H1 N H ℤ => (Int.castAddHom κ).comp G))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ κ x) = lam ℓ • x) :
    ∃ (X : CohCarrier.H1 N H ℂ) (θ : ℕ → integralClosure ℤ ℂ) (φ' : integralClosure ℤ ℂ →+* κ),
      X ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ ℂ X) =
          ((θ ℓ : integralClosure ℤ ℂ) : ℂ) • X) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → φ' (θ ℓ) = lam ℓ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int.solution
