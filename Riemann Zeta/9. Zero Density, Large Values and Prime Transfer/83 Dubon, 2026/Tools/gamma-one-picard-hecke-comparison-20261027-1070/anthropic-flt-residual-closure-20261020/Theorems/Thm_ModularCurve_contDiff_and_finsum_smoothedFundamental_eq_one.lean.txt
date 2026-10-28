import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
attribute [-instance] FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

open UpperHalfPlane
open scoped MatrixGroups Topology ContDiff

theorem ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ) :
    (∀ n : ℕ∞, ContDiff ℝ n (ModularCurve.smoothedFundamental Γ T)) ∧
    HasCompactSupport (ModularCurve.smoothedFundamental Γ T) ∧
    tsupport (ModularCurve.smoothedFundamental Γ T) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 ≤ ModularCurve.smoothedFundamental Γ T z) ∧
    (∀ τ : ℍ, (Function.support fun γ : Γ =>
        ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite) ∧
    (∀ τ : ℍ,
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1) ∧
    (∀ τ : ℍ, max τ.im τ.im⁻¹ ≤ T →
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1) ∧
    (∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      ModularCurve.smoothedFundamental Γ T τ ≠ 0 →
        ModularCurve.smoothedFundamental Γ T ((δ • τ : ℍ) : ℂ) = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.solution
