import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental
attribute [-instance] FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental
    {N : ℕ} [NeZero N] (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (CongruenceSubgroup.Gamma0 N) T z : ℂ)) :
    ∃ V : ℂ → ℂ,
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ (T : ℝ) (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
        Integrable fun z : ℂ => g (ofComplex z) * h T z *
          ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) ∧
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Tendsto (fun T : ℝ => 2 / Real.pi * ∫ z : ℂ, g (ofComplex z) * h T z *
            ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) atTop
          (𝓝 (∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) *
              ModularCurve.periodAlong N UpperHalfPlane.I s g)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental.solution
