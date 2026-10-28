import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental
attribute [-instance] FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental
    {N : ℕ} [NeZero N] (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (CongruenceSubgroup.Gamma0 N) T z : ℂ))
    (E : CuspForm (CongruenceSubgroup.Gamma0 N) 2 → ℂ → ℂ)
    (hE : ∀ g z, E g z = ModularCurve.periodAlong N UpperHalfPlane.I (ofComplex z) g) :
    (∀ (T : ℝ) (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      Integrable fun z : ℂ => E g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I - fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Tendsto (fun T : ℝ =>
          Complex.I / Real.pi * (∫ z : ℂ, E g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I -
              fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * E g a * h T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) *
              ModularCurve.periodAlong N UpperHalfPlane.I s g)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental.solution
