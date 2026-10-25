import Dubon2026.SourceOriginalWeilCoverRealAbelPotential
import Dubon2026.SourceOriginalWeilCoverDifferentialReadingFaithfulness
import Dubon2026.SourceOriginalWeilCoverCompact

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> raw reciprocity period correction. Reuse the native actual Abel potential and compact maximum-principle argument; only the exact linear and integer-coordinate consumers required for correction are retained. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

theorem coefficients_eq_zero_of_annihilates_periods {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (hli : LinearIndependent ℂ b) (ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b, ℓ u = 0) : PeriodRealDual.coefficients ℓ = 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_compactSpace N n radicand baseDivisor hRadicand hOrders
  letI := place_connectedSpace N n radicand baseDivisor hRadicand hOrders
  obtain ⟨P₀⟩ : Nonempty (Place ℂ (EE)) := inferInstance
  obtain ⟨v, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (continuous_realAbelPotential N n radicand baseDivisor hRadicand hOrders b hb ℓ hℓ P₀).continuousOn
  obtain ⟨Φ, hΦ, hlocal⟩ := realAbelPotential_local N n radicand baseDivisor hRadicand hOrders b hb ℓ hℓ P₀ v
  have hlocmax : IsLocalMax (fun z => (Φ z).re) (0 : ℂ) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders v).1] with z hz
    have h1 := hlocal z hz
    have h2 : realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀ (placeFamily N n radicand baseDivisor hRadicand hOrders v z) ≤ realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀ v :=
      hmax (mem_univ _)
    linarith
  have hdiff : DifferentiableOn ℂ Φ (ball 0 (placeRadius N n radicand baseDivisor hRadicand hOrders v)) :=
    fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ Φ 0 := hdiff.analyticAt (ball_mem_nhds _ (place_spec N n radicand baseDivisor hRadicand hOrders v).1)
  have hconst := PeriodRealDual.eventually_eq_of_isLocalMax_re han hlocmax
  have hzero : ∀ᶠ z in 𝓝 (0 : ℂ),
      ∑ i, PeriodRealDual.coefficients ℓ i * readDifferential N n radicand baseDivisor hRadicand hOrders v (b i) z = 0 := by
    filter_upwards [hconst.eventually_nhds, ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders v).1]
      with z hz hzb
    have hd : HasDerivAt Φ 0 z :=
      (hasDerivAt_const z (Φ 0)).congr_of_eventuallyEq hz
    exact (hΦ z hzb).unique hd
  have hread : ∀ᶠ z in 𝓝 (0 : ℂ),
      readDifferential N n radicand baseDivisor hRadicand hOrders v (∑ i, PeriodRealDual.coefficients ℓ i • b i) z = 0 := by
    filter_upwards [hzero, ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders v).1] with z hz hzb
    rw [readDifferential_sum_smul N n radicand baseDivisor hRadicand hOrders v (PeriodRealDual.coefficients ℓ) b hb hzb, hz]
  have hsum := eq_zero_of_readDifferential_eventually_eq_zero N n radicand baseDivisor hRadicand hOrders v _ hread
  funext i
  exact Fintype.linearIndependent_iff.mp hli (PeriodRealDual.coefficients ℓ) hsum i

theorem eq_zero_of_annihilates_periods {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (hli : LinearIndependent ℂ b) (ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b, ℓ u = 0) : ℓ = 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hc := coefficients_eq_zero_of_annihilates_periods N n radicand baseDivisor hRadicand hOrders b hb hli ℓ hℓ
  apply LinearMap.ext
  intro w
  rw [PeriodRealDual.apply_eq_re_sum ℓ w, hc]
  simp


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
