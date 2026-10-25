import Dubon2026.SourceOriginalWeilCoverDifferentialReadingLinear
import Dubon2026.SourceOriginalWeilCoverLocalAbelJacobi
import Dubon2026.SourcePeriodRealDual

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

/-- Applying a real functional to the actual chosen-path Abel-Jacobi vector. -/
def realAbelPotential {kDim : ℕ} (b : Fin kDim → Ω[EE⁄ℂ])
    (ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ) (P₀ P : Place ℂ (EE)) : ℝ :=
  ℓ (abelJacobiVec N n radicand baseDivisor hRadicand hOrders b P₀ P)

theorem realAbelPotential_local {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b, ℓ u = 0)
    (P₀ v : Place ℂ (EE)) :
    ∃ Φ : ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) (placeRadius N n radicand baseDivisor hRadicand hOrders v),
        HasDerivAt Φ (∑ i, PeriodRealDual.coefficients ℓ i * readDifferential N n radicand baseDivisor hRadicand hOrders v (b i) z) z) ∧
      ∀ z ∈ ball (0 : ℂ) (placeRadius N n radicand baseDivisor hRadicand hOrders v),
        realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀ (placeFamily N n radicand baseDivisor hRadicand hOrders v z) =
          realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀ v + ((Φ z).re - (Φ 0).re) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨Ψ, hΨ, hlocal⟩ := exists_abelJacobiVec_chart_primitive N n radicand baseDivisor hRadicand hOrders b hb P₀ v
  refine ⟨fun z => ∑ i, PeriodRealDual.coefficients ℓ i * Ψ i z,
    fun z hz => HasDerivAt.fun_sum fun i _ => (hΨ i z hz).const_mul _, ?_⟩
  intro z hz
  have h := hℓ _ (hlocal z hz)
  rw [map_sub, map_sub] at h
  have hs : ℓ (fun i => Ψ i z - Ψ i 0) =
      (∑ i, PeriodRealDual.coefficients ℓ i * Ψ i z).re -
        (∑ i, PeriodRealDual.coefficients ℓ i * Ψ i 0).re := by
    rw [PeriodRealDual.apply_eq_re_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
  rw [hs] at h
  change ℓ (abelJacobiVec N n radicand baseDivisor hRadicand hOrders b P₀ (placeFamily N n radicand baseDivisor hRadicand hOrders v z)) =
    ℓ (abelJacobiVec N n radicand baseDivisor hRadicand hOrders b P₀ v) + _
  linarith

theorem continuous_realAbelPotential {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (ℓ : (Fin kDim → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b, ℓ u = 0)
    (P₀ : Place ℂ (EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    Continuous (realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨Φ, hΦ, hlocal⟩ := realAbelPotential_local N n radicand baseDivisor hRadicand hOrders b hb ℓ hℓ P₀ v
  have hΦc : ContinuousAt Φ (placeChart N n radicand baseDivisor hRadicand hOrders v v) := by
    rw [placeChart_self]
    exact (hΦ 0 (mem_ball_self (place_spec N n radicand baseDivisor hRadicand hOrders v).1)).continuousAt
  have hc : ContinuousAt (fun w => Φ (placeChart N n radicand baseDivisor hRadicand hOrders v w)) v :=
    hΦc.comp (continuousAt_placeChart N n radicand baseDivisor hRadicand hOrders v v (mem_placeChart_source N n radicand baseDivisor hRadicand hOrders v))
  have hr : ContinuousAt (fun w => (Φ (placeChart N n radicand baseDivisor hRadicand hOrders v w)).re) v :=
    Complex.continuous_re.continuousAt.comp hc
  have hcont : ContinuousAt (fun w => realAbelPotential N n radicand baseDivisor hRadicand hOrders b ℓ P₀ v +
      ((Φ (placeChart N n radicand baseDivisor hRadicand hOrders v w)).re - (Φ 0).re)) v :=
    continuousAt_const.add (hr.sub continuousAt_const)
  apply hcont.congr
  filter_upwards [placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders v] with w hw
  have he := hlocal (placeChart N n radicand baseDivisor hRadicand hOrders v w) ((placeChart N n radicand baseDivisor hRadicand hOrders v).map_source hw)
  rw [show placeFamily N n radicand baseDivisor hRadicand hOrders v (placeChart N n radicand baseDivisor hRadicand hOrders v w) = w from (placeChart N n radicand baseDivisor hRadicand hOrders v).left_inv hw] at he
  exact he.symm


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
