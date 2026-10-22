import Dubon2026.SourceOriginalDifferentialReadingLinear
import Dubon2026.SourcePeriodRealDual

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> full real
span of actual loop periods. A real functional annihilating all loop
periods gives a continuous real function on the actual original curve.
The proved local Abel-Jacobi identity identifies it with the real part
of an analytic primitive. Compact maximum modulus can therefore test
the annihilator on the actual original regular differentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

/-- Applying a real functional to the actual chosen-path Abel-Jacobi vector. -/
def realAbelPotential {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ) (P₀ P : Place ℂ (modularFunctionFieldOver N ℂ)) : ℝ :=
  ℓ (abelJacobiVec N b P₀ P)

theorem realAbelPotential_local {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N b, ℓ u = 0)
    (P₀ v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ Φ : ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) (placeRadius N v),
        HasDerivAt Φ (∑ i, PeriodRealDual.coefficients ℓ i * readDifferential N v (b i) z) z) ∧
      ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
        realAbelPotential N b ℓ P₀ (placeFamily N v z) =
          realAbelPotential N b ℓ P₀ v + ((Φ z).re - (Φ 0).re) := by
  obtain ⟨Ψ, hΨ, hlocal⟩ := exists_abelJacobiVec_chart_primitive N b hb P₀ v
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
  change ℓ (abelJacobiVec N b P₀ (placeFamily N v z)) =
    ℓ (abelJacobiVec N b P₀ v) + _
  linarith

theorem continuous_realAbelPotential {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N b, ℓ u = 0)
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) :
    Continuous (realAbelPotential N b ℓ P₀) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨Φ, hΦ, hlocal⟩ := realAbelPotential_local N b hb ℓ hℓ P₀ v
  have hΦc : ContinuousAt Φ (placeChart N v v) := by
    rw [placeChart_self]
    exact (hΦ 0 (mem_ball_self (place_spec N v).1)).continuousAt
  have hc : ContinuousAt (fun w => Φ (placeChart N v w)) v :=
    hΦc.comp (continuousAt_placeChart N v v (mem_placeChart_source N v))
  have hr : ContinuousAt (fun w => (Φ (placeChart N v w)).re) v :=
    Complex.continuous_re.continuousAt.comp hc
  have hcont : ContinuousAt (fun w => realAbelPotential N b ℓ P₀ v +
      ((Φ (placeChart N v w)).re - (Φ 0).re)) v :=
    continuousAt_const.add (hr.sub continuousAt_const)
  apply hcont.congr
  filter_upwards [placeChart_source_mem_nhds N v] with w hw
  have he := hlocal (placeChart N v w) ((placeChart N v).map_source hw)
  rw [show placeFamily N v (placeChart N v w) = w from (placeChart N v).left_inv hw] at he
  exact he.symm

end
end Dubon2026.SourceFunctionField.OriginalChart
