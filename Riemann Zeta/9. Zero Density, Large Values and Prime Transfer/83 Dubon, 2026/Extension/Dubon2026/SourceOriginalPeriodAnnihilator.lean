import Dubon2026.SourceOriginalRealAbelPotential

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> full real
span of actual loop periods. A real functional annihilating the periods
defines a continuous potential on the proved compact original curve.
At a maximum its analytic primitive is locally constant. The actual
differential reading is therefore zero, hence the original differential
is zero; linear independence then kills the functional's coefficients.
Adapted from S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem coefficients_eq_zero_of_annihilates_periods {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (hli : LinearIndependent ℂ b) (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N b, ℓ u = 0) : PeriodRealDual.coefficients ℓ = 0 := by
  letI := place_compactSpace N
  letI := place_connectedSpace N
  obtain ⟨P₀⟩ : Nonempty (Place ℂ (modularFunctionFieldOver N ℂ)) := inferInstance
  obtain ⟨v, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (continuous_realAbelPotential N b hb ℓ hℓ P₀).continuousOn
  obtain ⟨Φ, hΦ, hlocal⟩ := realAbelPotential_local N b hb ℓ hℓ P₀ v
  have hlocmax : IsLocalMax (fun z => (Φ z).re) (0 : ℂ) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (place_spec N v).1] with z hz
    have h1 := hlocal z hz
    have h2 : realAbelPotential N b ℓ P₀ (placeFamily N v z) ≤ realAbelPotential N b ℓ P₀ v :=
      hmax (mem_univ _)
    linarith
  have hdiff : DifferentiableOn ℂ Φ (ball 0 (placeRadius N v)) :=
    fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ Φ 0 := hdiff.analyticAt (ball_mem_nhds _ (place_spec N v).1)
  have hconst := PeriodRealDual.eventually_eq_of_isLocalMax_re han hlocmax
  have hzero : ∀ᶠ z in 𝓝 (0 : ℂ),
      ∑ i, PeriodRealDual.coefficients ℓ i * readDifferential N v (b i) z = 0 := by
    filter_upwards [hconst.eventually_nhds, ball_mem_nhds (0 : ℂ) (place_spec N v).1]
      with z hz hzb
    have hd : HasDerivAt Φ 0 z :=
      (hasDerivAt_const z (Φ 0)).congr_of_eventuallyEq hz
    exact (hΦ z hzb).unique hd
  have hread : ∀ᶠ z in 𝓝 (0 : ℂ),
      readDifferential N v (∑ i, PeriodRealDual.coefficients ℓ i • b i) z = 0 := by
    filter_upwards [hzero, ball_mem_nhds (0 : ℂ) (place_spec N v).1] with z hz hzb
    rw [readDifferential_sum_smul N v (PeriodRealDual.coefficients ℓ) b hb hzb, hz]
  have hsum := eq_zero_of_readDifferential_eventually_eq_zero N v _ hread
  funext i
  exact Fintype.linearIndependent_iff.mp hli (PeriodRealDual.coefficients ℓ) hsum i

theorem eq_zero_of_annihilates_periods {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (hli : LinearIndependent ℂ b) (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hℓ : ∀ u ∈ pathPeriodLattice N b, ℓ u = 0) : ℓ = 0 := by
  have hc := coefficients_eq_zero_of_annihilates_periods N b hb hli ℓ hℓ
  apply LinearMap.ext
  intro w
  rw [PeriodRealDual.apply_eq_re_sum ℓ w, hc]
  simp

end
end Dubon2026.SourceFunctionField.OriginalChart
