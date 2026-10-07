import Dubon2026.PhaseVerticalRoots
import Dubon2026.RealAnalyticSign

/-! # Analytic sign tests for the coefficients of the actual vertical zero polynomial -/

namespace Dubon2026

open Filter Set MeasureTheory Metric
open scoped Topology

noncomputable section

/-- Evaluate an actual real multivariate polynomial on finitely many coefficients. -/
def phaseCoefficientTest (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T σ : ℝ) {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : PrimeCoordinate N → ℝ) : ℝ :=
  MvPolynomial.aeval (fun j : Fin d =>
    (phaseVerticalRealPolynomial a N hN ha l u T σ x).coeff j.val) p

theorem analyticAt_phaseCoefficientTest {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℝ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0) (σ : ℝ)
    {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    AnalyticAt ℝ (phaseCoefficientTest a N hN ha l u T σ p) x := by
  unfold phaseCoefficientTest
  apply AnalyticAt.aeval_mvPolynomial
  intro j
  exact analyticAt_phaseVerticalRealPolynomial_coeff hN ha x hlu hT hn σ j.val

/-- Finite algebraic sign tests on these actual coefficients have an almost-everywhere
continuous output near every zero-free enclosing border. This does not assume or
assert that a root count already has such a finite sign representation. -/
theorem phase_coefficient_signs_locally_ae_continuous {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℝ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0) (σ : ℝ)
    {d : ℕ} {ι : Type*} [Fintype ι] (p : ι → MvPolynomial (Fin d) ℝ)
    {W : Type*} [TopologicalSpace W] (F : (ι → SignType) → W) :
    ∃ r > 0, ∀ᵐ y ∂(volume : Measure (PrimeCoordinate N → ℝ)).restrict (ball x r),
      ContinuousAt (fun z => F (fun i => SignType.sign
        (phaseCoefficientTest a N hN ha l u T σ (p i) z))) y := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i, AnalyticAt ℝ
      (phaseCoefficientTest a N hN ha l u T σ (p i)) y := by
    apply Filter.eventually_all.mpr
    intro i
    exact (analyticAt_phaseCoefficientTest hN ha x hlu hT hn σ (p i)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, hr, analytic_finite_signs_ae_continuousAt volume F ?_⟩
  intro i y hy
  exact hball hy i

end

end Dubon2026
