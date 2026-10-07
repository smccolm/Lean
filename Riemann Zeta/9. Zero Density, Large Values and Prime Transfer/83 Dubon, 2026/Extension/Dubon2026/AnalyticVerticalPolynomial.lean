import Dubon2026.VerticalPolynomial

/-! # Real-analytic coefficients for vertical-line zero polynomials -/

namespace Dubon2026

open Filter Complex Polynomial
open scoped Topology ComplexConjugate

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem analyticAt_realNormPolynomial_coeff {f : V → ℂ[X]} {x : V}
    (hf : ∀ k, AnalyticAt ℝ (fun y => (f y).coeff k) x) (k : ℕ) :
    AnalyticAt ℝ (fun y => (realNormPolynomial (f y)).coeff k) x := by
  have hs : AnalyticAt ℝ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (f y).coeff ij.1 * conj ((f y).coeff ij.2)) x := by
    apply Finset.analyticAt_fun_sum
    intro ij _
    exact (hf ij.1).mul (AnalyticAt.comp (f := fun y : V => (f y).coeff ij.2)
      (Complex.conjCLE.toContinuousLinearMap.analyticAt _) (hf ij.2))
  have hr := (Complex.reCLM.analyticAt _).comp hs
  simpa only [realNormPolynomial, realPartPolynomial_coeff, Polynomial.coeff_mul,
    Polynomial.coeff_map] using hr

theorem verticalLinePolynomial_coeff_eq_sum {P : ℂ[X]} {d : ℕ}
    (hP : P.natDegree < d) (σ : ℝ) (k : ℕ) :
    (verticalLinePolynomial P σ).coeff k =
      ∑ j ∈ Finset.range d, P.coeff j * ((C (σ : ℂ) + C I * X) ^ j).coeff k := by
  have he := congrArg (fun Q : ℂ[X] => (verticalLinePolynomial Q σ).coeff k)
    (P.as_sum_range_C_mul_X_pow' hP)
  simpa only [verticalLinePolynomial, Polynomial.sum_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] using he

theorem analyticAt_verticalLinePolynomial_coeff {f : V → ℂ[X]} {x : V}
    (hf : ∀ k, AnalyticAt ℝ (fun y => (f y).coeff k) x)
    {d : ℕ} (hd : ∀ᶠ y in 𝓝 x, (f y).natDegree < d) (σ : ℝ) (k : ℕ) :
    AnalyticAt ℝ (fun y => (verticalLinePolynomial (f y) σ).coeff k) x := by
  have hs : AnalyticAt ℝ (fun y => ∑ j ∈ Finset.range d,
      (f y).coeff j * ((C (σ : ℂ) + C I * X) ^ j).coeff k) x := by
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (hf j).mul analyticAt_const
  apply hs.congr
  filter_upwards [hd] with y hy
  exact (verticalLinePolynomial_coeff_eq_sum hy σ k).symm

/-- Real phase coordinates embedded in the holomorphic phase family. -/
def complexifyPhase {N : ℕ} (x : PrimeCoordinate N → ℝ) : PrimeCoordinate N → ℂ :=
  fun p => (x p : ℂ)

theorem analyticAt_complexifyPhase {N : ℕ} (x : PrimeCoordinate N → ℝ) :
    AnalyticAt ℝ complexifyPhase x := by
  apply AnalyticAt.pi
  intro p
  exact AnalyticAt.comp (f := fun y : PrimeCoordinate N → ℝ => y p)
    (Complex.ofRealCLM.analyticAt (x p)) ((ContinuousLinearMap.proj p : (PrimeCoordinate N → ℝ) →L[ℝ] ℝ).analyticAt x)

/-- Real polynomial whose real roots detect the actual zeros on a specified vertical line. -/
def phaseVerticalRealPolynomial (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T σ : ℝ) (x : PrimeCoordinate N → ℝ) : ℝ[X] :=
  realNormPolynomial (verticalLinePolynomial
    (complexPhaseZeroPolynomial a N hN ha l u T (complexifyPhase x)) σ)

theorem analyticAt_phaseVerticalRealPolynomial_coeff {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℝ)
    {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ),
      complexPhaseFamily a N (complexifyPhase x, s) ≠ 0) (σ : ℝ) (k : ℕ) :
    AnalyticAt ℝ (fun y => (phaseVerticalRealPolynomial a N hN ha l u T σ y).coeff k) x := by
  have hcoeff : ∀ j, AnalyticAt ℝ (fun y =>
      (complexPhaseZeroPolynomial a N hN ha l u T (complexifyPhase y)).coeff j) x := by
    intro j
    exact ((analyticAt_complexPhaseZeroPolynomial_coeff hN ha (complexifyPhase x)
      hlu hT hn j).restrictScalars (𝕜 := ℝ)).comp (analyticAt_complexifyPhase x)
  have he := (analyticAt_complexifyPhase x).continuousAt.eventually
    (eventually_eq_complexPhaseZero_count hN ha (complexifyPhase x) hlu hT hn)
  let d := (complexPhaseZeroPolynomial a N hN ha l u T (complexifyPhase x)).natDegree + 1
  have hd : ∀ᶠ y in 𝓝 x,
      (complexPhaseZeroPolynomial a N hN ha l u T (complexifyPhase y)).natDegree < d := by
    filter_upwards [he] with y hy
    dsimp only [d, complexPhaseZeroPolynomial]
    rw [rectangleZeroPolynomial_natDegree, rectangleZeroPolynomial_natDegree, hy]
    exact Nat.lt_succ_self _
  exact analyticAt_realNormPolynomial_coeff
    (fun j => analyticAt_verticalLinePolynomial_coeff hcoeff hd σ j) k

end

end Dubon2026
