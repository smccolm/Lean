import Dubon2026.RealNormPolynomial

/-! # Vertical-line substitution and exact algebraic-to-analytic root multiplicities -/

namespace Dubon2026

open Polynomial Complex Filter
open scoped Topology

noncomputable section

theorem analyticOrderAt_polynomial_eval {P : ℂ[X]} (hP : P ≠ 0) (s : ℂ) :
    analyticOrderAt (fun z => P.eval z) s = (P.rootMultiplicity s : ℕ∞) := by
  have hA : AnalyticAt ℂ (fun z => P.eval z) s := analyticAt_id.aeval_polynomial P
  obtain ⟨Q, hQ, hn⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP s
  apply hA.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z => Q.eval z, analyticAt_id.aeval_polynomial Q, ?_, ?_⟩
  · intro hz
    exact hn (Polynomial.dvd_iff_isRoot.mpr hz)
  · exact Filter.Eventually.of_forall (fun z => by
      have hh := congrArg (fun R : ℂ[X] => R.eval z) hQ
      simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul] using hh)

theorem analyticOrderNatAt_polynomial_eval {P : ℂ[X]} (hP : P ≠ 0) (s : ℂ) :
    analyticOrderNatAt (fun z => P.eval z) s = P.rootMultiplicity s := by
  simp only [analyticOrderNatAt, analyticOrderAt_polynomial_eval hP, ENat.toNat_coe]

/-- Substitution of the actual vertical-line coordinate. -/
def verticalLinePolynomial (P : ℂ[X]) (σ : ℝ) : ℂ[X] :=
  P.comp (C (σ : ℂ) + C I * X)

theorem verticalLinePolynomial_eval (P : ℂ[X]) (σ : ℝ) (z : ℂ) :
    (verticalLinePolynomial P σ).eval z = P.eval ((σ : ℂ) + I * z) := by
  simp [verticalLinePolynomial]

theorem verticalLinePolynomial_ne_zero {P : ℂ[X]} (hP : P ≠ 0) (σ : ℝ) :
    verticalLinePolynomial P σ ≠ 0 := by
  intro hz
  obtain h | ⟨_, he⟩ := Polynomial.comp_eq_zero_iff.mp hz
  · exact hP h
  · have hh := congrArg (fun Q : ℂ[X] => Q.coeff 1) he
    simp at hh

theorem verticalLinePolynomial_rootMultiplicity {P : ℂ[X]} (hP : P ≠ 0) (σ : ℝ) (z : ℂ) :
    (verticalLinePolynomial P σ).rootMultiplicity z = P.rootMultiplicity ((σ : ℂ) + I * z) := by
  rw [← analyticOrderNatAt_polynomial_eval (verticalLinePolynomial_ne_zero hP σ),
    ← analyticOrderNatAt_polynomial_eval hP]
  have he : (fun w => (verticalLinePolynomial P σ).eval w) =
      (fun w => P.eval w) ∘ (fun w : ℂ => (σ : ℂ) + I * w) :=
    funext (verticalLinePolynomial_eval P σ)
  have ha : AnalyticAt ℂ (fun w : ℂ => (σ : ℂ) + I * w) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hd : deriv (fun w : ℂ => (σ : ℂ) + I * w) z = I := by
    simpa only [mul_one] using ((hasDerivAt_id z).const_mul I |>.const_add (σ : ℂ)).deriv
  simp only [analyticOrderNatAt, he, analyticOrderAt_comp_of_deriv_ne_zero ha (hd.trans_ne I_ne_zero)]

theorem vertical_realNorm_rootMultiplicity {P : ℂ[X]} (hP : P ≠ 0) (σ t : ℝ) :
    (realNormPolynomial (verticalLinePolynomial P σ)).rootMultiplicity t =
      2 * P.rootMultiplicity ((σ : ℂ) + I * t) := by
  rw [realNormPolynomial_rootMultiplicity (verticalLinePolynomial_ne_zero hP σ),
    verticalLinePolynomial_rootMultiplicity hP]

end

end Dubon2026
