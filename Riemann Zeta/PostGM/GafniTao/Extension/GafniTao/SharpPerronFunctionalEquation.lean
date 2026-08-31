import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A clean completed-zeta logarithmic functional equation

The pinned Kadiri source module also contains unrelated provisional results.
Consequently this file reconstructs only its proved completed-zeta chain from
the clean Hadamard-log-derivative and digamma modules.  The sign is the one
obtained by differentiating the reflection `s ↦ 1 - s`.
-/

namespace GafniTao

open MeasureTheory Complex Filter
open Kadiri
open scoped Topology

private lemma sharp_zetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma sharp_completedZetaFactor_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hΓhalf : Gamma (s / 2) ≠ 0) :
    completedZetaFactor s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  have hGamma : Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) :=
    Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor,
    sharp_zetaPiFactor_eq_cpow, hGamma, riemannZeta_def_of_ne_zero hs0,
    Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma sharp_gamma_half_avoid_neg_nat_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  cases m with
  | zero =>
      apply hs0
      rw [show s = 2 * (s / 2) by ring, hm]
      ring
  | succ m =>
      have hbad : s / 2 + 1 = -(m : ℂ) := by
        rw [hm]
        norm_num
      exact hΓdiff m hbad

private lemma sharp_gamma_half_ne_zero_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    Gamma (s / 2) ≠ 0 :=
  Gamma_ne_zero (sharp_gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff)

private theorem sharp_completedZetaFactor_one_sub {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓhalf : Gamma (s / 2) ≠ 0)
    (hΓhalfRef : Gamma ((1 - s) / 2) ≠ 0) :
    completedZetaFactor (1 - s) = completedZetaFactor s := by
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  rw [sharp_completedZetaFactor_eq_mul_completedRiemannZeta h1s0 hΓhalfRef,
    sharp_completedZetaFactor_eq_mul_completedRiemannZeta hs0 hΓhalf,
    completedRiemannZeta_one_sub]
  ring

private lemma sharp_differentiableAt_completedZetaFactor {s : ℂ}
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    DifferentiableAt ℂ completedZetaFactor s := by
  unfold completedZetaFactor zetaPoleFactor zetaPiFactor zetaGammaFactor
  exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ ↦ s - 1) s).mul
      (by
        rw [show (fun s : ℂ ↦ Complex.exp (-(s / 2) *
            (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun s : ℂ ↦ -(s / 2) *
            (Real.log Real.pi : ℂ)) by rfl]
        exact Complex.differentiableAt_exp.comp s (by fun_prop))).mul
      ((differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop))).mul
    (differentiableAt_riemannZeta hs1)

private theorem sharp_logDeriv_completedZetaFactor_one_sub {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiffS : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓdiffRef : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    logDeriv completedZetaFactor (1 - s) =
      -logDeriv completedZetaFactor s := by
  let R : ℂ → ℂ := fun z ↦ 1 - z
  have hΓhalfS : Gamma (s / 2) ≠ 0 :=
    sharp_gamma_half_ne_zero_of_shift hs0 hΓdiffS
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  have hΓhalfRef : Gamma ((1 - s) / 2) ≠ 0 :=
    sharp_gamma_half_ne_zero_of_shift h1s0 hΓdiffRef
  have hΓhalfNear : ∀ᶠ z in nhds s, Gamma (z / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ ↦ Gamma (z / 2)) s :=
      (differentiableAt_Gamma _
        (sharp_gamma_half_avoid_neg_nat_of_shift hs0 hΓdiffS)).comp s
          (by fun_prop)
    exact (hdiff.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hΓhalfS
  have hΓhalfRefNear : ∀ᶠ z in nhds s, Gamma ((1 - z) / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ
        (fun z : ℂ ↦ Gamma ((1 - z) / 2)) s :=
      (differentiableAt_Gamma _
        (sharp_gamma_half_avoid_neg_nat_of_shift h1s0 hΓdiffRef)).comp s
          (by fun_prop)
    exact (hdiff.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hΓhalfRef
  have hsymNear :
      (completedZetaFactor ∘ R) =ᶠ[nhds s] completedZetaFactor := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1,
      hΓhalfNear, hΓhalfRefNear] with z hz0 hz1 hΓz hΓrefz
    exact sharp_completedZetaFactor_one_sub hz0 hz1 hΓz hΓrefz
  have hcomp :
      logDeriv (completedZetaFactor ∘ R) s =
        logDeriv completedZetaFactor (R s) * deriv R s := by
    rw [logDeriv_comp]
    · exact sharp_differentiableAt_completedZetaFactor
        (by simpa [R] using sub_ne_zero.mpr hs0.symm) hΓdiffRef
    · dsimp [R]
      fun_prop
  have hderivR : deriv R s = -1 := by
    dsimp [R]
    simp
  have hlogEq :
      logDeriv (completedZetaFactor ∘ R) s =
        logDeriv completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply]
    rw [Filter.EventuallyEq.deriv_eq hsymNear]
    exact congrArg (fun z ↦ deriv completedZetaFactor s / z)
      hsymNear.eq_of_nhds
  rw [hcomp, hderivR] at hlogEq
  calc
    logDeriv completedZetaFactor (1 - s) =
        -(logDeriv completedZetaFactor (R s) * -1) := by simp [R]
    _ = -logDeriv completedZetaFactor s := by rw [hlogEq]

private theorem sharp_neg_logDeriv_zeta_left_eq_reflected {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0)
    (hζref : riemannZeta (1 - z) ≠ 0)
    (hΓzDiff : ∀ m : ℕ, z / 2 + 1 ≠ -m)
    (hΓrefDiff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m)
    (hΓz : zetaGammaFactor z ≠ 0)
    (hΓref : zetaGammaFactor (1 - z) ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + 1 / (z - 1) + 1 / ((1 - z) - 1)
        - (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * digamma (z / 2 + 1)
        + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
  have href1 : 1 - z ≠ 1 := by
    intro h
    apply hz0
    calc
      z = 1 - (1 - z) := by ring
      _ = 0 := by rw [h]; ring
  have hleft := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv
    z hz1 hΓzDiff hΓz hζz
  have hright := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv
    (1 - z) href1 hΓrefDiff hΓref hζref
  have htransport := sharp_logDeriv_completedZetaFactor_one_sub
    hz0 hz1 hΓzDiff hΓrefDiff
  have hnegLD :
      -logDeriv completedZetaFactor z =
        deriv riemannZeta (1 - z) / riemannZeta (1 - z)
          + 1 / ((1 - z) - 1)
          - (1 / 2 : ℂ) * Real.log Real.pi
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
    rw [htransport] at hright
    have hright' := congrArg Neg.neg hright
    ring_nf at hright' ⊢
    rw [hright']
    ring
  rw [hleft, hnegLD]
  ring

private lemma sharp_zetaGammaFactor_shift_avoid_of_not_zero {s : ℂ}
    (hsZ : s ∉ riemannZeta.zeroes) :
    ∀ m : ℕ, s / 2 + 1 ≠ -m := by
  intro m hm
  apply hsZ
  have hsEq : s = -2 * ((m : ℂ) + 1) := by
    calc
      s = 2 * (s / 2 + 1) - 2 := by ring
      _ = 2 * (-(m : ℂ)) - 2 := by rw [hm]
      _ = -2 * ((m : ℂ) + 1) := by ring
  rw [riemannZeta.zeroes]
  simpa [hsEq, Nat.cast_add, Nat.cast_one] using
    riemannZeta_neg_two_mul_nat_add_one m

private theorem sharp_functional_eq_correct_sign {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0)
    (hζref : riemannZeta (1 - s) ≠ 0)
    (hΓsDiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓrefDiff : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) +
        digamma ((1 - s) / 2)) := by
  have h1s0 : (1 : ℂ) - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  have hΓs : zetaGammaFactor s ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓsDiff
  have hΓref : zetaGammaFactor (1 - s) ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓrefDiff
  have hFE := sharp_neg_logDeriv_zeta_left_eq_reflected hs0 hs1
    hζs hζref hΓsDiff hΓrefDiff hΓs hΓref
  have hψs : digamma (s / 2 + 1) =
      digamma (s / 2) + (s / 2)⁻¹ :=
    digamma_apply_add_one _
      (sharp_gamma_half_avoid_neg_nat_of_shift hs0 hΓsDiff)
  have hψref : digamma ((1 - s) / 2 + 1) =
      digamma ((1 - s) / 2) + ((1 - s) / 2)⁻¹ :=
    digamma_apply_add_one _
      (sharp_gamma_half_avoid_neg_nat_of_shift h1s0 hΓrefDiff)
  have hcancel :
      1 / (s - 1) + 1 / (1 - s - 1)
        + (1 / 2 : ℂ) * (s / 2)⁻¹
        + (1 / 2 : ℂ) * ((1 - s) / 2)⁻¹ = 0 := by
    have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    field_simp [hs0, hsSub]
    ring_nf
  rw [hFE, hψs, hψref, Complex.ofReal_neg]
  linear_combination hcancel

/-- Completed-zeta logarithmic functional equation used on the left Perron
edge.  This public theorem has no dependency on the provisional Kadiri
declarations. -/
theorem sharpPerron_zeta_logDeriv_functional_eq {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζs : riemannZeta s ≠ 0)
    (hζ1s : riemannZeta (1 - s) ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) +
        digamma ((1 - s) / 2)) := by
  exact sharp_functional_eq_correct_sign hs0 hs1 hζs hζ1s
    (sharp_zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using hζs))
    (sharp_zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using hζ1s))

#print axioms sharpPerron_zeta_logDeriv_functional_eq
#print axioms Complex.exists_norm_digamma_div_two_le_log

end GafniTao
