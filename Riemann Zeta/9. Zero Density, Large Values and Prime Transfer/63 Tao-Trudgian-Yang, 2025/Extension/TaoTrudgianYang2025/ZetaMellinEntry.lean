import TaoTrudgianYang2025.ZetaIntervalCutoff
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The actual coefficient-one polynomial on the right Mellin line

Mellin inversion and absolutely convergent Dirichlet series give the exact
zeta integral before contour shifting. Integrability, termwise inversion,
and sum/integral interchange are proved from the native smooth-test data.
No critical-line entry estimate is assumed or asserted.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaMellinTerm (g : ℝ → ℂ) (c t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (1 : ℕ → ℂ) ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) n *
    mellin g ((c : ℂ) + (u : ℂ) * I)

theorem norm_zetaMellinTerm (g : ℝ → ℂ) (c t : ℝ) (n : ℕ) (u : ℝ) :
    ‖zetaMellinTerm g c t n u‖ =
      ‖LSeries.term (1 : ℕ → ℂ) (c : ℂ) n‖ * ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ := by
  unfold zetaMellinTerm
  rw [norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

theorem integrable_zetaMellinTerm {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (c t : ℝ) (n : ℕ) : Integrable (zetaMellinTerm g c t n) := by
  unfold zetaMellinTerm
  apply (hg.verticalIntegrable_mellin c).bdd_mul
    (c := ‖LSeries.term (1 : ℕ → ℂ) (c : ℂ) n‖)
  · by_cases hn : n = 0
    · subst n
      simpa only [LSeries.term_zero] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)))
    · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply]
      have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hpow : Continuous (fun u : ℝ =>
          (n : ℂ) ^ ((c : ℂ) + ((u + t : ℝ) : ℂ) * I)) :=
        (by fun_prop : Continuous (fun u : ℝ => (c : ℂ) + ((u + t : ℝ) : ℂ) * I)).const_cpow
          (Or.inl hbase)
      exact (continuous_const.div hpow (fun _ => cpow_ne_zero_iff.mpr (Or.inl hbase))).aestronglyMeasurable
  · filter_upwards with u
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

theorem integral_norm_zetaMellinTerm (g : ℝ → ℂ) (c t : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaMellinTerm g c t n u‖) =
      ‖LSeries.term (1 : ℕ → ℂ) (c : ℂ) n‖ *
        ∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ := by
  simp_rw [norm_zetaMellinTerm]
  exact integral_const_mul _ _

theorem summable_integral_norm_zetaMellinTerm (g : ℝ → ℂ) {c : ℝ} (hc : 1 < c) (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖zetaMellinTerm g c t n u‖) := by
  have hsum : LSeriesSummable (1 : ℕ → ℂ) (c : ℂ) :=
    LSeriesSummable_one_iff.mpr (by simpa using hc)
  have hnorm := hsum.norm.mul_right (∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖)
  exact hnorm.congr fun n => (integral_norm_zetaMellinTerm g c t n).symm

/-- Multiplication by the genuine negative Dirichlet phase shifts the
imaginary part of zeta in the positive direction in the Mellin integral. -/
theorem zetaMellinTerm_eq_phase_mul {n : ℕ} (hn : n ≠ 0)
    (g : ℝ → ℂ) (c t u : ℝ) :
    zetaMellinTerm g c t n u =
      dirichletPhase n t *
        ((n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * I)) * mellin g ((c : ℂ) + (u : ℂ) * I)) := by
  have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold zetaMellinTerm dirichletPhase
  rw [LSeries.term_of_ne_zero hn]
  simp only [Pi.one_apply, one_div, ← cpow_neg, cpow_eq_pow]
  have heq : -((c : ℂ) + ((u + t : ℝ) : ℂ) * I) =
      -(I * (t : ℂ)) + -((c : ℂ) + (u : ℂ) * I) := by push_cast; ring
  rw [heq, cpow_add _ _ hbase]
  ring

theorem integral_zetaMellinTerm_eq {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (c t : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * (∫ u : ℝ, zetaMellinTerm g c t n u) =
      g n * dirichletPhase n t := by
  by_cases hn : n = 0
  · subst n
    have hg0 : g 0 = 0 := by
      by_contra hne
      have hs := hg.support_subset hne
      linarith [hg.lower_pos, hs.1]
    simp [zetaMellinTerm, hg0]
  · have hInv := hg.mellinInversion c (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    unfold mellinInv at hInv
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat] at hInv
    simp_rw [zetaMellinTerm_eq_phase_mul hn]
    rw [integral_const_mul]
    calc
      _ = dirichletPhase n t * ((1 / (2 * Real.pi) : ℂ) *
          ∫ u : ℝ, (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * I)) *
            mellin g ((c : ℂ) + (u : ℂ) * I)) := by ring
      _ = _ := by rw [hInv]; ring

/-- Exact right-line zeta identity for a genuine smooth positive compact
test function. All inversion and Tonelli hypotheses are discharged. -/
theorem smooth_dirichlet_sum_eq_zeta_mellin {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {c : ℝ} (hc : 1 < c) (t : ℝ) :
    (∑' n : ℕ, g n * dirichletPhase n t) =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
          mellin g ((c : ℂ) + (u : ℂ) * I) := by
  simp_rw [← integral_zetaMellinTerm_eq hg c t]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (integrable_zetaMellinTerm hg c t) (summable_integral_norm_zetaMellinTerm g hc t)]
  congr 2
  funext u
  unfold zetaMellinTerm
  rw [tsum_mul_right]
  change LSeries (1 : ℕ → ℂ) _ * _ = _
  rw [LSeries_one_eq_riemannZeta (by simpa using hc)]

/-- The actual sharp coefficient-one polynomial has this zeta integral,
for any presentation of its active integer interval and any right line. -/
theorem ZetaLargeValuePattern.polynomial_eq_zeta_mellin (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) {c : ℝ} (hc : 1 < c) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
          mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((c : ℂ) + (u : ℂ) * I) := by
  rw [P.polynomial_eq_cutoff_tsum hactive]
  exact smooth_dirichlet_sum_eq_zeta_mellin
    (zetaIntervalCutoffTest a b (P.active_left_pos hactive)) hc t

/-- Source-object consumer: a single explicit interval cutoff represents
all large ordinates. Neither a Mellin identity nor a norm bound is an input. -/
theorem ZetaLargeValuePattern.exists_zeta_mellin_large (P : ZetaLargeValuePattern)
    {c : ℝ} (hc : 1 < c) :
    ∃ a b : ℕ, P.active = Finset.Icc a b ∧ 1 ≤ a ∧
      ∀ t ∈ P.ordinates, P.V ≤
        ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
            mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((c : ℂ) + (u : ℂ) * I)‖ := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  refine ⟨a, b, hactive, P.active_left_pos hactive, ?_⟩
  intro t ht
  rw [← P.polynomial_eq_zeta_mellin hactive hc t]
  exact P.large t ht

end TaoTrudgianYang2025
