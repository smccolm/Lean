import GafniTao.HeathBrownAtkinsonEquation719Sum

/-!
# Ivić Lemma 7.1: Bombieri--Halász with equation (7.19)

The theorem below is the exact finite large-values inequality before choosing
the Atkinson truncation length.  Its three terms are the diagonal, the
quadratic B-process contribution, and the harmonic first-derivative
contribution.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The row majorant in the finite form of Ivić Lemma 7.1. -/
def heathBrownAtkinsonLemma71RowMajorant
    (T : ℝ) (K R : ℕ) : ℝ :=
  (K : ℝ) + (R : ℝ) *
      heathBrownAtkinsonEquation719FirstCoefficient T K +
    heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
      (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ)))

theorem heathBrownAtkinsonLemma71RowMajorant_nonneg
    {T : ℝ} {K R : ℕ} (hT : 0 < T) :
    0 ≤ heathBrownAtkinsonLemma71RowMajorant T K R := by
  unfold heathBrownAtkinsonLemma71RowMajorant
  have hhQ : 0 ≤ harmonic ⌈T⌉₊ := by
    rw [harmonic_eq_sum_Icc]
    positivity
  have hh : 0 ≤ (((harmonic ⌈T⌉₊ : ℚ) : ℝ)) := by
    exact_mod_cast hhQ
  exact add_nonneg
    (add_nonneg (by positivity)
      (mul_nonneg (by positivity)
        (heathBrownAtkinsonEquation719FirstCoefficient_nonneg hT)))
    (mul_nonneg
      (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT)
      (mul_nonneg (by norm_num) hh))

/-- Complete Gram row, with the self-pair and both off-diagonal mechanisms
kept visible. -/
theorem sum_norm_heathBrownAtkinsonGram_row_le_lemma71
    {K : ℕ} {T t : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ W) (hSep : IsSeparated 1 W)
    (hRange : ∀ x ∈ W, x ∈ Set.Icc (T / 2) T) :
    (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
      heathBrownAtkinsonLemma71RowMajorant T K W.card := by
  have hfirst := heathBrownAtkinsonEquation719FirstCoefficient_nonneg
    (K := K) hT
  have hpoint : ∀ u ∈ W,
      ‖heathBrownAtkinsonGram K t u‖ ≤
        (if u = t then (K : ℝ) else 0) +
          heathBrownAtkinsonEquation719FirstCoefficient T K +
          heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
            (if u = t then 0 else 1 / |t - u|) := by
    intro u hu
    by_cases hut : u = t
    · subst u
      rw [norm_heathBrownAtkinsonGram_self]
      simpa using (le_add_of_nonneg_right hfirst :
        (K : ℝ) ≤ (K : ℝ) +
          heathBrownAtkinsonEquation719FirstCoefficient T K)
    · simp only [if_neg hut, zero_add]
      have h := norm_heathBrownAtkinsonGram_le_equation719_split
        hT hK hblock (hRange t ht) (hRange u hu) (Ne.symm hut)
      simpa only [div_eq_mul_inv, one_mul] using h
  calc
    (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        ∑ u ∈ W,
          ((if u = t then (K : ℝ) else 0) +
            heathBrownAtkinsonEquation719FirstCoefficient T K +
            heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (if u = t then 0 else 1 / |t - u|)) := by
      exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = (K : ℝ) + (W.card : ℝ) *
          heathBrownAtkinsonEquation719FirstCoefficient T K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
          (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq', if_pos ht]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ heathBrownAtkinsonLemma71RowMajorant T K W.card := by
      unfold heathBrownAtkinsonLemma71RowMajorant
      have hrec :
          heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) ≤
            heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (sum_ite_inv_abs_sub_le_harmonic W hT ht hSep hRange)
          (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT)
      linarith

/-- Finite Bombieri--Halász conclusion of Ivić Lemma 7.1. -/
theorem heathBrownAtkinson_lemma71
    {K : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖) :
    (W.card : ℝ) * V ^ (2 : ℕ) ≤
      heathBrownAtkinsonEnergy K *
        heathBrownAtkinsonLemma71RowMajorant T K W.card := by
  by_cases hW : W = ∅
  · subst W
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (heathBrownAtkinsonEnergy_nonneg K)
      (heathBrownAtkinsonLemma71RowMajorant_nonneg hT)
  · have hR : 0 < (W.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
    have hGram := heathBrownAtkinson_halasz_gram hV.le hLarge
    have hrows :
        (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
          (W.card : ℝ) *
            heathBrownAtkinsonLemma71RowMajorant T K W.card := by
      calc
        (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
            ∑ _t ∈ W, heathBrownAtkinsonLemma71RowMajorant T K W.card := by
          exact Finset.sum_le_sum fun t ht =>
            sum_norm_heathBrownAtkinsonGram_row_le_lemma71
              hT hK hblock ht hSep hRange
        _ = (W.card : ℝ) *
            heathBrownAtkinsonLemma71RowMajorant T K W.card := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    have hE : 0 ≤ heathBrownAtkinsonEnergy K :=
      heathBrownAtkinsonEnergy_nonneg K
    have hmul := mul_le_mul_of_nonneg_left hrows hE
    unfold heathBrownAtkinsonEnergy at hGram ⊢
    calc
      (W.card : ℝ) * V ^ (2 : ℕ) =
          (((W.card : ℝ) * V) ^ (2 : ℕ)) / (W.card : ℝ) := by
        field_simp [hR.ne']
      _ ≤ ((∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : ℝ) ^ (2 : ℕ)) *
            ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) /
          (W.card : ℝ) :=
        div_le_div_of_nonneg_right hGram hR.le
      _ ≤ ((∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : ℝ) ^ (2 : ℕ)) *
            ((W.card : ℝ) *
              heathBrownAtkinsonLemma71RowMajorant T K W.card)) /
          (W.card : ℝ) :=
        div_le_div_of_nonneg_right hmul hR.le
      _ = (∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : ℝ) ^ (2 : ℕ)) *
            heathBrownAtkinsonLemma71RowMajorant T K W.card := by
        field_simp [hR.ne']


end

end GafniTao
