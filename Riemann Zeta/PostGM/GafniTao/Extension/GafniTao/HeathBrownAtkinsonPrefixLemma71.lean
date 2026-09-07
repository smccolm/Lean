import GafniTao.HeathBrownAtkinsonPrefixGram
import GafniTao.HeathBrownAtkinsonLemma71Absorption

/-!
# Ivić Lemma 7.1 uniformly for literal Atkinson prefixes

The local mean-square formula contains an average of the partial sums
`S(x, K, t)`.  This file combines the common-block zero padding with the
already proved equation-(7.19) Gram row bound.  Consequently the constants,
block endpoints, reciprocal-gap term, and absorption condition are identical
for every integer prefix `0 ≤ j ≤ K`.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Finite Bombieri--Halász conclusion of Ivić Lemma 7.1, uniform in the
integer prefix `j`. -/
theorem heathBrownAtkinson_prefix_lemma71
    {K j : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hj : j ≤ K) (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖) :
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
    have hGram := heathBrownAtkinson_prefix_halasz_gram hj hV.le hLarge
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
    calc
      (W.card : ℝ) * V ^ (2 : ℕ) =
          (((W.card : ℝ) * V) ^ (2 : ℕ)) / (W.card : ℝ) := by
        field_simp [hR.ne']
      _ ≤ (heathBrownAtkinsonEnergy K *
            ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) /
          (W.card : ℝ) :=
        div_le_div_of_nonneg_right hGram hR.le
      _ ≤ (heathBrownAtkinsonEnergy K *
            ((W.card : ℝ) *
              heathBrownAtkinsonLemma71RowMajorant T K W.card)) /
          (W.card : ℝ) :=
        div_le_div_of_nonneg_right hmul hR.le
      _ = heathBrownAtkinsonEnergy K *
            heathBrownAtkinsonLemma71RowMajorant T K W.card := by
        field_simp [hR.ne']

/-- Ivić's absorption step, still uniform in the prefix. -/
theorem heathBrownAtkinson_prefix_lemma71_of_absorption
    {K j : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hj : j ≤ K) (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖)
    (hAbsorb :
      2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonEquation719FirstCoefficient T K ≤ V ^ (2 : ℕ)) :
    (W.card : ℝ) ≤
      2 * heathBrownAtkinsonEnergy K *
        heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
  have hMain := heathBrownAtkinson_prefix_lemma71
    hj hT hK hV hblock hSep hRange hLarge
  rw [heathBrownAtkinsonLemma71RowMajorant_eq] at hMain
  have hE : 0 ≤ heathBrownAtkinsonEnergy K :=
    heathBrownAtkinsonEnergy_nonneg K
  have hA : 0 ≤ heathBrownAtkinsonEquation719FirstCoefficient T K :=
    heathBrownAtkinsonEquation719FirstCoefficient_nonneg hT
  have hF : 0 ≤ heathBrownAtkinsonLemma71FreeMajorant T K :=
    heathBrownAtkinsonLemma71FreeMajorant_nonneg hT
  have hV2 : 0 < V ^ (2 : ℕ) := pow_pos hV _
  have hHalf :
      (W.card : ℝ) * (V ^ (2 : ℕ) / 2) ≤
        heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonLemma71FreeMajorant T K := by
    nlinarith [mul_nonneg (Nat.cast_nonneg W.card)
      (sub_nonneg.mpr hAbsorb)]
  calc
    (W.card : ℝ) =
        ((W.card : ℝ) * (V ^ (2 : ℕ) / 2)) /
          (V ^ (2 : ℕ) / 2) := by
            field_simp [hV2.ne']
    _ ≤ (heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonLemma71FreeMajorant T K) /
          (V ^ (2 : ℕ) / 2) := by
            exact div_le_div_of_nonneg_right hHalf (by positivity)
    _ = 2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
            field_simp [hV2.ne']

/-- The prefix-uniform absorbed estimate after inserting the elementary
divisor-square mean. -/
theorem heathBrownAtkinson_prefix_lemma71_logarithmic
    {K j : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hj : j ≤ K) (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖)
    (hAbsorb :
      2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonEquation719FirstCoefficient T K ≤ V ^ (2 : ℕ)) :
    (W.card : ℝ) ≤
      4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
        heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
  have hCard := heathBrownAtkinson_prefix_lemma71_of_absorption
    hj hT hK hV hblock hSep hRange hLarge hAbsorb
  have hEnergy : heathBrownAtkinsonEnergy K ≤
      ((2 * K : ℕ) : ℝ) *
        (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) :=
    sum_Ioc_heathBrownDivisorCoefficient_sq_le_log_cube hK
  have hFree : 0 ≤ heathBrownAtkinsonLemma71FreeMajorant T K :=
    heathBrownAtkinsonLemma71FreeMajorant_nonneg hT
  have hV2 : 0 < V ^ (2 : ℕ) := pow_pos hV _
  calc
    (W.card : ℝ) ≤
        2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := hCard
    _ ≤ 2 * (((2 * K : ℕ) : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ)) *
          heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
      gcongr
    _ = 4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
          heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
      push_cast
      ring


end

end GafniTao
