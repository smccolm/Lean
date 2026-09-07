import GafniTao.HeathBrownAtkinsonLemma71
import GafniTao.HeathBrownDivisorSquare

/-!
# Absorbing the cardinality term in Ivić's Lemma 7.1

This file performs the algebraic step immediately after equation (7.19).  The
coefficient of `W.card` in the Gram-row estimate is absorbed into the
left-hand side, and the exact divisor-square mean is then inserted.  No
zeta-to-Atkinson selection statement is assumed here.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The part of the row majorant independent of the cardinality. -/
def heathBrownAtkinsonLemma71FreeMajorant
    (T : ℝ) (K : ℕ) : ℝ :=
  (K : ℝ) +
    heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
      (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ)))

theorem heathBrownAtkinsonLemma71FreeMajorant_nonneg
    {T : ℝ} {K : ℕ} (hT : 0 < T) :
    0 ≤ heathBrownAtkinsonLemma71FreeMajorant T K := by
  unfold heathBrownAtkinsonLemma71FreeMajorant
  have hhQ : 0 ≤ harmonic ⌈T⌉₊ := by
    rw [harmonic_eq_sum_Icc]
    positivity
  have hh : 0 ≤ (((harmonic ⌈T⌉₊ : ℚ) : ℝ)) := by
    exact_mod_cast hhQ
  exact add_nonneg (by positivity)
    (mul_nonneg
      (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT)
      (mul_nonneg (by norm_num) hh))

theorem heathBrownAtkinsonLemma71RowMajorant_eq
    (T : ℝ) (K R : ℕ) :
    heathBrownAtkinsonLemma71RowMajorant T K R =
      heathBrownAtkinsonLemma71FreeMajorant T K +
        (R : ℝ) * heathBrownAtkinsonEquation719FirstCoefficient T K := by
  unfold heathBrownAtkinsonLemma71RowMajorant
    heathBrownAtkinsonLemma71FreeMajorant
  ring

/-- Ivić's absorption step after Lemma 7.1, with every constant and the
harmonic reciprocal-gap contribution still explicit. -/
theorem heathBrownAtkinson_lemma71_of_absorption
    {K : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖)
    (hAbsorb :
      2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonEquation719FirstCoefficient T K ≤ V ^ (2 : ℕ)) :
    (W.card : ℝ) ≤
      2 * heathBrownAtkinsonEnergy K *
        heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
  have hMain := heathBrownAtkinson_lemma71 hT hK hV hblock hSep hRange hLarge
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

/-- The absorbed large-values estimate with the elementary divisor-square
mean substituted.  This is the source-ready form used after choosing the
dyadic Atkinson block in the proof of Theorem 7.1. -/
theorem heathBrownAtkinson_lemma71_logarithmic
    {K : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖)
    (hAbsorb :
      2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonEquation719FirstCoefficient T K ≤ V ^ (2 : ℕ)) :
    (W.card : ℝ) ≤
      4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
        heathBrownAtkinsonLemma71FreeMajorant T K / V ^ (2 : ℕ) := by
  have hCard := heathBrownAtkinson_lemma71_of_absorption
    hT hK hV hblock hSep hRange hLarge hAbsorb
  have hEnergy : heathBrownAtkinsonEnergy K ≤
      ((2 * K : ℕ) : ℝ) *
        (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) := by
    exact sum_Ioc_heathBrownDivisorCoefficient_sq_le_log_cube hK
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
