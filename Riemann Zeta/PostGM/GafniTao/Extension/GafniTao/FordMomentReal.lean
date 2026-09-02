import GafniTao.FordRealCounts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Ford Lemma 3.4: the natural-to-real moment bridge

Ford states the Vinogradov mean-value hypothesis for every natural endpoint,
but the scales `Q_i` in equation (3.10) are real.  The hypothesis itself
forces its coefficient to be positive and its exponent to be nonnegative;
those facts make flooring the endpoint lossless in the required direction.
-/

namespace GafniTao

noncomputable section

theorem fordVinogradovMoment_one_le
    (s k : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    1 ≤ fordVinogradovMoment s k Q := by
  have hdiag := ford_floor_pow_le_vinogradovMoment s k (P := Q)
  have hfloor : 1 ≤ ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  have honePow : 1 ^ s ≤ ⌊Q⌋₊ ^ s := Nat.pow_le_pow_left hfloor s
  have honeMoment : 1 ≤ ⌊Q⌋₊ ^ s := by simpa using honePow
  exact honeMoment.trans hdiag

theorem FordVinogradovMomentBound.one_le_coefficient
    {s k : ℕ} {C delta : ℝ}
    (hmoment : FordVinogradovMomentBound s k C delta) :
    1 ≤ C := by
  have h := hmoment 1 (by omega)
  have hone : (1 : ℝ) ≤ fordVinogradovMomentNat s k 1 := by
    simpa [fordVinogradovMoment] using
      (fordVinogradovMoment_one_le s k (Q := 1) (by norm_num))
  simpa using hone.trans h

theorem FordVinogradovMomentBound.lambda_nonneg
    {s k : ℕ} {C delta : ℝ}
    (hmoment : FordVinogradovMomentBound s k C delta) :
    0 ≤ fordLambda34 s k delta := by
  let lambda := fordLambda34 s k delta
  by_contra hneg
  have hlambda : lambda < 0 := lt_of_not_ge hneg
  have htReal : Filter.Tendsto (fun x : ℝ => C * x ^ lambda)
      Filter.atTop (nhds 0) := by
    have ht := (tendsto_rpow_neg_atTop (y := -lambda) (by linarith)).const_mul C
    simpa [show - -lambda = lambda by ring] using ht
  have htNat : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ lambda)
      Filter.atTop (nhds 0) :=
    htReal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ lambda < 1 :=
    htNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  let n := max N 1
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn : 1 ≤ n := Nat.le_max_right _ _
  have hnsmall := hN n hnN
  have hbound := hmoment n hn
  have hone : (1 : ℝ) ≤ fordVinogradovMomentNat s k n := by
    have hdiag := fordVinogradovMoment_one_le s k (Q := (n : ℝ))
      (by exact_mod_cast hn)
    simpa [fordVinogradovMoment] using hdiag
  exact (not_lt_of_ge (hone.trans hbound)) hnsmall

/-- The exact real-endpoint version of Ford's source moment hypothesis. -/
theorem FordVinogradovMomentBound.real_endpoint
    {s k : ℕ} {C delta : ℝ}
    (hmoment : FordVinogradovMomentBound s k C delta)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    (fordVinogradovMoment s k Q : ℝ) ≤
      C * Q ^ fordLambda34 s k delta := by
  have hfloor : 1 ≤ ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  have hsource := hmoment ⌊Q⌋₊ hfloor
  have hfloorReal : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hlambda := hmoment.lambda_nonneg
  have hpow : (⌊Q⌋₊ : ℝ) ^ fordLambda34 s k delta ≤
      Q ^ fordLambda34 s k delta :=
    Real.rpow_le_rpow (by positivity) hfloorReal hlambda
  have hC : 0 ≤ C := (hmoment.one_le_coefficient).trans' zero_le_one
  exact hsource.trans (mul_le_mul_of_nonneg_left hpow hC)

#print axioms fordVinogradovMoment_one_le
#print axioms FordVinogradovMomentBound.one_le_coefficient
#print axioms FordVinogradovMomentBound.lambda_nonneg
#print axioms FordVinogradovMomentBound.real_endpoint

end

end GafniTao
