import GafniTao.FordCorollary64RealMoment
import GafniTao.FordCorollary64RealRoot

/-!
# Ford Lemma 6.3 in the exceptional `2.6 ≤ λ ≤ 4` scale

Ford treats this range directly with `k = 4` and `P = N^(1-λ/5)` rather
than invoking Corollary 6.4.  This file records the exact algebra for a
general certified Vinogradov moment.
-/

namespace GafniTao

noncomputable section

def fordLemma63DirectMu (lambda : ℝ) : ℝ := 1 - lambda / 5

def fordLemma63DirectSaving (s : ℕ) (delta lambda : ℝ) : ℝ :=
  (1 - fordLemma63DirectMu lambda * (1 + delta)) / (2 * s : ℝ)

def fordLemma63DirectCoefficient (s : ℕ) (C : ℝ) : ℝ :=
  4 * (C * (8 * Real.pi) ^ 4 * (Nat.factorial 4 : ℝ)) ^
      (1 / (2 * s : ℝ)) + 2

theorem fordLemma63_direct_le_power_saving
    {s N R : ℕ} {P u t lambda C delta : ℝ}
    (hs : 1 ≤ s) (hN : 1 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlambda4 : lambda ≤ 4)
    (hmu0 : 0 ≤ fordLemma63DirectMu lambda)
    (hmu1 : fordLemma63DirectMu lambda ≤ 1)
    (htEq : t = (N : ℝ) ^ lambda)
    (hPscale : P = (N : ℝ) ^ fordLemma63DirectMu lambda)
    (hC : 0 ≤ C)
    (hmoment : FordVinogradovMomentBound s 4 C delta)
    (hcMu : fordLemma63DirectSaving s delta lambda ≤
      fordLemma63DirectMu lambda)
    (hcOneMu : fordLemma63DirectSaving s delta lambda ≤
      1 - fordLemma63DirectMu lambda) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordLemma63DirectCoefficient s C *
        (N : ℝ) ^ (1 - fordLemma63DirectSaving s delta lambda) := by
  let mu := fordLemma63DirectMu lambda
  let q : ℝ := 1 / (2 * s : ℝ)
  let A : ℝ := C * (8 * Real.pi) ^ 4 * (Nat.factorial 4 : ℝ)
  let c := fordLemma63DirectSaving s delta lambda
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hP : 1 ≤ P := by
    rw [hPscale]
    exact Real.one_le_rpow hNreal hmu0
  have hPN : P ≤ N := by
    rw [hPscale]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNreal hmu1
  have ht : 0 < t := by rw [htEq]; positivity
  have htN : t ≤ (N : ℝ) ^ (4 : ℕ) := by
    rw [htEq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNreal hlambda4
  have hscaleEq : t * P ^ (4 + 1 : ℕ) = (N : ℝ) ^ (4 + 1 : ℕ) := by
    norm_num only [Nat.reduceAdd]
    rw [htEq, hPscale, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le,
      ← Real.rpow_add hNpos, ← Real.rpow_natCast]
    congr 1
    dsimp [mu, fordLemma63DirectMu]
    ring
  have hW : fordLemma63WReal N 4 P t ≤ (2 : ℝ) ^ 4 * P :=
    fordLemma63WReal_le_source_scale (by norm_num) hP ht hscaleEq
  have h63 := fordLemma63_real_cutoff
    (s := s) (k := 4) (N := N) (R := R) (P := P) (u := u) (t := t)
    hs (by norm_num) hP hPN hN hRlower hR hu0 hu1 ht htN hscaleEq.le
  have hfactor := fordCorollary64_real_moment_factor_le hP ht hW hmoment
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let X : ℝ :=
    (Real.pi ^ 4 * (Nat.factorial 4 : ℝ) * (4 : ℝ) ^ 4 *
        P ^ fordVinogradovKappa 4) *
      fordLemma63WReal N 4 P t * (fordVinogradovMoment s 4 P : ℝ)
  have hfactor' : X ≤ A * P ^ (2 * (s : ℝ) + 1 + delta) := by
    dsimp [X, A]
    norm_num at hfactor ⊢
    ring_nf at hfactor ⊢
    exact hfactor
  have hX0 : 0 ≤ X := by
    dsimp [X]
    have hW0 : 0 ≤ fordLemma63WReal N 4 P t := by
      unfold fordLemma63WReal
      positivity
    positivity
  have hroot : X ^ q ≤
      (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^ q :=
    Real.rpow_le_rpow hX0 hfactor' hq
  have hrootCancel :
      (1 / P) * (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^ q =
        (A * P ^ (1 + delta)) ^ q := by
    simpa [q] using fordCorollary64_real_root_cancel hs
      (zero_lt_one.trans_le hP) hA
  have hscaledRoot :
      (1 / P) * X ^ q ≤
        A ^ q * (N : ℝ) ^ (mu * ((1 + delta) * q)) := by
    calc
      (1 / P) * X ^ q ≤
          (1 / P) * (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^ q := by
        gcongr
      _ = (A * P ^ (1 + delta)) ^ q := hrootCancel
      _ = A ^ q * (P ^ (1 + delta)) ^ q := by
        rw [Real.mul_rpow hA (Real.rpow_nonneg (zero_lt_one.trans_le hP).le _)]
      _ = A ^ q * P ^ ((1 + delta) * q) := by
        rw [← Real.rpow_mul (zero_lt_one.trans_le hP).le]
      _ = A ^ q *
          ((N : ℝ) ^ mu) ^ ((1 + delta) * q) := by rw [hPscale]
      _ = A ^ q * (N : ℝ) ^ (mu * ((1 + delta) * q)) := by
        rw [← Real.rpow_mul hNpos.le]
  have hcEq : c = q * (1 - mu * (1 + delta)) := by
    dsimp [c, q, mu, fordLemma63DirectSaving]
    ring
  have hlead :
      4 * ((N : ℝ) ^ (1 - q) / P) * X ^ q ≤
        4 * A ^ q * (N : ℝ) ^ (1 - c) := by
    calc
      4 * ((N : ℝ) ^ (1 - q) / P) * X ^ q =
          4 * (N : ℝ) ^ (1 - q) * ((1 / P) * X ^ q) := by ring
      _ ≤ 4 * (N : ℝ) ^ (1 - q) *
          (A ^ q * (N : ℝ) ^ (mu * ((1 + delta) * q))) := by
        gcongr
      _ = 4 * A ^ q * ((N : ℝ) ^ (1 - q) *
          (N : ℝ) ^ (mu * ((1 + delta) * q))) := by ring
      _ = 4 * A ^ q *
          (N : ℝ) ^ ((1 - q) + mu * ((1 + delta) * q)) := by
        rw [Real.rpow_add hNpos]
      _ = 4 * A ^ q * (N : ℝ) ^ (1 - c) := by
        congr 2
        rw [hcEq]
        ring
  have hdivEq : (N : ℝ) / P = (N : ℝ) ^ (1 - mu) := by
    rw [hPscale, Real.rpow_sub hNpos, Real.rpow_one]
  have hdiv : (N : ℝ) / P ≤ (N : ℝ) ^ (1 - c) := by
    rw [hdivEq]
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    dsimp [c, mu] at hcMu ⊢
    linarith
  have hPbound : P ≤ (N : ℝ) ^ (1 - c) := by
    rw [hPscale]
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    dsimp [c, mu] at hcOneMu ⊢
    linarith
  apply h63.trans
  change 4 * ((N : ℝ) ^ (1 - q) / P) * X ^ q + (N : ℝ) / P + P ≤
    fordLemma63DirectCoefficient s C * (N : ℝ) ^ (1 - c)
  unfold fordLemma63DirectCoefficient
  dsimp [A, q]
  calc
    4 * ((N : ℝ) ^ (1 - q) / P) * X ^ q + (N : ℝ) / P + P ≤
        4 * A ^ q * (N : ℝ) ^ (1 - c) +
          (N : ℝ) ^ (1 - c) + (N : ℝ) ^ (1 - c) := by
      exact add_le_add (add_le_add hlead hdiv) hPbound
    _ = (4 * A ^ q + 2) * (N : ℝ) ^ (1 - c) := by ring

#print axioms fordLemma63_direct_le_power_saving

end

end GafniTao
