import GafniTao.FordLemma36Theta

/-!
# Ford Lemma 3.6: maximal-index and dyadic estimates

This file proves the integer content behind Ford's assertion that the maximal
index in (3.8) is at least `sqrt (2k-2)`, and proves the numerical dyadic
estimate used immediately after (3.12), without floating-point evaluation.
-/

namespace GafniTao

noncomputable section

theorem fordSqrt36_ge_fortyFour {k : ℕ} (hk : 1000 ≤ k) :
    44 ≤ Nat.sqrt (2 * k - 2) := by
  rw [Nat.le_sqrt]
  omega

theorem fordSqrt36_three_mul_le {k : ℕ} (hk : 1000 ≤ k) :
    3 * Nat.sqrt (2 * k - 2) ≤ k := by
  let q := Nat.sqrt (2 * k - 2)
  have hq44 : 44 ≤ q := fordSqrt36_ge_fortyFour hk
  have hsq : q * q ≤ 2 * k - 2 := Nat.sqrt_le _
  change 3 * q ≤ k
  by_contra h
  have hkq : k < 3 * q := by omega
  have hbad : q * q ≤ 6 * q - 4 := by omega
  have hbad' : q * q + 4 ≤ 6 * q := by omega
  have hbadR : (q : ℝ) ^ 2 + 4 ≤ 6 * q := by
    rw [pow_two]
    exact_mod_cast hbad'
  have hqR : (44 : ℝ) ≤ q := by exact_mod_cast hq44
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q - 6)
    (by positivity : (0 : ℝ) ≤ q)]

theorem fordR36_double_lower
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    k + 1 ≤ 2 * fordR36 k delta := by
  have hk26 : 26 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hreal := (fordR36_real_bounds hk26 hdeltaUpper).1
  have hdiv : delta / (k : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
    apply (div_le_iff₀ hkR).2
    nlinarith
  have hreal' : ((k : ℝ) + 1) ≤ 2 * fordR36 k delta := by
    nlinarith
  exact_mod_cast hreal'

theorem fordJ35_rounded_sqrt_lower
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    Nat.sqrt (2 * k - 2) + 1 ≤
      fordJ35 k (fordR36 k delta) delta := by
  let q := Nat.sqrt (2 * k - 2)
  let r := fordR36 k delta
  have hk26 : 26 ≤ k := by omega
  have hdeltaLower' : (k : ℝ) ≤ delta := hdeltaLower.le
  have hr := fordR36_bounds hk26 hdeltaLower' hdeltaUpper
  have hy0 := fordY35_rounded_nonneg hk26 hdeltaLower' hdeltaUpper
  have hyBounds := fordY35_rounded_bounds hk26 hdeltaLower' hdeltaUpper
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 1 < delta / (k : ℝ) := by
    apply (lt_div_iff₀ hkR).2
    simpa using hdeltaLower
  have hupper : delta / (k : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
    apply (div_le_iff₀ hkR).2
    nlinarith
  have hfactor : 0 ≤ 2 * (k : ℝ) - delta / (k : ℝ) - 2 := by
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hprod :
      2 * (k : ℝ) - 2 ≤
        (delta / (k : ℝ)) *
          (2 * (k : ℝ) - delta / (k : ℝ) - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.le) hfactor]
  have hyLower : ((2 * k - 2 : ℕ) : ℝ) ≤ fordY35 k r delta := by
    have hcast : ((2 * k - 2 : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * k)]
      push_cast
      ring
    rw [hcast]
    exact hprod.trans (by simpa [r] using hyBounds.1)
  have hqSq : q * q ≤ 2 * k - 2 := Nat.sqrt_le _
  have hadm :
      2 ≤ q + 1 ∧
        (((q + 1 - 1) * (q + 1 - 2) : ℕ) : ℝ) ≤
          fordY35 k r delta := by
    constructor
    · have : 44 ≤ q := fordSqrt36_ge_fortyFour hk
      omega
    · have hnat : (q + 1 - 1) * (q + 1 - 2) ≤ 2 * k - 2 := by
        have hqpos : 1 ≤ q := by
          have := fordSqrt36_ge_fortyFour hk
          omega
        have hmul : q * (q - 1) ≤ q * q :=
          Nat.mul_le_mul_left q (Nat.sub_le q 1)
        simpa [show q + 1 - 1 = q by omega,
          show q + 1 - 2 = q - 1 by omega] using hmul.trans hqSq
      have hnatReal :
          (((q + 1 - 1) * (q + 1 - 2) : ℕ) : ℝ) ≤
            ((2 * k - 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      exact hnatReal.trans hyLower
  have hq3 : 3 * q ≤ k := fordSqrt36_three_mul_le hk
  change 3 * q ≤ k at hq3
  have hr2 : k + 1 ≤ 2 * r := by
    simpa [r] using fordR36_double_lower hk hdeltaUpper
  have hrange : q + 1 ≤ 9 * r / 10 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).2
    change (q + 1) * 10 ≤ 9 * r
    omega
  change q + 1 ≤ fordJ35 k r delta
  by_contra h
  have hjq : fordJ35 k r delta < q + 1 := by omega
  exact (fordJ35_maximal hjq hrange) hadm

private theorem fordDyadicPolynomialAux
    {q : ℕ} (hq : 44 ≤ q) :
    125 * (((q + 1) ^ 2 + 1) ^ 4) ≤ 142 * 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      let A := (q + 1) ^ 2 + 1
      let B := (q + 2) ^ 2 + 1
      have hAB : 6 * B ≤ 7 * A := by
        dsimp [A, B]
        nlinarith
      have hp : (6 * B) ^ 4 ≤ (7 * A) ^ 4 := by gcongr
      norm_num [mul_pow] at hp
      have hB : B ^ 4 ≤ 2 * A ^ 4 := by omega
      calc
        125 * (((q + 1 + 1) ^ 2 + 1) ^ 4) = 125 * B ^ 4 := by
          simp [B, Nat.add_assoc]
        _ ≤ 2 * (125 * A ^ 4) := by omega
        _ ≤ 2 * (142 * 2 ^ q) := Nat.mul_le_mul_left 2 ih
        _ = 142 * 2 ^ (q + 1) := by rw [pow_succ]; ring

theorem fordDyadicPolynomial36 {k : ℕ} (hk : 1000 ≤ k) :
    1000 * k ^ 4 ≤ 71 * 2 ^ Nat.sqrt (2 * k - 2) := by
  let q := Nat.sqrt (2 * k - 2)
  let A := (q + 1) ^ 2 + 1
  have hq44 : 44 ≤ q := fordSqrt36_ge_fortyFour hk
  have hsqrt : 2 * k - 2 < (q + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hkA : 2 * k ≤ A := by
    dsimp [A]
    omega
  have hp : (2 * k) ^ 4 ≤ A ^ 4 := by gcongr
  norm_num [mul_pow] at hp
  have haux : 125 * A ^ 4 ≤ 142 * 2 ^ q := by
    simpa [A] using fordDyadicPolynomialAux hq44
  have htwo : 2000 * k ^ 4 ≤ 142 * 2 ^ q := by
    calc
      2000 * k ^ 4 = 125 * (16 * k ^ 4) := by ring
      _ ≤ 125 * A ^ 4 := Nat.mul_le_mul_left 125 hp
      _ ≤ 142 * 2 ^ q := haux
  change 1000 * k ^ 4 ≤ 71 * 2 ^ q
  have hcancel : 2 * (1000 * k ^ 4) ≤ 2 * (71 * 2 ^ q) := by
    calc
      2 * (1000 * k ^ 4) = 2000 * k ^ 4 := by ring
      _ ≤ 142 * 2 ^ q := htwo
      _ = 2 * (71 * 2 ^ q) := by ring
  exact Nat.le_of_mul_le_mul_left hcancel (by norm_num)

theorem fordDyadicTerm36
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    (1 / (fordR36 k delta : ℝ)) /
        (2 : ℝ) ^ (fordJ35 k (fordR36 k delta) delta - 1) ≤
      (71 / 1000 : ℝ) /
        ((k : ℝ) ^ 4 * fordR36 k delta) := by
  let q := Nat.sqrt (2 * k - 2)
  let r := fordR36 k delta
  let j := fordJ35 k r delta
  have hk26 : 26 ≤ k := by omega
  have hrNat := (fordR36_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hj : q + 1 ≤ j := by
    simpa [q, r, j] using fordJ35_rounded_sqrt_lower hk hdeltaLower hdeltaUpper
  have hqj : q ≤ j - 1 := by omega
  have hpowNat : 2 ^ q ≤ 2 ^ (j - 1) :=
    pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hqj
  have hpolyNat := fordDyadicPolynomial36 hk
  have hpoly :
      1000 * (k : ℝ) ^ 4 ≤ 71 * (2 : ℝ) ^ (j - 1) := by
    exact_mod_cast hpolyNat.trans (Nat.mul_le_mul_left 71 hpowNat)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpj : 0 < (2 : ℝ) ^ (j - 1) := by positivity
  have hkr : 0 < (k : ℝ) ^ 4 * r := mul_pos (by positivity) hr
  calc
    (1 / (fordR36 k delta : ℝ)) /
        (2 : ℝ) ^ (fordJ35 k (fordR36 k delta) delta - 1) =
      1 / (r * (2 : ℝ) ^ (j - 1)) := by
        change (1 / (r : ℝ)) / (2 : ℝ) ^ (j - 1) =
          1 / ((r : ℝ) * (2 : ℝ) ^ (j - 1))
        rw [div_div]
    _ ≤ (71 / 1000 : ℝ) / ((k : ℝ) ^ 4 * r) := by
      rw [div_le_div_iff₀ (mul_pos hr hpj) hkr]
      field_simp
      nlinarith

#print axioms fordJ35_rounded_sqrt_lower
#print axioms fordDyadicPolynomial36
#print axioms fordDyadicTerm36

end

end GafniTao
