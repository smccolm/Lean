import Dubon2026.SourceEllipticSequenceComplement

/-! The native complement sequence supplies the exact division needed for the
integral division-polynomial y-coordinate, including characteristics two and
three. This serves DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 through actual
torsion cardinality, the finite exceptional-fiber census, reverse genus and
good reduction. The argument adapts the complement proof in the archived
Apache-2.0 anthropics/fermats-last-theorem EDSEngine, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, directly to Mathlib's native
complEDS; no duplicate complement sequence or divisibility classification is
introduced. -/

namespace Dubon2026.SourceEllipticSequence
open scoped nonZeroDivisors
variable {R S : Type*} [CommRing R] [CommRing S] (b c d : R)

theorem invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    invarNum W 1 n = W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [invarNum]
theorem invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]
theorem invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]


variable (m : ℤ)

/-- The integral auxiliary term in the doubling complement. -/
def complEDS₂Aux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] theorem complEDS₂Aux_zero : complEDS₂Aux b c d 0 = -1 := by simp [complEDS₂Aux]
@[simp] theorem complEDS₂Aux_one : complEDS₂Aux b c d 1 = -b := by simp [complEDS₂Aux]
@[simp] theorem complEDS₂Aux_neg_one : complEDS₂Aux b c d (-1) = 0 := by simp [complEDS₂Aux]
@[simp] theorem complEDS₂Aux_two : complEDS₂Aux b c d 2 = 0 := by simp [complEDS₂Aux]
@[simp] theorem complEDS₂Aux_neg_two : complEDS₂Aux b c d (-2) = -d := by simp [complEDS₂Aux]

theorem complEDS₂Aux_mul_b :
    complEDS₂Aux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDS₂Aux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

theorem complEDS₂Aux_neg : complEDS₂Aux b c d (-m) = -complEDS₂ b c d m - complEDS₂Aux b c d m := by
  simp_rw [complEDS₂Aux, complEDS₂, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

theorem normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂, if_neg (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]
  ring

/-- The invariant numerator after removing the universal second term. -/
def redInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m

theorem complEDS₂_eq_redInvarNum_sub :
    complEDS₂ b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDS₂Aux b c d m := by
  rw [redInvarNum]; ring

theorem invarNum_eq_redInvarNum_mul : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b,
    complEDS₂Aux_mul_b, invarNum_normEDS]; ring

/-- The integral invariant denominator, using native complement quotients. -/
def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

theorem invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd (k m : ℤ) (dvd : k ∣ 6) (eq : m % 6 % k = 0) : k ∣ m :=
    Int.dvd_iff_emod_eq_zero.mpr ((Int.emod_emod_of_dvd m dvd).symm.trans eq)
  have hd2 {m} := hd 2 m ⟨3, rfl⟩
  have hd3 {m} := hd 3 m ⟨2, rfl⟩

  have dvd_sub {a b c : ℤ} (h : a % b = c) : b ∣ a - c := by
    rw [← h, Int.emod_def, sub_sub_cancel]
    exact dvd_mul_right _ _
  have mul_eq (k : ℤ) := normalized_mul_complement_div b c d (k := k)
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h
  · rw [← mul_eq _ h6 _ (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [← mul_eq _ h6 _ (dvd_sub h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel, ← mul_eq _ h6, normEDS_six_eq_mul]; ring
    exact dvd_sub (show (m + 6) % 6 = 5 by omega)
  on_goal 1 => rw [← mul_eq _ h3 _ (hd3 <| by simp [h, Int.add_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 2 => rw [← mul_eq _ h3 (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 3 => rw [← mul_eq _ h3 m (hd3 <| by simp [h]),
    ← mul_eq _ two_ne_zero (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] theorem redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom]

@[simp] theorem redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom]

@[simp] theorem redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom]


variable (f : R →+* S)

theorem map_complEDS₂Aux : f (complEDS₂Aux b c d m) = complEDS₂Aux (f b) (f c) (f d) m := by
  have mp : ∀ n : ℤ, f (preNormEDS (b ^ 4) c d n) = preNormEDS (f b ^ 4) (f c) (f d) n :=
    fun n ↦ by
      rw [show f b ^ 4 = f (b ^ 4) from (map_pow f b 4).symm]
      exact map_preNormEDS (b ^ 4) c d f n
  simp [complEDS₂Aux, apply_ite f, mp]

theorem map_redInvarNum : f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS b c d f n
  simp [redInvarNum, map_complEDS₂, mn, map_complEDS₂Aux, map_ofNat]

theorem map_redInvarDenom : f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS b c d f n
  simp [redInvarDenom, apply_ite f, mn, map_complEDS]


end Dubon2026.SourceEllipticSequence
