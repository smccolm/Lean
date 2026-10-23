import Dubon2026.SourceEllipticSequenceSpecialization

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
variable {R : Type*} [CommRing R] (b c d : R)

private theorem complement_of_regular (k : ℤ) (hk : normEDS b c d k ∈ R⁰) (n : ℤ) :
    normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k) := by
  induction n using Int.negInduction with
  | nat n =>
    induction n using complEDSRec with
    | zero => simp
    | one => simp
    | even m ih =>
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, complEDS_even]
      simp only [Nat.cast_add, Nat.cast_one] at ih
      rw [← mul_assoc, ih, normEDS_mul_complEDS₂]
      congr 1
      ring
    | odd m ih₁ ih₂ =>
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, complEDS_odd]
      rw [show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 by ring]
      rw [← mul_cancel_right_mem_nonZeroDivisors hk]
      have h := normalized_isEllSequence b c d (((m : ℤ) + 2) * k) (((m : ℤ) + 1) * k) 1
      rw [show ((m : ℤ) + 2) * k + ((m : ℤ) + 1) * k =
        (2 * ((m : ℤ) + 1) + 1) * k by ring,
        show ((m : ℤ) + 2) * k - ((m : ℤ) + 1) * k = k by ring] at h
      simp only [normEDS_one, one_pow, mul_one] at h
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at ih₁ ih₂
      rw [← ih₁, ← ih₂] at h
      linear_combination -h
  | neg ih n =>
    rw [complEDS_neg, mul_neg, neg_mul, normEDS_neg, ih]

theorem normalized_mul_complement (k n : ℤ) :
    normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k) := by
  obtain rfl | hk := eq_or_ne k 0
  · simp
  let U : ℤ → MvPolynomial (Fin 3) ℤ :=
    normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
  have hU : U k ≠ 0 := by
    intro h
    let g : MvPolynomial (Fin 3) ℤ →+* ℤ := (MvPolynomial.aeval ![2,3,2]).toRingHom
    have hg (m : ℤ) : g (U m) = m := by
      change g (normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) m) = _
      rw [map_normEDS]
      simpa [g] using congrFun normEDS_two_three_two m
    have hh := congrArg g h
    exact hk (by simpa only [hg, map_zero] using hh)
  have h := complement_of_regular (MvPolynomial.X (0 : Fin 3)) (MvPolynomial.X 1)
    (MvPolynomial.X 2) k (mem_nonZeroDivisors_of_ne_zero hU) n
  let f : MvPolynomial (Fin 3) ℤ →+* R := (MvPolynomial.aeval ![b,c,d]).toRingHom
  have hn (m : ℤ) : f (normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) m) =
      normEDS b c d m := by rw [map_normEDS]; simp [f]
  have hc : f (complEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) k n) =
      complEDS b c d k n := by rw [map_complEDS]; simp [f]
  simpa only [map_mul, hn, hc] using congrArg f h

theorem normalized_mul_complement_div {k : ℤ} (hk : k ≠ 0) (n : ℤ) (hkn : k ∣ n) :
    normEDS b c d k * complEDS b c d k (n / k) = normEDS b c d n := by
  obtain ⟨m, rfl⟩ := hkn
  rw [Int.mul_ediv_cancel_left _ hk, normalized_mul_complement, mul_comm]

end Dubon2026.SourceEllipticSequence
