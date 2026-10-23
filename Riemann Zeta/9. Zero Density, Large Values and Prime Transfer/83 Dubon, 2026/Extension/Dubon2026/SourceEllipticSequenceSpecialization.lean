import Dubon2026.SourceEllipticSequenceNormalized

/-! DUB-17/18 -> exceptional-fiber census -> actual elliptic n-torsion
cardinality -> division-polynomial multiplication formula -> the normalized
elliptic sequence net identity. Native recurrences and the proved parity
induction establish the identity over a polynomial ring. Specializing its
three variables removes every nonzero-divisor premise, including in small
characteristic. The reference general divisibility classification and
sequence uniqueness package are not needed for this step. -/
namespace Dubon2026.SourceEllipticSequence
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] {W U : ℤ → R}

theorem ell_ext (ellW : IsEllSequence W) (ellU : IsEllSequence U) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U := by
  funext n
  induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
    · rw [Nat.cast_zero, (ell_zero ellW) 1 two, (ell_zero ellU) 1 (h2 ▸ two)]
    · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
        ← mul_assoc, Nat.cast_mul, Nat.cast_add, (ell_evenRec ellW), h1, h2, (ell_evenRec ellU)]
      convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> omega
    · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
      erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, (ell_oddRec ellW), h1, (ell_oddRec ellU)]
      convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> omega
  | neg ih n => rw [(ell_neg ellW) one two, (ell_neg ellU) (h1 ▸ one) (h2 ▸ two), ih]

theorem normEDS_two_three_two : normEDS 2 3 2 = id := by
  apply ell_ext (normalized_isEllSequence _ _ _) isEllSequence_id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]

theorem complEDS₂_two_three_two (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact complEDS₂_zero ..
  · have := normEDS_mul_complEDS₂ (2 : ℤ) 3 2 n
    rwa [normEDS_two_three_two, id_eq, id_eq, mul_comm,
      mul_cancel_right_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn)] at this


end Dubon2026.SourceEllipticSequence
