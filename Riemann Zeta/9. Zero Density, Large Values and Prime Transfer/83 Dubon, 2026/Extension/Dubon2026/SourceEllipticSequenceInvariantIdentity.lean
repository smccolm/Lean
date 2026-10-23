import Dubon2026.SourceEllipticSequenceReducedInvariant

/-! Integral invariant identity needed to construct the division-polynomial
y-coordinate in all characteristics. The native complement and normalized
net proofs discharge all divisibility and regularity inputs. This is on the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 dependency chain through torsion,
finite exceptional fibers, reverse genus and good reduction. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/

namespace Dubon2026.SourceEllipticSequence
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] (b c d : R)

private theorem invariant_two_regular (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc,
    mul_comm (invarDenom _ _ _)]
  convert normalized_invariant b c d 1 m 2 <;>
    simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

private theorem reduced_invariant_regular (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb,
    ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invariant_two_regular b c d hb,
    invarDenom_eq_redInvarDenom_mul]
  ring

theorem reduced_invariant_identity (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have h := reduced_invariant_regular (MvPolynomial.X (0 : Fin 3))
    (MvPolynomial.X 1) (MvPolynomial.X 2)
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) _))
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := ℤ) _)) m
  let f : MvPolynomial (Fin 3) ℤ →+* R := (MvPolynomial.aeval ![b,c,d]).toRingHom
  have hh := congrArg f h
  rw [map_redInvarNum, map_mul, map_redInvarDenom, map_add, map_pow] at hh
  simpa [f] using hh

end Dubon2026.SourceEllipticSequence
