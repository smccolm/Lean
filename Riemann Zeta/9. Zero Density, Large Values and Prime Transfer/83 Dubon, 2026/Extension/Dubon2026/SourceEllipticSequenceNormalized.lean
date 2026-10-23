import Dubon2026.SourceEllipticSequenceNet
import Mathlib.Algebra.MvPolynomial.Basic

/-! DUB-17/18 -> exceptional-fiber census -> actual elliptic n-torsion
cardinality -> division-polynomial multiplication formula -> the normalized
elliptic sequence net identity. Native recurrences and the proved parity
induction establish the identity over a polynomial ring. Specializing its
three variables removes every nonzero-divisor premise, including in small
characteristic. The reference general divisibility classification and
sequence uniqueness package are not needed for this step. -/
namespace Dubon2026.SourceEllipticSequence
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]

theorem normalized_isEllSequence_of_nonZeroDivisors (b c d : R) (hb : b ∈ R⁰) :
    IsEllSequence (normEDS b c d) :=
  isEllSequence_of_oddRec_evenRec (normEDS_neg b c d) (normEDS_zero b c d)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two])
    (fun m _ => by
      simp only [OddRec, normEDS_one, one_pow, mul_one]
      exact normEDS_odd b c d m)
    (fun m _ => by
      simp only [EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
      rw [normEDS_even]
      ring)

theorem normalized_net (b c d : R) (p q r s : ℤ) :
    net (normEDS b c d) p q r s = 0 := by
  let U : ℤ → MvPolynomial (Fin 3) ℤ :=
    normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
  have hb : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℤ) ∈
      (MvPolynomial (Fin 3) ℤ)⁰ := mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero _)
  have hu : IsEllSequence U := normalized_isEllSequence_of_nonZeroDivisors _ _ _ hb
  have hn := ell_net hu (by dsimp [U]; rw [normEDS_one]; exact one_mem _)
    (by simpa only [U, normEDS_two] using hb) p q r s
  let f : MvPolynomial (Fin 3) ℤ →+* R := (MvPolynomial.aeval ![b,c,d]).toRingHom
  have hf (n : ℤ) : f (U n) = normEDS b c d n := by
    change f (normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) n) = _
    rw [map_normEDS]
    simp [f]
  have h := congrArg f hn
  simpa only [net, map_add, map_sub, map_mul, map_zero, hf] using h

theorem normalized_isEllSequence (b c d : R) : IsEllSequence (normEDS b c d) := by
  intro m n r
  have h := normalized_net b c d m n r 0
  simp only [net, add_zero] at h
  linear_combination h

theorem normalized_invariant (b c d : R) (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ (normalized_net b c d) s m n

end Dubon2026.SourceEllipticSequence
