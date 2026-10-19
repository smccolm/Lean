import Dubon2026.MatrixPrimePowerCongruence
import Mathlib.Algebra.Group.Commute.Units

/-! Finite quotients of the actual parameter algebra carry auxiliary
cyclic group actions. This is the algebraic input for annihilator
convergence in DUB-17's arithmetic patching chain. The prime-power
congruence is reused from the existing matrix theorem. -/

namespace Dubon2026

/-- A residue-one scalar gains an ideal-power order at every
prime-power iteration, by the already proved matrix congruence. -/
theorem scalar_primePower_congruence
    {R : Type*} [CommRing R] (I : Ideal R) {q : ℕ}
    (hq : q.Prime) (hqI : (q : R) ∈ I)
    (x : R) (hx : x - 1 ∈ I) (n : ℕ) :
    x ^ (q ^ n) - 1 ∈ I ^ (n + 1) := by
  have h := matrix_primePower_congruence I hq hqI
    (Matrix.scalar (Fin 1) x) (by
      intro i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simpa using hx) n
  have he := h (0 : Fin 1) (0 : Fin 1)
  simpa only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_pow,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using he

/-- The literal image of a residue-one scalar in an ideal-power
quotient has order dividing the corresponding prime power. -/
theorem scalar_primePower_quotient_eq_one
    {R : Type*} [CommRing R] (I : Ideal R) {q : ℕ}
    (hq : q.Prime) (hqI : (q : R) ∈ I)
    (x : R) (hx : x - 1 ∈ I) (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n) x) ^ (q ^ n) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_one (Ideal.Quotient.mk (I ^ n)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_le_pow_right (Nat.le_succ n)
    (scalar_primePower_congruence I hq hqI x hx n)

end Dubon2026
