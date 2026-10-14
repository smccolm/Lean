import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-! # The required translated prime-power cyclotomic polynomial

Transport the pinned integral cyclotomic Eisenstein theorem to the actual
coefficient ring when the original prime remains prime. This applies both
to the original rational prime valuation integers and the Witt coefficient
ring. It supplies the actual finite cyclotomic root algebra for convergent
evaluation of DUB-17's constructed semilinear series; no general formal
module or new cyclotomic irreducibility argument is needed.
-/
namespace Dubon2026
noncomputable section
open Polynomial

/-- The actual translated prime-power cyclotomic polynomial. -/
def primePowerShiftedCyclotomic (R : Type*) [CommRing R] (p n : ℕ) : R[X] :=
  (cyclotomic (p ^ (n + 1)) R).comp (X + 1)

/-- The actual translated polynomial is monic. -/
theorem primePowerShiftedCyclotomic_monic (R : Type*) [CommRing R] (p n : ℕ) :
    (primePowerShiftedCyclotomic R p n).Monic := by
  exact (cyclotomic.monic _ R).comp_X_add_C 1

/-- Its constant coefficient is the original prime. -/
theorem primePowerShiftedCyclotomic_coeff_zero (R : Type*) [CommRing R]
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (primePowerShiftedCyclotomic R p n).coeff 0 = p := by
  rw [primePowerShiftedCyclotomic, coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_add, eval_X, eval_one, zero_add]
  exact eval_one_cyclotomic_prime_pow n

/-- Its degree is the exact degree of the prime-power cyclotomic extension. -/
theorem primePowerShiftedCyclotomic_natDegree (R : Type*) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (primePowerShiftedCyclotomic R p n).natDegree = (p - 1) * p ^ n := by
  rw [primePowerShiftedCyclotomic, natDegree_comp,
    show (X + 1 : R[X]) = X + C 1 by simp, natDegree_X_add_C,
    mul_one, natDegree_cyclotomic, Nat.totient_prime_pow (Fact.out : p.Prime) (Nat.succ_pos n)]
  simp [Nat.mul_comm]

/-- The pinned integral Eisenstein theorem transfers whenever the actual prime is a prime element of the coefficient ring. -/
theorem primePowerShiftedCyclotomic_isEisensteinAt
    (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime]
    (hpR : Prime (p : R)) (n : ℕ) :
    (primePowerShiftedCyclotomic R p n).IsEisensteinAt (Ideal.span {(p : R)}) := by
  let F := primePowerShiftedCyclotomic ℤ p n
  have hF : F.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hmap : F.map (Int.castRingHom R) = primePowerShiftedCyclotomic R p n := by
    simp [F, primePowerShiftedCyclotomic, Polynomial.map_comp]
  have hdegree : (primePowerShiftedCyclotomic R p n).natDegree = F.natDegree := by
    rw [← hmap]
    exact (primePowerShiftedCyclotomic_monic ℤ p n).natDegree_map _
  apply (primePowerShiftedCyclotomic_monic R p n).isEisensteinAt_of_mem_of_notMem
    ((Ideal.span_singleton_prime hpR.ne_zero).mpr hpR).ne_top
  · intro i hi
    rw [← hmap, coeff_map, Ideal.mem_span_singleton]
    have hdiv := Ideal.mem_span_singleton.mp (hF.mem (hdegree ▸ hi))
    simpa only [map_natCast, map_intCast, Int.cast_natCast] using
      map_dvd (Int.castRingHom R) hdiv
  · rw [primePowerShiftedCyclotomic_coeff_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have hpow : ¬(p : R) ^ 2 ∣ (p : R) ^ 1 := by
      rw [pow_dvd_pow_iff hpR.ne_zero hpR.not_unit]
      omega
    simpa only [pow_one] using hpow

end
end Dubon2026
