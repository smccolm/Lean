import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # The rank obstruction to prime torsion in the original arithmetic group

DUB-17's small-level dependency needs to exclude nontrivial torsion in
finite arithmetic stabilizers. Existing congruence reductions force that
torsion to have residue-prime order. The native irreducibility of the
rational cyclotomic polynomial and Cayley-Hamilton give the precise rank
obstruction, without diagonalizing the original representation.
-/

namespace Dubon2026

noncomputable section

open Polynomial

/-- A nonidentity rational endomorphism of prime order needs at least p-1 dimensions. -/
theorem rationalPrimeOrderEndomorphism_rank_bound
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (p : ℕ) (hp : p.Prime) (f : Module.End ℚ V)
    (hpow : f ^ p = 1) (hne : f ≠ 1) : p - 1 ≤ Module.finrank ℚ V := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, map_one, hpow, sub_self]
  have hc : cyclotomic p ℚ ∣ minpoly ℚ f := by
    rcases (cyclotomic.irreducible_rat hp.pos).isCoprime_or_dvd (minpoly ℚ f) with h | h
    · obtain ⟨P, hP⟩ := h.symm.dvd_of_dvd_mul_left hd
      have he := congrArg (aeval f) hP
      simp only [map_sub, aeval_X, map_one, map_mul, minpoly.aeval, zero_mul] at he
      exact (hne (sub_eq_zero.mp he)).elim
    · exact h
  have hb := natDegree_le_of_dvd (hc.trans (LinearMap.minpoly_dvd_charpoly f))
    (LinearMap.charpoly_monic f).ne_zero
  simpa only [natDegree_cyclotomic, Nat.totient_prime hp, LinearMap.charpoly_natDegree] using hb

/-- Below the cyclotomic rank, prime torsion in the original rational linear group is trivial. -/
theorem rationalPrimeOrderEndomorphism_eq_one
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (p : ℕ) (hp : p.Prime) (hV : Module.finrank ℚ V < p - 1)
    (f : Module.End ℚ V) (hpow : f ^ p = 1) : f = 1 := by
  by_contra hne
  exact (not_le_of_gt hV) (rationalPrimeOrderEndomorphism_rank_bound p hp f hpow hne)

end
end Dubon2026
