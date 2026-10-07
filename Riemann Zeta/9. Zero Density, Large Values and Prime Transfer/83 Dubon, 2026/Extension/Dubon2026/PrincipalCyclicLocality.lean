import Dubon2026.PrincipalLowerProjection

/-! # A prime divisor translation belongs to exactly its local matrix factor -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal
attribute [local instance] primeFactorBaseNeZero primeFactorLevelNeZero primeFactorLowerFintype

/-- Every integral matrix component in the actual prime-factor equivalence is ordinary entrywise reduction. -/
theorem principalPrimeFactors_mk_entry (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (p : N.primeFactors) (i j : Fin 2) :
    principalPrimeFactorsEquiv N (QuotientGroup.mk γ) p i j =
      (γ i j : ZMod (p.val ^ N.factorization p.val)) := by
  change ZMod.equivPi N (NeZero.ne N) ((γ i j : ℤ) : ZMod N) p = _
  rw [map_intCast]
  rfl

/-- Removing a different prime leaves the entire q-primary factor of the level divisible. -/
theorem primeFactor_power_dvd_div (N : ℕ) [NeZero N]
    (p q : N.primeFactors) (hpq : p ≠ q) : q.val ^ N.factorization q.val ∣ N / p.val := by
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hq := Nat.prime_of_mem_primeFactors q.property
  have hqp : q.val ≠ p.val := fun h => hpq (Subtype.ext h.symm)
  have hc : (q.val ^ N.factorization q.val).Coprime p.val :=
    ((Nat.coprime_primes hq hp).mpr hqp).pow_left _
  apply (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_primeFactors p.property)).mpr
  simpa only [mul_comm] using hc.mul_dvd_of_dvd_of_dvd
    ((hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mpr le_rfl)
    (Nat.dvd_of_mem_primeFactors p.property)

/-- The prime translation generator is the identity in every distinct local matrix factor. -/
theorem principalCyclicGenerator_other_component (N : ℕ) [NeZero N]
    (p q : N.primeFactors) (hpq : p ≠ q) :
    principalPrimeFactorsEquiv N (principalCyclicGenerator N p.val) q = 1 := by
  have hz : (-(N / p.val : ℕ) : ZMod (q.val ^ N.factorization q.val)) = 0 := by
    rw [neg_eq_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (primeFactor_power_dvd_div N p q hpq)
  ext i j
  unfold principalCyclicGenerator
  rw [principalPrimeFactors_mk_entry]
  simp only [ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j
  · simp
  · change ((-((N / p.val : ℕ) : ℤ) : ℤ) : ZMod (q.val ^ N.factorization q.val)) = 0
    simpa only [Int.cast_neg, Int.cast_natCast] using hz
  · simp
  · simp

/-- The actual prime translation generator is supported in precisely its own prime-power factor. -/
theorem principalCyclicGenerator_eq_local (N : ℕ) [NeZero N] (p : N.primeFactors) :
    principalCyclicGenerator N p.val = principalPrimeFactorEmbedding N p
      (principalPrimeFactorsEquiv N (principalCyclicGenerator N p.val) p) := by
  apply (principalPrimeFactorsEquiv N).injective
  rw [principalPrimeFactorEmbedding_components]
  funext q
  by_cases hpq : p = q
  · subst q
    simp
  · rw [principalCyclicGenerator_other_component N p q hpq]
    simp [Pi.mulSingle_eq_of_ne (Ne.symm hpq)]

/-- Every operator from a different lower-triangular factor commutes with a prime Fourier projection. -/
theorem principalLowerDivisorProjection_cross_commute (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p q : N.primeFactors) (hpq : p ≠ q) :
    Commute (principalLowerProjection N k f p)
      (principalOrbitDivisorProjection (Nat.dvd_of_mem_primeFactors q.property) k f) := by
  letI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
  apply finiteGroupProjection_commute
  intro g a
  have hgen : Commute (principalPrimeFactorEmbedding N p g.val) (principalCyclicGenerator N q.val) := by
    rw [principalCyclicGenerator_eq_local]
    exact principalPrimeFactorEmbedding_commute N p q hpq _ _
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective a.toAdd
  change Commute (principalCuspOrbitRepresentation N k f (principalPrimeFactorEmbedding N p g.val))
    (principalCuspOrbitRepresentation N k f (finiteCyclicHom q.val (principalCyclicGenerator N q.val)
      (principalCyclicGenerator_pow (Nat.dvd_of_mem_primeFactors q.property)) (Multiplicative.ofAdd (j : ZMod q.val))))
  rw [finiteCyclicHom_intCast]
  exact (hgen.zpow_right j).map (principalCuspOrbitRepresentation N k f)

end
end Dubon2026
