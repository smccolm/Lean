import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Data.ZMod.Basic

/-! DUB-17/18 -> actual rank-two realization -> odd original determinant.
The original residue characteristic supplies the finite cyclotomic scalar
map at every positive adic precision. This will identify the constructed
determinant by the proved norm-Frobenius uniqueness theorem. -/
namespace Dubon2026
noncomputable section
variable {R : Type} [CommRing R] [IsLocalRing R]

/-- The original positive adic quotient kills the matching prime power,
derived from the actual residue characteristic. -/
theorem adicQuotient_prime_power_zero (p n : ℕ) [CharP (IsLocalRing.ResidueField R) p] :
    ((p ^ (n + 1) : ℕ) : R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) = 0 := by
  have hp : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    apply (IsLocalRing.residue_eq_zero_iff (p : R)).mp
    rw [map_natCast, CharP.cast_eq_zero]
  rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n + 1)))]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [Nat.cast_pow] using Ideal.pow_mem_pow hp (n + 1)

/-- The genuine scalar map from the original prime-power integers to the
matching original coefficient quotient. -/
def adicQuotientPrimePowerMap (p n : ℕ) [CharP (IsLocalRing.ResidueField R) p] :
    ZMod (p ^ (n + 1)) →+* R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1) :=
  ZMod.castHom ((CharP.cast_eq_zero_iff
    (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
    (ringChar (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))) _).mp
      (adicQuotient_prime_power_zero (R := R) p n)) _

end
end Dubon2026
