import Dubon2026.SourceLocalCyclotomicAction
import Dubon2026.ArithmeticCyclotomicRestriction
import Dubon2026.RationalPrimeNormResidueCard
import Mathlib.Algebra.CharP.Basic

/-! DUB-17/18 -> residual Galois association -> boundary Dirichlet pair.
The original rational completion and norm residue field supply the actual
cyclotomic Frobenius value and inertia triviality away from the conductor.
The existing arithmetic restriction retains the same global/local embedding.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The original closure norm residue field has the prescribed rational
prime characteristic, using the already proved base residue cardinality. -/
theorem sourceOriginalClosureResidue_charP (p : ℕ) (hp : p.Prime) :
    CharP (IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp))) p := by
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  letI : Finite (IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalField p hp))) :=
    Nat.finite_of_card_ne_zero (by rw [rationalPrimeOriginalNorm_residue_card p hp]; exact hp.ne_zero)
  have h := algebraicLocal_residue_cast_card_eq_zero
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  rwa [rationalPrimeOriginalNorm_residue_card p hp] at h

/-- Every original residue Frobenius has cyclotomic exponent equal to
the same rational prime modulo the conductor. -/
theorem sourceOriginalCyclotomic_frobenius
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n] (hpn : ¬p ∣ n)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp)), g • x = x ^ p) :
    rationalPrimeCyclotomicCharacter p hp n g =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) := by
  letI := sourceOriginalClosureResidue_charP p hp
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (rationalPrimeLocalClosure p hp) n
  have hn : (n : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp))) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ p]
  have he := sourceLocal_frobenius_root (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) n p (NeZero.ne n) hn g hg ζ hζ.pow_eq_one
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← rationalPrimeCyclotomicCharacter_apply_root p hp n g hζ, he,
    ZMod.coe_unitOfCoprime, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]

/-- Original norm inertia acts trivially under the cyclotomic character
at every rational prime away from its conductor. -/
theorem sourceOriginalCyclotomic_inertia
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n] (hpn : ¬p ∣ n)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : g ∈ rationalPrimeNormInertia p hp) :
    rationalPrimeCyclotomicCharacter p hp n g = 1 := by
  letI := sourceOriginalClosureResidue_charP p hp
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (rationalPrimeLocalClosure p hp) n
  have hn : (n : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp))) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ p]
  have he := sourceLocal_inertia_root (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) n (NeZero.ne n) hn g hg ζ hζ.pow_eq_one
  have h1 := rationalPrimeCyclotomicCharacter_apply_root p hp n 1 hζ
  rw [map_one] at h1
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact (rationalPrimeCyclotomicCharacter_apply_root p hp n g hζ).symm.trans
    (he.trans h1)

/-- The original arithmetic cyclotomic character has the required value
on the same restricted local residue Frobenius. -/
theorem sourceArithmeticCyclotomic_frobenius
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ n)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure p hp)), g • x = x ^ p) :
    rationalArithmeticCyclotomicCharacter a n hna
      (rationalPrimeArithmeticRestriction a p hp g) =
        ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) := by
  have h := DFunLike.congr_fun
    (rationalArithmeticCyclotomicCharacter_restriction a n hna p hp) g
  exact h.trans (sourceOriginalCyclotomic_frobenius p hp n hpn g hg)

/-- The same arithmetic restriction kills original norm inertia in every
cyclotomic conductor prime to the local rational prime. -/
theorem sourceArithmeticCyclotomic_inertia
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ n)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : g ∈ rationalPrimeNormInertia p hp) :
    rationalArithmeticCyclotomicCharacter a n hna
      (rationalPrimeArithmeticRestriction a p hp g) = 1 := by
  have h := DFunLike.congr_fun
    (rationalArithmeticCyclotomicCharacter_restriction a n hna p hp) g
  exact h.trans (sourceOriginalCyclotomic_inertia p hp n hpn g hg)

end
end Dubon2026
