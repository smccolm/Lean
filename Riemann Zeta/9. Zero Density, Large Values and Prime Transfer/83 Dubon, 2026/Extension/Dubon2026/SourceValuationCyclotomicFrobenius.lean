import Dubon2026.SourceValuationFrobeniusRoots
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! DUB-17/18 -> primitive Frobenius determinant. Evaluate the actual
padic cyclotomic character at the exact valuation-subring arithmetic
Frobenius used by the original Tate quadratic theorem. Root separation
and residue characteristic are reused from the existing local proofs. -/
namespace Dubon2026
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ

theorem valuation_cyclotomic_frobenius (A : ValuationSubring Qbar)
    (p : ℕ) (hp : p.Prime) (ell : ℕ) [Fact ell.Prime] (hpl : ¬p ∣ ell)
    (hA : (p : Qbar) ∈ A.nonunits) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hσ : ∃ hd : σ ∈ A.decompositionSubgroup ℚ,
      ∀ a : IsLocalRing.ResidueField A,
        (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    (cyclotomicCharacter Qbar ell σ.toRingEquiv : ℤ_[ell]) = (p : ℤ_[ell]) := by
  letI := SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits A p hp hA
  obtain ⟨hd, hσ⟩ := hσ
  have hell : (ell : IsLocalRing.ResidueField A) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ p]
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar (ell ^ k)
  have he := valuation_frobenius_root A (ell ^ k) p
    (pow_ne_zero k (Fact.out : ell.Prime).ne_zero)
    (by simpa only [Nat.cast_pow] using pow_ne_zero k hell)
    ⟨σ, hd⟩ hσ ζ hζ.pow_eq_one
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← cyclotomicCharacter.spec ell σ.toRingEquiv ζ hζ.pow_eq_one]
  change σ ζ = _
  rw [he, map_natCast, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]

end
end Dubon2026
