import Dubon2026.SourceLaurentRootTwist
import Dubon2026.SourceLaurentCoefficientMap
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! DUB-17/18 -> Hecke reduction compatibility -> the integral Laurent
norm product. Prime-order roots of unity lie in the actual valuation ring,
are units, and reduce to one in residue characteristic p. Coefficient maps
commute with twists over that ring. This adapts the elementary valuation
section of anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem coeffMap_qTwist_commRing {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (u : Rˣ) (y : LaurentSeries R) :
    coeffMap φ (qTwist u y) = qTwist (Units.map φ.toMonoidHom u) (coeffMap φ y) := by
  ext n
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map]
  rfl

variable {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) [Fact p.Prime]

theorem primeRoot_mem_valuation {ζ : L} (hζ : IsPrimitiveRoot ζ p) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have he : (ζ⁻¹) ^ (p - 1) = ζ := by
      rw [inv_pow]
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le, hζ.pow_eq_one]
    rw [← he]
    exact pow_mem h _

/-- The actual valuation-ring unit given by a prime-order root of unity. -/
def primeRootValuationUnit {ζ : L} (hζ : IsPrimitiveRoot ζ p) : Aˣ :=
  Units.ofPowEqOne (⟨ζ, primeRoot_mem_valuation A p hζ⟩ : A) p
    (Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζ.pow_eq_one)) (NeZero.ne p)

theorem primeRootValuationUnit_coe {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    ((primeRootValuationUnit A p hζ : A) : L) = ζ := rfl

theorem primeRootValuationUnit_residue [CharP (IsLocalRing.ResidueField A) p]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Units.map (IsLocalRing.residue A).toMonoidHom (primeRootValuationUnit A p hζ) = 1 := by
  have hp : (Units.map (IsLocalRing.residue A).toMonoidHom (primeRootValuationUnit A p hζ)) ^ p = 1 := by
    rw [← map_pow, primeRootValuationUnit, Units.pow_ofPowEqOne, map_one]
  apply Units.ext
  have hz : ((Units.map (IsLocalRing.residue A).toMonoidHom (primeRootValuationUnit A p hζ) :
      IsLocalRing.ResidueField A) - 1) ^ p = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hp, Units.val_one, one_pow, sub_self]
  rw [Units.val_one]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (NeZero.ne p)).mp hz)

end
end Dubon2026.SourceFunctionField
