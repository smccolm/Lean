import Dubon2026.OriginalKummerPairingNondegenerate
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! # The degree of the actual finite original Kummer extension

Both injections come from the actual radical pairing. Pinned finite
abelian duality, applied in each direction, gives equality of cardinalities
and hence the actual field degree. No perfect-pairing or degree hypothesis
is assumed. This is the Kummer degree input to DUB-17's global norm index.
-/

namespace Dubon2026
noncomputable section
open scoped IsMulCommutative
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- Every actual original power class is killed by the original exponent. -/
theorem originalKummerClassSubgroup_pow_eq_one (n : ℕ) (Δ : Subgroup Kˣ)
    (c : originalKummerClassSubgroup n Δ) : c ^ n = 1 := by
  apply Subtype.ext
  change c.val ^ n = 1
  induction c.val using QuotientGroup.induction_on with
  | H a =>
    change (QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range a) ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

/-- The actual original radical Galois group has exactly as many elements as the original power classes. -/
theorem originalKummerRadicalField_galois_card [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Nat.card Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) =
      Nat.card (originalKummerClassSubgroup n Δ) := by
  let E := originalKummerRadicalField (Ω := Ω) n Δ
  let G := Gal(E/K)
  let C := originalKummerClassSubgroup n Δ
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Finite G := originalKummerRadicalField_galois_finite n hn hζ Δ
  letI : IsMulCommutative G := originalKummerRadicalField_galois_commutative n hζ Δ
  letI : CommGroup G := inferInstance
  letI : HasEnoughRootsOfUnity E n := {
    prim := ⟨algebraMap K E hζ.choose,
      (isPrimitiveRoot_of_mem_primitiveRoots hζ.choose_spec).map_of_injective
        (algebraMap K E).injective⟩
    cyc := rootsOfUnity.isCyclic E n }
  letI : HasEnoughRootsOfUnity E (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd E (Monoid.exponent_dvd_of_forall_pow_eq_one
      (originalKummerRadicalField_galois_pow_eq_one n hζ Δ))
  letI : HasEnoughRootsOfUnity E (Monoid.exponent C) :=
    HasEnoughRootsOfUnity.of_dvd E (Monoid.exponent_dvd_of_forall_pow_eq_one
      (originalKummerClassSubgroup_pow_eq_one n Δ))
  apply Nat.le_antisymm
  · calc
      Nat.card G ≤ Nat.card (C →* Eˣ) :=
        Nat.card_le_card_of_injective _ (originalKummerTranspose_injective n hn hζ Δ)
      _ = Nat.card C := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity C E
  · calc
      Nat.card C ≤ Nat.card (G →* Eˣ) :=
        Nat.card_le_card_of_injective _ (originalKummerClassPairing_injective n hn hζ Δ)
      _ = Nat.card G := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G E

/-- The degree of the constructed original Kummer field is the original power-class cardinality. -/
theorem originalKummerRadicalField_finrank [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Module.finrank K (originalKummerRadicalField (Ω := Ω) n Δ) =
      Nat.card (originalKummerClassSubgroup n Δ) := by
  letI := originalKummerRadicalField_isGalois (Ω := Ω) n Δ
  letI := originalKummerRadicalField_finiteDimensional (Ω := Ω) n hn hζ Δ
  rw [← IsGalois.card_aut_eq_finrank]
  exact originalKummerRadicalField_galois_card n hn hζ Δ

end
end Dubon2026
