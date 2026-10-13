import Dubon2026.OriginalKummerDegree

/-! # Surjectivity of the original Kummer pairing and its restriction

The existing nondegenerate original pairing and proved Kummer degree have
equal finite cardinalities. Pinned finite-character duality therefore makes
that actual pairing bijective and its restriction to the actual kernel
surjective. This gives the image-cardinality route for the selected S-unit
local-power map in DUB-17, without a new classification of finite radicals.
-/
namespace Dubon2026
noncomputable section
open scoped IsMulCommutative
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]

/-- The already constructed original radical pairing is bijective for an
actual finite original power-class subgroup. -/
theorem originalKummerClassPairing_bijective
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Function.Bijective (originalKummerClassPairing (Ω := Ω) n hn hζ Δ) := by
  let E := originalKummerRadicalField (Ω := Ω) n Δ
  let G := Gal(E/K)
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
  apply (originalKummerClassPairing_injective (Ω := Ω) n hn hζ Δ).bijective_of_nat_card_le
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G E]
  exact (originalKummerRadicalField_galois_card (Ω := Ω) n hn hζ Δ).le

/-- Every character on the actual Kummer restriction subgroup is the
restriction of the ratio character of an original power class. -/
theorem originalKummerClassPairing_restrict_surjective
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)]
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) :
    Function.Surjective ((MonoidHom.restrictHom H
      (originalKummerRadicalField (Ω := Ω) n Δ)ˣ).comp
        (originalKummerClassPairing (Ω := Ω) n hn hζ Δ)) := by
  let E := originalKummerRadicalField (Ω := Ω) n Δ
  let G := Gal(E/K)
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
  exact (MonoidHom.restrict_surjective (M := E) H).comp
    (originalKummerClassPairing_bijective (Ω := Ω) n hn hζ Δ).2

end
end Dubon2026
