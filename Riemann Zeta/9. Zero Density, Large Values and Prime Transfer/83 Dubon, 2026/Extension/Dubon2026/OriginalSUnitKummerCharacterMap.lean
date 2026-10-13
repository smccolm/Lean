import Dubon2026.OriginalKummerPerfectRestriction
import Dubon2026.NumberFieldSUnitKummerFinite

/-! # Original S-units surject onto the Kummer kernel characters

The existing original S-unit power-quotient equivalence supplies every
original radical class. The proved restricted Kummer pairing therefore
gives every character of the actual restriction subgroup. Its value on
any actual root is the literal automorphism/root ratio. This supplies
the surjective comparison map for DUB-17's selected local-unit image
calculation, without assuming a numerical kernel or image size.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- The original S-unit maps to its actual class in the original field
power quotient, through the existing quotient equivalence. -/
def originalSUnitKummerClassMap (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) :
    (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      originalKummerClassSubgroup n ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔
        (powMonoidHom (α := Kˣ) n).range) :=
  (numberFieldSUnitPowerQuotientEquivClasses K S n hn).toMonoidHom.comp
    (QuotientGroup.mk' _)

/-- The constructed class is literally the field power class of the
original S-unit. -/
theorem originalSUnitKummerClassMap_val (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (originalSUnitKummerClassMap K S n hn x).val =
      QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x.val := rfl

/-- The actual S-unit class map is surjective onto all the original
classes defining the full S-unit Kummer field. -/
theorem originalSUnitKummerClassMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) : Function.Surjective (originalSUnitKummerClassMap K S n hn) :=
  (numberFieldSUnitPowerQuotientEquivClasses K S n hn).surjective.comp
    (QuotientGroup.mk'_surjective _)

variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]

/-- The actual original S-unit ratio-character map on a subgroup of the
actual full S-unit Kummer Galois group. -/
def originalSUnitKummerCharacterMap (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)/K)) :
    (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      (H →* (originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range))ˣ) :=
  ((MonoidHom.restrictHom H _).comp (originalKummerClassPairing n hn hζ _)).comp
    (originalSUnitKummerClassMap K S n hn.ne')

/-- Every actual character on the original Kummer subgroup comes from
an original S-unit. -/
theorem originalSUnitKummerCharacterMap_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)/K)) :
    Function.Surjective (originalSUnitKummerCharacterMap K Ω S n hn hζ H) := by
  letI := numberField_sUnit_kummerClasses_finite K S S.finite_toSet n hn.ne'
  exact (originalKummerClassPairing_restrict_surjective (Ω := Ω) n hn hζ _ H).comp
    (originalSUnitKummerClassMap_surjective K S n hn.ne')

omit [IsGalois K Ω] in
/-- The actual character is the automorphism/root ratio of any original
root of the same original S-unit equation. -/
theorem originalSUnitKummerCharacterMap_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (H : Subgroup Gal(originalKummerRadicalField (Ω := Ω) n
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)/K))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (β : (originalKummerRadicalField (Ω := Ω) n
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range))ˣ)
    (hβ : β ^ n = Units.map (algebraMap K _).toMonoidHom x.val) (σ : H) :
    originalSUnitKummerCharacterMap K Ω S n hn hζ H x σ = σ.val • β / β := by
  letI : NeZero n := ⟨hn.ne'⟩
  let Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range
  let c := originalSUnitKummerClassMap K S n hn.ne' x
  change σ.val • originalKummerClassRoot n hn Δ c / originalKummerClassRoot n hn Δ c = _
  apply galois_radical_ratios_eq_of_power_class n hζ
    (originalKummerClassRepresentative n Δ c).val x.val _ β
    (originalKummerClassRoot_pow n hn Δ c) hβ _ σ.val
  rw [originalKummerClassRepresentative_spec]
  exact originalSUnitKummerClassMap_val K S n hn.ne' x

end
end Dubon2026
