import Dubon2026.ArithmeticSUnitDivisibility
import Dubon2026.ArithmeticExceptionalSUnitSupport

/-! # Actual S-unit coefficients in a prescribed finite subfield

When the value of an original arithmetic S-unit lies in a given finite
Galois field, integrality of that value and its inverse descends to the
same field. This retains the finite field selected by cocycle periods.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

private theorem localizedUnit_preimage (K L Γ : Type) [Field K] [Field L] [Field Γ]
    [NumberField K] [NumberField L] [Algebra K L] [Algebra K Γ]
    (a : 𝓞 K) (ha : a ≠ 0) (j : L →ₐ[K] Γ)
    (u : (integralClosure (originalLocalizedIntegers K a ha) Γ)ˣ)
    (b : L) (hb : j b = u.val.val) :
    ∃ v : (originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
      (originalIntegerMap_ne_zero (L := L) a ha))ˣ, j v.val.val = u.val.val := by
  let R := originalLocalizedIntegers K a ha
  let jR : L →ₐ[R] Γ := { j.toRingHom with commutes' := fun r => j.commutes r.val }
  obtain ⟨v, hv⟩ := originalIntegralUnit_preimage jR u b hb
  let aL := algebraMap (𝓞 K) (𝓞 L) a
  have haL : aL ≠ 0 := originalIntegerMap_ne_zero (L := L) a ha
  let S := originalLocalizedIntegers L aL haL
  letI : Algebra R S := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure S R L := (canonicalLocalizedIntegerAlgebra_data (L := L) a ha).2.1
  let e := IsIntegralClosure.equiv R (integralClosure R L) L S
  let w : Sˣ := Units.map e.toMonoidHom v
  have hw : w.val.val = b :=
    (IsIntegralClosure.algebraMap_equiv R (integralClosure R L) L S v.val).trans hv
  exact ⟨w, (congrArg j hw).trans hb⟩

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

local instance : NumberField F := NumberField.of_module_finite K F

/-- An arithmetic S-unit whose value belongs to the prescribed finite Galois field is a unit of that field's original localized ring. -/
theorem originalArithmeticSUnit_localizedPreimage_at_finiteField
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ)
    (hu : u.val.val ∈ F.toIntermediateField) :
    ∃ v : (originalLocalizedIntegers F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha))ˣ,
      algebraMap F (originalUnramifiedGaloisUnion (Ω := Ω) a) v.val.val = u.val.val := by
  exact localizedUnit_preimage K F (originalUnramifiedGaloisUnion (Ω := Ω) a)
    a ha F.toIntermediateField.val u ⟨u.val.val, hu⟩ rfl

/-- The same original unit descends to the prescribed finite field's source S-unit coefficient with the exact original value. -/
theorem originalArithmeticSUnit_supportedPreimage_at_finiteField
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ)
    (hu : u.val.val ∈ F.toIntermediateField) :
    ∃ v : (↑(originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F,
      algebraMap F (originalUnramifiedGaloisUnion (Ω := Ω) a) v.val.val = u.val.val := by
  obtain ⟨v, hv⟩ := originalArithmeticSUnit_localizedPreimage_at_finiteField K Ω a ha F u hu
  refine ⟨originalLocalizedUnitsEquivSupportedSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha) v, ?_⟩
  exact (congrArg (algebraMap F (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (originalLocalizedUnitsEquivSupportedSUnits_coe F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) v)).trans hv

end
end Dubon2026
