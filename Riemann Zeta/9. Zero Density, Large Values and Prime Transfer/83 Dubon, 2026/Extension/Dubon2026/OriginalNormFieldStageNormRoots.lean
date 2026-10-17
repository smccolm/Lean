import Dubon2026.OriginalNormFieldUnramifiedPlacement
import Dubon2026.OriginalNormFieldTowerDivisibility

/-! # Actual enlarged arithmetic stages inherit invariant norm roots

The prescribed norm field is embedded into a constructed original
unramified stage above any given stage. The embedding defines the actual
field tower used by literal norm transitivity, so its norm containment
gives invariant roots in that same arithmetic stage. This assembles the
placement and coefficient-tower edge required by DUB-17; construction of
the input norm field and any primary-degree bound remain separate.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module

/-- Invariant roots for every actual outside-unit quotient with the
literal inverse-image support. This proposition alone asserts no proof. -/
def OriginalOutsideQuotientInvariantNormRoots
    (E M : Type) [Field E] [Field M] [NumberField M]
    [Algebra E M] [FiniteDimensional E M]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (n : ℕ) : Prop :=
  ∀ (T : Finset (HeightOneSpectrum (𝓞 M)))
    (hT : ∀ (σ : Gal(M/E)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv E M σ v ∈ T)
    (_hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E M w ∈ S)
    (x : originalIdeleClassesModOutsideRep E M T hT),
    ∃ d : originalIdeleClassesModOutsideRep E M T hT,
      (∀ g, (originalIdeleClassesModOutsideRep E M T hT).ρ g d = d) ∧
      (∑ g : Gal(M/E), (originalIdeleClassesModOutsideRep E M T hT).ρ g x) = n • d

/-- The actual norm tower proves the full original quotient-root
statement from the narrower intermediate norm containment. -/
theorem originalOutsideQuotientInvariantNormRoots_of_tower
    (E L M : Type) [Field E] [NumberField E] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra E L] [Algebra L M] [Algebra E M]
    [IsScalarTower E L M] [FiniteDimensional E L] [FiniteDimensional L M]
    [FiniteDimensional E M] [IsGalois E L] [IsGalois L M] [IsGalois E M]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ (σ : Gal(E/E)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv E E σ v ∈ S) (n : ℕ)
    (hNorm : (originalIdeleClassNormLinear E L).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep E E →ₗ[ℤ] originalIdeleClassRep E E)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom E E S hS).hom.toLinearMap) :
    OriginalOutsideQuotientInvariantNormRoots E M S n := by
  intro T hT hST x
  exact originalClassesModOutside_invariant_norm_divisibility_tower E L M S T hS hT hST n hNorm x

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
  (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
  (L : Type) [Field L] [NumberField L] [Algebra E L] [FiniteDimensional E L] [IsGalois E L]
  (S : Finset (HeightOneSpectrum (𝓞 E)))
  (hS : ∀ (σ : Gal(E/E)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv E E σ v ∈ S)

include ha hE in
/-- The actual norm field and its relative ramification construct an
original stage above any prescribed stage with invariant roots of all
literal quotient norms. No arbitrary coefficient or transition is used. -/
theorem originalNormField_exists_stage_invariant_norm_roots
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a) (n : ℕ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 E) (𝓞 L) (algebraMap (𝓞 K) (𝓞 E) a) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 E)).ramificationIdx w.asIdeal = 1)
    (hNorm : (originalIdeleClassNormLinear E L).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep E E →ₗ[ℤ] originalIdeleClassRep E E)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom E E S hS).hom.toLinearMap) :
    ∃ (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
      (hEN : E ≤ N.val.toIntermediateField),
      P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
      letI : Algebra E N.val := (IntermediateField.inclusion hEN).toAlgebra
      letI : IsScalarTower K E N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
      letI : FiniteDimensional E N.val := FiniteDimensional.right K E N.val
      OriginalOutsideQuotientInvariantNormRoots E N.val S n := by
  obtain ⟨N, hEN, hPN, i, hi⟩ :=
    originalNormField_exists_unramified_stage_above K Ω a ha E hE L P hUnram
  refine ⟨N, hEN, hPN, ?_⟩
  letI : Algebra E N.val := (IntermediateField.inclusion hEN).toAlgebra
  letI : IsScalarTower K E N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
  letI : FiniteDimensional E N.val := FiniteDimensional.right K E N.val
  letI : IsGalois E N.val := IsGalois.tower_top_of_isGalois K E N.val
  let j : L →ₐ[E] N.val := {
    toFun := fun x => ⟨i x, hi x⟩
    map_one' := Subtype.ext i.map_one
    map_mul' := fun x y => Subtype.ext (i.map_mul x y)
    map_zero' := Subtype.ext i.map_zero
    map_add' := fun x y => Subtype.ext (i.map_add x y)
    commutes' := fun x => Subtype.ext (i.commutes x) }
  letI : Algebra L N.val := j.toRingHom.toAlgebra
  letI : IsScalarTower E L N.val := IsScalarTower.of_algHom j
  letI : FiniteDimensional L N.val := FiniteDimensional.right E L N.val
  letI : IsGalois L N.val := IsGalois.tower_top_of_isGalois E L N.val
  exact originalOutsideQuotientInvariantNormRoots_of_tower E L N.val S hS n hNorm

end
end Dubon2026
