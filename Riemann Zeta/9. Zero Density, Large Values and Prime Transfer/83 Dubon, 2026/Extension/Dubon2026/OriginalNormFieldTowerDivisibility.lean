import Dubon2026.OriginalIdeleNormTower
import Dubon2026.OriginalClassQuotientInvariantNormDivisibility

/-! # Invariant norm roots persist above an actual norm field

The literal field-norm tower makes every upper norm a norm from the
constructed intermediate field. The existing original quotient theorem
then gives invariant roots in any such enlargement. This is the tower
transport needed between DUB-17's prescribed norm field and its actual
arithmetic enlarged-stage norm-divisibility obligation.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois E L] [IsGalois K L]

/-- Every literal upper class norm is a literal intermediate class norm. -/
theorem originalIdeleClassNorm_range_le_tower :
    (originalIdeleClassNormLinear K L).range ≤ (originalIdeleClassNormLinear K E).range := by
  rintro c ⟨b, rfl⟩
  exact ⟨originalIdeleClassNormLinear E L b,
    congrArg Additive.ofMul (originalIdeleClassNorm_tower K E L b.toMul)⟩

/-- A proved intermediate norm-field containment constructs invariant
roots of all literal upper-stage quotient norms through the actual tower. -/
theorem originalClassesModOutside_invariant_norm_divisibility_tower
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
    (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S) (n : ℕ)
    (hnorm : (originalIdeleClassNormLinear K E).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap)
    (x : originalIdeleClassesModOutsideRep K L T hT) :
    ∃ d : originalIdeleClassesModOutsideRep K L T hT,
      (∀ g, (originalIdeleClassesModOutsideRep K L T hT).ρ g d = d) ∧
      (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L T hT).ρ g x) = n • d :=
  originalClassesModOutside_invariant_norm_divisibility K L S T hS hT hST n
    ((originalIdeleClassNorm_range_le_tower K E L).trans hnorm) x

end
end Dubon2026
