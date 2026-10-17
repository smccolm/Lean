import Dubon2026.OriginalOutsideClassNormDescent
import Dubon2026.OriginalIdeleNormTower

/-! # Norm-field containment descends to the original base

The norm sends powers to powers and outside-unit classes to outside-unit
classes. Combined with the proved field-norm tower, this transfers the
norm-field containment needed by DUB-17 to the original base field.
In particular an isomorphic arithmetic realization does not require a
transport of the whole normalized class system or its cohomology.
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

/-- A norm-field containment over an intermediate base descends through
the actual norm tower, with its literal inverse-image support. -/
theorem originalNormField_containment_descends_base
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hT : ∀ (σ : Gal(E/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ T)
    (hTE : ∀ (σ : Gal(E/E)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv E E σ v ∈ T)
    (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K E w ∈ S) (n : ℕ)
    (hNorm : (originalIdeleClassNormLinear E L).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep E E →ₗ[ℤ] originalIdeleClassRep E E)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom E E T hTE).hom.toLinearMap) :
    (originalIdeleClassNormLinear K L).range ≤
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  rintro c ⟨x, rfl⟩
  have hx := hNorm (show originalIdeleClassNormLinear E L x ∈
    (originalIdeleClassNormLinear E L).range from ⟨x, rfl⟩)
  obtain ⟨y, ⟨z, rfl⟩, u, hu, he⟩ :=
    (Submodule.mem_sup (M := originalIdeleClassRep E E)).mp hx
  have hn := congrArg Additive.ofMul (originalIdeleClassNorm_tower K E L x.toMul)
  change originalIdeleClassNormLinear K E (originalIdeleClassNormLinear E L x) =
    originalIdeleClassNormLinear K L x at hn
  rw [← hn, ← he]
  let zm : OriginalNumberFieldIdeleClassGroup E := z.toMul
  let um : OriginalNumberFieldIdeleClassGroup E := u.toMul
  change Additive.ofMul (originalIdeleClassNorm K E (zm ^ n * um)) ∈ _
  rw [map_mul, map_pow]
  apply Submodule.add_mem_sup (M := originalIdeleClassRep K K)
  · refine ⟨originalIdeleClassNormLinear K E z, ?_⟩
    rfl
  · exact originalOutsideClass_norm_mem K E S T hS hT hST u hu

end
end Dubon2026
