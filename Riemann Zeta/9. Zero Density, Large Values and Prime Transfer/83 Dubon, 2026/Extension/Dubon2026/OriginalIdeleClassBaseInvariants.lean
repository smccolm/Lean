import Dubon2026.OriginalIdeleClassNorm
import Dubon2026.OriginalIdeleClassNormQuotientTorsion

/-! # Actual base classes and original generator-fixed class coefficients

The actual class inclusion identifies the original base classes with the
original cyclic invariant coefficient module. The norm comparison retains
the actual descended class norm. These discharge the coefficient-model
comparison in DUB-17's native class norm-index lower-bound chain.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

/-- The actual original class norm as an integer-linear map on the original additive tags. -/
def originalIdeleClassNormLinear :
    Additive (OriginalNumberFieldIdeleClassGroup L) →ₗ[ℤ] Additive (OriginalNumberFieldIdeleClassGroup K) :=
  (originalIdeleClassNorm K L).toAdditive.toIntLinearMap

/-- Actual base classes map to the original generator-fixed coefficient module. -/
def originalIdeleClassBaseInvariant (g : Gal(L/K)) :
    Additive (OriginalNumberFieldIdeleClassGroup K) →ₗ[ℤ]
      LinearMap.ker (Rep.applyAsHom (originalIdeleClassRep K L) g -
        𝟙 (originalIdeleClassRep K L)).hom.toLinearMap := by
  let φ : Additive (OriginalNumberFieldIdeleClassGroup K) →ₗ[ℤ] originalIdeleClassRep K L :=
    (originalIdeleClassBaseChangeMap K L).toAdditive.toIntLinearMap
  refine φ.codRestrict _ (fun c => ?_)
  change (originalIdeleClassRep K L).ρ g (φ c) - φ c = 0
  apply sub_eq_zero.mpr
  exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_fixed K L g c.toMul)

/-- Original class descent identifies actual base classes with all original generator-fixed coefficients. -/
def originalIdeleClassBaseInvariantEquiv (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Additive (OriginalNumberFieldIdeleClassGroup K) ≃ₗ[ℤ]
      LinearMap.ker (Rep.applyAsHom (originalIdeleClassRep K L) g -
        𝟙 (originalIdeleClassRep K L)).hom.toLinearMap := by
  apply LinearEquiv.ofBijective (originalIdeleClassBaseInvariant K L g)
  constructor
  · intro c d h
    apply Additive.toMul.injective
    apply originalIdeleClassBaseChangeMap_injective K L
    have hh := congrArg (fun z => Additive.toMul z.val) h
    exact hh
  · intro x
    have hx : x.val ∈ (originalIdeleClassRep K L).ρ.invariants := by
      apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
        (originalIdeleClassRep K L).ρ g hg x.val).mpr
      have he := x.property
      change (originalIdeleClassRep K L).ρ g x.val - x.val = 0 at he
      exact sub_eq_zero.mp he
    obtain ⟨c, hc⟩ := originalIdeleClassBaseChangeMap_surjective_fixed K L x.val.toMul
      (fun σ => congrArg Additive.toMul (hx σ))
    refine ⟨Additive.ofMul c, Subtype.ext ?_⟩
    exact congrArg Additive.ofMul hc

/-- The actual original class norm becomes the original representation norm after the actual class inclusion. -/
theorem originalIdeleClassBaseInvariant_norm (g : Gal(L/K))
    (x : Additive (OriginalNumberFieldIdeleClassGroup L)) :
    (originalIdeleClassBaseInvariant K L g (originalIdeleClassNormLinear K L x)).val =
      (originalIdeleClassRep K L).norm.hom x := by
  apply Additive.toMul.injective
  exact (originalIdeleClassBaseChangeMap_norm K L x.toMul).trans
    (originalIdeleClass_representation_norm K L x.toMul).symm

end
end Dubon2026
