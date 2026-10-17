import Dubon2026.OriginalClassQuotientBaseInvariants
import Dubon2026.OriginalIdeleClassNorm
import Dubon2026.OriginalIdeleClassInvariantNormQuotient
import Dubon2026.OriginalCoinducedInvariantNorms

/-! # The actual class norm in the original outside-unit quotient

The descended idele-class norm becomes the literal sum of Galois
conjugates after base change and projection. This comparison is needed
to apply the norm-field construction to invariant norm divisibility in
DUB-17's finite relation-extension and global-duality chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)

/-- The actual descended norm and base change give the literal original quotient norm. -/
theorem originalClassesModOutside_norm_comparison
    (c : OriginalNumberFieldIdeleClassGroup L) :
    (originalIdeleClassesModOutsideRepHom K L T hT).hom
      (Additive.ofMul (originalIdeleClassBaseChangeMap K L (originalIdeleClassNorm K L c))) =
        (originalIdeleClassesModOutsideRep K L T hT).ρ.norm
          ((originalIdeleClassesModOutsideRepHom K L T hT).hom (Additive.ofMul c)) := by
  have hn : Additive.ofMul (originalIdeleClassBaseChangeMap K L
      (originalIdeleClassNorm K L c)) =
      (originalIdeleClassRep K L).ρ.norm (Additive.ofMul c) := by
    apply Additive.toMul.injective
    exact (originalIdeleClassBaseChangeMap_norm K L c).trans
      (originalIdeleClass_representation_norm K L c).symm
  exact (congrArg (originalIdeleClassesModOutsideRepHom K L T hT).hom hn).trans
    (originalCoefficientMorphism_norm (originalIdeleClassesModOutsideRepHom K L T hT) _)

end
end Dubon2026
