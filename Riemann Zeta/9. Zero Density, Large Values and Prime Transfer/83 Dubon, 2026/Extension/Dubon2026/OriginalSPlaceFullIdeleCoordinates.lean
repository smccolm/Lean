import Dubon2026.OriginalSPlaceFullClassImage
import Dubon2026.OriginalIdeleAdicH2

/-! Literal finite coordinates of the original S-place inclusion.
These identify the actual full-idele class used by DUB-17's total-zero
criterion with the original local relation values. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Inclusion retains each original completion-unit coordinate inside S. -/
theorem originalSPlaceFullIdeleInclusion_finite
    (x : supportedUnrestrictedUnitRep K L S hS) (v : S) :
    (originalFullIdeleAdicRepHom K L v.val).hom ((originalSPlaceFullIdeleInclusion K L S hS).hom x) =
      x (Sum.inr v) := by
  change (supportedIdeleLocalFactorLinearEquiv L S
    ((supportedIdeleLocalFactorLinearEquiv L S).symm (x, 0))).1 (Sum.inr v) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The full-idele image has zero additive unit coordinate outside the
original finite support, exactly as in the source S-place coefficient. -/
theorem originalSPlaceFullIdeleInclusion_outside
    (x : supportedUnrestrictedUnitRep K L S hS)
    (v : HeightOneSpectrum (𝓞 L)) (hv : v ∉ S) :
    (originalFullIdeleAdicRepHom K L v).hom ((originalSPlaceFullIdeleInclusion K L S hS).hom x) = 0 := by
  have he := congrArg (fun z => z.2 ⟨v, hv⟩)
    ((supportedIdeleLocalFactorLinearEquiv L S).apply_symm_apply (x, 0))
  apply Additive.toMul.injective
  apply Units.ext
  exact congrArg (fun z : Additive (v.adicCompletionIntegers L)ˣ => (z.toMul.val : v.adicCompletion L)) he

end
end Dubon2026
