import Dubon2026.OriginalClassesModOutsideBaseChange
import Dubon2026.OriginalIdeleRootCorrection

/-! # Literal source-class representatives after an original root correction

The proved supported-idele correction gives an original S-place class and
retains the full-class base-change value modulo outside units. This is the
map compatibility needed by the actual q-torsion arithmetic stage lifting.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E L w ∈ S)

/-- An original principal root correction supplies an actual source class with precisely the original full-class transition image. -/
theorem originalSourceClass_exists_of_root_correction
    (q : ℕ) (hq : 0 < q) (x : (AdeleRing (𝓞 E) E)ˣ) (u : Eˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S →
      v.valuation E (u : E) = Valued.v (numberFieldIdeleFiniteComponent E v x).val ^ q)
    (β : Lˣ) (hβ : (β : L) ^ q = algebraMap E L (u : E)) :
    ∃ z : originalSPlaceIdeleClassRep K L T hT,
      (originalSPlaceClassComparison K L T hT).hom z =
        (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST).hom
          ((originalIdeleClassesModOutsideRepHom K E S hS).hom
            (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele E).range x))) := by
  let t : numberFieldSupportedIdeles L T :=
    ⟨originalIdeleBaseChangeMap E L x / numberFieldPrincipalIdele L β,
      originalIdele_rootCorrection_mem_supported E L S T hST q hq x u hu β hβ⟩
  let s : supportedUnrestrictedUnitRep K L T hT :=
    (originalSupportedUnrestrictedProjection K L T hT).hom (Additive.ofMul t)
  refine ⟨(originalSPlaceIdeleClassRepHom K L T hT).hom s, ?_⟩
  have he := originalSPlaceClassComparison_of_supported K L T hT (Additive.ofMul t)
  refine he.trans ?_
  change (originalIdeleClassesModOutsideRepHom K L T hT).hom
    (Additive.ofMul (QuotientGroup.mk' (numberFieldPrincipalIdele L).range t.val)) =
      (originalIdeleClassesModOutsideRepHom K L T hT).hom
        (Additive.ofMul (originalIdeleClassBaseChangeMap E L
          (QuotientGroup.mk' (numberFieldPrincipalIdele E).range x)))
  rw [originalIdeleClassBaseChangeMap_mk]
  apply congrArg ((originalIdeleClassesModOutsideRepHom K L T hT).hom ∘ Additive.ofMul)
  change QuotientGroup.mk' (numberFieldPrincipalIdele L).range
    (originalIdeleBaseChangeMap E L x / numberFieldPrincipalIdele L β) = _
  rw [map_div]
  have hp : QuotientGroup.mk' (numberFieldPrincipalIdele L).range
      (numberFieldPrincipalIdele L β) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨β, rfl⟩
  rw [hp, div_one]

end
end Dubon2026
