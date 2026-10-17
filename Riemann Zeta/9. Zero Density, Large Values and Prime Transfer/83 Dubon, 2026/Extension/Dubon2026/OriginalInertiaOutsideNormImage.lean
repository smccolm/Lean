import Dubon2026.OriginalCompletionUnitNormImage
import Dubon2026.OriginalAdicInertiaNormImage

/-! # Actual inertia images come from base outside-unit classes

The normalized completion norm comparison and integral inertia
representatives now supply the global outside-unit image, with the
same global cocycle throughout. This is the ramification-control edge
of DUB-17's prescribed-support norm-field dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)
  (w : HeightOneSpectrum (𝓞 L)) [(OriginalFiniteDecompositionGroup K L w).Normal]
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
  (ψ : groupCohomology.cocycles₂ (originalIdeleClassRep K L))
  (hD : ∀ H : Subgroup Gal(L/K),
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 2))

include hT hST in
/-- Outside the chosen support, every original inertia element has
abelianization image arising from a literal base outside-unit class. -/
theorem originalInertia_image_mem_base_outside_norm_image
    (hw : w ∉ T) (hc : OriginalCompletionNormComparison K L w p hG ψ hD)
    (σ : Gal(L/K)) (hσ : σ ∈ w.asIdeal.inertia Gal(L/K)) :
    Additive.ofMul (Abelianization.of σ) ∈
      (fun c => originalInvariantAbelianMap (originalIdeleClassRep K L) ψ p hG hD
        (originalFullClassBaseInvariantEquiv K L c)) ''
        {c | ∃ z, (originalOutsideIdeleClassRepHom K K S hS).hom z = c} := by
  let D := OriginalFiniteDecompositionGroup K L w
  letI : Fintype D := Fintype.ofFinite _
  obtain ⟨φ, hC, _, hu⟩ := originalCompletionUnit_norm_image_mem_base_outside
    K L S T hS hT hST w p hG ψ hD hw hc
  let I := (w.asIdeal.inertia Gal(L/K)).comap D.subtype
  let τ : D := ⟨σ, originalInertia_fixes_prime K L w σ hσ⟩
  let ι : I := ⟨τ, hσ⟩
  have hz : Additive.ofMul (Abelianization.of τ) ∈
      Set.range (Abelianization.map I.subtype).toAdditive :=
    ⟨Additive.ofMul (Abelianization.of ι), rfl⟩
  obtain ⟨x, hx, he⟩ := originalAdicInertia_image_mem_integral_norm_image
    K L w φ p (hG.to_subgroup D) hC hz
  have hm := hu x hx
  rw [he] at hm
  exact hm

end
end Dubon2026
