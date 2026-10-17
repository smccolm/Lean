import Dubon2026.OriginalSingleUnitOutsideClass
import Dubon2026.OriginalOutsideClassRelativeTrace
import Dubon2026.OriginalNormalizedCompletionNormMap

/-! # Local integral-unit norm images come from actual base outside units

The constructed completion norm square, literal single-unit insertion and
existing outside-unit descent identify the required global image. Only
the local identification of the integral-unit image with inertia remains
at this edge of DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
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
/-- The local integral-unit image under the actual normalized norm map
comes from the actual base outside-unit class image. -/
theorem originalCompletionUnit_norm_image_mem_base_outside
    (hw : w ∉ T) (hc : OriginalCompletionNormComparison K L w p hG ψ hD) :
    letI : Fintype (OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∃ φ : groupCohomology.cocycles₂ (originalAdicUnitRep K L w),
      ∃ hC : ∀ H : Subgroup (OriginalFiniteDecompositionGroup K L w),
        Limits.IsZero (groupCohomology (Rep.res H.subtype
          (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype
          (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 2),
      addOrderOf (groupCohomology.H2π (originalAdicUnitRep K L w) φ) =
        Nat.card (OriginalFiniteDecompositionGroup K L w) ∧
      ∀ x : (originalAdicUnitRep K L w).ρ.invariants,
        x.val.toMul ∈ (w.adicCompletionIntegers L).units →
        (Abelianization.map (OriginalFiniteDecompositionGroup K L w).subtype).toAdditive
          (originalInvariantAbelianMap (originalAdicUnitRep K L w) φ p
            (hG.to_subgroup (OriginalFiniteDecompositionGroup K L w)) hC x) ∈
        (fun c => originalInvariantAbelianMap (originalIdeleClassRep K L) ψ p hG hD
          (originalFullClassBaseInvariantEquiv K L c)) ''
          {c | ∃ z, (originalOutsideIdeleClassRepHom K K S hS).hom z = c} := by
  letI : Fintype (OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨φ, hC, ho, he⟩ := hc
  refine ⟨φ, hC, ho, fun x hx => ?_⟩
  let z := (Rep.invariantsFunctor ℤ (OriginalFiniteDecompositionGroup K L w)).map
    (originalCompletionClassRepHom K L w) x
  have hz : z.val ∈ LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap :=
    originalCompletionClass_integral_mem_outside K L T hT w hw x.val.toMul hx
  let y := originalInvariantRelativeTrace (originalIdeleClassRep K L)
    (OriginalFiniteDecompositionGroup K L w) z
  let β := originalFullClassBaseInvariantEquiv K L
  refine ⟨β.symm y, originalOutsideClass_relativeTrace_base_mem K L T hT
    (OriginalFiniteDecompositionGroup K L w) S hS hST z hz, ?_⟩
  change originalInvariantAbelianMap (originalIdeleClassRep K L) ψ p hG hD (β (β.symm y)) = _
  rw [β.apply_symm_apply]
  exact he x

end
end Dubon2026
