import Dubon2026.OriginalIndexedRelationPrimeSupport
import Dubon2026.OriginalPrimeInvariantSupportFromRealization

/-! The actual indexed relation has a finite normalized invariant sum.
Its support is proved from the constructed relation coordinates, using a
proved prime realization. This is the finite-sum step in DUB-17's canonical
rational Cartier total, before the actual arithmetic total is substituted. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] indexedPrimeRelationCosets

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) t, t ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ t ∈ S)
  (I : Type) [Fintype I] (v : I → HeightOneSpectrum (𝓞 K)) (w : I → S)
  (B : Rep.{0} ℤ Gal(L/K))
  (J : HeightOneSpectrum (𝓞 K) → groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))

/-- Actual coordinate support reduces the full normalized prime sum to
the given distinct prime index; no invariant-support assumption is made. -/
theorem originalIndexedRelation_invariants_finsum_eq_sum
    (hJ : OriginalPrimeInvariantRealization K L J)
    (hv : Function.Injective v)
    (hw : ∀ i : I, originalFinitePrimeBelow K L (w i).val = v i)
    (φ : ∀ i : I,
      Rep.res (OriginalFiniteDecompositionGroup K L (w i).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w i).val)
    (y : groupCohomology B 1) :
    let u := (groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
      (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
        (originalIndexedPrimeSPlaceRelation K L S hS I w B φ) y)
    ∑ᶠ t, J t u = ∑ i : I, J (v i) u := by
  intro u
  let T := Finset.univ.image v
  have hs : Function.support (fun t => J t u) ⊆ T := by
    intro t ht
    by_contra htT
    apply ht
    apply originalPrimeInvariant_zero_of_fibre K L J hJ t u
    intro z hz
    apply originalIndexedPrimeSPlaceRelation_adic_zero K L S hS I w B φ z _ y
    intro i hi
    apply htT
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hz, hw] at hi
    exact hi.symm
  calc
    ∑ᶠ t, J t u = ∑ t ∈ T, J t u := finsum_eq_sum_of_support_subset _ hs
    _ = ∑ i : I, J (v i) u := Finset.sum_image (fun _ _ _ _ hij => hv hij)

end
end Dubon2026
