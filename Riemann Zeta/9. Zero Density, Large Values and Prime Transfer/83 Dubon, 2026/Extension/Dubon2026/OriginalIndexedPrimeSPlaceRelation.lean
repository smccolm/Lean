import Dubon2026.OriginalSinglePrimeSPlaceRelation
import Dubon2026.OriginalFinitePrimeOrbits

/-! Assemble the original local relations on their actual finite index.
For DUB-17 the index is the original exceptional rational primes, so each
completion and Cartier cocycle keeps its literal prime parameter. This
reuses the native single-prime coinduction map and avoids transporting
the dependent completion fields through an image-finset equivalence. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (I : Type) [Fintype I] (w : I → S) (B : Rep.{0} ℤ Gal(L/K))

/-- The original finite Galois group gives the decomposition cosets used by coinduction. -/
local instance indexedPrimeRelationCosets (u : HeightOneSpectrum (𝓞 L)) :
    Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L u) := Fintype.ofFinite _

/-- Sum the existing original single-prime maps on the actual finite local index. -/
def originalIndexedPrimeSPlaceRelation
    (φ : ∀ i : I,
      Rep.res (OriginalFiniteDecompositionGroup K L (w i).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w i).val) :
    originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS := by
  let f (i : I) : originalRelationModule B →ₗ[ℤ] supportedUnrestrictedUnitRep K L S hS :=
    (originalSinglePrimeSPlaceRelation K L S hS (w i).val B (φ i)).hom.toLinearMap
  refine Rep.ofHom ⟨∑ i : I, f i, ?_⟩
  intro σ
  apply LinearMap.ext
  intro x
  change (∑ i : I, f i) ((originalRelationModule B).ρ σ x) =
    (supportedUnrestrictedUnitRep K L S hS).ρ σ ((∑ i : I, f i) x)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    Rep.hom_comm_apply (originalSinglePrimeSPlaceRelation K L S hS (w i).val B (φ i)) σ x)

omit [NumberField K] in
/-- Distinct original contractions ensure that the actual finite sum
recovers each local relation, using the native single-prime evaluation. -/
theorem originalIndexedPrimeSPlaceRelation_evaluation
    (hw : Function.Injective (fun i : I => originalFinitePrimeBelow K L (w i).val))
    (φ : ∀ i : I,
      Rep.res (OriginalFiniteDecompositionGroup K L (w i).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w i).val)
    (i : I) (x : originalRelationModule B) :
    (originalIndexedPrimeSPlaceRelation K L S hS I w B φ).hom x (Sum.inr (w i)) = (φ i).hom x := by
  let f (j : I) : originalRelationModule B →ₗ[ℤ] supportedUnrestrictedUnitRep K L S hS :=
    (originalSinglePrimeSPlaceRelation K L S hS (w j).val B (φ j)).hom.toLinearMap
  have he : (originalIndexedPrimeSPlaceRelation K L S hS I w B φ).hom x (Sum.inr (w i)) =
      ∑ j : I, ((originalSinglePrimeSPlaceRelation K L S hS (w j).val B (φ j)).hom x (Sum.inr (w i))) := by
    change (LinearMap.proj (R := ℤ) (Sum.inr (w i))) ((∑ j : I, f j) x) = _
    rw [LinearMap.sum_apply]
    exact map_sum (LinearMap.proj (R := ℤ) (Sum.inr (w i))) (fun j : I => f j x) Finset.univ
  rw [he, Finset.sum_eq_single i]
  · exact originalSinglePrimeSPlaceRelation_evaluation K L S hS (w i).val B (w i).property (φ i) x
  · intro j _ hji
    apply originalSinglePrimeSPlaceRelation_outside_orbit K L S hS (w j).val B (w i)
    intro σ hσ
    apply hji
    apply hw
    have h := congrArg (originalFinitePrimeBelow K L) hσ
    rw [originalFinitePrimeBelow_galois] at h
    exact h
  · intro h
    exact (h (Finset.mem_univ _)).elim

end
end Dubon2026
