import Dubon2026.OriginalSinglePrimeSPlaceRelation
import Dubon2026.OriginalFinitePrimeOrbits

/-! Assemble finitely many original local relation morphisms, one at a
chosen completion over each specified base prime. Distinct contractions
give disjoint Galois orbits, so the native single-prime construction recovers
the entire given family. This is the finite S-place realization needed for
DUB-17's canonical local-pairing sum and reverse localization. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 K))) (w : T → S)
  (B : Rep.{0} ℤ Gal(L/K))

/-- The original finite Galois group gives finite decomposition cosets. -/
local instance finitePrimeRelationCosets (u : HeightOneSpectrum (𝓞 L)) :
    Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L u) := Fintype.ofFinite _

/-- Sum the original single-prime relation maps in the actual S-place coefficient. -/
def originalFinitePrimeSPlaceRelation
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w v).val) :
    originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS := by
  let f (v : T) : originalRelationModule B →ₗ[ℤ] supportedUnrestrictedUnitRep K L S hS :=
    (originalSinglePrimeSPlaceRelation K L S hS (w v).val B (φ v)).hom.toLinearMap
  refine Rep.ofHom ⟨∑ v : T, f v, ?_⟩
  intro σ
  apply LinearMap.ext
  intro x
  change (∑ v : T, f v) ((originalRelationModule B).ρ σ x) =
    (supportedUnrestrictedUnitRep K L S hS).ρ σ ((∑ v : T, f v) x)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact Rep.hom_comm_apply (originalSinglePrimeSPlaceRelation K L S hS (w v).val B (φ v)) σ x

omit [NumberField K] in
/-- The assembled original S-place relation recovers every specified local
relation value. Orbit separation is derived from the actual prime below. -/
theorem originalFinitePrimeSPlaceRelation_evaluation
    (hw : ∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w v).val)
    (v : T) (x : originalRelationModule B) :
    (originalFinitePrimeSPlaceRelation K L S hS T w B φ).hom x (Sum.inr (w v)) = (φ v).hom x := by
  let f (u : T) : originalRelationModule B →ₗ[ℤ] supportedUnrestrictedUnitRep K L S hS :=
    (originalSinglePrimeSPlaceRelation K L S hS (w u).val B (φ u)).hom.toLinearMap
  have he : (originalFinitePrimeSPlaceRelation K L S hS T w B φ).hom x (Sum.inr (w v)) =
      ∑ u : T, ((originalSinglePrimeSPlaceRelation K L S hS (w u).val B (φ u)).hom x (Sum.inr (w v))) := by
    change (LinearMap.proj (R := ℤ) (Sum.inr (w v))) ((∑ u : T, f u) x) = _
    rw [LinearMap.sum_apply]
    exact map_sum (LinearMap.proj (R := ℤ) (Sum.inr (w v))) (fun u : T => f u x) Finset.univ
  rw [he, Finset.sum_eq_single v]
  · exact originalSinglePrimeSPlaceRelation_evaluation K L S hS (w v).val B (w v).property (φ v) x
  · intro u _ huv
    apply originalSinglePrimeSPlaceRelation_outside_orbit K L S hS (w u).val B (w v)
    intro σ hσ
    apply huv
    apply Subtype.ext
    have he := congrArg (originalFinitePrimeBelow K L) hσ
    rw [originalFinitePrimeBelow_galois, hw, hw] at he
    exact he
  · intro h
    exact (h (Finset.mem_univ _)).elim

end
end Dubon2026
