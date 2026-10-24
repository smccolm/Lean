import Dubon2026.SourceEllipticCharThreeEmbeddingOrbits
import Dubon2026.SourceRationalCoordinatePlaceOrbits
import Dubon2026.SourceRationalCoordinateFiberSurjectivity
import Dubon2026.SourceRationalEmbeddingFiberOrder
import Dubon2026.SourceEllipticCyclicCount

/-! Actual characteristic-three modular places are restrictions of the
constructed embedding family. The stabilizer classes are exactly its
fibers, and each j order is its fiber cardinality. The existing all-
characteristic restriction and order theorems discharge these inputs to
the DUB-17/18 exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceEllipticExceptional SourceEllipticStabilizer
open SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_char_three_modular_place_fibers
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) :
    let E := ofJ (RatFunc.X : RatFunc K)
    let E₀ := EA (-1 : K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      ∃ (v : Place K M)
        (Ψ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N})
        (Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X})
        (hfinite : ∀ ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X}, ψ.val.toRingHom.Finite),
        (∀ S T, cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
          Place.restrictAlongFinite (Φ T).val (hfinite (Φ T)) v =
            Place.restrictAlongFinite (Φ S).val (hfinite (Φ S)) v) ∧
        (∀ ψ, 0 < (Place.restrictAlongFinite ψ.val (hfinite ψ) v).ord (jCoeff N K)) ∧
        (∀ u : Place K (modularFunctionFieldCoeff N K), 0 < u.ord (jCoeff N K) →
          ∃ ψ, Place.restrictAlongFinite ψ.val (hfinite ψ) v = u) ∧
        ∀ ψ, (Place.restrictAlongFinite ψ.val (hfinite ψ) v).ord (jCoeff N K) =
          Nat.card {ψ' : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
              ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X} //
            Place.restrictAlongFinite ψ'.val (hfinite ψ') v =
              Place.restrictAlongFinite ψ.val (hfinite ψ) v} := by
  let E₀ := EA (-1 : K)
  letI : E₀.IsElliptic := isElliptic_EA_neg_one_of_char_three
  obtain ⟨M, hfd, hgal, v, Ψ, Φ, hv, horbit⟩ :=
    exists_char_three_modular_embedding_orbits K Ω N hNK
  haveI := hfd
  haveI := hgal
  have hfinite (ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
      ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X}) : ψ.val.toRingHom.Finite :=
    (finite_galois_along_coordinate (jCoeff N K) (transcendental_jCoeff N K)
      ψ.val ψ.property).1
  have hc : Nat.card {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} =
      SourceLevelProjective.dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (F := K) (K := K) E₀ hNK
  have hpos : 0 < Nat.card {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} := by
    rw [hc]
    exact SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  obtain ⟨S₀⟩ := (Nat.card_pos_iff.mp hpos).1
  let ι := Φ (Ψ.symm S₀)
  refine ⟨M, hfd, hgal, v, Ψ, Φ, hfinite, ?_, ?_, ?_, ?_⟩
  · intro S T
    rw [horbit S T]
    exact (Place.restrictAlongFinite_eq_iff_inertia (jCoeff N K)
      (transcendental_jCoeff N K) (Φ S).val (Φ T).val (Φ S).property (Φ T).property v).symm
  · intro ψ
    have ho := Place.ord_restrictAlongFinite ψ.val (hfinite ψ) v (jCoeff N K)
    rw [ψ.property] at ho
    rw [ho] at hv
    exact (mul_pos_iff_of_pos_right
      (Place.ord_restrictAlongFinite_uniformizer_pos ψ.val (hfinite ψ) v)).mp hv
  · intro u hu
    obtain ⟨ψ, hψ, he⟩ := Place.exists_coordinate_embedding_restrict_eq (jCoeff N K)
      (transcendental_jCoeff N K) ι.val ι.property v (0 : K)
      (by simpa only [map_zero, sub_zero] using hv) u
      (by simpa only [map_zero, sub_zero] using hu)
    exact ⟨⟨ψ, hψ⟩, he⟩
  · intro ψ
    simpa only [map_zero, sub_zero] using
      Place.restricted_coordinate_order_eq_embedding_fiber_card (jCoeff N K)
        (transcendental_jCoeff N K) v (0 : K)
        (by simpa only [map_zero, sub_zero] using hv) ψ

end
end Dubon2026.SourceEllipticDivisionField
