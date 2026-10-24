import Dubon2026.SourceEllipticPrescribedPlaceFibers
import Dubon2026.SourceRationalEmbeddingFiberOrder

/-! DUB-17/18 -> reverse genus -> normalized exceptional-fiber counts.
The actual modular coefficient-field place fiber is reached by the original
embedding family, its equality classes are the source cyclic-subgroup
relation, and the normalized j-order at every restriction is exactly its
embedding-fiber cardinality. All group/order inputs are derived. The next
step transports this cardinality through the cyclic-subgroup equivalence
to the existing numerical exceptional-orbit census. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_prescribed_ofJ_fiber_orders
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
    let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
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
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j) ∧
        (∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
          Place.restrictAlongFinite (Φ T).val (hfinite (Φ T)) v =
            Place.restrictAlongFinite (Φ S).val (hfinite (Φ S)) v) ∧
        (∀ ψ, 0 < (Place.restrictAlongFinite ψ.val (hfinite ψ) v).ord
          (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j)) ∧
        (∀ u : Place K (modularFunctionFieldCoeff N K),
          0 < u.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j) →
          ∃ ψ, Place.restrictAlongFinite ψ.val (hfinite ψ) v = u) ∧
        ∀ ψ, (Place.restrictAlongFinite ψ.val (hfinite ψ) v).ord
          (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j) =
          Nat.card {ψ' : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
              ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X} //
            Place.restrictAlongFinite ψ'.val (hfinite ψ') v =
              Place.restrictAlongFinite ψ.val (hfinite ψ) v} := by
  obtain ⟨M, hfd, hgal, v, Ψ, Φ, hfinite, hv, horbit, hpos, hsurj⟩ :=
    exists_prescribed_ofJ_place_fibers K Ω p hp N hNK E₀
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  haveI := hfd
  haveI := hgal
  refine ⟨M, hfd, hgal, v, Ψ, Φ, hfinite, hv, horbit, hpos, hsurj, ?_⟩
  intro ψ
  exact Place.restricted_coordinate_order_eq_embedding_fiber_card (jCoeff N K)
    (transcendental_jCoeff N K) v E₀.j hv ψ

end
end Dubon2026.SourceEllipticDivisionField
