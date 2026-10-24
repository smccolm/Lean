import Dubon2026.SourceEllipticPrescribedPlaceOrbits
import Dubon2026.SourceRationalCoordinateFiberSurjectivity

/-! DUB-17/18 -> reverse genus -> actual exceptional place fibers.
Every actual modular coefficient-field place at the prescribed j-value
is reached by the original embedding family, and every such embedding
restricts to that fiber. Equality of restrictions is the source relation
on specialized cyclic subgroups. All finite Galois, model, torsion and
root data remain derived and retained. Normalized fiber cardinalities
are the next remaining local obligation. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_prescribed_ofJ_place_fibers
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
        ∀ u : Place K (modularFunctionFieldCoeff N K),
          0 < u.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j) →
          ∃ ψ, Place.restrictAlongFinite ψ.val (hfinite ψ) v = u := by
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit, hroots, hlift⟩ :=
    exists_prescribed_ofJ_place_orbits K Ω p hp N hNK E₀
  letI := decResidue
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  haveI := hfd
  haveI := hgal
  obtain ⟨Θ, hΘ, hnat, hrootOrbit, Φ, hΦj, hΦnat, hΦorbit, hfinite, hplaceOrbit⟩ := hroots
  have hc : Nat.card {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} =
      SourceLevelProjective.dedekindPsi N := by
    simpa only [baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      (SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (F := K) (K := K) E₀ hNK)
  have hpos : 0 < Nat.card
      {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} := by
    rw [hc]
    exact SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  obtain ⟨S₀⟩ := (Nat.card_pos_iff.mp hpos).1
  let ι := Φ (Ψ.symm S₀)
  refine ⟨M, hfd, hgal, v, Ψ, Φ, hfinite, hv, hplaceOrbit, ?_, ?_⟩
  · intro ψ
    have ho := Place.ord_restrictAlongFinite ψ.val (hfinite ψ) v
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j)
    rw [map_sub, ψ.property, ψ.val.commutes] at ho
    rw [ho] at hv
    exact (mul_pos_iff_of_pos_right
      (Place.ord_restrictAlongFinite_uniformizer_pos ψ.val (hfinite ψ) v)).mp hv
  · intro u hu
    obtain ⟨ψ, hψ, he⟩ := Place.exists_coordinate_embedding_restrict_eq (jCoeff N K)
      (transcendental_jCoeff N K) ι.val ι.property v E₀.j hv u hu
    exact ⟨⟨ψ, hψ⟩, he⟩

end
end Dubon2026.SourceEllipticDivisionField
