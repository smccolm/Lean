import Dubon2026.SourceEllipticPrescribedFiberOrders

/-! DUB-17/18 -> reverse genus -> exceptional place census.
The original specialization supplies a surjective map from actual cyclic
subgroups of the prescribed elliptic curve to the actual modular j-fiber.
Its equality relation is the literal variable-change relation, and its
class sizes equal normalized place orders. This direct classifier avoids
an additional moduli-point presentation while preserving the source data. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceFunctionField
open SourceFunctionField.CoefficientPresentation SourceEllipticStabilizer
noncomputable section

theorem exists_cyclic_modular_place_fiber_classification
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
    ∃ f : {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} →
      {u : Place K (modularFunctionFieldCoeff N K) //
        0 < u.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j)},
      Function.Surjective f ∧
      (∀ S T, f S = f T ↔ cyclicStabilizerRelated E₀ S.val T.val) ∧
      ∀ S, (f S).val.ord
        (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j) =
        Nat.card {T : {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} //
          cyclicStabilizerRelated E₀ S.val T.val} := by
  obtain ⟨M, _hfd, _hgal, v, Ψ, Φ, hfinite, _hv, horbit, hpos, hsurj, horder⟩ :=
    exists_prescribed_ofJ_fiber_orders K Ω p hp N hNK E₀
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  let e := Ψ.symm.trans Φ
  let f (S : {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
      {u : Place K (modularFunctionFieldCoeff N K) //
        0 < u.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j)} :=
    ⟨Place.restrictAlongFinite (e S).val (hfinite (e S)) v, hpos (e S)⟩
  have hrel (S T) : f S = f T ↔ cyclicStabilizerRelated E₀ S.val T.val := by
    rw [Subtype.ext_iff]
    have h := horbit (Ψ.symm S) (Ψ.symm T)
    simp only [Equiv.apply_symm_apply] at h
    exact eq_comm.trans h.symm
  refine ⟨f, ?_, hrel, ?_⟩
  · intro u
    obtain ⟨ψ, hψ⟩ := hsurj u.val u.property
    refine ⟨e.symm ψ, Subtype.ext ?_⟩
    change Place.restrictAlongFinite (e (e.symm ψ)).val (hfinite (e (e.symm ψ))) v = u.val
    simpa only [Equiv.apply_symm_apply] using hψ
  · intro S
    have hc := horder (e S)
    let b : {T : {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} //
        cyclicStabilizerRelated E₀ S.val T.val} ≃
        {ψ' : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
          ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X} //
          Place.restrictAlongFinite ψ'.val (hfinite ψ') v =
            Place.restrictAlongFinite (e S).val (hfinite (e S)) v} :=
      Equiv.subtypeEquiv e (fun T =>
      show cyclicStabilizerRelated E₀ S.val T.val ↔
        Place.restrictAlongFinite (e T).val (hfinite (e T)) v =
          Place.restrictAlongFinite (e S).val (hfinite (e S)) v from
        (hrel S T).symm.trans (Subtype.ext_iff.trans eq_comm))
    have he := Nat.card_congr b
    change (f S).val.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) E₀.j) = _ at hc
    rw [he]
    exact hc

end
end Dubon2026.SourceEllipticDivisionField
