import Dubon2026.SourceEllipticCharTwoPlaceFibers

/-! DUB-17/18 -> characteristic-two weighted exceptional census.
Reuse the existing actual cyclic specialization, embedding-orbit reflection
and rational-coordinate place/fiber theorems with the constructed full inertia
image. No generic point-map or place infrastructure is rebuilt.

 A surjective classifier from the actual exceptional characteristic-
two cyclic subgroups to the actual modular j=0 places. Equality is
exactly the full stabilizer relation, and normalized j orders are its
class cardinalities. This supplies the geometric input to the DUB-17/18
weighted census; the order-twelve quotient marks remain to be applied. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceEllipticCharTwo SourceEllipticStabilizer
open SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_char_two_cyclic_modular_place_classification
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) :
    ∃ f : {S : AddSubgroup (ofJ0 K).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} →
      {u : Place K (modularFunctionFieldCoeff N K) // 0 < u.ord (jCoeff N K)},
      Function.Surjective f ∧
      (∀ S T, f S = f T ↔ cyclicStabilizerRelated (ofJ0 K) S.val T.val) ∧
      ∀ S, (f S).val.ord (jCoeff N K) =
        Nat.card {T : {S : AddSubgroup (ofJ0 K).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} //
          cyclicStabilizerRelated (ofJ0 K) S.val T.val} := by
  obtain ⟨M, _hfd, _hgal, v, Ψ, Φ, hfinite, horbit, hpos, hsurj, horder⟩ :=
    exists_char_two_modular_place_fibers K Ω N hNK
  let e := Ψ.symm.trans Φ
  let f (S : {S : AddSubgroup (ofJ0 K).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
      {u : Place K (modularFunctionFieldCoeff N K) // 0 < u.ord (jCoeff N K)} :=
    ⟨Place.restrictAlongFinite (e S).val (hfinite (e S)) v, hpos (e S)⟩
  have hrel (S T) : f S = f T ↔ cyclicStabilizerRelated (ofJ0 K) S.val T.val := by
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
    let b : {T : {S : AddSubgroup (ofJ0 K).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} //
        cyclicStabilizerRelated (ofJ0 K) S.val T.val} ≃
        {ψ' : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
          ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X} //
          Place.restrictAlongFinite ψ'.val (hfinite ψ') v =
            Place.restrictAlongFinite (e S).val (hfinite (e S)) v} :=
      Equiv.subtypeEquiv e (fun T =>
        (hrel S T).symm.trans (Subtype.ext_iff.trans eq_comm))
    have he := Nat.card_congr b
    change (f S).val.ord (jCoeff N K) = _ at hc
    rw [he]
    exact hc

end
end Dubon2026.SourceEllipticDivisionField
