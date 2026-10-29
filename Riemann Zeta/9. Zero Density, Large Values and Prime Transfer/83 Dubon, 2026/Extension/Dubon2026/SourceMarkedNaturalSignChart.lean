import Dubon2026.SourceMarkedOrbitMap
import Dubon2026.SourceMarkedChartStabilizerActions

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> natural marked
chart. Extend the matched original embedding and point to all actual
exact-order points modulo sign. The stabilizer and transitivity inputs are
strictly upstream and are discharged by the original-field construction.
This is the sign-invariant chart required by the finite-fiber consumer. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve MarkedTorsion

theorem exists_natural_sign_chart_of_stabilizers
    {K k F Ω : Type*} [Field K] [Field k] [Field F] [Field Ω] [DecidableEq Ω]
    [Algebra K k] [Algebra K F] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω]
    (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) (x : F)
    (P : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = N)
    (ψ : F →ₐ[K] Ω) (hψ : ψ x = algebraMap k Ω E.j)
    (hstab : ∀ σ : Ω ≃ₐ[k] Ω,
      (Affine.Point.map (W' := E) σ.toAlgHom P = P ∨
        Affine.Point.map (W' := E) σ.toAlgHom P = -P) ↔
        (σ.toAlgHom.restrictScalars K).comp ψ = ψ)
    (htrans : ∀ Q : (E.baseChange Ω).toAffine.Point, addOrderOf Q = N →
      ∃ σ : Ω ≃ₐ[k] Ω, Affine.Point.map (W' := E) σ.toAlgHom P = Q ∨
        Affine.Point.map (W' := E) σ.toAlgHom P = -Q) :
    ∃ Ψ : {Q : (E.baseChange Ω).toAffine.Point // addOrderOf Q = N} →
        {φ : F →ₐ[K] Ω // φ x = algebraMap k Ω E.j},
      (∀ Q (σ : Ω ≃ₐ[k] Ω),
        (Affine.Point.map (W' := E) σ.toAlgHom P = Q.val ∨
          Affine.Point.map (W' := E) σ.toAlgHom P = -Q.val) →
          (Ψ Q).val = (σ.toAlgHom.restrictScalars K).comp ψ) ∧
      (∀ Q Q' (σ : Ω ≃ₐ[k] Ω), Q'.val = Affine.Point.map (W' := E) σ.toAlgHom Q.val →
        (Ψ Q').val = (σ.toAlgHom.restrictScalars K).comp (Ψ Q).val) ∧
      (∀ Q Q', Ψ Q' = Ψ Q ↔ Q'.val = Q.val ∨ Q'.val = -Q.val) := by
  let X := {s : Set (E.baseChange Ω).toAffine.Point // ∃ Q : (E.baseChange Ω).toAffine.Point,
    addOrderOf Q = N ∧ s = {Q, -Q}}
  let Y := {φ : F →ₐ[K] Ω // φ x = algebraMap k Ω E.j}
  letI : MulAction (Ω ≃ₐ[k] Ω) X := signClassGaloisAction E N
  letI : MulAction (Ω ≃ₐ[k] Ω) Y := normalizedEmbeddingAction x E.j
  let pair : {Q : (E.baseChange Ω).toAffine.Point // addOrderOf Q = N} → X :=
    fun Q => ⟨{Q.val, -Q.val}, Q.val, Q.property, rfl⟩
  let η : X := pair ⟨P, hP⟩
  let ξ : Y := ⟨ψ, hψ⟩
  have ht : ∀ z : X, ∃ σ : Ω ≃ₐ[k] Ω, σ • η = z := by
    rintro ⟨s, Q, hQ, hs⟩
    obtain ⟨σ, hσ⟩ := htrans Q hQ
    refine ⟨σ, Subtype.ext ?_⟩
    have he := (signClass_smul_eq_iff E N P Q hP hQ σ).mpr hσ
    exact (congrArg Subtype.val he).trans hs.symm
  have hs : MulAction.stabilizer (Ω ≃ₐ[k] Ω) η =
      MulAction.stabilizer (Ω ≃ₐ[k] Ω) ξ := by
    ext σ
    exact (signClass_stabilizer_iff E N P hP σ).trans
      ((hstab σ).trans (normalizedEmbedding_stabilizer_iff x E.j ψ hψ σ).symm)
  obtain ⟨f, hf, hinj, heq⟩ := exists_injective_equivariant_map_of_stabilizer_eq η ξ ht hs
  refine ⟨fun Q => f (pair Q), ?_, ?_, ?_⟩
  · intro Q σ hσ
    have hp : σ • η = pair Q :=
      (signClass_smul_eq_iff E N P Q.val hP Q.property σ).mpr hσ
    change (f (pair Q)).val = _
    rw [← hp, heq, hf]
    rfl
  · intro Q Q' σ hσ
    have hp : σ • pair Q = pair Q' :=
      (signClass_smul_eq_iff E N Q.val Q'.val Q.property Q'.property σ).mpr
        (Or.inl hσ.symm)
    change (f (pair Q')).val = _
    rw [← hp, heq]
    rfl
  · intro Q Q'
    change f (pair Q') = f (pair Q) ↔ _
    rw [hinj.eq_iff]
    have hp : pair Q' = pair Q ↔
        ({Q'.val, -Q'.val} : Set (E.baseChange Ω).toAffine.Point) = {Q.val, -Q.val} :=
      Subtype.ext_iff
    exact hp.trans (signPair_eq_iff Q'.val Q.val)

end
end Dubon2026.SourceFunctionField.MarkedChart
