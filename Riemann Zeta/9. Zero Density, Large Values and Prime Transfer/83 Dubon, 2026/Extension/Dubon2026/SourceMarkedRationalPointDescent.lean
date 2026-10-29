import Dubon2026.SourceMarkedSeparableEmbeddingDescent
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original marked
chart over the finite torsion field. Galois covariance fixes the embedding
attached to every rational point. Original-coordinate separability then
descends its values from the algebraic closure. This is the necessary
finite-field-of-definition step; arbitrary changes of coefficient curve
are not needed for the source's ofJ specialization consumer. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve IntermediateField

theorem exists_descended_marked_chart
    {K k F Ω B : Type*} [Field K] [Field k] [Field F] [Field Ω] [Field B]
    [DecidableEq Ω] [DecidableEq B]
    [Algebra K k] [Algebra K F] [Algebra K Ω] [Algebra k Ω]
    [Algebra K B] [Algebra k B] [Algebra Ω B]
    [IsScalarTower K k Ω] [IsScalarTower K k B] [IsScalarTower K Ω B]
    [IsScalarTower k Ω B] [IsAlgClosure Ω B]
    (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) (x : F)
    [Algebra.IsSeparable (adjoin K ({x} : Set F)) F]
    (Φ : {P : (E.baseChange B).toAffine.Point // addOrderOf P = N} →
      {φ : F →ₐ[K] B // φ x = algebraMap k B E.j})
    (hnat : ∀ (σ : B ≃ₐ[k] B) P P',
      P'.val = Affine.Point.map (W' := E) σ.toAlgHom P.val →
      (Φ P').val = (σ.toAlgHom.restrictScalars K).comp (Φ P).val) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = N} →
      {ψ : F →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      ∀ (P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = N})
        (Q : {Q : (E.baseChange B).toAffine.Point // addOrderOf Q = N}),
        Q.val = Affine.Point.map (W' := E) (IsScalarTower.toAlgHom k Ω B) P.val →
        (IsScalarTower.toAlgHom K Ω B).comp (Ψ P).val = (Φ Q).val := by
  let ι := IsScalarTower.toAlgHom k Ω B
  let liftP : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = N} →
      {Q : (E.baseChange B).toAffine.Point // addOrderOf Q = N} :=
    fun P => ⟨Affine.Point.map (W' := E) ι P.val,
      (addOrderOf_injective _ (Affine.Point.map_injective ι) P.val).trans P.property⟩
  have hd (P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = N}) :
      ∃ ψ : F →ₐ[K] Ω, (IsScalarTower.toAlgHom K Ω B).comp ψ = (Φ (liftP P)).val ∧
        ψ x = algebraMap k Ω E.j := by
    apply exists_descended_separable_coordinate_embedding x (Φ (liftP P)).val
      (algebraMap k Ω E.j)
    · exact (Φ (liftP P)).property.trans
        (IsScalarTower.algebraMap_apply k Ω B E.j)
    · intro σ f
      have hp : (liftP P).val =
          Affine.Point.map (W' := E) (σ.restrictScalars k).toAlgHom (liftP P).val := by
        change Affine.Point.map ι P.val =
          Affine.Point.map _ (Affine.Point.map ι P.val)
        have hc : (σ.restrictScalars k).toAlgHom.comp ι = ι := by
          ext z
          exact σ.commutes z
        rw [Affine.Point.map_map, hc]
      exact (AlgHom.congr_fun (hnat (σ.restrictScalars k) (liftP P) (liftP P) hp) f).symm
  choose ψ hψ hx using hd
  refine ⟨fun P => ⟨ψ P, hx P⟩, ?_⟩
  intro P Q hQ
  have h : Q = liftP P := Subtype.ext hQ
  rw [h]
  exact hψ P

end
end Dubon2026.SourceFunctionField.MarkedChart
