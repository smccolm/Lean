import Dubon2026.SourceMarkedNaturalSignChart

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> natural marked
chart. Diamond covariance of a sign-invariant chart needs only a signed
diamond lift at one point. Galois maps commute with integer multiplication;
the four possible signs give the same field embedding. This avoids the
stronger unsigned transport lemma while preserving the exact chart output. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve

theorem sign_chart_diamond_of_signed_lift
    {K k F Ω : Type*} [Field K] [Field k] [Field F] [Field Ω] [DecidableEq Ω]
    [Algebra K k] [Algebra K F] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω]
    (E : WeierstrassCurve k) (N : ℕ)
    (P : (E.baseChange Ω).toAffine.Point) (ψ : F →ₐ[K] Ω)
    (Ψ : {Q : (E.baseChange Ω).toAffine.Point // addOrderOf Q = N} → (F →ₐ[K] Ω))
    (htrans : ∀ Q : (E.baseChange Ω).toAffine.Point, addOrderOf Q = N →
      ∃ σ : Ω ≃ₐ[k] Ω, Affine.Point.map (W' := E) σ.toAlgHom P = Q ∨
        Affine.Point.map (W' := E) σ.toAlgHom P = -Q)
    (hΨ : ∀ Q (σ : Ω ≃ₐ[k] Ω),
      (Affine.Point.map (W' := E) σ.toAlgHom P = Q.val ∨
        Affine.Point.map (W' := E) σ.toAlgHom P = -Q.val) →
        Ψ Q = (σ.toAlgHom.restrictScalars K).comp ψ)
    (ρ : F ≃ₐ[K] F) (n : ℕ) (δ : Ω ≃ₐ[k] Ω)
    (hδψ : (δ.toAlgHom.restrictScalars K).comp ψ = ψ.comp ρ.toAlgHom)
    (hδ : Affine.Point.map (W' := E) δ.toAlgHom P = n • P ∨
      Affine.Point.map (W' := E) δ.toAlgHom P = -(n • P))
    (Q Q' : {Q : (E.baseChange Ω).toAffine.Point // addOrderOf Q = N})
    (hQ' : Q'.val = n • Q.val) :
    Ψ Q' = (Ψ Q).comp ρ.toAlgHom := by
  obtain ⟨σ, hσ⟩ := htrans Q.val Q.property
  let τ : Ω ≃ₐ[k] Ω := δ.trans σ
  have hτ : Affine.Point.map (W' := E) τ.toAlgHom P = Q'.val ∨
      Affine.Point.map (W' := E) τ.toAlgHom P = -Q'.val := by
    change Affine.Point.map (W' := E) (σ.toAlgHom.comp δ.toAlgHom) P = Q'.val ∨
      Affine.Point.map (W' := E) (σ.toAlgHom.comp δ.toAlgHom) P = -Q'.val
    rw [← Affine.Point.map_map]
    rcases hδ with hd | hd <;> rcases hσ with hs | hs
    · left; rw [hd, map_nsmul, hs, ← hQ']
    · right; rw [hd, map_nsmul, hs, smul_neg, ← hQ']
    · right; rw [hd, map_neg, map_nsmul, hs, ← hQ']
    · left; rw [hd, map_neg, map_nsmul, hs, smul_neg, neg_neg, ← hQ']
  calc
    Ψ Q' = (τ.toAlgHom.restrictScalars K).comp ψ := hΨ Q' τ hτ
    _ = (σ.toAlgHom.restrictScalars K).comp
        ((δ.toAlgHom.restrictScalars K).comp ψ) := rfl
    _ = (σ.toAlgHom.restrictScalars K).comp (ψ.comp ρ.toAlgHom) := by rw [hδψ]
    _ = ((σ.toAlgHom.restrictScalars K).comp ψ).comp ρ.toAlgHom := rfl
    _ = (Ψ Q).comp ρ.toAlgHom := by rw [hΨ Q σ hσ]

end
end Dubon2026.SourceFunctionField.MarkedChart
