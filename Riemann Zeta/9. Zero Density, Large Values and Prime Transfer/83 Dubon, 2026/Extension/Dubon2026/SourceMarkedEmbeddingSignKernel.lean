import Dubon2026.SourceEllipticGaloisTorsionMap

/-! DUB-17/18 -> reverse genus -> wild differential bounds -> original
normal auxiliary field. Identity or negation on all actual N-torsion
fixes every coordinate-normalized original-field embedding, by exhaustion,
Galois covariance and sign invariance of the proved marked chart. This
reuses the native inertia sign kernels without a new ramification group. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticReduction

theorem normalized_embeddings_fixed_of_torsion_sign
    {K B F M : Type*} [Field K] [Field B] [Field F] [Field M]
    [Algebra K B] [Algebra K F] [Algebra K M] [Algebra B M] [IsScalarTower K B M]
    [DecidableEq M] (E : WeierstrassCurve B) (N : ℕ) (x : F) (c : M)
    (Φ : {P : (E.baseChange M).toAffine.Point // addOrderOf P = N} →
      {ψ : F →ₐ[K] M // ψ x = c})
    (hsurj : Function.Surjective Φ)
    (hnat : ∀ (σ : M ≃ₐ[B] M) P Q, Q.val = Affine.Point.map (W' := E) σ.toAlgHom P.val →
      (Φ Q).val = (σ.toAlgHom.restrictScalars K).comp (Φ P).val)
    (hneg : ∀ P Q, Q.val = -P.val → Φ Q = Φ P)
    (σ : M ≃ₐ[B] M)
    (hσ : (∀ T, galoisTorsionMap E N σ T = T) ∨
      (∀ T, galoisTorsionMap E N σ T = -T))
    (ψ : F →ₐ[K] M) (hψ : ψ x = c) :
    (σ.toAlgHom.restrictScalars K).comp ψ = ψ := by
  obtain ⟨P, hP⟩ := hsurj ⟨ψ, hψ⟩
  let T : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) :=
    ⟨P.val, by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      simpa only [P.property] using addOrderOf_nsmul_eq_zero P.val⟩
  rcases hσ with hid | hminus
  · have hmap := congrArg Subtype.val (hid T)
    have hn := hnat σ P P hmap.symm
    rw [hP] at hn
    exact hn.symm
  · let Q : {P : (E.baseChange M).toAffine.Point // addOrderOf P = N} :=
      ⟨-P.val, (addOrderOf_neg P.val).trans P.property⟩
    have hmap := congrArg Subtype.val (hminus T)
    have hn := hnat σ P Q hmap.symm
    rw [hneg P Q rfl, hP] at hn
    exact hn.symm

end
end Dubon2026.SourceFunctionField.MarkedChart
