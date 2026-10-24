import Dubon2026.SourceModularCoefficientModularRoots

/-! Reuse the proved original modular coefficient-field embedding/root
equivalence. Equality after an original field automorphism is detected by
the exact j_N root value. This supplies the embedding-action link between
the DUB-17/18 cyclic inertia orbits and actual restricted place fibers. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section

theorem embeddings_eq_postcomp_iff
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    {M : Type*} [Field M] [Algebra K M] {t : M}
    (hNK : (N : K) ≠ 0) (ht : Transcendental K t)
    (σ : M ≃ₐ[K] M) (hσ : σ t = t)
    (ψ ψ' : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M // ψ (jCoeff N K) = t}) :
    ψ'.val = σ.toAlgHom.comp ψ.val ↔
      (embeddingsEquivModularRoots N K hNK ht ψ').val =
        σ (embeddingsEquivModularRoots N K hNK ht ψ).val := by
  let ψσ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M // ψ (jCoeff N K) = t} :=
    ⟨σ.toAlgHom.comp ψ.val, by rw [AlgHom.comp_apply, ψ.property]; exact hσ⟩
  have hval : (embeddingsEquivModularRoots N K hNK ht ψσ).val =
      σ (embeddingsEquivModularRoots N K hNK ht ψ).val := by
    rw [embeddingsEquivModularRoots_apply, embeddingsEquivModularRoots_apply]
    rfl
  constructor
  · intro h
    have he : ψ' = ψσ := Subtype.ext h
    rw [he]
    exact hval
  · intro h
    have he := (embeddingsEquivModularRoots N K hNK ht).injective
      (Subtype.ext (h.trans hval.symm))
    exact congrArg Subtype.val he

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
