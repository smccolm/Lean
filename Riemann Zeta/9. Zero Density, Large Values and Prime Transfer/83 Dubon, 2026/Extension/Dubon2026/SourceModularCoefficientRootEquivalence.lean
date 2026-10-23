import Dubon2026.SourceModularCoefficientHomSpecialization

/-! DUB-17/18 -> good reduction -> exceptional-fiber orbit census. Actual
coefficient-field embeddings over a prescribed transcendental j correspond
to roots of the actual j_N minimal polynomial, with the root equal to the
image of the original j_N. The polynomial-to-cyclic-subgroup interpretation
and inertia orbit map remain separate, unresolved obligations. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] {j₀ : Ω}

omit [IsAlgClosed K] in
theorem mem_level_aroots_iff (hj₀ : Transcendental K j₀) (y : Ω) :
    letI := coordinateAlgebra N K hj₀
    y ∈ (minpoly K⟮jCoeff N K⟯ (jN N K)).aroots Ω ↔
      ((minpoly K⟮jCoeff N K⟯ (jN N K)).map
        (coordinateSpecialization N K hj₀).toRingHom).IsRoot y := by
  letI := coordinateAlgebra N K hj₀
  rw [mem_aroots', aeval_def, eval₂_eq_eval_map]
  exact ⟨fun h => h.2, fun h => ⟨
    ((minpoly.monic (level_isIntegral N K)).map _).ne_zero, h⟩⟩

/-- The actual embedding-root correspondence over any transcendental coordinate value. -/
def embeddingsEquivRoots (hNK : (N : K) ≠ 0) (hj₀ : Transcendental K j₀) :
    {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀} ≃
      {y : Ω // ((minpoly K⟮jCoeff N K⟯ (jN N K)).map
        (coordinateSpecialization N K hj₀).toRingHom).IsRoot y} := by
  letI := coordinateAlgebra N K hj₀
  exact (embeddingsEquivCoordinateHom N K hj₀).trans
    (((AlgEquiv.arrowCongr (adjoinLevelEquiv N K hNK)
      (AlgEquiv.refl : Ω ≃ₐ[K⟮jCoeff N K⟯] Ω)).symm.trans
        (algHomAdjoinIntegralEquiv K⟮jCoeff N K⟯ (level_isIntegral N K))).trans
          (Equiv.subtypeEquivRight (mem_level_aroots_iff N K hj₀)))

theorem embeddingsEquivRoots_apply (hNK : (N : K) ≠ 0) (hj₀ : Transcendental K j₀)
    (ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀}) :
    (embeddingsEquivRoots N K hNK hj₀ ψ).1 = ψ.1 (jN N K) := by
  letI := coordinateAlgebra N K hj₀
  let χ := (AlgEquiv.arrowCongr (adjoinLevelEquiv N K hNK)
    (AlgEquiv.refl : Ω ≃ₐ[K⟮jCoeff N K⟯] Ω)).symm (embeddingsEquivCoordinateHom N K hj₀ ψ)
  let e := algHomAdjoinIntegralEquiv (K := Ω) K⟮jCoeff N K⟯ (level_isIntegral N K)
  change (e χ).1 = ψ.1 (jN N K)
  have h := algHomAdjoinIntegralEquiv_symm_apply_gen K⟮jCoeff N K⟯
    (level_isIntegral N K) (e χ)
  rw [show (algHomAdjoinIntegralEquiv K⟮jCoeff N K⟯ (level_isIntegral N K)).symm (e χ) = χ
    from e.symm_apply_apply χ] at h
  exact h.symm

theorem specialized_level_minpoly_degree (hNK : (N : K) ≠ 0)
    (hj₀ : Transcendental K j₀) :
    ((minpoly K⟮jCoeff N K⟯ (jN N K)).map
      (coordinateSpecialization N K hj₀).toRingHom).natDegree =
        SourceLevelProjective.dedekindPsi N := by
  rw [(minpoly.monic (level_isIntegral N K)).natDegree_map, level_minpoly_natDegree N K hNK]

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
