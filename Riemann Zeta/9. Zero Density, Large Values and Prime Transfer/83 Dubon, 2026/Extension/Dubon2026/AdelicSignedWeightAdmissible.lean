import Dubon2026.AdelicSignedFiniteCompletion

/-! # Actual finite-adelic admissibility in every original signed real-character space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every open original finite-adelic subgroup has finite-dimensional fixed vectors at each original signed real rotation weight. -/
theorem adelicSignedWeight_finiteDimensional (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ
      (adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) ⊓ adelicFiniteSubgroupFixedSpace f J :
        Submodule ℂ (AdelicCyclicHilbert f)) := by
  let S := adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) ⊓ adelicFiniteSubgroupFixedSpace f J
  let toC : S →ₗ[ℂ] AdelicFullFiniteCoreCompletion f :=
    (adelicSignedFiniteCompletionEquiv f hf hk i).symm.toLinearMap.comp (Submodule.inclusion inf_le_left)
  have hreal (x : S) : adelicSignedFiniteCompletionIsometry f hf hk i (toC x) = x.val :=
    congrArg Subtype.val ((adelicSignedFiniteCompletionEquiv f hf hk i).apply_symm_apply ⟨x.val, x.property.1⟩)
  have hfixed (x : S) (g : J) : adelicFullFiniteCoreCompletionRepresentation f g.val (toC x) = toC x := by
    apply (adelicSignedFiniteCompletionIsometry f hf hk i).injective
    exact (adelicSignedFiniteCompletionIsometry_intertwines f hf hk i g.val (toC x)).trans
      ((congrArg (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding g.val)) (hreal x)).trans
        ((x.property.2 g).trans (hreal x).symm))
  let L := (adelicFullFiniteCoreCompletionInclusion f).toLinearMap.comp toC
  have hmem (x : S) : L x ∈ adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J := by
    constructor
    · rw [← adelicFullFiniteCoreCompletionInclusion_range f hf hk]
      exact ⟨toC x, rfl⟩
    · intro g
      exact (adelicFullFiniteCoreCompletionInclusion_intertwines f g.val (toC x)).symm.trans
        (congrArg (adelicFullFiniteCoreCompletionInclusion f) (hfixed x g))
  let T : S →ₗ[ℂ] (adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J :
      Submodule ℂ (AdelicCyclicHilbert f)) := {
    toFun := fun x => ⟨L x, hmem x⟩
    map_add' := fun x y => Subtype.ext (L.map_add x y)
    map_smul' := fun c x => Subtype.ext (L.map_smul c x) }
  have hT : Function.Injective T := by
    intro x y he
    have hc : toC x = toC y := (adelicFullFiniteCoreCompletionInclusion f).injective (congrArg Subtype.val he)
    exact Subtype.ext ((hreal x).symm.trans
      ((congrArg (adelicSignedFiniteCompletionIsometry f hf hk i) hc).trans (hreal y)))
  letI := adelicFiniteOpenLowest_finiteDimensional f hf hk J hJ
  exact FiniteDimensional.of_injective T hT

end
end Dubon2026
