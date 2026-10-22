import Dubon2026.SourceOriginalComplexFieldIndependence

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> extension
of actual arithmetic places. A complex-linear combination of original local
functions cannot equal an original function outside their Qbar-linear span.
The proved preservation of original Laurent coefficient independence supplies
this separation directly. Applied to the inverse uniformizer, it proves the
extended local ring has a proper uniformizer ideal, enabling place existence.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, span-separation argument.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ)
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem sum_ne_of_not_mem_span
    {ι : Type*} (c : ι → ℂ) (s : Finset ι) (o : ι → FQ) (y : FQ)
    (hy : y ∉ Submodule.span Qbar (Set.range o)) :
    ∑ j ∈ s, algebraMap ℂ FC (c j) * algebraMap FQ FC (o j) ≠ algebraMap FQ FC y := by
  classical
  intro heq
  set M := Submodule.span Qbar (Set.range o) with hM
  let bM := Module.Basis.ofVectorSpace Qbar M
  let v : Module.Basis.ofVectorSpaceIndex Qbar M → FQ := fun l => (bM l : FQ)
  have hv : LinearIndependent Qbar v :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hspan : Submodule.span Qbar (Set.range v) = M := by
    change Submodule.span Qbar (Set.range (M.subtype ∘ bM)) = M
    rw [Set.range_comp, Submodule.span_image, bM.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hyv : y ∉ Submodule.span Qbar (Set.range v) := by rwa [hspan]
  have hLI := fieldMap_linearIndependent N
    (hv.option hyv)
  have ho : ∀ j, o j ∈ M := fun j => Submodule.subset_span ⟨j, rfl⟩
  let R : ι → (Module.Basis.ofVectorSpaceIndex Qbar M →₀ Qbar) := fun j => bM.repr ⟨o j, ho j⟩
  have hR : ∀ j, ∀ T : Finset (Module.Basis.ofVectorSpaceIndex Qbar M), (R j).support ⊆ T →
      ∑ l ∈ T, algebraMap Qbar FQ (R j l) * v l = o j := by
    intro j T hT
    have h1 := bM.linearCombination_repr ⟨o j, ho j⟩
    rw [Finsupp.linearCombination_apply] at h1
    have h2 := congrArg (M.subtype) h1
    rw [map_finsuppSum, Finsupp.sum_of_support_subset _ hT _ (fun l _ => by simp)] at h2
    have h3 : ∑ x ∈ T, M.subtype ((R j) x • bM x) = o j := h2
    rw [← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Module.Basis.ofVectorSpaceIndex Qbar M),
      ∀ j ∈ s, (R j).support ⊆ T :=
    ⟨s.biUnion fun j => (R j).support, fun j hj =>
      Finset.subset_biUnion_of_mem (fun j => (R j).support) hj⟩
  let κ : Option (Module.Basis.ofVectorSpaceIndex Qbar M) → ℂ :=
    fun i => Option.casesOn' i (-1) (fun l => ∑ j ∈ s, R j l • c j)
  have hinner : ∑ l ∈ T, (∑ j ∈ s, R j l • c j) • algebraMap FQ FC (v l) =
      ∑ j ∈ s, algebraMap ℂ FC (c j) * algebraMap FQ FC (o j) := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hR j T (hT j hj), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply Qbar ℂ FC, ← IsScalarTower.algebraMap_apply Qbar FQ FC]
    ring
  have hsum : ∑ i ∈ Finset.insertNone T,
      κ i • algebraMap FQ FC (Option.casesOn' i y v) = 0 := by
    rw [Finset.sum_insertNone]
    simp only [κ, Option.casesOn'_none, Option.casesOn'_some]
    rw [hinner, heq, neg_one_smul, neg_add_cancel]
  have := linearIndependent_iff'.1 hLI (Finset.insertNone T) κ hsum none (by simp)
  simp [κ] at this

end
end Dubon2026.SourceFunctionField.OriginalConstantField
