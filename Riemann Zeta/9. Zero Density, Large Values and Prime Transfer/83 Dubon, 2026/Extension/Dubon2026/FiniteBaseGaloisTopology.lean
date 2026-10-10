import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # The genuine Krull topology on an original finite-base fixing subgroup -/

namespace Dubon2026

noncomputable section
open scoped Topology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The actual fixing-subgroup equivalence is continuous for the original Krull topologies when the intermediate base is finite. -/
theorem finiteBase_fixingSubgroupEquiv_continuous
    (F : IntermediateField K Ω) [FiniteDimensional K F] :
    Continuous (IntermediateField.fixingSubgroupEquiv F) := by
  let e := IntermediateField.fixingSubgroupEquiv F
  apply continuous_of_continuousAt_one e.toMonoidHom
  apply continuousAt_def.mpr
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨M, hMfinite, hMU⟩ := hU
  letI := hMfinite
  letI : FiniteDimensional K M := Module.Finite.trans F M
  letI : FiniteDimensional K (M.restrictScalars K) :=
    inferInstanceAs (FiniteDimensional K M)
  have hopen := (M.restrictScalars K).fixingSubgroup_isOpen.preimage
    (continuous_subtype_val : Continuous (F.fixingSubgroup.subtype : F.fixingSubgroup → Gal(Ω/K)))
  have hnhds : (F.fixingSubgroup.subtype ⁻¹'
      ((M.restrictScalars K).fixingSubgroup : Set Gal(Ω/K))) ∈ 𝓝 1 :=
    hopen.mem_nhds (Subgroup.one_mem _)
  apply Filter.mem_of_superset hnhds
  intro σ hσ
  apply hMU
  change σ.val ∈ (M.restrictScalars K).fixingSubgroup at hσ
  change e σ ∈ M.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  exact hσ x hx

/-- Compactness of the actual original closed fixing subgroup makes the inverse Galois equivalence continuous too. -/
theorem finiteBase_fixingSubgroupEquiv_symm_continuous [IsGalois K Ω]
    (F : IntermediateField K Ω) [FiniteDimensional K F] :
    Continuous (IntermediateField.fixingSubgroupEquiv F).symm := by
  letI : CompactSpace F.fixingSubgroup :=
    isCompact_iff_compactSpace.mp F.fixingSubgroup_isClosed.isCompact
  exact (Continuous.homeoOfEquivCompactToT2
    (f := (IntermediateField.fixingSubgroupEquiv F).toEquiv)
    (finiteBase_fixingSubgroupEquiv_continuous F)).symm.continuous

/-- Finiteness of actual continuous characters over the original finite intermediate field gives finiteness on its genuine original fixing subgroup. -/
theorem finiteBase_fixingSubgroup_characters_finite [IsGalois K Ω]
    {T : Type*} [Group T] [TopologicalSpace T]
    (F : IntermediateField K Ω) [FiniteDimensional K F]
    [Finite (Gal(Ω/F) →ₜ* T)] : Finite (F.fixingSubgroup →ₜ* T) := by
  let e : Gal(Ω/F) →ₜ* F.fixingSubgroup := {
    toMonoidHom := (IntermediateField.fixingSubgroupEquiv F).symm.toMonoidHom
    continuous_toFun := finiteBase_fixingSubgroupEquiv_symm_continuous F }
  apply Finite.of_injective (fun f : F.fixingSubgroup →ₜ* T => f.comp e)
  intro f g hfg
  ext x
  obtain ⟨y, rfl⟩ := (IntermediateField.fixingSubgroupEquiv F).symm.surjective x
  exact DFunLike.congr_fun hfg y

end
end Dubon2026
