import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.Topology.Algebra.Module.Compact

/-! # Compactness of actual finite integer lattices inside original local fields -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The original base-integer inclusion into the original extension field
is continuous, by the already proved continuity of the actual local map
between its original compact separated integer rings. -/
theorem localField_integerScalar_continuous : Continuous (algebraMap 𝒪[K] L) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  have h : Continuous (algebraMap 𝒪[K] 𝒪[L]) :=
    compactSeparatedLocalRingHom_continuous (algebraMap 𝒪[K] 𝒪[L])
  have hc : Continuous (algebraMap 𝒪[L] L) := continuous_subtype_val
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[L] L]
  exact hc.comp h

/-- Every actual finite base-integer lattice in the original extension field
is compact in its original topology. Its scalar action is the original field
action and its finite generation is explicit. -/
theorem localField_finite_lattice_isCompact
    (A : Submodule 𝒪[K] L) (hA : A.FG) : IsCompact (A : Set L) := by
  have h := localField_integerScalar_continuous K L
  haveI : ContinuousSMul 𝒪[K] L := {
    continuous_smul := by
      simpa only [Algebra.smul_def] using (h.comp continuous_fst).mul continuous_snd }
  exact Submodule.isCompact_of_fg hA

end
end Dubon2026
