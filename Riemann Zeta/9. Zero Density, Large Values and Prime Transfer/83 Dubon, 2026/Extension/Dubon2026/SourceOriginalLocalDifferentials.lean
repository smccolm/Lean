import Dubon2026.SourceCurveLocalDifferentials
import Dubon2026.SourceOriginalDifferentialRank

/-! DUB-17/18 -> matching cusp-form lower dimension bound -> regular
differential realization. Every actual place of the original modular function
field has a nonzero spanning uniformizer differential. Its coordinate
condition exactly characterizes the original regular differential subspace,
whose q-expansion is injective. No local spanning or separability premise
remains. The dimension and geometric-genus comparison remain separate.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open KaehlerDifferential SourceCurve SourceDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

omit [NeZero N] in
theorem original_place_dCoord_ne_zero (v : Place L (modularFunctionFieldOver N L)) :
    v.dCoord ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := (D_original_eq_zero_iff N L v.uniformizer).mp h
  have ho := v.ord_uniformizer
  rw [hc, v.ord_algebraMap] at ho
  exact zero_ne_one ho

/-- Each genuine place uniformizer gives a spanning differential of the actual original field. -/
theorem original_place_dCoordGenerates (v : Place L (modularFunctionFieldOver N L)) :
    v.DCoordGenerates :=
  ⟨(finrank_eq_one_iff_of_nonzero _ (original_place_dCoord_ne_zero N L v)).mp
    (finrank_original_differentials N L)⟩

/-- The regularity condition uses the actual normalized local differential coefficient at every place. -/
theorem mem_original_regularDifferentials_iff (ω : Ω[modularFunctionFieldOver N L⁄L]) :
    ω ∈ regularDifferentials L (modularFunctionFieldOver N L) ↔
      ∀ v : Place L (modularFunctionFieldOver N L),
        v.differentialCoeff ω ∈ v.toValuationSubring := by
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  constructor
  · intro h v
    obtain ⟨f, hf, he⟩ := h v
    rwa [v.differentialCoeff_unique he]
  · intro h v
    exact ⟨v.differentialCoeff ω, h v, (v.differentialCoeff_smul_dCoord ω).symm⟩

/-- The actual regular differential subspace has injective original q-expansion. -/
theorem regularDifferential_qExpansion_injective :
    Function.Injective (fun ω : regularDifferentials L (modularFunctionFieldOver N L) =>
      diffQExp (modularFunctionFieldOver N L) (ω : Ω[modularFunctionFieldOver N L⁄L])) := by
  intro ω η h
  exact Subtype.ext (diffQExp_original_injective N L h)

end
end Dubon2026.SourceFunctionField
