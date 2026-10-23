import Dubon2026.SourceCurveCompletionTraceFactor
import Dubon2026.SourceCurveCompletionResidueField
import Dubon2026.SourceCurveLocalTateLeibniz

/-! The literal local Tate residue is preserved under completion. The
proved principal-part factorization and cyclicity compare finite-rank
traces for integral second arguments; the proved Leibniz rule and native
fraction-field representation cover every original argument. This is the
local completion bridge for DUB-17/18 residue/field-trace compatibility. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Completion preserves local Tate residues with an integral second argument. -/
theorem completion_tateResidue_of_integral
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F)
    (hg : g ∈ v.toValuationSubring) :
    v.completionPlace.tateResidue
      (algebraMap F v.adicCompletion f) (algebraMap F v.adicCompletion g) =
        v.tateResidue f g := by
  let i := v.completionIntegralInclusion
  let B := v.completionCommutatorFactor hres f g
  have hBI := v.completionCommutatorFactor_comp_inclusion hres f g hg
  have hIB := v.inclusion_comp_completionCommutatorFactor hres f g hg
  obtain ⟨hfin, ht⟩ := v.tateResidue_integralRetraction hres f g
  obtain ⟨hfin', ht'⟩ := v.completionPlace.tateResidue_eq_retraction_trace
    (v.completionPlace_residue_algebraMap_surjective hres)
    (v.completionOriginalRetraction hres) (v.completionOriginalRetraction_apply hres)
    (algebraMap F v.adicCompletion f) (algebraMap F v.adicCompletion g)
    ((v.completion_integer_iff g).mpr hg)
  haveI : FiniteDimensional K (LinearMap.range (B ∘ₗ i)) := hBI.symm ▸ hfin
  haveI : FiniteDimensional K (LinearMap.range (i ∘ₗ B)) := hIB.symm ▸ hfin'
  calc
    _ = finrankTrace (i ∘ₗ B) := ht'.trans (congrArg finrankTrace hIB.symm)
    _ = finrankTrace (B ∘ₗ i) := (finrankTrace_comp_comm i B).symm
    _ = v.tateResidue f g := (congrArg finrankTrace hBI).trans ht.symm

/-- Completion preserves the local Tate residue of every pair of original field elements. -/
theorem completion_tateResidue
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) :
    v.completionPlace.tateResidue
      (algebraMap F v.adicCompletion f) (algebraMap F v.adicCompletion g) =
        v.tateResidue f g := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective v.toValuationSubring g
  change (a : F) / (b : F) = g at hab
  have hb0 : (b : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hgb : g * (b : F) ∈ v.toValuationSubring := by
    rw [← hab, div_mul_cancel₀ _ hb0]
    exact a.2
  let α := algebraMap F v.adicCompletion
  have ho := v.tateResidue_leibniz hres (f / (b : F)) g (b : F)
  rw [div_mul_cancel₀ f hb0] at ho
  have hc := v.completionPlace.tateResidue_leibniz
    (v.completionPlace_residue_algebraMap_surjective hres)
    (α (f / (b : F))) (α g) (α (b : F))
  simp only [← map_mul, div_mul_cancel₀ f hb0] at hc
  have he := v.completion_tateResidue_of_integral hres (f / (b : F)) (g * (b : F)) hgb
  rw [hc, ho, v.completion_tateResidue_of_integral hres _ (b : F) b.2] at he
  exact add_left_cancel he

end Dubon2026.SourceCurve.Place
