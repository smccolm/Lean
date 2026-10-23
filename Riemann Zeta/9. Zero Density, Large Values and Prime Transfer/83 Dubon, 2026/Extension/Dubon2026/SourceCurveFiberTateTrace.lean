import Dubon2026.SourceCurveFiberCompletionTrace
import Dubon2026.SourceCurveCompletionTraceUniformizer
import Dubon2026.SourceCurveLocalTateDerivation

/-! Sum the proved local completed field-trace identity over an actual
restriction fiber. The product decomposition supplies the sum of traces,
and the proved completion comparison returns the original base residue.
This is the local-to-global residue input for DUB-17/18 canonical degree. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (v : Place K F)

/-- For an integral base argument, the sum of original residues is the residue of the field trace. -/
theorem tateResidue_trace_fiber_of_integral
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (f : E) (g : F) (hg : g ∈ v.toValuationSubring) :
    v.tateResidue (Algebra.trace F E f) g =
      ∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.tateResidue f (algebraMap F E g) := by
  classical
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  rw [← v.completion_tateResidue hbase.surjective, v.completionTraceSum hbase htop]
  simp only [finsum_eq_sum_of_fintype]
  let φ := residueDualLinearMap K v.adicCompletion
    (v.completionPlace.tateResidueFunctional
      (v.completionPlace_residue_algebraMap_surjective hbase.surjective)
      (algebraMap F v.adicCompletion g))
  change φ (∑ w : {w : Place K E // w.restrict F = v},
      Algebra.trace v.adicCompletion w.1.adicCompletion
        (algebraMap E w.1.adicCompletion f)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  change v.completionPlace.tateResidue
    (Algebra.trace v.adicCompletion w.1.adicCompletion (algebraMap E w.1.adicCompletion f))
    (algebraMap F v.adicCompletion g) = _
  rcases w with ⟨w, hw⟩
  subst v
  exact (w.tateResidue_completion_fieldTrace (htop w).surjective f g hg).symm

/-- Fraction-field representation and Leibniz remove the integral base-argument restriction. -/
theorem tateResidue_trace_fiber
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (f : E) (g : F) :
    v.tateResidue (Algebra.trace F E f) g =
      ∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.tateResidue f (algebraMap F E g) := by
  classical
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective v.toValuationSubring g
  change (a : F) / (b : F) = g at hab
  have hb0 : (b : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hgb : g * (b : F) ∈ v.toValuationSubring := by
    rw [← hab, div_mul_cancel₀ _ hb0]
    exact a.2
  let α := algebraMap F E
  let f' := f / α (b : F)
  have hf : f' * α (b : F) = f :=
    div_mul_cancel₀ f ((map_ne_zero α).mpr hb0)
  have htrace (x : E) (c : F) :
      Algebra.trace F E (x * α c) = Algebra.trace F E x * c := by
    rw [mul_comm x, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have ht : Algebra.trace F E f' * (b : F) = Algebra.trace F E f := by
    rw [← htrace, hf]
  have he := v.tateResidue_trace_fiber_of_integral hbase htop f' (g * (b : F)) hgb
  rw [v.tateResidue_leibniz hbase.surjective, ht] at he
  have hbtrace := v.tateResidue_trace_fiber_of_integral hbase htop (f' * α g) (b : F) b.2
  rw [htrace] at hbtrace
  rw [hbtrace] at he
  simp only [finsum_eq_sum_of_fintype] at he ⊢
  have hsum : (∑ w : {w : Place K E // w.restrict F = v},
        w.1.tateResidue f' (algebraMap F E (g * (b : F)))) =
      (∑ w : {w : Place K E // w.restrict F = v},
        w.1.tateResidue (f' * α g) (α (b : F))) +
      ∑ w : {w : Place K E // w.restrict F = v}, w.1.tateResidue f (α g) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    change w.1.tateResidue f' (α (g * (b : F))) = _
    rw [map_mul, w.1.tateResidue_leibniz (htop w.1).surjective, hf]
  rw [hsum] at he
  exact add_left_cancel he

end Dubon2026.SourceCurve.Place
