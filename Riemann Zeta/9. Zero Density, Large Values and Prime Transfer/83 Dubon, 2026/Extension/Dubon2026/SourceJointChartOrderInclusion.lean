import Dubon2026.SourceJointChartResidueSpans
import Dubon2026.SourceJointChartWindows
import Dubon2026.SourceJointReductionIntegralChartImage
import Dubon2026.SourceValuationIntegralCriterion

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> chart dimensions.
Joint coordinate integrality proves that the original chart's residue span
lies in the actual residue order chart. This discharges chart inclusion
without classifying arbitrary valuation extensions. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open IsLocalRing

theorem residue_chart_le_order_chart
    {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ST R f ≤ Bsub (k := ResidueField A) (rv R f hf) := by
  rw [ST, Submodule.span_le]
  rintro h ⟨u, hu, hV, hres⟩ i w hw
  have hint : IsIntegral (Algebra.adjoin L ({f} : Set F)) u := by
    apply ConstantField.isIntegral_of_forall_mem_valuationSubring
    intro V hA
    apply hV V (fun a => hA (algebraMap L (Algebra.adjoin L ({f} : Set F)) a))
    exact hA ⟨f, Algebra.self_mem_adjoin_singleton L f⟩
  have hr := Joint.isIntegral_residue_of_joint_integral_chart A Fb R hR f hf htr heq u hu hint i
  rw [← hres i]
  apply w.ord_nonneg_of_mem
  exact Joint.mem_valuation_of_integral_chart hr w.toValuationSubring
    w.algebraMap_mem' (w.mem_of_ord_nonneg hw)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
