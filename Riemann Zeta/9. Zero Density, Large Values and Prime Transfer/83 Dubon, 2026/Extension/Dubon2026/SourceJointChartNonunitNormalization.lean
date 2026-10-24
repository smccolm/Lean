import Dubon2026.SourceJointChartIntegralAlgebras
import Dubon2026.SourceJointReductionNonunitFactor

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
The proved one-dimensional normalization applies directly to the original
chart's underlying linear subspace. No finite-generation assumption on that
entire chart is needed to divide a function with zero joint residue by a
coefficient nonunit while staying in the same chart. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem exists_nonunit_factor_in_chart
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
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (g u : F) (hu : u ∈ Sg R g)
    (hzero : ∀ i, (R i).residue ⟨u, hu.1 i⟩ = 0) :
    ∃ (a : A), a ∈ maximalIdeal A ∧ ∃ z ∈ Sg R g, u = (a : L) • z := by
  obtain ⟨a, z, ha, hz, hzc, he⟩ := Joint.exists_nonunit_smul_joint_integral
    A Fb R hR f hf htr heq (originalChart L g).toSubmodule u hu.1 hu.2 hzero
  refine ⟨a, ?_, z, ⟨hz, hzc⟩, he⟩
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ha

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
