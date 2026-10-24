import Dubon2026.SourceJointChartResidueAlgebras
import Dubon2026.SourceJointReductionIntegralChartImage
import Dubon2026.SourceJointChartGlobalConstants
import Dubon2026.SourceCurveTranscendentalDegree
import Dubon2026.SourceValuationResidueAlgClosed

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
Joint chart integrality makes each component of a vector in both residue
charts constant. Valuations contain either the coordinate or its inverse,
so the existing global-constant criterion applies. Equality of these
component constants remains the separate idempotent-gluing obligation. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

variable {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
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

include hR htr heq in
theorem residue_chart_isIntegral (h : ∀ i, Fb i) (hh : h ∈ JointChartAssembly.ST R f) (i : ι) :
    IsIntegral (Algebra.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
      (h i) := by
  obtain ⟨u, hu, hr⟩ := (mem_residue_chart_iff R f h).mp hh
  rw [← hr i]
  exact Joint.isIntegral_residue_of_joint_integral_chart A Fb R hR f hf htr heq u hu.1 hu.2 i

include hR htr heq in
theorem exists_component_constants [IsAlgClosed L] (h : ∀ i, Fb i)
    (hh : h ∈ JointChartAssembly.ST R f) (hhi : h ∈ JointChartAssembly.ST R f⁻¹) :
    ∀ i, ∃ c : ResidueField A, h i = algebraMap (ResidueField A) (Fb i) c := by
  haveI := Dubon2026.SourceEllipticReduction.residueField_isAlgClosed A
  have hne : ∀ i, (R i).residue ⟨f, hf i⟩ ≠ 0 :=
    fun i => JointChartAssembly.ne_zero_of_transcendental (htr i)
  have hfi := JointChartAssembly.inv_mem_integers hne
  have hri : ∀ i, (R i).residue ⟨f⁻¹, hfi i⟩ = ((R i).residue ⟨f, hf i⟩)⁻¹ :=
    JointChartAssembly.residue_inv hne
  have htri : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f⁻¹, hfi i⟩) :=
    fun i => by rw [hri i]; exact JointChartAssembly.transcendental_inv (htr i)
  letI : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  letI (i : ι) : FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f⁻¹, hfi i⟩} : Set (Fb i))) (Fb i) := by
    rw [hri i, adjoin_singleton_inv_eq]
    infer_instance
  have heqi : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f⁻¹, hfi i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq, ← heq]
    exact Finset.sum_congr rfl fun i _ => by rw [hri i, adjoin_singleton_inv_eq]
  intro i
  apply exists_eq_algebraMap_of_forall_mem
  intro V hV
  rcases V.mem_or_inv_mem ((R i).residue ⟨f, hf i⟩) with hv | hv
  · exact Joint.mem_valuation_of_integral_chart
      (residue_chart_isIntegral A Fb R hR f hf htr heq h hh i) V hV hv
  · exact Joint.mem_valuation_of_integral_chart
      (residue_chart_isIntegral A Fb R hR f⁻¹ hfi htri heqi h hhi i) V hV (by rwa [hri i])

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
