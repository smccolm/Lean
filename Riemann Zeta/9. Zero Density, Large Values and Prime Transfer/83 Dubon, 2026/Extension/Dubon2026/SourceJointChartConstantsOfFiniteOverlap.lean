import Dubon2026.SourceJointChartIdempotentConstants
import Dubon2026.SourceJointChartComponentConstants
import Dubon2026.SourceJointChartIndicators

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
All common-chart constants are equal once the actual localized overlap
quotient is finite over the coefficient valuation ring. Componentwise
constancy and interpolation are proved here; the sole additional upstream
input is the explicitly displayed finite-generation instance. Its proof
remains required before the Kummer genus inequality can be concluded. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem common_constants_of_finite_overlap
    {L F : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [Ring.KrullDimLE 1 A] [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hfi : ∀ i, f⁻¹ ∈ (R i).integers)
    [Module.Finite A (overlapQuotient R f hf hfi)]
    (h : ∀ i, Fb i) (hh : h ∈ JointChartAssembly.ST R f)
    (hhi : h ∈ JointChartAssembly.ST R f⁻¹) :
    ∃ c : ResidueField A, ∀ i, h i = algebraMap (ResidueField A) (Fb i) c := by
  classical
  choose cv hcv using
    (exists_component_constants A Fb R hR f hf htr heq h hh hhi)
  by_cases hi : Nonempty ι
  swap
  · exact ⟨0, fun i => (hi ⟨i⟩).elim⟩
  obtain ⟨i₀⟩ := hi
  let B := residueChartAlgebra R f ⊓ residueChartAlgebra R f⁻¹
  have hB : h ∈ B := by
    constructor
    · change h ∈ (residueChartAlgebra R f).toSubmodule
      rwa [residueChartAlgebra_toSubmodule]
    · change h ∈ (residueChartAlgebra R f⁻¹).toSubmodule
      rwa [residueChartAlgebra_toSubmodule]
  obtain ⟨e, he, h01, he0, hecv⟩ := exists_indicator B.toSubmodule
    (fun _ hx _ hy => B.mul_mem hx hy) (fun c => B.algebraMap_mem c) h hB cv hcv i₀
  have hef : e ∈ JointChartAssembly.ST R f := by
    rw [← residueChartAlgebra_toSubmodule]
    exact he.1
  have hei : e ∈ JointChartAssembly.ST R f⁻¹ := by
    rw [← residueChartAlgebra_toSubmodule]
    exact he.2
  have hall := forall_eq_one_of_idempotent_of_finite_overlap R hR f hf htrL htr heq
    hfi e hef hei h01 he0
  exact ⟨cv i₀, fun i => by rw [hcv i, hecv i (hall i)]⟩

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
