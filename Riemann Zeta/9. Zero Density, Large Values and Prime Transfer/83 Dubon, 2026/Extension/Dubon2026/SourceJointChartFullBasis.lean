import Dubon2026.SourceJointChartBasisDegree

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap. The
lifted polynomial residue basis has exactly the original coordinate-field
degree: residue monic multiples give the lower bound and joint residue
independence gives the upper bound. This is the finite chart basis needed
for integral coordinate representations and overlap generators. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem exists_full_lifted_residue_polynomial_basis
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
    [∀ i, Algebra.IsSeparable (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (d : ℕ) (z : Fin d → F) (hz : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, z σ ∈ originalChart (L := L) f) ∧
      (∀ q q' : Fin d → (ResidueField A)[X],
        ∑ σ, aeval (rv R f hf) (q σ) * rv R (z σ) (hz σ) =
          ∑ σ, aeval (rv R f hf) (q' σ) * rv R (z σ) (hz σ) → q = q') ∧
      (∀ h ∈ ST R f, ∃ q : Fin d → (ResidueField A)[X],
        h = ∑ σ, aeval (rv R f hf) (q σ) * rv R (z σ) (hz σ)) ∧
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F = d := by
  obtain ⟨d, z, hz, hchart, huniq, hgen, hcard⟩ :=
    exists_lifted_residue_polynomial_basis A Fb R hR f hf htr heq
  refine ⟨d, z, hz, hchart, huniq, hgen, Nat.le_antisymm ?_ ?_⟩
  · exact coordinate_finrank_le_chart_rank A Fb R hR f hf htr heq hcard
  · simpa only [Fintype.card_fin] using
      (linearIndependent_lifted_chart_basis R f hf z hz huniq).fintype_card_le_finrank

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
