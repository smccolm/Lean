import Dubon2026.SourceJointChartFullBasis
import Dubon2026.SourceJointChartGoodDenominators
import Dubon2026.SourceJointChartFiniteOverlap

/-! DUB-17/18 -> original Gamma1 Picard torsion injectivity -> Kummer
power lifting -> residue genus inequality -> common constants on the two
joint charts. Compose the native full residue basis, integral coordinates,
good denominators and finite Laurent overlap proofs directly. This avoids
recreating the separate Gamma0-specific basis wrappers for Gamma1. Finite
separating residue coordinates and total degree equality are precisely the
inputs supplied by the Gamma1 Kummer reduction family. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem finite_overlap_of_separating_residue_coordinates
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
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
    ∃ hfi : ∀ i, f⁻¹ ∈ (R i).integers, Module.Finite A (overlapQuotient R f hf hfi) := by
  classical
  obtain ⟨d, z, hz, hchart, huniq, hgen, hd⟩ :=
    exists_full_lifted_residue_polynomial_basis A Fb R hR f hf htr heq
  have hr0 : ∀ i, (R i).residue ⟨f, hf i⟩ ≠ 0 :=
    fun i h => htr i (h ▸ isAlgebraic_zero)
  have hfi : ∀ i, f⁻¹ ∈ (R i).integers := inv_mem_integers hr0
  let i₀ : ι := Classical.choice inferInstance
  have htrL : Transcendental L f :=
    transcendental_of_residue_transcendental (R i₀) ⟨f, hf i₀⟩ (htr i₀)
  have hgood : ∀ s ∈ Sg R f, ∃ (t : L[X]) (p : Fin d → L[X]), IsGood A t ∧
      (∀ j k, (p j).coeff k ∈ A) ∧ s * aeval f t = ∑ j, aeval f (p j) * z j := by
    intro s hs
    obtain ⟨w, hw, hsum⟩ := exists_integral_coords_of_full_chart_basis R f hf htr z hz huniq hd s hs.1
    obtain ⟨t, p, ht, hp, he⟩ :=
      exists_good_coordinate_denominator R f hf htr z hz hchart huniq hgen s hs.2 w hw hsum
    refine ⟨t, p, ht, hp, ?_⟩
    rw [hsum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_right_comm, he j]
  exact ⟨hfi, finite_overlap_of_good_basis R f hf hfi htrL z (fun j => ⟨hz j, hchart j⟩) hgood⟩

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
