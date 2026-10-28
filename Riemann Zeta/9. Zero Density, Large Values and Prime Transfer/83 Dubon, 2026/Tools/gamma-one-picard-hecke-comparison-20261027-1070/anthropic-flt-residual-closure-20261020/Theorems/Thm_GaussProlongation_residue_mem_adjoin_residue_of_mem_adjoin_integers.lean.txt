import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers

open AlgebraicCurve

theorem GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ i : ι) (w : IntermediateField.adjoin L ({f} : Set F)) (hw : (w : F) ∈ (R i₀).integers)
    (hwi : (w : F) ∈ (R i).integers) :
    (R i).residue ⟨(w : F), hwi⟩ ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by p2m_exact_reverting @_root_.P2MW.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers.solution
