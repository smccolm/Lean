import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i : ι) :
    FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq.solution
