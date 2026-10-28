import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hfO : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfO⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (W : ValuationSubring F)
    (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers)) :
    ∃ (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R' : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R'.integers = W ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hf'⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.solution
