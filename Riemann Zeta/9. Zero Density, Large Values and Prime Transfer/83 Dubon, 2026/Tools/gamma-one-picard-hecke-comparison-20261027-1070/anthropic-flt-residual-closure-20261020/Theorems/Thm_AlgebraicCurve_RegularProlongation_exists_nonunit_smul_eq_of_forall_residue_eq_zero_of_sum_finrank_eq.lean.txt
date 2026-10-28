import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
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
    (V : Submodule L F) [FiniteDimensional L V]
    (u : F) (huO : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, huO i⟩ = 0) :
    ∃ (a : A) (u' : F), ¬ IsUnit a ∧ (∀ i, u' ∈ (R i).integers) ∧ u' ∈ V ∧
      u = (a : L) • u' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq.solution
