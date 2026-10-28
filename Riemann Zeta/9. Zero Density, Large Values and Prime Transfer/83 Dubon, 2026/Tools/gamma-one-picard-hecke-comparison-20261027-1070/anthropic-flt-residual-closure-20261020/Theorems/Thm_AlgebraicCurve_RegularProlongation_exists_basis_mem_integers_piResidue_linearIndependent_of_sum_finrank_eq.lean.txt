import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
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
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ w : Fin (Module.finrank L V) → F, ∃ hwO : ∀ a i, w a ∈ (R i).integers,
      (∀ a, w a ∈ V) ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun a => fun i => (R i).residue ⟨w a, hwO a i⟩) ∧
      (∀ u : F, (∀ i, u ∈ (R i).integers) → u ∈ V →
        ∃ c : Fin (Module.finrank L V) → A, u = ∑ a, (c a : L) • w a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq.solution
