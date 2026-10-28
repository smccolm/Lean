import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (htr₁ : Transcendental (IsLocalRing.ResidueField A) (R₁.residue ⟨f, hf₁⟩))
    (htr₂ : Transcendental (IsLocalRing.ResidueField A) (R₂.residue ⟨f, hf₂⟩))
    (e : F) (he : e ∈ IntermediateField.adjoin L ({f} : Set F)) :
    e ∈ R₁.integers ↔ e ∈ R₂.integers := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue.solution
