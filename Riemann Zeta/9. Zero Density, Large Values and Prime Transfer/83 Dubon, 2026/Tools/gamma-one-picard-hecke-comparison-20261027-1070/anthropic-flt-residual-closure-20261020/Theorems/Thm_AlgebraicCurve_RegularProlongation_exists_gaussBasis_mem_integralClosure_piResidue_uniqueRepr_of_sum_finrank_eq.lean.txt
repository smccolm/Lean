import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ : ι)
    (hcomplete : ∀ W : ValuationSubring F,
      (∀ e ∈ IntermediateField.adjoin L ({f} : Set F), e ∈ W ↔ e ∈ (R i₀).integers) →
      ∃ j, W = (R j).integers)
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (d' : ℕ) (z : Fin d' → F) (hzO : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ q q' : Fin d' → Polynomial (IsLocalRing.ResidueField A),
        (∀ i, ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q σ)
            * (R i).residue ⟨z σ, hzO σ i⟩
          = ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' σ)
            * (R i).residue ⟨z σ, hzO σ i⟩) →
        q = q') ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ c : Fin d' → IntermediateField.adjoin L ({f} : Set F),
          (∀ σ, (c σ : F) ∈ (R i₀).integers) ∧ b = ∑ σ, (c σ : F) * z σ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.solution
