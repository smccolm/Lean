import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
          (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            w σ * aeval f q = aeval f p) ∧
          b = ∑ σ, w σ * z σ) ∧
      (∀ (y : F) (w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
        (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          w σ * aeval f q = aeval f p) →
        y = ∑ σ, w σ * z σ →
        ∃ (C₁ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → L[X])
          (μ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
          (∀ σ j, (C₁ σ).coeff j ∈ A) ∧
          (∀ σ, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            μ σ * aeval f q = aeval f p) ∧
          y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq.solution
