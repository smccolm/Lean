import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
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
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F),
        (∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
          (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
          x * aeval f t = aeval f p) →
        (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lp σ * aeval f t = aeval f p) ∧
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lm σ * aeval f⁻¹ t = aeval f⁻¹ p) ∧
          (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq.solution
