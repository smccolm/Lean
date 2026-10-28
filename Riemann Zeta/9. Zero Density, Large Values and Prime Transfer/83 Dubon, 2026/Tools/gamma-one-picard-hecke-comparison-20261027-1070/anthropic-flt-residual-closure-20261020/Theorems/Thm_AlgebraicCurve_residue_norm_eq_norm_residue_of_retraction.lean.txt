import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction

open AlgebraicCurve
open scoped Polynomial

theorem AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [FiniteDimensional (RatFunc E) FE]
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) :
    ∃ h : algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) ∈ O,
      ρ ⟨_, h⟩ = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction.solution
