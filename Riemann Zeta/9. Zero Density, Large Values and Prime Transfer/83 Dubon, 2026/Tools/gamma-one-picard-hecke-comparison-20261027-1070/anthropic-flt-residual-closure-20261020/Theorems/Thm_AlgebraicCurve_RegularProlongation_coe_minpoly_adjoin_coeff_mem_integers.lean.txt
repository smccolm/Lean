import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) f)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V)
    (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers.solution
