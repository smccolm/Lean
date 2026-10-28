import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (f u : R.integers)
    (hu : ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (u : F) = 0) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue f}) (R.residue u) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero.solution
