import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F))
      (h : F) = 0)
    (w : Place (IsLocalRing.ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.solution
