import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne

open AlgebraicCurve

theorem AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (hRR : FunctionFieldRiemannRoch K F) {P Q : Place K F} (hPQ : P ≠ Q) :
    ∃ ω : Ω[F⁄K], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place K F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne.solution
