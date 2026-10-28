import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_comap_eq_toValuationSubring {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) : ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.solution
