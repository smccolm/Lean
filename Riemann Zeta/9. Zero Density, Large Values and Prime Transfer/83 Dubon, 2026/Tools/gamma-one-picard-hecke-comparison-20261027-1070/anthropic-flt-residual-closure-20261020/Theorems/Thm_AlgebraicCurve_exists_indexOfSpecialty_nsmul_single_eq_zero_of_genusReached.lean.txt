import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached

open AlgebraicCurve

theorem AlgebraicCurve.exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, indexOfSpecialty ((n : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.solution
