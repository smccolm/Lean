import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

open AlgebraicCurve ModularCurve
theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.solution
