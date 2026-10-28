import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap

open AlgebraicCurve

universe u
theorem WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ι : E.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    ∃ (K₀ : IntermediateField ℚ K), Countable K₀ ∧
      ∃ (E₀ : WeierstrassCurve K₀), E₀.IsElliptic ∧ E₀.map (algebraMap K₀ K) = E ∧
        ∃ (ι₀ : (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
            (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField),
          ι₀.toRingHom.IsIntegral ∧
          ∃ (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
            finrankAlong (AlgebraicClosure K₀) ι₀ = finrankAlong K ι := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.solution
