import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [DecidableEq W.FunctionField]
    (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)
    (hcol : ¬ (φ₁ (polyToFunctionField W Polynomial.X) = φ₂ (polyToFunctionField W Polynomial.X) ∧
      φ₁ (yCoord W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
        (φ₂ (polyToFunctionField W Polynomial.X)) (φ₂ (yCoord W))))
    (hnc : ∀ c : F,
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ≠ algebraMap F W.FunctionField c)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point)
    (h₁0 : Q₁ = 0 → φ₁ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₁s : ∀ (a b : F) (h : W.Nonsingular a b), Q₁ = .some a b h →
      0 < v.ord (φ₁ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₁ (yCoord W) - algebraMap F W.FunctionField b))
    (h₂0 : Q₂ = 0 → φ₂ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₂s : ∀ (a b : F) (h : W.Nonsingular a b), Q₂ = .some a b h →
      0 < v.ord (φ₂ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₂ (yCoord W) - algebraMap F W.FunctionField b)) :
    (Q₁ + Q₂ = 0 →
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ∉ v.toValuationSubring) ∧
    (∀ (a b : F) (h : W.Nonsingular a b), Q₁ + Q₂ = .some a b h →
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField a) ∧
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addY
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          (φ₁ (yCoord W))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField b)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.solution
