import Dubon2026.ArithmeticFiniteRealCarryInvariant
import Dubon2026.ArithmeticFiniteCarryInvariant

/-! # Real restriction of original arithmetic finite inflation

The original arithmetic embedding defines the real unit-H2 map. The native
continuous base-change composition theorem compares it with the actual
finite-stage real map on the same inflated class. This supplies the real
compatibility required for DUB-17's global principal carry/invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower

attribute [local instance] arithmeticKummerStageAlgebra
  arithmeticKummerStageGalois arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete
  arithmeticFiniteLocalStageGalois originalRealPeriodQuadratic

variable (a : 𝓞 ℚ)

/-- The global real coefficient map uses the existing arithmetic embedding. -/
local instance arithmeticRealGlobalClosureAlgebra :
    Algebra (rationalUnramifiedExtension a) ℂ :=
  (rationalArithmeticLocalEmbedding (K := ℂ) a).toAlgebra

/-- Retain the scalar action of the same original global real embedding. -/
local instance arithmeticRealGlobalClosureSMul : SMul (rationalUnramifiedExtension a) ℂ :=
  (arithmeticRealGlobalClosureAlgebra a).toSMul

/-- The original global real embedding preserves rational scalars. -/
local instance arithmeticRealGlobalClosureTower : IsScalarTower ℚ (rationalUnramifiedExtension a) ℂ :=
  IsScalarTower.of_algHom (rationalArithmeticLocalEmbedding (K := ℂ) a)

/-- The base-change Galois map is exactly the existing original real arithmetic restriction. -/
theorem rationalArithmeticRealBaseChangeRestriction :
    galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ =
      (rationalRealArithmeticRestriction a).toMonoidHom := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply (rationalArithmeticLocalEmbedding (K := ℂ) a).injective
  exact (galoisBaseChangeRestriction_commutes ℚ ℝ (rationalUnramifiedExtension a) ℂ σ x).trans
    (rationalArithmeticLocalRestrictionContinuous_commutes (F := ℝ) (K := ℂ) a σ x).symm

variable [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
    [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

/-- Original global unit H2 restricts to the real place through the same
actual arithmetic embedding and original real Galois restriction. -/
def rationalArithmeticRealUnitH2Restriction :
    ContinuousRepresentationH2 (rationalArithmeticUnitRepresentation a)
      (rationalArithmeticUnitAction_continuous a) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) :=
  continuousGaloisUnitBaseChangeH2 ℚ ℝ (rationalUnramifiedExtension a) ℂ

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

attribute [local instance] arithmeticFiniteCarryGlobalAlgebra arithmeticFiniteCarryUnionSMul
  arithmeticFiniteCarryTopology arithmeticFiniteCarryDiscrete

attribute [local instance] arithmeticFiniteRealClosureAlgebra arithmeticFiniteRealClosureSMul
  arithmeticFiniteRealClosureTower

/-- The finite embedding and global original real embedding have the same value. -/
local instance arithmeticFiniteRealUnionTower : IsScalarTower F (rationalUnramifiedExtension a) ℂ :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Real restriction of the original finite inflation is precisely the
actual finite-stage real unit-H2 map, on the same original class. -/
theorem rationalArithmeticRealUnitH2Restriction_finiteStage
    (x : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) F) :
    rationalArithmeticRealUnitH2Restriction a (galoisUnitFiniteStageH2Inflation F x) =
      @rationalArithmeticFiniteRealUnitH2 a F (arithmeticFiniteCarryTopology a F)
        (arithmeticFiniteCarryDiscrete a F) _ _ x := by
  have h := continuousGaloisUnitBaseChangeH2_eq_finiteStage ℚ (rationalUnramifiedExtension a) F x
  have hcomp := continuousGaloisUnitBaseChangeH2_comp ℚ ℚ ℝ F (rationalUnramifiedExtension a) ℂ x
  have hfirst := (congrArg (continuousGaloisUnitBaseChangeH2 ℚ ℝ
    (rationalUnramifiedExtension a) ℂ) h.symm).trans hcomp
  exact hfirst.trans (congrArg (fun f => f x) (continuousGaloisUnitBaseChangeH2_eq_finite ℚ ℝ F ℂ))

/-- The original inflated arithmetic carry has the already proved real
invariant formula through the actual real arithmetic restriction. -/
theorem rationalArithmeticRealInflatedCarryInvariant
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (q : ℚˣ) :
    originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a
      (galoisUnitFiniteStageH2Inflation F
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q)))) =
      rationalCyclicInvariant n
        (χ (rationalRealArithmeticFiniteRestriction a F
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd := by
  exact (congrArg originalRealUnitH2Invariant
    (rationalArithmeticRealUnitH2Restriction_finiteStage a F _)).trans
      (@rationalArithmeticFiniteRealCarryInvariant a F
        (arithmeticFiniteCarryTopology a F) (arithmeticFiniteCarryDiscrete a F) _ _ n _ χ q)

end
end Dubon2026
