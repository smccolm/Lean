import Dubon2026.ArithmeticRealCyclotomicRestriction
import Dubon2026.OriginalRealH2Invariant
import Dubon2026.GaloisUnitCarryBaseChange

/-! # The real invariant of an original arithmetic finite carry

The exact original arithmetic embedding into the complex numbers supplies
the actual coefficient map and Galois restriction. The native carry
base-change theorem and the proved real carry invariant identify its value
with the character of the existing real arithmetic restriction. This is
DUB-17's real contribution to the principal carry/invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois originalRealPeriodQuadratic

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- Retain the literal rational algebra of the original finite stage. -/
abbrev arithmeticFiniteRealRationalAlgebra : Algebra ℚ F := F.toIntermediateField.algebra'

attribute [local instance] arithmeticFiniteRealRationalAlgebra

/-- The real coefficient embedding is the same original arithmetic embedding. -/
local instance arithmeticFiniteRealClosureAlgebra : Algebra F ℂ :=
  ((rationalArithmeticLocalEmbedding (K := ℂ) a).comp F.toIntermediateField.val).toAlgebra

/-- Use the scalar action of the same original real embedding. -/
local instance arithmeticFiniteRealClosureSMul : SMul F ℂ :=
  (arithmeticFiniteRealClosureAlgebra a F).toSMul

/-- The original real embedding preserves its original rational scalars. -/
local instance arithmeticFiniteRealClosureTower : IsScalarTower ℚ F ℂ :=
  IsScalarTower.of_algHom
    ((rationalArithmeticLocalEmbedding (K := ℂ) a).comp F.toIntermediateField.val)

/-- The literal base-change restriction is exactly the existing original
real arithmetic restriction on the same finite global field. -/
theorem rationalArithmeticFiniteRealBaseChangeRestriction :
    galoisBaseChangeRestriction ℚ ℝ F ℂ = rationalRealArithmeticFiniteRestriction a F := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  let j := (rationalArithmeticLocalEmbedding (K := ℂ) a).comp F.toIntermediateField.val
  apply j.injective
  exact (galoisBaseChangeRestriction_commutes ℚ ℝ F ℂ σ x).trans
    (rationalRealArithmeticFiniteRestriction_commutes a F σ x).symm

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

/-- Actual real unit-H2 restriction of the original finite arithmetic
class, using the original embedding and coefficient inclusion. -/
def rationalArithmeticFiniteRealUnitH2 :
    GaloisUnitContinuousH2 (K := ℚ) (Ω := F) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) :=
  finiteGaloisUnitBaseChangeH2 ℚ ℝ F ℂ

/-- The original arithmetic carry has real invariant equal to its finite
character on the actual sign-selected original real restriction. -/
theorem rationalArithmeticFiniteRealCarryInvariant
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n)) (q : ℚˣ) :
    originalRealUnitH2Invariant (rationalArithmeticFiniteRealUnitH2 a F
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ q))) =
      rationalCyclicInvariant n
        (χ (rationalRealArithmeticFiniteRestriction a F
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd := by
  have hcarry := finiteGaloisUnitBaseChangeH2_characterCarry ℚ ℝ F ℂ χ q
  have hlocal := originalRealUnitH2Invariant_characterCarry
    (χ.comp (galoisBaseChangeRestriction ℚ ℝ F ℂ))
    (Units.map (algebraMap ℚ ℝ).toMonoidHom q)
  have hfirst := (congrArg originalRealUnitH2Invariant hcarry).trans hlocal
  have hpos : 0 < (Units.map (algebraMap ℚ ℝ).toMonoidHom q).val ↔ 0 < q.val := by
    change 0 < (q.val : ℝ) ↔ 0 < q.val
    exact Rat.cast_pos
  have hval : galoisBaseChangeRestriction ℚ ℝ F ℂ
      (if 0 < (Units.map (algebraMap ℚ ℝ).toMonoidHom q).val then 1 else Complex.conjAe) =
      rationalRealArithmeticFiniteRestriction a F (if 0 < q.val then 1 else Complex.conjAe) := by
    simp only [hpos, rationalArithmeticFiniteRealBaseChangeRestriction a F]
    rfl
  exact hfirst.trans (congrArg (fun z => rationalCyclicInvariant n (χ z).toAdd) hval)

end
end Dubon2026
