import Dubon2026.ArithmeticRealCorestrictionOrbits
import Dubon2026.OriginalInfiniteEmbeddingH2Comparison
import Dubon2026.ArithmeticRelativeStageCocycles

/-! # The actual real Mackey orbit on the original finite stage

The coset representative twists the specified arithmetic complex embedding.
Its field square is derived from literal conjugation and genuine normal
restriction. Thus original infinite localization controls the same orbit,
without a supplied compatibility certificate. This serves DUB-17's
full-idele principal-kernel and same-stage class-generator obligation.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticRealGlobalClosureAlgebra arithmeticRealGlobalClosureSMul arithmeticRealGlobalClosureTower

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup)

/-- The actual real Mackey stabilizer, with the original restriction and coset. -/
abbrev ArithmeticRealOrbitStabilizer :=
  cosetOrbitStabilizer (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
    F.fixingSubgroup c

/-- The literal coset-twisted complex embedding of the same arithmetic union. -/
def rationalArithmeticRealOrbitEmbedding : rationalUnramifiedExtension a →+* ℂ :=
  (rationalArithmeticLocalEmbedding (K := ℂ) a).toRingHom.comp c.out.toRingHom

/-- The actual stabilizer acts on the original upper field over F by its
literal Mackey conjugation. -/
def rationalArithmeticRealOrbitFieldAction :
    ArithmeticRealOrbitStabilizer a F c →* Gal(rationalUnramifiedExtension a/F) :=
  F.fixingSubgroupEquiv.toMonoidHom.comp
    (cosetOrbitSubgroupMap (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup c)

/-- The original real orbit embedding intertwines the actual field action. -/
theorem rationalArithmeticRealOrbitEmbedding_equivariant
    (d : ArithmeticRealOrbitStabilizer a F c) (x : rationalUnramifiedExtension a) :
    rationalArithmeticRealOrbitEmbedding a F c (rationalArithmeticRealOrbitFieldAction a F c d x) =
      d.val (rationalArithmeticRealOrbitEmbedding a F c x) := by
  have hf := cosetOrbitSubgroupMap_factor
    (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup c d
  have he := congrArg (fun g : Gal(rationalUnramifiedExtension a/ℚ) => g x) hf
  change c.out (rationalArithmeticRealOrbitFieldAction a F c d x) =
    galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ d.val (c.out x) at he
  change rationalArithmeticLocalEmbedding (K := ℂ) a
    (c.out (rationalArithmeticRealOrbitFieldAction a F c d x)) =
      d.val (rationalArithmeticLocalEmbedding (K := ℂ) a (c.out x))
  rw [he]
  exact galoisBaseChangeRestriction_commutes ℚ ℝ (rationalUnramifiedExtension a) ℂ d.val (c.out x)

variable (H : IntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H)

variable [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  IsGalois F H]

/-- Restrict the actual real orbit action to the same original finite stage. -/
def rationalArithmeticRealOrbitFiniteRestriction :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ArithmeticRealOrbitStabilizer a F c →* Gal(H/F) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsGalois F H := hGal
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  exact (galoisBaseChangeRestriction F F H (rationalUnramifiedExtension a)).comp
    (rationalArithmeticRealOrbitFieldAction a F c)

/-- The orbit uses the literal restriction of its original complex embedding. -/
def rationalArithmeticRealOrbitFiniteEmbedding : H →+* ℂ :=
  (rationalArithmeticRealOrbitEmbedding a F c).comp H.val.toRingHom

/-- Genuine normal restriction derives the finite-stage field square
needed by the original infinite-completion comparison. -/
theorem rationalArithmeticRealOrbitFiniteEmbedding_equivariant
    (d : ArithmeticRealOrbitStabilizer a F c) (x : H) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    rationalArithmeticRealOrbitFiniteEmbedding a F c H
      (rationalArithmeticRealOrbitFiniteRestriction a F c H hFH d x) =
        d.val (rationalArithmeticRealOrbitFiniteEmbedding a F c H x) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsGalois F H := hGal
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  have he := galoisBaseChangeRestriction_commutes F F H (rationalUnramifiedExtension a)
    (rationalArithmeticRealOrbitFieldAction a F c d) x
  change rationalArithmeticRealOrbitEmbedding a F c
    (algebraMap H (rationalUnramifiedExtension a)
      (galoisBaseChangeRestriction F F H (rationalUnramifiedExtension a)
        (rationalArithmeticRealOrbitFieldAction a F c d) x)) = _
  rw [he]
  exact rationalArithmeticRealOrbitEmbedding_equivariant a F c d x.val

end
end Dubon2026
