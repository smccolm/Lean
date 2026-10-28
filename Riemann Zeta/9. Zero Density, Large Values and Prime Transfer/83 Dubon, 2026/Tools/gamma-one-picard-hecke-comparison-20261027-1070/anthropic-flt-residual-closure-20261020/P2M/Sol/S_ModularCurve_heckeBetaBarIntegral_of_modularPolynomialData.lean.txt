import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData
import P2M.Util
namespace P2MW.S_ModularCurve_heckeBetaBarIntegral_of_modularPolynomialData
attribute [-simp] ModularCurve.jqNModC_one

open ModularCurve AlgebraicCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hsymm : ModularCurve.EvalSymm data.Φ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : ModularCurve.HeckeBetaBarIntegral L N ℓ := by
  letI : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := (heckeBetaBar L N ℓ).toRingHom.toAlgebra
  letI : Module (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.toModule
  haveI : Module.Finite (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    finiteAlong_heckeBetaBar_of_modularPolynomialData L data hsymm hℓ N
  haveI : Algebra.IsIntegral (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) := Algebra.IsIntegral.of_finite _ _
  exact fun x => Algebra.IsIntegral.isIntegral (R := laurentBaseChange L (modularFunctionFieldFull N)) x
