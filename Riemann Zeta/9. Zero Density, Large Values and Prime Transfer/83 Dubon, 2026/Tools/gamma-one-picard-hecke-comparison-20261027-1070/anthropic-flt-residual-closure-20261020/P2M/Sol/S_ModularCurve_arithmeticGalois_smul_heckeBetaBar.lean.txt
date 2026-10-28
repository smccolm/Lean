import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_heckeBetaBar

open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L) (x : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N)) : ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull (N * ℓ)) σ • (ModularCurve.heckeBetaBar L N ℓ x) = ModularCurve.heckeBetaBar L N ℓ (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull N) σ • x) :=
  Subtype.ext <| by
    show coeffMap (σ : L →+* L) (qExpand L ℓ (x : LaurentSeries L))
      = qExpand L ℓ (coeffMap (σ : L →+* L) (x : LaurentSeries L))
    exact coeffMap_qExpand (σ : L →+* L) ℓ (x : LaurentSeries L)
