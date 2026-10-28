import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_heckeAlphaBar

open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (σ : L ≃ₐ[ℚ] L) (x : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N)) : ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull (N * ℓ)) σ • (ModularCurve.heckeAlphaBar L N ℓ x) = ModularCurve.heckeAlphaBar L N ℓ (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull N) σ • x) :=
  Subtype.ext <|
    (coe_arithmeticGalois_smul (modularFunctionFieldFull (N * ℓ)) σ
        (heckeAlphaBar L N ℓ x)).trans <|
      ((congrArg (coeffMap (σ : L →+* L)) (coe_heckeAlphaBar N ℓ x)).trans
        ((coe_arithmeticGalois_smul (modularFunctionFieldFull N) σ x).symm.trans
          (coe_heckeAlphaBar N ℓ
            (arithmeticGalois (modularFunctionFieldFull N) σ • x)).symm))
