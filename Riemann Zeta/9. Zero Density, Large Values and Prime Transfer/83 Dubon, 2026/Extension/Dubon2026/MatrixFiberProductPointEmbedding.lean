import Dubon2026.MatrixCoefficientPointActions
import Dubon2026.LocalCoefficientFiberProduct
import Dubon2026.FiniteFreeHopfPointModelProduct

/-! # The actual compatible coefficient-vector group embeds in its original two factors -/

namespace Dubon2026
noncomputable section
open Matrix

variable {F K ι A B C : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C]

omit [Fintype ι] [DecidableEq ι] in
/-- The literal original vector group over the genuine compatible-pair coefficient ring maps to the two original vector groups through its actual coordinate projections. -/
def matrixFiberProductVectorMap (f : A →+* C) (g : B →+* C) :
    Multiplicative (ι → CoefficientFiberProduct f g) →*
      Multiplicative (ι → A) × Multiplicative (ι → B) :=
  (matrixCoefficientVectorMap (coefficientFiberProductFst f g)).prod
    (matrixCoefficientVectorMap (coefficientFiberProductSnd f g))

omit [Fintype ι] [DecidableEq ι] in
/-- Equality of both original projected coordinate vectors determines every original compatible coefficient and hence the entire original vector. -/
theorem matrixFiberProductVectorMap_injective (f : A →+* C) (g : B →+* C) :
    Function.Injective (matrixFiberProductVectorMap (ι := ι) f g) := by
  intro v w h
  change Multiplicative.toAdd v = Multiplicative.toAdd w
  funext i
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun x : Multiplicative (ι → A) × Multiplicative (ι → B) =>
      Multiplicative.toAdd x.1 i) h)
    (congrArg (fun x : Multiplicative (ι → A) × Multiplicative (ι → B) =>
      Multiplicative.toAdd x.2 i) h)

/-- The original representation over the actual coefficient fiber product embeds equivariantly into the product of its two original projected actions. Both components use the exact original coefficient-change matrix-vector identity. -/
theorem matrixFiberProductVectorMap_equivariant (f : A →+* C) (g : B →+* C)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (s : K ≃ₐ[F] K) (v : Multiplicative (ι → CoefficientFiberProduct f g)) :
    matrixFiberProductVectorMap f g (matrixUnderlyingGroupAction ρ s v) =
      galoisModuleProductAction
        (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
          (coefficientFiberProductFst f g)).comp ρ))
        (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
          (coefficientFiberProductSnd f g)).comp ρ)) s
        (matrixFiberProductVectorMap f g v) := by
  apply Prod.ext
  · exact matrixCoefficientVectorMap_equivariant (coefficientFiberProductFst f g) ρ s v
  · exact matrixCoefficientVectorMap_equivariant (coefficientFiberProductSnd f g) ρ s v

end
end Dubon2026
