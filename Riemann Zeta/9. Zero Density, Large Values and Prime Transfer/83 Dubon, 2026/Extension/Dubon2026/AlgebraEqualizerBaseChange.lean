import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Literal coordinate equalizers commute with actual flat scalar extension -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The range of the actual scalar-extended coordinate equalizer is precisely the equalizer of the actual scalar-extended maps. This is the pinned flat linear-equalizer theorem applied to the same underlying coordinate maps. -/
theorem algebraEqualizerBaseChange_range (f g : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (AlgHom.id S S) (AlgHom.equalizer f g).val).range =
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S S) f)
        (Algebra.TensorProduct.map (AlgHom.id S S) g) := by
  apply Subalgebra.toSubmodule_injective
  change LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor S S
      (LinearMap.eqLocus f.toLinearMap g.toLinearMap).subtype) =
    LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap)
      (TensorProduct.AlgebraTensorModule.lTensor S S g.toLinearMap)
  exact (Module.Flat.eqLocus_lTensor_eq S S f.toLinearMap g.toLinearMap).symm

/-- The same genuine scalar-extended equalizer inclusion is injective, by flatness of the actual scalar extension. -/
theorem algebraEqualizerBaseChange_injective (f g : A →ₐ[R] B) :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id S S) (AlgHom.equalizer f g).val) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (AlgHom.equalizer f g).val.toLinearMap Subtype.val_injective

end
end Dubon2026
