import Dubon2026.AlgebraBaseChangePoints
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Faithful original coordinates remain faithful in the generic fiber -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R F A B : Type*} [CommRing R] [CommRing F] [Algebra R F]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra F B]
  [IsScalarTower R F B]

/-- An actual injective coordinate map into a localization-algebra remains injective after base change, by clearing one genuine common denominator. -/
theorem localizedAlgebraPoint_injective (S : Submonoid R) [IsLocalization S F]
    (p : A →ₐ[R] B) (hp : Function.Injective p) :
    Function.Injective (AlgHom.liftEquiv R F A B p) := by
  let f := AlgHom.liftEquiv R F A B p
  have hz (z : F ⊗[R] A) (h : f z = 0) : z = 0 := by
    obtain ⟨⟨a, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (TensorProduct.mk R F A 1) z
    have ha : p a = 0 := by
      calc
        p a = f (1 ⊗ₜ[R] a) := (algebraBaseChangePoint_original p a).symm
        _ = f ((s : R) • z) := congrArg f hs.symm
        _ = (s : R) • f z := (f.toLinearMap.restrictScalars R).map_smul _ _
        _ = 0 := by rw [h, smul_zero]
    have ha0 : a = 0 := hp (ha.trans (map_zero p).symm)
    apply IsLocalizedModule.smul_injective (TensorProduct.mk R F A 1) s
    simpa only [ha0, TensorProduct.mk_apply, TensorProduct.tmul_zero, smul_zero]
      using hs
  intro z w h
  apply sub_eq_zero.mp
  exact hz (z - w) (by rw [map_sub, h, sub_self])

/-- A genuine injection into reduced coordinates proves reducedness of the actual localized algebra. -/
theorem localizedAlgebraPoint_isReduced (S : Submonoid R) [IsLocalization S F]
    [IsReduced B] (p : A →ₐ[R] B) (hp : Function.Injective p) :
    IsReduced (F ⊗[R] A) :=
  isReduced_of_injective (AlgHom.liftEquiv R F A B p)
    (localizedAlgebraPoint_injective S p hp)

end
end Dubon2026
