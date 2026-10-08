import Dubon2026.AdelicComplexSl2Action
import Dubon2026.ComplexSl2EnvelopingCasimir

/-! # The actual central enveloping-algebra Casimir acts by the original Hilbert operator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem commuting_end_eigen {W : Type*} [AddCommGroup W] [Module ℂ W]
    (C T : Module.End ℂ W) (v : W) (a : ℂ) (hCT : Commute C T) (hv : C v = a • v) :
    C (T v) = a • T v := by
  calc
    C (T v) = T (C v) := congrArg (fun S : Module.End ℂ W => S v) hCT.eq
    _ = T (a • v) := congrArg T hv
    _ = a • T v := T.map_smul a v

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine universal enveloping algebra acts on the original smooth space through the proved matrix Lie algebra action. -/
def adelicEnvelopingAction : UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ]
    Module.End ℂ (adelicRealSmoothSubmodule f) :=
  UniversalEnvelopingAlgebra.lift ℂ (adelicComplexSl2Action f)

/-- The actual enveloping action retains exactly the original matrix infinitesimal action. -/
theorem adelicEnvelopingAction_generator (x : ComplexSl2) :
    adelicEnvelopingAction f (UniversalEnvelopingAlgebra.ι ℂ x) = adelicComplexSl2Action f x :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (adelicComplexSl2Action f) x

/-- The genuine central normalized Casimir has exactly the original successive Hilbert derivative operator as its image. -/
theorem adelicEnvelopingAction_casimir :
    adelicEnvelopingAction f complexSl2EnvelopingCasimir = adelicSmoothCasimirOperator f := by
  simp only [complexSl2EnvelopingCasimir, normalizedSl2Casimir, map_sub, map_add, map_mul,
    map_neg, adelicEnvelopingAction_generator, adelicComplexSl2Action_A, adelicComplexSl2Action_U,
    adelicComplexSl2Action_F, adelicSmoothCasimirOperator_eq_normalized]

/-- The original second-order operator commutes with the action of every element of the full actual enveloping algebra. -/
theorem adelicEnvelopingAction_casimir_commutes (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) :
    Commute (adelicSmoothCasimirOperator f) (adelicEnvelopingAction f z) := by
  rw [← adelicEnvelopingAction_casimir]
  exact (complexSl2EnvelopingCasimir_commutes z).map (adelicEnvelopingAction f)

/-- The original smooth generator has the exact central enveloping-algebra Casimir eigenvalue. -/
theorem adelicEnvelopingAction_casimir_generator :
    adelicEnvelopingAction f complexSl2EnvelopingCasimir (adelicSmoothGenerator f) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicSmoothGenerator f := by
  rw [adelicEnvelopingAction_casimir]
  exact adelicSmoothGenerator_casimir f

/-- Every original enveloping-algebra translate of the genuine smooth generator has the same actual central Casimir eigenvalue. -/
theorem adelicEnvelopingAction_casimir_orbit (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) :
    adelicSmoothCasimirOperator f (adelicEnvelopingAction f z (adelicSmoothGenerator f)) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) •
        adelicEnvelopingAction f z (adelicSmoothGenerator f) := by
  exact commuting_end_eigen (adelicSmoothCasimirOperator f) (adelicEnvelopingAction f z)
    (adelicSmoothGenerator f) _ (adelicEnvelopingAction_casimir_commutes f z)
    (adelicSmoothGenerator_casimir f)

end
end Dubon2026
