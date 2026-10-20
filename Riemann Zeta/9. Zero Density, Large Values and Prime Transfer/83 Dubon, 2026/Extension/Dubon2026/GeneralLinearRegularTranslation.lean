import Dubon2026.GeneralLinearRegularPoints
import Mathlib.RepresentationTheory.Basic

/-! The exact right-translation representation on the original regular
functions, required by the source integral Borel induction. Evaluation is
proved over every coefficient algebra, preserving the source action order. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Right translation evaluates the original regular function on the original generic matrix multiplied by the specified coefficient-ring matrix. -/
def generalLinearRegularRightTranslate (g : GeneralLinearGroup (Fin n) R) :
    GeneralLinearRegularFunctions R n →ₐ[R] GeneralLinearRegularFunctions R n :=
  generalLinearRegularEval (generalLinearRegularGeneric R n *
    GeneralLinearGroup.map (algebraMap R (GeneralLinearRegularFunctions R n)) g)

/-- Right translation has exactly the source formula f(xg) over every coefficient algebra. -/
theorem generalLinearRegularEval_rightTranslate
    {A : Type*} [CommRing A] [Algebra R A]
    (g : GeneralLinearGroup (Fin n) R) (x : GeneralLinearGroup (Fin n) A) :
    (generalLinearRegularEval (R := R) x).comp (generalLinearRegularRightTranslate g) =
      generalLinearRegularEval (x * GeneralLinearGroup.map (algebraMap R A) g) := by
  have hc : GeneralLinearGroup.map (generalLinearRegularEval (R := R) x).toRingHom
      (GeneralLinearGroup.map (algebraMap R (GeneralLinearRegularFunctions R n)) g) =
        GeneralLinearGroup.map (algebraMap R A) g := by
    apply Units.ext
    ext i j
    exact (generalLinearRegularEval (R := R) x).commutes (g.val i j)
  rw [generalLinearRegularRightTranslate, generalLinearRegularEval_natural, map_mul,
    generalLinearRegularGeneric_eval, hc]

/-- Translation by the identity is the identity on the original regular-function algebra. -/
theorem generalLinearRegularRightTranslate_one :
    generalLinearRegularRightTranslate (1 : GeneralLinearGroup (Fin n) R) =
      AlgHom.id R (GeneralLinearRegularFunctions R n) := by
  rw [generalLinearRegularRightTranslate, map_one, mul_one, generalLinearRegularEval_generic]

/-- The original right-translation operators compose in precisely the source representation order. -/
theorem generalLinearRegularRightTranslate_mul (g h : GeneralLinearGroup (Fin n) R) :
    generalLinearRegularRightTranslate (g * h) =
      (generalLinearRegularRightTranslate g).comp (generalLinearRegularRightTranslate h) := by
  symm
  change (generalLinearRegularEval (generalLinearRegularGeneric R n *
    GeneralLinearGroup.map (algebraMap R (GeneralLinearRegularFunctions R n)) g)).comp
      (generalLinearRegularRightTranslate h) = _
  rw [generalLinearRegularEval_rightTranslate, generalLinearRegularRightTranslate, map_mul,
    mul_assoc]

/-- The actual coefficient group acts by the source right translation on original regular functions. -/
def generalLinearRegularRepresentation :
    Representation R (GeneralLinearGroup (Fin n) R) (GeneralLinearRegularFunctions R n) where
  toFun g := (generalLinearRegularRightTranslate g).toLinearMap
  map_one' := by
    rw [generalLinearRegularRightTranslate_one]
    rfl
  map_mul' g h := by
    rw [generalLinearRegularRightTranslate_mul]
    rfl

end
end Dubon2026
