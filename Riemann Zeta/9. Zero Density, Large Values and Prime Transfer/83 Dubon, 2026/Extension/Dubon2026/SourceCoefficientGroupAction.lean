import Dubon2026.SourceInducedCoefficientMap

/-! The original integral group action under coefficient change.
Generic evaluation compares the same right-translated regular function on
both sides. This identifies the generic-fibre map as the original source
representation comparison, not merely a vector-space isomorphism.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- Original coefficient change commutes with the same right translation by an original integral matrix. -/
theorem sourceRegularCoefficientMap_rightTranslate
    (g : GeneralLinearGroup (Fin n) R) (p : GeneralLinearRegularFunctions R n) :
    sourceRegularCoefficientMap R B n (generalLinearRegularRightTranslate g p) =
      generalLinearRegularRightTranslate (GeneralLinearGroup.map (algebraMap R B) g)
        (sourceRegularCoefficientMap R B n p) := by
  have hR := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate
    (R := R) g (generalLinearRegularGeneric B n)) p
  have hB := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate
    (R := B) (GeneralLinearGroup.map (algebraMap R B) g)
      (generalLinearRegularGeneric B n)) (sourceRegularCoefficientMap R B n p)
  rw [generalLinearRegularEval_generic] at hB
  change generalLinearRegularRightTranslate (GeneralLinearGroup.map (algebraMap R B) g)
      (sourceRegularCoefficientMap R B n p) =
    generalLinearRegularEval (R := B)
      (generalLinearRegularGeneric B n *
        GeneralLinearGroup.map (algebraMap B (GeneralLinearRegularFunctions B n))
          (GeneralLinearGroup.map (algebraMap R B) g))
      (sourceRegularCoefficientMap R B n p) at hB
  rw [sourceRegularCoefficientMap_eval] at hB
  have hm : GeneralLinearGroup.map (algebraMap B (GeneralLinearRegularFunctions B n))
      (GeneralLinearGroup.map (algebraMap R B) g) =
      GeneralLinearGroup.map (algebraMap R (GeneralLinearRegularFunctions B n)) g := by
    apply Units.ext
    ext i j
    exact (IsScalarTower.algebraMap_apply R B (GeneralLinearRegularFunctions B n) (g.val i j)).symm
  rw [hm] at hB
  exact hR.trans hB.symm

/-- The exact original induced group action is preserved by the actual coefficient-module map. -/
theorem sourceInducedCoefficientMap_action (lam : Fin n → ℤ)
    (g : GeneralLinearGroup (Fin n) R) (p : generalLinearIntegralInducedSubmodule R n lam) :
    sourceInducedCoefficientMap R B n lam (generalLinearIntegralInducedRepresentation R n lam g p) =
      generalLinearIntegralInducedRepresentation B n lam (GeneralLinearGroup.map (algebraMap R B) g)
        (sourceInducedCoefficientMap R B n lam p) :=
  Subtype.ext (sourceRegularCoefficientMap_rightTranslate R B n g p.val)

end
end Dubon2026
