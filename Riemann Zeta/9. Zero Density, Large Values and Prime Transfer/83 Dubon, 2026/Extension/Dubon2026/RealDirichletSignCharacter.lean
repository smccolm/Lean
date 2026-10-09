import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Real.Lemmas

/-! # The genuine real sign component of an original Dirichlet idèle character -/

namespace Dubon2026

noncomputable section

variable {D : ℕ} (χ : DirichletCharacter ℂ D)

/-- The original character evaluated on the actual sign of a nonzero real unit. -/
def realDirichletSignCharacter : ℝˣ →* ℂ :=
  χ.toMonoidHom.comp ((SignType.castHom (α := ZMod D)).toMonoidHom.comp
    ((signHom (α := ℝ)).toMonoidHom.comp (Units.coeHom ℝ)))

/-- The real character uses precisely the sign of the actual original real value. -/
theorem realDirichletSignCharacter_apply (u : ℝˣ) :
    realDirichletSignCharacter χ u = χ (SignType.sign u.val : ZMod D) := rfl

/-- The genuine real sign component is trivial on positive real units. -/
theorem realDirichletSignCharacter_positive (u : ℝˣ) (hu : 0 < u.val) :
    realDirichletSignCharacter χ u = 1 := by
  rw [realDirichletSignCharacter_apply, sign_pos hu]
  exact map_one χ

/-- The negative real component is the original Dirichlet value at minus one. -/
theorem realDirichletSignCharacter_negative (u : ℝˣ) (hu : u.val < 0) :
    realDirichletSignCharacter χ u = χ (-1) := by
  rw [realDirichletSignCharacter_apply, sign_neg hu]
  rfl

/-- The actual real sign component is continuous on the original real unit group. -/
theorem realDirichletSignCharacter_continuous : Continuous (realDirichletSignCharacter χ) := by
  have hc : Continuous (fun s : SignType => χ (s : ZMod D)) := continuous_of_discreteTopology
  apply hc.comp
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (continuousAt_sign_of_ne_zero (Units.ne_zero u)).comp Units.continuous_val.continuousAt

end
end Dubon2026
