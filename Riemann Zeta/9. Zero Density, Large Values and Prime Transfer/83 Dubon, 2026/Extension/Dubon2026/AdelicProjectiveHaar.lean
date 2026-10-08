import Dubon2026.FiniteProjectiveGL2Haar
import Dubon2026.RealProjectiveArithmetic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Actual both-sided product Haar measure for the real and finite projective adelic coordinates -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Set MeasureTheory
open scoped MatrixGroups

/-- The actual real special-projective group times the actual canonical finite general-projective group. -/
abbrev AdelicProjectiveGroup := PSL(2, ℝ) × RationalFiniteProjectiveGL2

/-- The genuine product of the existing real projective Haar measure and normalized finite projective Haar measure. -/
def adelicProjectiveMeasure : Measure AdelicProjectiveGroup :=
  realProjectiveMeasure.prod finiteProjectiveGL2Measure

instance adelicProjectiveMeasureIsHaarMeasure : adelicProjectiveMeasure.IsHaarMeasure := by
  unfold adelicProjectiveMeasure
  infer_instance

instance adelicProjectiveMeasureIsMulRightInvariant : adelicProjectiveMeasure.IsMulRightInvariant := by
  unfold adelicProjectiveMeasure
  infer_instance

instance adelicProjectiveMeasureSigmaFinite : SigmaFinite adelicProjectiveMeasure := by
  unfold adelicProjectiveMeasure
  infer_instance

/-- Every actual right translation preserves the original product projective Haar measure. -/
theorem adelicProjectiveMeasure_right_invariant (g : AdelicProjectiveGroup) :
    MeasurePreserving (fun h : AdelicProjectiveGroup => h * g)
      adelicProjectiveMeasure adelicProjectiveMeasure :=
  measurePreserving_mul_right adelicProjectiveMeasure g

/-- The literal real full-level region times the actual compact full finite level subgroup. -/
def adelicProjectiveBaseRegion : Set AdelicProjectiveGroup :=
  realProjectiveGamma0Domain 1 ×ˢ finiteProjectiveGL2Level 1

/-- The original adelic base region is open in the actual product topology. -/
theorem adelicProjectiveBaseRegion_isOpen : IsOpen adelicProjectiveBaseRegion :=
  (realProjectiveGamma0Domain_isOpen 1).prod (finiteProjectiveGL2Level_compact_open 1).2

/-- The normalized finite factor leaves exactly the original real-domain volume. -/
theorem adelicProjectiveBaseRegion_volume :
    adelicProjectiveMeasure adelicProjectiveBaseRegion =
      realProjectiveMeasure (realProjectiveGamma0Domain 1) := by
  rw [adelicProjectiveMeasure, adelicProjectiveBaseRegion, Measure.prod_prod,
    finiteProjectiveGL2Measure_level_one, mul_one]

/-- The actual original adelic base region has finite product Haar volume. -/
theorem adelicProjectiveBaseRegion_volume_lt_top :
    adelicProjectiveMeasure adelicProjectiveBaseRegion < ⊤ := by
  rw [adelicProjectiveBaseRegion_volume]
  exact realProjectiveGamma0Domain_volume_lt_top 1

end
end Dubon2026
