import Dubon2026.SourceCurveParameterTateTrace
import Dubon2026.SourceCurveRationalExtensionDivisors

/-! The actual rational function field supplies rational residues, so
the parameter trace calculation has no residue-field hypothesis. This is
the exact local power calculation for the characteristic-free rational
residue theorem in the DUB-17/18 canonical-degree dependency. -/

noncomputable section

namespace Dubon2026.SourceCurve

/-- Exact local power residues in the literal rational field, in every characteristic. -/
theorem rational_tateResidue_parameter_zpow (K : Type*) [Field K] [IsAlgClosed K]
    (v : Place K (RatFunc K)) {t : RatFunc K} (ht : v.ord t = 1) (n : ℤ) :
    v.tateResidue (t ^ n) t = if n = -1 then 1 else 0 := by
  haveI := rational_coordinate_finite K
  exact v.tateResidue_parameter_zpow ht
    (place_residue_bijective_of_finite_coordinate (RatFunc.X : RatFunc K) v).surjective n

end Dubon2026.SourceCurve
