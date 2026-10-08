import Dubon2026.RealSmoothInfinitesimalTangents

/-! # Exact norm differentiation by the original smooth tangent operators -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- On the original smooth space, the actual entry tangent gives its genuine Hilbert norm derivative without a global smoothness assumption on the curve. -/
theorem realSmoothInfinitesimal_hasDerivAt_tangent {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (ρ : Representation ℂ SL(2, ℝ) V) (L : SL(2, ℝ) → V →L[ℝ] V)
    (hL : ∀ g v, L g v = ρ g v) (v : realMatrixSmoothSubmodule ρ)
    (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    HasDerivAt (fun t => ρ (c t) v.val)
      (((b : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realLowerUnipotent realLowerUnipotent_entries_contDiff +
        ((2 * a : ℝ) : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realGeodesicCurve realGeodesicCurve_entries_contDiff +
        (d : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realUpperUnipotent realUpperUnipotent_entries_contDiff) v).val 0 := by
  have hD := realSmoothOrbitDifferential_hasDerivAt ρ v.val v.property c hc a b d ha hb hd
  have hT := realSmoothOrbitDifferential_tangent ρ v.val v.property c hc a b d ha hb hd
  rw [hD.deriv] at hT
  rw [hT] at hD
  exact hD

end
end Dubon2026
