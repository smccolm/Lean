import Dubon2026.RealSmoothOrbitDifferential
import Dubon2026.RealInfinitesimalEntryTangents
import Dubon2026.RealSmoothInfinitesimalOperator

/-! # Original smooth infinitesimals as the exact linear combination of entry tangents -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The actual Gaussian orbit differential on the lower coordinate axis is the original lower infinitesimal. -/
theorem realSmoothOrbitDifferential_lower (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) :
    deriv (fun t => ρ (realLowerUnipotent t) v) 0 = realSmoothOrbitDifferential ρ v (1, 0, 0) := by
  simpa only [mul_zero] using realSmoothOrbitDifferential_deriv ρ v hv
    realLowerUnipotent realLowerUnipotent_zero 0 1 0
    (realLowerUnipotent_entry_hasDerivAt 0 0) (realLowerUnipotent_entry_hasDerivAt 1 0)
    (realLowerUnipotent_entry_hasDerivAt 0 1)

/-- The actual Gaussian orbit differential on the middle coordinate axis is the original geodesic infinitesimal. -/
theorem realSmoothOrbitDifferential_geodesic (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) :
    deriv (fun t => ρ (realGeodesicCurve t) v) 0 = realSmoothOrbitDifferential ρ v (0, 1, 0) := by
  convert realSmoothOrbitDifferential_deriv ρ v hv realGeodesicCurve realGeodesicCurve_zero
    (1 / 2) 0 0 (realGeodesicCurve_entry_hasDerivAt 0 0)
    (realGeodesicCurve_entry_hasDerivAt 1 0) (realGeodesicCurve_entry_hasDerivAt 0 1) using 1
  norm_num

/-- The actual Gaussian orbit differential on the upper coordinate axis is the original upper infinitesimal. -/
theorem realSmoothOrbitDifferential_upper (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) :
    deriv (fun t => ρ (realUpperUnipotent t) v) 0 = realSmoothOrbitDifferential ρ v (0, 0, 1) := by
  simpa only [mul_zero] using realSmoothOrbitDifferential_deriv ρ v hv
    realUpperUnipotent realUpperUnipotent_zero 0 0 1
    (realUpperUnipotent_entry_hasDerivAt 0 0) (realUpperUnipotent_entry_hasDerivAt 1 0)
    (realUpperUnipotent_entry_hasDerivAt 0 1)

/-- The actual orbit derivative is the exact linear combination of the three original infinitesimals. -/
theorem realSmoothOrbitDifferential_tangent (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ)
    (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    deriv (fun t => ρ (c t) v) 0 =
      (b : ℂ) • deriv (fun t => ρ (realLowerUnipotent t) v) 0 +
      ((2 * a : ℝ) : ℂ) • deriv (fun t => ρ (realGeodesicCurve t) v) 0 +
      (d : ℂ) • deriv (fun t => ρ (realUpperUnipotent t) v) 0 := by
  rw [realSmoothOrbitDifferential_deriv ρ v hv c hc a b d ha hb hd,
    realSmoothOrbitDifferential_lower ρ v hv, realSmoothOrbitDifferential_geodesic ρ v hv,
    realSmoothOrbitDifferential_upper ρ v hv]
  have he : (b, 2 * a, d) = b • ((1, 0, 0) : ℝ × ℝ × ℝ) +
      (2 * a) • ((0, 1, 0) : ℝ × ℝ × ℝ) + d • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    simp
  rw [he, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Original entry tangents determine the actual endomorphism of the genuine smooth-vector space. -/
theorem realMatrixSmoothInfinitesimal_tangent (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hc0 : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    realMatrixSmoothInfinitesimal ρ L hL c hc =
      (b : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realLowerUnipotent realLowerUnipotent_entries_contDiff +
      ((2 * a : ℝ) : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realGeodesicCurve realGeodesicCurve_entries_contDiff +
      (d : ℂ) • realMatrixSmoothInfinitesimal ρ L hL realUpperUnipotent realUpperUnipotent_entries_contDiff := by
  ext v
  exact realSmoothOrbitDifferential_tangent ρ v.val v.property c hc0 a b d ha hb hd

end
end Dubon2026
