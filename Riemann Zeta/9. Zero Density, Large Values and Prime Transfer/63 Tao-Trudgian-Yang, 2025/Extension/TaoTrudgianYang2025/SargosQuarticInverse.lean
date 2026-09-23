import TaoTrudgianYang2025.SargosQuarticPhase
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! The inverse of the actual quartic slope and its signed Legendre phase.
Differentiation is restricted to the image of the open source interval. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticSlopeRange (N α γ : ℝ) : Set ℝ :=
  sargosQuarticSlope α γ '' Ioo N (2*N)

def sargosQuarticInverseSlope (N α γ : ℝ) : ℝ → ℝ :=
  Function.invFunOn (sargosQuarticSlope α γ) (Icc N (2*N))

def sargosQuarticLegendre (N α γ y : ℝ) : ℝ :=
  sargosQuarticPhase α γ (sargosQuarticInverseSlope N α γ y) -
    y*sargosQuarticInverseSlope N α γ y

theorem sargosQuarticInverseSlope_slope {N α γ x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hx : x ∈ Icc N (2*N)) :
    sargosQuarticInverseSlope N α γ (sargosQuarticSlope α γ x) = x :=
  (sargosQuarticSlope_strictMonoOn hN hα hγ).injOn.leftInvOn_invFunOn hx

theorem sargosQuarticInverseSlope_mem {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticInverseSlope N α γ y ∈ Ioo N (2*N) := by
  rcases hy with ⟨x,hx,rfl⟩
  rw [sargosQuarticInverseSlope_slope hN hα hγ ⟨hx.1.le,hx.2.le⟩]
  exact hx

theorem sargosQuarticSlope_inverse {N α γ y : ℝ}
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticSlope α γ (sargosQuarticInverseSlope N α γ y) = y := by
  apply Function.invFunOn_eq
  rcases hy with ⟨x,hx,rfl⟩
  exact ⟨x,⟨hx.1.le,hx.2.le⟩,rfl⟩

theorem sargosQuarticSlope_hasStrictDerivAt (α γ x : ℝ) :
    HasStrictDerivAt (sargosQuarticSlope α γ) (2*α+12*γ*x^2) x := by
  have h := ((contDiff_sargosQuarticSlope α γ).contDiffAt (x := x)).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  rwa [(sargosQuarticSlope_hasDerivAt α γ x).deriv] at h

theorem sargosQuartic_curvature_pos {N α γ x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hx : x ∈ Icc N (2*N)) :
    0 < 2*α+12*γ*x^2 :=
  lt_of_lt_of_le (by positivity : 0 < 3*α/2)
    (sargosQuarticPhase_curvature hN hα hγ hx).1

theorem sargosQuarticInverseSlope_hasStrictDerivAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    HasStrictDerivAt (sargosQuarticInverseSlope N α γ)
      (2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2)⁻¹ y := by
  rcases hy with ⟨x,hx,rfl⟩
  rw [sargosQuarticInverseSlope_slope hN hα hγ ⟨hx.1.le,hx.2.le⟩]
  apply (sargosQuarticSlope_hasStrictDerivAt α γ x).to_local_left_inverse
    (ne_of_gt (sargosQuartic_curvature_pos hN hα hγ ⟨hx.1.le,hx.2.le⟩))
  filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
  exact sargosQuarticInverseSlope_slope hN hα hγ ⟨hu.1.le,hu.2.le⟩

theorem sargosQuarticSlopeRange_isOpen {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    IsOpen (sargosQuarticSlopeRange N α γ) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hi := Filter.image_mem_map (m := sargosQuarticSlope α γ) (isOpen_Ioo.mem_nhds hx)
  rwa [(sargosQuarticSlope_hasStrictDerivAt α γ x).map_nhds_eq
    (ne_of_gt (sargosQuartic_curvature_pos hN hα hγ ⟨hx.1.le,hx.2.le⟩))] at hi

theorem sargosQuarticInverseSlope_contDiffAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ContDiffAt ℝ ∞ (sargosQuarticInverseSlope N α γ) y := by
  rcases hy with ⟨x,hx,rfl⟩
  have hc := (contDiff_sargosQuarticSlope α γ).contDiffAt (x := x)
  have hd := sargosQuarticSlope_hasStrictDerivAt α γ x
  have he := hd.hasStrictFDerivAt_equiv
    (ne_of_gt (sargosQuartic_curvature_pos hN hα hγ ⟨hx.1.le,hx.2.le⟩))
  have hg : ∀ᶠ u in 𝓝 x,
      sargosQuarticInverseSlope N α γ (sargosQuarticSlope α γ u) = u := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
    exact sargosQuarticInverseSlope_slope hN hα hγ ⟨hu.1.le,hu.2.le⟩
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

theorem sargosQuarticLegendre_hasDerivAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    HasDerivAt (sargosQuarticLegendre N α γ) (-sargosQuarticInverseSlope N α γ y) y := by
  have hi := (sargosQuarticInverseSlope_hasStrictDerivAt hN hα hγ hy).hasDerivAt
  have hg := (sargosQuarticPhase_hasDerivAt α γ _).comp y hi
  have h := hg.sub ((hasDerivAt_id y).mul hi)
  rw [sargosQuarticSlope_inverse hy] at h
  convert h using 1
  dsimp only [id_eq]
  ring

theorem sargosQuarticLegendre_contDiffAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ContDiffAt ℝ ∞ (sargosQuarticLegendre N α γ) y := by
  have hi := sargosQuarticInverseSlope_contDiffAt hN hα hγ hy
  exact ((contDiff_sargosQuarticPhase α γ).contDiffAt.comp y hi).sub
    (contDiffAt_id.mul hi)

end TaoTrudgianYang2025
