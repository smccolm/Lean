import Dubon2026.SourceComplexDbarCutoff

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> smooth invariant
comparison function -> compact dipole with exact integer local orders.
The existing wedge/residue identity and antiholomorphic derivative are reused.
This constructs a smooth local comparison, without assuming meromorphic
realization or the desired principal-divisor converse. -/
namespace Dubon2026.SourceComplexReciprocity.Dipole
noncomputable section
open Complex MeasureTheory Filter Set Metric DbarFundamental
open scoped Real Topology Manifold ContDiff
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

/-- Antiholomorphic coordinate projection of a real differential. -/
def dbarL (T : ℂ →L[ℝ] ℂ) : ℂ := (T 1 + I * T I) / 2

theorem dbar_eq (f : ℂ → ℂ) (z : ℂ) : D f z = dbarL (fderiv ℝ f z) := rfl

theorem dbarL_add (T T' : ℂ →L[ℝ] ℂ) : dbarL (T + T') = dbarL T + dbarL T' := by
  simp only [dbarL, ContinuousLinearMap.add_apply]; ring

theorem dbarL_smul (c : ℂ) (T : ℂ →L[ℝ] ℂ) : dbarL (c • T) = c * dbarL T := by
  simp only [dbarL, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

theorem dbarL_neg (T : ℂ →L[ℝ] ℂ) : dbarL (-T) = -dbarL T := by
  simp only [dbarL, ContinuousLinearMap.neg_apply]; ring

theorem dbarL_of_hasDerivAt {q : ℂ → ℂ} {q' z : ℂ} (h : HasDerivAt q q' z) :
    dbarL (fderiv ℝ q z) = 0 := by
  rw [h.complexToReal_fderiv.fderiv]
  simp only [dbarL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  ring_nf; simp [I_sq]

section Core

variable {b s : ℂ} (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s)
  {χ : ℂ → ℝ} {O K : Set ℂ}
  (hχ : ContDiff ℝ 2 χ) (hO : IsOpen O) (hSeg : segment ℝ b s ⊆ O) (hχ1 : ∀ z ∈ O, χ z = 1)
  (hOK : O ⊆ K) (hK : IsClosed K) (hχK : tsupport χ ⊆ K) (h01 : ∀ z, χ z ∈ Icc (0 : ℝ) 1)

/-- The real cutoff viewed as a complex-valued function. -/
def χC (χ : ℂ → ℝ) (z : ℂ) : ℂ := (χ z : ℂ)

/-- Compactly supported modification of the ratio (z-s)/(z-b), with pole value zero. -/
def dfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ :=
  if z = b then 0 else 1 - χC χ z * (s - b) / (z - b)

/-- The formula for the dipole away from its pole. -/
def gfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := 1 - χC χ z * ((s - b) * (z - b)⁻¹)

/-- The numerator of the cutoff dipole. -/
def wfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := z - b - χC χ z * (s - b)

/-- Antiholomorphic derivative of the complex-valued cutoff. -/
def Dχ (χ : ℂ → ℝ) (z : ℂ) : ℂ := D (χC χ) z

/-- Continuous compactly supported logarithmic antiholomorphic derivative of the dipole. -/
def Ffun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := -Dχ χ z * (s - b) / wfun b s χ z

include hχ in
theorem contDiff_χC : ContDiff ℝ 2 (χC χ) := ofRealCLM.contDiff.comp hχ

theorem support_χC : Function.support (χC χ) = Function.support χ := by
  ext z; simp [χC]

theorem tsupport_χC : tsupport (χC χ) = tsupport χ := by
  rw [tsupport, tsupport, support_χC]

include hSeg hχ1 h01 in

theorem wfun_eq_zero_iff (z : ℂ) : wfun b s χ z = 0 ↔ z = s := by
  constructor
  · intro hw
    have hz : z = b + (χ z : ℂ) * (s - b) := by
      simp only [wfun, χC] at hw; linear_combination hw
    have hmem : z ∈ segment ℝ b s := by
      rw [segment_eq_image]
      refine ⟨χ z, h01 z, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hz
    have h1 : χ z = 1 := hχ1 z (hSeg hmem)
    calc z = b + (χ z : ℂ) * (s - b) := hz
      _ = s := by rw [h1]; push_cast; ring
  · intro hz
    subst hz
    have hmem : z ∈ segment ℝ b z := right_mem_segment _ _ _
    simp only [wfun, χC, hχ1 z (hSeg hmem)]; push_cast; ring

theorem dfun_of_ne {z : ℂ} (hz : z ≠ b) : dfun b s χ z = wfun b s χ z / (z - b) := by
  rw [dfun, if_neg hz, wfun, sub_div, div_self (sub_ne_zero.2 hz), mul_div_assoc]

theorem dfun_eq_gfun_of_ne {z : ℂ} (hz : z ≠ b) : dfun b s χ z = gfun b s χ z := by
  simp only [dfun, if_neg hz, gfun, div_eq_mul_inv, mul_assoc]

theorem dfun_eventuallyEq_gfun {z : ℂ} (hz : z ≠ b) : dfun b s χ =ᶠ[𝓝 z] gfun b s χ := by
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw using dfun_eq_gfun_of_ne hw

include hχ in
theorem contDiffAt_gfun {z : ℂ} (hz : z ≠ b) : ContDiffAt ℝ 2 (gfun b s χ) z := by
  refine contDiffAt_const.sub ((contDiff_χC hχ).contDiffAt.mul ?_)
  exact contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.2 hz))

include hχ in
theorem contDiffAt_dfun {z : ℂ} (hz : z ≠ b) : ContDiffAt ℝ 2 (dfun b s χ) z :=
  (contDiffAt_gfun hχ hz).congr_of_eventuallyEq (dfun_eventuallyEq_gfun hz)

include hSeg hχ1 h01 in

theorem dfun_ne_zero {z : ℂ} (hzb : z ≠ b) (hzs : z ≠ s) : dfun b s χ z ≠ 0 := by
  rw [dfun_of_ne hzb]
  exact div_ne_zero (fun h => hzs ((wfun_eq_zero_iff hSeg hχ1 h01 z).1 h)) (sub_ne_zero.2 hzb)

include hχK in
theorem dfun_eq_one {z : ℂ} (hz : z ∉ K) (hbK : b ∈ K) : dfun b s χ z = 1 := by
  have hzb : z ≠ b := fun h => hz (h ▸ hbK)
  have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hχK h)
  simp [dfun, if_neg hzb, χC, hχ0]

include hχ1 in

theorem dfun_eq_near {z : ℂ} (hz : z ∈ O) (hzb : z ≠ b) : dfun b s χ z = (z - s) / (z - b) := by
  simp only [dfun, if_neg hzb, χC, hχ1 z hz]
  field_simp [sub_ne_zero.2 hzb]
  push_cast; ring

include hχ hO hSeg hχ1 h01 hbs in

theorem dfun_localModel (τ : ℂ) : ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
    dfun b s χ =ᶠ[𝓝 τ] fun z =>
      (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z := by
  by_cases hτb : τ = b
  · subst hτb
    refine ⟨fun z => z - s, (contDiffAt_id.sub contDiffAt_const), sub_ne_zero.2 hbs, ?_⟩
    have hexp : ((if τ = s then (1 : ℤ) else 0) - (if τ = τ then (1 : ℤ) else 0)) = -1 := by
      simp [hbs]
    rw [hexp]
    have hbO : τ ∈ O := hSeg (left_mem_segment _ _ _)
    filter_upwards [hO.mem_nhds hbO] with z hz
    by_cases hzb : z = τ
    · subst hzb; simp [dfun]
    · rw [dfun_eq_near hχ1 hz hzb, zpow_neg, zpow_one, div_eq_mul_inv, mul_comm]
  by_cases hτs : τ = s
  · subst hτs
    refine ⟨fun z => (z - b)⁻¹, (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.2 hτb),
      inv_ne_zero (sub_ne_zero.2 hτb), ?_⟩
    have hexp : ((if τ = τ then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) = 1 := by
      simp [hτb]
    rw [hexp]
    have hsO : τ ∈ O := hSeg (right_mem_segment _ _ _)
    filter_upwards [hO.mem_nhds hsO, isOpen_ne.mem_nhds hτb] with z hz hzb
    rw [dfun_eq_near hχ1 hz hzb, div_eq_mul_inv, zpow_one]
  · refine ⟨dfun b s χ, (contDiffAt_dfun hχ hτb).of_le (by norm_num),
      dfun_ne_zero hSeg hχ1 h01 hτb hτs, ?_⟩
    simp only [if_neg hτs, if_neg hτb, sub_self, zpow_zero, one_mul]
    exact Filter.EventuallyEq.rfl

end Core
end
end Dubon2026.SourceComplexReciprocity.Dipole
