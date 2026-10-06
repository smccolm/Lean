import Dubon2026.VerticalJets

/-! # Real components and local derivative lower bounds for the genuine vertical family -/

namespace Dubon2026

open Filter Set
open scoped Topology ContDiff

noncomputable section

/-- One of the two real coordinate projections, as a continuous real linear map. -/
def realComponent (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.reCLM else Complex.imCLM

theorem abs_realComponent_le_norm (b : Bool) (z : ℂ) : |realComponent b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem exists_realComponent_ne_zero {z : ℂ} (hz : z ≠ 0) : ∃ b, realComponent b z ≠ 0 := by
  by_cases hr : z.re = 0
  · refine ⟨false, ?_⟩
    intro hi
    exact hz (Complex.ext hr hi)
  · exact ⟨true, hr⟩

/-- The real or imaginary component of the actual kth vertical derivative. -/
def realVerticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ) (b : Bool)
    (z : PrimeTorus N) (t : ℝ) : ℝ := realComponent b (verticalJet a N σ k z t)

theorem hasDerivAt_realVerticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ) (b : Bool)
    (z : PrimeTorus N) (t : ℝ) :
    HasDerivAt (realVerticalJet a N σ k b z) (realVerticalJet a N σ (k + 1) b z t) t :=
  (realComponent b).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_verticalJet a N σ k z t)

theorem iteratedDeriv_real_verticalFamily (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ)
    (b : Bool) (z : PrimeTorus N) :
    iteratedDeriv k (fun t => realComponent b (verticalFamily a N σ z t)) =
      realVerticalJet a N σ k b z := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    funext t
    simp only [realVerticalJet, verticalJet_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun t => (hasDerivAt_realVerticalJet a N σ k b z t).deriv)

theorem contDiff_real_verticalFamily (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (b : Bool)
    (z : PrimeTorus N) : ContDiff ℝ ∞ (fun t => realComponent b (verticalFamily a N σ z t)) := by
  have h : AnalyticOnNhd ℝ (verticalFamily a N σ z) Set.univ :=
    fun t _ => analyticAt_verticalFamily a N σ z t
  exact (realComponent b).contDiff.comp h.contDiff

theorem continuous_realVerticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ) (b : Bool) :
    Continuous (fun zt : PrimeTorus N × ℝ => realVerticalJet a N σ k b zt.1 zt.2) :=
  (realComponent b).continuous.comp (continuous_verticalJet a N σ k)

theorem exists_rectangle_lower_bound {X : Type*} [TopologicalSpace X]
    (f : X × ℝ → ℝ) (hf : Continuous f) (x : X) (t : ℝ) (hne : f (x, t) ≠ 0) :
    ∃ (U : Set X) (left right L : ℝ),
      IsOpen U ∧ x ∈ U ∧ left < t ∧ t < right ∧ 0 < L ∧
      ∀ w ∈ U, ∀ u ∈ Icc left right, L ≤ |f (w, u)| := by
  let L := |f (x, t)| / 2
  have hL : 0 < L := half_pos (abs_pos.mpr hne)
  have hopen : IsOpen {xt : X × ℝ | L < |f xt|} :=
    isOpen_lt continuous_const hf.abs
  have hmem : (x, t) ∈ {xt : X × ℝ | L < |f xt|} :=
    half_lt_self (abs_pos.mpr hne)
  obtain ⟨U, V, hU, hxU, hV, htV, hsub⟩ := mem_nhds_prod_iff'.mp (hopen.mem_nhds hmem)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds htV)
  refine ⟨U, t - r / 2, t + r / 2, L, hU, hxU, by linarith, by linarith, hL, ?_⟩
  intro w hw u hu
  have huV : u ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2])
  exact (hsub ⟨hw, huV⟩).le

theorem exists_vertical_jet_rectangle {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    ∃ (k : ℕ) (b : Bool) (U : Set (PrimeTorus N)) (left right L : ℝ),
      IsOpen U ∧ z ∈ U ∧ left < t ∧ t < right ∧ 0 < L ∧
      ∀ w ∈ U, ∀ u ∈ Icc left right, L ≤ |realVerticalJet a N σ k b w u| := by
  obtain ⟨k, hk⟩ := exists_nonzero_verticalJet hN ha σ z t
  obtain ⟨b, hb⟩ := exists_realComponent_ne_zero hk
  exact ⟨k, b, exists_rectangle_lower_bound
    (fun zt : PrimeTorus N × ℝ => realVerticalJet a N σ k b zt.1 zt.2)
    (continuous_realVerticalJet a N σ k b) z t hb⟩

end

end Dubon2026
