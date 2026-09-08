import GafniTao.SharpPerronLandauZeros

/-!
# A good ordinate chosen from the actual normalized zeta zeros

This is the finite pigeonhole layer of the sharp explicit formula.  The
candidate set is the image of the literal Landau zero disk, and its size is
controlled by the analytic vanishing orders counted by Jensen's theorem.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

namespace GafniTao

/-- Among `|S|+1` equally spaced midpoints of `[a,a+1]`, one stays this far
from every member of a finite real set. -/
theorem exists_far_point (S : Finset ℝ) (a : ℝ) :
    ∃ R : ℝ, a ≤ R ∧ R ≤ a + 1 ∧
      ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |R - y| := by
  classical
  set n : ℕ := S.card with hn
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδn : 2 * ((n : ℝ) + 1) * δ = 1 := by rw [hδ]; field_simp
  set cand : ℕ → ℝ := fun k => a + (2 * (k : ℝ) + 1) * δ with hcand
  by_contra hcon
  push Not at hcon
  have hbad : ∀ k ∈ Finset.range (n + 1),
      ∃ y ∈ S, |cand k - y| < δ := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : a ≤ cand k := by simp only [hcand]; nlinarith
    have h2 : cand k ≤ a + 1 := by
      simp only [hcand]
      have : (2 * (k : ℝ) + 1) * δ ≤ (2 * (n : ℝ) + 1) * δ := by gcongr
      nlinarith
    obtain ⟨y, hy, hlt⟩ := hcon (cand k) h1 h2
    exact ⟨y, hy, hlt⟩
  choose! f hf using hbad
  have hmaps : Set.MapsTo f (Finset.range (n + 1)) S :=
    fun k hk => (hf k hk).1
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1 := (hf x hx).2
  have h2 := (hf y hy).2
  rw [hfxy] at h1
  have hdist : |cand x - cand y| = 2 * |(x : ℝ) - y| * δ := by
    simp only [hcand]
    rw [show a + (2 * (x : ℝ) + 1) * δ -
        (a + (2 * (y : ℝ) + 1) * δ) =
        (2 * δ) * ((x : ℝ) - y) by ring,
      abs_mul, abs_of_pos (by positivity)]
    ring
  have hxy1 : (1 : ℝ) ≤ |(x : ℝ) - y| := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have htri : |cand x - cand y| < 2 * δ := by
    calc
      |cand x - cand y| = |(cand x - f y) - (cand y - f y)| := by ring_nf
      _ ≤ |cand x - f y| + |cand y - f y| := abs_sub _ _
      _ < δ + δ := add_lt_add h1 h2
      _ = 2 * δ := by ring
  rw [hdist] at htri
  nlinarith

/-- The local zero disk used in `FinalBound`, with its genuine analytic
multiplicities. -/
noncomputable def sharpLandauZeroFinset (T : ℝ) (hT : 8 ≤ T) : Finset ℂ :=
  (finiteSetOfZeros_mono (by norm_num : (24 / 25 : ℝ) < 1)
    (finite_sharpLandauNormalized_zeros hT)).toFinset

noncomputable def sharpLandauZeroMass (T : ℝ) (hT : 8 ≤ T) : ℕ :=
  ∑ ρ ∈ sharpLandauZeroFinset T hT,
    analyticOrderNatAt (sharpLandauNormalized T) ρ

noncomputable def sharpLandauZeroOrdinates (T : ℝ) (hT : 8 ≤ T) : Finset ℝ :=
  (sharpLandauZeroFinset T hT).image
    (fun ρ => (sharpLandauMap T ρ).im)

theorem one_le_sharpLandau_zero_order
    {T : ℝ} (hT : 8 ≤ T) {ρ : ℂ}
    (hρ : ρ ∈ sharpLandauZeroFinset T hT) :
    1 ≤ analyticOrderNatAt (sharpLandauNormalized T) ρ := by
  have hTT : T ∈ Set.Icc (T - 1) (2 * T) := ⟨by linarith, by linarith⟩
  have hρzero : sharpLandauNormalized T ρ = 0 := by
    exact ((finiteSetOfZeros_mono (by norm_num : (24 / 25 : ℝ) < 1)
      (finite_sharpLandauNormalized_zeros hT)).mem_toFinset.mp hρ).2
  have hρnorm : ‖ρ‖ ≤ 1 := by
    have := ((finiteSetOfZeros_mono (by norm_num : (24 / 25 : ℝ) < 1)
      (finite_sharpLandauNormalized_zeros hT)).mem_toFinset.mp hρ).1
    linarith
  have hana : AnalyticAt ℂ (sharpLandauNormalized T) ρ :=
    (analyticOnNhd_sharpLandauNormalized hT hTT) ρ (by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hρnorm)
  have hfinite : analyticOrderAt (sharpLandauNormalized T) ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (x := (0 : ℂ)) (y := ρ)
      (analyticOnNhd_sharpLandauNormalized hT hTT)
      Metric.isPreconnected_closedBall ?_ ?_ ?_
    · exact Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)
    · simpa [Metric.mem_closedBall, Complex.dist_eq] using hρnorm
    · rw [analyticOrderAt_eq_zero.mpr (Or.inr (by
        rw [sharpLandauNormalized_zero T]
        exact one_ne_zero))]
      exact ENat.zero_ne_top
  have horderNe : analyticOrderAt (sharpLandauNormalized T) ρ ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hρzero
  have hnatNe : analyticOrderNatAt (sharpLandauNormalized T) ρ ≠ 0 := by
    intro h
    apply horderNe
    rw [← Nat.cast_analyticOrderNatAt hfinite, h]
    rfl
  exact Nat.one_le_iff_ne_zero.mpr hnatNe

theorem sharpLandauZeroOrdinates_card_le_mass
    {T : ℝ} (hT : 8 ≤ T) :
    (sharpLandauZeroOrdinates T hT).card ≤ sharpLandauZeroMass T hT := by
  calc
    (sharpLandauZeroOrdinates T hT).card ≤
        (sharpLandauZeroFinset T hT).card := Finset.card_image_le
    _ = ∑ _ρ ∈ sharpLandauZeroFinset T hT, 1 := by simp
    _ ≤ ∑ ρ ∈ sharpLandauZeroFinset T hT,
        analyticOrderNatAt (sharpLandauNormalized T) ρ := by
          exact Finset.sum_le_sum (fun ρ hρ => one_le_sharpLandau_zero_order hT hρ)
    _ = sharpLandauZeroMass T hT := rfl

theorem sharpLandauZeroMass_le
    {T : ℝ} (hT : 8 ≤ T) :
    sharpLandauZeroMass T hT ≤
      1 / Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ)) *
        Real.log (200 * T ^ (3 : ℝ)) := by
  have hTT : T ∈ Set.Icc (T - 1) (2 * T) := ⟨by linarith, by linarith⟩
  apply ZerosBound (B := 200 * T ^ (3 : ℝ))
      (r := 24 / 25) (R := 49 / 50)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact analyticOnNhd_sharpLandauNormalized hT hTT
  · exact sharpLandauNormalized_zero T
  · exact finite_sharpLandauNormalized_zeros hT
  · intro w hw
    exact norm_sharpLandauNormalized_le hT hTT (by linarith)

/-- A height in `[T,T+1]` separated from every zero used by the local
partial-fraction expansion. -/
theorem exists_sharpPerron_good_height
    {T : ℝ} (hT : 8 ≤ T) :
    ∃ R : ℝ, T ≤ R ∧ R ≤ T + 1 ∧
      ∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im| := by
  obtain ⟨R, hR1, hR2, hfar⟩ :=
    exists_far_point (sharpLandauZeroOrdinates T hT) T
  refine ⟨R, hR1, hR2, ?_⟩
  intro ρ hρ
  exact hfar _ (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩)

end GafniTao
