import Dubon2026.ZeroCountHeight
import Dubon2026.ZeroFreeBoundaries

/-! # Transferring genuine zero-count limits from nearby contour heights -/

namespace Dubon2026

open Filter
open scoped Topology

theorem verticalZeroCount_zero_height {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    verticalZeroCount a N hN ha l u 0 = 0 := by
  have he : zerosInOpenRectangleFinset a N hN ha l u 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have ht := ((mem_zerosInOpenRectangleFinset a N hN ha l u 0 s).mp hs).2.2.1
    exact (not_lt_of_ge (abs_nonneg s.im)) ht
  simp [verticalZeroCount, he]

theorem exists_verticalZeroCount_linear_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (verticalZeroCount a N hN ha l u T : ℝ) ≤ C * T := by
  obtain ⟨B, hB, hb⟩ := exists_verticalZeroCount_unit_increment_bound hN ha l u
  have hn (n : ℕ) : (verticalZeroCount a N hN ha l u n : ℝ) ≤ n * B := by
    induction n with
    | zero => simp [verticalZeroCount_zero_height]
    | succ n ih =>
      have hi := hb n (n + 1) (Nat.cast_nonneg n) (by linarith) le_rfl
      push_cast
      linarith
  refine ⟨2 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro T hT
  have hc := Nat.le_ceil T
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
  have hm : (verticalZeroCount a N hN ha l u T : ℝ) ≤
      verticalZeroCount a N hN ha l u (⌈T⌉₊ : ℝ) := by
    exact_mod_cast verticalZeroCount_mono_height hN ha l u hc
  have hbceil := mul_le_mul_of_nonneg_right hceil.le hB
  have hbT := mul_le_mul_of_nonneg_right (show T + 1 ≤ 2 * T by linarith) hB
  have hnceil := hn ⌈T⌉₊
  nlinarith

theorem tendsto_nearby_height_ratio {U : ℝ → ℝ}
    (hU : ∀ᶠ T in atTop, T ≤ U T ∧ U T ≤ T + 1) :
    Tendsto (fun T => U T / T) atTop (𝓝 1) := by
  have hd : Tendsto (fun T => (U T - T) / T) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tendsto_id.const_div_atTop 1)
    · filter_upwards [hU, eventually_ge_atTop (1 : ℝ)] with T hu ht
      exact div_nonneg (sub_nonneg.mpr hu.1) (by linarith)
    · filter_upwards [hU, eventually_ge_atTop (1 : ℝ)] with T hu ht
      exact div_le_div_of_nonneg_right (by linarith [hu.2]) (by linarith)
  have he : (fun T => U T / T) =ᶠ[atTop] (fun T => (U T - T) / T + 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T ht
    field_simp
    ring
  have hh : Tendsto (fun T => (U T - T) / T + 1) atTop (𝓝 1) := by
    simpa using hd.add_const 1
  exact hh.congr' he.symm

theorem tendsto_verticalZeroCount_nearby_difference {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {U : ℝ → ℝ}
    (hU : ∀ᶠ T in atTop, T ≤ U T ∧ U T ≤ T + 1) :
    Tendsto (fun T => ((verticalZeroCount a N hN ha l u (U T) : ℝ) -
      verticalZeroCount a N hN ha l u T) / (2 * T)) atTop (𝓝 0) := by
  obtain ⟨B, _hB, hb⟩ := exists_verticalZeroCount_unit_increment_bound hN ha l u
  apply squeeze_zero' ?_ ?_
    ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).const_div_atTop B)
  · filter_upwards [hU, eventually_ge_atTop (1 : ℝ)] with T hu ht
    have hm : (verticalZeroCount a N hN ha l u T : ℝ) ≤
        verticalZeroCount a N hN ha l u (U T) := by
      exact_mod_cast verticalZeroCount_mono_height hN ha l u hu.1
    exact div_nonneg (sub_nonneg.mpr hm) (by positivity)
  · filter_upwards [hU, eventually_ge_atTop (1 : ℝ)] with T hu ht
    have hi := hb T (U T) (by linarith) hu.1 hu.2
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The narrower hypothesis is a density limit only on nearby selected heights.
The actual uniform collar bound, rather than a new zero-count assumption, fills the gaps. -/
theorem tendsto_verticalZeroCount_of_nearby_heights {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {U : ℝ → ℝ} {L : ℝ}
    (hU : ∀ᶠ T in atTop, T ≤ U T ∧ U T ≤ T + 1)
    (hlim : Tendsto (fun T => (verticalZeroCount a N hN ha l u (U T) : ℝ) /
      (2 * U T)) atTop (𝓝 L)) :
    Tendsto (fun T => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T))
      atTop (𝓝 L) := by
  have hp := hlim.mul (tendsto_nearby_height_ratio hU)
  have hd := tendsto_verticalZeroCount_nearby_difference hN ha l u hU
  have hh := hp.sub hd
  simp only [mul_one, sub_zero] at hh
  apply hh.congr'
  filter_upwards [hU, eventually_ge_atTop (1 : ℝ)] with T hu ht
  have hT : T ≠ 0 := by linarith
  have hUT : U T ≠ 0 := by linarith [hu.1]
  field_simp
  ring

theorem exists_count_contour_height_selection {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ s : ℂ, s.re = l → dirichletSum a N s ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → dirichletSum a N s ≠ 0) :
    ∃ U : ℝ → ℝ, (∀ T, max T 0 < U T ∧ U T < max T 0 + 1) ∧
      ∀ T, RectangleIntegral' (logDeriv (dirichletSum a N))
        (⟨l, -U T⟩ : ℂ) (⟨u, U T⟩ : ℂ) =
          (verticalZeroCount a N hN ha l u (U T) : ℂ) := by
  choose U hU hU' hc using exists_arbitrarily_high_count_contour hN ha hlu hl hu
  exact ⟨U, fun T => ⟨hU T, hU' T⟩, hc⟩

/-- A contour limit is still required; this theorem supplies the actual finite-count
identity and the transfer to all heights for a derived nearby contour selection. -/
theorem exists_contour_selection_density_transfer {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ s : ℂ, s.re = l → dirichletSum a N s ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → dirichletSum a N s ≠ 0) :
    ∃ U : ℝ → ℝ, (∀ T, max T 0 < U T ∧ U T < max T 0 + 1) ∧
      (∀ T, RectangleIntegral' (logDeriv (dirichletSum a N))
        (⟨l, -U T⟩ : ℂ) (⟨u, U T⟩ : ℂ) =
          (verticalZeroCount a N hN ha l u (U T) : ℂ)) ∧
      ∀ L : ℝ,
        Tendsto (fun T => (RectangleIntegral' (logDeriv (dirichletSum a N))
          (⟨l, -U T⟩ : ℂ) (⟨u, U T⟩ : ℂ)).re / (2 * U T)) atTop (𝓝 L) →
        Tendsto (fun T => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T))
          atTop (𝓝 L) := by
  obtain ⟨U, hU, hc⟩ := exists_count_contour_height_selection hN ha hlu hl hu
  refine ⟨U, hU, hc, ?_⟩
  intro L hlim
  apply tendsto_verticalZeroCount_of_nearby_heights hN ha l u (U := U)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T ht
    have hi := hU T
    rw [max_eq_left ht] at hi
    exact ⟨hi.1.le, hi.2.le⟩
  · simpa only [hc, Complex.natCast_re] using hlim

end Dubon2026
