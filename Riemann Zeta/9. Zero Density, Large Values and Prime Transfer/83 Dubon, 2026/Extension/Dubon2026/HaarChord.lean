import Dubon2026.GridProductBounds

/-! # Chord bounds for the Haar logarithmic potential -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

theorem haarLogPotential_le_grid_chord {a : ℕ → ℂ} {N m : ℕ} [NeZero m]
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u σ : ℝ} (hlu : l < u) (hσ : σ ∈ Icc l u)
    {εl εu A B : ℝ} (hεl : 0 < εl) (hεu : 0 < εu)
    (hl : ∀ z : PrimeTorus N, (∑ j : PrimeCoordinate N → ZMod m,
      Real.log (max ‖bohrOnTorus a N l (z + torusGridPoint N m j)‖ εl)) ≤
        (Fintype.card (PrimeCoordinate N → ZMod m) : ℝ) * A)
    (hu : ∀ z : PrimeTorus N, (∑ j : PrimeCoordinate N → ZMod m,
      Real.log (max ‖bohrOnTorus a N u (z + torusGridPoint N m j)‖ εu)) ≤
        (Fintype.card (PrimeCoordinate N → ZMod m) : ℝ) * B) :
    haarLogPotential a N σ ≤ (1 - (σ - l) / (u - l)) * A + ((σ - l) / (u - l)) * B := by
  classical
  let q : ℝ := Fintype.card (PrimeCoordinate N → ZMod m)
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PrimeCoordinate N → ZMod m))
  have hne : ∀ᵐ z ∂torusHaar N, ∀ j : PrimeCoordinate N → ZMod m,
      bohrOnTorus a N σ (z + torusGridPoint N m j) ≠ 0 :=
    ae_all_iff.mpr (fun j => translated_bohr_ne_zero_ae hN ha σ (torusGridPoint N m j))
  have hb : ∀ᵐ z ∂torusHaar N,
      Real.log ‖∏ j : PrimeCoordinate N → ZMod m,
        bohrOnTorus a N σ (z + torusGridPoint N m j)‖ ≤
          q * ((1 - (σ - l) / (u - l)) * A + ((σ - l) / (u - l)) * B) := by
    filter_upwards [hne] with z hz
    have hp : twistProduct a N (fun j => z + torusGridPoint N m j) σ ≠ 0 := by
      rw [twistProduct_real]
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => hz j)
    have h := log_norm_twistProduct_le_three_lines a N
      (fun j => z + torusGridPoint N m j) hlu hσ
      (fun s hs => grid_twistProduct_boundary_bound a N m l (q * A) hεl hl z s hs)
      (fun s hs => grid_twistProduct_boundary_bound a N m u (q * B) hεu hu z s hs) hp
    rw [twistProduct_real] at h
    convert h using 1
    ring
  have hi := integral_mono_ae
    (integrable_log_norm_translated_bohr_product hN ha σ (torusGridPoint N m))
    (integrable_const (q * ((1 - (σ - l) / (u - l)) * A + ((σ - l) / (u - l)) * B))) hb
  rw [integral_log_norm_translated_bohr_product hN ha σ, integral_const, probReal_univ, one_smul] at hi
  exact (mul_le_mul_iff_right₀ hq).mp hi

theorem exists_truncation_integral_lt_haar_add {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N) < haarLogPotential a N σ + δ := by
  have he := (tendsto_order.mp (tendsto_haar_truncated_log hN ha σ)).2
    (haarLogPotential a N σ + δ) (by linarith)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  exact (hpos.and he).exists

theorem haarLogPotential_le_chord {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u σ : ℝ} (hlu : l < u) (hσ : σ ∈ Icc l u) :
    haarLogPotential a N σ ≤
      (1 - (σ - l) / (u - l)) * haarLogPotential a N l +
        ((σ - l) / (u - l)) * haarLogPotential a N u := by
  have hθ0 : 0 ≤ (σ - l) / (u - l) := div_nonneg (sub_nonneg.mpr hσ.1) (sub_pos.mpr hlu).le
  have hθ1 : (σ - l) / (u - l) ≤ 1 := (div_le_one (sub_pos.mpr hlu)).mpr (by linarith [hσ.2])
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨εl, hεl, hl⟩ := exists_truncation_integral_lt_haar_add hN ha l (half_pos hδ)
  obtain ⟨εu, hεu, hu⟩ := exists_truncation_integral_lt_haar_add hN ha u (half_pos hδ)
  obtain ⟨n, hgl, hgu⟩ := ((eventually_grid_truncated_log_le a N l hεl (half_pos hδ)).and
    (eventually_grid_truncated_log_le a N u hεu (half_pos hδ))).exists
  have h := haarLogPotential_le_grid_chord hN ha hlu hσ hεl hεu hgl hgu
  have hl' : (∫ z, Real.log (max ‖bohrOnTorus a N l z‖ εl) ∂torusHaar N) + δ / 2 ≤
      haarLogPotential a N l + δ := by linarith
  have hu' : (∫ z, Real.log (max ‖bohrOnTorus a N u z‖ εu) ∂torusHaar N) + δ / 2 ≤
      haarLogPotential a N u + δ := by linarith
  have hb := add_le_add (mul_le_mul_of_nonneg_left hl' (sub_nonneg.mpr hθ1))
    (mul_le_mul_of_nonneg_left hu' hθ0)
  exact (h.trans hb).trans_eq (by ring)

end

end Dubon2026
