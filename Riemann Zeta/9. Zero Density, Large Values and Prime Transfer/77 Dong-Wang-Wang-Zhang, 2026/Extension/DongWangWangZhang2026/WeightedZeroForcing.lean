import DongWangWangZhang2026.GaussianFrequency
import DongWangWangZhang2026.ZeroRepulsion
import DongWangWangZhang2026.XiConjugation

/-!
# Actual weighted-zero forcing

The large frequency point is converted through the proved source zero
repulsion, then conjugated with every multiplicity label preserved.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex MeasureTheory
open scoped Topology

/-- A quantitatively large frequency point forces the actual convergent source zero kernel. -/
theorem exists_zero_forcing_of_weighted_frequency :
    ∃ C : ℝ, 0 < C ∧ ∀ a L t ξ : ℝ, 0 < a → a ≤ 1 / 2 → 0 < L →
      (2 * C / a) * Real.exp (a * L / 2) <
        ‖riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
          (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖ * Real.exp (-ξ ^ 2 / (4 * (a / L))) →
      Summable (fun p : XiZero =>
        a / ‖(((1 + a : ℝ) : ℂ) + ((t - ξ : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2) ∧
      L / 4 < ∑' p : XiZero,
        a / ‖(((1 + a : ℝ) : ℂ) + ((t - ξ : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
  obtain ⟨C, hC, hrep⟩ := exists_source_zero_repulsion
  refine ⟨C, hC, ?_⟩
  intro a L t ξ ha ha2 hL hpoint
  let Z := riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I)
  let d := ‖(((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖
  have hdre : 1 - a ≤ d := by
    simpa [d] using Complex.re_le_norm (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)
  have hdhalf : 1 / 2 ≤ d := by linarith
  have hd : 0 < d := by linarith
  have hg : Real.exp (-ξ ^ 2 / (4 * (a / L))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg ξ)) (by positivity)
  have hq : ‖Z‖ / d ≤ 2 * ‖Z‖ := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [norm_nonneg Z]
  have hpoint' : (C / a) * Real.exp (a * L / 2) < ‖Z‖ := by
    rw [norm_div] at hpoint
    change (2 * C / a) * Real.exp (a * L / 2) <
      (‖Z‖ / d) * Real.exp (-ξ ^ 2 / (4 * (a / L))) at hpoint
    have h := mul_le_mul_of_nonneg_left hg (div_nonneg (norm_nonneg Z) hd.le)
    simp only [mul_one] at h
    have he : (2 * C / a) * Real.exp (a * L / 2) =
        2 * ((C / a) * Real.exp (a * L / 2)) := by ring
    rw [he] at hpoint
    linarith
  let K := ∑' p : XiZero,
    a / ‖(((1 + a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2
  have hz := (hrep a (ξ - t) ha ha2).2
  have he : (∑' p : XiZero,
      2 * a ^ 2 / ‖(((1 + a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2) =
      2 * a * K := by
    dsimp only [K]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro p
    ring
  rw [he] at hz
  have hexp : Real.exp (a * L / 2) < Real.exp (2 * a * K) :=
    (mul_lt_mul_iff_right₀ (div_pos hC ha)).mp (hpoint'.trans_le hz)
  have hK : L / 4 < K := by
    have h := Real.exp_lt_exp.mp hexp
    nlinarith
  have hconj := source_zero_kernel_neg_height ha (t - ξ)
  refine ⟨hconj.1, ?_⟩
  have heq : K = ∑' p : XiZero,
      a / ‖(((1 + a : ℝ) : ℂ) + ((t - ξ : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
    simpa only [neg_sub] using hconj.2
  rwa [← heq]

/-- The sixth-power source cutoff makes the prescribed frequency threshold smaller than the integral. -/
theorem weighted_frequency_threshold_mass_lt {D a L N : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hL : 0 < L) (hN : 1 ≤ N)
    (hscale : ((128 * D ^ 2 + 1) / Real.pi) * N ^ (6 : ℕ) ≤ a * L) :
    ((2 * D / a) * Real.exp (a * L / 2)) * Real.sqrt (4 * Real.pi * (a / L)) <
      (Real.pi / (2 * N)) * Real.exp (a * L / 2) := by
  have hN0 : 0 < N := by linarith
  have hN26 : N ^ (2 : ℕ) ≤ N ^ (6 : ℕ) := pow_le_pow_right₀ hN (by decide)
  have hcore : 64 * D ^ 2 * N ^ 2 < Real.pi * (a * L) := by
    have hs : (128 * D ^ 2 + 1) * N ^ (6 : ℕ) ≤ (a * L) * Real.pi := by
      apply (div_le_iff₀ Real.pi_pos).mp
      simpa only [div_mul_eq_mul_div] using hscale
    have hmono := mul_le_mul_of_nonneg_left hN26 (by positivity : 0 ≤ 128 * D ^ 2 + 1)
    nlinarith [sq_pos_of_pos hN0, sq_nonneg D]
  have hmult := mul_lt_mul_of_pos_right hcore
    (div_pos (mul_pos Real.pi_pos ha) hL)
  have hsq : (4 * D * N * Real.sqrt (4 * Real.pi * (a / L))) ^ 2 <
      (Real.pi * a) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    convert hmult using 1
    · ring
    · field_simp
  have hroot := (sq_lt_sq₀ (by positivity : 0 ≤ 4 * D * N *
    Real.sqrt (4 * Real.pi * (a / L))) (by positivity : 0 ≤ Real.pi * a)).mp hsq
  have hratio : (2 * D / a) * Real.sqrt (4 * Real.pi * (a / L)) < Real.pi / (2 * N) := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ ha (by positivity : 0 < 2 * N)).mpr
    nlinarith only [hroot]
  have h := mul_lt_mul_of_pos_right hratio (Real.exp_pos (a * L / 2))
  convert h using 1
  ring

/-- Proposition 4.1 from the actual large sum, with one maximizing twist before every scale. -/
theorem exists_large_sum_weighted_zero_forcing :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧
      ∀ T t x N : ℝ, T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        Real.exp (Real.sqrt (Real.log T)) ≤ x → x ≤ Real.sqrt T →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          ∃ η : ℝ, |η| ≤ 2 * a * Real.sqrt (Real.log T / Real.log x) ∧
            Summable (fun p : XiZero => a /
              ‖(((1 + a : ℝ) : ℂ) + ((t - t₀ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2) ∧
            Real.log x / 4 ≤ ∑' p : XiZero, a /
              ‖(((1 + a : ℝ) : ℂ) + ((t - t₀ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
  obtain ⟨c₀, hc₀, x₀, hx₀, hfreq⟩ := exists_large_sum_gaussian_frequency_lower
  obtain ⟨C, hC, hforce⟩ := exists_zero_forcing_of_weighted_frequency
  let D := C + 121
  have hD : 0 < D := by dsimp only [D]; linarith
  let c := max c₀ ((128 * D ^ 2 + 1) / Real.pi)
  have hc : 0 < c := hc₀.trans_le (le_max_left _ _)
  have hcold : c₀ ≤ c := le_max_left _ _
  have hcnew : (128 * D ^ 2 + 1) / Real.pi ≤ c := le_max_right _ _
  refine ⟨c, max 3 (Real.exp (x₀ ^ 2)), hc, le_max_left _ _, ?_⟩
  intro T t x N hT₀ htlow httop hxlow hxtop hN hNtop hsum
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hT₀
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hQT : x₀ ^ 2 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos (x₀ ^ 2)) ((le_max_right _ _).trans hT₀)
    simpa only [Real.log_exp] using h
  have hroot : x₀ ≤ Real.sqrt (Real.log T) := by
    have h := Real.sqrt_le_sqrt hQT
    simpa only [Real.sqrt_sq (by linarith : 0 ≤ x₀)] using h
  have hxx₀ : x₀ ≤ x := (Real.le_exp_self x₀).trans
    ((Real.exp_le_exp.mpr hroot).trans hxlow)
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxT : x ≤ T := hxtop.trans (Real.sqrt_le_iff.mpr ⟨hT0.le, by nlinarith⟩)
  have hLT : Real.log x ≤ T := by linarith [Real.log_le_sub_one_of_pos hx0]
  obtain ⟨t₀, ht₀, hmax, hdisplace, hint⟩ :=
    hfreq x hxx₀ t N (hxT.trans htlow) hN hNtop hsum
  have hN0 : 0 < N := by linarith
  have hheight : |t - t₀| ≤ 3 * T := by
    have h := abs_sub t t₀
    linarith
  refine ⟨t₀, ht₀, hmax, hdisplace.trans (mul_le_mul_of_nonneg_right hcold hN0.le), ?_⟩
  intro a halow ha2
  have ha : 0 < a := (div_pos (mul_pos hc (pow_pos hN0 _)) hL).trans_le halow
  have halow₀ : c₀ * N ^ (6 : ℕ) / Real.log x ≤ a :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcold (by positivity)) hL.le).trans halow
  have hscale : ((128 * D ^ 2 + 1) / Real.pi) * N ^ (6 : ℕ) ≤ a * Real.log x :=
    (mul_le_mul_of_nonneg_right hcnew (by positivity)).trans ((div_le_iff₀ hL).mp halow)
  have hmass := weighted_frequency_threshold_mass_lt hD ha hL hN hscale
  have hi := (hint a halow₀ ha2).2
  obtain ⟨ξ, hpoint⟩ := exists_zeta_gaussian_frequency_gt a (t - t₀) (a / Real.log x)
    ((2 * D / a) * Real.exp (a * Real.log x / 2)) (div_pos ha hL) (hmass.trans_le hi)
  have hExp : 1 ≤ Real.exp (a * Real.log x / 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hM : 120 / a ≤ (2 * D / a) * Real.exp (a * Real.log x / 2) := by
    apply (div_le_div_of_nonneg_right (by dsimp only [D]; linarith : (120 : ℝ) ≤ 2 * D) ha.le).trans
    exact le_mul_of_one_le_right (by positivity) hExp
  have hξ : |ξ| < 2 * a * Real.sqrt (Real.log T / Real.log x) := by
    by_contra hn
    have htail := source_gaussian_weighted_zeta_tail ha ha2 hL hT1 hheight (le_of_not_gt hn)
    linarith
  have hforcing := hforce a (Real.log x) (t - t₀) ξ ha ha2 hL
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by dsimp only [D]; linarith : 2 * C ≤ 2 * D) ha.le)
      (Real.exp_pos _).le) hpoint)
  refine ⟨-ξ, by simpa only [abs_neg] using hξ.le, ?_⟩
  simpa only [sub_eq_add_neg] using And.intro hforcing.1 hforcing.2.le

end
end DongWangWangZhang2026
