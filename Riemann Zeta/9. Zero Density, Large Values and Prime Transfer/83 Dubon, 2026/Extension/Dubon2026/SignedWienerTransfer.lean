import GafniTao.WienerSource
import Mathlib.NumberTheory.LSeries.Linearity

/-! # Signed Wiener--Ikehara transfer dominated by the actual von Mangoldt function

The nonnegative Tauberian theorem and actual zeta boundary regular part are
reused from the repository's audited node-63 Wiener source. The signed series
must have its own displayed continuous boundary extension.
-/

namespace Dubon2026

open Filter Set ArithmeticFunction
open scoped Topology

noncomputable section

/-- Domination by the true von Mangoldt coefficients gives absolute convergence on Re(s)>1. -/
theorem lseriesSummable_of_abs_le_vonMangoldt {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C * vonMangoldt n) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (a n : ℂ)) s := by
  have hv := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  apply Summable.of_norm
  apply (hv.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, mul_zero, le_refl]
  · simp only [LSeries.term_def, if_neg hn, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg (n := n))]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (ha n) (norm_nonneg ((n : ℂ) ^ s))

/-- The actual von Mangoldt Chebyshev estimate supplies the absolute coefficient bound required by Wiener--Ikehara. -/
theorem cheby_of_abs_le_vonMangoldt {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C * vonMangoldt n) : cheby (fun n => (a n : ℂ)) := by
  obtain ⟨B,hB⟩ := vonMangoldt_cheby
  refine ⟨C * B, fun N => ?_⟩
  calc
    cumsum (fun n => ‖(a n : ℂ)‖) N ≤ C * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      simp only [cumsum, Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (vonMangoldt_nonneg (n := _))]
      exact Finset.sum_le_sum (fun n _ => ha n)
    _ ≤ C * (B * N) := mul_le_mul_of_nonneg_left (hB N) hC
    _ = _ := by ring

/-- The already proved zeta boundary regular part equals the actual von Mangoldt L-series with its simple pole removed. -/
theorem vonMangoldt_regularPart_eq {s : ℂ} (hs : 1 < s.re) :
    vonMangoldt.LFunctionResidueClassAux (q := 1) 1 s =
      LSeries (fun n => (vonMangoldt n : ℂ)) s - 1 / (s - 1) := by
  have he := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
  simp only [he, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one,
    one_div, sub_left_inj]
  apply LSeries_congr
  intro n _
  simp only [Complex.ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
  exact fun hn => absurd (Subsingleton.eq_one _) hn

/-- A signed coefficient sequence dominated by actual von Mangoldt coefficients has zero mean when its own Dirichlet series extends continuously to Re(s)=1. -/
theorem signed_wiener_vonMangoldt_cancellation {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C * vonMangoldt n) (G : ℂ → ℂ)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hseries : Set.EqOn G (LSeries (fun n => (a n : ℂ))) {s | 1 < s.re}) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / (N : ℝ)) atTop (𝓝 0) := by
  let b : ℕ → ℝ := fun n => a n + C * vonMangoldt n
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    dsimp only [b]
    have he := (abs_le.mp (ha n)).1
    linarith
  have hb : ∀ n, |b n| ≤ (2 * C) * vonMangoldt n := by
    intro n
    rw [abs_of_nonneg (hb0 n)]
    dsimp only [b]
    have he := (abs_le.mp (ha n)).2
    linarith
  let F : ℂ → ℂ := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hF : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have hbseries : ∀ σ : ℝ, 1 < σ → Summable (nterm (fun n => (b n : ℂ)) σ) := by
    intro σ hσ
    simpa only [← nterm_eq_norm_term] using
      (lseriesSummable_of_abs_le_vonMangoldt hb (s := (σ : ℂ)) (by simpa using hσ)).norm
  have hcont : ContinuousOn (fun s => G s + (C : ℂ) * F s) {s | 1 ≤ s.re} :=
    hG.add (continuousOn_const.mul hF)
  have hident : Set.EqOn (fun s => G s + (C : ℂ) * F s)
      (fun s => LSeries (fun n => (b n : ℂ)) s - (C : ℂ) / (s - 1)) {s | 1 < s.re} := by
    intro s hs
    dsimp only
    have he : (fun n => (b n : ℂ)) =
        (fun n => (a n : ℂ)) + (C : ℂ) • (fun n => (vonMangoldt n : ℂ)) := by
      funext n
      simp [b]
    rw [he, LSeries_add (lseriesSummable_of_abs_le_vonMangoldt ha hs)
      ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (C : ℂ)), LSeries_smul,
      hseries hs, show F s = LSeries (fun n => (vonMangoldt n : ℂ)) s - 1 / (s - 1) from
        vonMangoldt_regularPart_eq hs]
    ring
  have hw := WienerIkeharaTheorem' hb0 hbseries
    (cheby_of_abs_le_vonMangoldt (by positivity : 0 ≤ 2 * C) hb) hcont hident
  have ht : Tendsto (fun N : ℕ => cumsum b N / (N : ℝ) - C * (cumsum vonMangoldt N / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_one, sub_self] using hw.sub (WeakPNT.const_mul C)
  apply ht.congr
  intro N
  simp only [cumsum, b, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
  ring

end
end Dubon2026
