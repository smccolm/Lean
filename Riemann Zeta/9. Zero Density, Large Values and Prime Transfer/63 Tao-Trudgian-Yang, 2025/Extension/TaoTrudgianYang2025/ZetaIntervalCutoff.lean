import TaoTrudgianYang2025.LargeValuePattern
import GuthMaynard.DFIProposition1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Exact smooth interpolation of a coefficient-one integer interval

The transitions lie strictly between neighboring integers. Thus the
smoothed polynomial is the actual sharp polynomial, with no endpoint
error. This does not yet shift a zeta contour or bound a Mellin kernel.
-/

noncomputable section

open Finset Set
open RiemannZeta.GuthMaynard
open scoped ContDiff

namespace TaoTrudgianYang2025

def zetaIntervalCutoff (a b : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * (x - a) + 1) *
    Real.smoothTransition (2 * (b - x) + 1)

theorem zetaIntervalCutoff_nonneg (a b : ℕ) (x : ℝ) : 0 ≤ zetaIntervalCutoff a b x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem zetaIntervalCutoff_le_one (a b : ℕ) (x : ℝ) : zetaIntervalCutoff a b x ≤ 1 := by
  simpa only [one_mul] using mul_le_mul (Real.smoothTransition.le_one _)
    (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one

theorem contDiff_zetaIntervalCutoff (a b : ℕ) : ContDiff ℝ ∞ (zetaIntervalCutoff a b) :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem zetaIntervalCutoff_eq_one {a b : ℕ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ b) : zetaIntervalCutoff a b x = 1 := by
  unfold zetaIntervalCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (x - a) + 1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (b - x) + 1), one_mul]

theorem zetaIntervalCutoff_eq_zero_left {a b : ℕ} {x : ℝ}
    (h : x ≤ (a : ℝ) - 1 / 2) : zetaIntervalCutoff a b x = 0 := by
  unfold zetaIntervalCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * (x - a) + 1 ≤ 0), zero_mul]

theorem zetaIntervalCutoff_eq_zero_right {a b : ℕ} {x : ℝ}
    (h : (b : ℝ) + 1 / 2 ≤ x) : zetaIntervalCutoff a b x = 0 := by
  unfold zetaIntervalCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * (b - x) + 1 ≤ 0), mul_zero]

theorem zetaIntervalCutoff_nat (a b n : ℕ) :
    zetaIntervalCutoff a b n = if n ∈ Finset.Icc a b then 1 else 0 := by
  split_ifs with hn
  · obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hn
    exact zetaIntervalCutoff_eq_one (by exact_mod_cast ha) (by exact_mod_cast hb)
  · have hnot : n < a ∨ b < n := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hn
    rcases hnot with ha | hb
    · apply zetaIntervalCutoff_eq_zero_left
      have : (n : ℝ) + 1 ≤ a := by exact_mod_cast ha
      linarith
    · apply zetaIntervalCutoff_eq_zero_right
      have : (b : ℝ) + 1 ≤ n := by exact_mod_cast hb
      linarith

theorem support_zetaIntervalCutoff (a b : ℕ) :
    Function.support (zetaIntervalCutoff a b) ⊆ Set.Icc ((a : ℝ) - 1 / 2) ((b : ℝ) + 1 / 2) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (zetaIntervalCutoff_eq_zero_left (le_of_not_ge h))
  · by_contra h
    exact hx (zetaIntervalCutoff_eq_zero_right (le_of_not_ge h))

/-- The native smooth-test interface is instantiated from the actual
cutoff, not accepted as an analytic premise. Empty integer intervals are
allowed and still have their exact zero coefficients. -/
def zetaIntervalCutoffTest (a b : ℕ) (ha : 1 ≤ a) :
    DFIVoronoiTestFunction (fun x => (zetaIntervalCutoff a b x : ℂ)) where
  lower := (a : ℝ) - 1 / 2
  upper := max (a : ℝ) b + 1 / 2
  lower_pos := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  lower_le_upper := by have := le_max_left (a : ℝ) b; linarith
  smooth := Complex.ofRealCLM.contDiff.comp (contDiff_zetaIntervalCutoff a b)
  support_subset := by
    intro x hx
    have hreal : zetaIntervalCutoff a b x ≠ 0 := by simpa using hx
    have hs := support_zetaIntervalCutoff a b hreal
    exact ⟨hs.1, hs.2.trans (by have := le_max_right (a : ℝ) b; linarith)⟩

theorem ZetaLargeValuePattern.polynomial_eq_active_sum (P : ZetaLargeValuePattern) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      ∑ n ∈ P.active, dirichletPhase n t := by
  calc
    _ = ∑ n ∈ P.indices, if n ∈ P.active then dirichletPhase n t else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [P.coeff_eq_indicator n hn]
      split_ifs <;> simp
    _ = ∑ n ∈ P.active, dirichletPhase n t := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hn => ⟨P.active_subset hn, hn⟩⟩

/-- Any interval presentation of the active coefficients has positive
left endpoint, since zero is excluded by the real dyadic support. -/
theorem ZetaLargeValuePattern.active_left_pos (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) : 1 ≤ a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  have hzero : 0 ∈ P.active := by rw [hactive, ha0]; simp
  have hN := (P.mem_indices_iff 0).1 (P.active_subset hzero)
  norm_num at hN
  linarith [P.one_lt_N]

/-- Exact sharp-to-smooth source entry at every ordinate, not merely the
large-value set. The infinite sum has precisely the original finite support. -/
theorem ZetaLargeValuePattern.polynomial_eq_cutoff_tsum (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      ∑' n : ℕ, (zetaIntervalCutoff a b n : ℂ) * dirichletPhase n t := by
  rw [P.polynomial_eq_active_sum, hactive]
  rw [tsum_eq_sum (s := Finset.Icc a b) (fun n hn => by simp [zetaIntervalCutoff_nat, hn])]
  apply Finset.sum_congr rfl
  intro n hn
  simp [zetaIntervalCutoff_nat, hn]

theorem ZetaLargeValuePattern.active_nonempty_of_mem_ordinates (P : ZetaLargeValuePattern)
    {t : ℝ} (ht : t ∈ P.ordinates) : P.active.Nonempty := by
  by_contra h
  have hempty := Finset.not_nonempty_iff_eq_empty.mp h
  have hlarge := P.large t ht
  rw [P.polynomial_eq_active_sum, hempty, Finset.sum_empty, norm_zero] at hlarge
  exact (not_le_of_gt P.V_pos) hlarge

theorem ZetaLargeValuePattern.active_interval_bounds (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) :
    a ≤ b ∧ P.N ≤ (a : ℝ) ∧ (b : ℝ) ≤ 2 * P.N := by
  have hab : a ≤ b := Finset.nonempty_Icc.mp (hactive ▸ hne)
  have ha : a ∈ P.active := by rw [hactive]; exact Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
  have hb : b ∈ P.active := by rw [hactive]; exact Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
  exact ⟨hab, ((P.mem_indices_iff a).mp (P.active_subset ha)).1,
    ((P.mem_indices_iff b).mp (P.active_subset hb)).2⟩

/-- The sharp interval's smooth interpolation has physically linked
positive support, uniformly in every nonempty active interval. -/
theorem ZetaLargeValuePattern.cutoff_support_in_scale (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) :
    Function.support (zetaIntervalCutoff a b) ⊆ Set.Icc (P.N / 2) (3 * P.N) := by
  obtain ⟨hab, ha, hb⟩ := P.active_interval_bounds hactive hne
  intro x hx
  have hs := support_zetaIntervalCutoff a b hx
  constructor <;> linarith [hs.1, hs.2, P.one_lt_N]

end TaoTrudgianYang2025
