import Dubon2026.HigherRolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # A real exponential sum has fewer ordered zeros than nonzero terms

Rolle induction supplies the nonoscillation input for horizontal argument bounds.
All frequencies, coefficients and function values in the statement are literal.
-/

namespace Dubon2026

open Set

noncomputable section

/-- The actual finite real exponential sum. -/
def realExponentialSum {ι : Type*} (s : Finset ι) (c ω : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, c i * Real.exp (ω i * x)

theorem hasDerivAt_realExponentialSum {ι : Type*} (s : Finset ι) (c ω : ι → ℝ) (x : ℝ) :
    HasDerivAt (realExponentialSum s c ω)
      (realExponentialSum s (fun i => c i * ω i) ω x) x := by
  have hh (i : ι) : HasDerivAt (fun y : ℝ => c i * Real.exp (ω i * y))
      (c i * ω i * Real.exp (ω i * x)) x := by
    convert ((hasDerivAt_id x).const_mul (ω i)).exp.const_mul (c i) using 1
    simp only [id_eq]
    ring
  exact HasDerivAt.fun_sum (fun i (_ : i ∈ s) => hh i)

theorem realExponentialSum_sub_coeff {ι : Type*} (s : Finset ι)
    (c ω : ι → ℝ) (v x : ℝ) :
    realExponentialSum s (fun i => c i * (ω i - v)) ω x =
      realExponentialSum s (fun i => c i * ω i) ω x - v * realExponentialSum s c ω x := by
  unfold realExponentialSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_scaled_realExponentialSum {ι : Type*} (s : Finset ι)
    (c ω : ι → ℝ) (v x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-v * y) * realExponentialSum s c ω y)
      (Real.exp (-v * x) * realExponentialSum s (fun i => c i * (ω i - v)) ω x) x := by
  have hh := ((hasDerivAt_id x).const_mul (-v)).exp.mul
    (hasDerivAt_realExponentialSum s c ω x)
  convert hh using 1
  rw [realExponentialSum_sub_coeff]
  simp only [id_eq]
  ring

theorem realExponentialSum_not_zero_at_all_ordered_points {ι : Type*} (s : Finset ι) :
    ∀ c ω : ι → ℝ, s.Nonempty → (∀ i ∈ s, c i ≠ 0) → Set.InjOn ω s →
      ∀ x : Fin s.card → ℝ, StrictMono x → ¬ ∀ j, realExponentialSum s c ω (x j) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro c ω hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro c ω _ hc hω
    rw [Finset.card_insert_of_notMem ha]
    intro x hx hz
    by_cases hs : s = ∅
    · subst s
      have hz0 := hz 0
      have hc0 := hc a (Finset.mem_insert_self _ _)
      simp only [realExponentialSum, Finset.sum_insert ha, Finset.sum_empty, add_zero] at hz0
      exact (mul_ne_zero hc0 (Real.exp_pos _).ne') hz0
    · let g : ℝ → ℝ := fun y => Real.exp (-(ω a) * y) *
        realExponentialSum (insert a s) c ω y
      have hgzero (j) : g (x j) = 0 := by simp only [g, hz j, mul_zero]
      have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_scaled_realExponentialSum (insert a s) c ω (ω a) t).continuousAt
      have hgderiv (t : ℝ) : deriv g t = Real.exp (-(ω a) * t) *
          realExponentialSum s (fun i => c i * (ω i - ω a)) ω t := by
        simpa only [realExponentialSum, Finset.sum_insert ha, sub_self, mul_zero, zero_mul,
          zero_add, g] using
          (hasDerivAt_scaled_realExponentialSum (insert a s) c ω (ω a) t).deriv
      have hbetween (i : Fin s.card) :
          ∃ t ∈ Ioo (x i.castSucc) (x i.succ), deriv g t = 0 := by
        apply exists_deriv_eq_zero (hx Fin.castSucc_lt_succ) hgc.continuousOn
        rw [hgzero, hgzero]
      choose y hy hyzero using hbetween
      have hymono : StrictMono y := by
        intro i j hij
        have hm : x i.succ ≤ x j.castSucc := hx.monotone (by simpa using hij)
        exact (hy i).2.trans_le hm |>.trans (hy j).1
      have hyG (i : Fin s.card) : realExponentialSum s
          (fun j => c j * (ω j - ω a)) ω (y i) = 0 := by
        have hh := hyzero i
        rw [hgderiv] at hh
        exact (mul_eq_zero.mp hh).resolve_left (Real.exp_pos _).ne'
      have hc' : ∀ i ∈ s, c i * (ω i - ω a) ≠ 0 := by
        intro i hi
        apply mul_ne_zero (hc i (Finset.mem_insert_of_mem hi))
        apply sub_ne_zero.mpr
        intro he
        have heq := hω (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self _ _) he
        exact ha (heq ▸ hi)
      exact ih (fun i => c i * (ω i - ω a)) ω (Finset.nonempty_iff_ne_empty.mpr hs) hc'
        (hω.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)) y hymono hyG

end

end Dubon2026
