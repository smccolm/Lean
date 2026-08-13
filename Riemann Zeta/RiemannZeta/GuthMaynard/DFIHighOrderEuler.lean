import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Floor
import RiemannZeta.GuthMaynard.DFIPsi

open Set
open scoped BigOperators ContDiff Interval

namespace RiemannZeta.GuthMaynard

/-!
# High-order Euler--Maclaurin for DFI equation (12)

The proof is developed cell by cell.  On `[n,n+1)` the periodized Bernoulli
function is an ordinary Bernoulli polynomial, so integration by parts is
classical and all interior boundary terms telescope exactly.
-/

/-- The polynomial representative of `dfiPsi j` on the integer cell
`[n,n+1)`. -/
noncomputable def dfiPsiCell (j n : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun j (x - n) / j.factorial

/-- On an integer cell the local polynomial and the periodized function
agree pointwise away from the right endpoint. -/
theorem dfiPsiCell_eq_dfiPsi {j n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ)) :
    dfiPsiCell j n x = dfiPsi j x := by
  have hfloor : ⌊x⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, by simpa using hx.2⟩
  simp only [dfiPsiCell, dfiPsi, Int.fract, hfloor, Int.cast_natCast]

/-- The derivative recurrence for the local Bernoulli representatives. -/
theorem hasDerivAt_dfiPsiCell_succ (j n : ℕ) (x : ℝ) :
    HasDerivAt (dfiPsiCell (j + 1) n) (dfiPsiCell j n x) x := by
  have hinner : HasDerivAt (fun y : ℝ => y - n) 1 x :=
    hasDerivAt_id x |>.sub_const (n : ℝ)
  have hbern := (hasDerivAt_bernoulliFun (j + 1) (x - n)).comp x hinner
  have hdiv := hbern.div_const ((j + 1).factorial : ℝ)
  convert hdiv using 1
  simp only [dfiPsiCell, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.add_sub_cancel, mul_one]
  field_simp

/-- One integration-by-parts step on a single integer cell.  This is the
local identity from which the arbitrary-order Euler--Maclaurin remainder is
assembled. -/
theorem integral_dfiPsiCell_mul_iteratedDeriv_succ
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j n : ℕ) :
    (∫ x in (n : ℝ)..(n + 1 : ℝ),
        dfiPsiCell (j + 1) n x * iteratedDeriv (j + 1) g x) =
      dfiPsiCell (j + 1) n (n + 1) * iteratedDeriv j g (n + 1) -
        dfiPsiCell (j + 1) n n * iteratedDeriv j g n -
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            dfiPsiCell j n x * iteratedDeriv j g x := by
  have hgDiff : Differentiable ℝ (iteratedDeriv j g) :=
    hg.differentiable_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top j))
  have hv (x : ℝ) : HasDerivAt (iteratedDeriv j g)
      (iteratedDeriv (j + 1) g x) x := by
    rw [iteratedDeriv_succ]
    exact (hgDiff x).hasDerivAt
  have huInt : IntervalIntegrable (dfiPsiCell j n) MeasureTheory.volume
      (n : ℝ) (n + 1 : ℝ) :=
    (by
      unfold dfiPsiCell
      fun_prop : Continuous (dfiPsiCell j n)).intervalIntegrable _ _
  have hvInt : IntervalIntegrable (iteratedDeriv (j + 1) g) MeasureTheory.volume
      (n : ℝ) (n + 1 : ℝ) :=
    (hg.continuous_iteratedDeriv (j + 1)
      (WithTop.coe_le_coe.mpr
        (le_of_lt (ENat.coe_lt_top (j + 1))))).intervalIntegrable _ _
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _hx => hasDerivAt_dfiPsiCell_succ j n x)
    (fun x _hx => hv x) huInt hvInt

/-- Replacing the cell polynomial by the periodized function does not alter
an interval integral.  The right endpoint is the sole possible discrepancy
and has Lebesgue measure zero. -/
theorem integral_dfiPsiCell_mul_eq_dfiPsi_mul
    (j n : ℕ) (h : ℝ → ℝ) :
    (∫ x in (n : ℝ)..(n + 1 : ℝ), dfiPsiCell j n x * h x) =
      ∫ x in (n : ℝ)..(n + 1 : ℝ), dfiPsi j x * h x := by
  apply intervalIntegral.integral_congr_ae
  have hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ (n + 1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx hmem
  have hmem' : x ∈ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
    simpa [Set.uIoc_of_le (by norm_num : (n : ℝ) ≤ n + 1)] using hmem
  have hxIco : x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ) :=
    ⟨hmem'.1.le, lt_of_le_of_ne hmem'.2 hx⟩
  rw [dfiPsiCell_eq_dfiPsi hxIco]

/-- The integration-by-parts recurrence on one cell, stated with the global
periodized functions.  Boundary values deliberately retain the local
polynomial convention so they telescope in the next theorem. -/
theorem integral_dfiPsi_mul_iteratedDeriv_succ_cell
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j n : ℕ) :
    (∫ x in (n : ℝ)..(n + 1 : ℝ),
        dfiPsi (j + 1) x * iteratedDeriv (j + 1) g x) =
      dfiPsiCell (j + 1) n (n + 1) * iteratedDeriv j g (n + 1) -
        dfiPsiCell (j + 1) n n * iteratedDeriv j g n -
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            dfiPsi j x * iteratedDeriv j g x := by
  rw [← integral_dfiPsiCell_mul_eq_dfiPsi_mul (j + 1) n
      (iteratedDeriv (j + 1) g),
    ← integral_dfiPsiCell_mul_eq_dfiPsi_mul j n (iteratedDeriv j g)]
  exact integral_dfiPsiCell_mul_iteratedDeriv_succ g hg j n

/-- An interval with natural endpoints is the exact sum of its unit-cell
integrals. -/
theorem sum_intervalIntegral_nat_cells (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b)
    (R : ℕ) :
    (∑ n ∈ Finset.range R,
        ∫ x in (n : ℝ)..(n + 1 : ℝ), f x) =
      ∫ x in (0 : ℝ)..R, f x := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hf 0 R) (hf R (R + 1))]
      norm_num

/-- The periodized Bernoulli representative is measurable. -/
theorem measurable_dfiPsi (j : ℕ) : Measurable (dfiPsi j) := by
  unfold dfiPsi
  have hb : Measurable (bernoulliFun j) :=
    (by fun_prop : Continuous (bernoulliFun j)).measurable
  fun_prop

/-- A periodized Bernoulli factor times a continuous function is integrable
on every compact interval. -/
theorem intervalIntegrable_dfiPsi_mul_continuous
    (j : ℕ) (h : ℝ → ℝ) (hh : Continuous h) (a b : ℝ) :
    IntervalIntegrable (fun x => dfiPsi j x * h x)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff']
  obtain ⟨C, hCpos, hC⟩ := exists_bound_dfiPsi j
  have hcompact : IsCompact (Set.uIcc a b) := isCompact_uIcc
  obtain ⟨D, hD⟩ := hcompact.bddAbove_image hh.abs.continuousOn
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (by simp) ?_ (M := C * max 0 D) ?_
  · exact ((measurable_dfiPsi j).mul hh.measurable).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIcc]
      with x hx
    have hhx : |h x| ≤ D := hD ⟨x, hx, rfl⟩
    have hhx' : |h x| ≤ max 0 D := hhx.trans (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC x) hhx' (abs_nonneg _) hCpos.le

/-- For order at least two the Bernoulli polynomial has matching cell
endpoint values, which is the exact telescoping condition. -/
theorem dfiPsiCell_succ_endpoint_eq (j n : ℕ) (hj : 1 ≤ j) :
    dfiPsiCell (j + 1) n (n + 1) = dfiPsiCell (j + 1) n n := by
  unfold dfiPsiCell
  have hne : j + 1 ≠ 1 := by omega
  rw [show (n : ℝ) + 1 - n = 1 by ring,
    sub_self, bernoulliFun_endpoints_eq_of_ne_one hne]

/-- The elementary finite telescoping identity used for all cell boundary
terms. -/
theorem sum_range_succ_sub (u : ℕ → ℝ) (R : ℕ) :
    (∑ n ∈ Finset.range R, (u (n + 1) - u n)) = u R - u 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Raising the Euler--Maclaurin remainder order by one negates the
periodized-Bernoulli integral when the relevant endpoint derivative
vanishes.  This is the telescoping engine for DFI equation (12). -/
theorem integral_dfiPsi_iteratedDeriv_succ_eq_neg
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j R : ℕ) (hj : 1 ≤ j)
    (h0 : iteratedDeriv j g 0 = 0)
    (hR : iteratedDeriv j g R = 0) :
    (∫ x in (0 : ℝ)..R,
        dfiPsi (j + 1) x * iteratedDeriv (j + 1) g x) =
      -(∫ x in (0 : ℝ)..R, dfiPsi j x * iteratedDeriv j g x) := by
  have hcont (k : ℕ) : Continuous (iteratedDeriv k g) :=
    hg.continuous_iteratedDeriv k
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have hint (k : ℕ) (a b : ℝ) :
      IntervalIntegrable (fun x => dfiPsi k x * iteratedDeriv k g x)
        MeasureTheory.volume a b :=
    intervalIntegrable_dfiPsi_mul_continuous k _ (hcont k) a b
  rw [← sum_intervalIntegral_nat_cells
      (fun x => dfiPsi (j + 1) x * iteratedDeriv (j + 1) g x)
      (hint (j + 1)) R,
    ← sum_intervalIntegral_nat_cells
      (fun x => dfiPsi j x * iteratedDeriv j g x) (hint j) R]
  let H : ℕ → ℝ := fun n => iteratedDeriv j g n
  let c : ℝ := bernoulliFun (j + 1) 0 / (j + 1).factorial
  have hboundary (n : ℕ) :
      dfiPsiCell (j + 1) n (n + 1) * H (n + 1) -
          dfiPsiCell (j + 1) n n * H n =
        c * (H (n + 1) - H n) := by
    rw [dfiPsiCell_succ_endpoint_eq j n hj]
    have hleft : dfiPsiCell (j + 1) n n = c := by
      simp [dfiPsiCell, c]
    rw [hleft]
    ring
  have hboundarySum :
      (∑ n ∈ Finset.range R,
        (dfiPsiCell (j + 1) n (n + 1) * H (n + 1) -
          dfiPsiCell (j + 1) n n * H n)) = 0 := by
    calc
      _ = c * ∑ n ∈ Finset.range R, (H (n + 1) - H n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        exact hboundary n
      _ = c * (H R - H 0) := by rw [sum_range_succ_sub]
      _ = 0 := by simp [H, h0, hR]
  calc
    (∑ n ∈ Finset.range R,
        ∫ x in (n : ℝ)..(n + 1 : ℝ),
          dfiPsi (j + 1) x * iteratedDeriv (j + 1) g x) =
        ∑ n ∈ Finset.range R,
          ((dfiPsiCell (j + 1) n (n + 1) * H (n + 1) -
              dfiPsiCell (j + 1) n n * H n) -
            ∫ x in (n : ℝ)..(n + 1 : ℝ),
              dfiPsi j x * iteratedDeriv j g x) := by
          apply Finset.sum_congr rfl
          intro n _hn
          simpa [H] using
            integral_dfiPsi_mul_iteratedDeriv_succ_cell g hg j n
    _ = (∑ n ∈ Finset.range R,
          (dfiPsiCell (j + 1) n (n + 1) * H (n + 1) -
            dfiPsiCell (j + 1) n n * H n)) -
        ∑ n ∈ Finset.range R,
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            dfiPsi j x * iteratedDeriv j g x := by
          rw [Finset.sum_sub_distrib]
    _ = -(∑ n ∈ Finset.range R,
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            dfiPsi j x * iteratedDeriv j g x) := by
          rw [hboundarySum, zero_sub]

/-- High-order Euler--Maclaurin with vanishing endpoint jets.  This is the
exact form used twice in the proof of DFI equation (12). -/
theorem dfi_high_order_euler_maclaurin
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (R j : ℕ) (hj : 1 ≤ j)
    (hend : ∀ k : ℕ,
      iteratedDeriv k g 0 = 0 ∧ iteratedDeriv k g R = 0) :
    (∑ r ∈ Finset.Ioc 0 R, g r) =
      (∫ x in (0 : ℝ)..R, g x) +
        (-1 : ℝ) ^ (j + 1) *
          ∫ x in (0 : ℝ)..R, dfiPsi j x * iteratedDeriv j g x := by
  let P : ℕ → Prop := fun k =>
    (∑ r ∈ Finset.Ioc 0 R, g r) =
      (∫ x in (0 : ℝ)..R, g x) +
        (-1 : ℝ) ^ (k + 1) *
          ∫ x in (0 : ℝ)..R, dfiPsi k x * iteratedDeriv k g x
  have hbase : P 1 := by
    have hgDiff : Differentiable ℝ g := hg.differentiable (by simp)
    have hgDeriv : Continuous (deriv g) := hg.continuous_deriv (by simp)
    have hEM := sum_eq_integral_add_integral_deriv
      (f := g) (a := (0 : ℝ)) (b := (R : ℝ))
      (by norm_num) (Nat.cast_nonneg R)
      (fun x _hx => hgDiff x) hgDeriv.continuousOn
    have hpsi :
        (∫ x in (0 : ℝ)..R, deriv g x * B1 x) =
          ∫ x in (0 : ℝ)..R, dfiPsi 1 x * iteratedDeriv 1 g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) R := by
        simpa [Set.uIcc_of_le (Nat.cast_nonneg R)] using hx
      change deriv g x * B1 x = dfiPsi 1 x * iteratedDeriv 1 g x
      rw [dfiPsi_one_eq_B1 x hx'.1]
      simp [iteratedDeriv_succ, mul_comm]
    obtain ⟨hg0, hgR⟩ := hend 0
    have hg0' : g 0 = 0 := by simpa using hg0
    have hgR' : g R = 0 := by simpa using hgR
    have hEM' :
        (∑ r ∈ Finset.Ioc 0 R, g r) =
          (∫ x in (0 : ℝ)..R, g x) +
            ∫ x in (0 : ℝ)..R, deriv g x * B1 x := by
      simpa [hg0', hgR'] using hEM
    dsimp [P]
    rw [hpsi] at hEM'
    simpa using hEM'
  have hstep : ∀ k : ℕ, 1 ≤ k → P k → P (k + 1) := by
    intro k hk hPk
    obtain ⟨hk0, hkR⟩ := hend k
    have hrec := integral_dfiPsi_iteratedDeriv_succ_eq_neg
      g hg k R hk hk0 hkR
    dsimp [P] at hPk ⊢
    rw [hrec]
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
    nlinarith
  exact Nat.le_induction hbase hstep j hj

end RiemannZeta.GuthMaynard
