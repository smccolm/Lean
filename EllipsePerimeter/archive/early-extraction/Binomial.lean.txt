import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

-- Note: Adjust this import to match your project's path to Module A.
import EllipsePerimeter.Wallis

noncomputable section

namespace EllipseOmega

/-!
# THE MASTER BLUEPRINT: A Mechanized Ellipse Perimeter
## MODULE B: The Analytic Core (The Binomial IVT Hack)

Purpose: Prove that `S(x) = ∑ a_n x^n = sqrt(1 - x)` strictly for `x ∈ (-1, 1)`,
using combinatorial algebra and topology, bypassing complex analysis entirely.
-/

-- 1. Absolute Summability:

def sqrtOneSubSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  sqrtOneSubCoeff n * x ^ n

def sqrtOneSubSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, sqrtOneSubSeriesTerm x n

def sqrtOneSubSeriesTarget (x : ℝ) : Prop :=
  Real.sqrt (1 - x) = sqrtOneSubSeries x

theorem abs_sqrtOneSubCoeffRatio_le_one (n : ℕ) :
    |((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2))| ≤ 1 := by
  have hnum : |2 * (n : ℝ) - 1| ≤ 2 * (n : ℝ) + 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hden_nonneg : 0 ≤ 2 * (n : ℝ) + 2 := by positivity
  have hden_pos : 0 < 2 * (n : ℝ) + 2 := by positivity
  have hden_ne : 2 * (n : ℝ) + 2 ≠ 0 := ne_of_gt hden_pos
  have haux :
      |2 * (n : ℝ) - 1| / (2 * (n : ℝ) + 2) ≤
        (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 2) := by
    exact div_le_div_of_nonneg_right hnum hden_nonneg
  calc
    |((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2))|
        = |2 * (n : ℝ) - 1| / (2 * (n : ℝ) + 2) := by
            rw[abs_div, abs_of_nonneg hden_nonneg]
    _ ≤ (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 2) := haux
    _ = 1 := by field_simp [hden_ne]

theorem sqrtOneSubSeriesTerm_succ_eq_ratio_mul (x : ℝ) (n : ℕ) :
    sqrtOneSubSeriesTerm x (n + 1) =
      (((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2)) * x) *
        sqrtOneSubSeriesTerm x n := by
  unfold sqrtOneSubSeriesTerm
  rw [sqrtOneSubCoeff_succ, pow_succ]
  ring

theorem abs_sqrtOneSubSeriesTerm_succ (x : ℝ) (n : ℕ) :
    |sqrtOneSubSeriesTerm x (n + 1)| =
      |((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2) * x)| *
        |sqrtOneSubSeriesTerm x n| := by
  rw[sqrtOneSubSeriesTerm_succ_eq_ratio_mul]
  rw [abs_mul]

theorem norm_sqrtOneSubSeriesTerm_succ_le_abs_mul (x : ℝ) (n : ℕ) :
    ‖sqrtOneSubSeriesTerm x (n + 1)‖ ≤
      |x| * ‖sqrtOneSubSeriesTerm x n‖ := by
  rw[Real.norm_eq_abs, Real.norm_eq_abs, abs_sqrtOneSubSeriesTerm_succ]
  have hr :
      |((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2) * x)| ≤ |x| := by
    rw [abs_mul]
    calc
      |(2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2)| * |x|
          ≤ 1 * |x| := by
            exact mul_le_mul_of_nonneg_right
              (abs_sqrtOneSubCoeffRatio_le_one n) (abs_nonneg x)
      _ = |x| := by ring
  exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)

theorem sqrtOneSubSeriesSummable_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => sqrtOneSubSeriesTerm x n) := by
  have hratio :
      ∀ᶠ n : ℕ in Filter.atTop,
        ‖sqrtOneSubSeriesTerm x (n + 1)‖ ≤
          |x| * ‖sqrtOneSubSeriesTerm x n‖ := by
    exact Filter.Eventually.of_forall (norm_sqrtOneSubSeriesTerm_succ_le_abs_mul x)
  exact summable_of_ratio_norm_eventually_le hx hratio

theorem sqrtOneSubSeries_abs_summable_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => |sqrtOneSubSeriesTerm x n|) := by
  have hratio :
      ∀ᶠ n : ℕ in Filter.atTop,
        ‖|sqrtOneSubSeriesTerm x (n + 1)|‖ ≤
          |x| * ‖|sqrtOneSubSeriesTerm x n|‖ := by
    exact Filter.Eventually.of_forall (fun n => by
      have h := norm_sqrtOneSubSeriesTerm_succ_le_abs_mul x n
      simpa[Real.norm_eq_abs, abs_abs] using h)
  exact summable_of_ratio_norm_eventually_le hx hratio


-- 2. The Cauchy Product & Vandermonde:

def binomHalf : ℕ → ℝ
  | 0 => 1
  | n + 1 => binomHalf n * (1 / 2 - (n : ℝ)) / ((n : ℝ) + 1)

theorem binomHalf_succ (n : ℕ) :
    binomHalf (n + 1) = binomHalf n * (1 / 2 - (n : ℝ)) / ((n : ℝ) + 1) := rfl

theorem sqrtOneSubCoeff_eq_binomHalf_mul_neg_one_pow (n : ℕ) :
    sqrtOneSubCoeff n = binomHalf n * (-1 : ℝ) ^ n := by
  induction n with
  | zero =>
      unfold sqrtOneSubCoeff wallisEvenCoeff binomHalf
      norm_num
  | succ n ih =>
      rw[sqrtOneSubCoeff_succ n, ih, binomHalf_succ n]
      have h_pow : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) := by
        rw [pow_add, pow_one]
      rw [h_pow]
      have hd1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hd2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

theorem sqrtOneSubSeriesTerm_eq_binomHalf_term (x : ℝ) (n : ℕ) :
    sqrtOneSubSeriesTerm x n = binomHalf n * (-x) ^ n := by
  unfold sqrtOneSubSeriesTerm
  rw[sqrtOneSubCoeff_eq_binomHalf_mul_neg_one_pow n]
  have h_neg_x : (-x) ^ n = (-1 : ℝ) ^ n * x ^ n := by
    have h_eq : -x = -1 * x := by ring
    rw [h_eq, mul_pow]
  rw[h_neg_x]
  ring

theorem ring_choose_succ_right (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  have h :=
    Ring.choose_smul_choose (r := a) (n := n + 1) (k := n) (Nat.le_succ n)
  have hcoeff : (((n + 1).choose n : ℕ) : ℝ) = n + 1 := by
    exact_mod_cast Nat.choose_succ_self_right n
  have hsub : n + 1 - n = 1 := by omega
  rw [nsmul_eq_mul, hcoeff, hsub] at h
  have hone : Ring.choose (a - n) 1 = a - n := by simp
  rw [hone] at h
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn1).2
  simpa[mul_comm, mul_left_comm, mul_assoc] using h

theorem binomHalf_eq_choose (n : ℕ) :
    binomHalf n = Ring.choose ((1 : ℝ) / 2) n := by
  induction n with
  | zero => simp [binomHalf]
  | succ n ih =>
      rw[binomHalf_succ, ih, ring_choose_succ_right ((1 : ℝ) / 2) n]

theorem sqrtOneSubSeriesTerm_eq_choose_term (x : ℝ) (n : ℕ) :
    sqrtOneSubSeriesTerm x n = Ring.choose ((1 : ℝ) / 2) n * (-x) ^ n := by
  rw[sqrtOneSubSeriesTerm_eq_binomHalf_term, binomHalf_eq_choose]

theorem sqrtOneSubSeries_cauchy_coeff (x : ℝ) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n,
      sqrtOneSubSeriesTerm x kl.1 * sqrtOneSubSeriesTerm x kl.2 =
        Ring.choose (1 : ℝ) n * (-x) ^ n := by
  calc
    ∑ kl ∈ Finset.antidiagonal n,
        sqrtOneSubSeriesTerm x kl.1 * sqrtOneSubSeriesTerm x kl.2
      = ∑ kl ∈ Finset.antidiagonal n,
          (Ring.choose ((1 : ℝ) / 2) kl.1 *
            Ring.choose ((1 : ℝ) / 2) kl.2) * (-x) ^ n := by
        apply Finset.sum_congr rfl
        intro kl hkl
        rcases Finset.mem_antidiagonal.mp hkl with hsum
        rw[sqrtOneSubSeriesTerm_eq_choose_term, sqrtOneSubSeriesTerm_eq_choose_term]
        calc
          Ring.choose ((1 : ℝ) / 2) kl.1 * (-x) ^ kl.1 *
              (Ring.choose ((1 : ℝ) / 2) kl.2 * (-x) ^ kl.2)
            = (Ring.choose ((1 : ℝ) / 2) kl.1 *
                Ring.choose ((1 : ℝ) / 2) kl.2) *
                  ((-x) ^ kl.1 * (-x) ^ kl.2) := by ring
          _ = (Ring.choose ((1 : ℝ) / 2) kl.1 *
                Ring.choose ((1 : ℝ) / 2) kl.2) *
                  (-x) ^ n := by rw[← pow_add, hsum]
    _ = (∑ kl ∈ Finset.antidiagonal n,
          Ring.choose ((1 : ℝ) / 2) kl.1 *
            Ring.choose ((1 : ℝ) / 2) kl.2) * (-x) ^ n := by
        rw[← Finset.sum_mul]
    _ = Ring.choose (1 : ℝ) n * (-x) ^ n := by
        have hadd :
            ∑ kl ∈ Finset.antidiagonal n,
              Ring.choose ((1 : ℝ) / 2) kl.1 *
                Ring.choose ((1 : ℝ) / 2) kl.2
              = Ring.choose (1 : ℝ) n := by
          calc
            ∑ kl ∈ Finset.antidiagonal n,
                Ring.choose ((1 : ℝ) / 2) kl.1 *
                  Ring.choose ((1 : ℝ) / 2) kl.2
              = Ring.choose (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) n := by
                  symm
                  exact Ring.add_choose_eq (r := ((1 : ℝ) / 2)) (s := ((1 : ℝ) / 2))
                    (k := n) (h := Commute.all ((1 : ℝ) / 2) ((1 : ℝ) / 2))
            _ = Ring.choose (1 : ℝ) n := by
                  congr 1; ring
        rw[hadd]

theorem choose_one_mul_pow_eq_zero_of_two_le (x : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    Ring.choose (1 : ℝ) n * (-x) ^ n = 0 := by
  have hlt : 1 < n := by linarith
  have hchoose_nat : Nat.choose 1 n = 0 := Nat.choose_eq_zero_of_lt hlt
  have hchoose : Ring.choose (1 : ℝ) n = 0 := by
    rw[show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Ring.choose_natCast]
    exact_mod_cast hchoose_nat
  rw [hchoose, zero_mul]

theorem sqrtOneSubSeries_sq_eq_one_sub {x : ℝ} (hx : |x| < 1) :
    (sqrtOneSubSeries x) ^ 2 = 1 - x := by
  have hsabs : Summable (fun n : ℕ => ‖sqrtOneSubSeriesTerm x n‖) := by
    simpa[Real.norm_eq_abs] using sqrtOneSubSeries_abs_summable_of_abs_lt_one hx
  calc
    (sqrtOneSubSeries x) ^ 2
        = (∑' n : ℕ, sqrtOneSubSeriesTerm x n) *
            (∑' n : ℕ, sqrtOneSubSeriesTerm x n) := by
          simp [sqrtOneSubSeries, pow_two]
    _ = ∑' n : ℕ,
          ∑ kl ∈ Finset.antidiagonal n,
            sqrtOneSubSeriesTerm x kl.1 * sqrtOneSubSeriesTerm x kl.2 := by
          exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsabs hsabs
    _ = ∑' n : ℕ, Ring.choose (1 : ℝ) n * (-x) ^ n := by
          apply tsum_congr
          intro n
          exact sqrtOneSubSeries_cauchy_coeff x n
    _ = Finset.sum ({0, 1} : Finset ℕ)
          (fun n : ℕ => Ring.choose (1 : ℝ) n * (-x) ^ n) := by
          exact tsum_eq_sum (s := ({0, 1} : Finset ℕ))
            (f := fun n : ℕ => Ring.choose (1 : ℝ) n * (-x) ^ n)
            (by
              intro n hn
              have h2 : 2 ≤ n := by
                rcases n with _ | _ | n
                · simp at hn
                · simp at hn
                · omega
              exact choose_one_mul_pow_eq_zero_of_two_le x h2)
    _ = Ring.choose (1 : ℝ) 0 * (-x) ^ 0 +
          Ring.choose (1 : ℝ) 1 * (-x) ^ 1 := by simp
    _ = 1 - x := by
          have hchoose0 : Ring.choose (1 : ℝ) 0 = 1 := by simp
          have hchoose1 : Ring.choose (1 : ℝ) 1 = 1 := by
            rw[show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Ring.choose_natCast]
            norm_num
          rw[hchoose0, hchoose1]
          ring


-- 3. The IVT Hack (Sign Choice):

theorem sqrtOneSubSeries_zero_val :
    sqrtOneSubSeries 0 = 1 := by
  unfold sqrtOneSubSeries
  have h : (fun n : ℕ => sqrtOneSubSeriesTerm 0 n) = (fun n : ℕ => if n = 0 then 1 else 0) := by
    ext n
    cases n with
    | zero =>
        unfold sqrtOneSubSeriesTerm sqrtOneSubCoeff wallisEvenCoeff
        simp
    | succ n =>
        unfold sqrtOneSubSeriesTerm
        simp [pow_succ]
  rw [h, tsum_ite_eq]

theorem sqrtOneSubSeriesTerm_continuous (n : ℕ) :
    Continuous (fun x : ℝ => sqrtOneSubSeriesTerm x n) := by
  unfold sqrtOneSubSeriesTerm
  exact continuous_const.mul (continuous_id.pow n)

theorem norm_sqrtOneSubSeriesTerm_le_on_Icc
    {r x : ℝ} (hr0 : 0 ≤ r) (hx : x ∈ Set.Icc (-r) r) (n : ℕ) :
    ‖sqrtOneSubSeriesTerm x n‖ ≤ |sqrtOneSubSeriesTerm r n| := by
  have hxr : |x| ≤ r := abs_le.mpr ⟨hx.1, hx.2⟩
  unfold sqrtOneSubSeriesTerm
  rw[Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hr0]
  apply mul_le_mul_of_nonneg_left
  · induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hxr (abs_nonneg x) (pow_nonneg hr0 n)
  · exact abs_nonneg _

theorem sqrtOneSubSeries_continuousOn_Icc
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn sqrtOneSubSeries (Set.Icc (-r) r) := by
  have hsumm : Summable (fun n : ℕ => |sqrtOneSubSeriesTerm r n|) := by
    have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
    exact sqrtOneSubSeries_abs_summable_of_abs_lt_one hrabs
  unfold sqrtOneSubSeries
  apply continuousOn_tsum
  · intro n
    exact (sqrtOneSubSeriesTerm_continuous n).continuousOn
  · exact hsumm
  · intro n x hx
    exact norm_sqrtOneSubSeriesTerm_le_on_Icc hr0 hx n

theorem sqrtOneSubSeries_nonneg_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    0 ≤ sqrtOneSubSeries x := by
  by_contra hxneg
  have hxlt : sqrtOneSubSeries x < 0 := lt_of_not_ge hxneg
  let r : ℝ := (|x| + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; nlinarith [abs_nonneg x]
  have hxr : |x| < r := by dsimp [r]; nlinarith
  have hr1 : r < 1 := by dsimp [r]; nlinarith
  have hxmem : x ∈ Set.Icc (-r) r := ⟨le_of_lt (abs_lt.mp hxr).1, le_of_lt (abs_lt.mp hxr).2⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (-r) r := ⟨by nlinarith [hr0], by nlinarith [hr0]⟩
  have hseg : Set.uIcc x 0 ⊆ Set.Icc (-r) r := by
    intro y hy
    have hmin : -r ≤ min x 0 := le_min hxmem.1 h0mem.1
    have hmax : max x 0 ≤ r := max_le hxmem.2 h0mem.2
    exact ⟨le_trans hmin hy.1, le_trans hy.2 hmax⟩
  have hcont_Icc : ContinuousOn sqrtOneSubSeries (Set.Icc (-r) r) :=
    sqrtOneSubSeries_continuousOn_Icc hr0 hr1
  have hcont_seg : ContinuousOn sqrtOneSubSeries (Set.uIcc x 0) :=
    hcont_Icc.mono hseg
  have h0pos : 0 < sqrtOneSubSeries 0 := by
    rw[sqrtOneSubSeries_zero_val]
    norm_num
  have hzmem : (0 : ℝ) ∈ Set.uIcc (sqrtOneSubSeries x) (sqrtOneSubSeries 0) := by
    constructor
    · exact le_trans (min_le_left _ _) (le_of_lt hxlt)
    · exact le_trans (le_of_lt h0pos) (le_max_right _ _)
  rcases intermediate_value_uIcc hcont_seg hzmem with ⟨y, hyseg, hyzero⟩
  have hymem : y ∈ Set.Icc (-r) r := hseg hyseg
  have hyabs_le : |y| ≤ r := abs_le.mpr ⟨hymem.1, hymem.2⟩
  have hyabs : |y| < 1 := lt_of_le_of_lt hyabs_le hr1
  have hsq : (sqrtOneSubSeries y) ^ 2 = 1 - y := sqrtOneSubSeries_sq_eq_one_sub hyabs
  rw [hyzero] at hsq
  have hy1 : y = 1 := by nlinarith
  have hylt1 : y < 1 := (abs_lt.mp hyabs).2
  linarith

theorem sqrtOneSubSeriesTarget_of_abs_lt_one (x : ℝ) (hx : |x| < 1) :
    sqrtOneSubSeriesTarget x := by
  unfold sqrtOneSubSeriesTarget
  have hxnonneg : 0 ≤ 1 - x := by
    have hx' := abs_lt.mp hx
    nlinarith
  have hsq : (sqrtOneSubSeries x) ^ 2 = (Real.sqrt (1 - x)) ^ 2 := by
    calc
      (sqrtOneSubSeries x) ^ 2 = 1 - x := sqrtOneSubSeries_sq_eq_one_sub hx
      _ = (Real.sqrt (1 - x)) ^ 2 := by symm; exact Real.sq_sqrt hxnonneg
  have hser_nonneg : 0 ≤ sqrtOneSubSeries x := sqrtOneSubSeries_nonneg_of_abs_lt_one hx
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  have hEq : sqrtOneSubSeries x = Real.sqrt (1 - x) := by
    nlinarith [hsq, hser_nonneg, hsqrt_nonneg]
  exact hEq.symm

end EllipseOmega
