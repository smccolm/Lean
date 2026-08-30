import PrimeShell.GMInterface
import Mathlib.Algebra.BigOperators.Module

namespace PrimeShell

open scoped BigOperators

/-- Prefix sums of a finite sequence. -/
def cumulativePrefix (c : ℕ → ℝ) (H : ℕ) : ℝ := ∑ h ∈ Finset.Icc 1 H, c h

/-- The information retained by a shift-prefix interface after two `n`
locations have been collapsed into the same shift column. -/
def twoPointShiftPrefix (a : Bool → ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ b : Bool, a b h

/-- The corresponding two-location functional for a kernel that still
depends on the dyadic position. -/
def twoPointKernelFunctional
    (K₀ K₁ : ℕ → ℝ) (a : Bool → ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, (K₀ h * a false h + K₁ h * a true h)

/-- The precise assertion that collapsed shift-prefix data determine every
two-location kernel functional.  This is the interface that F1 would need if
no `n`-local information or direct variation-remainder estimate were supplied. -/
def PrefixOnlyTwoPointTransfer (K₀ K₁ : ℕ → ℝ) : Prop :=
  ∀ a : Bool → ℕ → ℝ,
    (∀ H : ℕ, twoPointShiftPrefix a H = 0) →
    ∀ H : ℕ, twoPointKernelFunctional K₀ K₁ a H = 0

/-- Exact finite no-go for F1.  If the literal trace kernel takes different
values at two `n`-locations for one shift, then *all* cumulative shift-prefix
data can vanish while the trace functional is nonzero.  Thus a theorem whose
only arithmetic input is the collapsed prefix cannot control the exact
two-variable kernel; it needs `n`-localized/rectangle-prefix information (or
a direct estimate of the variation remainder). -/
theorem all_shift_prefixes_insufficient_for_nonconstant_two_variable_kernel
    (K₀ K₁ : ℕ → ℝ) {h₀ : ℕ} (hh₀ : 1 ≤ h₀) (hne : K₀ h₀ ≠ K₁ h₀) :
    ∃ a : Bool → ℕ → ℝ,
      (∀ H : ℕ, twoPointShiftPrefix a H = 0) ∧
      twoPointKernelFunctional K₀ K₁ a h₀ ≠ 0 := by
  let a : Bool → ℕ → ℝ := fun b h =>
    if h = h₀ then if b then -1 else 1 else 0
  refine ⟨a, ?_, ?_⟩
  · intro H
    unfold twoPointShiftPrefix
    apply Finset.sum_eq_zero
    intro h hh
    by_cases heq : h = h₀ <;> simp [a, heq]
  · unfold twoPointKernelFunctional
    have hmem : h₀ ∈ Finset.Icc 1 h₀ := Finset.mem_Icc.mpr ⟨hh₀, le_rfl⟩
    have hsum :
        (∑ h ∈ Finset.Icc 1 h₀,
          (K₀ h * a false h + K₁ h * a true h)) = K₀ h₀ - K₁ h₀ := by
      calc
        (∑ h ∈ Finset.Icc 1 h₀,
          (K₀ h * a false h + K₁ h * a true h)) =
            ∑ h ∈ Finset.Icc 1 h₀, if h = h₀ then K₀ h - K₁ h else 0 := by
              apply Finset.sum_congr rfl
              intro h hh
              by_cases heq : h = h₀ <;> simp [a, heq, sub_eq_add_neg]
        _ = K₀ h₀ - K₁ h₀ := by simp [hmem]
    rw [hsum]
    exact sub_ne_zero.mpr hne

/-- Specialization of the no-go to the literal Prime Shell kernel at two
dyadic positions. -/
theorem literal_dyadic_kernel_prefix_no_go
    (Φ : ℝ → ℝ) (T : ℝ) {n₀ n₁ h₀ : ℕ}
    (hh₀ : 1 ≤ h₀)
    (hne : dyadicShiftKernel Φ T n₀ h₀ ≠ dyadicShiftKernel Φ T n₁ h₀) :
    ∃ a : Bool → ℕ → ℝ,
      (∀ H : ℕ, twoPointShiftPrefix a H = 0) ∧
      twoPointKernelFunctional
        (fun h => dyadicShiftKernel Φ T n₀ h)
        (fun h => dyadicShiftKernel Φ T n₁ h) a h₀ ≠ 0 :=
  all_shift_prefixes_insufficient_for_nonconstant_two_variable_kernel
    (fun h => dyadicShiftKernel Φ T n₀ h)
    (fun h => dyadicShiftKernel Φ T n₁ h) hh₀ hne

/-- Any prefix-only transfer theorem for two rows forces the two kernel rows
to agree at every positive shift.  This is an unconditional necessary
condition, not an appeal to a heuristic claim that the source kernel varies. -/
theorem prefix_only_two_point_transfer_forces_row_constancy
    (K₀ K₁ : ℕ → ℝ) (htransfer : PrefixOnlyTwoPointTransfer K₀ K₁) :
    ∀ h : ℕ, 1 ≤ h → K₀ h = K₁ h := by
  intro h hh
  by_contra hne
  obtain ⟨a, hpref, hfun⟩ :=
    all_shift_prefixes_insufficient_for_nonconstant_two_variable_kernel K₀ K₁ hh hne
  exact hfun (htransfer a hpref h)

/-- Applied to the literal Prime Shell kernel: a consumer using only collapsed
shift prefixes can exist only if every pair of dyadic-position rows is equal.
The exact decomposition supplies no such row-constancy identity. -/
theorem literal_prefix_only_transfer_forces_kernel_row_constancy
    (Φ : ℝ → ℝ) (T : ℝ) {n₀ n₁ : ℕ}
    (htransfer : PrefixOnlyTwoPointTransfer
      (fun h => dyadicShiftKernel Φ T n₀ h)
      (fun h => dyadicShiftKernel Φ T n₁ h)) :
    ∀ h : ℕ, 1 ≤ h →
      dyadicShiftKernel Φ T n₀ h = dyadicShiftKernel Φ T n₁ h :=
  prefix_only_two_point_transfer_forces_row_constancy _ _ htransfer

/-- The theorem-level F1 FAIL certificate at any witnessed row variation of
the literal kernel.  Its hypothesis is exactly the missing equality test, not
an abstract cardinality estimate or a theorem-equivalent trace hypothesis. -/
theorem literal_prefix_only_transfer_fails_of_row_variation
    (Φ : ℝ → ℝ) (T : ℝ) {n₀ n₁ h : ℕ} (hh : 1 ≤ h)
    (hne : dyadicShiftKernel Φ T n₀ h ≠ dyadicShiftKernel Φ T n₁ h) :
    ¬ PrefixOnlyTwoPointTransfer
      (fun j => dyadicShiftKernel Φ T n₀ j)
      (fun j => dyadicShiftKernel Φ T n₁ j) := by
  intro htransfer
  exact hne (literal_prefix_only_transfer_forces_kernel_row_constancy
    Φ T htransfer h hh)

/-- Exact finite Abel identity on the endpoint convention used by the shift
sum.  It shows that cumulative prefixes do control a genuinely scalar
shift-kernel; the two-variable remainder is the separate obstruction. -/
theorem finite_abel_identity
    (K c : ℕ → ℝ) {H : ℕ} (hH : 1 ≤ H) :
    (∑ h ∈ Finset.Icc 1 H, K h * c h) =
      K H * cumulativePrefix c H +
        ∑ h ∈ Finset.Icc 1 (H - 1),
          (K h - K (h + 1)) * cumulativePrefix c h := by
  let g : ℕ → ℝ := fun h => if h = 0 then 0 else c h
  have hprefix : ∀ j : ℕ,
      (∑ i ∈ Finset.range (j + 1), g i) = cumulativePrefix c j := by
    intro j
    have hrange : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hrange, Finset.sum_insert]
    · simp only [g, if_pos, zero_add]
      unfold cumulativePrefix
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i ≠ 0 := by
        exact Nat.ne_of_gt (Finset.mem_Icc.mp hi).1
      simp [hi0]
    · simp
  have hbp := Finset.sum_Ioc_by_parts K g (Nat.zero_lt_of_lt hH)
  have hleft : (∑ i ∈ Finset.Ioc 0 H, K i • g i) =
      ∑ h ∈ Finset.Icc 1 H, K h * c h := by
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro i hi
      have hi0 : i ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hi).1
      simp [g, hi0, smul_eq_mul]
  have hvar :
      -(∑ i ∈ Finset.Ioc 0 (H - 1),
          (K (i + 1) - K i) * cumulativePrefix c i) =
        ∑ i ∈ Finset.Icc 1 (H - 1),
          (K i - K (i + 1)) * cumulativePrefix c i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro i hi
      ring
  rw [hleft] at hbp
  simp_rw [hprefix] at hbp
  have hp0 : cumulativePrefix c 0 = 0 := by simp [cumulativePrefix]
  simp only [Nat.zero_add, hp0, mul_zero, sub_zero, smul_eq_mul] at hbp
  rw [sub_eq_add_neg, hvar] at hbp
  exact hbp

/-- Total discrete variation of a scalar shift kernel on the exact positive
shift interval. -/
def scalarKernelTotalVariation (K : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (H - 1), |K h - K (h + 1)|

/-- Quantitative Abel transfer from a uniform cumulative-prefix bound. -/
theorem abs_weighted_sum_le_of_prefix_bound
    (K c : ℕ → ℝ) {H : ℕ} (hH : 1 ≤ H) {B : ℝ}
    (hprefix : ∀ J : ℕ, J ≤ H → |cumulativePrefix c J| ≤ B) :
    |∑ h ∈ Finset.Icc 1 H, K h * c h| ≤
      B * (|K H| + scalarKernelTotalVariation K H) := by
  rw [finite_abel_identity K c hH]
  calc
    |K H * cumulativePrefix c H +
        ∑ h ∈ Finset.Icc 1 (H - 1),
          (K h - K (h + 1)) * cumulativePrefix c h| ≤
        |K H * cumulativePrefix c H| +
          |∑ h ∈ Finset.Icc 1 (H - 1),
            (K h - K (h + 1)) * cumulativePrefix c h| := abs_add_le _ _
    _ ≤ |K H| * B +
          ∑ h ∈ Finset.Icc 1 (H - 1), |K h - K (h + 1)| * B := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hprefix H le_rfl) (abs_nonneg _)
      · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro h hh
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left
        · exact hprefix h ((Finset.mem_Icc.mp hh).2.trans (Nat.sub_le H 1))
        · exact abs_nonneg _
    _ = B * (|K H| + scalarKernelTotalVariation K H) := by
      unfold scalarKernelTotalVariation
      rw [← Finset.sum_mul]
      ring

/-- The weakest exact extra analytic input left by the scalar Abel transfer:
a direct bound for the kernel-variation remainder already present in the
source decomposition.  This is a specification, not an assumed theorem. -/
def DyadicKernelVariationBound
    (Φ : ℝ → ℝ) (T : ℝ) (N H : ℕ) (E : ℝ) : Prop :=
  |dyadicKernelVariationRemainder Φ T N H| ≤ E

/-- Exact consumer ledger: a scalar-prefix estimate plus a direct remainder
estimate controls the literal dyadic shift sum. -/
theorem abs_dyadicShiftSum_le_of_prefix_and_variation
    (Φ : ℝ → ℝ) (T : ℝ) (N : ℕ) {H : ℕ} (hH : 1 ≤ H)
    {B E : ℝ}
    (hprefix : ∀ J : ℕ, J ≤ H → |cumulativePrefix (dyadicLambdaCorrelation N) J| ≤ B)
    (hvariation : DyadicKernelVariationBound Φ T N H E) :
    |dyadicShiftSum Φ T N H| ≤
      B * (|anchoredDyadicShiftKernel Φ T N H| +
        scalarKernelTotalVariation (anchoredDyadicShiftKernel Φ T N) H) + E := by
  rw [dyadicShiftSum_eq_kernel_mul_correlation_add_remainder]
  refine (abs_add_le _ _).trans (add_le_add ?_ hvariation)
  exact abs_weighted_sum_le_of_prefix_bound
    (anchoredDyadicShiftKernel Φ T N) (dyadicLambdaCorrelation N) hH hprefix

/-- A precise finite no-go: knowing only the final cumulative sum cannot control a nonconstant weight. -/
theorem final_prefix_information_insufficient
    {H : ℕ} (hH : 2 ≤ H) (K : ℕ → ℝ) (hK : K 1 ≠ K 2) :
    ∃ c : ℕ → ℝ, cumulativePrefix c H = 0 ∧
      (∑ h ∈ Finset.Icc 1 H, K h * c h) ≠ 0 := by
  let c : ℕ → ℝ := fun h => if h = 1 then 1 else if h = 2 then -1 else 0
  refine ⟨c, ?_, ?_⟩
  · have hc : ∀ h, c h = (if h = 1 then 1 else 0) + (if h = 2 then -1 else 0) := by
      intro h
      by_cases h1 : h = 1
      · simp [c, h1]
      · by_cases h2 : h = 2 <;> simp [c, h1, h2]
    unfold cumulativePrefix
    simp_rw [hc, Finset.sum_add_distrib, Finset.sum_ite_eq']
    have h1H : 1 ≤ H := by omega
    simp [h1H, hH]
  · have hc : ∀ h, K h * c h =
        (if h = 1 then K 1 else 0) + (if h = 2 then -K 2 else 0) := by
      intro h
      by_cases h1 : h = 1
      · simp [c, h1]
      · by_cases h2 : h = 2 <;> simp [c, h1, h2]
    simp_rw [hc, Finset.sum_add_distrib, Finset.sum_ite_eq']
    have h1H : 1 ≤ H := by omega
    have hd : K 1 - K 2 ≠ 0 := sub_ne_zero.mpr hK
    simpa [h1H, hH, sub_eq_add_neg] using hd

/-- The strict algebraic scale margin behind the candidate overlap. -/
theorem gm_overlap_iff_alpha_gt_fifteen_thirteenths
    {α : ℝ} (hα : 0 < α) :
    2 / 15 < 1 - 1 / α ↔ 15 / 13 < α := by
  constructor <;> intro h
  · have h' : 1 / α < 13 / 15 := by linarith
    rw [div_lt_iff₀ hα] at h'
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 13)]
    nlinarith
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 13)] at h
    have h' : 1 / α < 13 / 15 := by
      rw [div_lt_iff₀ hα]
      nlinarith
    linarith

/-- Exact resonant-scale algebra: if `N=T^α`, then `N/T=T^(α-1)`. -/
theorem resonant_scale_of_power {T α : ℝ} (hT : 0 < T) :
    T ^ α / T = T ^ (α - 1) := by
  rw [Real.rpow_sub_one hT.ne' α]

/-- A literal logarithmic resonance condition forces `h` into a constant
multiple of `n/T`.  No `log(1+u)≈u` heuristic is used. -/
theorem resonant_log_shift_implies_range
    {T n h : ℝ} (hT : 0 < T) (hn : 0 < n) (hh : 0 < h)
    (hres : |T * (Real.log (n + h) - Real.log n)| ≤ 1) :
    (2 * T - 1) * h ≤ 2 * n := by
  have hnh : 0 < n + h := by linarith
  have hratio : 0 ≤ h / n := (div_nonneg hh.le hn.le)
  have hlogeq : Real.log (n + h) - Real.log n = Real.log (1 + h / n) := by
    rw [← Real.log_div hnh.ne' hn.ne']
    congr 1
    field_simp
  have hlower : 2 * h / (h + 2 * n) ≤ Real.log (n + h) - Real.log n := by
    rw [hlogeq]
    have hbase := Real.le_log_one_add_of_nonneg hratio
    convert hbase using 1
    field_simp
  have hlogpos : 0 < Real.log (n + h) - Real.log n := by
    rw [hlogeq]
    have hdiv : 0 < h / n := div_pos hh hn
    exact Real.log_pos (by linarith)
  have hphase : T * (Real.log (n + h) - Real.log n) ≤ 1 := by
    rw [abs_of_pos (mul_pos hT hlogpos)] at hres
    exact hres
  have hden : 0 < h + 2 * n := by positivity
  have hfrac : 2 * T * h / (h + 2 * n) ≤ 1 := by
    calc
      2 * T * h / (h + 2 * n) = T * (2 * h / (h + 2 * n)) := by ring
      _ ≤ T * (Real.log (n + h) - Real.log n) :=
        mul_le_mul_of_nonneg_left hlower hT.le
      _ ≤ 1 := hphase
  rw [div_le_iff₀ hden] at hfrac
  nlinarith

/-- Strict epsilon-budget form of the GM overlap.  An admissible positive
margin exists exactly beyond `α=15/13`; equality is excluded. -/
theorem exists_strict_gm_margin_iff_alpha_gt_fifteen_thirteenths
    {α : ℝ} (hα : 0 < α) :
    (∃ ε : ℝ, 0 < ε ∧ 2 / 15 + ε < 1 - 1 / α) ↔ 15 / 13 < α := by
  constructor
  · rintro ⟨ε, hε, hoverlap⟩
    have hbase : 2 / 15 < 1 - 1 / α := lt_trans (by linarith) hoverlap
    exact (gm_overlap_iff_alpha_gt_fifteen_thirteenths hα).mp hbase
  · intro hαmargin
    have hbase : 2 / 15 < 1 - 1 / α :=
      (gm_overlap_iff_alpha_gt_fifteen_thirteenths hα).mpr hαmargin
    refine ⟨((1 - 1 / α) - 2 / 15) / 2, by linarith, by linarith⟩

end PrimeShell
