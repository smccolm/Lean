import PrimeShell.KernelLocalization

namespace PrimeShell

noncomputable section

open scoped BigOperators
open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

/-- The actual normalized von-Mangoldt correlation on a short `n`-box,
while retaining the endpoint imposed by the ambient dyadic block. -/
def boxLambdaCorrelation (N A B h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc A B,
    if n + h ∈ Finset.Ioc N (2 * N) then dyadicLambdaWeight n h else 0

/-- The literal kernel-weighted contribution of one short `n`-box. -/
def boxShiftSum
    (Phi : ℝ → ℝ) (T : ℝ) (N A B H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc A B,
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h
    else 0

/-- The literal kernel anchored at the first integer of a short box. -/
def boxAnchoredKernel
    (Phi : ℝ → ℝ) (T : ℝ) (A h : ℕ) : ℝ :=
  dyadicShiftKernel Phi T (A + 1) h

/-- The exact error made by freezing the literal kernel at the first integer
of a short box. -/
def boxKernelVariation
    (Phi : ℝ → ℝ) (T : ℝ) (N A B H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc A B,
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h *
        (dyadicShiftKernel Phi T n h - boxAnchoredKernel Phi T A h)
    else 0

/-- Exact anchor-plus-variation identity on a short `n`-box.  No analytic or
arithmetic estimate is used. -/
theorem boxShiftSum_eq_anchor_add_variation
    (Phi : ℝ → ℝ) (T : ℝ) (N A B H : ℕ) :
    boxShiftSum Phi T N A B H =
      (∑ h ∈ Finset.Icc 1 H,
        boxAnchoredKernel Phi T A h * boxLambdaCorrelation N A B h) +
      boxKernelVariation Phi T N A B H := by
  unfold boxShiftSum boxLambdaCorrelation boxKernelVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true]
    ring
  · simp [hmem]

/-- Explicit row-oscillation budget furnished by the literal Zeta23 kernel.
The box width is a real variable so later scale arguments can use either an
integer width or a sharper external upper bound without changing the kernel. -/
def boxKernelOscillationBudget
    (Phi : ℝ → ℝ) (T N W : ℝ) (h : ℕ) : ℝ :=
  3 * T ^ 2 * ((h : ℝ) * W / N ^ 2) * (∫ x, Phi x ^ 2) +
    2 * T * (W / N) * (∫ x, Phi x ^ 2 * |x|) +
    12 * T * (W / N) * (∫ x, Phi x ^ 2)

/-- A point in `(A,B]` lies at most `B-A` from the literal anchor `A+1`. -/
theorem abs_natCast_sub_anchor_le_boxWidth
    {A B n : ℕ} (hn : n ∈ Finset.Ioc A B) :
    |(n : ℝ) - (A + 1 : ℕ)| ≤ (B - A : ℕ) := by
  have hn' := Finset.mem_Ioc.mp hn
  have hanchor : A + 1 ≤ n := by omega
  rw [abs_of_nonneg]
  · exact_mod_cast (show n - (A + 1) ≤ B - A by omega)
  · exact sub_nonneg.mpr (by exact_mod_cast hanchor)

/-- Pointwise short-box localization of the actual kernel.  This is the
precise analytic bridge from a correlation theorem on the box to the trace
consumer; the right side contains the actual zeroth and first moments. -/
theorem abs_dyadicShiftKernel_sub_boxAnchor_le
    {Phi : ℝ → ℝ} {T : ℝ} {N A B n h : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hNA : N ≤ A) (hA : A < 2 * N) (hB : B ≤ 2 * N)
    (hn : n ∈ Finset.Ioc A B)
    (hh : 1 ≤ h) (hhN : h ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |dyadicShiftKernel Phi T n h - boxAnchoredKernel Phi T A h| ≤
      boxKernelOscillationBudget Phi T N (B - A : ℕ) h := by
  have hn' := Finset.mem_Ioc.mp hn
  have hndyadic : n ∈ Finset.Ioc N (2 * N) :=
    Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hNA hn'.1, hn'.2.trans hB⟩
  have hanchor : A + 1 ∈ Finset.Ioc N (2 * N) := by
    rw [Finset.mem_Ioc]
    omega
  have hdist := abs_natCast_sub_anchor_le_boxWidth hn
  have hI0 : 0 ≤ ∫ x, Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hI1 : 0 ≤ ∫ x, Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  unfold boxAnchoredKernel boxKernelOscillationBudget
  refine (abs_dyadicShiftKernel_sub_le_dyadicBox hT hN hndyadic hanchor
    hh hhN hPhi hPhi2 hPhiAbs).trans ?_
  have hfrac1 :
      (h : ℝ) * |(n : ℝ) - (A + 1 : ℕ)| / (N : ℝ) ^ 2 ≤
        (h : ℝ) * (B - A : ℕ) / (N : ℝ) ^ 2 := by
    gcongr
  have hfrac2 :
      |(n : ℝ) - (A + 1 : ℕ)| / (N : ℝ) ≤
        (B - A : ℕ) / (N : ℝ) := by
    exact div_le_div_of_nonneg_right hdist (by positivity)
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrac1 (by positivity)) hI0
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrac2 (by positivity)) hI1
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfrac2 (by positivity)) hI0

/-- Every term in the explicit oscillation budget is nonnegative. -/
theorem boxKernelOscillationBudget_nonneg
    {Phi : ℝ → ℝ} {T N W : ℝ} {h : ℕ}
    (hT : 0 ≤ T) (hN : 0 < N) (hW : 0 ≤ W) :
    0 ≤ boxKernelOscillationBudget Phi T N W h := by
  unfold boxKernelOscillationBudget
  have hI0 : 0 ≤ ∫ x, Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hI1 : 0 ≤ ∫ x, Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  positivity

/-- Complete finite error ledger for freezing the literal kernel separately
on every short box.  The remaining arithmetic object is exactly the actual
normalized von-Mangoldt correlation on that box. -/
theorem abs_boxKernelVariation_le
    {Phi : ℝ → ℝ} {T : ℝ} {N A B H : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hNA : N ≤ A) (hA : A < 2 * N) (hB : B ≤ 2 * N)
    (hHN : H ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |boxKernelVariation Phi T N A B H| ≤
      ∑ h ∈ Finset.Icc 1 H,
        boxKernelOscillationBudget Phi T N (B - A : ℕ) h *
          boxLambdaCorrelation N A B h := by
  unfold boxKernelVariation boxLambdaCorrelation
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro h hhmem
  have hh := Finset.mem_Icc.mp hhmem
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true, abs_mul]
    have hw : 0 ≤ dyadicLambdaWeight n h := dyadicLambdaWeight_nonneg n h
    rw [abs_of_nonneg hw]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (abs_dyadicShiftKernel_sub_boxAnchor_le hT hN hNA hA hB hn
        hh.1 (hh.2.trans hHN) hPhi hPhi2 hPhiAbs) hw
  · simp [hmem]

/-- The exact arithmetic interface required after kernel localization.  It
does not mention traces or zeros: it bounds only the actual box correlation
against an explicit proposed main term. -/
def BoxCorrelationEstimate
    (N A B H : ℕ) (main error : ℕ → ℝ) : Prop :=
  ∀ h ∈ Finset.Icc 1 H,
    |boxLambdaCorrelation N A B h - main h| ≤ error h

/-- Exact consumer of a localized arithmetic estimate.  It keeps the main
term, arithmetic error, and literal kernel-variation cost visibly separate. -/
theorem abs_boxShiftSum_sub_anchoredMain_le
    {Phi : ℝ → ℝ} {T : ℝ} {N A B H : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hNA : N ≤ A) (hA : A < 2 * N) (hB : B ≤ 2 * N)
    (hHN : H ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|)
    (main error : ℕ → ℝ)
    (harith : BoxCorrelationEstimate N A B H main error) :
    |boxShiftSum Phi T N A B H -
        ∑ h ∈ Finset.Icc 1 H, boxAnchoredKernel Phi T A h * main h| ≤
      (∑ h ∈ Finset.Icc 1 H,
        |boxAnchoredKernel Phi T A h| * error h) +
      ∑ h ∈ Finset.Icc 1 H,
        boxKernelOscillationBudget Phi T N (B - A : ℕ) h *
          boxLambdaCorrelation N A B h := by
  rw [boxShiftSum_eq_anchor_add_variation]
  rw [show
      (∑ h ∈ Finset.Icc 1 H,
          boxAnchoredKernel Phi T A h * boxLambdaCorrelation N A B h) +
          boxKernelVariation Phi T N A B H -
        ∑ h ∈ Finset.Icc 1 H, boxAnchoredKernel Phi T A h * main h =
      (∑ h ∈ Finset.Icc 1 H,
          boxAnchoredKernel Phi T A h *
            (boxLambdaCorrelation N A B h - main h)) +
        boxKernelVariation Phi T N A B H by
    calc
      (∑ h ∈ Finset.Icc 1 H,
          boxAnchoredKernel Phi T A h * boxLambdaCorrelation N A B h) +
          boxKernelVariation Phi T N A B H -
        ∑ h ∈ Finset.Icc 1 H, boxAnchoredKernel Phi T A h * main h =
        ((∑ h ∈ Finset.Icc 1 H,
            boxAnchoredKernel Phi T A h * boxLambdaCorrelation N A B h) -
          ∑ h ∈ Finset.Icc 1 H,
            boxAnchoredKernel Phi T A h * main h) +
          boxKernelVariation Phi T N A B H := by ring
      _ = (∑ h ∈ Finset.Icc 1 H,
          (boxAnchoredKernel Phi T A h * boxLambdaCorrelation N A B h -
            boxAnchoredKernel Phi T A h * main h)) +
          boxKernelVariation Phi T N A B H := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ h ∈ Finset.Icc 1 H,
          boxAnchoredKernel Phi T A h *
            (boxLambdaCorrelation N A B h - main h)) +
          boxKernelVariation Phi T N A B H := by
        apply congrArg (fun z => z + boxKernelVariation Phi T N A B H)
        apply Finset.sum_congr rfl
        intro h hh
        ring]
  refine (abs_add_le _ _).trans (add_le_add ?_
    (abs_boxKernelVariation_le hT hN hNA hA hB hHN hPhi hPhi2 hPhiAbs))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro h hh
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (harith h hh) (abs_nonneg _)

end

end PrimeShell
