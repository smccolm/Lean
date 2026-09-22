import GafniTao.FordZetaBasicExplicit
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Ford's elementary logarithmic-derivative bound

This file formalizes the second line of Ford's lemma `zeta basic`.  The
finite identities below are the summation-by-parts calculation in the source;
they are stated separately so that the strict inequality and its endpoint
terms remain visible to the later zero detector.
-/

open Complex Set MeasureTheory Filter Topology

namespace GafniTao

noncomputable def fordRpowTerm (sigma : ℝ) (m : ℕ) : ℝ :=
  (((m + 1 : ℕ) : ℝ) ^ (-sigma))

noncomputable def fordLogStep (n : ℕ) : ℝ :=
  Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))

theorem ford_sum_logStep (M : ℕ) :
    ∑ n ∈ Finset.range M, fordLogStep n = Real.log (M + 1) := by
  induction M with
  | zero => simp [fordLogStep]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      unfold fordLogStep
      rw [Real.log_div (by positivity) (by positivity)]
      push_cast
      ring_nf

noncomputable def fordFiniteRpowTail (sigma : ℝ) (M n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (n + 1) M, fordRpowTerm sigma m

theorem fordFiniteRpowTail_succ
    (sigma : ℝ) {M n : ℕ} (hn : n < M) :
    fordFiniteRpowTail sigma (M + 1) n =
      fordFiniteRpowTail sigma M n + fordRpowTerm sigma M := by
  unfold fordFiniteRpowTail
  rw [Finset.sum_Ico_succ_top (by omega)]

theorem ford_finite_log_moment_eq (sigma : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.range M,
        fordRpowTerm sigma m * Real.log (m + 1)) =
      ∑ n ∈ Finset.range M,
        fordLogStep n * fordFiniteRpowTail sigma M n := by
  induction M with
  | zero => simp [fordFiniteRpowTail]
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hlast : fordFiniteRpowTail sigma (M + 1) M = 0 := by
        simp [fordFiniteRpowTail]
      rw [hlast, mul_zero, add_zero]
      have hsumTail :
          (∑ n ∈ Finset.range M,
              fordLogStep n * fordFiniteRpowTail sigma (M + 1) n) =
            ∑ n ∈ Finset.range M,
              fordLogStep n *
                (fordFiniteRpowTail sigma M n + fordRpowTerm sigma M) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [fordFiniteRpowTail_succ sigma (M := M) (n := n) (by simpa using hn)]
      rw [hsumTail]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← ih]
      rw [← Finset.sum_mul]
      rw [ford_sum_logStep]
      ring_nf

theorem fordFiniteRpowTail_le
    {sigma : ℝ} (hsigma : 1 < sigma) (M n : ℕ) :
    fordFiniteRpowTail sigma M n ≤
      (((n + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1) := by
  by_cases hn : n + 1 ≤ M
  · have hanti : AntitoneOn (fun x : ℝ => x ^ (-sigma))
        (Icc ((n + 1 : ℕ) : ℝ) (M : ℝ)) := by
      apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (show -sigma ≤ 0 by linarith)).mono
      intro x hx
      exact (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)).trans_le hx.1
    unfold fordFiniteRpowTail fordRpowTerm
    have hsum := hanti.sum_le_integral_Ico hn
    calc
      ∑ m ∈ Finset.Ico (n + 1) M, ((m + 1 : ℕ) : ℝ) ^ (-sigma) ≤
          ∫ x in ((n : ℝ) + 1)..(M : ℝ), x ^ (-sigma) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hsum
      _ = ((((n + 1 : ℕ) : ℝ) ^ (1 - sigma)) -
            (M : ℝ) ^ (1 - sigma)) / (sigma - 1) := by
          rw [integral_rpow]
          · rw [show -sigma + 1 = -(sigma - 1) by ring_nf, div_neg]
            push_cast
            ring_nf
          · right
            constructor
            · linarith
            · rw [uIcc_of_le]
              · intro hzero
                exact (not_lt_of_ge hzero.1) (by positivity)
              · norm_cast
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1) := by
          have hden : 0 < sigma - 1 := by linarith
          have hpow : 0 ≤ (M : ℝ) ^ (1 - sigma) := Real.rpow_nonneg (by positivity) _
          exact (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  · have hempty : Finset.Ico (n + 1) M = ∅ :=
      Finset.Ico_eq_empty_of_le (by omega)
    rw [fordFiniteRpowTail, hempty, Finset.sum_empty]
    positivity

theorem fordLogStep_nonneg (n : ℕ) : 0 ≤ fordLogStep n := by
  unfold fordLogStep
  apply Real.log_nonneg
  rw [one_le_div (by positivity)]
  norm_num

theorem fordLogStep_lt (n : ℕ) :
    fordLogStep n < 1 / ((n + 1 : ℕ) : ℝ) := by
  unfold fordLogStep
  have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hne : (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≠ 1 := by
    intro h
    have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hden] at h
    norm_cast at h
    omega
  have h := Real.log_lt_sub_one_of_pos hpos hne
  calc
    Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) <
        (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) - 1 := h
    _ = 1 / ((n + 1 : ℕ) : ℝ) := by
      field_simp
      push_cast
      ring_nf

theorem ford_rpow_envelope_eq
    (sigma : ℝ) (n : ℕ) :
    (1 / ((n + 1 : ℕ) : ℝ)) *
          ((((n + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1)) =
      fordRpowTerm sigma n / (sigma - 1) := by
  unfold fordRpowTerm
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [one_div, ← Real.rpow_neg_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
  rw [← Real.rpow_add hx]
  congr 1
  ring_nf

theorem fordFiniteRpowTail_pos
    {sigma : ℝ} {M : ℕ} (hM : 2 ≤ M) :
    0 < fordFiniteRpowTail sigma M 0 := by
  have hmem : 1 ∈ Finset.Ico (0 + 1) M := by
    simp only [Finset.mem_Ico]
    omega
  have hnonneg (m : ℕ) : 0 ≤ fordRpowTerm sigma m := by
    exact Real.rpow_nonneg (by positivity) _
  have hle : fordRpowTerm sigma 1 ≤ fordFiniteRpowTail sigma M 0 := by
    unfold fordFiniteRpowTail
    exact Finset.single_le_sum (fun m _ => hnonneg m) hmem
  exact (Real.rpow_pos_of_pos (by positivity) _).trans_le hle

theorem ford_finite_log_moment_lt
    {sigma : ℝ} (hsigma : 1 < sigma) {M : ℕ} (hM : 2 ≤ M) :
    (∑ m ∈ Finset.range M,
        fordRpowTerm sigma m * Real.log (m + 1)) <
      (∑ m ∈ Finset.range M, fordRpowTerm sigma m) / (sigma - 1) := by
  rw [ford_finite_log_moment_eq]
  rw [Finset.sum_div]
  apply Finset.sum_lt_sum
  · intro n hn
    have htailNonneg : 0 ≤ fordFiniteRpowTail sigma M n := by
      unfold fordFiniteRpowTail
      exact Finset.sum_nonneg fun m _ => Real.rpow_nonneg (by positivity) _
    calc
      fordLogStep n * fordFiniteRpowTail sigma M n ≤
          (1 / ((n + 1 : ℕ) : ℝ)) * fordFiniteRpowTail sigma M n :=
        mul_le_mul_of_nonneg_right (fordLogStep_lt n).le htailNonneg
      _ ≤ (1 / ((n + 1 : ℕ) : ℝ)) *
          ((((n + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1)) :=
        mul_le_mul_of_nonneg_left (fordFiniteRpowTail_le hsigma M n) (by positivity)
      _ = fordRpowTerm sigma n / (sigma - 1) :=
        ford_rpow_envelope_eq sigma n
  · refine ⟨0, by simp [show 0 < M by omega], ?_⟩
    have htailPos : 0 < fordFiniteRpowTail sigma M 0 :=
      fordFiniteRpowTail_pos hM
    have hstrict :
        fordLogStep 0 * fordFiniteRpowTail sigma M 0 <
          (1 / (((0 + 1 : ℕ) : ℝ)) * fordFiniteRpowTail sigma M 0) :=
      mul_lt_mul_of_pos_right (fordLogStep_lt 0) htailPos
    exact hstrict.trans_le <| by
      calc
        (1 / (((0 + 1 : ℕ) : ℝ)) * fordFiniteRpowTail sigma M 0) ≤
            (1 / (((0 + 1 : ℕ) : ℝ)) *
              ((((0 + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1))) :=
          mul_le_mul_of_nonneg_left (fordFiniteRpowTail_le hsigma M 0) (by positivity)
        _ = fordRpowTerm sigma 0 / (sigma - 1) :=
          ford_rpow_envelope_eq sigma 0

theorem ford_finite_log_moment_le_split
    {sigma : ℝ} (hsigma : 1 < sigma) (M : ℕ) :
    (∑ m ∈ Finset.range (M + 1),
        fordRpowTerm sigma m * Real.log (m + 1)) ≤
      Real.log 2 / (sigma - 1) +
        ∑ n ∈ Finset.range M, fordRpowTerm sigma (n + 1) / (sigma - 1) := by
  rw [ford_finite_log_moment_eq, Finset.sum_range_succ']
  rw [add_comm (Real.log 2 / (sigma - 1))]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro n hn
    have htailNonneg : 0 ≤ fordFiniteRpowTail sigma (M + 1) (n + 1) := by
      unfold fordFiniteRpowTail
      exact Finset.sum_nonneg fun m _ => Real.rpow_nonneg (by positivity) _
    calc
      fordLogStep (n + 1) * fordFiniteRpowTail sigma (M + 1) (n + 1) ≤
          (1 / (((n + 1) + 1 : ℕ) : ℝ)) *
            fordFiniteRpowTail sigma (M + 1) (n + 1) :=
        mul_le_mul_of_nonneg_right (fordLogStep_lt (n + 1)).le htailNonneg
      _ ≤ (1 / (((n + 1) + 1 : ℕ) : ℝ)) *
          (((((n + 1) + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1)) :=
        mul_le_mul_of_nonneg_left
          (fordFiniteRpowTail_le hsigma (M + 1) (n + 1)) (by positivity)
      _ = fordRpowTerm sigma (n + 1) / (sigma - 1) :=
        ford_rpow_envelope_eq sigma (n + 1)
  · calc
      fordLogStep 0 * fordFiniteRpowTail sigma (M + 1) 0 ≤
          fordLogStep 0 *
            ((((0 + 1 : ℕ) : ℝ) ^ (1 - sigma)) / (sigma - 1)) :=
        mul_le_mul_of_nonneg_left
          (fordFiniteRpowTail_le hsigma (M + 1) 0) (fordLogStep_nonneg 0)
      _ = Real.log 2 / (sigma - 1) := by
        norm_num [fordLogStep, div_eq_mul_inv]

theorem summable_fordRpowTerm {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fordRpowTerm sigma) := by
  have hall : Summable (fun n : ℕ => ((n : ℝ) ^ (-sigma))) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_nat_rpow_inv.mpr hsigma)
  apply ((summable_nat_add_iff 1).mpr hall).congr
  intro n
  simp only [fordRpowTerm, Nat.cast_add, Nat.cast_one]

theorem summable_fordRpowTerm_succ {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => fordRpowTerm sigma (n + 1)) := by
  exact (summable_nat_add_iff 1).mpr (summable_fordRpowTerm hsigma)

theorem ford_tsum_rpowTerm_succ_eq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, fordRpowTerm sigma (n + 1)) =
      (riemannZeta (sigma : ℂ)).re - 1 := by
  have hfull := summable_fordRpowTerm hsigma
  have hsplit := hfull.tsum_eq_zero_add
  rw [ford_riemannZeta_real_series hsigma]
  change (∑' n : ℕ, fordRpowTerm sigma (n + 1)) =
    (∑' n : ℕ, fordRpowTerm sigma n) - 1
  rw [hsplit]
  norm_num [fordRpowTerm]

theorem summable_ford_log_moment {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun m : ℕ =>
      fordRpowTerm sigma m * Real.log (m + 1)) := by
  have hshift := summable_fordRpowTerm_succ hsigma
  apply summable_of_sum_range_le
    (c := Real.log 2 / (sigma - 1) +
      (∑' n : ℕ, fordRpowTerm sigma (n + 1)) / (sigma - 1))
  · intro m
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.log_nonneg (by norm_num))
  · intro N
    cases N with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        have hlogNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hden : 0 < sigma - 1 := by linarith
        exact add_nonneg (div_nonneg hlogNonneg hden.le)
          (div_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _) hden.le)
    | succ M =>
        refine (ford_finite_log_moment_le_split hsigma M).trans ?_
        have hsumDiv :
            (∑ n ∈ Finset.range M,
                fordRpowTerm sigma (n + 1) / (sigma - 1)) ≤
              (∑' n : ℕ, fordRpowTerm sigma (n + 1)) / (sigma - 1) := by
          rw [← Finset.sum_div]
          apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ sigma - 1)
          exact hshift.sum_le_tsum (Finset.range M)
            (fun n _ => Real.rpow_nonneg (by positivity) _)
        exact add_le_add_right hsumDiv _

theorem ford_tsum_log_moment_le_split
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' m : ℕ, fordRpowTerm sigma m * Real.log (m + 1)) ≤
      Real.log 2 / (sigma - 1) +
        (∑' n : ℕ, fordRpowTerm sigma (n + 1)) / (sigma - 1) := by
  have hleftBase := (summable_ford_log_moment hsigma).hasSum.tendsto_sum_nat
  have hleft : Tendsto
      (fun M : ℕ => ∑ m ∈ Finset.range (M + 1),
        fordRpowTerm sigma m * Real.log (m + 1))
      atTop
      (nhds (∑' m : ℕ, fordRpowTerm sigma m * Real.log (m + 1))) := by
    simpa only [Nat.add_comm] using hleftBase.comp (tendsto_add_atTop_nat 1)
  have hshift := summable_fordRpowTerm_succ hsigma
  have hright : Tendsto
      (fun M : ℕ => Real.log 2 / (sigma - 1) +
        (∑ n ∈ Finset.range M, fordRpowTerm sigma (n + 1) / (sigma - 1)))
      atTop
      (nhds (Real.log 2 / (sigma - 1) +
        (∑' n : ℕ, fordRpowTerm sigma (n + 1)) / (sigma - 1))) := by
    apply tendsto_const_nhds.add
    simpa only [tsum_div_const] using
      (hshift.div_const (sigma - 1)).hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto' hleft hright fun M =>
    ford_finite_log_moment_le_split hsigma M

theorem ford_tsum_log_moment_lt_zeta_div
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' m : ℕ, fordRpowTerm sigma m * Real.log (m + 1)) <
      (riemannZeta (sigma : ℂ)).re / (sigma - 1) := by
  refine (ford_tsum_log_moment_le_split hsigma).trans_lt ?_
  rw [ford_tsum_rpowTerm_succ_eq hsigma]
  have hlog : Real.log 2 < 1 := by
    simpa [fordLogStep] using fordLogStep_lt 0
  have hden : 0 < sigma - 1 := by linarith
  rw [← add_div]
  apply (div_lt_div_iff_of_pos_right hden).mpr
  linarith

theorem ford_neg_deriv_riemannZeta_eq_log_moment
    {sigma : ℝ} (hsigma : 1 < sigma) :
    -deriv riemannZeta (sigma : ℂ) =
      ((∑' m : ℕ, fordRpowTerm sigma m * Real.log (m + 1)) : ℝ) := by
  have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
  have habscissa : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ((sigma : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hsigma
  have hderivEq :
      deriv (LSeries (1 : ℕ → ℂ)) (sigma : ℂ) =
        deriv riemannZeta (sigma : ℂ) := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z | 1 < z.re},
      (isOpen_lt continuous_const continuous_re).mem_nhds hs,
      fun _ => LSeries_one_eq_riemannZeta⟩
  rw [← hderivEq, LSeries_deriv habscissa, neg_neg]
  unfold LSeries
  have hsumComplex : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) (sigma : ℂ) :=
    LSeriesSummable_logMul_of_lt_re habscissa
  rw [hsumComplex.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  rw [LSeries.term_of_ne_zero (by omega : m + 1 ≠ 0)]
  simp only [LSeries.logMul, Pi.one_apply, mul_one]
  rw [show ((m + 1 : ℕ) : ℂ) = ((((m + 1 : ℕ) : ℝ) : ℂ)) by rfl]
  rw [← Complex.ofReal_cpow (x := ((m + 1 : ℕ) : ℝ)) (by positivity)
    (y := sigma)]
  unfold fordRpowTerm
  rw [Real.rpow_neg (by positivity)]
  rw [Complex.ofReal_mul, Complex.ofReal_log (by positivity), Complex.ofReal_inv]
  rw [mul_comm]
  congr 2
  push_cast
  rfl

theorem ford_norm_deriv_riemannZeta_real_eq_log_moment
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖deriv riemannZeta (sigma : ℂ)‖ =
      ∑' m : ℕ, fordRpowTerm sigma m * Real.log (m + 1) := by
  rw [← norm_neg, ford_neg_deriv_riemannZeta_eq_log_moment hsigma,
    norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact tsum_nonneg fun m => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.log_nonneg (by norm_num))

theorem ford_norm_logDerivative_real_lt
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ)‖ <
      1 / (sigma - 1) := by
  have hzetaPos : 0 < (riemannZeta (sigma : ℂ)).re := by
    simpa using (riemannZeta_pos_of_one_lt hsigma).1
  rw [norm_div, ford_norm_deriv_riemannZeta_real_eq_log_moment hsigma,
    ford_riemannZeta_real_norm hsigma]
  rw [div_lt_iff₀ hzetaPos]
  simpa [div_eq_mul_inv, mul_comm] using ford_tsum_log_moment_lt_zeta_div hsigma

theorem ford_zeta_basic_logDerivative
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖-deriv riemannZeta ((sigma : ℂ) + Complex.I * t) /
        riemannZeta ((sigma : ℂ) + Complex.I * t)‖ <
      1 / (sigma - 1) :=
  (ford_norm_logDerivative_le_real hsigma).trans_lt
    (ford_norm_logDerivative_real_lt hsigma)

end GafniTao
