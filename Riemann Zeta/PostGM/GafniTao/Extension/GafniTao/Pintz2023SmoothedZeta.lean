import GafniTao.Pintz2023HalaszDiagonal

/-!
# Pintz (2023), Lemma 3.4: the smoothed zeta series

This is the exact infinite series on the left of (3.4).  Exponential decay
gives absolute convergence throughout the half-plane used in (4.19), and
the finite Gram cutoffs converge to this literal series.
-/

open Complex Finset Filter Topology
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

noncomputable def pintz2023SmoothedZetaTerm
    (N : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    ((pintz2023HalaszKernel N n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

noncomputable def pintz2023SmoothedZetaSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, pintz2023SmoothedZetaTerm N s n

theorem summable_pintz2023SmoothedZetaTerm
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    Summable (pintz2023SmoothedZetaTerm N s) := by
  let c : ℝ := -1 / (2 * (N : ℝ))
  have hc : c < 0 := by
    dsimp only [c]
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_neg_of_neg_of_pos (by norm_num) (mul_pos (by norm_num) hNReal)
  have hgeom : Summable (fun n : ℕ => Real.exp (n * c)) :=
    Real.summable_exp_nat_mul_iff.mpr hc
  apply Summable.of_norm_bounded (g := fun n : ℕ => Real.exp (n * c)) hgeom
  intro n
  by_cases hn : n = 0
  · simp [pintz2023SmoothedZetaTerm, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    have hkernelPos := pintz2023HalaszKernel_pos hN hnPos
    have hkernelExp :
        pintz2023HalaszKernel N n ≤
          Real.exp (-(n : ℝ) / (2 * N)) := by
      unfold pintz2023HalaszKernel
      linarith [Real.exp_pos (-(n : ℝ) / N)]
    have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnReal]
      have hexponent : (-s).re = -s.re := by simp
      rw [hexponent]
      exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr hs)
    rw [pintz2023SmoothedZetaTerm, if_neg hn, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkernelPos]
    calc
      pintz2023HalaszKernel N n * ‖(n : ℂ) ^ (-s)‖ ≤
          Real.exp (-(n : ℝ) / (2 * N)) * 1 := by
        exact mul_le_mul hkernelExp hpow (norm_nonneg _)
          (Real.exp_pos _).le
      _ = Real.exp (n * c) := by
        dsimp only [c]
        have hNReal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp [hNReal]

theorem pintz2023SmoothedZetaTerm_eq
    {N n : ℕ} {s : ℂ} (hn : 0 < n) :
    pintz2023SmoothedZetaTerm N s n =
      ((pintz2023HalaszKernel N n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  simp [pintz2023SmoothedZetaTerm, hn.ne']

theorem sum_Icc_pintz2023SmoothedZetaTerm_eq
    (N M : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n) =
      ∑ n ∈ Finset.range (M + 1), pintz2023SmoothedZetaTerm N s n := by
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_range]
    have hnM := (Finset.mem_Icc.mp hn).2
    omega
  · intro n hnRange hnNotIcc
    have hnZero : n = 0 := by
      rw [Finset.mem_range] at hnRange
      by_contra hnNe
      apply hnNotIcc
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hnNe, by omega⟩
    subst n
    simp [pintz2023SmoothedZetaTerm]

theorem tendsto_sum_Icc_pintz2023SmoothedZetaTerm
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    Tendsto (fun M : ℕ =>
      ∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n)
      atTop (nhds (pintz2023SmoothedZetaSum N s)) := by
  have hsum := (summable_pintz2023SmoothedZetaTerm hN hs).hasSum.tendsto_sum_nat
  rw [show pintz2023SmoothedZetaSum N s =
      ∑' n : ℕ, pintz2023SmoothedZetaTerm N s n by rfl]
  apply (hsum.comp (tendsto_add_atTop_nat 1)).congr'
  filter_upwards with M
  exact (sum_Icc_pintz2023SmoothedZetaTerm_eq N M s).symm

/-- The finite Gram sums converge to the exact infinite series in Lemma
3.4, with no unspecified remainder. -/
theorem tendsto_pintz2023HalaszFiniteGram
    {N : ℕ} (eta etaJ etaK gamma delta : ℝ) (hN : 0 < N)
    (hreal : 0 ≤ 1 - etaJ - etaK - 4 * eta) :
    Tendsto (fun M : ℕ =>
      pintz2023HalaszFiniteGram N M eta etaJ etaK gamma delta)
      atTop
      (nhds (pintz2023SmoothedZetaSum N
        (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
          I * ((delta - gamma : ℝ) : ℂ)))) := by
  let s : ℂ :=
    ((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
      I * ((delta - gamma : ℝ) : ℂ)
  have hs : 0 ≤ s.re := by
    dsimp only [s]
    simpa using hreal
  have hlim := tendsto_sum_Icc_pintz2023SmoothedZetaTerm hN hs
  apply hlim.congr'
  filter_upwards with M
  unfold pintz2023HalaszFiniteGram
  apply Finset.sum_congr rfl
  intro n hn
  rw [pintz2023SmoothedZetaTerm_eq
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)]

#print axioms summable_pintz2023SmoothedZetaTerm
#print axioms tendsto_sum_Icc_pintz2023SmoothedZetaTerm
#print axioms tendsto_pintz2023HalaszFiniteGram

end

end GafniTao
