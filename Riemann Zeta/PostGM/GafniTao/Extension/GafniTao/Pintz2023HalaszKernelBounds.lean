import GafniTao.Pintz2023HalaszVectors

/-!
# Pintz (2023), equations (4.18) and (4.22): kernel bounds

These are bounds for the literal kernel `exp (-n/(2N)) - exp (-n/N)`.
The upper estimate is the source's small-block estimate (4.22).  The lower
estimate on `(N,2N]` makes the reciprocal square-root in `d_n` quantitative.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem pintz2023HalaszKernel_factor
    {N n : ℕ} (hN : 0 < N) :
    pintz2023HalaszKernel N n =
      Real.exp (-(n : ℝ) / (2 * N)) *
        (1 - Real.exp (-(n : ℝ) / (2 * N))) := by
  have hNReal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hexponent :
      -(n : ℝ) / N =
        -(n : ℝ) / (2 * N) + -(n : ℝ) / (2 * N) := by
    field_simp [hNReal]
    ring
  unfold pintz2023HalaszKernel
  rw [hexponent, Real.exp_add]
  ring

/-- Pintz (4.22), with an explicit constant `1/2`. -/
theorem pintz2023HalaszKernel_le_div
    {N n : ℕ} (hN : 0 < N) :
    pintz2023HalaszKernel N n ≤ (n : ℝ) / (2 * N) := by
  let x : ℝ := (n : ℝ) / (2 * N)
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hexpNonneg : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hexpLe : Real.exp (-x) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have honeSubNonneg : 0 ≤ 1 - Real.exp (-x) := sub_nonneg.mpr hexpLe
  have honeSubLe : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  rw [pintz2023HalaszKernel_factor hN]
  have hresult : Real.exp (-x) * (1 - Real.exp (-x)) ≤ x := by
    calc
    Real.exp (-x) * (1 - Real.exp (-x)) ≤
        1 * (1 - Real.exp (-x)) :=
      mul_le_mul_of_nonneg_right hexpLe honeSubNonneg
    _ ≤ x := by simpa using honeSubLe
  dsimp only [x] at hresult
  simpa only [neg_div] using hresult

theorem pintz2023HalaszKernel_le_one
    {N n : ℕ} (hN : 0 < N) :
    pintz2023HalaszKernel N n ≤ 1 := by
  rw [pintz2023HalaszKernel_factor hN]
  have hfirst : Real.exp (-(n : ℝ) / (2 * N)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (Nat.cast_nonneg n)
    · positivity
  have hsecond : 1 - Real.exp (-(n : ℝ) / (2 * N)) ≤ 1 := by
    linarith [Real.exp_pos (-(n : ℝ) / (2 * N))]
  have hsecondNonneg :
      0 ≤ 1 - Real.exp (-(n : ℝ) / (2 * N)) := by
    have := hfirst
    linarith
  calc
    Real.exp (-(n : ℝ) / (2 * N)) *
        (1 - Real.exp (-(n : ℝ) / (2 * N))) ≤
      1 * 1 := mul_le_mul hfirst hsecond hsecondNonneg (by positivity)
    _ = 1 := mul_one 1

/-- A uniform positive lower bound for the kernel on the selected dyadic
interval `(N,2N]`. -/
theorem pintz2023HalaszKernel_lower_Ioc
    {N n : ℕ} (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2 * N)) :
    Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))) ≤
      pintz2023HalaszKernel N n := by
  let x : ℝ := (n : ℝ) / (2 * N)
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnLower : (N : ℝ) < n := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hnUpper : (n : ℝ) ≤ 2 * N := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hxLower : (1 / 2 : ℝ) ≤ x := by
    dsimp only [x]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    nlinarith
  have hxUpper : x ≤ 1 := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    nlinarith
  have hfirst : Real.exp (-1) ≤ Real.exp (-x) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hxUpper)
  have hsecond :
      1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 - Real.exp (-x) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hxLower)
    linarith
  have hfirstNonneg : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hsecondNonneg :
      0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
    have : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  rw [pintz2023HalaszKernel_factor hN]
  have hresult :
      Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))) ≤
        Real.exp (-x) * (1 - Real.exp (-x)) :=
    mul_le_mul hfirst hsecond hsecondNonneg
      ((Real.exp_pos _).le.trans hfirst)
  dsimp only [x] at hresult
  simpa only [neg_div] using hresult

theorem pintz2023HalaszKernel_uniform_lower_pos :
    0 < Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))) := by
  apply mul_pos (Real.exp_pos _)
  rw [sub_pos]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

#print axioms pintz2023HalaszKernel_factor
#print axioms pintz2023HalaszKernel_le_div
#print axioms pintz2023HalaszKernel_le_one
#print axioms pintz2023HalaszKernel_lower_Ioc

end

end GafniTao
