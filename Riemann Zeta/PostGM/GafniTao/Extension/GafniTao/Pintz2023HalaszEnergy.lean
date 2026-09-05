import GafniTao.Pintz2023HalaszAmbient

/-!
# Pintz (2023), equation (4.19): exact `d_n` energy

This file expands the first Cauchy--Schwarz factor without asymptotic
notation.  Its kernel reciprocal and exponent are therefore visible to the
later dyadic estimate.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem norm_pintz2023HalaszD_sq
    {N n : ℕ} (b : ℕ → ℂ) (eta lambda : ℝ)
    (hN : 0 < N) (hn : 0 < n) :
    ‖pintz2023HalaszD b N eta lambda n‖ ^ 2 =
      ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
        (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) := by
  have hkernel : 0 < pintz2023HalaszKernel N n :=
    pintz2023HalaszKernel_pos hN hn
  have hsqrt : 0 < Real.sqrt (pintz2023HalaszKernel N n) :=
    Real.sqrt_pos.2 hkernel
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pintz2023HalaszD
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hsqrt]
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnReal]
  have hexponent :
      (-(((1 / 2 + 2 * eta + 1 / lambda : ℝ) : ℂ))).re =
        -(1 / 2 + 2 * eta + 1 / lambda) := by norm_num
  rw [hexponent]
  have hsqrtSq :
      (Real.sqrt (pintz2023HalaszKernel N n)) ^ 2 =
        pintz2023HalaszKernel N n := Real.sq_sqrt hkernel.le
  have hinvSq :
      (Real.sqrt (pintz2023HalaszKernel N n))⁻¹ ^ 2 =
        (pintz2023HalaszKernel N n)⁻¹ := by
    rw [inv_pow, hsqrtSq]
  have hrpowSq :
      ((n : ℝ) ^ (-(1 / 2 + 2 * eta + 1 / lambda))) ^ 2 =
        (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnReal.le]
    congr 2
    ring
  rw [mul_pow, mul_pow, hinvSq, hrpowSq]

theorem norm_pintz2023HalaszDSupported_sq
    {N n : ℕ} (Iset : Finset ℕ) (b : ℕ → ℂ)
    (eta lambda : ℝ) (hN : 0 < N) (hn : 0 < n) :
    ‖pintz2023HalaszDSupported Iset b N eta lambda n‖ ^ 2 =
      if n ∈ Iset then
        ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)
      else 0 := by
  by_cases hmem : n ∈ Iset
  · simp only [pintz2023HalaszDSupported, hmem, if_true]
    exact norm_pintz2023HalaszD_sq b eta lambda hN hn
  · simp [pintz2023HalaszDSupported, hmem]

/-- Exact restriction of the ambient `d_n` energy back to its support. -/
theorem sum_norm_pintz2023HalaszDSupported_sq
    {N : ℕ} (ambient Iset : Finset ℕ) (b : ℕ → ℂ)
    (eta lambda : ℝ) (hN : 0 < N)
    (hI : Iset ⊆ ambient) (hpositive : ∀ n ∈ ambient, 0 < n) :
    (∑ n ∈ ambient,
        ‖pintz2023HalaszDSupported Iset b N eta lambda n‖ ^ 2) =
      ∑ n ∈ Iset,
        ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) := by
  rw [← Finset.sum_subset hI]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [norm_pintz2023HalaszDSupported_sq Iset b eta lambda hN
      (hpositive n (hI hn)), if_pos hn]
  · intro n hnAmbient hnI
    rw [norm_pintz2023HalaszDSupported_sq Iset b eta lambda hN
      (hpositive n hnAmbient), if_neg hnI]

/-- Explicit dyadic estimate for Pintz's first Cauchy--Schwarz factor.
The small coefficient exponent is intentionally visible: it is later paid
from Pintz's epsilon budget rather than suppressed in `O` notation. -/
theorem sum_norm_pintz2023HalaszDSupported_sq_le
    {N : ℕ} (ambient Iset : Finset ℕ) (b : ℕ → ℂ)
    (eta lambda epsilon C : ℝ) (hN : 0 < N)
    (hIambient : Iset ⊆ ambient)
    (hpositive : ∀ n ∈ ambient, 0 < n)
    (hIdyadic : Iset ⊆ Finset.Ioc N (2 * N))
    (hC : 0 ≤ C)
    (hExponent : -1 - 4 * eta - 2 / lambda + 2 * epsilon ≤ 0)
    (hCoeff : ∀ n ∈ Iset, ‖b n‖ ≤ C * (n : ℝ) ^ epsilon) :
    (∑ n ∈ ambient,
        ‖pintz2023HalaszDSupported Iset b N eta lambda n‖ ^ 2) ≤
      C ^ 2 *
        (Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))))⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilon) := by
  rw [sum_norm_pintz2023HalaszDSupported_sq ambient Iset b eta lambda
    hN hIambient hpositive]
  let q : ℝ := Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ)))
  let p : ℝ := -1 - 4 * eta - 2 / lambda + 2 * epsilon
  have hq : 0 < q := pintz2023HalaszKernel_uniform_lower_pos
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hpoint : ∀ n ∈ Iset,
      ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) ≤
        C ^ 2 * q⁻¹ * (N : ℝ) ^ p := by
    intro n hn
    have hnDyadic := hIdyadic hn
    have hnPos : 0 < n := hpositive n (hIambient hn)
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnLower : (N : ℝ) ≤ n := by
      exact_mod_cast (Nat.le_of_lt (Finset.mem_Ioc.mp hnDyadic).1)
    have hkernel := pintz2023HalaszKernel_lower_Ioc hN hnDyadic
    have hkernelPos := pintz2023HalaszKernel_pos hN hnPos
    have hinv : (pintz2023HalaszKernel N n)⁻¹ ≤ q⁻¹ :=
      (inv_le_inv₀ hkernelPos hq).2 hkernel
    have hcoeffSq : ‖b n‖ ^ 2 ≤
        (C * (n : ℝ) ^ epsilon) ^ 2 := by
      have hb := hCoeff n hn
      have hright : 0 ≤ C * (n : ℝ) ^ epsilon := mul_nonneg hC (by positivity)
      exact (sq_le_sq₀ (norm_nonneg _) hright).2 hb
    have hrpowCombine :
        ((n : ℝ) ^ epsilon) ^ 2 *
            (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) =
          (n : ℝ) ^ p := by
      calc
        ((n : ℝ) ^ epsilon) ^ 2 *
            (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) =
          (n : ℝ) ^ (epsilon * 2) *
            (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hnReal.le]
              norm_num
        _ = (n : ℝ) ^
            (epsilon * 2 + (-1 - 4 * eta - 2 / lambda)) := by
              rw [Real.rpow_add hnReal]
        _ = (n : ℝ) ^ p := by
              apply congrArg (fun z : ℝ => (n : ℝ) ^ z)
              dsimp only [p]
              ring
    have hpNonpos : p ≤ 0 := by exact hExponent
    have hrpowMono : (n : ℝ) ^ p ≤ (N : ℝ) ^ p :=
      Real.rpow_le_rpow_of_nonpos hNReal hnLower hpNonpos
    calc
      ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) ≤
          (C * (n : ℝ) ^ epsilon) ^ 2 * q⁻¹ *
            (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) := by
        gcongr
      _ = C ^ 2 * q⁻¹ * (n : ℝ) ^ p := by
        rw [mul_pow]
        calc
          C ^ 2 * ((n : ℝ) ^ epsilon) ^ 2 * q⁻¹ *
              (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda) =
            C ^ 2 * q⁻¹ *
              (((n : ℝ) ^ epsilon) ^ 2 *
                (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) := by ring
          _ = _ := by rw [hrpowCombine]
      _ ≤ C ^ 2 * q⁻¹ * (N : ℝ) ^ p := by
        gcongr
  calc
    (∑ n ∈ Iset,
        ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) ≤
        (Iset.card : ℝ) *
          (C ^ 2 * q⁻¹ * (N : ℝ) ^ p) := by
      calc
        _ ≤ ∑ _n ∈ Iset,
            (C ^ 2 * q⁻¹ * (N : ℝ) ^ p) :=
          Finset.sum_le_sum hpoint
        _ = _ := by simp
    _ ≤ (N : ℝ) * (C ^ 2 * q⁻¹ * (N : ℝ) ^ p) := by
      gcongr
      exact_mod_cast Finset.card_le_card hIdyadic |>.trans_eq (by
        simp only [Nat.card_Ioc]
        omega)
    _ = C ^ 2 * q⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilon) := by
      calc
        (N : ℝ) * (C ^ 2 * q⁻¹ * (N : ℝ) ^ p) =
            C ^ 2 * q⁻¹ *
              ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ p) := by
          rw [Real.rpow_one]
          ring
        _ = C ^ 2 * q⁻¹ * (N : ℝ) ^ (1 + p) := by
          congr 1
          exact (Real.rpow_add hNReal 1 p).symm
        _ = _ := by
          congr 1
          apply congrArg (fun z : ℝ => (N : ℝ) ^ z)
          dsimp only [p]
          ring

/-- Source specialization of the preceding energy estimate to the exact
powered coefficient of a selected Pintz interval. -/
theorem exists_sum_norm_pintz2023IntervalPowerHalaszD_sq_le
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X U N : ℕ) (baseI ambient Iset : Finset ℕ)
        (eta lambda : ℝ),
        baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N →
        Iset ⊆ ambient → (∀ n ∈ ambient, 0 < n) →
        Iset ⊆ Finset.Ioc N (2 * N) →
        -1 - 4 * eta - 2 / lambda + 2 * epsilon ≤ 0 →
        (∑ n ∈ ambient,
          ‖pintz2023HalaszDSupported Iset
            (pintz2023IntervalPowerCoeff X baseI h) N eta lambda n‖ ^ 2) ≤
          C ^ 2 *
            (Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))))⁻¹ *
            (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilon) := by
  obtain ⟨C, hC, hCoeff⟩ :=
    pintz2023IntervalPowerCoeff_bound_native h epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro X U N baseI ambient Iset eta lambda hbaseI hU hN
    hIambient hpositive hIdyadic hExponent
  apply sum_norm_pintz2023HalaszDSupported_sq_le ambient Iset
    (pintz2023IntervalPowerCoeff X baseI h) eta lambda epsilon C hN
    hIambient hpositive hIdyadic hC.le hExponent
  intro n hn
  exact hCoeff X U n baseI hbaseI hU (hpositive n (hIambient hn))

#print axioms norm_pintz2023HalaszD_sq
#print axioms sum_norm_pintz2023HalaszDSupported_sq
#print axioms sum_norm_pintz2023HalaszDSupported_sq_le
#print axioms exists_sum_norm_pintz2023IntervalPowerHalaszD_sq_le

end

end GafniTao
