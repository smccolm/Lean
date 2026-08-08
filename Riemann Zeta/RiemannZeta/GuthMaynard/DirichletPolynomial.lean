import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import RiemannZeta.FiniteDirichletPolynomial

open Complex Finset

namespace RiemannZeta.GuthMaynard

/-- 
The exact interval convention used in Section 13.1 for dyadic Dirichlet polynomials.
`n ∼ N` is interpreted as `n ∈ (N, 2N]`, which matches `Finset.Ioc N (2 * N)`.
-/
def dyadicInterval (N : ℕ) : Finset ℕ :=
  Ioc N (2 * N)

/-- 
An interval-indexed Dirichlet polynomial $D_N(t) = \sum_{n \sim N} a_n n^{-it}$.
-/
noncomputable def dirichletPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (-t * I)

/-- The positive-sign convention used in Guth--Maynard Theorem 1.1. -/
noncomputable def sourceDirichletPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (t * I)

/-- Pointwise complex conjugation of a coefficient sequence. -/
noncomputable def conjugateCoeffs (a : ℕ → ℂ) (n : ℕ) : ℂ := star (a n)

/-- The positive- and negative-sign Dirichlet-polynomial conventions have the
same norms after conjugating the arbitrary coefficient sequence. -/
theorem norm_sourceDirichletPoly_conjugateCoeffs
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceDirichletPoly N (conjugateCoeffs a) t‖ = ‖dirichletPoly N a t‖ := by
  have hstar : star (sourceDirichletPoly N (conjugateCoeffs a) t) = dirichletPoly N a t := by
    unfold sourceDirichletPoly conjugateCoeffs dirichletPoly
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [star_mul, star_star,
      mul_comm (star ((n : ℂ) ^ ((t : ℂ) * I))) (a n)]
    congr 1
    have hnPos : 0 < n := by
      rw [dyadicInterval, Finset.mem_Ioc] at hn
      omega
    have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
      change ((((n : ℝ) : ℂ)).arg ≠ Real.pi)
      rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      exact Real.pi_ne_zero.symm
    have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [hnCast]
    have hConj := Complex.cpow_conj (((n : ℝ) : ℂ)) ((t : ℂ) * I) hnArg
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hConj
    convert hConj.symm using 1
    ring_nf
  rw [← hstar, norm_star]

theorem norm_conjugateCoeffs (a : ℕ → ℂ) (n : ℕ) :
    ‖conjugateCoeffs a n‖ = ‖a n‖ := by
  exact norm_star _

/--
Twist coefficients by the unimodular phase produced when the ordinate is
translated by `c`.  The value at `0` is left unchanged; dyadic intervals never
use that index, and this convention makes norm preservation unconditional.
-/
noncomputable def phaseShiftCoeffs (c : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then a n else a n * (n : ℂ) ^ (-c * I)

/-- Translating the ordinate is exactly coefficient phase twisting. -/
theorem dirichletPoly_translate (N : ℕ) (a : ℕ → ℂ) (c t : ℝ) :
    dirichletPoly N a (t + c) = dirichletPoly N (phaseShiftCoeffs c a) t := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [phaseShiftCoeffs, if_neg hnPos.ne']
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- The coefficient twist used for ordinate translation preserves every norm. -/
theorem norm_phaseShiftCoeffs (c : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖phaseShiftCoeffs c a n‖ = ‖a n‖ := by
  by_cases hn : n = 0
  · simp [phaseShiftCoeffs, hn]
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [phaseShiftCoeffs, if_neg hn, norm_mul]
    change ‖a n‖ * ‖((n : ℝ) : ℂ) ^ (-c * I)‖ = ‖a n‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    simp

/-- 
The normalized coefficients $\widetilde{b}_n = (N/n)^\sigma b_n$. 
-/
noncomputable def normalizedCoeffs (N : ℕ) (σ : ℝ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((N : ℝ) / (n : ℝ) : ℂ) ^ (σ : ℂ) * b n

/--
A bridge from the interval-indexed `dirichletPoly` to the existing `RiemannZeta.dirichletPoly` over `PNat`.
-/
theorem dirichletPoly_eq_existing (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPoly N a t = 
      RiemannZeta.dirichletPoly 
        (fun n => a n.val) 
        ((dyadicInterval N).subtype (fun n => 0 < n)) 
        (t * I) := by
  dsimp [dirichletPoly, RiemannZeta.dirichletPoly]
  apply Finset.sum_bij (fun (n : ℕ) _ => (⟨n, by 
      have hn : n ∈ dyadicInterval N := by assumption
      rw [dyadicInterval, mem_Ioc] at hn
      omega⟩ : { n // 0 < n }))
  case hi =>
    intro n hn
    simp only [mem_subtype]
    exact hn
  case h =>
    intro n hn
    simp
  case i_inj =>
    intro n1 hn1 n2 hn2 h_eq
    exact Subtype.mk.inj h_eq
  case i_surj =>
    intro b hb
    simp only [mem_subtype] at hb
    exact ⟨b.val, hb, Subtype.ext rfl⟩

/-- The pointwise bound on the normalized coefficients. -/
lemma norm_normalizedCoeffs_le (N : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (b : ℕ → ℂ) (n : ℕ) (hn : n ∈ dyadicInterval N) :
    ‖normalizedCoeffs N σ b n‖ ≤ ‖b n‖ := by
  dsimp [normalizedCoeffs]
  rw [norm_mul]
  have h_pos_nat : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  have h_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr h_pos_nat
  have h_N_le_n : (N : ℝ) ≤ (n : ℝ) := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    exact Nat.cast_le.mpr hn.1.le
  have h_frac_le_one : (N : ℝ) / (n : ℝ) ≤ 1 := (div_le_one h_pos).mpr h_N_le_n
  have h_frac_nonneg : 0 ≤ (N : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) h_pos.le
  
  have h_cpow : ‖((N : ℝ) / (n : ℝ) : ℂ) ^ (σ : ℂ)‖ = ((N : ℝ) / (n : ℝ)) ^ σ := by
    have h1 : ((N : ℝ) / (n : ℝ) : ℂ) = (↑((N : ℝ) / (n : ℝ)) : ℂ) := by push_cast; rfl
    have h2 : (σ : ℂ) = ↑σ := rfl
    rw [h1, h2]
    rw [Complex.norm_cpow_real]
    congr 1
    rw [Complex.norm_real]
    exact abs_of_nonneg h_frac_nonneg

  have h_replace : ‖((N : ℝ) / (n : ℝ) : ℂ) ^ (σ : ℂ)‖ * ‖b n‖ ≤ ‖b n‖ := by
    rw [h_cpow]
    have h_pow_le_one : ((N : ℝ) / (n : ℝ)) ^ σ ≤ 1 := by
      exact Real.rpow_le_one h_frac_nonneg h_frac_le_one hσ
    exact mul_le_of_le_one_left (norm_nonneg _) h_pow_le_one
  exact h_replace

/-- 
Convolution support: If $n_1 \in (N_1, 2N_1]$ and $n_2 \in (N_2, 2N_2]$, 
then $n_1 n_2 \in (N_1 N_2, 4 N_1 N_2]$. 
-/
lemma convolution_support (N₁ N₂ n₁ n₂ : ℕ) (hn₁ : n₁ ∈ dyadicInterval N₁) (hn₂ : n₂ ∈ dyadicInterval N₂) :
    n₁ * n₂ ∈ Ioc (N₁ * N₂) (4 * N₁ * N₂) := by
  rw [dyadicInterval, Finset.mem_Ioc] at hn₁ hn₂
  rw [Finset.mem_Ioc]
  constructor
  · have h1 : (N₁ : ℝ) < (n₁ : ℝ) := Nat.cast_lt.mpr hn₁.1
    have h2 : (N₂ : ℝ) < (n₂ : ℝ) := Nat.cast_lt.mpr hn₂.1
    have hN1 : 0 ≤ (N₁ : ℝ) := Nat.cast_nonneg _
    have hN2 : 0 ≤ (N₂ : ℝ) := Nat.cast_nonneg _
    have res : (N₁ : ℝ) * (N₂ : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by nlinarith
    exact Nat.cast_lt.mp (by exact_mod_cast res)
  · have h1 : (n₁ : ℝ) ≤ 2 * (N₁ : ℝ) := by exact_mod_cast hn₁.2
    have h2 : (n₂ : ℝ) ≤ 2 * (N₂ : ℝ) := by exact_mod_cast hn₂.2
    have hn1 : 0 ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    have hn2 : 0 ≤ (n₂ : ℝ) := Nat.cast_nonneg _
    have res : (n₁ : ℝ) * (n₂ : ℝ) ≤ 4 * (N₁ : ℝ) * (N₂ : ℝ) := by nlinarith
    exact Nat.cast_le.mp (by exact_mod_cast res)


end RiemannZeta.GuthMaynard
