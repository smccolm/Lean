import Mathlib.Analysis.Normed.Ring.InfiniteSum
import RiemannZeta.GuthMaynard.LargeValuesLanguage
import RiemannZeta.GuthMaynard.LargeValuesReflection
import RiemannZeta.GuthMaynard.Separated

open Complex Finset Filter MeasureTheory Real Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Cubic Poisson trace and the `S₁/S₂/S₃` split

This module formalizes Guth--Maynard Lemma 4.5 and the decomposition (5.5).
Every dual sum is an absolutely summable integer series.  The three pieces are
obtained by writing each Gram kernel as its zero Fourier mode plus its complete
nonzero-frequency tail and expanding the resulting cubic product.
-/

/-- The scaled `m`-th Fourier mode `N h-hat_t(Nm)` in the source Poisson
formula. -/
noncomputable def gmScaledTraceMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) (m : ℤ) : ℂ :=
  (N : ℂ) * gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))

/-- The complete nonzero-frequency tail at ordinate difference `t`. -/
noncomputable def gmTraceNonzeroTailAt (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else gmScaledTraceMode cutoff N t m

/-- The scaled zero Fourier mode. -/
noncomputable def gmTraceZeroMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  gmScaledTraceMode cutoff N t 0

theorem gmScaledTraceMode_summable (cutoff : GMSmoothCutoff) (N : ℕ)
    (hN : 0 < N) (t : ℝ) :
    Summable (gmScaledTraceMode cutoff N t) := by
  simpa [gmScaledTraceMode] using
    gmScaledTraceFourier_summable cutoff t (N : ℝ) (by exact_mod_cast hN)

theorem gmScaledTraceMode_tsum_decompose (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ∑' m : ℤ, gmScaledTraceMode cutoff N t m =
      gmTraceZeroMode cutoff N t + gmTraceNonzeroTailAt cutoff N t := by
  rw [(gmScaledTraceMode_summable cutoff N hN t).tsum_eq_add_tsum_ite 0]
  simp [gmTraceZeroMode, gmTraceNonzeroTailAt]

/-- Uniform arbitrary-order control of the complete nonzero-frequency tail.
This is the summed version of Lemma 4.3(1), with the full ordinate dependence
left explicit. -/
theorem gmTraceNonzeroTailAt_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N → ∀ t : ℝ,
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
        K * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1) := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff q
  have hSeries : Summable (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ q‖) := by
    have hNorm : (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ q‖) =
        fun m : ℤ ↦ |1 / (m : ℝ) ^ q| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by omega)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ q‖
  have hB : 0 ≤ B := tsum_nonneg fun m ↦ norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N hN t
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let scale : ℝ := C * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1)
  have hPointwise : ∀ m : ℤ,
      ‖if m = 0 then 0 else gmScaledTraceMode cutoff N t m‖ ≤
        scale * ‖1 / (m : ℂ) ^ q‖ := by
    intro m
    by_cases hm : m = 0
    · have hq0 : q ≠ 0 := by omega
      simp [hm, hq0]
    · have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hmAbs : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
      have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
          (N : ℝ) * |(m : ℝ)| := by
        rw [abs_mul, abs_of_pos hNr]
      have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by positivity
      have hFourier :
          ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
            C * (1 + |t|) ^ q /
              |(N : ℝ) * (m : ℝ)| ^ q := by
        rw [le_div_iff₀ (pow_pos hFreqPos q)]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hDecay t ((N : ℝ) * (m : ℝ))
      simp only [if_false, hm, gmScaledTraceMode, norm_mul,
        Complex.norm_natCast, norm_div, norm_one, norm_pow,
        Complex.norm_intCast]
      calc
        (N : ℝ) * ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
            (N : ℝ) *
              (C * (1 + |t|) ^ q /
                |(N : ℝ) * (m : ℝ)| ^ q) := by gcongr
        _ = scale * (1 / |(m : ℝ)| ^ q) := by
          rw [hFreqAbs, mul_pow]
          have hqEq : q = (q - 1) + 1 := by omega
          have hNpow : (N : ℝ) ^ q =
              (N : ℝ) ^ (q - 1) * (N : ℝ) := by
            conv_lhs => rw [hqEq, pow_succ]
          dsimp only [scale]
          rw [hNpow]
          field_simp
  have hScaled : Summable (fun m : ℤ ↦ scale * ‖1 / (m : ℂ) ^ q‖) :=
    hSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaled.hasSum hPointwise
  rw [tsum_mul_left] at hBound
  change ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ scale * B at hBound
  calc
    ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1) := by
      dsimp only [scale]
      have hPow : 0 < (N : ℝ) ^ (q - 1) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hPow).2
      have htPow : 0 ≤ (1 + |t|) ^ q := by positivity
      nlinarith

/-- A uniform bound for every scaled zero mode. -/
theorem gmTraceZeroMode_bound (cutoff : GMSmoothCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (t : ℝ),
      ‖gmTraceZeroMode cutoff N t‖ ≤ (N : ℝ) * B := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff 0
  refine ⟨C + 1, by positivity, ?_⟩
  intro N t
  have h := hDecay t 0
  simp only [abs_zero, pow_zero, one_mul] at h
  simp only [gmTraceZeroMode, gmScaledTraceMode, Int.cast_zero, mul_zero,
    norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (h.trans (by nlinarith [hC]))
    (Nat.cast_nonneg N)

/-- A separated nonzero ordinate difference makes its scaled zero mode
arbitrarily small. -/
theorem gmTraceZeroMode_separated_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) {δ t : ℝ}, 0 < δ → δ ≤ |t| →
      ‖gmTraceZeroMode cutoff N t‖ ≤
        (N : ℝ) * C / δ ^ q := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_zero_uniform_decay_source cutoff q
  refine ⟨C, hC, ?_⟩
  intro N δ t hδ ht
  have htPos : 0 < |t| := hδ.trans_le ht
  have hFourier : ‖gmTraceFourier cutoff t 0‖ ≤ C / |t| ^ q := by
    rw [le_div_iff₀ (pow_pos htPos q)]
    simpa [mul_comm] using hDecay t
  simp only [gmTraceZeroMode, gmScaledTraceMode, Int.cast_zero, mul_zero,
    norm_mul, Complex.norm_natCast]
  calc
    (N : ℝ) * ‖gmTraceFourier cutoff t 0‖ ≤
        (N : ℝ) * (C / |t| ^ q) := by gcongr
    _ = (N : ℝ) * C / |t| ^ q := by ring
    _ ≤ (N : ℝ) * C / δ ^ q := by
      have hpow : δ ^ q ≤ |t| ^ q := pow_le_pow_left₀ hδ.le ht q
      exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg N) hC.le)
        (pow_pos hδ q) hpow

private theorem gmTraceKernel_eq_scaled_phase
    (cutoff : GMSmoothCutoff) (N n : ℕ) (hN : 0 < N) (hn : 0 < n)
    (t : ℝ) :
    (cutoff ((n : ℝ) / N) ^ 2 : ℂ) *
        (n : ℂ) ^ ((t : ℂ) * I) =
      (N : ℂ) ^ ((t : ℂ) * I) *
        gmTraceKernel cutoff t ((n : ℝ) / N) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : 0 < (n : ℝ) / N := div_pos hnr hNr
  have hcast :
      ((n : ℂ) : ℂ) = (N : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) := by
    have hreal : (n : ℝ) = (N : ℝ) * ((n : ℝ) / N) :=
      (mul_div_cancel₀ (n : ℝ) hNr.ne').symm
    calc
      (n : ℂ) = (((n : ℝ) : ℂ)) := by norm_num
      _ = ((((N : ℝ) * ((n : ℝ) / N) : ℝ)) : ℂ) := congrArg Complex.ofReal hreal
      _ = (N : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  change (cutoff ((n : ℝ) / N) ^ 2 : ℂ) *
      ((((N : ℝ) : ℂ) * (((n : ℝ) / N : ℝ) : ℂ)) ^ ((t : ℂ) * I)) = _
  rw [Complex.mul_cpow_ofReal_nonneg hNr.le hratio.le]
  unfold gmTraceKernel
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have harg :
      ((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * ((t : ℂ) * I) =
        (((t * Real.log ((n : ℝ) / N) : ℝ)) : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  ac_rfl

/-- Compact support identifies the integer kernel sum with the actual matrix
columns for every ordinate difference. -/
theorem gmTraceKernel_tsum_eq_column_sum (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ∑' n : ℤ, gmTraceKernel cutoff t ((n : ℝ) / N) =
      ∑ n : GMColumn N, gmTraceKernel cutoff t ((n : ℝ) / N) := by
  rw [gmTraceKernel_tsum_eq_intBlock cutoff t (N : ℝ) (by exact_mod_cast hN)]
  have hFloorN : Int.floor (N : ℝ) = (N : ℤ) := by simp
  have hFloorTwoN : Int.floor (2 * (N : ℝ)) = ((2 * N : ℕ) : ℤ) := by
    calc
      Int.floor (2 * (N : ℝ)) = Int.floor (((2 * N : ℕ) : ℝ)) := by
        congr 1
        norm_num
      _ = ((2 * N : ℕ) : ℤ) := Int.floor_natCast (R := ℝ) (2 * N)
  rw [hFloorN, hFloorTwoN]
  have hInterval :
      Finset.Ioc (N : ℤ) ((2 * N : ℕ) : ℤ) =
        (Finset.Ioc N (2 * N)).map Nat.castEmbedding := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map]
    constructor
    · intro hz
      have hzNonneg : 0 ≤ z := by omega
      refine ⟨z.toNat, ?_, ?_⟩
      · constructor <;> omega
      · exact Int.toNat_of_nonneg hzNonneg
    · rintro ⟨n, hn, rfl⟩
      change (N : ℤ) < (n : ℤ) ∧ (n : ℤ) ≤ (2 * N : ℤ)
      exact_mod_cast hn
  rw [hInterval, Finset.sum_map]
  have hAttach :
      (∑ n : GMColumn N, gmTraceKernel cutoff t ((n : ℝ) / N)) =
        ∑ n ∈ dyadicInterval N, gmTraceKernel cutoff t ((n : ℝ) / N) := by
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.univ_eq_attach (dyadicInterval N)]
  rw [hAttach]
  apply Finset.sum_congr rfl
  intro n hn
  rfl

/-- A Gram entry is a Mellin phase times the full scaled Fourier series. -/
theorem gmMatrix_gram_apply_eq_phase_mul_fourier_tsum
    (cutoff : GMSmoothCutoff) (N : ℕ) (hN : 0 < N)
    (W : Finset ℝ) (t u : GMRow W) :
    (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) t u =
      (N : ℂ) ^ (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I) *
        ∑' m : ℤ, gmScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m := by
  rw [gmMatrix_gram_apply_eq_phase_sum]
  have hColumn :
      (∑ n : GMColumn N,
          (cutoff ((n : ℝ) / N) ^ 2 : ℂ) *
            (n : ℂ) ^ (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I)) =
        (N : ℂ) ^ (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I) *
          ∑ n : GMColumn N,
            gmTraceKernel cutoff ((t : ℝ) - (u : ℝ)) ((n : ℝ) / N) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnPos : 0 < (n : ℕ) := by
      have hnMem : (n : ℕ) ∈ Finset.Ioc N (2 * N) := n.property
      rw [Finset.mem_Ioc] at hnMem
      omega
    exact gmTraceKernel_eq_scaled_phase cutoff N n hN
      hnPos
      ((t : ℝ) - (u : ℝ))
  rw [show (((t : ℂ) - (u : ℂ)) * I) =
      (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I) by
        rw [Complex.ofReal_sub]]
  rw [hColumn, ← gmTraceKernel_tsum_eq_column_sum cutoff N hN]
  rw [gmTraceKernel_poisson cutoff ((t : ℝ) - (u : ℝ)) (N : ℝ)
    (by exact_mod_cast hN)]
  congr 1

private theorem gmCubicPhase_cancel (N : ℕ) (hN : 0 < N)
    (t u v : ℝ) :
    (N : ℂ) ^ (((t - u : ℝ) : ℂ) * I) *
        (N : ℂ) ^ (((u - v : ℝ) : ℂ) * I) *
          (N : ℂ) ^ (((v - t : ℝ) : ℂ) * I) = 1 := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Complex.cpow_add _ _ hNne, ← Complex.cpow_add _ _ hNne]
  convert Complex.cpow_zero (N : ℂ) using 2
  push_cast
  ring

/-- The exact contribution of the all-zero frequency. -/
noncomputable def gmCubicZeroMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))

/-- The diagonal main term in Guth--Maynard Lemma 4.5. -/
noncomputable def gmCubicDiagonalMain (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  (N : ℂ) ^ 3 * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ) ^ 3

/-- The off-diagonal part of the all-zero Fourier mode. -/
noncomputable def gmCubicZeroRemainder (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    if t = u ∧ u = v then 0 else
      gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
        gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
          gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))

@[simp]
theorem gmTraceZeroMode_zero (cutoff : GMSmoothCutoff) (N : ℕ) :
    gmTraceZeroMode cutoff N 0 =
      (N : ℂ) * (gmCutoffL2Sq cutoff : ℂ) := by
  simp [gmTraceZeroMode, gmScaledTraceMode,
    gmTraceFourier_zero_zero_eq_cutoffL2Sq]

/-- Exact separation of the zero-frequency contribution into its diagonal
main term and off-diagonal remainder. -/
theorem gmCubicZeroMode_eq_main_add_remainder (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) :
    gmCubicZeroMode cutoff N W =
      gmCubicDiagonalMain cutoff N W + gmCubicZeroRemainder cutoff N W := by
  unfold gmCubicZeroMode gmCubicDiagonalMain gmCubicZeroRemainder
  have hMain :
      (N : ℂ) ^ 3 * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ) ^ 3 =
        ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
          if t = u ∧ u = v then
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))
          else 0 := by
    symm
    calc
      (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
          if t = u ∧ u = v then
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))
          else 0) =
          ∑ _t : GMRow W,
            ((N : ℂ) * (gmCutoffL2Sq cutoff : ℂ)) ^ 3 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_eq_single t]
        · rw [Finset.sum_eq_single t]
          · simp
            ring
          · intro v hv hvt
            have htv : t ≠ v := Ne.symm hvt
            simp [htv]
          · simp
        · intro u hu hut
          have htu : t ≠ u := Ne.symm hut
          simp [htu]
        · simp
      _ = (N : ℂ) ^ 3 * (W.card : ℂ) *
          (gmCutoffL2Sq cutoff : ℂ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nsmul_eq_mul]
        ring
  rw [hMain]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases htu : t = u
  · subst u
    by_cases htv : t = v
    · subst v
      simp
    · simp [htv]
  · simp [htu]

/-- The piece with exactly one nonzero Fourier frequency. -/
noncomputable def gmCubicS1Summand (cutoff : GMSmoothCutoff) (N : ℕ)
    {W : Finset ℝ} (t u v : GMRow W) : ℂ :=
  (gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))

/-- The piece with exactly one nonzero Fourier frequency. -/
noncomputable def gmCubicS1 (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmCubicS1Summand cutoff N t u v

/-- The piece with exactly two nonzero Fourier frequencies. -/
noncomputable def gmCubicS2 (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    (gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
          gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
      gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
        gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
          gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)) +
      gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
          gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))

/-- The piece with all three Fourier frequencies nonzero. -/
noncomputable def gmCubicS3 (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))

/-- Exact Guth--Maynard cubic Poisson expansion before separating the four
frequency classes. -/
theorem gmMatrix_cubic_trace_poisson_expand (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (W : Finset ℝ) :
    Matrix.trace
        ((gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) ^ 3) =
      ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        (gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))) *
          (gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))) *
          (gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))) := by
  rw [matrix_trace_cube_expand]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp_rw [gmMatrix_gram_apply_eq_phase_mul_fourier_tsum cutoff N hN W,
    gmScaledTraceMode_tsum_decompose cutoff N hN]
  calc
    (N : ℂ) ^ (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I) *
          (gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))) *
        ((N : ℂ) ^ (((((u : ℝ) - (v : ℝ)) : ℝ) : ℂ) * I) *
          (gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)))) *
        ((N : ℂ) ^ (((((v : ℝ) - (t : ℝ)) : ℝ) : ℂ) * I) *
          (gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))) =
      ((N : ℂ) ^ (((((t : ℝ) - (u : ℝ)) : ℝ) : ℂ) * I) *
        (N : ℂ) ^ (((((u : ℝ) - (v : ℝ)) : ℝ) : ℂ) * I) *
        (N : ℂ) ^ (((((v : ℝ) - (t : ℝ)) : ℝ) : ℂ) * I)) *
        ((gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))) *
          (gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))) *
          (gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))) := by ring
    _ = _ := by rw [gmCubicPhase_cancel N hN t u v]; ring

/-- Equation (5.5): the exact cubic trace is the zero mode plus the pieces
with exactly one, exactly two, and exactly three nonzero frequencies. -/
theorem gmMatrix_cubic_trace_split (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (W : Finset ℝ) :
    Matrix.trace
        ((gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) ^ 3) =
      gmCubicZeroMode cutoff N W + gmCubicS1 cutoff N W +
        gmCubicS2 cutoff N W + gmCubicS3 cutoff N W := by
  rw [gmMatrix_cubic_trace_poisson_expand cutoff N hN W]
  unfold gmCubicZeroMode gmCubicS1 gmCubicS1Summand gmCubicS2 gmCubicS3
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

private theorem gmRow_difference_abs_le {T : ℝ} {W : Finset ℝ}
    (hW : InBaseInterval T W) (t u : GMRow W) :
    |(t : ℝ) - (u : ℝ)| ≤ T := by
  have ht := hW t t.property
  have hu := hW u u.property
  rw [Set.mem_Icc] at ht hu
  rw [abs_le]
  constructor <;> linarith

private theorem gmRow_difference_separated {δ : ℝ} {W : Finset ℝ}
    (hSep : IsSeparated δ W) (t u : GMRow W) (htu : t ≠ u) :
    δ ≤ |(t : ℝ) - (u : ℝ)| := by
  have hval : (t : ℝ) ≠ (u : ℝ) := fun h => htu (Subtype.ext h)
  simpa [Real.dist_eq] using hSep t t.property u u.property hval

/-- A one-separated set in the source interval `[0,T]` has at most `2T`
points.  This packages the floor-bin argument used implicitly in Proposition
5.1. -/
theorem gmSeparated_card_le_two_height {T : ℝ} {W : Finset ℝ}
    (hT : 1 ≤ T) (hSep : IsSeparated 1 W) (hW : InBaseInterval T W) :
    (W.card : ℝ) ≤ 2 * T := by
  have hInject : ∀ x ∈ W, ∀ y ∈ W, ⌊x⌋ = ⌊y⌋ → x = y :=
    floor_injective_on_of_separated W hSep
  have hCardImage : (floorImage W).card = W.card := by
    unfold floorImage
    exact Finset.card_image_iff.mpr hInject
  have hSubset : floorImage W ⊆ Finset.Icc 0 ⌊T⌋ := by
    intro z hz
    rw [floorImage, Finset.mem_image] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hxIcc := hW x hx
    exact Finset.mem_Icc.mpr ⟨Int.floor_nonneg.mpr hxIcc.1,
      Int.floor_mono hxIcc.2⟩
  have hCardNat : W.card ≤ (⌊T⌋ + 1).toNat := by
    calc
      W.card = (floorImage W).card := hCardImage.symm
      _ ≤ (Finset.Icc 0 ⌊T⌋).card := Finset.card_le_card hSubset
      _ = (⌊T⌋ + 1).toNat := by rw [Int.card_Icc]; simp
  have hFloor : ((⌊T⌋ + 1).toNat : ℝ) ≤ T + 1 := by
    have hNonneg : 0 ≤ ⌊T⌋ + 1 := by
      have : (0 : ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.mpr (by linarith)
      omega
    have hToNat : (((⌊T⌋ + 1).toNat : ℕ) : ℤ) = ⌊T⌋ + 1 :=
      Int.toNat_of_nonneg hNonneg
    have hCast : ((⌊T⌋ + 1).toNat : ℝ) = ((⌊T⌋ + 1 : ℤ) : ℝ) := by
      exact_mod_cast hToNat
    rw [hCast]
    exact_mod_cast (show ((⌊T⌋ : ℤ) : ℝ) + 1 ≤ T + 1 by
      linarith [Int.floor_le T])
  calc
    (W.card : ℝ) ≤ ((⌊T⌋ + 1).toNat : ℝ) := by exact_mod_cast hCardNat
    _ ≤ T + 1 := hFloor
    _ ≤ 2 * T := by linarith

/-- Fully explicit finite bound behind Guth--Maynard Proposition 5.1.  The
first term is the off-diagonal contribution, killed by separation; the second
is the diagonal nonzero-frequency tail. -/
theorem gmCubicS1_quantitative (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T δ : ℝ},
      0 < N → 0 < δ → IsSeparated δ W → InBaseInterval T W →
      ‖gmCubicS1 cutoff N W‖ ≤
        K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
  obtain ⟨B, hB, hZero⟩ := gmTraceZeroMode_bound cutoff
  obtain ⟨C, hC, hSmall⟩ := gmTraceZeroMode_separated_bound cutoff q
  obtain ⟨L, hL, hTail⟩ := gmTraceNonzeroTailAt_bound cutoff 2 (by norm_num)
  obtain ⟨D, hD, hTailZero⟩ :=
    gmTraceNonzeroTailAt_bound cutoff 30 (by norm_num)
  let K : ℝ := 3 * (L * B * C + B ^ 2 * D) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N W T δ hN hδ hSep hW
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let offMajor : ℝ :=
    L * (1 + |T|) ^ 2 / (N : ℝ) *
      ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q)
  let diagMajor : ℝ :=
    3 * ((N : ℝ) * B) ^ 2 *
      (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29)
  have hOffNonneg : 0 ≤ offMajor := by dsimp only [offMajor]; positivity
  have hDiagNonneg : 0 ≤ diagMajor := by dsimp only [diagMajor]; positivity
  have hTailAny : ∀ t u : GMRow W,
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
        L * (1 + |T|) ^ 2 / (N : ℝ) := by
    intro t u
    have hdiff := gmRow_difference_abs_le hW t u
    have hbase : 1 + |(t : ℝ) - (u : ℝ)| ≤ 1 + |T| := by
      have hT0 : 0 ≤ T := by
        have ht := hW t t.property
        rw [Set.mem_Icc] at ht
        linarith
      rw [abs_of_nonneg hT0]
      linarith
    calc
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
          L * (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 /
            (N : ℝ) ^ (2 - 1) := hTail N hN ((t : ℝ) - (u : ℝ))
      _ ≤ L * (1 + |T|) ^ 2 / (N : ℝ) := by
        simp only [Nat.reduceSubDiff, pow_one]
        gcongr
  have hTailDiag : ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
      D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29 := by
    simpa using hTailZero N hN 0
  have hSummand : ∀ t u v : GMRow W,
      ‖gmCubicS1Summand cutoff N t u v‖ ≤ offMajor * 3 + diagMajor := by
    intro t u v
    by_cases hAll : t = u ∧ u = v
    · rcases hAll with ⟨rfl, rfl⟩
      simp only [sub_self, gmCubicS1Summand]
      have hDiagOne :
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
        calc
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
              ((N : ℝ) * B) * ((N : ℝ) * B) := by
                gcongr
                · exact hZero N 0
                · exact hZero N 0
              
          _ = _ := by ring
      calc
        ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceNonzeroTailAt cutoff N 0‖ ≤
            3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
          calc
            ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ ≤
              ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ := by
                    calc
                      ‖(_ + _) + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
                      _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
                        gcongr
                        exact norm_add_le _ _
            _ ≤ 3 * ((N : ℝ) * B) ^ 2 *
                (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                  simp only [norm_mul]
                  have hDiagTwo :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
                            ‖gmTraceZeroMode cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
                            ((N : ℝ) * B) := by
                              gcongr
                              · exact hZero N 0
                              · exact hZero N 0
                      _ = _ := by ring
                  have hDiagThree :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceZeroMode cutoff N 0‖ *
                            ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) * ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                            gcongr
                            · exact hZero N 0
                            · exact hZero N 0
                      _ = _ := by ring
                  nlinarith
      _ = diagMajor := by rfl
      _ ≤ offMajor * 3 + diagMajor := by nlinarith
    · have hTerm1 :
          ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : u ≠ v ∨ v ≠ t := by
          by_cases huv : u = v
          · right
            intro hvt
            apply hAll
            subst v
            subst u
            exact ⟨rfl, rfl⟩
          · exact Or.inl huv
        rcases hCases with huv | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by rfl
      have hTerm2 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ v ≠ t := by
          by_cases htu : t = u
          · right
            intro hvt
            apply hAll
            subst u
            subst v
            exact ⟨rfl, rfl⟩
          · exact Or.inl htu
        rcases hCases with htu | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hTailAny u v
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                  ((N : ℝ) * C / δ ^ q) := by
                    gcongr
                    · exact hZero N ((t : ℝ) - (u : ℝ))
                    · exact hTailAny u v
                    · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by dsimp only [offMajor]; ring
      have hTerm3 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ u ≠ v := by
          by_cases htu : t = u
          · right
            intro huv
            exact hAll ⟨htu, huv⟩
          · exact Or.inl htu
        rcases hCases with htu | huv
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hZero N ((t : ℝ) - (u : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
      unfold gmCubicS1Summand
      calc
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ := by
                  exact (norm_add_le _ _).trans
                    (by gcongr; exact norm_add_le _ _)
        _ ≤ offMajor * 3 := by nlinarith
        _ ≤ offMajor * 3 + diagMajor := le_add_of_nonneg_right hDiagNonneg
  unfold gmCubicS1
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS1Summand cutoff N t u v‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W,
          gmCubicS1Summand cutoff N t u v‖ := norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖∑ v : GMRow W, gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ‖gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W,
        (offMajor * 3 + diagMajor) := by
          gcongr with t ht u hu v hv
          exact hSummand t u v
    _ = (W.card : ℝ) ^ 3 * (offMajor * 3 + diagMajor) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
      dsimp only [offMajor, diagMajor, K]
      have hFirst :
          L * (1 + |T|) ^ 2 / (N : ℝ) * ((N : ℝ) * B) *
              ((N : ℝ) * C / δ ^ q) =
            L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) := by
        field_simp [hNr.ne']
      have hSecond :
          3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) =
            3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
        norm_num
        ring
      rw [hFirst, hSecond]
      have hCardNonneg : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
      have hx : 0 ≤ (N : ℝ) * (1 + |T|) ^ 2 / δ ^ q := by positivity
      have hy : 0 ≤ (N : ℝ) ^ 2 / (N : ℝ) ^ 29 := by positivity
      calc
        (W.card : ℝ) ^ 3 *
              (L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) * 3 +
                3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29)) ≤
            (W.card : ℝ) ^ 3 *
              (K * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29)) := by
          apply mul_le_mul_of_nonneg_left _ hCardNonneg
          nlinarith [mul_nonneg (mul_nonneg hL.le hB.le) hC.le,
            mul_nonneg (sq_nonneg B) hD.le]
        _ = K * (W.card : ℝ) ^ 3 *
              ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by ring

/-- Finite-scale form of Guth--Maynard Proposition 5.1.  The hypothesis
`T^16 ≤ δ^q` records the exact amount of separation decay consumed by the
proof; arbitrary `T^ε` separation supplies it by choosing `q > 16/ε`.
The scale window contains the source specialization `T=N^(6/5)`. -/
theorem gmCubicS1_power_decay (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 0 < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T δ : ℝ},
      0 < N → 1 ≤ (N : ℝ) → 1 ≤ T → (N : ℝ) ≤ T →
      T ≤ (N : ℝ) ^ 2 → 0 < δ → T ^ 16 ≤ δ ^ q →
      IsSeparated δ W → InBaseInterval T W →
      ‖gmCubicS1 cutoff N W‖ ≤ K / T ^ 10 := by
  obtain ⟨K₀, hK₀, hQuant⟩ := gmCubicS1_quantitative cutoff q
  refine ⟨40 * K₀, by positivity, ?_⟩
  intro N W T δ hN hNOne hT hNT hTN hδ hδPow hSep hW
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hOneSep : IsSeparated 1 W := by
    intro x hx y hy hxy
    have hδOne : 1 ≤ δ := by
      by_contra hnot
      have hδlt : δ < 1 := lt_of_not_ge hnot
      have hδq : δ ^ q < 1 := pow_lt_one₀ hδ.le hδlt hq.ne'
      have hTpow : 1 ≤ T ^ 16 := one_le_pow₀ hT
      linarith
    exact hδOne.trans (hSep x hx y hy hxy)
  have hCard : (W.card : ℝ) ≤ 2 * T :=
    gmSeparated_card_le_two_height hT hOneSep hW
  have hQuantitative := hQuant N W hN hδ hSep hW
  have hCardCube : (W.card : ℝ) ^ 3 ≤ 8 * T ^ 3 := by
    calc
      (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hCard 3
      _ = 8 * T ^ 3 := by ring
  have hAbsT : |T| = T := abs_of_pos hTpos
  have hNum : (N : ℝ) * (1 + |T|) ^ 2 ≤ 4 * T ^ 3 := by
    rw [hAbsT]
    have hOneAdd : 1 + T ≤ 2 * T := by linarith
    calc
      (N : ℝ) * (1 + T) ^ 2 ≤ T * (1 + T) ^ 2 :=
        mul_le_mul_of_nonneg_right hNT (sq_nonneg (1 + T))
      _ ≤ T * (2 * T) ^ 2 := by gcongr
      _ = 4 * T ^ 3 := by ring
  have hOff : (N : ℝ) * (1 + |T|) ^ 2 / δ ^ q ≤ 4 / T ^ 13 := by
    calc
      _ ≤ (4 * T ^ 3) / T ^ 16 :=
        div_le_div₀ (by positivity) hNum (by positivity) hδPow
      _ = 4 / T ^ 13 := by field_simp
  have hT13N26 : T ^ 13 ≤ (N : ℝ) ^ 26 := by
    calc
      T ^ 13 ≤ ((N : ℝ) ^ 2) ^ 13 :=
        pow_le_pow_left₀ (by positivity) hTN 13
      _ = (N : ℝ) ^ 26 := by ring
  have hT13N27 : T ^ 13 ≤ (N : ℝ) ^ 27 := by
    calc
      T ^ 13 ≤ (N : ℝ) ^ 26 := hT13N26
      _ ≤ (N : ℝ) ^ 27 := by
        rw [show (N : ℝ) ^ 27 = (N : ℝ) ^ 26 * (N : ℝ) by ring]
        exact le_mul_of_one_le_right (by positivity) hNOne
  have hDiag : (N : ℝ) ^ 2 / (N : ℝ) ^ 29 ≤ 1 / T ^ 13 := by
    have hEq : (N : ℝ) ^ 2 / (N : ℝ) ^ 29 = 1 / (N : ℝ) ^ 27 := by
      field_simp
    rw [hEq]
    exact one_div_le_one_div_of_le (by positivity) hT13N27
  calc
    ‖gmCubicS1 cutoff N W‖ ≤ K₀ * (W.card : ℝ) ^ 3 *
        ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
          (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := hQuantitative
    _ ≤ K₀ * (8 * T ^ 3) * (4 / T ^ 13 + 1 / T ^ 13) := by gcongr
    _ = 40 * K₀ / T ^ 10 := by field_simp; ring

/-- Guth--Maynard Proposition 5.1 in its source epsilon-separated form:
uniformly throughout the scale window containing `T=N^(6/5)`, the one-tail
piece of the cubic trace is `O_ε(T⁻¹⁰)`. -/
theorem gmCubicS1_estimate (cutoff : GMSmoothCutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T : ℝ},
      0 < N → 1 ≤ (N : ℝ) → 1 ≤ T → (N : ℝ) ≤ T →
      T ≤ (N : ℝ) ^ 2 → IsSeparated (T ^ ε) W →
      InBaseInterval T W → ‖gmCubicS1 cutoff N W‖ ≤ K / T ^ 10 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (16 / ε)
  have hqPos : 0 < q := by
    have : 0 < (q : ℝ) := (div_pos (by norm_num) hε).trans hq
    exact_mod_cast this
  obtain ⟨K, hK, hDecay⟩ := gmCubicS1_power_decay cutoff q hqPos
  refine ⟨K, hK, ?_⟩
  intro N W T hN hNOne hT hNT hTN hSep hW
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hScalePos : 0 < T ^ ε := Real.rpow_pos_of_pos hTpos ε
  have hExponent : 16 < ε * (q : ℝ) := by
    rw [div_lt_iff₀ hε] at hq
    nlinarith
  apply hDecay N W hN hNOne hT hNT hTN hScalePos
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT hExponent.le
  · exact hSep
  · exact hW

/-- Arbitrary-order off-diagonal bound for the all-zero Fourier mode. -/
theorem gmCubicZeroRemainder_quantitative (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {δ : ℝ},
      0 < δ → IsSeparated δ W →
      ‖gmCubicZeroRemainder cutoff N W‖ ≤
        K * (W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 / δ ^ q) := by
  obtain ⟨B, hB, hZero⟩ := gmTraceZeroMode_bound cutoff
  obtain ⟨C, hC, hSmall⟩ := gmTraceZeroMode_separated_bound cutoff q
  let K : ℝ := C * B ^ 2 + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N W δ hδ hSep
  let major : ℝ := ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) ^ 2
  have hMajorNonneg : 0 ≤ major := by
    dsimp only [major]
    positivity
  have hTerm : ∀ t u v : GMRow W,
      ‖if t = u ∧ u = v then 0 else
          gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
            gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
              gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ major := by
    intro t u v
    by_cases hAll : t = u ∧ u = v
    · simp [hAll, hMajorNonneg]
    · simp only [if_neg hAll, norm_mul]
      by_cases htu : t = u
      · have huv : u ≠ v := by
          intro huv
          exact hAll ⟨htu, huv⟩
        calc
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) *
                ((N : ℝ) * B) := by
            gcongr
            · exact hZero N ((t : ℝ) - (u : ℝ))
            · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
            · exact hZero N ((v : ℝ) - (t : ℝ))
          _ = major := by dsimp only [major]; ring
      · calc
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) *
                ((N : ℝ) * B) := by
            gcongr
            · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
            · exact hZero N ((u : ℝ) - (v : ℝ))
            · exact hZero N ((v : ℝ) - (t : ℝ))
          _ = major := by dsimp only [major]; ring
  unfold gmCubicZeroRemainder
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        if t = u ∧ u = v then 0 else
          gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
            gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
              gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W,
          if t = u ∧ u = v then 0 else
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖∑ v : GMRow W, if t = u ∧ u = v then 0 else
          gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
            gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
              gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ‖if t = u ∧ u = v then 0 else
          gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
            gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
              gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W, major := by
      gcongr with t ht u hu v hv
      exact hTerm t u v
    _ = (W.card : ℝ) ^ 3 * major := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
      ring
    _ ≤ K * (W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 / δ ^ q) := by
      calc
        (W.card : ℝ) ^ 3 * major =
            (C * B ^ 2) *
              ((W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 / δ ^ q)) := by
          dsimp only [major]
          field_simp
        _ ≤ K * ((W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 / δ ^ q)) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp only [K]
            linarith
          · positivity
        _ = K * (W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 / δ ^ q) := by ring

/-- The all-zero-frequency contribution in Lemma 4.5 equals its diagonal
main term up to `O_ε(T⁻¹⁰⁰)` in the source scale window. -/
theorem gmCubicZeroMode_main_term (cutoff : GMSmoothCutoff)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T : ℝ},
      0 < N → 1 ≤ T → (N : ℝ) ≤ T → IsSeparated (T ^ ε) W →
      InBaseInterval T W →
      ‖gmCubicZeroMode cutoff N W - gmCubicDiagonalMain cutoff N W‖ ≤
        K / T ^ 100 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (106 / ε)
  obtain ⟨K₀, hK₀, hRemainder⟩ := gmCubicZeroRemainder_quantitative cutoff q
  refine ⟨8 * K₀, by positivity, ?_⟩
  intro N W T hN hT hNT hSep hW
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hScalePos : 0 < T ^ ε := Real.rpow_pos_of_pos hTpos ε
  have hScaleOne : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hOneSep : IsSeparated 1 W := by
    intro x hx y hy hxy
    exact hScaleOne.trans (hSep x hx y hy hxy)
  have hCard := gmSeparated_card_le_two_height hT hOneSep hW
  have hCardCube : (W.card : ℝ) ^ 3 ≤ 8 * T ^ 3 := by
    calc
      (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hCard 3
      _ = 8 * T ^ 3 := by ring
  have hNCube : (N : ℝ) ^ 3 ≤ T ^ 3 :=
    pow_le_pow_left₀ (by positivity) hNT 3
  have hExponent : 106 < ε * (q : ℝ) := by
    rw [div_lt_iff₀ hε] at hq
    nlinarith
  have hScalePower : T ^ 106 ≤ (T ^ ε) ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT hExponent.le
  rw [gmCubicZeroMode_eq_main_add_remainder, add_sub_cancel_left]
  calc
    ‖gmCubicZeroRemainder cutoff N W‖ ≤
        K₀ * (W.card : ℝ) ^ 3 *
          ((N : ℝ) ^ 3 / (T ^ ε) ^ q) :=
      hRemainder N W hScalePos hSep
    _ ≤ K₀ * (8 * T ^ 3) * (T ^ 3 / T ^ 106) := by
      gcongr
    _ = 8 * K₀ / T ^ 100 := by field_simp

end RiemannZeta.GuthMaynard
