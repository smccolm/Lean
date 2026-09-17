import Tao2026.SmoothNumberSaddlePerronCutoff

/-!
# Large-height limits of the smooth sharp-Perron kernels

The finite-height comparison has a half-weight at its discontinuity in the
large-height limit.  This module proves the three scalar cases, constructs a
summable height-independent envelope, and applies Tannery's theorem to the
complete smooth-number series.  It is the exact endpoint convention underlying
the `O(1)` in Granville's Perron formula.
-/

open Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The sharp-Perron kernel tends to one strictly below the endpoint. -/
theorem tendsto_sharpPerronKernel_atTop_of_natCast_lt
    {sigma x : ℝ} {n : ℕ} (hsigma : 0 < sigma) (hx : 0 < x)
    (hn : 1 ≤ n) (hnx : (n : ℝ) < x) :
    Tendsto (fun T : ℝ => GafniTao.sharpPerronKernel sigma T x n)
      atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let C : ℝ := (x / (n : ℝ)) ^ sigma /
    (Real.pi * Real.log (x / (n : ℝ)))
  have hupper : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have h := GafniTao.norm_sharpPerronKernel_sub_one_le_of_natCast_lt
    hsigma hT hx hn hnx
  convert h using 1
  dsimp only [C]
  ring_nf

/-- The sharp-Perron kernel tends to zero strictly above the endpoint. -/
theorem tendsto_sharpPerronKernel_atTop_of_natCast_gt
    {sigma x : ℝ} {n : ℕ} (hsigma : 0 < sigma) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x < (n : ℝ)) :
    Tendsto (fun T : ℝ => GafniTao.sharpPerronKernel sigma T x n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := (x / (n : ℝ)) ^ sigma /
    (Real.pi * (-Real.log (x / (n : ℝ))))
  have hupper : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have h := GafniTao.norm_sharpPerronKernel_le_of_natCast_lt
    hsigma hT hx hn hxn
  convert h using 1
  dsimp only [C]
  ring_nf

/-- At the discontinuity the symmetric sharp-Perron kernel tends to the
classical half-weight. -/
theorem tendsto_sharpPerronKernel_atTop_of_eq_natCast
    {sigma x : ℝ} {n : ℕ} (hsigma : 0 < sigma) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x = (n : ℝ)) :
    Tendsto (fun T : ℝ => GafniTao.sharpPerronKernel sigma T x n)
      atTop (𝓝 (1 / 2 : ℂ)) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have harg : Tendsto (fun T : ℝ => T / sigma) atTop atTop :=
    tendsto_id.atTop_div_const hsigma
  have harctan : Tendsto (fun T : ℝ => Real.arctan (T / sigma))
      atTop (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have hreal : Tendsto
      (fun T : ℝ =>
        (Real.arctan (T / sigma) - Real.arctan (-T / sigma)) /
          (2 * Real.pi)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hdiv := harctan.div_const Real.pi
    convert hdiv using 1
    · funext T
      rw [show -T / sigma = -(T / sigma) by ring]
      rw [Real.arctan_neg]
      ring
    · field_simp [Real.pi_ne_zero]
  have hkernel (T : ℝ) :
      GafniTao.sharpPerronKernel sigma T x n =
        (((Real.arctan (T / sigma) - Real.arctan (-T / sigma)) /
          (2 * Real.pi) : ℝ) : ℂ) := by
    rw [GafniTao.sharpPerronKernel_eq_ratioKernel hx hn, hxn,
      div_self hnpos.ne', GafniTao.sharpPerronRatioKernel_one hsigma]
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hc using 1
  · funext T
    exact hkernel T
  · norm_num

/-- The half-weighted source cutoff selected by symmetric Perron inversion. -/
noncomputable def smoothHalfPerronCutoff
    (X y : ℕ) (n : Nat.smoothNumbers (y + 1)) : ℂ :=
  if n.1 < X then 1 else if n.1 = X then (1 / 2 : ℂ) else 0

/-- The possible half-mass at the integral endpoint. -/
noncomputable def smoothPerronEndpointMass
    (X y : ℕ) (n : Nat.smoothNumbers (y + 1)) : ℂ :=
  if n.1 = X then (1 / 2 : ℂ) else 0

/-- The endpoint correction is present precisely when `X` itself is
source-smooth. -/
noncomputable def smoothPerronEndpointCorrection (X y : ℕ) : ℂ :=
  if X ∈ Nat.smoothNumbers (y + 1) then (1 / 2 : ℂ) else 0

/-- The half cutoff differs from the inclusive source cutoff by exactly the
possible endpoint half-mass. -/
theorem smoothHalfPerronCutoff_eq_cutoff_sub_endpointMass
    (X y : ℕ) (n : Nat.smoothNumbers (y + 1)) :
    smoothHalfPerronCutoff X y n =
      smoothSharpPerronCutoff X y n - smoothPerronEndpointMass X y n := by
  unfold smoothHalfPerronCutoff smoothSharpPerronCutoff
    smoothPerronEndpointMass GafniTao.sharpPerronCutoff
  by_cases hnLt : n.1 < X
  · have hnLe : (n.1 : ℝ) ≤ X := by exact_mod_cast hnLt.le
    simp [hnLt, ne_of_lt hnLt, hnLe]
  · by_cases hnEq : n.1 = X
    · subst X
      simp
      ring
    · have hXn : X < n.1 := lt_of_le_of_ne
        (Nat.le_of_not_gt hnLt) (Ne.symm hnEq)
      have hnLe : ¬ (n.1 : ℝ) ≤ X := by
        exact_mod_cast (not_le_of_gt hXn)
      simp [hnLt, hnEq, hnLe]

/-- The endpoint-mass series has at most one nonzero term. -/
theorem summable_smoothPerronEndpointMass (X y : ℕ) :
    Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothPerronEndpointMass X y n) := by
  by_cases hXsmooth : X ∈ Nat.smoothNumbers (y + 1)
  · let xX : Nat.smoothNumbers (y + 1) := ⟨X, hXsmooth⟩
    apply summable_of_ne_finset_zero (s := {xX})
    intro n hn
    have hnNe : n ≠ xX := by simpa using hn
    have hval : n.1 ≠ X := by
      intro heq
      exact hnNe (Subtype.ext heq)
    simp [smoothPerronEndpointMass, hval]
  · have hne (n : Nat.smoothNumbers (y + 1)) : n.1 ≠ X := by
      intro heq
      apply hXsmooth
      simpa [heq] using n.2
    simp [smoothPerronEndpointMass, hne]

/-- The endpoint-mass series is the explicit endpoint correction. -/
theorem tsum_smoothPerronEndpointMass_eq (X y : ℕ) :
    ∑' n : Nat.smoothNumbers (y + 1), smoothPerronEndpointMass X y n =
      smoothPerronEndpointCorrection X y := by
  by_cases hXsmooth : X ∈ Nat.smoothNumbers (y + 1)
  · let xX : Nat.smoothNumbers (y + 1) := ⟨X, hXsmooth⟩
    rw [tsum_eq_single xX]
    · simp [xX, smoothPerronEndpointMass, smoothPerronEndpointCorrection,
        hXsmooth]
    · intro n hn
      have hval : n.1 ≠ X := by
        intro heq
        exact hn (Subtype.ext heq)
      simp [smoothPerronEndpointMass, hval]
  · have hne (n : Nat.smoothNumbers (y + 1)) : n.1 ≠ X := by
      intro heq
      apply hXsmooth
      simpa [heq] using n.2
    simp [smoothPerronEndpointMass, smoothPerronEndpointCorrection,
      hXsmooth, hne]

/-- The half-cutoff series is finite, hence summable. -/
theorem summable_smoothHalfPerronCutoff (X y : ℕ) :
    Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothHalfPerronCutoff X y n) := by
  refine ((summable_smoothSharpPerronCutoff X y).sub
    (summable_smoothPerronEndpointMass X y)).congr (fun n => ?_)
  exact (smoothHalfPerronCutoff_eq_cutoff_sub_endpointMass X y n).symm

/-- Symmetric Perron inversion recovers `psiNat` up to the explicit possible
half-weight at the endpoint. -/
theorem tsum_smoothHalfPerronCutoff_eq_psiNat_sub_endpointCorrection
    (X y : ℕ) :
    ∑' n : Nat.smoothNumbers (y + 1), smoothHalfPerronCutoff X y n =
      (psiNat X y : ℂ) - smoothPerronEndpointCorrection X y := by
  rw [show (∑' n : Nat.smoothNumbers (y + 1),
      smoothHalfPerronCutoff X y n) =
        ∑' n : Nat.smoothNumbers (y + 1),
          (smoothSharpPerronCutoff X y n -
            smoothPerronEndpointMass X y n) by
      apply tsum_congr
      intro n
      exact smoothHalfPerronCutoff_eq_cutoff_sub_endpointMass X y n]
  rw [(summable_smoothSharpPerronCutoff X y).tsum_sub
    (summable_smoothPerronEndpointMass X y),
    tsum_smoothSharpPerronCutoff_eq_psiNat,
    tsum_smoothPerronEndpointMass_eq]

/-- The endpoint correction is uniformly bounded by one half. -/
theorem norm_smoothPerronEndpointCorrection_le_half (X y : ℕ) :
    ‖smoothPerronEndpointCorrection X y‖ ≤ (1 / 2 : ℝ) := by
  unfold smoothPerronEndpointCorrection
  split <;> norm_num

/-- A height-independent Cauchy envelope for the smooth sharp-Perron kernel
once the height is at least one. -/
noncomputable def smoothSharpPerronKernelEnvelope
    (sigma : ℝ) (X : ℕ) (n : ℕ) : ℝ :=
  if n < X then
    1 + ((X : ℝ) / n) ^ sigma /
      (Real.pi * Real.log ((X : ℝ) / n))
  else if n = X then 1 / 2
  else
    ((X : ℝ) / n) ^ sigma /
      (Real.pi * (-Real.log ((X : ℝ) / n)))

/-- The envelope dominates every kernel at every height `T ≥ 1`. -/
theorem norm_smoothSharpPerronKernel_le_envelope
    {k : ℕ} {sigma T : ℝ} {X : ℕ} (hsigma : 0 < sigma) (hX : 1 ≤ X)
    (hT : 1 ≤ T) (n : Nat.smoothNumbers k) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1‖ ≤
      smoothSharpPerronKernelEnvelope sigma X n.1 := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hXpos : (0 : ℝ) < X := by positivity
  by_cases hnX : n.1 < X
  · rw [smoothSharpPerronKernelEnvelope, if_pos hnX]
    have hnXreal : (n.1 : ℝ) < X := by exact_mod_cast hnX
    have hratio : 1 < (X : ℝ) / n.1 := by
      exact (one_lt_div (by positivity : (0 : ℝ) < n.1)).2 hnXreal
    have hlog : 0 < Real.log ((X : ℝ) / n.1) := Real.log_pos hratio
    calc
      ‖GafniTao.sharpPerronKernel sigma T X n.1‖ ≤
          ‖GafniTao.sharpPerronKernel sigma T X n.1 - 1‖ + 1 := by
            simpa using norm_le_norm_sub_add
              (GafniTao.sharpPerronKernel sigma T X n.1) 1
      _ ≤ ((X : ℝ) / n.1) ^ sigma /
            (Real.pi * T * Real.log ((X : ℝ) / n.1)) + 1 := by
          gcongr
          exact GafniTao.norm_sharpPerronKernel_sub_one_le_of_natCast_lt
            hsigma hTpos hXpos hn hnXreal
      _ ≤ ((X : ℝ) / n.1) ^ sigma /
            (Real.pi * Real.log ((X : ℝ) / n.1)) + 1 := by
          have hnum : 0 ≤ ((X : ℝ) / n.1) ^ sigma :=
            Real.rpow_nonneg (by positivity) _
          have hden : Real.pi * Real.log ((X : ℝ) / n.1) ≤
              Real.pi * T * Real.log ((X : ℝ) / n.1) := by
            have hprod : 0 ≤ (T - 1) *
                (Real.pi * Real.log ((X : ℝ) / n.1)) :=
              mul_nonneg (sub_nonneg.mpr hT)
                (mul_nonneg Real.pi_pos.le hlog.le)
            nlinarith
          gcongr
      _ = 1 + ((X : ℝ) / n.1) ^ sigma /
            (Real.pi * Real.log ((X : ℝ) / n.1)) := by ring
  · by_cases hnEq : n.1 = X
    · rw [smoothSharpPerronKernelEnvelope, if_neg hnX, if_pos hnEq]
      exact GafniTao.norm_sharpPerronKernel_at_natCast_le_half hsigma hXpos hn
        (by exact_mod_cast hnEq.symm)
    · rw [smoothSharpPerronKernelEnvelope, if_neg hnX, if_neg hnEq]
      have hXn : X < n.1 := lt_of_le_of_ne
        (Nat.le_of_not_gt hnX) (Ne.symm hnEq)
      have hXnReal : (X : ℝ) < n.1 := by exact_mod_cast hXn
      have hratioPos : 0 < (X : ℝ) / n.1 := by positivity
      have hratio : (X : ℝ) / n.1 < 1 :=
        (div_lt_one (by positivity : (0 : ℝ) < n.1)).2 hXnReal
      have hlog : 0 < -Real.log ((X : ℝ) / n.1) :=
        neg_pos.mpr (Real.log_neg hratioPos hratio)
      calc
        ‖GafniTao.sharpPerronKernel sigma T X n.1‖ ≤
            ((X : ℝ) / n.1) ^ sigma /
              (Real.pi * T * (-Real.log ((X : ℝ) / n.1))) :=
          GafniTao.norm_sharpPerronKernel_le_of_natCast_lt
            hsigma hTpos hXpos hn hXnReal
        _ ≤ ((X : ℝ) / n.1) ^ sigma /
              (Real.pi * (-Real.log ((X : ℝ) / n.1))) := by
          have hden : Real.pi * (-Real.log ((X : ℝ) / n.1)) ≤
              Real.pi * T * (-Real.log ((X : ℝ) / n.1)) := by
            have hprod : 0 ≤ (T - 1) *
                (Real.pi * (-Real.log ((X : ℝ) / n.1))) :=
              mul_nonneg (sub_nonneg.mpr hT)
                (mul_nonneg Real.pi_pos.le hlog.le)
            nlinarith
          gcongr

/-- The height-independent kernel envelope is summable over every fixed
smooth-number semigroup. -/
theorem summable_smoothSharpPerronKernelEnvelope
    {sigma : ℝ} {X y : ℕ} (hsigma : 0 < sigma) (hX : 1 ≤ X) :
    Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSharpPerronKernelEnvelope sigma X n.1) := by
  let B := fun n : Nat.smoothNumbers (y + 1) =>
    smoothSharpPerronKernelEnvelope sigma X n.1
  have hfinite : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      if n.1 ≤ X then B n else 0) := by
    apply summable_of_ne_finset_zero (s := smoothNumbersUpToSubtype X y)
    intro n hn
    have hnX : ¬ n.1 ≤ X := by
      simpa only [mem_smoothNumbersUpToSubtype] using hn
    simp [hnX]
  let delta : ℝ := -Real.log ((X : ℝ) / (X + 1 : ℕ))
  have hratio0 : 0 < (X : ℝ) / (X + 1 : ℕ) := by positivity
  have hratio1 : (X : ℝ) / (X + 1 : ℕ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (X + 1 : ℕ))]
    exact_mod_cast Nat.lt_succ_self X
  have hdelta : 0 < delta := neg_pos.mpr (Real.log_neg hratio0 hratio1)
  let C : ℝ := (X : ℝ) ^ sigma / (Real.pi * delta)
  have hC : 0 ≤ C := by
    exact div_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg Real.pi_pos.le hdelta.le)
  have hmajor : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      C * (n.1 : ℝ) ^ (-sigma)) :=
    (summable_smoothDirichletSeries_and_eq_eulerProduct
      (y + 1) hsigma).1.mul_left C
  have hBnonneg (n : Nat.smoothNumbers (y + 1)) : 0 ≤ B n := by
    have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_zero_of_mem_smoothNumbers n.2)
    have hnpos : (0 : ℝ) < n.1 := by exact_mod_cast hn
    unfold B smoothSharpPerronKernelEnvelope
    by_cases hnX : n.1 < X
    · rw [if_pos hnX]
      have hratio : 1 < (X : ℝ) / n.1 := by
        apply (one_lt_div hnpos).2
        exact_mod_cast hnX
      exact add_nonneg zero_le_one
        (div_nonneg (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg Real.pi_pos.le (Real.log_pos hratio).le))
    · rw [if_neg hnX]
      by_cases hnEq : n.1 = X
      · rw [if_pos hnEq]
        norm_num
      · rw [if_neg hnEq]
        have hXn : X < n.1 := lt_of_le_of_ne
          (Nat.le_of_not_gt hnX) (Ne.symm hnEq)
        have hratioPos : 0 < (X : ℝ) / n.1 :=
          div_pos (by positivity) hnpos
        have hratio : (X : ℝ) / n.1 < 1 := by
          apply (div_lt_one hnpos).2
          exact_mod_cast hXn
        have hlog : 0 < -Real.log ((X : ℝ) / n.1) :=
          neg_pos.mpr (Real.log_neg hratioPos hratio)
        exact div_nonneg (Real.rpow_nonneg hratioPos.le _)
          (mul_nonneg Real.pi_pos.le hlog.le)
  have htail : Summable (fun n : Nat.smoothNumbers (y + 1) =>
      if X < n.1 then B n else 0) := by
    apply Summable.of_nonneg_of_le
      (fun n => by
        split
        · exact hBnonneg n
        · exact le_rfl)
      (fun n => by
        by_cases hXn : X < n.1
        · rw [if_pos hXn]
          unfold B smoothSharpPerronKernelEnvelope
          rw [if_neg (not_lt_of_ge hXn.le), if_neg (ne_of_gt hXn)]
          have hsuccXn : X + 1 ≤ n.1 := by omega
          have hnpos : 0 < (n.1 : ℝ) := by
            exact_mod_cast (Nat.zero_lt_of_lt hXn)
          have hratioLe : (X : ℝ) / n.1 ≤
              (X : ℝ) / (X + 1 : ℕ) := by
            apply (div_le_div_iff₀ hnpos
              (by positivity : (0 : ℝ) < (X + 1 : ℕ))).2
            exact mul_le_mul_of_nonneg_left
              (by exact_mod_cast hsuccXn) (by positivity)
          have hratioNPos : 0 < (X : ℝ) / n.1 := by positivity
          have hlogLe := Real.log_le_log hratioNPos hratioLe
          have hden : delta ≤ -Real.log ((X : ℝ) / n.1) := by
            dsimp only [delta]
            linarith
          have hdenPos : 0 < -Real.log ((X : ℝ) / n.1) :=
            hdelta.trans_le hden
          have hquot :
              ((X : ℝ) / n.1) ^ sigma /
                  (Real.pi * (-Real.log ((X : ℝ) / n.1))) ≤
                ((X : ℝ) / n.1) ^ sigma / (Real.pi * delta) := by
            gcongr
          refine hquot.trans_eq ?_
          dsimp only [C]
          rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ X) hnpos.le,
            Real.rpow_neg hnpos.le]
          ring
        · rw [if_neg hXn]
          exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      hmajor
  refine (hfinite.add htail).congr (fun n => ?_)
  dsimp only [B]
  by_cases hnX : n.1 ≤ X
  · simp [hnX, not_lt_of_ge hnX]
  · have hXn : X < n.1 := Nat.lt_of_not_ge hnX
    simp [hnX, hXn]

/-- Pointwise large-height inversion for every source-smooth integer. -/
theorem tendsto_smoothSharpPerronKernel_atTop
    {X y : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) (hX : 1 ≤ X)
    (n : Nat.smoothNumbers (y + 1)) :
    Tendsto
      (fun T : ℝ => GafniTao.sharpPerronKernel sigma T X n.1)
      atTop (𝓝 (smoothHalfPerronCutoff X y n)) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  by_cases hnX : n.1 < X
  · rw [smoothHalfPerronCutoff, if_pos hnX]
    exact tendsto_sharpPerronKernel_atTop_of_natCast_lt hsigma
      (show (0 : ℝ) < X by positivity) hn (by exact_mod_cast hnX)
  · by_cases hnEq : n.1 = X
    · rw [smoothHalfPerronCutoff, if_neg hnX, if_pos hnEq]
      exact tendsto_sharpPerronKernel_atTop_of_eq_natCast
        (x := (X : ℝ)) (n := n.1) hsigma
        (show (0 : ℝ) < X by positivity) hn (by exact_mod_cast hnEq.symm)
    · have hXn : X < n.1 :=
        lt_of_le_of_ne (Nat.le_of_not_gt hnX) (Ne.symm hnEq)
      rw [smoothHalfPerronCutoff, if_neg hnX, if_neg hnEq]
      exact tendsto_sharpPerronKernel_atTop_of_natCast_gt hsigma
        (show (0 : ℝ) < X by positivity) hn (by exact_mod_cast hXn)

/-- Every finite smooth partial sum obeys symmetric sharp-Perron inversion
term by term. -/
theorem tendsto_finsetSum_smoothSharpPerronKernel_atTop
    {X y : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) (hX : 1 ≤ X)
    (s : Finset (Nat.smoothNumbers (y + 1))) :
    Tendsto
      (fun T : ℝ => ∑ n ∈ s,
        GafniTao.sharpPerronKernel sigma T X n.1)
      atTop (𝓝 (∑ n ∈ s, smoothHalfPerronCutoff X y n)) := by
  exact tendsto_finsetSum s fun n _hn =>
    tendsto_smoothSharpPerronKernel_atTop hsigma hX n

/-- Tannery's theorem upgrades the scalar inversion limits to the complete
smooth-number sharp-Perron series. -/
theorem tendsto_tsum_smoothSharpPerronKernel_atTop
    {X y : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) (hX : 1 ≤ X) :
    Tendsto
      (fun T : ℝ => ∑' n : Nat.smoothNumbers (y + 1),
        GafniTao.sharpPerronKernel sigma T X n.1)
      atTop (𝓝 ((psiNat X y : ℂ) - smoothPerronEndpointCorrection X y)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (summable_smoothSharpPerronKernelEnvelope hsigma hX)
    (tendsto_smoothSharpPerronKernel_atTop hsigma hX)
    (show ∀ᶠ T : ℝ in atTop, ∀ n : Nat.smoothNumbers (y + 1),
        ‖GafniTao.sharpPerronKernel sigma T X n.1‖ ≤
          smoothSharpPerronKernelEnvelope sigma X n.1 by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT n
      exact norm_smoothSharpPerronKernel_le_envelope hsigma hX hT n)
  simpa only [tsum_smoothHalfPerronCutoff_eq_psiNat_sub_endpointCorrection]
    using h

end

end Tao2026
