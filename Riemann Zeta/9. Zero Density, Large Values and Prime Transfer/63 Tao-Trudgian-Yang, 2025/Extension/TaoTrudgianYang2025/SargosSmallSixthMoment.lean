import TaoTrudgianYang2025.SargosSixthIntegral

/-!
# The unweighted small-alpha sixth moment

A two-window estimate suffices: the small window uses the trivial square
bound, and the large window uses the actual quartic curvature bound.
This yields log^5, stronger than the source's log^6 assertion.
-/

noncomputable section

open MeasureTheory Set Filter

namespace TaoTrudgianYang2025

theorem sargosQuartic_small_sixth_moment {N : ℕ} (hN : 1 ≤ N) :
    (∫ α in Icc (0 : ℝ) (1/Real.sqrt N),
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
      44845498368*(1+Real.log N)^5 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNp
  have hsN : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [Real.sq_sqrt hNp.le,Real.sqrt_nonneg (N : ℝ),
      mul_nonneg hNp.le (sub_nonneg.mpr hNr)]
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt hNp.le,Real.sqrt_nonneg (N : ℝ)]
  let A : ℝ := 1/Real.sqrt N
  let B : ℝ := 128/(N : ℝ)
  let c : ℝ := -(1/(N : ℝ)^3)
  let d : ℝ := 1/(N : ℝ)^3
  let L : ℝ := 1+Real.log N
  let J (p : ℕ) (α : ℝ) : ℝ := ∫ γ in Icc c d,
    (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^p
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : A ≤ 1 := by dsimp [A]; exact (div_le_one hs).2 hs1
  have hAlo : 1/(N : ℝ) ≤ A := by
    dsimp [A]
    exact one_div_le_one_div_of_le hs hsN
  have hBlo : 1/(N : ℝ) ≤ B := by
    dsimp [B]
    exact div_le_div_of_nonneg_right (by norm_num) hNp.le
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hJ (p : ℕ) (α : ℝ) : 0 ≤ J p α :=
    integral_nonneg (fun γ => pow_nonneg
      (sargosQuarticPrefixMaximum_nonneg N (fun _ => 1) α γ) p)
  have hJi (p : ℕ) (a b : ℝ) : IntegrableOn (J p) (Icc a b) :=
    integrable_sargosQuarticUnweightedPower_outer N p a b c d
  have hsplit := sargos_integral_Icc_split_le (J 6) A B (hJ 6) (hJi 6 0 B) (hJi 6 B A)
  have hsmall := sargosQuartic_sixth_rectangle_le_trivial N 0 B c d
  have hlarge := sargosQuartic_sixth_rectangle_le_curvature hN hA1
  change (∫ α in Icc B A, J 6 α) ≤
    (4096*(N : ℝ)^2*A)*(∫ α in Icc B A, J 4 α) at hlarge
  have hsub : Icc B A ⊆ Icc (0 : ℝ) A := Icc_subset_Icc hB0 le_rfl
  have hmono : (∫ α in Icc B A, J 4 α) ≤ ∫ α in Icc (0 : ℝ) A, J 4 α :=
    setIntegral_mono_set (hJi 4 0 A) (Eventually.of_forall (hJ 4)) hsub.eventuallyLE
  have h4small := sargosQuartic_maximal_fourth_moment hN (fun _ => 1)
    (by intro n hn; simp) hBlo
  have h4large := sargosQuartic_maximal_fourth_moment hN (fun _ => 1)
    (by intro n hn; simp) hAlo
  have hAeq : (N : ℝ)*A^2 = 1 := by
    dsimp [A]
    rw [div_pow,one_pow,Real.sq_sqrt hNp.le]
    field_simp
  calc
    _ ≤ (∫ α in Icc (0 : ℝ) B, J 6 α)+(∫ α in Icc B A, J 6 α) := hsplit
    _ ≤ (N : ℝ)^2*(∫ α in Icc (0 : ℝ) B, J 4 α)+
        (4096*(N : ℝ)^2*A)*(∫ α in Icc (0 : ℝ) A, J 4 α) :=
      add_le_add hsmall (hlarge.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
    _ ≤ (N : ℝ)^2*(10616832*B/(N : ℝ)*L^5)+
        (4096*(N : ℝ)^2*A)*(10616832*A/(N : ℝ)*L^5) :=
      add_le_add
        (mul_le_mul_of_nonneg_left h4small (by positivity))
        (mul_le_mul_of_nonneg_left h4large (by positivity))
    _ = _ := by
      have he1 : (N : ℝ)^2*(10616832*B/(N : ℝ)*L^5) = 1358954496*L^5 := by
        dsimp [B]
        field_simp
        ring
      have he2 : (4096*(N : ℝ)^2*A)*(10616832*A/(N : ℝ)*L^5) =
          43486543872*L^5*((N : ℝ)*A^2) := by
        field_simp
        ring
      rw [he1,he2,hAeq]
      dsimp [L]
      ring

theorem sargosQuartic_small_sixth_moment_log_six {N : ℕ} (hN : 1 ≤ N) :
    (∫ α in Icc (0 : ℝ) (1/Real.sqrt N),
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
      44845498368*(1+Real.log N)^6 := by
  apply (sargosQuartic_small_sixth_moment hN).trans
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hp : (1+Real.log (N : ℝ))^5 ≤ (1+Real.log (N : ℝ))^6 := by
    have h := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1+Real.log N)
      (by positivity : 0 ≤ (1+Real.log (N : ℝ))^5)
    nlinarith
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

theorem sargosQuartic_small_sixth_moment_source {N : ℕ} (hN : 2 ≤ N) :
    (∫ α in Icc (0 : ℝ) (1/Real.sqrt N),
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
      (44845498368*(1+1/Real.log 2)^6)*(Real.log N)^6 := by
  have hN1 : 1 ≤ N := by omega
  apply (sargosQuartic_small_sixth_moment_log_six hN1).trans
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNr
  have hlog : 0 ≤ Real.log (N : ℝ) := le_trans h2.le hl
  have hquot : 1 ≤ Real.log (N : ℝ)/Real.log 2 := (le_div_iff₀ h2).2 (by simpa)
  have hbase : 1+Real.log (N : ℝ) ≤ (1+1/Real.log 2)*Real.log N := by
    calc
      _ ≤ Real.log (N : ℝ)/Real.log 2+Real.log N := add_le_add hquot le_rfl
      _ = _ := by ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+Real.log (N : ℝ)) hbase 6
  calc
    _ ≤ 44845498368*((1+1/Real.log 2)*Real.log N)^6 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by rw [mul_pow]; ring

end TaoTrudgianYang2025
