import GafniTao.FordAsymptoticZeroFree
import GafniTao.Pintz2023DyadicHeightShell

/-!
# Pintz (2023): positivity of the shifted zero distance

Equation (4.12) replaces `eta_j` by `eta_j - 1/lambda`.  The positivity of
this shifted quantity is a genuine use of the Vinogradov--Korobov zero-free
region; it is not implied by membership in the near-one rectangle alone.
-/

open Filter Asymptotics
open scoped Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem vinogradovKorobovDenominator_isLittleO_log :
    vinogradovKorobovDenominator =o[atTop] Real.log := by
  have hCore :=
    (isLittleO_log_rpow_rpow_atTop (1 / 3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
        Real.tendsto_log_atTop
  have hProd := hCore.mul_isBigO
    (isBigO_refl (fun T : ℝ => Real.log T ^ (2 / 3 : ℝ)) atTop)
  have hEventually := eventually_ge_atTop (Real.exp (Real.exp 1))
  refine hProd.congr' ?_ ?_
  · filter_upwards [hEventually] with T hT
    unfold vinogradovKorobovDenominator
    simp only [Function.comp_apply]
    ring
  · filter_upwards [hEventually] with T hT
    have hLogPos : 0 < Real.log T := by
      have hLower : Real.exp 1 ≤ Real.log T := by
        simpa only [Real.log_exp] using
          Real.log_le_log (Real.exp_pos _) hT
      exact (Real.exp_pos 1).trans_le hLower
    simp only [Function.comp_apply]
    rw [← Real.rpow_add hLogPos]
    norm_num

/-- Uniformly on the physical shell, Ford's proved zero-free region makes
the shifted parameter `eta_j - 1/lambda` strictly positive. -/
theorem eventually_pintz2023_shifted_eta_pos_on_shell
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ T : ℝ in atTop, ∀ rho ∈ pintz2023DyadicHeightShell (1 / 2) T,
      1 / pintz2023SourceLambda T k < 1 - rho.re := by
  obtain ⟨c, H, hc, hH, hZeroFree⟩ := ford_asymptotic_zero_free_native
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hSmall := vinogradovKorobovDenominator_isLittleO_log.bound
    (div_pos (mul_pos two_pos hc) hkReal)
  filter_upwards [hSmall,
    eventually_ge_atTop (max (2 * H) (Real.exp (Real.exp 1)))] with
      T hSmallT hT
  intro rho hrho
  have hTBase : Real.exp (Real.exp 1) ≤ T :=
    (le_max_right _ _).trans hT
  have hTPos : 0 < T := (Real.exp_pos _).trans_le hTBase
  have hLogPos : 0 < Real.log T := by
    have hLower : Real.exp 1 ≤ Real.log T := by
      simpa only [Real.log_exp] using
        Real.log_le_log (Real.exp_pos _) hTBase
    exact (Real.exp_pos 1).trans_le hLower
  have hDenPos : 0 < vinogradovKorobovDenominator T :=
    vinogradovKorobovDenominator_pos hTBase
  have hDenNonneg : 0 ≤ vinogradovKorobovDenominator T := hDenPos.le
  have hLogNonneg : 0 ≤ Real.log T := hLogPos.le
  rw [Real.norm_eq_abs, abs_of_nonneg hDenNonneg,
    Real.norm_eq_abs, abs_of_nonneg hLogNonneg] at hSmallT
  have hWidth : 1 / pintz2023SourceLambda T k ≤
      c / vinogradovKorobovDenominator T := by
    unfold pintz2023SourceLambda
    apply (div_le_div_iff₀ (mul_pos (div_pos two_pos hkReal) hLogPos)
      hDenPos).2
    have hScaled := mul_le_mul_of_nonneg_left hSmallT hkReal.le
    field_simp [hkReal.ne'] at hScaled ⊢
    nlinarith
  have hrhoShell := Finset.mem_filter.mp hrho
  have hrhoZero : rho ∈ zeroSet 0 T :=
    zeroSet_subset_of_sigma_le (by norm_num) hrhoShell.1
  have hrhoHigh : H ≤ |rho.im| := by
    have hHalf : H ≤ T / 2 := by
      have := (le_max_left (2 * H) (Real.exp (Real.exp 1))).trans hT
      linarith
    exact (hHalf.trans_lt hrhoShell.2).le
  have hFord := vinogradovKorobov_high_zero_uniform hc.le hH hZeroFree
    hrhoZero hrhoHigh
  exact hWidth.trans_lt (by linarith)

/-- The same positivity statement for every narrower near-one shell. -/
theorem eventually_pintz2023_shifted_eta_pos_on_shell_of_le_half
    {eta : ℝ} {k : ℕ} (heta : eta ≤ 1 / 2) (hk : 0 < k) :
    ∀ᶠ T : ℝ in atTop, ∀ rho ∈ pintz2023DyadicHeightShell eta T,
      1 / pintz2023SourceLambda T k < 1 - rho.re := by
  filter_upwards [eventually_pintz2023_shifted_eta_pos_on_shell hk] with
      T hT
  intro rho hrho
  apply hT rho
  unfold pintz2023DyadicHeightShell at hrho ⊢
  rw [Finset.mem_filter] at hrho ⊢
  exact ⟨zeroSet_subset_of_sigma_le (by linarith) hrho.1, hrho.2⟩

#print axioms vinogradovKorobovDenominator_isLittleO_log
#print axioms eventually_pintz2023_shifted_eta_pos_on_shell
#print axioms eventually_pintz2023_shifted_eta_pos_on_shell_of_le_half

end

end GafniTao
