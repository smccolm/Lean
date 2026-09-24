import TaoTrudgianYang2025.DirichletMeanSquareLower
import TaoTrudgianYang2025.ZetaGrowthHighHeight

/-!
# Nonvanishing mean-square mass forbids negative growth exponents

A uniform power saving for all literal Dirichlet blocks at sigma=1/2
contradicts their actual lower mean square. The high-height growth
transfer therefore forces every genuine closed-strip growth candidate
to be nonnegative, and so also the actual extended-real infimum.
-/

noncomputable section
open Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem zetaLargeValueExponent_half_ne_bot_highHeight
    {τ : ℝ} (hτ : 2 ≤ τ) : zetaLargeValueExponent (1/2) τ ≠ ⊥ := by
  intro hbot
  obtain ⟨C,δ,hC,hδ,hpoint⟩ :=
    exists_zetaPointwise_powerSaving_of_exponent_eq_bot hbot
  have hev : ∀ᶠ x : ℝ in atTop, 2 ≤ x^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop 2)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  obtain ⟨N,hNlarge⟩ := exists_nat_gt (max (max C N₀) (4*(5*Real.pi+1)+2))
  have hNC : C ≤ (N : ℝ) := (le_max_left _ _).trans
    ((le_max_left _ _).trans hNlarge.le)
  have hNt : N₀ ≤ (N : ℝ) := (le_max_right _ _).trans
    ((le_max_left _ _).trans hNlarge.le)
  have hNconst : 4*(5*Real.pi+1)+2 < (N : ℝ) :=
    (le_max_right _ _).trans_lt hNlarge
  have hNtwo : (2 : ℝ) < N := by nlinarith [Real.pi_pos]
  have hNpos : (0 : ℝ) < N := by linarith
  have hN : 0 < N := by exact_mod_cast hNpos
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hpowδ : 2 ≤ (N : ℝ)^δ := hN₀ _ hNt
  let H : ℝ := (N : ℝ)^τ
  have hHpos : 0 < H := Real.rpow_pos_of_pos hNpos _
  have hHlower : (N : ℝ)^2 ≤ H := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNone hτ
  have hI : IsIntegerInterval (Finset.Icc (N+1) (2*N)) := ⟨N+1,2*N,rfl⟩
  have hIN : Finset.Icc (N+1) (2*N) ⊆ Finset.Icc N (2*N) := by
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
  have hpointSq (t : ℝ) (ht : t ∈ Icc H (2*H)) :
      ‖dirichletTime N (fun _ => 1) t‖^2 ≤ (N : ℝ)/4 := by
    have htl : (N : ℝ)^(τ-δ) ≤ t :=
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)).trans ht.1
    have htu : t ≤ (N : ℝ)^(τ+δ) := by
      calc
        t ≤ 2*H := ht.2
        _ ≤ (N : ℝ)^δ*H := mul_le_mul_of_nonneg_right hpowδ hHpos.le
        _ = _ := by dsimp [H]; rw [← Real.rpow_add hNpos]; congr 1; ring
    have hh := (hpoint N _ t hNC hI hIN htl htu).le
    rw [← dirichletTime_one_eq_phase_interval] at hh
    have hs := mul_self_le_mul_self (norm_nonneg _) hh
    have hpowTwo : ((N : ℝ)^(1/2-δ))^2 = (N : ℝ)^(1-2*δ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
      congr 1
      norm_num
      ring
    have hδTwo : (4 : ℝ) ≤ (N : ℝ)^(2*δ) := by
      have hsδ := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hpowδ
      rw [← Real.rpow_add hNpos] at hsδ
      have heq : δ+δ = 2*δ := by ring
      norm_num only [heq] at hsδ
      exact hsδ
    have hmul : (N : ℝ)^(1-2*δ)*(N : ℝ)^(2*δ) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      have heq : (1-2*δ)+(2*δ) = 1 := by ring
      rw [heq,Real.rpow_one]
    have hquarter : (N : ℝ)^(1-2*δ) ≤ (N : ℝ)/4 := by
      have hm := mul_le_mul_of_nonneg_left hδTwo
        (Real.rpow_nonneg hNpos.le (1-2*δ))
      rw [hmul] at hm
      linarith
    calc
      _ ≤ ((N : ℝ)^(1/2-δ))^2 := by simpa only [pow_two] using hs
      _ ≤ _ := hpowTwo ▸ hquarter
  have hupper :
      (∫ t in H..2*H, ‖dirichletTime N (fun _ => 1) t‖^2) ≤ H*(N : ℝ)/4 := by
    calc
      _ ≤ ∫ _t in H..2*H, (N : ℝ)/4 :=
        intervalIntegral.integral_mono_on (by linarith)
          (((continuous_dirichletTime N (fun _ => 1)).norm.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) hpointSq
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]; ring
  have hlower := integral_dirichletPhase_norm_sq_ge N H (2*H) hN
  simp only [← dirichletTime_one_eq_phase_interval] at hlower
  have hmain : 4*(5*Real.pi+1)*(N : ℝ) < H := by
    have hm := mul_lt_mul_of_pos_right (show 4*(5*Real.pi+1) < (N : ℝ) by linarith) hNpos
    nlinarith
  have hpos : 0 < H*(N : ℝ) := mul_pos hHpos hNpos
  nlinarith

theorem IsZetaGrowthBound.closedStrip_nonneg {c m : ℝ}
    (hGrowth : IsZetaGrowthBound c m) (hc : 1/2 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ m := by
  by_contra hneg
  have hm : m < 0 := lt_of_not_ge hneg
  let τ : ℝ := 2+(c+1)/(-m)
  have hτ : 2 ≤ τ := by
    have hdiv : 0 ≤ (c+1)/(-m) := div_nonneg (by linarith) (by linarith)
    dsimp [τ]
    linarith
  have hgap : c+τ*m < 1/2 := by
    have heq : c+τ*m = 2*m-1 := by dsimp [τ]; field_simp [hm.ne]; ring
    rw [heq]
    linarith
  exact zetaLargeValueExponent_half_ne_bot_highHeight hτ
    (hGrowth.highHeight_exponent_eq_bot hc hc1 le_rfl (by norm_num) hτ hgap)

theorem zetaGrowthExponent_closedStrip_nonneg {c : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) : 0 ≤ zetaGrowthExponent c := by
  apply le_sInf
  rintro x ⟨m,hm,rfl⟩
  change (0 : EReal) ≤ (m : EReal)
  exact_mod_cast hm.closedStrip_nonneg hc hc1

end TaoTrudgianYang2025
