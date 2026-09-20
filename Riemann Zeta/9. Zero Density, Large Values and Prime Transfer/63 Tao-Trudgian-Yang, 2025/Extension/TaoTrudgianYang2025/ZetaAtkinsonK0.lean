import TaoTrudgianYang2025.ZetaAtkinsonVoronoi

/-!
# Decay of the phase-adjusted modified-Bessel source

The integer-lattice phase has unit norm, not a constant value on the
continuous source. Its integral is not identified with the unadjusted
integral: the genuine pointwise majorant, support and mass are transferred.
Every arithmetic coefficient remains in the summable complete branch.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_zetaAtkinsonK0_integrand (T G L : ℝ) (n : ℕ) (x : ℝ) :
    ‖zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ =
        ‖zetaBesselK0SourceIntegrand T G L n x‖ := by
  simp only [zetaBesselK0SourceIntegrand, norm_mul, norm_zetaAtkinsonDivisorTest]

theorem integrable_zetaAtkinsonK0_integrand {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun x : ℝ => zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)) := by
  have hi := (integrable_zetaBesselK0SourceIntegrand hT hG hL hwidth hn).bdd_mul
    contDiff_zetaDivisorLatticePhase.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (norm_zetaDivisorLatticePhase x).le))
  convert hi using 1
  ext x
  simp only [zetaAtkinsonDivisorTest, zetaBesselK0SourceIntegrand, mul_assoc]

theorem norm_integral_zetaAtkinsonK0_le {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
          ∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest T G L x‖ := by
  have hi : IntegrableOn (fun x : ℝ =>
      (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
        ‖zetaSmoothDivisorTest T G L x‖) (Ioi 0) :=
    ((integrable_zetaSmoothDivisorTest (by linarith : 0 < T) hG hL).norm.integrableOn).const_mul _
  have hb (x : ℝ) : ‖zetaAtkinsonDivisorTest T G L x *
      (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
        (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) *
          ‖zetaSmoothDivisorTest T G L x‖ := by
    rw [norm_zetaAtkinsonK0_integrand]
    exact norm_zetaBesselK0SourceIntegrand_le hT hG hL hwidth hn k x
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
  simpa only [integral_const_mul] using h

theorem exists_norm_integral_zetaAtkinsonK0_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
      ‖∫ x : ℝ in Ioi 0, zetaAtkinsonDivisorTest T G L x *
        (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * n)) : ℂ)‖ ≤
          C * G * T / (T ^ k * (n : ℝ) ^ k) := by
  obtain ⟨C, hC, hmass⟩ := exists_integral_norm_zetaSmoothDivisorTest_le
  refine ⟨zetaBesselK0PowerConstant k * C, mul_pos (zetaBesselK0PowerConstant_pos k) hC, ?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  apply (norm_integral_zetaAtkinsonK0_le hT hG hL hwidth hn k).trans
  have hfac : 0 ≤ zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k) :=
    div_nonneg (zetaBesselK0PowerConstant_pos k).le (by positivity)
  calc
    _ ≤ (zetaBesselK0PowerConstant k / (T ^ k * (n : ℝ) ^ k)) * (C * G * T) :=
      mul_le_mul_of_nonneg_left (hmass T G L hT hG hGT hL hwidth) hfac
    _ = _ := by ring

theorem exists_norm_zetaAtkinsonBesselPlusTerm_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
      ‖zetaAtkinsonBesselPlusTerm T G L n‖ ≤
        (C * G * T / T ^ k) * ‖divisorDirichletTerm 2 n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_zetaAtkinsonK0_le k
  refine ⟨4 * C, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonBesselPlusTerm, divisorWeight, divisorDirichletTerm, LSeries.term]
  have hnpos := Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnk : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ k := pow_le_pow_right₀ hn1 hk
  have hsmall : C * G * T / (T ^ k * (n : ℝ) ^ k) ≤
      C * G * T / (T ^ k * (n : ℝ) ^ 2) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hnk (by positivity))
  unfold zetaAtkinsonBesselPlusTerm
  rw [norm_mul, norm_mul, norm_divisorDirichletTerm_two]
  norm_num only [norm_ofNat]
  calc
    _ ≤ ‖divisorWeight n‖ * 4 * (C * G * T / (T ^ k * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left ((hbound T G L hT hG hGT hL hwidth n hnpos).trans hsmall) (by positivity)
    _ = _ := by ring

theorem summable_zetaAtkinsonBesselPlusTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G) : Summable (zetaAtkinsonBesselPlusTerm T G L) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlusTerm_le (k := 2) le_rfl
  exact Summable.of_norm_bounded
    (((summable_divisorDirichletTerm (s := (2 : ℂ)) (by norm_num)).norm).mul_left (C * G * T / T ^ 2))
    (hbound T G L hT hG hGT hL hwidth)

theorem hasSum_zetaAtkinsonBesselPlusTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    HasSum (zetaAtkinsonBesselPlusTerm T G L) (zetaAtkinsonBesselPlus T G L) :=
  (summable_zetaAtkinsonBesselPlusTerm hT hG hGT hL hwidth).hasSum

theorem exists_norm_zetaAtkinsonBesselPlus_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ‖zetaAtkinsonBesselPlus T G L‖ ≤ C * G * T / T ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlusTerm_le hk
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm 2 n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := summable_zetaAtkinsonBesselPlusTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (2 : ℂ)) (by norm_num)).norm
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  change ‖∑' n : ℕ, zetaAtkinsonBesselPlusTerm T G L n‖ ≤ _
  calc
    _ ≤ ∑' n : ℕ, ‖zetaAtkinsonBesselPlusTerm T G L n‖ := hnorm
    _ ≤ ∑' n : ℕ, (C * G * T / T ^ k) * ‖divisorDirichletTerm 2 n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = (C * G * T / T ^ k) * S := tsum_mul_left
    _ ≤ _ := by
      have hpos : 0 ≤ C * G * T / T ^ k := by positivity
      have h := mul_le_mul_of_nonneg_left (show S ≤ 1 + S by linarith) hpos
      convert h using 1
      ring


theorem exists_zetaAtkinsonBesselPlus_powerSaving {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T →
      T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-A) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (A + 2)
  let k : ℕ := max 2 m
  have hk : 2 ≤ k := le_max_left _ _
  have hkA : A + 2 ≤ (k : ℝ) := hm.le.trans (by exact_mod_cast le_max_right 2 m)
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonBesselPlus_le hk
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-A) := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop C] with T hsupport hscale hTC
    intro G hlower hupper
    obtain ⟨hG, hlog, hwidth, _⟩ := hsupport.2 G hlower
    have hb := hbound T G (Real.log T) hsupport.1 hG (hscale.2.2 G hG hupper).1 hlog hwidth
    have hp := mul_le_mul_of_nonneg_left
      (besselK0_source_power_absorb (by linarith [hsupport.1]) hTC hkA) hG.le
    apply hb.trans
    convert hp using 1
    ring
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨max 16 T₁, le_max_left _ _, ?_⟩
  intro T G hT hlower hupper
  exact hT₁ T ((le_max_right _ _).trans hT) G hlower hupper


end TaoTrudgianYang2025

