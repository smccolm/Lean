import TaoTrudgianYang2025.AtkinsonMorseStationary
import TaoTrudgianYang2025.AtkinsonGaussianVariation
import TaoTrudgianYang2025.AtkinsonSaddleSamples
import TaoTrudgianYang2025.AtkinsonMainWeightBounds

/-!
# Ivić's sharp printed Atkinson local mean-square source

Theorem 6.2, (6.20)--(6.23), in Ivić's Orsay 83.06 text is proved at
the actual zeta integral, original full power widths and literal printed
phase, prefix endpoints, dyadic range, logarithmic cutoff and damping.

The alternate proof consumes the full-width Morse stationary theorem at
width 4G. Both original signed weights are controlled; finite Abel summation
retains the endpoint-plus-integral expression. Exact divisor summation
absorbs the small blocks without an epsilon loss, and the actual Gaussian
decay pays for replacing the working cutoff by the printed one.

No source-form estimate, moment theorem or conclusion-shaped certificate is
assumed. This module does not alter either frozen false source contract or
either permanently retained counterexample. The shifted-height display
(6.24) is distinct and is not asserted by the theorem below.
-/

noncomputable section
open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025.AtkinsonPrintedSource

theorem abs_saddleRoot_sub_le {A : ℝ} (hA : 0 < A) (b c : ℝ) :
    |atkinsonSaddleRoot A b-atkinsonSaddleRoot A c| ≤ |b-c| := by
  have hordered (b c : ℝ) (hbc : b ≤ c) :
      atkinsonSaddleRoot A c-atkinsonSaddleRoot A b ≤ c-b := by
    have hr := atkinsonSaddleRoot_monotone hA hbc
    have hd := div_le_div_of_nonneg_left hA.le (atkinsonSaddleRoot_pos hA b) hr
    have hb := atkinsonSaddleRoot_inverse_identity hA b
    have hc := atkinsonSaddleRoot_inverse_identity hA c
    linarith
  rcases le_total b c with hbc | hcb
  · rw [abs_of_nonpos (sub_nonpos.mpr (atkinsonSaddleRoot_monotone hA hbc)),
      abs_of_nonpos (sub_nonpos.mpr hbc)]
    linarith [hordered b c hbc]
  · rw [abs_of_nonneg (sub_nonneg.mpr (atkinsonSaddleRoot_monotone hA hcb)),
      abs_of_nonneg (sub_nonneg.mpr hcb)]
    exact hordered c b hcb

theorem sqrt_succ_sub_le {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x+1)-Real.sqrt x ≤ 1/Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hle := Real.sqrt_le_sqrt (show x ≤ x+1 by linarith)
  have he : (Real.sqrt (x+1)-Real.sqrt x)*(Real.sqrt (x+1)+Real.sqrt x) = 1 := by
    nlinarith [Real.sq_sqrt hx.le,Real.sq_sqrt (show 0 ≤ x+1 by linarith)]
  apply (le_div_iff₀ hs).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (Real.sqrt_nonneg (x+1))]

theorem abs_saddleRoot_sqrt_succ_sub_le {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    |atkinsonSaddleRoot (T/(2*Real.pi)) (Real.sqrt ((n+1:ℕ):ℝ))-
      atkinsonSaddleRoot (T/(2*Real.pi)) (Real.sqrt (n:ℝ))| ≤ 1/Real.sqrt (n:ℝ) := by
  have h := abs_saddleRoot_sub_le (by positivity : 0 < T/(2*Real.pi))
    (Real.sqrt ((n+1:ℕ):ℝ)) (Real.sqrt (n:ℝ))
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)))] at h
  exact h.trans (by simpa only [Nat.cast_add,Nat.cast_one] using
    sqrt_succ_sub_le (by exact_mod_cast hn : 0 < (n:ℝ)))

theorem abs_saddleRoot_neg_sqrt_succ_sub_le {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    |atkinsonSaddleRoot (T/(2*Real.pi)) (-Real.sqrt ((n+1:ℕ):ℝ))-
      atkinsonSaddleRoot (T/(2*Real.pi)) (-Real.sqrt (n:ℝ))| ≤ 1/Real.sqrt (n:ℝ) := by
  have h := abs_saddleRoot_sub_le (by positivity : 0 < T/(2*Real.pi))
    (-Real.sqrt ((n+1:ℕ):ℝ)) (-Real.sqrt (n:ℝ))
  have harg : |-Real.sqrt ((n+1:ℕ):ℝ)-(-Real.sqrt (n:ℝ))| =
      Real.sqrt ((n+1:ℕ):ℝ)-Real.sqrt (n:ℝ) := by
    rw [neg_sub_neg,abs_of_nonpos
      (sub_nonpos.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)))]
    ring
  rw [harg] at h
  exact h.trans (by simpa only [Nat.cast_add,Nat.cast_one] using
    sqrt_succ_sub_le (by exact_mod_cast hn : 0 < (n:ℝ)))

theorem zetaDivisorBandCutoff_width_ratio (G L T x : ℝ) :
    zetaDivisorBandCutoff T (G/L) 1 x = zetaDivisorBandCutoff T G L x := by
  unfold zetaDivisorBandCutoff zetaBandCutoff zetaDivisorBandEdge
  congr 4 <;> field_simp

theorem exists_intervalC2Bound_cutoff_width_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → 0 < L → 8*L ≤ G →
      IntervalC2Bound (fun u => (zetaDivisorBandCutoff T G L (T*u^2) : ℂ))
        (1/4) 1 C ((1+2*Real.pi*Real.exp 1)*(G/L)) := by
  obtain ⟨C,hC,hbound⟩ := exists_intervalC2Bound_zetaDivisorBandCutoff_root
  refine ⟨C,hC,?_⟩
  intro T G L hT hG hL hwidth
  have h := hbound T (G/L) 1 hT (by positivity) le_rfl
    (by apply (le_div_iff₀ hL).mpr; nlinarith)
  simpa only [zetaDivisorBandCutoff_width_ratio] using h

theorem exists_norm_saddleCutoff_increment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → 0 < L → 8*L ≤ G →
      ∀ n : ℕ, 0 < n → 10000*((n+1:ℕ):ℝ) ≤ T →
      ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (Real.sqrt ((n+1:ℕ):ℝ))) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (Real.sqrt (n:ℝ))) : ℂ)‖ ≤
          C*G/(L*Real.sqrt T*Real.sqrt (n:ℝ)) ∧
      ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (-Real.sqrt ((n+1:ℕ):ℝ))) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (-Real.sqrt (n:ℝ))) : ℂ)‖ ≤
          C*G/(L*Real.sqrt T*Real.sqrt (n:ℝ)) := by
  obtain ⟨C,hC,hcut⟩ := exists_intervalC2Bound_cutoff_width_ratio
  refine ⟨C*(1+2*Real.pi*Real.exp 1),by positivity,?_⟩
  intro T G L hT hG hL hwidth n hn hN
  have hb := hcut T G L hT hG hL hwidth
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hmem0 := atkinsonRootSample_mem hT n 1 hN 0 (by norm_num)
  have hmem1 := atkinsonRootSample_mem hT n 1 hN 1 le_rfl
  have he (b : ℝ) : T*(atkinsonSaddleRoot (T/(2*Real.pi)) b/Real.sqrt T)^2 =
      zetaAtkinsonSaddle T b := by
    unfold zetaAtkinsonSaddle
    rw [div_pow,Real.sq_sqrt hT.le]
    field_simp
  have hbound (b c : ℝ)
      (hx : atkinsonSaddleRoot (T/(2*Real.pi)) b/Real.sqrt T ∈ Icc (1/4) 1)
      (hy : atkinsonSaddleRoot (T/(2*Real.pi)) c/Real.sqrt T ∈ Icc (1/4) 1)
      (hd : |atkinsonSaddleRoot (T/(2*Real.pi)) b-
        atkinsonSaddleRoot (T/(2*Real.pi)) c| ≤ 1/Real.sqrt (n:ℝ)) :
      ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T c) : ℂ)‖ ≤
          (C*(1+2*Real.pi*Real.exp 1))*G/(L*Real.sqrt T*Real.sqrt (n:ℝ)) := by
    have h := hb.norm_sub_le hy hx
    simp only [he,← sub_div,abs_div,abs_of_pos hs] at h
    apply h.trans
    calc
      _ ≤ C*((1+2*Real.pi*Real.exp 1)*(G/L))*((1/Real.sqrt (n:ℝ))/Real.sqrt T) := by
        gcongr
      _ = _ := by ring
  constructor
  · exact hbound _ _ hmem1.1 (by simpa only [atkinsonPositiveRootSample,Nat.add_zero] using hmem0.1)
      (abs_saddleRoot_sqrt_succ_sub_le hT n hn)
  · exact hbound _ _ hmem1.2 (by simpa only [atkinsonNegativeRootSample,Nat.add_zero] using hmem0.2)
      (abs_saddleRoot_neg_sqrt_succ_sub_le hT n hn)

theorem exists_norm_saddleCutoff_source_increment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → G ≤ Real.sqrt T →
      1 ≤ L → 1200*L ≤ G → ∀ n : ℕ, 0 < n → n+1 ≤ atkinsonSourceCutoff T G L →
      ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (Real.sqrt ((n+1:ℕ):ℝ))) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (Real.sqrt (n:ℝ))) : ℂ)‖ ≤ C/(n:ℝ) ∧
      ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (-Real.sqrt ((n+1:ℕ):ℝ))) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T (-Real.sqrt (n:ℝ))) : ℂ)‖ ≤ C/(n:ℝ) := by
  obtain ⟨C,hC,hinc⟩ := exists_norm_saddleCutoff_increment_le
  refine ⟨7*C,by positivity,?_⟩
  intro T G L hT hG hupper hL hwidth n hn hncut
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hN := atkinsonSourceCutoff_le_small hT hG hL0.le hwidth
  have hnsmall : 10000*((n+1:ℕ):ℝ) ≤ T := by
    have hcast : ((n+1:ℕ):ℝ) ≤ atkinsonSourceCutoff T G L := by exact_mod_cast hncut
    linarith
  have hnatural := atkinsonSourceCutoff_frequency_natural (by linarith : 1 ≤ T)
    hG hupper hL (show n < atkinsonSourceCutoff T G L by omega)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hnatural
  have hscale : G*Real.sqrt (n:ℝ) ≤ 7*Real.sqrt T*L := by
    have h := (le_div_iff₀ hG).mp (show Real.sqrt (n:ℝ) ≤ 7*Real.sqrt T*L/G by
      convert hnatural using 1; ring)
    nlinarith
  have hmajor : C*G/(L*Real.sqrt T*Real.sqrt (n:ℝ)) ≤ (7*C)/(n:ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < L*Real.sqrt T*Real.sqrt (n:ℝ)) hn0).mpr
    have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ C*Real.sqrt (n:ℝ) by positivity)
    have he := Real.sq_sqrt hn0.le
    calc
      C*G*(n:ℝ) = C*Real.sqrt (n:ℝ)*(G*Real.sqrt (n:ℝ)) := by
        linear_combination -C*G*he
      _ ≤ _ := h
      _ = _ := by ring
  obtain ⟨hp,hm⟩ := hinc T G L hT0 hG hL0 (by linarith) n hn hnsmall
  exact ⟨hp.trans hmajor,hm.trans hmajor⟩

theorem exists_norm_saddleMellin_increment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ n : ℕ, 0 < n →
      10000*((n+1:ℕ):ℝ) ≤ T →
      ‖zetaMainMellinProfile (zetaAtkinsonSaddle T (Real.sqrt ((n+1:ℕ):ℝ))/T)-
        zetaMainMellinProfile (zetaAtkinsonSaddle T (Real.sqrt (n:ℝ))/T)‖ ≤ C/(n:ℝ) ∧
      ‖zetaMainMellinProfile (zetaAtkinsonSaddle T (-Real.sqrt ((n+1:ℕ):ℝ))/T)-
        zetaMainMellinProfile (zetaAtkinsonSaddle T (-Real.sqrt (n:ℝ))/T)‖ ≤ C/(n:ℝ) := by
  obtain ⟨C,hC,hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile 0
  refine ⟨C,hC,?_⟩
  intro T hT n hn hN
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hnT : (n:ℝ) ≤ T := by
    push_cast at hN
    linarith
  have hmem0 := atkinsonRootSample_mem hT n 1 hN 0 (by norm_num)
  have hmem1 := atkinsonRootSample_mem hT n 1 hN 1 le_rfl
  have hmajor : C*((1/Real.sqrt (n:ℝ))/Real.sqrt T) ≤ C/(n:ℝ) := by
    have hroot := Real.sqrt_le_sqrt hnT
    have hprod : (n:ℝ) ≤ Real.sqrt (n:ℝ)*Real.sqrt T := by
      nlinarith [Real.sq_sqrt hn0.le,mul_nonneg (Real.sqrt_nonneg (n:ℝ))
        (sub_nonneg.mpr hroot)]
    calc
      _ = C/(Real.sqrt (n:ℝ)*Real.sqrt T) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hC.le hn0 hprod
  have hbound (b c : ℝ)
      (hx : atkinsonSaddleRoot (T/(2*Real.pi)) b/Real.sqrt T ∈ Icc (1/4) 1)
      (hy : atkinsonSaddleRoot (T/(2*Real.pi)) c/Real.sqrt T ∈ Icc (1/4) 1)
      (hd : |atkinsonSaddleRoot (T/(2*Real.pi)) b-
        atkinsonSaddleRoot (T/(2*Real.pi)) c| ≤ 1/Real.sqrt (n:ℝ)) :
      ‖zetaMainMellinProfile (zetaAtkinsonSaddle T b/T)-
        zetaMainMellinProfile (zetaAtkinsonSaddle T c/T)‖ ≤ C/(n:ℝ) := by
    rw [zetaMainMellinProfile_saddle_eq_root hT b,zetaMainMellinProfile_saddle_eq_root hT c]
    have h := hprofile.norm_sub_le hy hx
    simp only [mul_one,← sub_div,abs_div,abs_of_pos hs] at h
    apply h.trans
    apply le_trans _ hmajor
    gcongr
  constructor
  · exact hbound _ _ hmem1.1 (by simpa only [atkinsonPositiveRootSample,Nat.add_zero] using hmem0.1)
      (abs_saddleRoot_sqrt_succ_sub_le hT n hn)
  · exact hbound _ _ hmem1.2 (by simpa only [atkinsonNegativeRootSample,Nat.add_zero] using hmem0.2)
      (abs_saddleRoot_neg_sqrt_succ_sub_le hT n hn)

theorem exists_norm_saddleResidual_source_increment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → G ≤ Real.sqrt T →
      1 ≤ L → 1200*L ≤ G → ∀ n : ℕ, 0 < n → n+1 ≤ atkinsonSourceCutoff T G L →
      ‖atkinsonSaddleResidual T G L (Real.sqrt ((n+1:ℕ):ℝ))-
        atkinsonSaddleResidual T G L (Real.sqrt (n:ℝ))‖ ≤ C/(n:ℝ) ∧
      ‖atkinsonSaddleResidual T G L (-Real.sqrt ((n+1:ℕ):ℝ))-
        atkinsonSaddleResidual T G L (-Real.sqrt (n:ℝ))‖ ≤ C/(n:ℝ) := by
  obtain ⟨A,hA,hcut⟩ := exists_norm_saddleCutoff_source_increment_le
  obtain ⟨B,hB,hmel⟩ := exists_norm_saddleMellin_increment_le
  obtain ⟨D,hD,hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile 0
  refine ⟨D*A+B,by positivity,?_⟩
  intro T G L hT hG hupper hL hwidth n hn hncut
  have hT0 : 0 < T := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hN := atkinsonSourceCutoff_le_small hT hG (by linarith) hwidth
  have hnsmall : 10000*((n+1:ℕ):ℝ) ≤ T := by
    have hcast : ((n+1:ℕ):ℝ) ≤ atkinsonSourceCutoff T G L := by exact_mod_cast hncut
    linarith
  obtain ⟨hcp,hcm⟩ := hcut T G L hT hG hupper hL hwidth n hn hncut
  obtain ⟨hmp,hmm⟩ := hmel T hT0 n hn hnsmall
  have hmem := atkinsonRootSample_mem hT0 n 1 hnsmall 1 le_rfl
  have hbound (b c : ℝ)
      (hb : ‖zetaMainMellinProfile (zetaAtkinsonSaddle T b/T)‖ ≤ D)
      (hc : ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)-
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T c) : ℂ)‖ ≤ A/(n:ℝ))
      (hm : ‖zetaMainMellinProfile (zetaAtkinsonSaddle T b/T)-
        zetaMainMellinProfile (zetaAtkinsonSaddle T c/T)‖ ≤ B/(n:ℝ)) :
      ‖atkinsonSaddleResidual T G L b-atkinsonSaddleResidual T G L c‖ ≤
        (D*A+B)/(n:ℝ) := by
    have hcutone : ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T c) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      change |zetaBandCutoff _ _ _ _ _| ≤ 1
      rw [abs_of_nonneg (zetaBandCutoff_nonneg _ _ _ _ _)]
      exact zetaBandCutoff_le_one _ _ _ _ _
    unfold atkinsonSaddleResidual
    have he (p q r s : ℂ) : p*r-q*s = p*(r-s)+(p-q)*s := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    calc
      _ ≤ D*(A/(n:ℝ))+(B/(n:ℝ))*1 := add_le_add
        (mul_le_mul hb hc (norm_nonneg _) hD.le)
        (mul_le_mul hm hcutone (norm_nonneg _) (by positivity))
      _ = _ := by ring
  constructor
  · apply hbound _ _ _ hcp hmp
    rw [zetaMainMellinProfile_saddle_eq_root hT0]
    exact hprofile.norm_le _ hmem.1
  · apply hbound _ _ _ hcm hmm
    rw [zetaMainMellinProfile_saddle_eq_root hT0]
    exact hprofile.norm_le _ hmem.2

theorem abs_arsinh_sub_le (x y : ℝ) : |Real.arsinh x-Real.arsinh y| ≤ |x-y| := by
  have hd (z : ℝ) : ‖deriv Real.arsinh z‖ ≤ 1 := by
    rw [(Real.hasDerivAt_arsinh z).deriv,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hs : 1 ≤ Real.sqrt (1+z^2) := by
      have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+z^2 by nlinarith [sq_nonneg z])
      simpa only [Real.sqrt_one] using h
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => Real.differentiable_arsinh z)
    (fun z _ => hd z) (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using h

theorem arsinh_sq_sub_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    (Real.arsinh x)^2-(Real.arsinh y)^2 ≤ x^2-y^2 := by
  have hx := hy.trans hyx
  have hax : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr hx
  have hay : 0 ≤ Real.arsinh y := Real.arsinh_nonneg_iff.mpr hy
  have hmono := Real.arsinh_strictMono.monotone hyx
  have hdiff := abs_arsinh_sub_le x y
  rw [abs_of_nonneg (sub_nonneg.mpr hmono),abs_of_nonneg (sub_nonneg.mpr hyx)] at hdiff
  have h₁ := abs_arsinh_sub_le x 0
  have h₂ := abs_arsinh_sub_le y 0
  simp only [Real.arsinh_zero,sub_zero,abs_of_nonneg hax,abs_of_nonneg hx] at h₁
  simp only [Real.arsinh_zero,sub_zero,abs_of_nonneg hay,abs_of_nonneg hy] at h₂
  have h := mul_le_mul hdiff (add_le_add h₁ h₂) (by positivity : 0 ≤ Real.arsinh x+Real.arsinh y)
    (sub_nonneg.mpr hyx)
  nlinarith

theorem saddleFrequency_sq_succ_sub_le {T : ℝ} (hT : 0 < T) (n : ℕ) :
    (atkinsonSaddleFrequency T (n+1))^2-(atkinsonSaddleFrequency T n)^2 ≤ 2*Real.pi/T := by
  let x := Real.sqrt (Real.pi*((n+1:ℕ):ℝ)/(2*T))
  let y := Real.sqrt (Real.pi*(n:ℝ)/(2*T))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hyx : y ≤ x := by
    apply Real.sqrt_le_sqrt
    gcongr
    exact_mod_cast Nat.le_succ n
  have h := arsinh_sq_sub_le hy hyx
  have hx2 : x^2 = Real.pi*((n+1:ℕ):ℝ)/(2*T) := Real.sq_sqrt (by positivity)
  have hy2 : y^2 = Real.pi*(n:ℝ)/(2*T) := Real.sq_sqrt (by positivity)
  have he : x^2-y^2 = Real.pi/(2*T) := by rw [hx2,hy2]; push_cast; ring
  change (2*Real.arsinh x)^2-(2*Real.arsinh y)^2 ≤ _
  have he' : (4:ℝ)*(Real.pi/(2*T)) = 2*Real.pi/T := by ring
  nlinarith

theorem exp_neg_sub_le (a b : ℝ) :
    Real.exp (-a)-Real.exp (-b) ≤ (b-a)*Real.exp (-a) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-b)) (Real.exp_pos (-a)).le
  rw [← Real.exp_add,show -a+(a-b) = -b by ring] at h
  nlinarith

theorem norm_saddleGaussian_increment_le {T G : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hGT : G^2 ≤ 2*T) (n : ℕ) (hn : (n:ℝ) ≤ T) :
    ‖atkinsonSaddleGaussian T G (n+1)-atkinsonSaddleGaussian T G n‖ ≤
      (Real.sqrt Real.pi*Real.pi/2)*(G^3/T)*Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
  have hinc := norm_quadraticGaussian_increment_le hT hG hGT
    (atkinsonSaddleFrequency_nonneg T n) (atkinsonSaddleFrequency_monotone hT (Nat.le_succ n))
  have hsq := saddleFrequency_sq_succ_sub_le hT n
  have hexp := exp_neg_sub_le ((G*atkinsonSaddleFrequency T n)^2/8)
    ((G*atkinsonSaddleFrequency T (n+1))^2/8)
  have hgap : (G*atkinsonSaddleFrequency T (n+1))^2/8-
      (G*atkinsonSaddleFrequency T n)^2/8 ≤ Real.pi*G^2/(4*T) := by
    have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ G^2/8 by positivity)
    convert h using 1 <;> ring
  have henv := quadraticFrequencyEnvelope_saddle_le_physical hT G n hn
  change ‖atkinsonSaddleGaussian T G (n+1)-atkinsonSaddleGaussian T G n‖ ≤ _ at hinc
  apply hinc.trans
  have hmain : quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T n)-
      quadraticFrequencyEnvelope G (atkinsonSaddleFrequency T (n+1)) ≤
      (Real.pi*G^2/(4*T))*Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
    have he : Real.exp (-((G*atkinsonSaddleFrequency T n)^2/8)) ≤
        Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
      simpa only [quadraticFrequencyEnvelope,neg_div] using henv
    have h := hexp.trans (mul_le_mul hgap he (by positivity) (by positivity))
    simpa only [quadraticFrequencyEnvelope,neg_div] using h
  convert mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2*Real.sqrt Real.pi*G by positivity) using 1
  ring

theorem norm_saddleGaussian_fourWidth_le {T G : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hGT : 8*G^2 ≤ T) (n : ℕ) (hn : (n:ℝ) ≤ T) :
    ‖atkinsonSaddleGaussian T (4*G) n‖ ≤
      4*Real.sqrt Real.pi*G*Real.exp (-(G^2*(n:ℝ))/T) := by
  apply (norm_atkinsonSaddleGaussian_le_physical hT (by positivity : 0 < 4*G)
    (by nlinarith : (4*G)^2 ≤ 2*T) n hn).trans
  have he : -((4*G)^2*(n:ℝ))/(12*T) ≤ -(G^2*(n:ℝ))/T := by
    have ha : 0 ≤ G^2*(n:ℝ)/T := by positivity
    have hnorm : -((4*G)^2*(n:ℝ))/(12*T) = -(4/3:ℝ)*(G^2*(n:ℝ)/T) := by ring
    rw [hnorm,neg_div]
    linarith
  convert mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (show 0 ≤ 4*Real.sqrt Real.pi*G by positivity) using 1
  ring

theorem norm_saddleGaussian_fourWidth_increment_le {T G : ℝ} (hT : 0 < T) (hG : 0 < G)
    (hGT : 8*G^2 ≤ T) (n : ℕ) (hn : 0 < n) (hnT : (n:ℝ) ≤ T) :
    ‖atkinsonSaddleGaussian T (4*G) (n+1)-atkinsonSaddleGaussian T (4*G) n‖ ≤
      (96*Real.sqrt Real.pi*Real.pi)*(G/(n:ℝ))*Real.exp (-(G^2*(n:ℝ))/T) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  let a := G^2*(n:ℝ)/T
  have habs : a*Real.exp (-(4/3:ℝ)*a) ≤ 3*Real.exp (-a) := by
    have h := (Real.mul_exp_neg_le_exp_neg_one (a/3)).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0))
    have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 3)
    have h'' := mul_le_mul_of_nonneg_right h' (Real.exp_pos (-a)).le
    calc
      _ = (3*((a/3)*Real.exp (-(a/3))))*Real.exp (-a) := by
        rw [show -(4/3:ℝ)*a = -(a/3)+(-a) by ring,Real.exp_add]
        ring
      _ ≤ _ := h''
      _ = _ := by ring
  apply (norm_saddleGaussian_increment_le hT (by positivity : 0 < 4*G)
    (by nlinarith : (4*G)^2 ≤ 2*T) n hnT).trans
  calc
    _ = (32*Real.sqrt Real.pi*Real.pi)*(G/(n:ℝ))*(a*Real.exp (-(4/3:ℝ)*a)) := by
      dsimp [a]
      have he : -((4*G)^2*(n:ℝ))/(12*T) = -(4/3:ℝ)*(G^2*(n:ℝ)/T) := by ring
      rw [he]
      field_simp
      ring
    _ ≤ (32*Real.sqrt Real.pi*Real.pi)*(G/(n:ℝ))*(3*Real.exp (-a)) := by gcongr
    _ = _ := by simp only [a,neg_div]; ring

theorem abs_rpow_succ_sub_le {x p : ℝ} (hx : 0 < x) (hp : p ≤ 0) :
    |(x+1)^p-x^p| ≤ (-p)*x^p/x := by
  have hf (z : ℝ) (hz : z ∈ Icc x (x+1)) :
      HasDerivAt (fun w : ℝ => w^p) (p*z^(p-1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (hx.trans_le hz.1).ne')
  have hd (z : ℝ) (hz : z ∈ Icc x (x+1)) :
      ‖deriv (fun w : ℝ => w^p) z‖ ≤ (-p)*x^(p-1) := by
    rw [(hf z hz).deriv,norm_mul,Real.norm_eq_abs,abs_of_nonpos hp,
      Real.norm_of_nonneg (Real.rpow_nonneg (hx.le.trans hz.1) _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hz.1 (by linarith : p-1 ≤ 0)) (by linarith)
  have h := (convex_Icc x (x+1)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt) hd
    (show x ∈ Icc x (x+1) by constructor <;> linarith)
    (show x+1 ∈ Icc x (x+1) by constructor <;> linarith)
  simp only [Real.norm_eq_abs,show x+1-x = 1 by ring,abs_one,mul_one,
    Real.rpow_sub_one hx.ne'] at h
  convert h using 1
  ring

theorem norm_fourthRootCoefficient_increment_le {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    ‖(atkinsonFourthRootCoefficient T (n+1) : ℂ)-(atkinsonFourthRootCoefficient T n : ℂ)‖ ≤
      (((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ)))/(2*(n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  let c := 2*T/Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  let a := (n:ℝ)^(-(1/4:ℝ))
  let b := ((n:ℝ)+c)^(-(1/4:ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have haInc := abs_rpow_succ_sub_le hn0 (by norm_num : -(1/4:ℝ) ≤ 0)
  have hbInc := abs_rpow_succ_sub_le (show 0 < (n:ℝ)+c by positivity) (by norm_num : -(1/4:ℝ) ≤ 0)
  have hbMono : ((n:ℝ)+1+c)^(-(1/4:ℝ)) ≤ b :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hdiff : |((n:ℝ)+1)^(-(1/4:ℝ))*((n:ℝ)+1+c)^(-(1/4:ℝ))-a*b| ≤ a*b/(2*(n:ℝ)) := by
    have he (p q r s : ℝ) : p*r-q*s = (p-q)*r+q*(r-s) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ha,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)+1+c) _)]
    have hbInc' : |((n:ℝ)+1+c)^(-(1/4:ℝ))-b| ≤ b/(4*(n:ℝ)) := by
      have h := hbInc.trans (div_le_div_of_nonneg_left (by positivity)
        hn0 (by linarith : (n:ℝ) ≤ (n:ℝ)+c))
      rw [show (n:ℝ)+1+c = (n:ℝ)+c+1 by ring]
      convert h using 1
      dsimp [b]
      ring
    calc
      _ ≤ ((1/4:ℝ)*a/(n:ℝ))*b+a*(b/(4*(n:ℝ))) := add_le_add
        (mul_le_mul (by simpa only [neg_neg] using haInc) hbMono (by positivity) (by positivity))
        (mul_le_mul_of_nonneg_left hbInc' ha)
      _ = _ := by ring
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    atkinsonFourthRootCoefficient_eq hT,atkinsonFourthRootCoefficient_eq hT]
  push_cast
  have he : (1/Real.sqrt 2)*((n:ℝ)+1)^(-(1/4:ℝ))*((n:ℝ)+1+2*T/Real.pi)^(-(1/4:ℝ))-
      (1/Real.sqrt 2)*(n:ℝ)^(-(1/4:ℝ))*((n:ℝ)+2*T/Real.pi)^(-(1/4:ℝ)) =
      (1/Real.sqrt 2)*(((n:ℝ)+1)^(-(1/4:ℝ))*((n:ℝ)+1+c)^(-(1/4:ℝ))-a*b) := by dsimp [a,b,c]; ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt 2)]
  apply (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans
  have hcoef := atkinsonFourthRootCoefficient_le_height hT n
  rw [atkinsonFourthRootCoefficient_eq hT] at hcoef
  have h := div_le_div_of_nonneg_right hcoef (show 0 ≤ 2*(n:ℝ) by positivity)
  convert h using 1
  dsimp [a,b,c]
  ring

theorem exists_norm_mainWeights_fourWidth_increment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → 16*G^2 ≤ T →
      1 ≤ L → 1200*L ≤ 4*G → ∀ n : ℕ, 0 < n → n+1 ≤ atkinsonSourceCutoff T (4*G) L →
      ‖atkinsonPositiveMainWeight T (4*G) L (n+1)-atkinsonPositiveMainWeight T (4*G) L n‖ ≤
        C*(G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))/(n:ℝ))*Real.exp (-(G^2*(n:ℝ))/T) ∧
      ‖atkinsonNegativeMainWeight T (4*G) L (n+1)-atkinsonNegativeMainWeight T (4*G) L n‖ ≤
        C*(G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))/(n:ℝ))*Real.exp (-(G^2*(n:ℝ))/T) := by
  obtain ⟨D,hD,hres⟩ := exists_norm_atkinsonSaddleResidual_le
  obtain ⟨E,hE,hinc⟩ := exists_norm_saddleResidual_source_increment_le
  let K : ℝ := (1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*(2*Real.sqrt Real.pi*D+96*Real.sqrt Real.pi*Real.pi*D+4*Real.sqrt Real.pi*E),by positivity,?_⟩
  intro T G L hT hG hGT hL hwidth n hn hncut
  have hT0 : 0 < T := by linarith
  have hG4 : 0 < 4*G := by positivity
  have hL0 : 0 < L := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hupper : 4*G ≤ Real.sqrt T := by nlinarith [Real.sq_sqrt hT0.le,Real.sqrt_nonneg T]
  have hN := atkinsonSourceCutoff_le_small hT hG4 hL0.le hwidth
  have hnsmall : 10000*((n+1:ℕ):ℝ) ≤ T := by
    have hcast : ((n+1:ℕ):ℝ) ≤ atkinsonSourceCutoff T (4*G) L := by exact_mod_cast hncut
    linarith
  have hnT : (n:ℝ) ≤ T := by push_cast at hnsmall; linarith
  have hn1T : ((n+1:ℕ):ℝ) ≤ T := by have hn1 := Nat.cast_nonneg (α := ℝ) (n+1); linarith
  let X := T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))
  let e := Real.exp (-(G^2*(n:ℝ))/T)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hcoeff (m : ℕ) (hm : n ≤ m) : ‖(atkinsonFourthRootCoefficient T m : ℂ)‖ ≤ K*X := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (atkinsonFourthRootCoefficient_nonneg hT0 m)]
    apply (atkinsonFourthRootCoefficient_le_height hT0 m).trans
    change K*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ)) ≤ K*X
    dsimp [X]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hm) (by norm_num)
  have hcoefInc : ‖(atkinsonFourthRootCoefficient T (n+1) : ℂ)-(atkinsonFourthRootCoefficient T n : ℂ)‖ ≤
      K*X/(2*(n:ℝ)) := by convert norm_fourthRootCoefficient_increment_le hT0 n hn using 1; dsimp [K,X]; ring
  have hg0 : ‖atkinsonSaddleGaussian T (4*G) n‖ ≤ 4*Real.sqrt Real.pi*G*e :=
    norm_saddleGaussian_fourWidth_le hT0 hG (by nlinarith) n hnT
  have hg1 : ‖atkinsonSaddleGaussian T (4*G) (n+1)‖ ≤ 4*Real.sqrt Real.pi*G*e := by
    apply (norm_saddleGaussian_fourWidth_le hT0 hG (by nlinarith) (n+1) hn1T).trans
    dsimp [e]
    gcongr
    exact_mod_cast Nat.le_succ n
  have hgInc := norm_saddleGaussian_fourWidth_increment_le hT0 hG (by nlinarith) n hn hnT
  obtain ⟨hrp,hrm⟩ := hinc T (4*G) L hT hG4 hupper hL hwidth n hn hncut
  have hbound (b c : ℝ) (hrInc : ‖atkinsonSaddleResidual T (4*G) L b-
      atkinsonSaddleResidual T (4*G) L c‖ ≤ E/(n:ℝ)) :
      ‖(atkinsonFourthRootCoefficient T (n+1) : ℂ)*atkinsonSaddleGaussian T (4*G) (n+1)*
        atkinsonSaddleResidual T (4*G) L b-
        (atkinsonFourthRootCoefficient T n : ℂ)*atkinsonSaddleGaussian T (4*G) n*
        atkinsonSaddleResidual T (4*G) L c‖ ≤
          (K*(2*Real.sqrt Real.pi*D+96*Real.sqrt Real.pi*Real.pi*D+4*Real.sqrt Real.pi*E))*
            (G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))/(n:ℝ))*e := by
    have hr := hres T (4*G) L c hT0 hG4 hL0 (by linarith)
    have he (a b c d p q : ℂ) : a*c*p-b*d*q = (a-b)*d*q+a*(c-d)*q+a*c*(p-q) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul]
    calc
      _ ≤ (K*X/(2*(n:ℝ)))*(4*Real.sqrt Real.pi*G*e)*D+
          (K*X)*((96*Real.sqrt Real.pi*Real.pi)*(G/(n:ℝ))*e)*D+
          (K*X)*(4*Real.sqrt Real.pi*G*e)*(E/(n:ℝ)) := by
        gcongr <;> exact hcoeff (n+1) (Nat.le_succ n)
      _ = _ := by dsimp [X]; ring
  exact ⟨hbound _ _ hrp,hbound _ _ hrm⟩

theorem floor_step_ae (f : ℕ → ℝ) (k : ℕ) :
    (fun x : ℝ => f ⌊x⌋₊) =ᵐ[volume.restrict (uIoc (k:ℝ) ((k+1:ℕ):ℝ))] fun _ => f k := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (volume.ae_ne ((k+1:ℕ):ℝ))] with x hx hne
  rw [uIoc_of_le (by exact_mod_cast Nat.le_succ k)] at hx
  have hfloor : ⌊x⌋₊ = k := Nat.floor_eq_on_Ico k x ⟨hx.1.le,by
    have hlt := lt_of_le_of_ne hx.2 hne
    simpa only [Nat.cast_add,Nat.cast_one] using hlt⟩
  exact congrArg f hfloor

theorem integral_floor_step_unit (f : ℕ → ℝ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => f ⌊x⌋₊) volume (k:ℝ) ((k+1:ℕ):ℝ) ∧
      (∫ x in (k:ℝ)..((k+1:ℕ):ℝ), f ⌊x⌋₊) = f k := by
  have he := floor_step_ae f k
  refine ⟨(intervalIntegrable_const (c := f k)).congr_ae he.symm,?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict he,intervalIntegral.integral_const]
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_smul]

theorem integral_floor_step_nat (f : ℕ → ℝ) (N : ℕ) :
    (∫ x in (0:ℝ)..(N:ℝ), f ⌊x⌋₊) = ∑ k ∈ Finset.range N, f k := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ => (n:ℝ))
    (n := N) (fun k _ => (integral_floor_step_unit f k).1)
  simp only [Nat.cast_zero,(integral_floor_step_unit f _).2] at h
  exact h.symm

theorem norm_sum_mul_le_endpoint_integral (w a : ℕ → ℂ) (N : ℕ) {B D : ℝ}
    (hw : ‖w (N-1)‖ ≤ B) (hd : ∀ i < N-1, ‖w (i+1)-w i‖ ≤ D) :
    ‖∑ i ∈ Finset.range N, w i*a i‖ ≤ B*‖∑ i ∈ Finset.range N, a i‖+
      D*(∫ x in (0:ℝ)..(N:ℝ), ‖∑ i ∈ Finset.range ⌊x⌋₊, a i‖) := by
  rw [integral_floor_step_nat (fun k => ‖∑ i ∈ Finset.range k, a i‖) N]
  have hsum : (∑ i ∈ Finset.range (N-1), ‖∑ j ∈ Finset.range (i+1), a j‖) =
      ∑ i ∈ Finset.range N, ‖∑ j ∈ Finset.range i, a j‖ := by
    cases N with
    | zero => simp
    | succ N =>
      rw [show N.succ-1 = N by omega,Finset.sum_range_succ']
      simp only [Finset.sum_range_zero,norm_zero,add_zero]
  apply (norm_sum_mul_le_discrete_parts w a N).trans
  apply add_le_add (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  calc
    _ ≤ ∑ i ∈ Finset.range (N-1), D*‖∑ j ∈ Finset.range (i+1), a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hd i (Finset.mem_range.mp hi)) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum,hsum]

def printedAtkinsonPhase (T : ℝ) (n : ℕ) : ℝ :=
  2*T*Real.arsinh (Real.sqrt (Real.pi*(n:ℝ)/(2*T)))+
    Real.sqrt (2*Real.pi*(n:ℝ)*T+Real.pi^2*(n:ℝ)^2)

def printedAtkinsonPrefix (T : ℝ) (K : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc K ⌊(K:ℝ)+x⌋₊,
    divisorWeight n*(-1:ℂ)^n*Complex.exp ((printedAtkinsonPhase T n : ℂ)*I)

theorem printedAtkinsonPhase_eq (T : ℝ) (n : ℕ) :
    printedAtkinsonPhase T n = atkinsonSourcePhase T n+Real.pi/4 := by
  unfold printedAtkinsonPhase atkinsonSourcePhase
  ring

theorem sum_Ioc_nat_eq_range (f : ℕ → ℂ) (K N : ℕ) :
    (∑ n ∈ Finset.Ioc K (K+N), f n) = ∑ i ∈ Finset.range N, f (K+1+i) := by
  have hs : Finset.Ioc K (K+N) = Finset.Ico (K+1) (K+N+1) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [hs,Finset.sum_Ico_eq_sum_range,show K+N+1-(K+1) = N by omega]

theorem norm_printedAtkinsonPrefix (T : ℝ) (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖printedAtkinsonPrefix T K x‖ =
      ‖∑ i ∈ Finset.range ⌊x⌋₊, atkinsonPositivePhaseTerm T (K+1+i)‖ := by
  have he (n : ℕ) : divisorWeight n*(-1:ℂ)^n*Complex.exp ((printedAtkinsonPhase T n : ℂ)*I) =
      atkinsonPositivePhaseTerm T n*Complex.exp (((Real.pi/4:ℝ):ℂ)*I) := by
    rw [printedAtkinsonPhase_eq,Complex.ofReal_add,add_mul,Complex.exp_add]
    unfold atkinsonPositivePhaseTerm
    ring
  have hfloor : ⌊(K:ℝ)+x⌋₊ = K+⌊x⌋₊ := by
    rw [add_comm,Nat.floor_add_natCast hx,Nat.add_comm]
  unfold printedAtkinsonPrefix
  rw [hfloor,sum_Ioc_nat_eq_range]
  simp_rw [he]
  rw [← Finset.sum_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

def printedBlockScale (T G : ℝ) (K : ℕ) : ℝ :=
  G*T^(-(1/4:ℝ))*(K:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(K:ℝ))/T)

theorem exists_mainWeights_fourWidth_block_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → 16*G^2 ≤ T →
      1 ≤ L → 1200*L ≤ 4*G → ∀ K : ℕ, 0 < K → 2*K ≤ atkinsonSourceCutoff T (4*G) L →
      (∀ n : ℕ, K ≤ n → n ≤ 2*K →
        ‖atkinsonPositiveMainWeight T (4*G) L n‖ ≤ C*printedBlockScale T G K ∧
        ‖atkinsonNegativeMainWeight T (4*G) L n‖ ≤ C*printedBlockScale T G K) ∧
      (∀ n : ℕ, K ≤ n → n+1 ≤ 2*K →
        ‖atkinsonPositiveMainWeight T (4*G) L (n+1)-atkinsonPositiveMainWeight T (4*G) L n‖ ≤
          C*printedBlockScale T G K/(K:ℝ) ∧
        ‖atkinsonNegativeMainWeight T (4*G) L (n+1)-atkinsonNegativeMainWeight T (4*G) L n‖ ≤
          C*printedBlockScale T G K/(K:ℝ)) := by
  obtain ⟨A,hA,hsize⟩ := exists_norm_atkinsonMainWeights_le
  obtain ⟨B,hB,hinc⟩ := exists_norm_mainWeights_fourWidth_increment_le
  let C := max (4*A) B
  have hC : 0 < C := hB.trans_le (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro T G L hT hG hGT hL hwidth K hK hcut
  have hT0 : 0 < T := by linarith
  have hG4 : 0 < 4*G := by positivity
  have hL0 : 0 < L := by linarith
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hN := atkinsonSourceCutoff_le_small hT hG4 hL0.le hwidth
  have hKT : 10000*((2*K:ℕ):ℝ) ≤ T := by
    have hh : ((2*K:ℕ):ℝ) ≤ atkinsonSourceCutoff T (4*G) L := by exact_mod_cast hcut
    linarith
  have hmon (n : ℕ) (hKn : K ≤ n) :
      printedBlockScale T G n ≤ printedBlockScale T G K := by
    have hKnR : (K:ℝ) ≤ n := by exact_mod_cast hKn
    unfold printedBlockScale
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hK0 hKnR (by norm_num : -(1/4:ℝ) ≤ 0))
      (by positivity)) _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    gcongr
  constructor
  · intro n hKn hnK
    have hnT : (n:ℝ) ≤ T := by
      have hh : (n:ℝ) ≤ (2*K:ℕ) := by exact_mod_cast hnK
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    obtain ⟨hp,hm⟩ := hsize T (4*G) L hT0 hG4 (by nlinarith) hL0 (by linarith) n hnT
    have he : -((4*G)^2*(n:ℝ))/(12*T) ≤ -(G^2*(n:ℝ))/T := by
      have ha : 0 ≤ G^2*(n:ℝ)/T := by positivity
      have heq : -((4*G)^2*(n:ℝ))/(12*T) = -(4/3:ℝ)*(G^2*(n:ℝ)/T) := by ring
      rw [heq,neg_div]
      linarith
    have hmajor : A*(4*G)*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*Real.exp (-((4*G)^2*(n:ℝ))/(12*T)) ≤
        C*printedBlockScale T G K := by
      calc
        _ ≤ (4*A)*printedBlockScale T G n := by
          unfold printedBlockScale
          have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
            (show 0 ≤ (4*A)*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ)) by positivity)
          convert hh using 1 <;> ring
        _ ≤ C*printedBlockScale T G K := mul_le_mul (le_max_left _ _) (hmon n hKn)
          (by unfold printedBlockScale; positivity) hC.le
    exact ⟨hp.trans hmajor,hm.trans hmajor⟩
  · intro n hKn hnK
    obtain ⟨hp,hm⟩ := hinc T G L hT hG hGT hL hwidth n (hK.trans_le hKn) (hnK.trans hcut)
    have hKnR : (K:ℝ) ≤ n := by exact_mod_cast hKn
    have hmajor : B*(G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))/(n:ℝ))*Real.exp (-(G^2*(n:ℝ))/T) ≤
        C*printedBlockScale T G K/(K:ℝ) := by
      calc
        _ = B*printedBlockScale T G n/(n:ℝ) := by unfold printedBlockScale; ring
        _ ≤ C*printedBlockScale T G K/(K:ℝ) := by
          apply div_le_div₀ (by unfold printedBlockScale; positivity)
            (mul_le_mul (le_max_right _ _) (hmon n hKn) (by unfold printedBlockScale; positivity) hC.le) hK0 hKnR
    exact ⟨hp.trans hmajor,hm.trans hmajor⟩

theorem exists_stationary_printed_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → 16*G^2 ≤ T →
      1 ≤ L → 1200*L ≤ 4*G → ∀ K : ℕ, 0 < K → 2*K ≤ atkinsonSourceCutoff T (4*G) L →
      ‖∑ n ∈ Finset.Ioc K (2*K), atkinsonStationaryLeadingTerm T (4*G) L n‖ ≤
        C*printedBlockScale T G K*(‖printedAtkinsonPrefix T K (K:ℝ)‖+
          (1/(K:ℝ))*(∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖)) := by
  obtain ⟨C,hC,hweights⟩ := exists_mainWeights_fourWidth_block_bounds
  refine ⟨4*C,by positivity,?_⟩
  intro T G L hT hG hGT hL hwidth K hK hcut
  have hT0 : 0 < T := by linarith
  obtain ⟨hw,hd⟩ := hweights T G L hT hG hGT hL hwidth K hK hcut
  have hp := norm_sum_mul_le_endpoint_integral
    (fun i => atkinsonPositiveMainWeight T (4*G) L (K+1+i))
    (fun i => atkinsonPositivePhaseTerm T (K+1+i)) K
    (hw (K+1+(K-1)) (by omega) (by omega)).1
    (by
      intro i hi
      have h := (hd (K+1+i) (by omega) (by omega)).1
      simpa only [Nat.add_assoc] using h)
  have hm := norm_sum_mul_le_endpoint_integral
    (fun i => atkinsonNegativeMainWeight T (4*G) L (K+1+i))
    (fun i => atkinsonNegativePhaseTerm T (K+1+i)) K
    (hw (K+1+(K-1)) (by omega) (by omega)).2
    (by
      intro i hi
      have h := (hd (K+1+i) (by omega) (by omega)).2
      simpa only [Nat.add_assoc] using h)
  have hneg (N : ℕ) : ‖∑ i ∈ Finset.range N, atkinsonNegativePhaseTerm T (K+1+i)‖ =
      ‖∑ i ∈ Finset.range N, atkinsonPositivePhaseTerm T (K+1+i)‖ := by
    simp only [atkinsonNegativePhaseTerm_eq_conj,← map_sum,Complex.norm_conj]
  simp only [hneg] at hm
  have hend : ‖printedAtkinsonPrefix T K (K:ℝ)‖ =
      ‖∑ i ∈ Finset.range K, atkinsonPositivePhaseTerm T (K+1+i)‖ := by
    simpa only [Nat.floor_natCast] using norm_printedAtkinsonPrefix T K (Nat.cast_nonneg K)
  have hint : (∫ x in (0:ℝ)..(K:ℝ), ‖∑ i ∈ Finset.range ⌊x⌋₊, atkinsonPositivePhaseTerm T (K+1+i)‖) =
      ∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (Nat.cast_nonneg K)] at hx
    exact (norm_printedAtkinsonPrefix T K hx.1).symm
  rw [hint,← hend] at hp hm
  rw [show 2*K = K+K by omega,sum_Ioc_nat_eq_range]
  simp_rw [atkinsonStationaryLeadingTerm_eq_signed hT0 (by positivity : 4*G ≠ 0) L]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,norm_mul]
  apply (mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hp hm) (by norm_num : (0:ℝ) ≤ 2)).trans_eq
  ring

theorem sum_divisorCard_le_log (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)) ≤ (N:ℝ)*(1+Real.log N) := by
  have hid := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N
  simp only [ArithmeticFunction.sigma_zero_apply] at hid
  have hidR : (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)) =
      ∑ n ∈ Finset.Ioc 0 N, ((N/n:ℕ):ℝ) := by
    exact_mod_cast hid
  rw [hidR]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (N:ℝ)/(n:ℝ) :=
      Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = (N:ℝ)*(harmonic N:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      have he : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
      simp only [he,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum,div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg N)

theorem sum_mul_le_of_prefix_le (a w : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    (hp : ∀ n ≤ N, (∑ i ∈ Finset.range n, a i) ≤ C*(n:ℝ)) :
    (∑ i ∈ Finset.range N, w i*a i) ≤ C*∑ i ∈ Finset.range N, w i := by
  have ha := Finset.sum_range_by_parts w a N
  have hb := Finset.sum_range_by_parts w (fun _ => C) N
  simp only [smul_eq_mul] at ha hb
  rw [ha]
  have hbase : (∑ i ∈ Finset.range N, w i*C) = C*∑ i ∈ Finset.range N, w i := by
    rw [← Finset.sum_mul,mul_comm]
  rw [← hbase,hb]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hp N le_rfl) (hw _)
  · apply Finset.sum_le_sum
    intro i hi
    have hiN : i+1 ≤ N := by have := Finset.mem_range.mp hi; omega
    exact mul_le_mul_of_nonpos_left (by simpa only [mul_comm] using hp (i+1) hiN)
      (sub_nonpos.mpr (hanti (Nat.le_succ i)))

theorem sum_shift_quarter_rpow_le (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) ≤
      (4/3:ℝ)*((N+1:ℕ):ℝ)^(3/4:ℝ) := by
  have hanti : AntitoneOn (fun x : ℝ => x^(-(1/4:ℝ))) (Icc 1 (1+(N:ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(1/4:ℝ) ≤ 0)).mono
      (fun _ hx => lt_of_lt_of_le (by norm_num) hx.1)
  have hi := hanti.sum_le_integral
  have hs : (∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) ≤
      1+∑ i ∈ Finset.range N, (1+((i+1:ℕ):ℝ))^(-(1/4:ℝ)) := by
    have h := Finset.sum_range_succ (fun i : ℕ => ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) N
    have h' := Finset.sum_range_succ' (fun i : ℕ => ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) N
    have he : (∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-(1/4:ℝ)))+
        ((N+1:ℕ):ℝ)^(-(1/4:ℝ)) =
        1+∑ i ∈ Finset.range N, (1+((i+1:ℕ):ℝ))^(-(1/4:ℝ)) := by
      rw [← h,h']
      simp only [Nat.cast_add,Nat.cast_one,zero_add,Real.one_rpow]
      simp only [add_comm]
    linarith [Real.rpow_nonneg (Nat.cast_nonneg (N+1)) (-(1/4:ℝ))]
  apply (hs.trans (add_le_add_right hi 1)).trans
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/4:ℝ)))]
  norm_num only [show -(1/4:ℝ)+1 = 3/4 by norm_num,Real.one_rpow,Nat.cast_add,Nat.cast_one]
  rw [add_comm (N:ℝ) 1]
  linarith

theorem sum_Ioc_real_eq_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, f n) = ∑ i ∈ Finset.range N, f (i+1) := by
  have he : Finset.Ioc 0 N = Finset.Ico 1 (N+1) := by ext n; simp; omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.add_comm 1]

theorem sum_divisorCard_quarter_le_log (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ))) ≤
      (4/3:ℝ)*((N+1:ℕ):ℝ)^(3/4:ℝ)*(1+Real.log N) := by
  by_cases hN : N = 0
  · norm_num [hN]
  have hlog : 0 ≤ 1+Real.log (N:ℝ) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
    linarith
  have hanti : Antitone (fun i : ℕ => ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) := by
    intro i j hij
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1) (by norm_num)
  have hp (n : ℕ) (hn : n ≤ N) :
      (∑ i ∈ Finset.range n, ((i+1).divisors.card:ℝ)) ≤ (1+Real.log N)*(n:ℝ) := by
    rw [← sum_Ioc_real_eq_range (fun i => (i.divisors.card:ℝ)) n]
    by_cases hn0 : n = 0
    · simp [hn0]
    apply (sum_divisorCard_le_log n).trans
    have hlogn := Real.log_le_log (show (0:ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn0)
      (show (n:ℝ) ≤ N by exact_mod_cast hn)
    nlinarith [mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg (α := ℝ) n)]
  rw [sum_Ioc_real_eq_range]
  have hb := sum_mul_le_of_prefix_le (fun i => ((i+1).divisors.card:ℝ))
    (fun i => ((i+1:ℕ):ℝ)^(-(1/4:ℝ))) N (1+Real.log N) (fun _ => by positivity) hanti hp
  simp only [mul_comm] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right (sum_shift_quarter_rpow_le N) hlog
  convert hh using 1
  ring

theorem sum_divisorCard_quarter_le_three (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ))) ≤
      3*(N:ℝ)^(3/4:ℝ)*(1+Real.log N) := by
  by_cases hN : N = 0
  · simp [hN]
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hp : ((N+1:ℕ):ℝ)^(3/4:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ) := by
    calc
      _ ≤ (2*(N:ℝ))^(3/4:ℝ) := Real.rpow_le_rpow (by positivity)
        (by push_cast; linarith) (by norm_num)
      _ = (2:ℝ)^(3/4:ℝ)*(N:ℝ)^(3/4:ℝ) := Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)
      _ ≤ 2*(N:ℝ)^(3/4:ℝ) := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (by norm_num : (3/4:ℝ) ≤ 1)).trans_eq (Real.rpow_one 2)
  have hl : 0 ≤ 1+Real.log (N:ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0:ℝ) ≤ 4/3)) hl
  apply (sum_divisorCard_quarter_le_log N).trans
  nlinarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) (3/4:ℝ)) hl]

theorem exists_stationaryTerm_norm_le_divisor :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T →
      0 < L → 8*L ≤ G → ∀ n : ℕ, (n:ℝ) ≤ T →
      ‖atkinsonStationaryLeadingTerm T G L n‖ ≤
        C*G*T^(-(1/4:ℝ))*(n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ)) := by
  obtain ⟨A,hA,hw⟩ := exists_norm_atkinsonMainWeights_le
  refine ⟨4*A,by positivity,?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  obtain ⟨hp,hm⟩ := hw T G L hT hG hGT hL hwidth n hn
  have he : Real.exp (-(G^2*(n:ℝ))/(12*T)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (by positivity))
  have hb : A*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(n:ℝ))/(12*T)) ≤
      A*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ)) := mul_le_of_le_one_right (by positivity) he
  have hphase : ‖atkinsonPositivePhaseTerm T n‖ = (n.divisors.card:ℝ) ∧
      ‖atkinsonNegativePhaseTerm T n‖ = (n.divisors.card:ℝ) := by
    rw [atkinsonNegativePhaseTerm_eq_conj,Complex.norm_conj]
    have hp : ‖atkinsonPositivePhaseTerm T n‖ = (n.divisors.card:ℝ) := by
      simp [atkinsonPositivePhaseTerm,divisorWeight,Complex.norm_exp_ofReal_mul_I]
    exact ⟨hp,hp⟩
  rw [atkinsonStationaryLeadingTerm_eq_signed hT hG.ne' L,norm_mul]
  apply (mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans
  simp only [norm_mul,hphase.1,hphase.2]
  have hh := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right (hp.trans hb) (Nat.cast_nonneg n.divisors.card))
    (mul_le_mul_of_nonneg_right (hm.trans hb) (Nat.cast_nonneg n.divisors.card)))
    (by norm_num : (0:ℝ) ≤ 2)
  convert hh using 1
  ring

theorem exists_stationarySmallPrefix_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 4 ≤ T → 1 ≤ Real.log T →
      0 < G → G^2 ≤ 2*T → 0 < L → 8*L ≤ G →
      ∀ N : ℕ, (N:ℝ) ≤ 2*T^(1/3:ℝ) →
      ‖∑ n ∈ Finset.Ioc 0 N, atkinsonStationaryLeadingTerm T G L n‖ ≤ C*G*Real.log T := by
  obtain ⟨A,hA,hterm⟩ := exists_stationaryTerm_norm_le_divisor
  refine ⟨12*A,by positivity,?_⟩
  intro T G L hT hlog hG hGT hL hwidth N hN
  have hT0 : 0 < T := by linarith
  have hpow : 2*T^(1/3:ℝ) ≤ T := by
    have hp : T^(1/3:ℝ) ≤ Real.sqrt T := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hs := Real.sqrt_le_sqrt hT
    norm_num at hs
    nlinarith [Real.sq_sqrt hT0.le]
  have hsum := (norm_sum_le (Finset.Ioc 0 N) _).trans (Finset.sum_le_sum (fun n hn =>
    hterm T G L hT0 hG hGT hL hwidth n
      ((show (n:ℝ) ≤ N by exact_mod_cast (Finset.mem_Ioc.mp hn).2).trans (hN.trans hpow))))
  have he : (∑ n ∈ Finset.Ioc 0 N, A*G*T^(-(1/4:ℝ))*(n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ))) =
      A*G*T^(-(1/4:ℝ))*∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he] at hsum
  apply (hsum.trans (mul_le_mul_of_nonneg_left (sum_divisorCard_quarter_le_three N) (by positivity))).trans
  have hp : (N:ℝ)^(3/4:ℝ) ≤ 2*T^(1/4:ℝ) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg N) hN (by norm_num : (0:ℝ) ≤ 3/4)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),← Real.rpow_mul hT0.le] at h
    norm_num only [show (1/3:ℝ)*(3/4) = 1/4 by norm_num] at h
    have htwo : (2:ℝ)^(3/4:ℝ) ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (3/4:ℝ) ≤ 1)).trans_eq (Real.rpow_one 2)
    exact h.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
  have hl : 1+Real.log (N:ℝ) ≤ 2*Real.log T := by
    by_cases hN0 : N = 0
    · simp only [hN0,Nat.cast_zero,Real.log_zero,add_zero]
      linarith
    · have h := Real.log_le_log (show (0:ℝ) < N by exact_mod_cast Nat.pos_of_ne_zero hN0) (hN.trans hpow)
      linarith
  have hbound := mul_le_mul_of_nonneg_left (mul_le_mul
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 3)) hl (by positivity) (by positivity))
    (show 0 ≤ A*G*T^(-(1/4:ℝ)) by positivity)
  apply hbound.trans_eq
  have hcancel : T^(-(1/4:ℝ))*T^(1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hT0]
    norm_num
  calc
    _ = (12*A)*G*Real.log T*(T^(-(1/4:ℝ))*T^(1/4:ℝ)) := by ring
    _ = _ := by rw [hcancel,mul_one]

theorem sum_Ioc_pow_two_dyadic {α : Type*} [AddCommMonoid α] (f : ℕ → α) (J : ℕ) :
    (∑ n ∈ Finset.Ioc 0 (2^J), f n) =
      f 1+∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2*2^j), f n := by
  induction J with
  | zero =>
    have he : Finset.Ioc 0 1 = ({1}:Finset ℕ) := by
      ext n
      simp only [Finset.mem_Ioc,Finset.mem_singleton]
      omega
    simp [he]
  | succ J ih =>
    have hle : (2:ℕ)^J ≤ 2*2^J := by omega
    have hu := Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le (2^J)) hle
    rw [pow_succ,show (2:ℕ)^J*2 = 2*2^J by omega,← hu,
      Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),ih,Finset.sum_range_succ]
    simp only [add_assoc]

theorem pow_clog_two_le_double {N : ℕ} (hN : 0 < N) : (2:ℕ)^(Nat.clog 2 N) ≤ 2*N := by
  by_cases h1 : N ≤ 1
  · have he : N = 1 := by omega
    simp [he]
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2:ℕ)) (show 1 < N by omega)
  have hc := Nat.clog_pos (by norm_num : 1 < (2:ℕ)) (show 1 < N by omega)
  have he : Nat.clog 2 N = (Nat.clog 2 N).pred+1 := (Nat.succ_pred_eq_of_pos hc).symm
  rw [he,pow_succ]
  omega

theorem ceil_support_dyadic_le_cutoff {a : ℝ} (ha : 1 ≤ a) :
    (2:ℕ)^(Nat.clog 2 ⌈a⌉₊) ≤ ⌈4*a⌉₊ := by
  have hc := Nat.le_ceil a
  have hc1 : 0 < ⌈a⌉₊ := by
    by_contra hh
    have hz : ⌈a⌉₊ = 0 := by omega
    simp only [hz,Nat.cast_zero] at hc
    linarith
  have hp := pow_clog_two_le_double hc1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
  have hb := Nat.le_ceil (4*a)
  have hR : ((2^Nat.clog 2 ⌈a⌉₊:ℕ):ℝ) ≤ (⌈4*a⌉₊:ℝ) := by
    have hpR : ((2^Nat.clog 2 ⌈a⌉₊:ℕ):ℝ) ≤ 2*(⌈a⌉₊:ℝ) := by exact_mod_cast hp
    linarith
  exact_mod_cast hR

theorem stationaryTerm_eq_zero_of_support {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G)
    {n : ℕ} (hn : 9*T*(L/G)^2 < (n:ℝ)) :
    atkinsonStationaryLeadingTerm T G L n = 0 := by
  obtain ⟨hp,hm⟩ := atkinsonStationaryMain_pair_eq_zero_of_index hT hG hL hwidth (1/4) n hn
  simp only [atkinsonStationaryLeadingTerm,atkinsonStationaryLeadingIntegral,hp,hm,
    mul_zero,add_zero]

theorem stationarySum_eq_dyadic_support {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    atkinsonStationaryLeadingSum T G L = atkinsonStationaryLeadingTerm T G L 1+
      ∑ j ∈ Finset.range (Nat.clog 2 ⌈9*T*(L/G)^2⌉₊),
        ∑ n ∈ Finset.Ioc (2^j) (2*2^j), atkinsonStationaryLeadingTerm T G L n := by
  let J := Nat.clog 2 ⌈9*T*(L/G)^2⌉₊
  have hsum : HasSum (atkinsonStationaryLeadingTerm T G L)
      (∑ n ∈ Finset.Ioc 0 (2^J), atkinsonStationaryLeadingTerm T G L n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    by_cases hn0 : n = 0
    · simpa only [hn0] using atkinsonStationaryLeadingTerm_zero T G L
    have hnR : ((2^J:ℕ):ℝ) < n := by
      have hh : 2^J < n := Nat.lt_of_not_ge (fun hh => hn
        (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,hh⟩))
      exact_mod_cast hh
    have hceil : (⌈9*T*(L/G)^2⌉₊:ℝ) ≤ ((2^J:ℕ):ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) ⌈9*T*(L/G)^(2:ℕ)⌉₊
    exact stationaryTerm_eq_zero_of_support hT hG hL hwidth
      ((Nat.le_ceil _).trans_lt (hceil.trans_lt hnR))
  exact hsum.tsum_eq.trans (sum_Ioc_pow_two_dyadic _ J)

theorem stationarySupport_dyadic_le_cutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G^2 ≤ T) (hL : 1 ≤ L) :
    (2:ℕ)^Nat.clog 2 ⌈9*T*(L/G)^2⌉₊ ≤ atkinsonSourceCutoff T G L := by
  have hLsq : 1 ≤ L^2 := by nlinarith
  have hbase : 1 ≤ 9*T*(L/G)^2 := by
    rw [div_pow,← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hG)).mpr
    have hh := mul_le_mul_of_nonneg_left hLsq hT.le
    nlinarith
  have h := ceil_support_dyadic_le_cutoff hbase
  unfold atkinsonSourceCutoff
  convert h using 1
  congr 1
  ring

def printedAtkinsonBlockBound (T G : ℝ) (K : ℕ) : ℝ :=
  printedBlockScale T G K*(‖printedAtkinsonPrefix T K (K:ℝ)‖+
    (1/(K:ℝ))*(∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖))

theorem printedAtkinsonBlockBound_nonneg {T G : ℝ} (hT : 0 ≤ T) (hG : 0 ≤ G) (K : ℕ) :
    0 ≤ printedAtkinsonBlockBound T G K := by
  have hi : 0 ≤ ∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖ :=
    intervalIntegral.integral_nonneg (Nat.cast_nonneg K) (fun _ _ => norm_nonneg _)
  unfold printedAtkinsonBlockBound printedBlockScale
  positivity

theorem exists_stationarySum_le_printed_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 1 ≤ Real.log T →
      0 < G → 16*G^2 ≤ T → 1 ≤ L → 1200*L ≤ 4*G →
      ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤ C*(G*Real.log T+
        ∑ j ∈ Finset.range (Nat.clog 2 ⌈9*T*(L/(4*G))^2⌉₊),
          printedAtkinsonBlockBound T G (2^j)) := by
  obtain ⟨A,hA,hsmall⟩ := exists_stationarySmallPrefix_le_log
  obtain ⟨B,hB,hblock⟩ := exists_stationary_printed_block_bound
  let C := max (4*A) B
  have hC : 0 < C := hB.trans_le (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro T G L hT hlog hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  have hG4 : 0 < 4*G := by positivity
  have hL0 : 0 < L := by linarith
  have hGT4 : (4*G)^2 ≤ T := by nlinarith
  have hwidth4 : 8*L ≤ 4*G := by linarith
  let J := Nat.clog 2 ⌈9*T*(L/(4*G))^2⌉₊
  have hs := hsmall T (4*G) L (by linarith) hlog hG4 (by linarith) hL0 hwidth4 1
    (by have h := Real.one_le_rpow (by linarith : 1 ≤ T) (by norm_num : (0:ℝ) ≤ 1/3)
        norm_num only [Nat.cast_one]; linarith)
  have he : Finset.Ioc 0 1 = ({1}:Finset ℕ) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_singleton]
    omega
  simp only [he,Finset.sum_singleton] at hs
  have hsC : ‖atkinsonStationaryLeadingTerm T (4*G) L 1‖ ≤ C*(G*Real.log T) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (4*A) B) (show 0 ≤ G*Real.log T by positivity)
    nlinarith
  have hcut := stationarySupport_dyadic_le_cutoff hT0 hG4 hGT4 hL
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      ‖∑ n ∈ Finset.Ioc (2^j) (2*2^j), atkinsonStationaryLeadingTerm T (4*G) L n‖ ≤
        C*printedAtkinsonBlockBound T G (2^j) := by
    have hp : (2:ℕ)*2^j ≤ 2^J := by
      rw [mul_comm,← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hj)
    apply (hblock T G L hT hG hGT hL hwidth (2^j) (pow_pos (by norm_num) _) (hp.trans hcut)).trans
    rw [mul_assoc]
    change B*printedAtkinsonBlockBound T G (2^j) ≤ C*printedAtkinsonBlockBound T G (2^j)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (printedAtkinsonBlockBound_nonneg hT0.le hG.le _)
  rw [stationarySum_eq_dyadic_support hT0 hG4 hL0 hwidth4]
  apply (norm_add_le _ _).trans
  apply (add_le_add hsC ((norm_sum_le _ _).trans (Finset.sum_le_sum hb))).trans_eq
  rw [← Finset.mul_sum,← mul_add]

theorem pow_clog_ceil_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ ((2^Nat.clog 2 ⌈x⌉₊:ℕ):ℝ) ∧ ((2^Nat.clog 2 ⌈x⌉₊:ℕ):ℝ) ≤ 2*x := by
  have hl : (⌈x⌉₊:ℝ) ≤ ((2^Nat.clog 2 ⌈x⌉₊:ℕ):ℝ) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) ⌈x⌉₊
  refine ⟨(Nat.le_ceil _).trans hl,?_⟩
  by_cases hc : ⌈x⌉₊ ≤ 1
  · have hx1 : x ≤ 1 := by simpa only [Nat.cast_one] using Nat.ceil_le.mp hc
    have he : x = 1 := le_antisymm hx1 hx
    norm_num [he]
  have hc1 : 1 < ⌈x⌉₊ := by omega
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2:ℕ)) hc1
  have hpR : (((2:ℕ)^(Nat.clog 2 ⌈x⌉₊).pred:ℕ):ℝ) < x := Nat.lt_ceil.mp hp
  have he : Nat.clog 2 ⌈x⌉₊ = (Nat.clog 2 ⌈x⌉₊).pred+1 :=
    (Nat.succ_pred_eq_of_pos (Nat.clog_pos (by norm_num) hc1)).symm
  rw [he,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
  linarith

theorem sum_Ioc_pow_two_split {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    {M J : ℕ} (hMJ : M ≤ J) :
    (∑ n ∈ Finset.Ioc 0 (2^J), f n) =
      (∑ n ∈ Finset.Ioc 0 (2^M), f n)+
        ∑ j ∈ Finset.Ico M J, ∑ n ∈ Finset.Ioc (2^j) (2*2^j), f n := by
  have hs := Finset.sum_Ico_consecutive (fun j => ∑ n ∈ Finset.Ioc (2^j) (2*2^j), f n)
    (Nat.zero_le M) hMJ
  simp only [Nat.Ico_zero_eq_range] at hs
  rw [sum_Ioc_pow_two_dyadic,sum_Ioc_pow_two_dyadic,← hs,add_assoc]

theorem exists_stationarySum_le_largePrinted_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 1 ≤ Real.log T →
      0 < G → 16*G^2 ≤ T → 1 ≤ L → 1200*L ≤ 4*G →
      ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤ C*(G*Real.log T+
        ∑ j ∈ (Finset.range (Nat.clog 2 ⌈9*T*(L/(4*G))^2⌉₊)).filter
          (fun j => T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ)), printedAtkinsonBlockBound T G (2^j)) := by
  obtain ⟨A,hA,hsmall⟩ := exists_stationarySmallPrefix_le_log
  obtain ⟨B,hB,hblock⟩ := exists_stationary_printed_block_bound
  let C := max (4*A) B
  have hC : 0 < C := hB.trans_le (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro T G L hT hlog hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  have hG4 : 0 < 4*G := by positivity
  have hL0 : 0 < L := by linarith
  have hGT4 : (4*G)^2 ≤ T := by nlinarith
  have hwidth4 : 8*L ≤ 4*G := by linarith
  let J := Nat.clog 2 ⌈9*T*(L/(4*G))^2⌉₊
  let J₀ := Nat.clog 2 ⌈T^(1/3:ℝ)⌉₊
  let M := min J₀ J
  have hMJ : M ≤ J := min_le_right _ _
  have hMJ0 : M ≤ J₀ := min_le_left _ _
  have hpM : ((2^M:ℕ):ℝ) ≤ 2*T^(1/3:ℝ) := by
    have hh : ((2^M:ℕ):ℝ) ≤ ((2^J₀:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hMJ0
    exact hh.trans (pow_clog_ceil_bounds (Real.one_le_rpow (by linarith : 1 ≤ T)
      (by norm_num : (0:ℝ) ≤ 1/3))).2
  have hs := hsmall T (4*G) L (by linarith) hlog hG4 (by linarith) hL0 hwidth4 (2^M) hpM
  have hsC : ‖∑ n ∈ Finset.Ioc 0 (2^M), atkinsonStationaryLeadingTerm T (4*G) L n‖ ≤
      C*(G*Real.log T) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (4*A) B) (show 0 ≤ G*Real.log T by positivity)
    nlinarith
  have hfilter : (Finset.range J).filter (fun j => T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ)) = Finset.Ico M J := by
    ext j
    have he : T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ) ↔ J₀ ≤ j := by
      rw [← Nat.ceil_le]
      exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2:ℕ))).symm
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico,he]
    dsimp [M]
    omega
  have hcut := stationarySupport_dyadic_le_cutoff hT0 hG4 hGT4 hL
  have hb (j : ℕ) (hj : j ∈ Finset.Ico M J) :
      ‖∑ n ∈ Finset.Ioc (2^j) (2*2^j), atkinsonStationaryLeadingTerm T (4*G) L n‖ ≤
        C*printedAtkinsonBlockBound T G (2^j) := by
    have hp : (2:ℕ)*2^j ≤ 2^J := by
      rw [mul_comm,← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (Finset.mem_Ico.mp hj).2
    apply (hblock T G L hT hG hGT hL hwidth (2^j) (pow_pos (by norm_num) _) (hp.trans hcut)).trans
    rw [mul_assoc]
    change B*printedAtkinsonBlockBound T G (2^j) ≤ C*printedAtkinsonBlockBound T G (2^j)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (printedAtkinsonBlockBound_nonneg hT0.le hG.le _)
  have heq : atkinsonStationaryLeadingSum T (4*G) L =
      (∑ n ∈ Finset.Ioc 0 (2^M), atkinsonStationaryLeadingTerm T (4*G) L n)+
        ∑ j ∈ Finset.Ico M J, ∑ n ∈ Finset.Ioc (2^j) (2*2^j), atkinsonStationaryLeadingTerm T (4*G) L n := by
    rw [stationarySum_eq_dyadic_support hT0 hG4 hL0 hwidth4,
      ← sum_Ioc_pow_two_dyadic, sum_Ioc_pow_two_split _ hMJ]
  change ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤ C*(G*Real.log T+
    ∑ j ∈ (Finset.range J).filter (fun j => T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ)), printedAtkinsonBlockBound T G (2^j))
  rw [heq,hfilter]
  apply (norm_add_le _ _).trans
  apply (add_le_add hsC ((norm_sum_le _ _).trans (Finset.sum_le_sum hb))).trans_eq
  rw [← Finset.mul_sum,← mul_add]

theorem norm_printedPrefix_le_square {T : ℝ} (hT : 0 ≤ T) (K : ℕ)
    (hK : 2*(K:ℝ) ≤ T) {x : ℝ} (hx : x ∈ Icc 0 (K:ℝ)) :
    ‖printedAtkinsonPrefix T K x‖ ≤ T^2 := by
  rw [norm_printedAtkinsonPrefix T K hx.1]
  have hfloor : ⌊x⌋₊ ≤ K := Nat.floor_le_of_le hx.2
  have hn (i : ℕ) (hi : i ∈ Finset.range ⌊x⌋₊) :
      ‖atkinsonPositivePhaseTerm T (K+1+i)‖ ≤ T := by
    have hiK : K+1+i ≤ 2*K := by have := Finset.mem_range.mp hi; omega
    have hnR : ((K+1+i:ℕ):ℝ) ≤ 2*(K:ℝ) := by exact_mod_cast hiK
    have hd : ((K+1+i).divisors.card:ℝ) ≤ ((K+1+i:ℕ):ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (K+1+i)
    have hp : ‖atkinsonPositivePhaseTerm T (K+1+i)‖ = ((K+1+i).divisors.card:ℝ) := by
      simp [atkinsonPositivePhaseTerm,divisorWeight,Complex.norm_exp_ofReal_mul_I]
    rw [hp]
    exact hd.trans (hnR.trans hK)
  apply ((norm_sum_le _ _).trans (Finset.sum_le_sum hn)).trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hfR : (⌊x⌋₊:ℝ) ≤ K := by exact_mod_cast hfloor
  nlinarith [Nat.cast_nonneg (α := ℝ) K]

theorem integral_printedPrefix_eq_sum (T : ℝ) (K : ℕ) :
    (∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖) =
      ∑ i ∈ Finset.range K, ‖printedAtkinsonPrefix T K (i:ℝ)‖ := by
  have hi : (∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖) =
      ∫ x in (0:ℝ)..(K:ℝ), ‖∑ n ∈ Finset.range ⌊x⌋₊, atkinsonPositivePhaseTerm T (K+1+n)‖ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (Nat.cast_nonneg K)] at hx
    exact norm_printedAtkinsonPrefix T K hx.1
  rw [hi,integral_floor_step_nat (fun j => ‖∑ n ∈ Finset.range j, atkinsonPositivePhaseTerm T (K+1+n)‖) K]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.floor_natCast] using (norm_printedAtkinsonPrefix T K (Nat.cast_nonneg i)).symm

theorem printedBlockBound_le_damped_square {T G : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    {K : ℕ} (hK0 : 0 < K) (hK : 2*(K:ℝ) ≤ T) :
    printedAtkinsonBlockBound T G K ≤ 2*G*T^2*Real.exp (-(G^2*(K:ℝ))/T) := by
  have hT0 : 0 ≤ T := by linarith
  have hKR : (0:ℝ) < K := by exact_mod_cast hK0
  have hend := norm_printedPrefix_le_square hT0 K hK ⟨(Nat.cast_nonneg K),le_rfl⟩
  have hint : (∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖) ≤ (K:ℝ)*T^2 := by
    rw [integral_printedPrefix_eq_sum]
    apply (Finset.sum_le_sum (fun i hi => norm_printedPrefix_le_square hT0 K hK
      ⟨Nat.cast_nonneg i,by exact_mod_cast (Finset.mem_range.mp hi).le⟩)).trans_eq
    simp
  have hbracket : ‖printedAtkinsonPrefix T K (K:ℝ)‖+
      (1/(K:ℝ))*(∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖) ≤ 2*T^2 := by
    have hh := mul_le_mul_of_nonneg_left hint (show 0 ≤ 1/(K:ℝ) by positivity)
    have he : (1/(K:ℝ))*((K:ℝ)*T^2) = T^2 := by field_simp
    rw [he] at hh
    linarith
  have ht := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num : -(1/4:ℝ) ≤ 0)
  have hk := Real.rpow_le_one_of_one_le_of_nonpos
    (show (1:ℝ) ≤ K by exact_mod_cast hK0) (by norm_num : -(1/4:ℝ) ≤ 0)
  have hs : printedBlockScale T G K ≤ G*Real.exp (-(G^2*(K:ℝ))/T) := by
    unfold printedBlockScale
    have hh := mul_le_mul ht hk (by positivity) (by norm_num : (0:ℝ) ≤ 1)
    norm_num only [mul_one] at hh
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hG)
      (Real.exp_pos (-(G^2*(K:ℝ))/T)).le
    convert hh' using 1 <;> ring
  unfold printedAtkinsonBlockBound
  apply (mul_le_mul hs hbracket (by
    have hi : 0 ≤ ∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖ :=
      intervalIntegral.integral_nonneg (Nat.cast_nonneg K) (fun _ _ => norm_nonneg _)
    positivity) (by positivity)).trans_eq
  ring

def printedAtkinsonB (T G η : ℝ) : ℝ :=
  T/(2*Real.pi*G)*(Real.log T)^((1+η)/2)

def printedAtkinsonCutoff (T G η : ℝ) : ℝ :=
  (printedAtkinsonB T G η)^2/(T/(2*Real.pi)-printedAtkinsonB T G η)

theorem printedCutoff_damping_lower {T G η : ℝ} (hT : 1 < T) (hG : 0 < G)
    (hB : printedAtkinsonB T G η < T/(2*Real.pi)) :
    (Real.log T)^(1+η)/(2*Real.pi) ≤ G^2*printedAtkinsonCutoff T G η/T := by
  have hT0 : 0 < T := by linarith
  have hl0 : 0 < Real.log T := Real.log_pos hT
  have hB0 : 0 ≤ printedAtkinsonB T G η := by unfold printedAtkinsonB; positivity
  have hd := div_le_div_of_nonneg_left (sq_nonneg (printedAtkinsonB T G η))
    (sub_pos.mpr hB) (sub_le_self _ hB0)
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ G^2/T by positivity)
  have he : G^2/T*((printedAtkinsonB T G η)^2/(T/(2*Real.pi))) =
      (Real.log T)^(1+η)/(2*Real.pi) := by
    have hp : ((Real.log T)^((1+η)/2))^2 = (Real.log T)^(1+η) := by
      rw [sq,← Real.rpow_add (Real.log_pos hT)]
      congr 1
      ring
    unfold printedAtkinsonB
    rw [mul_pow,hp]
    field_simp
  rw [he] at hh
  convert hh using 1
  unfold printedAtkinsonCutoff
  ring

theorem exists_logPower_exponential_tail (C p A : ℝ) {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      C*T^p*Real.exp (-b*(Real.log T)^(1+η)) ≤ T^(-A) := by
  have hev : ∀ᶠ T : ℝ in Filter.atTop,
      C*T^p*Real.exp (-b*(Real.log T)^(1+η)) ≤ T^(-A) := by
    filter_upwards [Filter.eventually_ge_atTop (2:ℝ),Filter.eventually_ge_atTop C,
      ((tendsto_rpow_atTop hη).comp Real.tendsto_log_atTop).eventually
        (Filter.eventually_ge_atTop ((A+p+1)/b))] with T hT hTC hlog
    dsimp only [Function.comp_apply] at hlog
    have hT0 : 0 < T := by linarith
    have hl0 : 0 < Real.log T := Real.log_pos (by linarith)
    have hbLog : A+p+1 ≤ b*(Real.log T)^η := by
      have h := (div_le_iff₀ hb).mp hlog
      linarith
    have hexp : Real.exp (-b*(Real.log T)^(1+η)) ≤ T^(-(A+p+1)) := by
      rw [Real.rpow_def_of_pos hT0,Real.rpow_add hl0,Real.rpow_one]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hbLog hl0.le]
    calc
      _ ≤ T*T^p*Real.exp (-b*(Real.log T)^(1+η)) := by gcongr
      _ ≤ T*T^p*T^(-(A+p+1)) := by gcongr
      _ = T^(1+p)*T^(-(A+p+1)) := by rw [Real.rpow_add hT0,Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hT0]; congr 1; ring
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 D,le_max_left _ _,?_⟩
  intro T hT
  exact hD T ((le_max_right _ _).trans hT)

theorem sum_printedBlocks_tail_le {T G N : ℝ} (hT : 1 ≤ T) (hG : 0 ≤ G)
    (J : ℕ) (hJ : ((2^J:ℕ):ℝ) ≤ T) :
    (∑ j ∈ (Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ)),
      printedAtkinsonBlockBound T G (2^j)) ≤ 2*G*T^3*Real.exp (-(G^2*N)/T) := by
  have hT0 : 0 < T := by linarith
  have hb (j : ℕ) (hj : j ∈ (Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ))) :
      printedAtkinsonBlockBound T G (2^j) ≤ 2*G*T^2*Real.exp (-(G^2*N)/T) := by
    obtain ⟨hj,hNj⟩ := Finset.mem_filter.mp hj
    have hp : (2:ℕ)*2^j ≤ 2^J := by
      rw [mul_comm,← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hj)
    have hKR : 2*((2^j:ℕ):ℝ) ≤ T := (show 2*((2^j:ℕ):ℝ) ≤ ((2^J:ℕ):ℝ) by exact_mod_cast hp).trans hJ
    apply (printedBlockBound_le_damped_square hT hG (pow_pos (by norm_num) _) hKR).trans
    gcongr
  have hc : (((Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ))).card:ℝ) ≤ T := by
    have hcard : ((Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ))).card ≤ J :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range J)
    have hjpow : J ≤ 2^J := (Nat.lt_two_pow_self).le
    exact (show (((Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ))).card:ℝ) ≤ ((2^J:ℕ):ℝ) by
      exact_mod_cast hcard.trans hjpow).trans hJ
  calc
    _ ≤ ∑ _j ∈ (Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ)),
        2*G*T^2*Real.exp (-(G^2*N)/T) := Finset.sum_le_sum hb
    _ = (((Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ))).card:ℝ)*
        (2*G*T^2*Real.exp (-(G^2*N)/T)) := by simp
    _ ≤ T*(2*G*T^2*Real.exp (-(G^2*N)/T)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

def printedAtkinsonDyadicIndices (T G η : ℝ) : Finset ℕ :=
  (Finset.range (Nat.clog 2 (⌊printedAtkinsonCutoff T G η⌋₊+1))).filter
    (fun j => T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ))

theorem mem_printedAtkinsonDyadicIndices {T G η : ℝ}
    (hN : 0 ≤ printedAtkinsonCutoff T G η) (j : ℕ) :
    j ∈ printedAtkinsonDyadicIndices T G η ↔
      T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ) ∧ ((2^j:ℕ):ℝ) ≤ printedAtkinsonCutoff T G η := by
  simp only [printedAtkinsonDyadicIndices,Finset.mem_filter,Finset.mem_range,
    Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2:ℕ)),Nat.lt_succ_iff,Nat.le_floor_iff hN]
  exact and_comm

theorem exists_stationarySum_le_exactPrinted {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G L : ℝ,
      T₀ ≤ T → 1 ≤ Real.log T → 0 < G → 16*G^2 ≤ T → 1 ≤ L → 1200*L ≤ 4*G →
      printedAtkinsonB T G η < T/(2*Real.pi) →
      ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤ C*(G*Real.log T+
        ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j)) := by
  obtain ⟨A,hA,hmain⟩ := exists_stationarySum_le_largePrinted_dyadic
  obtain ⟨B,_,htail⟩ := exists_logPower_exponential_tail 2 3 0
    (b := 1/(2*Real.pi)) (by positivity) hη
  refine ⟨2*A,by positivity,max 40000 B,le_max_left _ _,?_⟩
  intro T G L hT hlog hG hGT hL hwidth hB
  have hTlarge : 40000 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hG4 : 0 < 4*G := by positivity
  have hGT4 : (4*G)^2 ≤ T := by nlinarith
  let J := Nat.clog 2 ⌈9*T*(L/(4*G))^2⌉₊
  let N := printedAtkinsonCutoff T G η
  let S := (Finset.range J).filter (fun j => T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ))
  have hN : 0 ≤ N := div_nonneg (sq_nonneg _) (sub_pos.mpr hB).le
  have hC := atkinsonSourceCutoff_le_small hTlarge hG4 (by linarith : 0 ≤ L) hwidth
  have hJ : ((2^J:ℕ):ℝ) ≤ T := by
    have hh : ((2^J:ℕ):ℝ) ≤ atkinsonSourceCutoff T (4*G) L := by
      exact_mod_cast stationarySupport_dyadic_le_cutoff hT0 hG4 hGT4 hL
    linarith [Nat.cast_nonneg (α := ℝ) (atkinsonSourceCutoff T (4*G) L)]
  have hexp : 2*T^3*Real.exp (-(G^2*N)/T) ≤ 1 := by
    have hd := printedCutoff_damping_lower (by linarith : 1 < T) hG hB
    have he : Real.exp (-(G^2*N)/T) ≤ Real.exp (-(1/(2*Real.pi))*(Real.log T)^(1+η)) := by
      apply Real.exp_le_exp.mpr
      dsimp [N]
      rw [neg_div]
      convert neg_le_neg hd using 1
      ring
    have ht := htail T ((le_max_right _ _).trans hT)
    norm_num only [neg_zero,Real.rpow_zero,Real.rpow_ofNat] at ht
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans ht
  have htailG : (∑ j ∈ (Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ)),
      printedAtkinsonBlockBound T G (2^j)) ≤ G*Real.log T := by
    apply (sum_printedBlocks_tail_le (by linarith) hG.le J hJ).trans
    have hh := mul_le_mul_of_nonneg_left hexp hG.le
    have hlogG := mul_le_mul_of_nonneg_left hlog hG.le
    nlinarith
  have hlow : (∑ j ∈ S.filter (fun j => ((2^j:ℕ):ℝ) ≤ N), printedAtkinsonBlockBound T G (2^j)) ≤
      ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hj,hjN⟩ := Finset.mem_filter.mp hj
      exact (mem_printedAtkinsonDyadicIndices hN j).mpr ⟨(Finset.mem_filter.mp hj).2,hjN⟩
    · intro j _ _
      exact printedAtkinsonBlockBound_nonneg hT0.le hG.le (2^j)
  have hhigh : (∑ j ∈ S.filter (fun j => ¬((2^j:ℕ):ℝ) ≤ N), printedAtkinsonBlockBound T G (2^j)) ≤
      G*Real.log T := by
    apply LE.le.trans (b := ∑ j ∈ (Finset.range J).filter (fun j => N < ((2^j:ℕ):ℝ)),
      printedAtkinsonBlockBound T G (2^j)) _ htailG
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hj,hjN⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,lt_of_not_ge hjN⟩
    · intro j _ _
      exact printedAtkinsonBlockBound_nonneg hT0.le hG.le (2^j)
  have hsum : (∑ j ∈ S, printedAtkinsonBlockBound T G (2^j)) ≤
      (∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j))+G*Real.log T := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => ((2^j:ℕ):ℝ) ≤ N)]
    exact add_le_add hlow hhigh
  have hm := hmain T G L hTlarge hlog hG hGT hL hwidth
  change ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤
    A*(G*Real.log T+∑ j ∈ S, printedAtkinsonBlockBound T G (2^j)) at hm
  have hsum0 : 0 ≤ ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j) :=
    Finset.sum_nonneg (fun j _ => printedAtkinsonBlockBound_nonneg hT0.le hG.le (2^j))
  nlinarith [mul_le_mul_of_nonneg_left hsum hA.le]

theorem eventually_printedAtkinson_geometry {δ : ℝ} (hδ : 0 < δ) (η : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ G : ℝ, T^δ ≤ G → G ≤ T^(1/2-δ) →
      1 ≤ Real.log T ∧ 0 < G ∧ 16*G^2 ≤ T ∧ 1200*Real.log T ≤ 4*G ∧
      printedAtkinsonB T G η < T/(2*Real.pi) ∧
      T^(δ/2) ≤ 4*G ∧ 4*G ≤ T^(1/2-δ/2) := by
  have hlogpow := ((isLittleO_log_rpow_rpow_atTop ((1+η)/2) hδ).const_mul_left (2:ℝ)).eventuallyLE
  filter_upwards [Filter.eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1),
    (tendsto_rpow_atTop (show 0 < δ/2 by linarith)).eventually (Filter.eventually_ge_atTop 4),
    eventually_const_log_pow_le_rpow 300 (by norm_num) 1 hδ,hlogpow] with T hT hlog hp4 hlogwidth hlogpow
  intro G hlower hupper
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog0 : 0 ≤ Real.log T := by linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 2*(Real.log T)^((1+η)/2) by positivity),
    abs_of_nonneg (Real.rpow_nonneg hT0.le δ)] at hlogpow
  have hscaled : 4*G ≤ T^(1/2-δ/2) := by
    calc
      _ ≤ T^(δ/2)*T^(1/2-δ) := mul_le_mul hp4 hupper hG.le (Real.rpow_pos_of_pos hT0 _).le
      _ = _ := by rw [← Real.rpow_add hT0]; congr 1; ring
  have hGsqrt : 4*G ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact hscaled.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hGT : 16*G^2 ≤ T := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 4*G by positivity) hGsqrt 2
    rw [Real.sq_sqrt hT0.le] at hh
    nlinarith
  have hwidth : 1200*Real.log T ≤ 4*G := by
    simp only [pow_one] at hlogwidth
    linarith
  have hB : printedAtkinsonB T G η < T/(2*Real.pi) := by
    have hlogG : (Real.log T)^((1+η)/2) < G := by linarith
    have hh := mul_lt_mul_of_pos_left hlogG (show 0 < T/(2*Real.pi*G) by positivity)
    have he : T/(2*Real.pi*G)*G = T/(2*Real.pi) := by field_simp
    rw [he] at hh
    exact hh
  refine ⟨hlog,hG,hGT,hwidth,hB,?_,hscaled⟩
  have hh := (Real.rpow_le_rpow_of_exponent_le hT1 (show δ/2 ≤ δ by linarith)).trans hlower
  linarith

theorem exists_zetaSquareLocalMean_le_exactPrinted {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ C*(G*Real.log T+
        ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j)) := by
  obtain ⟨A,hA,B,_,hstationary⟩ := exists_stationarySum_le_exactPrinted hη
  obtain ⟨D,hD,E,_,hmean⟩ := exists_zetaSquareLocalMean_le_stationary_full_width (show 0 < δ/2 by linarith)
  obtain ⟨F,hF⟩ := Filter.eventually_atTop.mp (eventually_printedAtkinson_geometry hδ η)
  let C := 2*Real.exp 1*A+4*D
  refine ⟨C,by dsimp [C]; positivity,max 40000 (max B (max E F)),le_max_left _ _,?_⟩
  intro T G hT hlower hupper
  have hTlarge : 40000 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hBT : B ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hET : E ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  have hFT : F ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  obtain ⟨hlog,hG,hGT,hwidth,hB,hlo,hhi⟩ := hF T hFT G hlower hupper
  have hm := hmean T (4*G) hET hlo hhi
  have hs := hstationary T G (Real.log T) hBT hlog hG hGT hlog hwidth hB
  have hmono : (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
      ∫ t in T-4*G..T+4*G, zetaMomentCriticalNorm t^2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (zetaMomentCriticalNorm t))
    · exact (continuous_zetaMomentCriticalNorm.pow 2).intervalIntegrable _ _
  have hr := (Complex.re_le_norm (atkinsonStationaryLeadingSum T (4*G) (Real.log T))).trans hs
  have hsum0 : 0 ≤ ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j) :=
    Finset.sum_nonneg (fun j _ => printedAtkinsonBlockBound_nonneg hT0.le hG.le (2^j))
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.exp 1 by positivity)
  dsimp [C]
  nlinarith

theorem printedBlockBound_eq_source {T : ℝ} (hT : 0 ≤ T) (G : ℝ) (K : ℕ) :
    printedAtkinsonBlockBound T G K = G*(T*(K:ℝ))^(-(1/4:ℝ))*
      (‖printedAtkinsonPrefix T K (K:ℝ)‖+
        (K:ℝ)⁻¹*(∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖))*
      Real.exp (-(G^2*(K:ℝ))/T) := by
  unfold printedAtkinsonBlockBound printedBlockScale
  rw [Real.mul_rpow hT (Nat.cast_nonneg K)]
  ring

/-- Ivić Orsay 83.06, Theorem 6.2, (6.20)--(6.23), at the literal source
phase, prefix endpoints, cutoff, damping and original full power widths. -/
theorem exists_zetaSquareLocalMean_le_printedAtkinson {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ C*(G*Real.log T+
        G*∑ j ∈ printedAtkinsonDyadicIndices T G η,
          (T*((2^j:ℕ):ℝ))^(-(1/4:ℝ))*
            (‖printedAtkinsonPrefix T (2^j) ((2^j:ℕ):ℝ)‖+
              (((2^j:ℕ):ℝ))⁻¹*(∫ x in (0:ℝ)..((2^j:ℕ):ℝ), ‖printedAtkinsonPrefix T (2^j) x‖))*
            Real.exp (-(G^2*((2^j:ℕ):ℝ))/T)) := by
  obtain ⟨C,hC,T₀,hT₀,hm⟩ := exists_zetaSquareLocalMean_le_exactPrinted hδ hη
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T G hT hlower hupper
  have hT0 : 0 ≤ T := by linarith [hT₀.trans hT]
  have h := hm T G hT hlower hupper
  simp only [printedBlockBound_eq_source hT0] at h
  convert h using 1
  rw [Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

end TaoTrudgianYang2025.AtkinsonPrintedSource

