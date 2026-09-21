import TaoTrudgianYang2025.AtkinsonResidualVariation
import TaoTrudgianYang2025.AtkinsonGaussianVariation

/-!
# Uniform damped variation of both actual normalized main weights

All four factors are constructed at the linked physical scales.
The bound holds for every positive-index block in the actual small-frequency
range, not just for a supplied abstract weight or a single boundary case.
-/

noncomputable section

open Complex Set

namespace TaoTrudgianYang2025

theorem atkinsonFourthRootCoefficient_antitone {T : ℝ} (hT : 0 < T) :
    AntitoneOn (atkinsonFourthRootCoefficient T) (Ici 1) := by
  intro m hm n hn hmn
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hp := Real.rpow_le_rpow_of_nonpos hm0 hmnR (by norm_num : -(1/4:ℝ) ≤ 0)
  have hq := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (m:ℝ)+2*T/Real.pi)
    (add_le_add hmnR (le_rfl : 2*T/Real.pi ≤ 2*T/Real.pi)) (by norm_num : -(1/4:ℝ) ≤ 0)
  rw [atkinsonFourthRootCoefficient_eq hT,atkinsonFourthRootCoefficient_eq hT]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hq
    (Real.rpow_nonneg (by positivity) _) (by positivity)

theorem finiteVariationBound_fourthRootCoefficient {T : ℝ} (hT : 0 < T)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    FiniteVariationBound (fun i => (atkinsonFourthRootCoefficient T (m+i) : ℂ)) N
      (((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))) := by
  have hanti : Antitone (fun i : ℕ => atkinsonFourthRootCoefficient T (m+i)) := by
    intro i j hij
    apply atkinsonFourthRootCoefficient_antitone hT (by simp only [mem_Ici]; omega)
      (by simp only [mem_Ici]; omega)
    omega
  have h := finiteVariationBound_of_antitone (atkinsonFourthRootCoefficient_nonneg hT m)
    (hanti.antitoneOn (Iic N)) (fun i _ => ⟨atkinsonFourthRootCoefficient_nonneg hT _,by
      simpa only [Nat.add_zero] using hanti (Nat.zero_le i)⟩)
  exact h.mono (atkinsonFourthRootCoefficient_le_height hT m)

theorem exists_finiteVariationBound_atkinsonMainWeights :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ m N : ℕ, 0 < m → 10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => atkinsonPositiveMainWeight T G L (m+i)) N
        (C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))) ∧
      FiniteVariationBound (fun i => atkinsonNegativeMainWeight T G L (m+i)) N
        (C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))) := by
  obtain ⟨D,hD,hres⟩ := exists_finiteVariationBound_saddleResidual
  let K : ℝ := (1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨8*K*Real.sqrt Real.pi*D,by positivity,?_⟩
  intro T G L hT hG hGT hL m N hm hN
  have hmT : (m:ℝ) ≤ T := by
    have hcast : (m:ℝ) ≤ (m+N:ℕ) := by exact_mod_cast Nat.le_add_right m N
    have hn0 : (0:ℝ) ≤ (m+N:ℕ) := Nat.cast_nonneg _
    linarith
  have hc := finiteVariationBound_fourthRootCoefficient hT hm N
  have hg := finiteVariationBound_atkinsonSaddleGaussian_physical hT hG hGT m N hmT
  obtain ⟨hrp,hrm⟩ := hres T G L hT hG hL m N hN
  constructor
  · convert (hc.mul hg).mul hrp using 1
    dsimp [K]
    ring
  · convert (hc.mul hg).mul hrm using 1
    dsimp [K]
    ring

end TaoTrudgianYang2025
