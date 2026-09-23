import TaoTrudgianYang2025.SargosMaximalWindow
import TaoTrudgianYang2025.SargosSlowPowerWindow

/-!
# Robert--Sargos Lemma 1 with explicit constants

The first integral is a genuine upper integral; no parameter measurability
is imposed. The source logarithm, literal ordered tuple count, derivative
loss, and both physical window widths remain explicit. The proof also works
for delta > 1, so no unused upper restriction on delta is imposed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

def sargosWindowConstant (p : ℕ) (K : ℝ) : ℝ :=
  16*(3*(1+2*Real.pi*K)*(1+1/Real.log 2))^(2*p)

theorem sargosWindowConstant_nonneg (p : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ sargosWindowConstant p K := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold sargosWindowConstant
  positivity

theorem sargosWindow_coefficient_le {N : ℕ} (hN : 2 ≤ N) (p : ℕ)
    {K : ℝ} (hK : 0 ≤ K) :
    (1+2*Real.pi*K)^(2*p)*(3*(1+Real.log N))^(2*p) ≤
      (sargosWindowConstant p K/16)*(Real.log N)^(2*p) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hbase : (1+2*Real.pi*K)*(3*(1+Real.log N)) ≤
      (3*(1+2*Real.pi*K)*(1+1/Real.log 2))*Real.log N := by
    have h := mul_le_mul_of_nonneg_left (sargos_one_add_log_le_source hN)
      (by positivity : 0 ≤ 3*(1+2*Real.pi*K))
    convert h using 1 <;> ring
  calc
    _ = ((1+2*Real.pi*K)*(3*(1+Real.log N)))^(2*p) := (mul_pow _ _ _).symm
    _ ≤ ((3*(1+2*Real.pi*K)*(1+1/Real.log 2))*Real.log N)^(2*p) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by rw [mul_pow]; unfold sargosWindowConstant; ring

theorem sargosSlowQuartic_upper_even_window_le_count {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K δ lambda : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hlambda : 0 < lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))
      (fun t : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))) ≤
      ENNReal.ofReal (sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p)*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  apply (sargosSlowQuartic_upper_power_rectangle_le hN1 (2*p) z hK
    c (c+δ) d (d+lambda) φ φ' hφ hφ').trans
  apply ENNReal.ofReal_le_ofReal
  let B : ℝ := (sargosMomentNearCount N p
    (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ)
  have hB : 0 ≤ B := Nat.cast_nonneg _
  calc
    _ ≤ (1+2*Real.pi*K)^(2*p)*((3*(1+Real.log N))^(2*p)*(16*δ*lambda)*B) :=
      mul_le_mul_of_nonneg_left
        (sargosQuartic_maximal_even_window_le_count hN1 hp z hz hδ hlambda c d) (by positivity)
    _ = ((1+2*Real.pi*K)^(2*p)*(3*(1+Real.log N))^(2*p))*((16*δ*lambda)*B) := by ring
    _ ≤ ((sargosWindowConstant p K/16)*(Real.log N)^(2*p))*((16*δ*lambda)*B) :=
      mul_le_mul_of_nonneg_right (sargosWindow_coefficient_le hN p hK) (by positivity)
    _ = _ := by dsimp [B]; ring

theorem sargos_lemma_one_upper {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ δ μ lambda : ℝ} (hK : 0 ≤ K) (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N) :
    (sargosUpperIntegral
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))
      (fun t : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))) ≤
      ENNReal.ofReal (sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p)*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ))) ∧
    ((sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p))) :=
  ⟨sargosSlowQuartic_upper_even_window_le_count hN hp z hz hK
      (hΔ.trans_le hδ) (hμ.trans_le hlambda) c d φ φ' hφ hφ',
    sargosMomentNearCount_window_le_central (by omega) p hΔ hμ hδ hlambda⟩

theorem sargosSlowQuartic_upper_even_window_transfer {N p : ℕ}
    (hN : 2 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ δ μ lambda : ℝ} (hK : 0 ≤ K) (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda)
    (c d : ℝ) (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+δ), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda))))
      (fun t : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^(2*p))) ≤
      ENNReal.ofReal ((64*sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p)/(Δ*μ))*
        (∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
          ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p))) := by
  obtain ⟨hleft,hright⟩ := sargos_lemma_one_upper hN hp z hz hK hΔ hμ hδ hlambda c d φ φ' hφ hφ'
  apply hleft.trans
  apply ENNReal.ofReal_le_ofReal
  have hδp := hΔ.trans_le hδ
  have hlambdap := hμ.trans_le hlambda
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hC := sargosWindowConstant_nonneg p hK
  calc
    _ ≤ (sargosWindowConstant p K*δ*lambda*(Real.log N)^(2*p))*
        ((64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
          ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p))) :=
      mul_le_mul_of_nonneg_left hright (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025

