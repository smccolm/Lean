import TaoTrudgianYang2025.SargosPrefixMaximum
import Mathlib.Analysis.MeanInequalitiesPow

/-! Natural-power Fourier majorants from finite weighted Jensen. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_weighted_sum_pow_succ {ι : Type*} (S : Finset ι)
    (b x : ι → ℝ) (hb : ∀ i ∈ S, 0 ≤ b i) (hx : ∀ i ∈ S, 0 ≤ x i)
    (hB : 0 < ∑ i ∈ S, b i) (p : ℕ) :
    (∑ i ∈ S, b i*x i)^(p+1) ≤
      (∑ i ∈ S, b i)^p*(∑ i ∈ S, b i*(x i)^(p+1)) := by
  let B : ℝ := ∑ i ∈ S, b i
  have hBp : 0 < B := hB
  have hw : ∑ i ∈ S, b i/B = 1 := by
    rw [← Finset.sum_div]
    exact div_self hBp.ne'
  have h := Real.pow_arith_mean_le_arith_mean_pow S
    (fun i => b i/B) x (fun i hi => div_nonneg (hb i hi) hBp.le) hw hx (p+1)
  have he1 : (∑ i ∈ S, b i/B*x i) = (∑ i ∈ S, b i*x i)/B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have he2 : (∑ i ∈ S, b i/B*(x i)^(p+1)) =
      (∑ i ∈ S, b i*(x i)^(p+1))/B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he1,he2,div_pow] at h
  have hm := (div_le_iff₀ (pow_pos hBp (p+1))).1 h
  calc
    _ ≤ ((∑ i ∈ S, b i*(x i)^(p+1))/B)*B^(p+1) := hm
    _ = _ := by rw [pow_succ]; dsimp [B]; field_simp

theorem sum_sargosPrefixMajorant_pos {N : ℕ} [NeZero N] :
    0 < ∑ k : ZMod N, sargosPrefixMajorant k := by
  rw [sum_sargosPrefixMajorant_eq]
  have h : 0 ≤ ∑ j ∈ Finset.range N, (j : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun j hj => by positivity)
  linarith

def sargosFourierPowerMajorant {N : ℕ} [NeZero N] (p : ℕ) (f : ZMod N → ℂ) : ℝ :=
  (∑ k : ZMod N, sargosPrefixMajorant k)^p*
    (∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖^(p+1))

theorem sargosFourierPowerMajorant_nonneg {N : ℕ} [NeZero N]
    (p : ℕ) (f : ZMod N → ℂ) :
    0 ≤ sargosFourierPowerMajorant p f := by
  unfold sargosFourierPowerMajorant
  exact mul_nonneg (pow_nonneg (sum_sargosPrefixMajorant_pos (N := N)).le p)
    (Finset.sum_nonneg (fun k hk => mul_nonneg (sargosPrefixMajorant_nonneg k)
      (pow_nonneg (norm_nonneg _) _)))

theorem norm_sargosFinitePrefix_pow_succ_le {N H : ℕ} [NeZero N]
    (p : ℕ) (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖^(p+1) ≤ sargosFourierPowerMajorant p f := by
  calc
    _ ≤ (∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖)^(p+1) :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sargosFinitePrefix_le_fourierMajorant f hH) _
    _ ≤ _ := sargos_weighted_sum_pow_succ Finset.univ sargosPrefixMajorant
      (fun k => ‖ZMod.dft f k‖) (fun k hk => sargosPrefixMajorant_nonneg k)
      (fun k hk => norm_nonneg _) sum_sargosPrefixMajorant_pos p

theorem sargosFinitePrefixMaximum_pow_succ_le {N : ℕ} [NeZero N]
    (p : ℕ) (f : ZMod N → ℂ) :
    (sargosFinitePrefixMaximum f)^(p+1) ≤ sargosFourierPowerMajorant p f := by
  obtain ⟨H,hH,he⟩ := sargosFinitePrefixMaximum_attained f
  rw [he]
  exact norm_sargosFinitePrefix_pow_succ_le p f hH

end TaoTrudgianYang2025
