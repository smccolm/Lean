import TaoTrudgianYang2025.SargosQuarticRoundedScale

/-! The actual stationary polynomial maximum reduced to two rounded dyadic blocks. -/

noncomputable section

open Set
open scoped BigOperators FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticDualBlockMaximum (m : ℕ) (α γ : ℝ) : ℝ :=
  sargosIntegerPrefixMaximum ((m:ℤ)+1) m
    (fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ))

theorem sargosQuarticDualBlockMaximum_nonneg (m : ℕ) (α γ : ℝ) :
    0 ≤ sargosQuarticDualBlockMaximum m α γ :=
  sargosIntegerPrefixMaximum_nonneg _ _ _

theorem sargosQuarticPolynomialPrefixMaximum_le_two_blocks {N Δ α γ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) (hα : α ∈ Icc Δ (2*Δ))
    (hγ : |γ| ≤ 1/N^3) :
    let m := sargosQuarticRoundedDualScale N Δ
    sargosQuarticPolynomialPrefixMaximum N α γ ≤
      2*sargosQuarticDualBlockMaximum m α γ+
        2*sargosQuarticDualBlockMaximum (2*m) α γ+40 := by
  intro m
  let a : ℤ := ⌈sargosQuarticSlope α γ N⌉
  let b : ℤ := ⌊sargosQuarticSlope α γ (2*N)⌋
  let H := (b+1-a).toNat
  let f : ℤ → ℂ := fun y => (𝐞 (sargosQuarticDualPolynomial α γ y) : ℂ)
  have hb := sargosQuarticRoundedFrequency_bounds hN hΔ hα hγ
  have hlo : (m:ℤ)-4 ≤ a := hb.1
  have hhi : b ≤ 4*(m:ℤ)+35 := hb.2
  obtain ⟨L,hL,he⟩ := sargosIntegerPrefixMaximum_attained a H f
  change sargosIntegerPrefixMaximum a H f ≤ _
  rw [he]
  cases L with
  | zero =>
    simp only [sargosIntegerPrefix,Finset.sum_range_zero,norm_zero]
    have h₁ := sargosQuarticDualBlockMaximum_nonneg m α γ
    have h₂ := sargosQuarticDualBlockMaximum_nonneg (2*m) α γ
    linarith
  | succ L =>
    have htop : a+(L:ℤ) ≤ b := by dsimp [H] at hL; omega
    have hsum : sargosIntegerPrefix a (L+1) f =
        ∑ y ∈ Finset.Icc a (a+(L:ℤ)), f y := by
      rw [sargos_sum_Icc_eq_range]
      have hlen : (a+(L:ℤ)+1-a).toNat = L+1 := by omega
      rw [hlen]
      rfl
    rw [hsum]
    have hh := norm_sargosInteger_interval_le_two_dyadic m a (a+(L:ℤ)) f hlo
      (htop.trans hhi) (fun y => by dsimp [f]; rw [Circle.norm_coe])
    simpa only [sargosQuarticDualBlockMaximum,f,Nat.cast_mul,Nat.cast_ofNat] using hh

theorem sargosQuartic_source_le_two_dual_blocks :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (Δ α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ Δ → Δ ≤ 1/2 →
      α ∈ Icc Δ (2*Δ) → |γ| ≤ 1/(N : ℝ)^3 →
      let m := sargosQuarticRoundedDualScale N Δ
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤
        C*((1/Real.sqrt Δ)*(sargosQuarticDualBlockMaximum m α γ+
          sargosQuarticDualBlockMaximum (2*m) α γ)+(N : ℝ)^((1:ℝ)/4)) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_source_le_polynomialPrefixMaximum
  refine ⟨41*C,by linarith,?_⟩
  intro N Δ α γ hN hΔ hΔ₁ hα hγ m
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hN₁ : (1:ℝ) ≤ N := by linarith
  have hαs : 1/Real.sqrt (N : ℝ) ≤ α := hΔ.trans hα.1
  have hα₁ : α ≤ 1 := by linarith [hα.2]
  have hΔp := (sargosQuartic_source_scale hNr hΔ).1
  have hαp : 0 < α := hΔp.trans_le hα.1
  have hs := hsource N α γ hN hαs hα₁ hγ
  have hb := sargosQuarticPolynomialPrefixMaximum_le_two_blocks hNr hΔ hα hγ
  have hscale := sargos_source_inverse_sqrt_le_quarterPower hN₁ hαs
  have hcompare : 1/Real.sqrt α ≤ 1/Real.sqrt Δ :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hΔp) (Real.sqrt_le_sqrt hα.1)
  let B := sargosQuarticDualBlockMaximum m α γ+sargosQuarticDualBlockMaximum (2*m) α γ
  have hB : 0 ≤ B := add_nonneg (sargosQuarticDualBlockMaximum_nonneg m α γ)
    (sargosQuarticDualBlockMaximum_nonneg (2*m) α γ)
  have hi : 0 ≤ 1/Real.sqrt α := by positivity
  have hiΔ : 0 ≤ 1/Real.sqrt Δ := by positivity
  have hp : 0 ≤ (N : ℝ)^((1:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcb : sargosQuarticPolynomialPrefixMaximum N α γ ≤ 2*B+40 := by
    change _ ≤ 2*(sargosQuarticDualBlockMaximum m α γ+sargosQuarticDualBlockMaximum (2*m) α γ)+40
    linarith only [hb]
  have hmul := mul_le_mul_of_nonneg_left hcb hi
  have hmax := mul_le_mul_of_nonneg_right hcompare hB
  have hcpos : 0 ≤ C := by linarith
  have hinside :
      (1/Real.sqrt α)*sargosQuarticPolynomialPrefixMaximum N α γ+(N : ℝ)^((1:ℝ)/4) ≤
        41*((1/Real.sqrt Δ)*B+(N : ℝ)^((1:ℝ)/4)) := by
    have hh : 0 ≤ (1/Real.sqrt Δ)*B := mul_nonneg hiΔ hB
    nlinarith only [hmul,hmax,hscale,hh,hp]
  apply hs.trans
  change _ ≤ (41*C)*((1/Real.sqrt Δ)*B+(N : ℝ)^((1:ℝ)/4))
  exact (mul_le_mul_of_nonneg_left hinside hcpos).trans_eq (by ring)

end TaoTrudgianYang2025

