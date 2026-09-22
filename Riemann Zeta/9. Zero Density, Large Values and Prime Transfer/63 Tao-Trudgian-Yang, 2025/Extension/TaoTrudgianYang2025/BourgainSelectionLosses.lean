import TaoTrudgianYang2025.BourgainCommonCorrelation

/-!
# Uniform small-power control of all three finite selection counts

The actual amplitude, relative-multiplicity and correlation counts have
a product bounded by an arbitrary positive power. Fixed alpha is included
among the allowed dependencies; no uniform-in-alpha threshold is asserted.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgainRelativeLevelCount_uniform_power {τ η : ℝ} (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (bourgainRelativeLevelCount N τ : ℝ) ≤ D*N^η := by
  obtain ⟨D, N₀, hD, hN₀, hbound⟩ := bourgainZetaBandCount_uniform_power
    (B := 1) (A := |τ|+2) (u := 0) (by norm_num) (by positivity) (by norm_num) hη
  refine ⟨D, N₀, hD, hN₀, ?_⟩
  intro N hN
  exact hbound N 0 hN (by norm_num) (by norm_num)

/-- All three actual counts on the physical pattern have a joint
small-power bound, with constants fixed before the pattern and height window. -/
theorem bourgain_selection_counts_uniform_power {B C α τ ε η : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ), δ ≤ 1 → N₀ ≤ P.N → P.T ≤ P.N^(τ+δ) →
        let U := P.T+P.N^(ε/8)+1
        let J := bourgainZetaBandCount B U (P.N^(-bourgainSharedFloorExponent α τ ε))
        let Q := bourgainRelativeLevelCount P.N τ
        let K := bourgainCorrelationLevelCount P.N B C α τ ε
        (J : ℝ)*(Q : ℝ)*(K : ℝ) ≤ D*P.N^η := by
  have hthird : 0 < η/3 := by positivity
  obtain ⟨D₁, N₁, hD₁, hN₁, hfirst⟩ := bourgainZetaBandCount_uniform_power
    (B := B) (A := bourgainSharedFloorExponent α τ ε) (u := |τ|+ε+1)
    hB (bourgainSharedFloorExponent_pos α τ hε).le (by positivity) hthird
  obtain ⟨D₂, N₂, hD₂, hN₂, hsecond⟩ :=
    bourgainRelativeLevelCount_uniform_power (τ := τ) hthird
  obtain ⟨D₃, N₃, hD₃, hN₃, hthirdBound⟩ :=
    bourgainCorrelationLevelCount_uniform_power (B := B) (C := C)
      (α := α) (τ := τ) hC hε hthird
  let N₀ := max N₁ (max N₂ N₃)
  have hN₀ : 2 ≤ N₀ := hN₁.trans (le_max_left _ _)
  have hD : 1 ≤ D₁*D₂*D₃ := by
    have h12 : 1 ≤ D₁*D₂ := by nlinarith
    nlinarith
  refine ⟨D₁*D₂*D₃, N₀, hD, hN₀, ?_⟩
  intro P δ hδ hN hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hP₁ : N₁ ≤ P.N := (le_max_left _ _).trans hN
  have hP₂ : N₂ ≤ P.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hP₃ : N₃ ≤ P.N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  let U := P.T+P.N^(ε/8)+1
  let J := bourgainZetaBandCount B U (P.N^(-bourgainSharedFloorExponent α τ ε))
  let Q := bourgainRelativeLevelCount P.N τ
  let K := bourgainCorrelationLevelCount P.N B C α τ ε
  have hU : 0 ≤ U := by
    dsimp only [U]
    have ht := P.T_pos
    positivity
  have hJ : (J : ℝ) ≤ D₁*P.N^(η/3) :=
    hfirst P.N U hP₁ hU (bourgain_shared_band_radius_le P hε hδ hT)
  have hQ : (Q : ℝ) ≤ D₂*P.N^(η/3) := hsecond P.N hP₂
  have hK : (K : ℝ) ≤ D₃*P.N^(η/3) := hthirdBound P.N hP₃
  have hp : (P.N^(η/3))^3 = P.N^η := by
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    norm_num
  change (J : ℝ)*(Q : ℝ)*(K : ℝ) ≤ _
  calc
    _ ≤ (D₁*P.N^(η/3))*(D₂*P.N^(η/3))*(D₃*P.N^(η/3)) := by gcongr
    _ = D₁*D₂*D₃*(P.N^(η/3))^3 := by ring
    _ = _ := by rw [hp]

end TaoTrudgianYang2025
