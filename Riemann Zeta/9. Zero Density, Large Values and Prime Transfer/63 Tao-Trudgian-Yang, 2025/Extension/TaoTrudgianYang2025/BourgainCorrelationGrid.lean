import TaoTrudgianYang2025.BourgainCorrelationWindow

/-!
# A shared logarithmic correlation grid

The count uses the common power floor and physical upper endpoint.
Actual component correlations select half-open bands on this grid.
-/

open Filter MeasureTheory RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainCorrelationLevel (N B C α τ ε : ℝ) (k : ℕ) : ℝ :=
  bourgainCorrelationFloor N B C α τ ε*(2 : ℝ)^k

def bourgainCorrelationLevelCount (N B C α τ ε : ℝ) : ℕ :=
  bourgainZetaBandCount (4*bourgainCorrelationConstant B C ε)
    (N^(ε/8)-1) (N^(-bourgainCorrelationExponent α τ ε))

theorem bourgainCorrelationLevelCount_pos (N B C α τ ε : ℝ) :
    0 < bourgainCorrelationLevelCount N B C α τ ε := by
  exact bourgainZetaBandCount_pos _ _ _

/-- The actual ceiling count is logarithmic, with all fixed-parameter
dependencies explicit and no component-dependent floor. -/
theorem bourgainCorrelationLevelCount_log_bound {N B C α τ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (bourgainCorrelationLevelCount N B C α τ ε : ℝ) ≤
      2+(Real.log (16*bourgainCorrelationConstant B C ε+1)+
        (ε/8+bourgainCorrelationExponent α τ ε)*Real.log N)/Real.log 2 := by
  have hK : 0 < bourgainCorrelationConstant B C ε :=
    zero_lt_one.trans_le (bourgainCorrelationConstant_one_le B hC ε)
  have hH : 1 ≤ N^(ε/8) := Real.one_le_rpow hN (by positivity)
  have hh := bourgainZetaBandCount_power_log_bound
    (B := 4*bourgainCorrelationConstant B C ε) (N := N) (U := N^(ε/8)-1)
    (A := bourgainCorrelationExponent α τ ε) (u := ε/8)
    (by positivity) hN (by linarith) (bourgainCorrelationExponent_pos α τ hε).le
    (by positivity) (by linarith)
  simpa only [bourgainCorrelationLevelCount,
    show 4*(4*bourgainCorrelationConstant B C ε)+1 =
      16*bourgainCorrelationConstant B C ε+1 by ring] using hh

/-- For fixed parameters the correlation selection costs any prescribed
positive power. The constants may depend on alpha, tau and epsilon. -/
theorem bourgainCorrelationLevelCount_uniform_power {B C α τ ε η : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (bourgainCorrelationLevelCount N B C α τ ε : ℝ) ≤ D*N^η := by
  have hK : 0 < bourgainCorrelationConstant B C ε :=
    zero_lt_one.trans_le (bourgainCorrelationConstant_one_le B hC ε)
  obtain ⟨D, N₀, hD, hN₀, hbound⟩ := bourgainZetaBandCount_uniform_power
    (B := 4*bourgainCorrelationConstant B C ε)
    (A := bourgainCorrelationExponent α τ ε) (u := ε/8) (η := η)
    (by positivity) (bourgainCorrelationExponent_pos α τ hε).le (by positivity) hη
  refine ⟨D, N₀, hD, hN₀, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by linarith
  have hH : 1 ≤ N^(ε/8) := Real.one_le_rpow hN1 (by positivity)
  exact hbound N (N^(ε/8)-1) hN (by linarith) (by linarith)

/-- The terminal endpoint strictly exceeds the proved physical
correlation upper bound, including exact powers of two. -/
theorem bourgainCorrelationLevel_terminal {N B C α τ ε : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) :
    4*N^(ε/8) < bourgainCorrelationFloor N B C α τ ε*
      (2 : ℝ)^(bourgainCorrelationLevelCount N B C α τ ε) := by
  let K := bourgainCorrelationConstant B C ε
  have hK : 0 < K := zero_lt_one.trans_le (bourgainCorrelationConstant_one_le B hC ε)
  have ha : 0 < N^(-bourgainCorrelationExponent α τ ε) := Real.rpow_pos_of_pos hN _
  have hh := bourgainZetaBandCount_terminal
    (B := 4*K) (T := N^(ε/8)-1) ha
  change 4*K*(1+(N^(ε/8)-1)) <
    N^(-bourgainCorrelationExponent α τ ε)*
      (2 : ℝ)^(bourgainCorrelationLevelCount N B C α τ ε) at hh
  apply (mul_lt_mul_iff_of_pos_left hK).mp
  convert hh using 1
  · ring
  · dsimp only [bourgainCorrelationFloor, K]
    have hKne : bourgainCorrelationConstant B C ε ≠ 0 := hK.ne'
    field_simp [hKne]

/-- A genuine component chooses a common-grid correlation band, with
two-sided bounds on its actual occupancy mass. -/
theorem bourgain_component_correlation_grid (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates)
    {B C α τ ε δ : ℝ} {j q : ℕ}
    (hband : BourgainComponentBand P.N P.T B C τ α ε W j q)
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let H := P.N^(ε/8)
    let U := P.T+H+1
    let a := P.N^(-bourgainSharedFloorExponent α τ ε)
    let D := bourgainDifferenceLevel W j
    let V := a*(2 : ℝ)^q
    let r := bourgainZetaBandCorrelation D H U V
    let μ := volume.real (bourgainZetaBand U V)
    ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
      let s := bourgainCorrelationLevel P.N B C α τ ε k
      0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
      s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
      bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ) := by
  let H := P.N^(ε/8)
  let U := P.T+H+1
  let a := P.N^(-bourgainSharedFloorExponent α τ ε)
  let D := bourgainDifferenceLevel W j
  let V := a*(2 : ℝ)^q
  let r := bourgainZetaBandCorrelation D H U V
  let μ := volume.real (bourgainZetaBand U V)
  obtain ⟨hf, hlo, hupper⟩ :=
    bourgain_component_correlation_window P hsub hband hB hC hε hδ hT
  have hterminal := bourgainCorrelationLevel_terminal (B := B) (α := α) (τ := τ) (ε := ε)
    (zero_lt_one.trans P.one_lt_N) hC.le
  obtain ⟨k, hk, hslo, hshi⟩ :=
    exists_bourgain_dyadic_amplitude hlo.le (hupper.trans_lt hterminal)
  have hs : 0 < bourgainCorrelationLevel P.N B C α τ ε k := mul_pos hf (by positivity)
  have hdata := hband.2.2.2.2.2
  rcases hdata with ⟨_, _, _, _, hμ, _, _, _, _, _, heq, _⟩
  have hD : (0 : ℝ) < D.card := by
    exact_mod_cast Finset.card_pos.mpr hband.2.1
  have hμsqrt : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hDsqrt : 0 < Real.sqrt (D.card : ℝ) := Real.sqrt_pos.mpr hD
  refine ⟨k, hk, hs, hslo, hshi, hslo.trans hupper, ?_, ?_⟩
  · rw [heq]
    simpa only [bourgainCorrelationLevel, mul_assoc] using
      mul_le_mul_of_nonneg_right hslo (mul_pos hμsqrt hDsqrt).le
  · rw [heq]
    simpa only [bourgainCorrelationLevel, mul_assoc] using
      mul_lt_mul_of_pos_right hshi (mul_pos hμsqrt hDsqrt)

end TaoTrudgianYang2025
