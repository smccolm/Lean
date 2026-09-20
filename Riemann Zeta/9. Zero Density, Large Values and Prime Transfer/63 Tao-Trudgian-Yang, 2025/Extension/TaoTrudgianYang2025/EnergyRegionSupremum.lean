import TaoTrudgianYang2025.EnergyRegionAsymptotics
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Compactness for energy-region suprema

This module supplies the subsequence argument needed for the reverse
region-supremum characterization.  The three logarithmic coordinates are
kept together, so the cardinality, energy, and double-zeta exponents are
extracted along one common subsequence.
-/

open Filter Set Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- The three logarithmic exponents of a finite large-value pattern. -/
def energyLogCoordinates (P : LargeValuePattern) : ℝ × ℝ × ℝ :=
  (Real.logb P.N (P.ordinates.card : ℝ),
    Real.logb P.N (finsetAdditiveEnergy P.ordinates : ℝ),
    Real.logb P.N (doubleZetaSum P))

/-- The elementary cardinality, additive-energy, and double-sum estimates put
the three logarithmic coordinates in a fixed compact box. -/
theorem energyLogCoordinates_mem_box
    (P : LargeValuePattern) {τ e : ℝ}
    (hτ : 0 ≤ τ) (hePos : 0 < e) (heOne : e ≤ 1)
    (hNtwo : 2 ≤ P.N) (hT : P.T ≤ P.N ^ (τ + e))
    (hCardPos : 0 < (P.ordinates.card : ℝ))
    (hEnergyPos : 0 < (finsetAdditiveEnergy P.ordinates : ℝ))
    (hSumPos : 0 < doubleZetaSum P) :
    energyLogCoordinates P ∈
      Icc (0, 0, 0) (τ + 2, 3 * τ + 8, 2 * τ + 8) := by
  have hNPos : 0 < P.N := lt_of_lt_of_le (by norm_num) hNtwo
  have hNNonneg : 0 ≤ P.N := hNPos.le
  have hPowNonneg : 0 ≤ P.N ^ (τ + e) := Real.rpow_nonneg hNNonneg _
  have hPowOne : 1 ≤ P.N ^ (τ + e) := by
    exact Real.one_le_rpow P.one_lt_N.le (by linarith)
  have hCardUpper : (P.ordinates.card : ℝ) ≤ P.N ^ (τ + 2) := by
    calc
      (P.ordinates.card : ℝ) ≤ P.T + 1 := P.ordinate_card_cast_le
      _ ≤ P.N ^ (τ + e) + 1 := by linarith
      _ ≤ 2 * P.N ^ (τ + e) := by linarith
      _ ≤ P.N * P.N ^ (τ + e) :=
        mul_le_mul_of_nonneg_right hNtwo hPowNonneg
      _ = P.N ^ (1 : ℝ) * P.N ^ (τ + e) := by rw [Real.rpow_one]
      _ = P.N ^ (1 + (τ + e)) :=
        (Real.rpow_add hNPos 1 (τ + e)).symm
      _ ≤ P.N ^ (τ + 2) := by
        exact Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
  have hCardSquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (P.N ^ (τ + 2)) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hNNonneg _)).2
      hCardUpper
  have hCardCube : (P.ordinates.card : ℝ) ^ 3 ≤
      (P.N ^ (τ + 2)) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hCardUpper 3
  have hEnergyCombinatorial :
      (finsetAdditiveEnergy P.ordinates : ℝ) ≤
        3 * (P.ordinates.card : ℝ) ^ 3 := by
    exact_mod_cast finset_additiveEnergy_le_three_mul_cube
      P.ordinates P.ordinates_oneSeparated
  have hThree : (3 : ℝ) ≤ P.N ^ 2 := by nlinarith
  have hCardPowerSquare : (P.N ^ (τ + 2)) ^ 2 =
      P.N ^ (2 * (τ + 2)) := by
    calc
      (P.N ^ (τ + 2)) ^ 2 = P.N ^ ((τ + 2) * (2 : ℝ)) := by
        rw [Real.rpow_mul hNNonneg]
        exact (Real.rpow_natCast (P.N ^ (τ + 2)) 2).symm
      _ = P.N ^ (2 * (τ + 2)) := by ring_nf
  have hCardPowerCube : (P.N ^ (τ + 2)) ^ 3 =
      P.N ^ (3 * (τ + 2)) := by
    calc
      (P.N ^ (τ + 2)) ^ 3 = P.N ^ ((τ + 2) * (3 : ℝ)) := by
        rw [Real.rpow_mul hNNonneg]
        exact (Real.rpow_natCast (P.N ^ (τ + 2)) 3).symm
      _ = P.N ^ (3 * (τ + 2)) := by ring_nf
  have hEnergyUpper : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      P.N ^ (3 * τ + 8) := by
    calc
      (finsetAdditiveEnergy P.ordinates : ℝ) ≤
          3 * (P.ordinates.card : ℝ) ^ 3 := hEnergyCombinatorial
      _ ≤ 3 * (P.N ^ (τ + 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left hCardCube (by norm_num)
      _ ≤ P.N ^ 2 * (P.N ^ (τ + 2)) ^ 3 :=
        mul_le_mul_of_nonneg_right hThree (by positivity)
      _ = P.N ^ (3 * τ + 8) := by
        rw [hCardPowerCube, ← Real.rpow_natCast P.N 2,
          ← Real.rpow_add hNPos]
        congr 1
        ring
  have hIndexSquare : (P.indices.card : ℝ) ^ 2 ≤ 4 * P.N ^ 2 := by
    calc
      (P.indices.card : ℝ) ^ 2 ≤ (2 * P.N) ^ 2 :=
        (sq_le_sq₀ (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) hNNonneg)).2
            P.indices_card_cast_le_two_mul_N
      _ = 4 * P.N ^ 2 := by ring
  have hFour : (4 : ℝ) ≤ P.N ^ 2 := by nlinarith
  have hSumUpper : doubleZetaSum P ≤ P.N ^ (2 * τ + 8) := by
    calc
      doubleZetaSum P ≤ (P.ordinates.card : ℝ) ^ 2 *
          (P.indices.card : ℝ) ^ 2 := doubleZetaSum_card_upper P
      _ ≤ (P.N ^ (τ + 2)) ^ 2 * (4 * P.N ^ 2) :=
        mul_le_mul hCardSquare hIndexSquare (sq_nonneg _) (sq_nonneg _)
      _ = 4 * ((P.N ^ (τ + 2)) ^ 2 * P.N ^ 2) := by ring
      _ ≤ P.N ^ 2 * ((P.N ^ (τ + 2)) ^ 2 * P.N ^ 2) :=
        mul_le_mul_of_nonneg_right hFour (by positivity)
      _ = P.N ^ (2 * τ + 8) := by
        rw [hCardPowerSquare, ← Real.rpow_natCast P.N 2,
          ← Real.rpow_add hNPos, ← Real.rpow_add hNPos]
        congr 1
        ring
  have hCardNatPos : 0 < P.ordinates.card := by exact_mod_cast hCardPos
  have hEnergyNatPos : 0 < finsetAdditiveEnergy P.ordinates := by
    exact_mod_cast hEnergyPos
  have hCardOne : (1 : ℝ) ≤ P.ordinates.card := by
    exact_mod_cast hCardNatPos
  have hEnergyOne : (1 : ℝ) ≤ finsetAdditiveEnergy P.ordinates := by
    exact_mod_cast hEnergyNatPos
  have hIndexOne : (1 : ℝ) ≤ P.indices.card := by
    rw [P.indices_card]
    norm_num
  have hSumOne : 1 ≤ doubleZetaSum P := by
    calc
      (1 : ℝ) ≤ (P.ordinates.card : ℝ) *
          (P.indices.card : ℝ) ^ 2 := by nlinarith [sq_nonneg (P.indices.card : ℝ)]
      _ ≤ doubleZetaSum P := doubleZetaSum_diagonal_lower P
  refine ⟨?_, ?_⟩
  · exact ⟨Real.logb_nonneg P.one_lt_N hCardOne,
      Real.logb_nonneg P.one_lt_N hEnergyOne,
      Real.logb_nonneg P.one_lt_N hSumOne⟩
  · exact ⟨(Real.logb_le_iff_le_rpow P.one_lt_N hCardPos).2 hCardUpper,
      (Real.logb_le_iff_le_rpow P.one_lt_N hEnergyPos).2 hEnergyUpper,
      (Real.logb_le_iff_le_rpow P.one_lt_N hSumPos).2 hSumUpper⟩

/-- A bounded counterexample family to a proposed energy exponent produces
a feasible point whose energy coordinate is at least the counterexample
exponent.  This is the compactness core of the reverse supremum argument. -/
theorem energyRegion_exists_of_counterexampleFamily
    {σ τ B η : ℝ}
    (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (P : ℕ → LargeValuePattern) (err : ℕ → ℝ)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (herrPos : ∀ n, 0 < err n)
    (herrZero : Tendsto err atTop (nhds 0))
    (hT : ∀ n,
      (P n).N ^ (τ - err n) ≤ (P n).T ∧
        (P n).T ≤ (P n).N ^ (τ + err n))
    (hV : ∀ n,
      (P n).N ^ (σ - err n) ≤ (P n).V ∧
        (P n).V ≤ (P n).N ^ (σ + err n))
    (hCardPos : ∀ n, 0 < ((P n).ordinates.card : ℝ))
    (hEnergyPos : ∀ n,
      0 < (finsetAdditiveEnergy (P n).ordinates : ℝ))
    (hSumPos : ∀ n, 0 < doubleZetaSum (P n))
    (upper : ℝ × ℝ × ℝ)
    (hbounded : ∀ n,
      energyLogCoordinates (P n) ∈ Icc (0, 0, 0) upper)
    (hEnergyLower : ∀ n,
      (P n).N ^ (B + η) ≤
        (finsetAdditiveEnergy (P n).ordinates : ℝ)) :
    ∃ ρ ρstar s : ℝ,
      InLargeValueEnergyRegion σ τ ρ ρstar s ∧ B + η ≤ ρstar := by
  obtain ⟨x, hx, φ, hφMono, hxLimit⟩ :=
    isCompact_Icc.tendsto_subseq hbounded
  have hφTop : Tendsto φ atTop atTop := hφMono.tendsto_atTop
  have hRhoLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n))).1) atTop (nhds x.1) := by
    simpa [Function.comp_def] using
      (continuous_fst.tendsto x).comp hxLimit
  have hRhoStarLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n))).2.1) atTop
        (nhds x.2.1) := by
    simpa [Function.comp_def] using
      ((continuous_fst.comp continuous_snd).tendsto x).comp hxLimit
  have hSumLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n))).2.2) atTop
        (nhds x.2.2) := by
    simpa [Function.comp_def] using
      ((continuous_snd.comp continuous_snd).tendsto x).comp hxLimit
  have herrInfinitesimal :
      Expdb.VariableObject.IsInfinitesimal
        (fun n => err (φ n) : Expdb.VariableObject ℝ) := by
    rw [Expdb.VariableObject.IsInfinitesimal]
    have hzero := herrZero.comp hφTop
    simpa [Real.norm_eq_abs] using
      (continuous_abs.tendsto 0).comp hzero
  have hNSubTop : Tendsto (fun n => (P (φ n)).N) atTop atTop :=
    hNtop.comp hφTop
  have hTAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (P (φ n)).T) (fun n => (P (φ n)).N) τ := by
    exact Expdb.isPowerAsymptotic_of_between
      (fun n => (P (φ n)).one_lt_N)
      (fun n => (P (φ n)).T_pos)
      (fun n => (herrPos (φ n)).le) herrInfinitesimal
      (fun n => hT (φ n))
  have hVAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (P (φ n)).V) (fun n => (P (φ n)).N) σ := by
    exact Expdb.isPowerAsymptotic_of_between
      (fun n => (P (φ n)).one_lt_N)
      (fun n => (P (φ n)).V_pos)
      (fun n => (herrPos (φ n)).le) herrInfinitesimal
      (fun n => hV (φ n))
  have hCardAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => ((P (φ n)).ordinates.card : ℝ))
      (fun n => (P (φ n)).N) x.1 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hCardPos (φ n))
    simpa [energyLogCoordinates] using hRhoLimit
  have hEnergyAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (finsetAdditiveEnergy (P (φ n)).ordinates : ℝ))
      (fun n => (P (φ n)).N) x.2.1 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hEnergyPos (φ n))
    simpa [energyLogCoordinates] using hRhoStarLimit
  have hSumAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => doubleZetaSum (P (φ n)))
      (fun n => (P (φ n)).N) x.2.2 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hSumPos (φ n))
    simpa [energyLogCoordinates] using hSumLimit
  have hRhoNonneg : 0 ≤ x.1 := hx.1.1
  have hRhoStarNonneg : 0 ≤ x.2.1 := hx.1.2.1
  have hB : B + η ≤ x.2.1 := by
    apply ge_of_tendsto' hRhoStarLimit
    intro n
    apply (Real.le_logb_iff_rpow_le
      (P (φ n)).one_lt_N (hEnergyPos (φ n))).2
    exact hEnergyLower (φ n)
  refine ⟨x.1, x.2.1, x.2.2, ?_, hB⟩
  apply inLargeValueEnergyRegionAsymptotic_iff.mp
  exact ⟨hσLower, hσUpper, hτ, hRhoNonneg, hRhoStarNonneg,
    ⟨fun n => P (φ n), hNSubTop, hTAsymptotic, hVAsymptotic,
      hCardAsymptotic, hEnergyAsymptotic, hSumAsymptotic⟩⟩

/-- Zeta-restricted version of the common-subsequence compactness theorem. -/
theorem zetaEnergyRegion_exists_of_counterexampleFamily
    {σ τ B η : ℝ}
    (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (P : ℕ → ZetaLargeValuePattern) (err : ℕ → ℝ)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (herrPos : ∀ n, 0 < err n)
    (herrZero : Tendsto err atTop (nhds 0))
    (hT : ∀ n,
      (P n).N ^ (τ - err n) ≤ (P n).T ∧
        (P n).T ≤ (P n).N ^ (τ + err n))
    (hV : ∀ n,
      (P n).N ^ (σ - err n) ≤ (P n).V ∧
        (P n).V ≤ (P n).N ^ (σ + err n))
    (hCardPos : ∀ n, 0 < ((P n).ordinates.card : ℝ))
    (hEnergyPos : ∀ n,
      0 < (finsetAdditiveEnergy (P n).ordinates : ℝ))
    (hSumPos : ∀ n, 0 < doubleZetaSum (P n).toLargeValuePattern)
    (upper : ℝ × ℝ × ℝ)
    (hbounded : ∀ n,
      energyLogCoordinates (P n).toLargeValuePattern ∈ Icc (0, 0, 0) upper)
    (hEnergyLower : ∀ n,
      (P n).N ^ (B + η) ≤
        (finsetAdditiveEnergy (P n).ordinates : ℝ)) :
    ∃ ρ ρstar s : ℝ,
      InZetaLargeValueEnergyRegion σ τ ρ ρstar s ∧
        B + η ≤ ρstar := by
  obtain ⟨x, hx, φ, hφMono, hxLimit⟩ :=
    isCompact_Icc.tendsto_subseq hbounded
  have hφTop : Tendsto φ atTop atTop := hφMono.tendsto_atTop
  have hRhoLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n)).toLargeValuePattern).1)
        atTop (nhds x.1) := by
    simpa [Function.comp_def] using
      (continuous_fst.tendsto x).comp hxLimit
  have hRhoStarLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n)).toLargeValuePattern).2.1)
        atTop (nhds x.2.1) := by
    simpa [Function.comp_def] using
      ((continuous_fst.comp continuous_snd).tendsto x).comp hxLimit
  have hSumLimit : Tendsto
      (fun n => (energyLogCoordinates (P (φ n)).toLargeValuePattern).2.2)
        atTop (nhds x.2.2) := by
    simpa [Function.comp_def] using
      ((continuous_snd.comp continuous_snd).tendsto x).comp hxLimit
  have herrInfinitesimal :
      Expdb.VariableObject.IsInfinitesimal
        (fun n => err (φ n) : Expdb.VariableObject ℝ) := by
    rw [Expdb.VariableObject.IsInfinitesimal]
    have hzero := herrZero.comp hφTop
    simpa [Real.norm_eq_abs] using (continuous_abs.tendsto 0).comp hzero
  have hNSubTop : Tendsto (fun n => (P (φ n)).N) atTop atTop :=
    hNtop.comp hφTop
  have hTAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (P (φ n)).T) (fun n => (P (φ n)).N) τ :=
    Expdb.isPowerAsymptotic_of_between
      (fun n => (P (φ n)).one_lt_N) (fun n => (P (φ n)).T_pos)
      (fun n => (herrPos (φ n)).le) herrInfinitesimal
      (fun n => hT (φ n))
  have hVAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (P (φ n)).V) (fun n => (P (φ n)).N) σ :=
    Expdb.isPowerAsymptotic_of_between
      (fun n => (P (φ n)).one_lt_N) (fun n => (P (φ n)).V_pos)
      (fun n => (herrPos (φ n)).le) herrInfinitesimal
      (fun n => hV (φ n))
  have hCardAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => ((P (φ n)).ordinates.card : ℝ))
      (fun n => (P (φ n)).N) x.1 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hCardPos (φ n))
    simpa [energyLogCoordinates] using hRhoLimit
  have hEnergyAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => (finsetAdditiveEnergy (P (φ n)).ordinates : ℝ))
      (fun n => (P (φ n)).N) x.2.1 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hEnergyPos (φ n))
    simpa [energyLogCoordinates] using hRhoStarLimit
  have hSumAsymptotic : Expdb.IsPowerAsymptotic
      (fun n => doubleZetaSum (P (φ n)).toLargeValuePattern)
      (fun n => (P (φ n)).N) x.2.2 := by
    apply Expdb.isPowerAsymptotic_of_logb_tendsto
      (Filter.Eventually.of_forall fun n => (P (φ n)).one_lt_N)
      (Filter.Eventually.of_forall fun n => hSumPos (φ n))
    simpa [energyLogCoordinates] using hSumLimit
  have hB : B + η ≤ x.2.1 := by
    apply ge_of_tendsto' hRhoStarLimit
    intro n
    apply (Real.le_logb_iff_rpow_le
      (P (φ n)).one_lt_N (hEnergyPos (φ n))).2
    exact hEnergyLower (φ n)
  refine ⟨x.1, x.2.1, x.2.2, ?_, hB⟩
  apply inZetaLargeValueEnergyRegionAsymptotic_iff.mp
  exact ⟨hσLower, hσUpper, hτ, hx.1.1, hx.1.2.1,
    ⟨fun n => P (φ n), hNSubTop, hTAsymptotic, hVAsymptotic,
      hCardAsymptotic, hEnergyAsymptotic, hSumAsymptotic⟩⟩

/-- Failure of a proposed uniform energy bound yields a feasible region point
with strictly larger energy coordinate. -/
theorem energyRegion_exists_rhoStar_gt_of_not_bound
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) (hnot : ¬ IsLargeValueEnergyBound σ τ B) :
    ∃ ρ ρstar s : ℝ,
      InLargeValueEnergyRegion σ τ ρ ρstar s ∧ B < ρstar := by
  rw [IsLargeValueEnergyBound] at hnot
  push Not at hnot
  obtain ⟨η, hη, hfail⟩ := hnot
  let err : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrPos (n : ℕ) : 0 < err n := by
    dsimp [err]
    positivity
  have herrOne (n : ℕ) : err n ≤ 1 := by
    dsimp [err]
    exact (div_le_one (by positivity)).2 (by norm_num)
  have herrZero : Tendsto err atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hexists (n : ℕ) : ∃ P : LargeValuePattern,
      ((n : ℝ) + 2) ≤ P.N ∧
      P.N ^ (τ - err n) ≤ P.T ∧
      P.T ≤ P.N ^ (τ + err n) ∧
      P.N ^ (σ - err n) ≤ P.V ∧
      P.V ≤ P.N ^ (σ + err n) ∧
      ((n : ℝ) + 2) * P.N ^ (B + η) <
        (finsetAdditiveEnergy P.ordinates : ℝ) := by
    exact hfail ((n : ℝ) + 2) (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith) (err n) (herrPos n)
  let P : ℕ → LargeValuePattern := fun n => Classical.choose (hexists n)
  have hP (n : ℕ) :
      ((n : ℝ) + 2) ≤ (P n).N ∧
      (P n).N ^ (τ - err n) ≤ (P n).T ∧
      (P n).T ≤ (P n).N ^ (τ + err n) ∧
      (P n).N ^ (σ - err n) ≤ (P n).V ∧
      (P n).V ≤ (P n).N ^ (σ + err n) ∧
      ((n : ℝ) + 2) * (P n).N ^ (B + η) <
        (finsetAdditiveEnergy (P n).ordinates : ℝ) :=
    Classical.choose_spec (hexists n)
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun n => (hP n).1)
    exact tendsto_atTop_add_const_right atTop 2
      tendsto_natCast_atTop_atTop
  have hCardPos (n : ℕ) : 0 < ((P n).ordinates.card : ℝ) := by
    have hEnergyPositive :
        0 < (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
      have hProductPositive :
          0 < ((n : ℝ) + 2) * (P n).N ^ (B + η) :=
        mul_pos (by positivity) (Real.rpow_pos_of_pos
          (lt_trans zero_lt_one (P n).one_lt_N) _)
      exact hProductPositive.trans (hP n).2.2.2.2.2
    have hEnergyNat : 0 < finsetAdditiveEnergy (P n).ordinates := by
      exact_mod_cast hEnergyPositive
    have hUpper := finset_additiveEnergy_le_three_mul_cube
      (P n).ordinates (P n).ordinates_oneSeparated
    have : 0 < (P n).ordinates.card := by
      by_contra hcard
      have hcardZero : (P n).ordinates.card = 0 := Nat.eq_zero_of_not_pos hcard
      rw [hcardZero] at hUpper
      norm_num at hUpper
      omega
    exact_mod_cast this
  have hEnergyPos (n : ℕ) :
      0 < (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
    have hProductPositive :
        0 < ((n : ℝ) + 2) * (P n).N ^ (B + η) :=
      mul_pos (by positivity) (Real.rpow_pos_of_pos
        (lt_trans zero_lt_one (P n).one_lt_N) _)
    exact hProductPositive.trans (hP n).2.2.2.2.2
  have hSumPos (n : ℕ) : 0 < doubleZetaSum (P n) := by
    have hdiag := doubleZetaSum_diagonal_lower (P n)
    have hIndex : 0 < ((P n).indices.card : ℝ) := by
      rw [(P n).indices_card]
      positivity
    exact (mul_pos (hCardPos n) (sq_pos_of_pos hIndex)).trans_le hdiag
  have hEnergyLower (n : ℕ) :
      (P n).N ^ (B + η) ≤
        (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
    have hFactor : 1 ≤ (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact le_trans
      (le_mul_of_one_le_left (Real.rpow_nonneg
        (zero_le_one.trans (P n).one_lt_N.le) _) hFactor)
      (hP n).2.2.2.2.2.le
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    energyRegion_exists_of_counterexampleFamily
      hσLower hσUpper hτ P err hNtop herrPos herrZero
      (fun n => ⟨(hP n).2.1, (hP n).2.2.1⟩)
      (fun n => ⟨(hP n).2.2.2.1, (hP n).2.2.2.2.1⟩)
      hCardPos hEnergyPos hSumPos
      (τ + 2, 3 * τ + 8, 2 * τ + 8)
      (fun n => energyLogCoordinates_mem_box (P n) hτ (herrPos n)
        (herrOne n) (by linarith [(hP n).1]) (hP n).2.2.1
        (hCardPos n) (hEnergyPos n) (hSumPos n))
      hEnergyLower
  exact ⟨ρ, ρstar, s, hregion, lt_of_lt_of_le (by linarith) hB⟩

/-- On the source domain, the energy exponent is at most the supremum of the
energy coordinates in the feasible region. -/
theorem largeValueEnergyExponent_le_largeValueEnergyRegionSupremum
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    largeValueEnergyExponent σ τ ≤
      largeValueEnergyRegionSupremum σ τ := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hSupB
  apply largeValueEnergyExponent_le_of_bound
  by_contra hnot
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    energyRegion_exists_rhoStar_gt_of_not_bound
      hσLower hσUpper hτ hnot
  have hRhoStarSup : (ρstar : EReal) ≤
      largeValueEnergyRegionSupremum σ τ := by
    apply le_sSup
    exact ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  have hBRhoStar : (B : EReal) < (ρstar : EReal) :=
    EReal.coe_lt_coe_iff.mpr hB
  exact (not_lt_of_ge hRhoStarSup) (hSupB.trans hBRhoStar)

/-- The general energy large-value exponent equals the feasible-region
supremum on the source domain. -/
theorem largeValueEnergyExponent_eq_regionSupremum
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    largeValueEnergyExponent σ τ =
      largeValueEnergyRegionSupremum σ τ :=
  le_antisymm
    (largeValueEnergyExponent_le_largeValueEnergyRegionSupremum
      hσLower hσUpper hτ)
    (largeValueEnergyRegionSupremum_le_largeValueEnergyExponent σ τ)

/-- Failure of a proposed zeta-restricted energy bound yields a zeta feasible
point with strictly larger energy coordinate. -/
theorem zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) (hnot : ¬ IsZetaLargeValueEnergyBound σ τ B) :
    ∃ ρ ρstar s : ℝ,
      InZetaLargeValueEnergyRegion σ τ ρ ρstar s ∧ B < ρstar := by
  rw [IsZetaLargeValueEnergyBound] at hnot
  push Not at hnot
  obtain ⟨η, hη, hfail⟩ := hnot
  let err : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrPos (n : ℕ) : 0 < err n := by
    dsimp [err]
    positivity
  have herrOne (n : ℕ) : err n ≤ 1 := by
    dsimp [err]
    exact (div_le_one (by positivity)).2 (by norm_num)
  have herrZero : Tendsto err atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hexists (n : ℕ) : ∃ P : ZetaLargeValuePattern,
      ((n : ℝ) + 2) ≤ P.N ∧
      P.N ^ (τ - err n) ≤ P.T ∧
      P.T ≤ P.N ^ (τ + err n) ∧
      P.N ^ (σ - err n) ≤ P.V ∧
      P.V ≤ P.N ^ (σ + err n) ∧
      ((n : ℝ) + 2) * P.N ^ (B + η) <
        (finsetAdditiveEnergy P.ordinates : ℝ) := by
    exact hfail ((n : ℝ) + 2) (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith) (err n) (herrPos n)
  let P : ℕ → ZetaLargeValuePattern := fun n => Classical.choose (hexists n)
  have hP (n : ℕ) :
      ((n : ℝ) + 2) ≤ (P n).N ∧
      (P n).N ^ (τ - err n) ≤ (P n).T ∧
      (P n).T ≤ (P n).N ^ (τ + err n) ∧
      (P n).N ^ (σ - err n) ≤ (P n).V ∧
      (P n).V ≤ (P n).N ^ (σ + err n) ∧
      ((n : ℝ) + 2) * (P n).N ^ (B + η) <
        (finsetAdditiveEnergy (P n).ordinates : ℝ) :=
    Classical.choose_spec (hexists n)
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun n => (hP n).1)
    exact tendsto_atTop_add_const_right atTop 2
      tendsto_natCast_atTop_atTop
  have hEnergyPos (n : ℕ) :
      0 < (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
    have hProductPositive :
        0 < ((n : ℝ) + 2) * (P n).N ^ (B + η) :=
      mul_pos (by positivity) (Real.rpow_pos_of_pos
        (lt_trans zero_lt_one (P n).one_lt_N) _)
    exact hProductPositive.trans (hP n).2.2.2.2.2
  have hCardPos (n : ℕ) : 0 < ((P n).ordinates.card : ℝ) := by
    have hEnergyNat : 0 < finsetAdditiveEnergy (P n).ordinates := by
      exact_mod_cast hEnergyPos n
    have hUpper := finset_additiveEnergy_le_three_mul_cube
      (P n).ordinates (P n).ordinates_oneSeparated
    have hCardNat : 0 < (P n).ordinates.card := by
      by_contra hcard
      have hcardZero : (P n).ordinates.card = 0 := Nat.eq_zero_of_not_pos hcard
      rw [hcardZero] at hUpper
      norm_num at hUpper
      omega
    exact_mod_cast hCardNat
  have hSumPos (n : ℕ) :
      0 < doubleZetaSum (P n).toLargeValuePattern := by
    have hdiag := doubleZetaSum_diagonal_lower (P n).toLargeValuePattern
    have hIndex : 0 < ((P n).indices.card : ℝ) := by
      rw [(P n).toLargeValuePattern.indices_card]
      positivity
    exact (mul_pos (hCardPos n) (sq_pos_of_pos hIndex)).trans_le hdiag
  have hEnergyLower (n : ℕ) :
      (P n).N ^ (B + η) ≤
        (finsetAdditiveEnergy (P n).ordinates : ℝ) := by
    have hFactor : 1 ≤ (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact le_trans
      (le_mul_of_one_le_left (Real.rpow_nonneg
        (zero_le_one.trans (P n).one_lt_N.le) _) hFactor)
      (hP n).2.2.2.2.2.le
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    zetaEnergyRegion_exists_of_counterexampleFamily
      hσLower hσUpper hτ P err hNtop herrPos herrZero
      (fun n => ⟨(hP n).2.1, (hP n).2.2.1⟩)
      (fun n => ⟨(hP n).2.2.2.1, (hP n).2.2.2.2.1⟩)
      hCardPos hEnergyPos hSumPos
      (τ + 2, 3 * τ + 8, 2 * τ + 8)
      (fun n => energyLogCoordinates_mem_box (P n).toLargeValuePattern
        hτ (herrPos n) (herrOne n) (by linarith [(hP n).1])
        (hP n).2.2.1 (hCardPos n) (hEnergyPos n) (hSumPos n))
      hEnergyLower
  exact ⟨ρ, ρstar, s, hregion, lt_of_lt_of_le (by linarith) hB⟩

/-- On the source domain, the zeta-restricted energy exponent is at most the
supremum of the zeta feasible-region energy coordinates. -/
theorem zetaLargeValueEnergyExponent_le_zetaLargeValueEnergyRegionSupremum
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    zetaLargeValueEnergyExponent σ τ ≤
      zetaLargeValueEnergyRegionSupremum σ τ := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hSupB
  apply zetaLargeValueEnergyExponent_le_of_bound
  by_contra hnot
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
      hσLower hσUpper hτ hnot
  have hRhoStarSup : (ρstar : EReal) ≤
      zetaLargeValueEnergyRegionSupremum σ τ := by
    apply le_sSup
    exact ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  have hBRhoStar : (B : EReal) < (ρstar : EReal) :=
    EReal.coe_lt_coe_iff.mpr hB
  exact (not_lt_of_ge hRhoStarSup) (hSupB.trans hBRhoStar)

/-- The zeta-restricted energy large-value exponent equals its
feasible-region supremum on the source domain. -/
theorem zetaLargeValueEnergyExponent_eq_regionSupremum
    {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    zetaLargeValueEnergyExponent σ τ =
      zetaLargeValueEnergyRegionSupremum σ τ :=
  le_antisymm
    (zetaLargeValueEnergyExponent_le_zetaLargeValueEnergyRegionSupremum
      hσLower hσUpper hτ)
    (zetaLargeValueEnergyRegionSupremum_le_zetaLargeValueEnergyExponent σ τ)

end TaoTrudgianYang2025
