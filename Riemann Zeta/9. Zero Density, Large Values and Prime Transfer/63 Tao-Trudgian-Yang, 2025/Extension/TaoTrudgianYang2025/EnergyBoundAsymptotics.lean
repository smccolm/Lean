import TaoTrudgianYang2025.EnergyRegionAsymptotics

/-!
# Asymptotic interfaces for large-value energy bounds

This module identifies the installed fixed-parameter epsilon--delta bounds
with the paper's statement about every unbounded family of large-value
patterns.  A failed uniform estimate is diagonalized into one counterexample
family; conversely, a uniform estimate applies eventually along every family.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

private def IsEnergyBoundAsymptoticFor {ι : Type*}
    (N T V energy : ι → ℝ) (σ τ ρstar : ℝ) : Prop :=
  ∀ P : ℕ → ι,
    Expdb.VariableObject.IsUnbounded (fun n => N (P n)) →
    Expdb.IsPowerAsymptotic (fun n => T (P n)) (fun n => N (P n)) τ →
    Expdb.IsPowerAsymptotic (fun n => V (P n)) (fun n => N (P n)) σ →
    Expdb.IsPowerBounded (fun n => energy (P n))
      (fun n => N (P n)) ρstar

private def IsEnergyBoundNonAsymptoticFor {ι : Type*}
    (N T V energy : ι → ℝ) (σ τ ρstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ p : ι,
          C ≤ N p →
          N p ^ (τ - δ) ≤ T p →
          T p ≤ N p ^ (τ + δ) →
          N p ^ (σ - δ) ≤ V p →
          V p ≤ N p ^ (σ + δ) →
          energy p ≤ C * N p ^ (ρstar + ε)

private theorem isEnergyBoundAsymptoticFor_iff_nonAsymptotic
    {ι : Type*} {N T V energy : ι → ℝ} {σ τ ρstar : ℝ}
    (hN : ∀ p, 1 < N p) (henergy : ∀ p, 0 ≤ energy p) :
    IsEnergyBoundAsymptoticFor N T V energy σ τ ρstar ↔
      IsEnergyBoundNonAsymptoticFor N T V energy σ τ ρstar := by
  constructor
  · intro hasymptotic
    by_contra hfailure
    rw [IsEnergyBoundNonAsymptoticFor] at hfailure
    push Not at hfailure
    obtain ⟨ε, hε, hfailure⟩ := hfailure
    let err : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let threshold : ℕ → ℝ := fun n => (n : ℝ) + 2
    have herrPos (n : ℕ) : 0 < err n := by
      dsimp [err]
      positivity
    have hthresholdOne (n : ℕ) : 1 ≤ threshold n := by
      dsimp [threshold]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    choose P hP using fun n =>
      hfailure (threshold n) (hthresholdOne n) (err n) (herrPos n)
    have hbase (n : ℕ) : 1 < N (P n) := hN (P n)
    have hbaseOne (n : ℕ) : 1 ≤ N (P n) := (hbase n).le
    have herrNonneg (n : ℕ) : 0 ≤ err n := (herrPos n).le
    have herrInfinitesimal :
        Expdb.VariableObject.IsInfinitesimal
          (err : Expdb.VariableObject ℝ) := by
      rw [Expdb.VariableObject.IsInfinitesimal]
      have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [err, Real.norm_eq_abs, abs_of_nonneg (herrNonneg _)] using hlim
    have hTpos (n : ℕ) : 0 < T (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).2.1
    have hVpos (n : ℕ) : 0 < V (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).2.2.2.1
    have hTAsymptotic : Expdb.IsPowerAsymptotic
        (fun n => T (P n)) (fun n => N (P n)) τ :=
      Expdb.isPowerAsymptotic_of_between hbase hTpos herrNonneg
        herrInfinitesimal
        (fun n => ⟨(hP n).2.1, (hP n).2.2.1⟩)
    have hVAsymptotic : Expdb.IsPowerAsymptotic
        (fun n => V (P n)) (fun n => N (P n)) σ :=
      Expdb.isPowerAsymptotic_of_between hbase hVpos herrNonneg
        herrInfinitesimal
        (fun n => ⟨(hP n).2.2.2.1, (hP n).2.2.2.2.1⟩)
    have hNUnbounded : Expdb.VariableObject.IsUnbounded
        (fun n => N (P n)) := by
      apply (Expdb.VariableObject.isUnbounded_iff_forall_eventually_norm_ge
        (fun n => N (P n))).2
      intro D
      obtain ⟨j : ℕ, hj : D ≤ (j : ℝ)⟩ := exists_nat_ge D
      filter_upwards [eventually_ge_atTop j] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (hbase n).le)]
      calc
        D ≤ (j : ℝ) := hj
        _ ≤ (n : ℝ) := by exact_mod_cast hn
        _ ≤ threshold n := by dsimp [threshold]; linarith
        _ ≤ N (P n) := (hP n).1
    have hpower := hasymptotic P hNUnbounded hTAsymptotic hVAsymptotic
    have hbigO := (Expdb.isPowerBounded_iff_forall_pos
      (fun n => energy (P n)) (fun n => N (P n)) ρstar
      hbaseOne hNUnbounded).mp hpower (ε / 2) (by linarith)
    obtain ⟨K, hK⟩ := hbigO.bound
    have hKthreshold : ∀ᶠ n in atTop, K ≤ threshold n := by
      obtain ⟨j : ℕ, hj : K ≤ (j : ℝ)⟩ := exists_nat_ge K
      filter_upwards [eventually_ge_atTop j] with n hn
      calc
        K ≤ (j : ℝ) := hj
        _ ≤ (n : ℝ) := by exact_mod_cast hn
        _ ≤ threshold n := by dsimp [threshold]; linarith
    obtain ⟨n, hnBigO, hnThreshold⟩ := (hK.and hKthreshold).exists
    have henergyBound : energy (P n) ≤
        K * N (P n) ^ (ρstar + ε / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (henergy (P n)),
        abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hbase n).le) _)]
        using hnBigO
    have hdominated : energy (P n) ≤
        threshold n * N (P n) ^ (ρstar + ε) := by
      calc
        energy (P n) ≤ K * N (P n) ^ (ρstar + ε / 2) := henergyBound
        _ ≤ threshold n * N (P n) ^ (ρstar + ε / 2) := by
          exact mul_le_mul_of_nonneg_right hnThreshold
            (Real.rpow_nonneg (zero_le_one.trans (hbase n).le) _)
        _ ≤ threshold n * N (P n) ^ (ρstar + ε) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (hbaseOne n) (by linarith))
            (zero_le_one.trans (hthresholdOne n))
    exact (not_lt_of_ge hdominated) (hP n).2.2.2.2.2
  · intro hnonAsymptotic P hNUnbounded hTAsymptotic hVAsymptotic
    apply (Expdb.isPowerBounded_iff_forall_pos
      (fun n => energy (P n)) (fun n => N (P n)) ρstar
      (fun n => (hN (P n)).le) hNUnbounded).2
    intro ε hε
    obtain ⟨C, hC, δ, hδ, hbound⟩ := hnonAsymptotic ε hε
    have hbase : ∀ᶠ n in atTop, 1 ≤ N (P n) :=
      Filter.Eventually.of_forall fun n => (hN (P n)).le
    have hthreshold : ∀ᶠ n in atTop, C ≤ N (P n) := by
      have hnorm :=
        (Expdb.VariableObject.isUnbounded_iff_forall_eventually_norm_ge
          (fun n => N (P n))).mp hNUnbounded C
      filter_upwards [hnorm] with n hn
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans (hN (P n)).le)] using hn
    have hTbounds := hTAsymptotic.eventually_between hbase hδ
    have hVbounds := hVAsymptotic.eventually_between hbase hδ
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hthreshold, hTbounds, hVbounds] with n hn hTn hVn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (henergy (P n)),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hN (P n)).le) _)]
      using hbound (P n) hn hTn.1 hTn.2 hVn.1 hVn.2

/-- The paper's asymptotic general large-value energy bound: every unbounded
family with `T = N^(τ+o(1))` and `V = N^(σ+o(1))` has energy
`≪ N^(ρ*+o(1))`. -/
def IsLargeValueEnergyBoundAsymptotic (σ τ ρstar : ℝ) : Prop :=
  IsEnergyBoundAsymptoticFor
    LargeValuePattern.N LargeValuePattern.T LargeValuePattern.V
    (fun P => (finsetAdditiveEnergy P.ordinates : ℝ)) σ τ ρstar

/-- The asymptotic and epsilon--delta general energy bounds are equivalent. -/
theorem isLargeValueEnergyBoundAsymptotic_iff
    {σ τ ρstar : ℝ} :
    IsLargeValueEnergyBoundAsymptotic σ τ ρstar ↔
      IsLargeValueEnergyBound σ τ ρstar := by
  change IsEnergyBoundAsymptoticFor _ _ _ _ σ τ ρstar ↔
    IsEnergyBoundNonAsymptoticFor _ _ _ _ σ τ ρstar
  exact isEnergyBoundAsymptoticFor_iff_nonAsymptotic
    (fun P => P.one_lt_N) (fun P => by positivity)

/-- The paper's asymptotic zeta-restricted large-value energy bound. -/
def IsZetaLargeValueEnergyBoundAsymptotic (σ τ ρstar : ℝ) : Prop :=
  IsEnergyBoundAsymptoticFor
    (fun P : ZetaLargeValuePattern => P.N)
    (fun P : ZetaLargeValuePattern => P.T)
    (fun P : ZetaLargeValuePattern => P.V)
    (fun P : ZetaLargeValuePattern =>
      (finsetAdditiveEnergy P.ordinates : ℝ)) σ τ ρstar

/-- The asymptotic and epsilon--delta zeta energy bounds are equivalent. -/
theorem isZetaLargeValueEnergyBoundAsymptotic_iff
    {σ τ ρstar : ℝ} :
    IsZetaLargeValueEnergyBoundAsymptotic σ τ ρstar ↔
      IsZetaLargeValueEnergyBound σ τ ρstar := by
  change IsEnergyBoundAsymptoticFor _ _ _ _ σ τ ρstar ↔
    IsEnergyBoundNonAsymptoticFor _ _ _ _ σ τ ρstar
  exact isEnergyBoundAsymptoticFor_iff_nonAsymptotic
    (fun P => P.one_lt_N) (fun P => by positivity)

/-- The filter-at-infinity formulation of a shifted zero-density energy
bound.  The shift may depend on the requested exponent accuracy, matching the
paper's infinitesimal-shift convention. -/
def IsZeroDensityEnergyBoundAsymptotic (σ Astar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ => (zeroAdditiveEnergy (σ - δ) T : ℝ))
        (fun T : ℝ => T ^ (Astar * (1 - σ) + ε))

/-- The filter-at-infinity and fixed-threshold formulations of a shifted
zero-density energy bound are equivalent. -/
theorem isZeroDensityEnergyBoundAsymptotic_iff
    {σ Astar : ℝ} :
    IsZeroDensityEnergyBoundAsymptotic σ Astar ↔
      IsZeroDensityEnergyBound σ Astar := by
  constructor
  · intro hasymptotic ε hε
    obtain ⟨δ, hδ, hbigO⟩ := hasymptotic ε hε
    obtain ⟨K, hKpos, hK⟩ := hbigO.exists_pos
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hK.bound
    let C : ℝ := max 1 (max K T₀)
    have hC : 1 ≤ C := le_max_left _ _
    have hKC : K ≤ C := (le_max_left K T₀).trans (le_max_right 1 _)
    have hT₀C : T₀ ≤ C := (le_max_right K T₀).trans (le_max_right 1 _)
    refine ⟨C, hC, δ, hδ, ?_⟩
    intro T hCT
    have hT₀T : T₀ ≤ T := hT₀C.trans hCT
    have hraw := hT₀ T hT₀T
    have hTnonneg : 0 ≤ T := zero_le_one.trans (hC.trans hCT)
    have hpowNonneg : 0 ≤ T ^ (Astar * (1 - σ) + ε) :=
      Real.rpow_nonneg hTnonneg _
    have hnormalized : (zeroAdditiveEnergy (σ - δ) T : ℝ) ≤
        K * T ^ (Astar * (1 - σ) + ε) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
          0 ≤ (zeroAdditiveEnergy (σ - δ) T : ℝ)),
        abs_of_nonneg hpowNonneg] using hraw
    exact hnormalized.trans
      (mul_le_mul_of_nonneg_right hKC hpowNonneg)
  · intro hnonAsymptotic ε hε
    obtain ⟨C, hC, δ, hδ, hbound⟩ := hnonAsymptotic ε hε
    refine ⟨δ, hδ, Asymptotics.IsBigO.of_bound C ?_⟩
    filter_upwards [eventually_ge_atTop C] with T hCT
    have hTnonneg : 0 ≤ T := zero_le_one.trans (hC.trans hCT)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (zeroAdditiveEnergy (σ - δ) T : ℝ)),
      abs_of_nonneg (Real.rpow_nonneg hTnonneg _)] using hbound T hCT

end TaoTrudgianYang2025
