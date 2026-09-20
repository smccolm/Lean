import TaoTrudgianYang2025.EnergyRegions
import Expdb.Basic.PowerAsymptotics

/-!
# Asymptotic interfaces for the energy regions

The paper defines its energy regions through unbounded families and then uses
an epsilon--delta formulation.  This module supplies both interfaces and
proves that they are equivalent.  The family retains the actual large-value
patterns, rather than only their six numerical measurements.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- Six measurements of a family have the power asymptotics occurring in the
paper's definition of a large-value energy region. -/
def HasEnergyRegionAsymptotics {ι : Type*}
    (N T V card energy sum : ι → ℝ)
    (τ σ ρ ρstar s : ℝ) : Prop :=
  ∃ P : ℕ → ι,
    Tendsto (fun n => N (P n)) atTop atTop ∧
    Expdb.IsPowerAsymptotic (fun n => T (P n)) (fun n => N (P n)) τ ∧
    Expdb.IsPowerAsymptotic (fun n => V (P n)) (fun n => N (P n)) σ ∧
    Expdb.IsPowerAsymptotic (fun n => card (P n)) (fun n => N (P n)) ρ ∧
    Expdb.IsPowerAsymptotic (fun n => energy (P n)) (fun n => N (P n)) ρstar ∧
    Expdb.IsPowerAsymptotic (fun n => sum (P n)) (fun n => N (P n)) s

private structure EnergyRegionSandwich
    (N T V card energy sum τ σ ρ ρstar s ε δ C : ℝ) : Prop where
  scale : C ≤ N
  timeLower : N ^ (τ - δ) ≤ T
  timeUpper : T ≤ N ^ (τ + δ)
  valueLower : N ^ (σ - δ) ≤ V
  valueUpper : V ≤ N ^ (σ + δ)
  cardLower : N ^ (ρ - ε) ≤ card
  cardUpper : card ≤ N ^ (ρ + ε)
  energyLower : N ^ (ρstar - ε) ≤ energy
  energyUpper : energy ≤ N ^ (ρstar + ε)
  sumLower : N ^ (s - ε) ≤ sum
  sumUpper : sum ≤ N ^ (s + ε)

private def HasEnergyRegionSandwiches {ι : Type*}
    (N T V card energy sum : ι → ℝ)
    (τ σ ρ ρstar s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, 0 < C →
    ∃ p : ι, EnergyRegionSandwich
      (N p) (T p) (V p) (card p) (energy p) (sum p)
      τ σ ρ ρstar s ε δ C

private theorem hasEnergyRegionAsymptotics_iff_sandwiches
    {ι : Type*} {N T V card energy sum : ι → ℝ}
    {τ σ ρ ρstar s : ℝ} (hN : ∀ p, 1 < N p) :
    HasEnergyRegionAsymptotics N T V card energy sum τ σ ρ ρstar s ↔
      HasEnergyRegionSandwiches N T V card energy sum τ σ ρ ρstar s := by
  constructor
  · rintro ⟨P, hNtop, hT, hV, hcard, henergy, hsum⟩
    intro ε hε δ hδ C _
    have hbase : ∀ᶠ n in atTop, 1 ≤ N (P n) :=
      Filter.Eventually.of_forall fun n => (hN (P n)).le
    have hscale : ∀ᶠ n in atTop, C ≤ N (P n) :=
      hNtop.eventually (eventually_ge_atTop C)
    have hTbounds := hT.eventually_between hbase hδ
    have hVbounds := hV.eventually_between hbase hδ
    have hcardBounds := hcard.eventually_between hbase hε
    have henergyBounds := henergy.eventually_between hbase hε
    have hsumBounds := hsum.eventually_between hbase hε
    obtain ⟨n, hn⟩ := (hscale.and <| hTbounds.and <| hVbounds.and <|
      hcardBounds.and <| henergyBounds.and hsumBounds).exists
    exact ⟨P n, {
      scale := hn.1
      timeLower := hn.2.1.1
      timeUpper := hn.2.1.2
      valueLower := hn.2.2.1.1
      valueUpper := hn.2.2.1.2
      cardLower := hn.2.2.2.1.1
      cardUpper := hn.2.2.2.1.2
      energyLower := hn.2.2.2.2.1.1
      energyUpper := hn.2.2.2.2.1.2
      sumLower := hn.2.2.2.2.2.1
      sumUpper := hn.2.2.2.2.2.2 }⟩
  · intro h
    let err : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have herrPos (n : ℕ) : 0 < err n := by
      dsimp [err]
      positivity
    let P : ℕ → ι := fun n => Classical.choose
      (h (err n) (herrPos n) (err n) (herrPos n) ((n : ℝ) + 2) (by positivity))
    have hP (n : ℕ) : EnergyRegionSandwich
        (N (P n)) (T (P n)) (V (P n)) (card (P n))
          (energy (P n)) (sum (P n))
        τ σ ρ ρstar s (err n) (err n) ((n : ℝ) + 2) :=
      Classical.choose_spec
        (h (err n) (herrPos n) (err n) (herrPos n)
          ((n : ℝ) + 2) (by positivity))
    have herrNonneg (n : ℕ) : 0 ≤ err n := (herrPos n).le
    have herrInfinitesimal :
        Expdb.VariableObject.IsInfinitesimal
          (err : Expdb.VariableObject ℝ) := by
      rw [Expdb.VariableObject.IsInfinitesimal]
      have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [err, Real.norm_eq_abs, abs_of_nonneg (herrNonneg _)] using hlim
    have hbase (n : ℕ) : 1 < N (P n) := hN (P n)
    have hTpos (n : ℕ) : 0 < T (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).timeLower
    have hVpos (n : ℕ) : 0 < V (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).valueLower
    have hcardPos (n : ℕ) : 0 < card (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).cardLower
    have henergyPos (n : ℕ) : 0 < energy (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).energyLower
    have hsumPos (n : ℕ) : 0 < sum (P n) :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans (hbase n)) _).trans_le
        (hP n).sumLower
    refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
      exact tendsto_atTop_mono' atTop
        (Filter.Eventually.of_forall fun n => (hP n).scale) hnat
    · exact Expdb.isPowerAsymptotic_of_between
        hbase hTpos herrNonneg herrInfinitesimal
        (fun n => ⟨(hP n).timeLower, (hP n).timeUpper⟩)
    · exact Expdb.isPowerAsymptotic_of_between
        hbase hVpos herrNonneg herrInfinitesimal
        (fun n => ⟨(hP n).valueLower, (hP n).valueUpper⟩)
    · exact Expdb.isPowerAsymptotic_of_between
        hbase hcardPos herrNonneg herrInfinitesimal
        (fun n => ⟨(hP n).cardLower, (hP n).cardUpper⟩)
    · exact Expdb.isPowerAsymptotic_of_between
        hbase henergyPos herrNonneg herrInfinitesimal
        (fun n => ⟨(hP n).energyLower, (hP n).energyUpper⟩)
    · exact Expdb.isPowerAsymptotic_of_between
        hbase hsumPos herrNonneg herrInfinitesimal
        (fun n => ⟨(hP n).sumLower, (hP n).sumUpper⟩)

/-- The source-facing unbounded-family formulation of membership in `E`. -/
def InLargeValueEnergyRegionAsymptotic
    (σ τ ρ ρstar s : ℝ) : Prop :=
  1 / 2 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ 0 ≤ ρ ∧ 0 ≤ ρstar ∧
    HasEnergyRegionAsymptotics
      LargeValuePattern.N LargeValuePattern.T LargeValuePattern.V
      (fun P => (P.ordinates.card : ℝ))
      (fun P => (finsetAdditiveEnergy P.ordinates : ℝ)) doubleZetaSum
      τ σ ρ ρstar s

/-- The source-facing unbounded-family formulation of membership in `E_ζ`. -/
def InZetaLargeValueEnergyRegionAsymptotic
    (σ τ ρ ρstar s : ℝ) : Prop :=
  1 / 2 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ 0 ≤ ρ ∧ 0 ≤ ρstar ∧
    HasEnergyRegionAsymptotics
      (fun P : ZetaLargeValuePattern => P.N)
      (fun P : ZetaLargeValuePattern => P.T)
      (fun P : ZetaLargeValuePattern => P.V)
      (fun P : ZetaLargeValuePattern => (P.ordinates.card : ℝ))
      (fun P : ZetaLargeValuePattern =>
        (finsetAdditiveEnergy P.ordinates : ℝ))
      (fun P : ZetaLargeValuePattern =>
        doubleZetaSum P.toLargeValuePattern)
      τ σ ρ ρstar s

/-- The asymptotic and epsilon--delta formulations of the general energy
region are equivalent. -/
theorem inLargeValueEnergyRegionAsymptotic_iff
    {σ τ ρ ρstar s : ℝ} :
    InLargeValueEnergyRegionAsymptotic σ τ ρ ρstar s ↔
      InLargeValueEnergyRegion σ τ ρ ρstar s := by
  constructor
  · rintro ⟨hσLower, hσUpper, hτ, hρ, hρstar, hasAsymptotics⟩
    refine ⟨hσLower, hσUpper, hτ, hρ, hρstar, ?_⟩
    have hsandwiches :=
      (hasEnergyRegionAsymptotics_iff_sandwiches
        (N := LargeValuePattern.N) (T := LargeValuePattern.T)
        (V := LargeValuePattern.V)
        (card := fun P => (P.ordinates.card : ℝ))
        (energy := fun P => (finsetAdditiveEnergy P.ordinates : ℝ))
        (sum := doubleZetaSum) (fun P => P.one_lt_N)).mp hasAsymptotics
    intro ε hε δ hδ C hC
    obtain ⟨P, hP⟩ := hsandwiches ε hε δ hδ C hC
    exact ⟨P, hP.scale, hP.timeLower, hP.timeUpper,
      hP.valueLower, hP.valueUpper, hP.cardLower, hP.cardUpper,
      hP.energyLower, hP.energyUpper, hP.sumLower, hP.sumUpper⟩
  · rintro ⟨hσLower, hσUpper, hτ, hρ, hρstar, hsandwiches⟩
    refine ⟨hσLower, hσUpper, hτ, hρ, hρstar, ?_⟩
    apply (hasEnergyRegionAsymptotics_iff_sandwiches
      (N := LargeValuePattern.N) (T := LargeValuePattern.T)
      (V := LargeValuePattern.V)
      (card := fun P => (P.ordinates.card : ℝ))
      (energy := fun P => (finsetAdditiveEnergy P.ordinates : ℝ))
      (sum := doubleZetaSum) (fun P => P.one_lt_N)).mpr
    intro ε hε δ hδ C hC
    obtain ⟨P, hP⟩ := hsandwiches ε hε δ hδ C hC
    exact ⟨P, {
      scale := hP.1
      timeLower := hP.2.1
      timeUpper := hP.2.2.1
      valueLower := hP.2.2.2.1
      valueUpper := hP.2.2.2.2.1
      cardLower := hP.2.2.2.2.2.1
      cardUpper := hP.2.2.2.2.2.2.1
      energyLower := hP.2.2.2.2.2.2.2.1
      energyUpper := hP.2.2.2.2.2.2.2.2.1
      sumLower := hP.2.2.2.2.2.2.2.2.2.1
      sumUpper := hP.2.2.2.2.2.2.2.2.2.2 }⟩

/-- The asymptotic and epsilon--delta formulations of the zeta energy region
are equivalent. -/
theorem inZetaLargeValueEnergyRegionAsymptotic_iff
    {σ τ ρ ρstar s : ℝ} :
    InZetaLargeValueEnergyRegionAsymptotic σ τ ρ ρstar s ↔
      InZetaLargeValueEnergyRegion σ τ ρ ρstar s := by
  constructor
  · rintro ⟨hσLower, hσUpper, hτ, hρ, hρstar, hasAsymptotics⟩
    refine ⟨hσLower, hσUpper, hτ, hρ, hρstar, ?_⟩
    have hsandwiches :=
      (hasEnergyRegionAsymptotics_iff_sandwiches
        (N := fun P : ZetaLargeValuePattern => P.N)
        (T := fun P : ZetaLargeValuePattern => P.T)
        (V := fun P : ZetaLargeValuePattern => P.V)
        (card := fun P : ZetaLargeValuePattern => (P.ordinates.card : ℝ))
        (energy := fun P : ZetaLargeValuePattern =>
          (finsetAdditiveEnergy P.ordinates : ℝ))
        (sum := fun P : ZetaLargeValuePattern =>
          doubleZetaSum P.toLargeValuePattern)
        (fun P => P.one_lt_N)).mp hasAsymptotics
    intro ε hε δ hδ C hC
    obtain ⟨P, hP⟩ := hsandwiches ε hε δ hδ C hC
    exact ⟨P, hP.scale, hP.timeLower, hP.timeUpper,
      hP.valueLower, hP.valueUpper, hP.cardLower, hP.cardUpper,
      hP.energyLower, hP.energyUpper, hP.sumLower, hP.sumUpper⟩
  · rintro ⟨hσLower, hσUpper, hτ, hρ, hρstar, hsandwiches⟩
    refine ⟨hσLower, hσUpper, hτ, hρ, hρstar, ?_⟩
    apply (hasEnergyRegionAsymptotics_iff_sandwiches
      (N := fun P : ZetaLargeValuePattern => P.N)
      (T := fun P : ZetaLargeValuePattern => P.T)
      (V := fun P : ZetaLargeValuePattern => P.V)
      (card := fun P : ZetaLargeValuePattern => (P.ordinates.card : ℝ))
      (energy := fun P : ZetaLargeValuePattern =>
        (finsetAdditiveEnergy P.ordinates : ℝ))
      (sum := fun P : ZetaLargeValuePattern =>
        doubleZetaSum P.toLargeValuePattern)
      (fun P => P.one_lt_N)).mpr
    intro ε hε δ hδ C hC
    obtain ⟨P, hP⟩ := hsandwiches ε hε δ hδ C hC
    exact ⟨P, {
      scale := hP.1
      timeLower := hP.2.1
      timeUpper := hP.2.2.1
      valueLower := hP.2.2.2.1
      valueUpper := hP.2.2.2.2.1
      cardLower := hP.2.2.2.2.2.1
      cardUpper := hP.2.2.2.2.2.2.1
      energyLower := hP.2.2.2.2.2.2.2.1
      energyUpper := hP.2.2.2.2.2.2.2.2.1
      sumLower := hP.2.2.2.2.2.2.2.2.2.1
      sumUpper := hP.2.2.2.2.2.2.2.2.2.2 }⟩

end TaoTrudgianYang2025
