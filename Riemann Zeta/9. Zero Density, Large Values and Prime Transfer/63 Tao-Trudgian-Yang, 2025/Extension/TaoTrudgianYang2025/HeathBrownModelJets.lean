import TaoTrudgianYang2025.BetaModelJetEstimates

/-!
# Positive signed jets for Heath--Brown's derivative theorem

The sign and the positive lower constant depend only on the fixed model
parameter and derivative order. The actual model errors imply the signed
bounds; no derivative hypothesis is supplied independently of the source.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseJetSign (σ : ℝ) (p : ℕ) : ℝ :=
  if 0 ≤ (descPochhammer ℝ p).eval (-σ) then 1 else -1

def modelPhaseJetLower (σ : ℝ) (p : ℕ) : ℝ :=
  modelPhaseJetCoefficient σ p * (2 : ℝ)^(-σ-p) / 2

theorem modelPhaseJetCoefficient_pos {σ : ℝ} (hσ : 0 < σ) (p : ℕ) :
    0 < modelPhaseJetCoefficient σ p := by
  unfold modelPhaseJetCoefficient
  apply abs_pos.mpr
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem modelPhaseJetSign_abs (σ : ℝ) (p : ℕ) :
    |modelPhaseJetSign σ p| = 1 := by
  unfold modelPhaseJetSign
  split <;> norm_num

theorem modelPhaseJetSign_coefficient (σ : ℝ) (p : ℕ) :
    modelPhaseJetSign σ p * (descPochhammer ℝ p).eval (-σ) =
      modelPhaseJetCoefficient σ p := by
  unfold modelPhaseJetSign modelPhaseJetCoefficient
  split
  · rename_i h
    simp only [one_mul,abs_of_nonneg h]
  · rename_i h
    simp only [neg_mul,one_mul,abs_of_neg (lt_of_not_ge h)]

theorem modelPhaseJetLower_pos {σ : ℝ} (hσ : 0 < σ) (p : ℕ) :
    0 < modelPhaseJetLower σ p := by
  unfold modelPhaseJetLower
  exact div_pos (mul_pos (modelPhaseJetCoefficient_pos hσ p)
    (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)

theorem modelPhase_signed_referenceJet_bounds {σ : ℝ} (hσ : 0 < σ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    2*modelPhaseJetLower σ p ≤ modelPhaseJetSign σ p *
        iteratedDeriv p (modelPhase σ) u ∧
      modelPhaseJetSign σ p * iteratedDeriv p (modelPhase σ) u ≤
        modelPhaseJetCoefficient σ p := by
  have hc : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hu.1).ne'
  have he := iteratedDerivWithin_modelPhase σ p ⟨hu.1.le,hu.2.le⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hc
    ⟨hu.1.le,hu.2.le⟩] at he
  rw [he,← mul_assoc,modelPhaseJetSign_coefficient]
  have hneg : -σ-(p : ℝ) ≤ 0 := by
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hlo := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hu.1) hu.2.le hneg
  have hhi := Real.rpow_le_one_of_one_le_of_nonpos hu.1.le hneg
  have hcoef := (modelPhaseJetCoefficient_pos hσ p).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo hcoef
    dsimp only [modelPhaseJetLower]
    linarith
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hhi hcoef

theorem approximateModelPhase_signedJet_bounds
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P)
    (hδ : δ ≤ min (modelPhaseJetLower σ p) 1) :
    modelPhaseJetLower σ p ≤ modelPhaseJetSign σ p * iteratedDeriv (p+1) F u ∧
      modelPhaseJetSign σ p * iteratedDeriv (p+1) F u ≤
        modelPhaseJetCoefficient σ p+1 := by
  have he := approximateModelPhase_iteratedDeriv_error hF hu p hp
  have hs : |modelPhaseJetSign σ p * iteratedDeriv (p+1) F u -
      modelPhaseJetSign σ p * iteratedDeriv p (modelPhase σ) u| ≤ δ := by
    rw [← mul_sub,abs_mul,modelPhaseJetSign_abs,one_mul]
    exact he
  rw [abs_le] at hs
  have hb := modelPhase_signed_referenceJet_bounds hσ hu p
  have hd₀ := hδ.trans (min_le_left _ _)
  have hd₁ := hδ.trans (min_le_right _ _)
  constructor <;> linarith

end TaoTrudgianYang2025
