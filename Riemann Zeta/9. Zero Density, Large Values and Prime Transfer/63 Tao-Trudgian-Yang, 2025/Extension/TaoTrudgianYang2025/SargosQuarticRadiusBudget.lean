import TaoTrudgianYang2025.SargosQuarticRoundedBounds
import TaoTrudgianYang2025.BetaBufferedLogBudget

/-! Polynomial bounds for the constructed quartic radius and all integer logarithmic lengths. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosQuarticSharpRadius (C N α γ l b η : ℝ) : ℕ :=
  ⌈C*(α*N^2)*(1+α*N^2)^2/N⌉₊+
    (sargosQuarticSupportLower N α γ l η).natAbs+
    (sargosQuarticSupportUpper N α γ b η).natAbs+1

theorem sargosQuarticSharpRadius_contains (C N α γ l b η : ℝ) :
    0 < sargosQuarticSharpRadius C N α γ l b η ∧
      -(sargosQuarticSharpRadius C N α γ l b η : ℤ) ≤ sargosQuarticSupportLower N α γ l η ∧
      sargosQuarticSupportUpper N α γ b η ≤ (sargosQuarticSharpRadius C N α γ l b η : ℤ) := by
  unfold sargosQuarticSharpRadius
  omega

theorem sargosQuarticSharpRadius_le_polynomial {C N α γ l b η : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    (sargosQuarticSharpRadius C N α γ l b η : ℝ) ≤ (C+16)*(α*N^2+1)^3 := by
  let T := α*N^2
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hX : 0 ≤ C*T*(1+T)^2/N := by positivity
  have hceil := Nat.ceil_lt_add_one hX
  have hc := sargosQuarticBand_natAbs_bounds hN hα hγ hη hl hb hflat
  have hdiv := div_le_self (show 0 ≤ C*T*(1+T)^2 by positivity) hN
  have hm := mul_le_mul_of_nonneg_left (show T ≤ T+1 by linarith)
    (show 0 ≤ C*(T+1)^2 by positivity)
  have hXupper : C*T*(1+T)^2/N ≤ C*(T+1)^3 := by nlinarith
  have hp : T+1 ≤ (T+1)^3 := by
    nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
  change ((⌈C*T*(1+T)^2/N⌉₊+(sargosQuarticSupportLower N α γ l η).natAbs+
    (sargosQuarticSupportUpper N α γ b η).natAbs+1 : ℕ) : ℝ) ≤ (C+16)*(T+1)^3
  push_cast
  have hL : ((sargosQuarticSupportLower N α γ l η).natAbs : ℝ) ≤ 6*T+1 := hc.1
  have hU : ((sargosQuarticSupportUpper N α γ b η).natAbs : ℝ) ≤ 6*T+1 := hc.2.1
  nlinarith

theorem sargosQuarticSharpFarLengths_le_polynomial {C N α γ l b η : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    let L := sargosQuarticSupportLower N α γ l η
    let U := sargosQuarticSupportUpper N α γ b η
    let R := sargosQuarticSharpRadius C N α γ l b η
    ((L+(R : ℤ)).toNat : ℝ) ≤ (C+24)*(α*N^2+1)^3 ∧
      (((R : ℤ)-U).toNat : ℝ) ≤ (C+24)*(α*N^2+1)^3 := by
  intro L U R
  let T := α*N^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hc := sargosQuarticBand_natAbs_bounds hN hα hγ hη hl hb hflat
  have hr : (R : ℝ) ≤ (C+16)*(T+1)^3 :=
    sargosQuarticSharpRadius_le_polynomial hC hN hα hγ hη hl hb hflat
  have hi := sargosQuarticSharpRadius_contains C N α γ l b η
  have hL : (L : ℝ) ≤ (L.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using le_abs_self (L : ℝ)
  have hU : -(U : ℝ) ≤ (U.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using neg_le_abs (U : ℝ)
  have hzL : 0 ≤ L+(R : ℤ) := by have hh : -(R : ℤ) ≤ L := hi.2.1; omega
  have hzU : 0 ≤ (R : ℤ)-U := by have hh : U ≤ (R : ℤ) := hi.2.2; omega
  have heL : ((L+(R : ℤ)).toNat : ℝ) = (L : ℝ)+(R : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzL
  have heU : (((R : ℤ)-U).toNat : ℝ) = (R : ℝ)-(U : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzU
  rw [heL,heU]
  have hp : T+1 ≤ (T+1)^3 := by
    nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
  have hcL : (L.natAbs : ℝ) ≤ 6*T+1 := hc.1
  have hcU : (U.natAbs : ℝ) ≤ 6*T+1 := hc.2.1
  constructor <;> change _ ≤ (C+24)*(T+1)^3 <;> nlinarith

theorem sargosQuarticSharpInnerLength_le_polynomial {C N α γ l b η : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    (((sargosQuarticPlateauUpper N α γ b η-
      sargosQuarticPlateauLower N α γ l η-1).toNat : ℕ) : ℝ) ≤ (C+24)*(α*N^2+1)^3 := by
  let A := sargosQuarticPlateauLower N α γ l η
  let B := sargosQuarticPlateauUpper N α γ b η
  let T := α*N^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hc := sargosQuarticBand_natAbs_bounds hN hα hγ hη hl hb hflat
  have hA : -(A : ℝ) ≤ (A.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using neg_le_abs (A : ℝ)
  have hB : (B : ℝ) ≤ (B.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using le_abs_self (B : ℝ)
  have hcA : (A.natAbs : ℝ) ≤ 6*T+1 := hc.2.2.1
  have hcB : (B.natAbs : ℝ) ≤ 6*T+1 := hc.2.2.2
  change ((B-A-1).toNat : ℝ) ≤ (C+24)*(T+1)^3
  by_cases hz : 0 ≤ B-A-1
  · have he : ((B-A-1).toNat : ℝ) = (B : ℝ)-(A : ℝ)-1 := by
      exact_mod_cast Int.toNat_of_nonneg hz
    rw [he]
    have hp : T+1 ≤ (T+1)^3 := by
      nlinarith [sq_nonneg T,mul_nonneg hT (sq_nonneg T)]
    have hCp : 0 ≤ C*(T+1)^3 := by positivity
    nlinarith
  · have he : (B-A-1).toNat = 0 := by omega
    rw [he,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025

