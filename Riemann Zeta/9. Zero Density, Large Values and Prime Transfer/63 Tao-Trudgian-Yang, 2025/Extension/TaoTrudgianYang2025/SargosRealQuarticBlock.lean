import TaoTrudgianYang2025.SargosSixthMomentTheorem

/-! Literal real-scale source blocks and their exact integer endpoints. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosRealSourceInterval (M : ℝ) : Finset ℤ := Finset.Ioc ⌊M⌋ ⌊2*M⌋

def sargosRealBlockLength (M : ℝ) : ℕ := (⌊2*M⌋-⌊M⌋).toNat

def sargosRealQuarticPrefix (M : ℝ) (H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊M⌋ (⌊M⌋+H),
    z n*fordAdditiveCharacter ((n:ℝ)^2*α+(n:ℝ)^4*γ)

def sargosRealQuarticMaximum (M : ℝ) (z : ℤ → ℂ) (α γ : ℝ) : ℝ :=
  (Finset.range (sargosRealBlockLength M+1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
    (fun H => ‖sargosRealQuarticPrefix M H z α γ‖)

theorem mem_sargosRealSourceInterval (M : ℝ) (n : ℤ) :
    n ∈ sargosRealSourceInterval M ↔ M < (n:ℝ) ∧ (n:ℝ) ≤ 2*M := by
  simp only [sargosRealSourceInterval,Finset.mem_Ioc,Int.floor_lt,Int.le_floor]

theorem sargosRealBlockLength_cast {M : ℝ} (hM : 0 ≤ M) :
    (sargosRealBlockLength M : ℤ) = ⌊2*M⌋-⌊M⌋ := by
  have hm : ⌊M⌋ ≤ ⌊2*M⌋ := Int.floor_mono (by linarith only [hM])
  exact Int.toNat_of_nonneg (sub_nonneg.mpr hm)

theorem sargosRealBlockLength_floor_bounds {M : ℝ} (hM : 0 ≤ M) :
    ⌊M⌋₊ ≤ sargosRealBlockLength M ∧ sargosRealBlockLength M ≤ ⌊M⌋₊+1 := by
  have hf := Int.natCast_floor_eq_floor hM
  have hL := sargosRealBlockLength_cast hM
  have hlow : 2*⌊M⌋ ≤ ⌊2*M⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith only [Int.floor_le M]
  have hupp : ⌊2*M⌋ ≤ 2*⌊M⌋+1 := by
    apply Int.floor_le_iff.mpr
    push_cast
    linarith only [Int.lt_floor_add_one M]
  omega

theorem sargosRealQuarticPrefix_eq_natural {M : ℝ} (hM : 0 ≤ M)
    (H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosRealQuarticPrefix M H z α γ = sargosQuarticPrefix ⌊M⌋₊ H z α γ := by
  simp only [sargosRealQuarticPrefix,sargosQuarticPrefix,Int.natCast_floor_eq_floor hM]

theorem sargosSourceInterval_subset_real {M : ℝ} (hM : 0 ≤ M) :
    sargosSourceInterval ⌊M⌋₊ ⊆ sargosRealSourceInterval M := by
  have hf := Int.natCast_floor_eq_floor hM
  have hL := sargosRealBlockLength_cast hM
  have hb := sargosRealBlockLength_floor_bounds hM
  intro n hn
  simp only [sargosSourceInterval,Finset.mem_Ioc] at hn
  simp only [sargosRealSourceInterval,Finset.mem_Ioc]
  omega

end TaoTrudgianYang2025
