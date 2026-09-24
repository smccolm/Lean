import TaoTrudgianYang2025.ClassicalReflectedSourceTransfer

/-!
# Explicit logarithmic and separation losses for reflected source families

Both loss functions are the literal factors in the actual source consumers.
Their growth is bounded uniformly in the reflected cutoff and displacement,
using the proved subpower bound for the source dyadic count.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def classicalReflectedColorCount (M : ℕ) (D : ℝ) : ℝ :=
  Fintype.card (Fin (Nat.clog 2 M) × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1)))

def classicalReflectedCardinalityLoss (M : ℕ) (D : ℝ) : ℝ :=
  4*classicalReflectedColorCount M D

def classicalReflectedEnergyLoss (M : ℕ) (D : ℝ) : ℝ :=
  (4*Nat.ceil (1+4*D)+6)*9*(classicalReflectedColorCount M D)^4*2304

theorem eventually_classicalReflected_losses_le_const_mul_rpow
    (d a : ℝ) (hd : 0 < d) (ha : 0 ≤ a) :
    ∃ Kcard Kenergy : ℝ, 0 < Kcard ∧ 0 < Kenergy ∧
      ∀ᶠ T : ℝ in Filter.atTop, ∀ (M : ℕ) (D : ℝ),
        M ≤ ⌊sharpZetaCutoff T⌋₊ → 0 ≤ D → D ≤ a*T^d →
        classicalReflectedCardinalityLoss M D ≤ Kcard*T^(2*d) ∧
        classicalReflectedEnergyLoss M D ≤ Kenergy*T^(9*d) := by
  let b := 4*a+8
  let c := 14+16*a
  let Kcard := 4*b
  let Kenergy := c*9*b^4*2304
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨Kcard,Kenergy,by dsimp [Kcard]; positivity,
    by dsimp [Kenergy]; positivity,?_⟩
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow 1 d
    (by norm_num) hd,Filter.eventually_ge_atTop (8 : ℝ)] with T hclog hT
  intro M D hM hD hDupper
  have hTpos : 0 < T := by linarith
  let q := T^d
  have hq : 1 ≤ q := Real.one_le_rpow (by linarith) hd.le
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hJ : (Nat.clog 2 M : ℝ) ≤ q := by
    calc
      (Nat.clog 2 M : ℝ) ≤ Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
        exact_mod_cast Nat.clog_mono_right 2 hM
      _ ≤ q := by simpa only [one_mul] using hclog
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2*D+2 by linarith)).le
  have hrank : (2 : ℝ)*(Nat.ceil (2*D+2)+1) ≤ b*q := by
    dsimp [b]
    nlinarith
  have hColors : classicalReflectedColorCount M D ≤ b*q^2 := by
    calc
      classicalReflectedColorCount M D =
          (Nat.clog 2 M : ℝ)*(2*(Nat.ceil (2*D+2)+1)) := by
        simp only [classicalReflectedColorCount, Fintype.card_prod, Fintype.card_fin,
          ZMod.card, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      _ ≤ q*(b*q) := mul_le_mul hJ hrank (by positivity) hqpos.le
      _ = b*q^2 := by ring
  have hfirst : (4*Nat.ceil (1+4*D)+6 : ℝ) ≤ c*q := by
    have hceil' := (Nat.ceil_lt_add_one (show 0 ≤ 1+4*D by linarith)).le
    dsimp [c]
    nlinarith
  have hqTwo : q^2 = T^(2*d) := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    congr 1
    push_cast
    ring
  have hqNine : q^9 = T^(9*d) := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    congr 1
    push_cast
    ring
  have hColorNonneg : 0 ≤ classicalReflectedColorCount M D := Nat.cast_nonneg _
  constructor
  · calc
      classicalReflectedCardinalityLoss M D ≤ 4*(b*q^2) :=
        mul_le_mul_of_nonneg_left hColors (by norm_num)
      _ = Kcard*T^(2*d) := by rw [← hqTwo]; dsimp [Kcard]; ring
  · calc
      classicalReflectedEnergyLoss M D ≤ (c*q)*9*(b*q^2)^4*2304 := by
        dsimp [classicalReflectedEnergyLoss]
        gcongr
      _ = Kenergy*q^9 := by dsimp [Kenergy]; ring
      _ = Kenergy*T^(9*d) := by rw [hqNine]

theorem classicalReflected_dualCutoff_le_sharpCutoff
    {T tau d : ℝ} {Q : ℕ}
    (hT : 8 ≤ T) (htau : 0 < tau) (htauTwo : tau ≤ 2)
    (hd : d ≤ 1/2) (hQ : 1 < Q) (hScale : (Q : ℝ)^tau = T) :
    mediumTypeIDualCutoff T d Q ≤ ⌊sharpZetaCutoff T⌋₊ := by
  have hTpos : 0 < T := by linarith
  have hInv : (1/2 : ℝ) ≤ 1/tau :=
    div_le_div_of_nonneg_left (by norm_num) htau htauTwo
  have hM := classicalReflected_dyadic_length_le_physical_scale
    hTpos htau hQ hScale (le_refl (mediumTypeIDualCutoff T d Q))
  have hMToT : (mediumTypeIDualCutoff T d Q : ℝ) ≤ T := by
    calc
      (mediumTypeIDualCutoff T d Q : ℝ) ≤ T^(1+d-1/tau) := hM
      _ ≤ T^1 := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = T := Real.rpow_one _
  apply Nat.le_floor
  have hSharp := four_mul_lt_sharpZetaCutoff T
  linarith

end TaoTrudgianYang2025
