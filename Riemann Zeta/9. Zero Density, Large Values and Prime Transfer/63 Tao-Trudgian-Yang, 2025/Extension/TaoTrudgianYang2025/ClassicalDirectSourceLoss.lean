import TaoTrudgianYang2025.ClassicalDirectSourceTransfer

/-!
# Absorption of the exact two-color direct-source losses

The two dyadic labels are dominated by the already proved logarithmic
color-count majorant once the sharp cutoff has at least two dyadic levels.
This preserves the exact cardinality and fourth-power energy factors.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirect_twoColor_losses_le_reflected
    (M : ℕ) (D : ℝ) (hM : 2 ≤ Nat.clog 2 M) :
    let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1))) : ℝ)
    4*K ≤ classicalReflectedCardinalityLoss M D ∧
      (4*Nat.ceil (1+4*D)+6)*9*K^4*2304 ≤ classicalReflectedEnergyLoss M D := by
  dsimp only
  let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1))) : ℝ)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hCompare : K ≤ classicalReflectedColorCount M D := by
    simp only [K,classicalReflectedColorCount,Fintype.card_prod,Fintype.card_fin,
      ZMod.card,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (by positivity)
  constructor
  · exact mul_le_mul_of_nonneg_left hCompare (by norm_num)
  · change (4*Nat.ceil (1+4*D)+6)*9*K^4*2304 ≤
      (4*Nat.ceil (1+4*D)+6)*9*(classicalReflectedColorCount M D)^4*2304
    gcongr

theorem eventually_classicalDirect_twoColor_losses_le_const_mul_rpow
    (d a : ℝ) (hd : 0 < d) (ha : 0 ≤ a) :
    ∃ Kcard Kenergy : ℝ, 0 < Kcard ∧ 0 < Kenergy ∧
      ∀ᶠ T : ℝ in Filter.atTop, ∀ D : ℝ, 0 ≤ D → D ≤ a*T^d →
        let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (Nat.ceil (2*D+2)+1))) : ℝ)
        4*K ≤ Kcard*T^(2*d) ∧
          (4*Nat.ceil (1+4*D)+6)*9*K^4*2304 ≤ Kenergy*T^(9*d) := by
  obtain ⟨Kcard,Kenergy,hKcard,hKenergy,hLoss⟩ :=
    eventually_classicalReflected_losses_le_const_mul_rpow d a hd ha
  refine ⟨Kcard,Kenergy,hKcard,hKenergy,?_⟩
  filter_upwards [hLoss,Filter.eventually_ge_atTop (8 : ℝ)] with T hLossT hT
  intro D hD hUpper
  dsimp only
  have hA : 4 ≤ ⌊sharpZetaCutoff T⌋₊ := by
    apply Nat.le_floor
    exact (show (4 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hClog : 2 ≤ Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
    have hFour : Nat.clog 2 4 = 2 := by decide
    rw [← hFour]
    exact Nat.clog_mono_right 2 hA
  have hDom := classicalDirect_twoColor_losses_le_reflected
    ⌊sharpZetaCutoff T⌋₊ D hClog
  have hBound := hLossT ⌊sharpZetaCutoff T⌋₊ D le_rfl hD hUpper
  exact ⟨hDom.1.trans hBound.1,hDom.2.trans hBound.2⟩

end TaoTrudgianYang2025
