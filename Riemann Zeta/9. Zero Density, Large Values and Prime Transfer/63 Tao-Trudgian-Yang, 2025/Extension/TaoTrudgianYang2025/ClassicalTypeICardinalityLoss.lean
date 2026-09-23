import TaoTrudgianYang2025.ClassicalTypeIFourierCardinality

/-! # Exact cardinality cost of Fourier displacement and positive height slabs -/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def classicalTypeIFourierCardinalityLoss (d : ℝ) : ℝ :=
  (Fintype.card (ZMod 2 × Fin (Nat.ceil (2 * d + 2) + 1)) : ℝ) * 3

theorem classicalTypeIFourierCardinalityLoss_le (d : ℝ) (hd : 0 ≤ d) :
    classicalTypeIFourierCardinalityLoss d ≤ 24 * (1 + d) := by
  simp only [classicalTypeIFourierCardinalityLoss, Fintype.card_prod, ZMod.card,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * d + 2 by linarith)
  linarith

theorem eventually_classicalTypeIFourierCardinalityLoss_le_rpow
    (θ η : ℝ) (hθ : 0 ≤ θ) (hgap : θ < η) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ d : ℝ, 0 ≤ d →
      d ≤ 2 * Real.pi * T ^ θ →
      classicalTypeIFourierCardinalityLoss d ≤ T ^ η := by
  let K : ℝ := 24 * (1 + 2 * Real.pi)
  have hconst : ∀ᶠ T : ℝ in Filter.atTop, K ≤ T ^ (η - θ) :=
    (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually
      (Filter.eventually_ge_atTop K)
  filter_upwards [hconst, Filter.eventually_ge_atTop (1 : ℝ)] with T hconst hT
  intro d hd hdT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hpowOne : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ
  have hbase : 1 + d ≤ (1 + 2 * Real.pi) * T ^ θ := by nlinarith
  calc
    classicalTypeIFourierCardinalityLoss d ≤ 24 * (1 + d) :=
      classicalTypeIFourierCardinalityLoss_le d hd
    _ ≤ K * T ^ θ := by dsimp only [K]; nlinarith
    _ ≤ T ^ (η - θ) * T ^ θ :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hTpos.le _)
    _ = T ^ η := by rw [← Real.rpow_add hTpos, sub_add_cancel]

end TaoTrudgianYang2025
