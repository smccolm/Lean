import Dubon2026.SourceEllipticCharTwoQuaternionStabilizers

/-! DUB-17/18 -> characteristic-two fixed cyclic-subgroup count nuThree.
The actual cubic scaling on native ofJ0 satisfies beta^2+beta+id=0 by
the native elliptic addition law. Existing point-map coordinates are reused.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, characteristic-two nuThree solution. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticStabilizer
open SourceEllipticExceptional SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

/-- The actual cubic stabilized inverse coordinate map on the exceptional curve. -/
def cubicPoint (ω : K) (hω : ω ^ 2 + ω + 1 = 0) : AddAut (ofJ0 K).toAffine.Point :=
  stabilizerPointHom (ofJ0 K) (cubicStabilizer ω hω)

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)

theorem cubicPoint_some {x y : K} (h : (ofJ0 K).toAffine.Nonsingular x y) :
    ∃ h', cubicPoint ω hω (Point.some x y h) = Point.some (ω * x) y h' := by
  apply exists_eq_some_of_xy_eq
  change xy (stabilizerPointEquiv (ofJ0 K) (cubicChange ω hω) _ (Point.some x y h)) = _
  rw [xy_stabilizerPointEquiv]
  show some (vcXInv (cubicChange ω hω) x, vcYInv (cubicChange ω hω) x y) = some (ω * x, y)
  have h3 := omega_pow_three ω hω
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by
    calc ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := h3)
  have h4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3, one_mul]
  have h6 : ω ^ 6 = 1 := by
    calc ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  simp only [vcXInv, vcYInv, cubicChange, Units.val_inv_eq_inv_val, coe_omegaUnit, hinv,
    sub_zero, zero_mul, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [← pow_mul, show 2 * 2 = 4 by norm_num, h4]
  · rw [← pow_mul, show 2 * 3 = 6 by norm_num, h6, one_mul]

theorem cubicPoint_quadratic (P : (ofJ0 K).toAffine.Point) : cubicPoint ω hω (cubicPoint ω hω P) + cubicPoint ω hω P + P = 0 := by
  have hq' := hω
  have hu0 : ω ≠ 0 := omega_ne_zero ω hω
  have ha1 : (ofJ0 K).a₁ = 0 := rfl
  have ha2 : (ofJ0 K).a₂ = 0 := rfl
  have hnegY : ∀ a b : K, (ofJ0 K).toAffine.negY a b = b + 1 := by
    intro a b
    simp [WeierstrassCurve.Affine.negY, ofJ0, CharTwo.neg_eq, CharTwo.sub_eq_add]
  rcases P with _ | ⟨x, y, h⟩
  · show cubicPoint ω hω (cubicPoint ω hω 0) + cubicPoint ω hω 0 + 0 = 0
    rw [map_zero, map_zero, add_zero, add_zero]
  · by_cases hx : x = 0
    ·
      subst hx
      have hfix : cubicPoint ω hω (Point.some 0 y h) = Point.some 0 y h := by
        obtain ⟨h', e⟩ := cubicPoint_some ω hω h
        rw [e]
        apply xy_injective
        simp [xy]
      rw [hfix, hfix]
      have hyne : y ≠ (ofJ0 K).toAffine.negY 0 y := by
        rw [hnegY]; intro e
        have : (1 : K) = 0 := by linear_combination -e
        exact one_ne_zero this
      rw [Point.add_of_Y_ne hyne]
      have hsl : (ofJ0 K).toAffine.slope 0 0 y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne]
        simp [ofJ0]
      apply Point.add_of_Y_eq
      · simp [hsl, ha1, ha2]
      · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, hsl, hnegY, ha1, ha2]
        ring
    ·
      obtain ⟨h₁, e₁⟩ := cubicPoint_some ω hω h
      obtain ⟨h₂, e₂⟩ := cubicPoint_some ω hω h₁
      rw [e₁, e₂]
      have hne : ω * (ω * x) ≠ ω * x := by
        intro e
        have : ω * x * (ω - 1) = 0 := by linear_combination e
        rcases mul_eq_zero.mp this with h0 | h0
        · rcases mul_eq_zero.mp h0 with h00 | h00
          · exact hu0 h00
          · exact hx h00
        · exact (omega_ne_one ω hω) (sub_eq_zero.mp h0)
      rw [Point.add_of_X_ne hne]
      have hsl : (ofJ0 K).toAffine.slope (ω * (ω * x)) (ω * x) y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hne, sub_self, zero_div]
      apply Point.add_of_Y_eq
      · simp only [WeierstrassCurve.Affine.addX, hsl, ha1, ha2]
        linear_combination (-x) * hq'
      · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, hsl, hnegY, ha1, ha2]
        ring


end
end Dubon2026.SourceEllipticCharTwo
