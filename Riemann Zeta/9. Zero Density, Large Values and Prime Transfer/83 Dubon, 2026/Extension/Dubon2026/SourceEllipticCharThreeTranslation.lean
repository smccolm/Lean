import Dubon2026.SourceEllipticCharThreeModel

/-! The actual order-three translation of the exceptional characteristic-
three curve. Its coordinate action and quadratic additive identity are
the remaining elliptic input to the DUB-17/18 cubic fixed-point count.
Existing optional coordinates and stabilizer point equivalences are reused.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 3]

omit [DecidableEq K] in
theorem char_three_translation_fixes :
    (⟨1, 1, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K) := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, EA, h3]

/-- The actual characteristic-three elliptic automorphism (x,y) ↦ (x-1,y). -/
def charThreeTranslation : (EA (-1 : K)).toAffine.Point ≃+ (EA (-1 : K)).toAffine.Point :=
  stabilizerPointEquiv (EA (-1 : K)) ⟨1, 1, 0, 0⟩ char_three_translation_fixes

theorem xy_charThreeTranslation (P : (EA (-1 : K)).toAffine.Point) :
    xy (charThreeTranslation P) = (xy P).map fun q => (q.1 - 1, q.2) := by
  rw [charThreeTranslation, xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv, vcYInv]

theorem charThreeTranslation_quadratic (T : (EA (-1 : K)).toAffine.Point) :
    charThreeTranslation (charThreeTranslation T) + charThreeTranslation T + T = 0 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rcases T with _ | ⟨x, y, h⟩
  · change charThreeTranslation (charThreeTranslation 0) + charThreeTranslation 0 +
      (0 : (EA (-1 : K)).toAffine.Point) = 0
    simp only [map_zero, add_zero]
  · have hβ : xy (charThreeTranslation (Point.some x y h)) = some (x - 1, y) := by
      rw [xy_charThreeTranslation]; rfl
    have hββ : xy (charThreeTranslation (charThreeTranslation (Point.some x y h))) =
        some (x - 1 - 1, y) := by rw [xy_charThreeTranslation, xy_charThreeTranslation]; rfl
    obtain ⟨h₁, e₁⟩ := exists_eq_some_of_xy_eq hβ
    obtain ⟨h₂, e₂⟩ := exists_eq_some_of_xy_eq hββ
    rw [e₂, e₁]
    have hne : x - 1 - 1 ≠ x - 1 := by
      intro hx
      have : (1 : K) = 0 := by linear_combination -hx
      exact one_ne_zero this
    rw [Point.add_of_X_ne hne]
    have hsum : xy (Point.some _ _ (nonsingular_add h₂ h₁ fun hxy => hne hxy.left) :
        (EA (-1 : K)).toAffine.Point) = xy (-(Point.some x y h) : (EA (-1 : K)).toAffine.Point) := by
      rw [xy_neg]
      simp only [xy, Option.map_some, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY,
        Affine.slope_of_X_ne hne, sub_self, zero_div, Option.some.injEq, Prod.mk.injEq]
      constructor
      · linear_combination (1 - x) * h3
      · ring
    rw [xy_injective hsum, neg_add_cancel]

end
end Dubon2026.SourceEllipticExceptional
