import Dubon2026.SourceEllipticQuarticModel

/-! The actual characteristic-three exceptional curve is the existing
EA(-1). Its invariants supply the prescribed model for the DUB-17/18
wild exceptional-fiber census. No new elliptic-curve representation is used. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem two_ne_zero_of_char_three : (2 : K) ≠ 0 := by
  intro h2
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h1 : (1 : K) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem EA_neg_one_discriminant_of_char_three : (EA (-1 : K)).Δ = 1 := by
  rw [EA_Δ]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination 21 * h3

theorem isElliptic_EA_neg_one_of_char_three : (EA (-1 : K)).IsElliptic := by
  refine ⟨?_⟩
  rw [EA_neg_one_discriminant_of_char_three]
  exact isUnit_one

theorem EA_neg_one_j_of_char_three [hE : (EA (-1 : K)).IsElliptic] :
    (EA (-1 : K)).j = 0 := by
  apply WeierstrassCurve.j_eq_zero
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination 16 * h3

end
end Dubon2026.SourceEllipticExceptional
