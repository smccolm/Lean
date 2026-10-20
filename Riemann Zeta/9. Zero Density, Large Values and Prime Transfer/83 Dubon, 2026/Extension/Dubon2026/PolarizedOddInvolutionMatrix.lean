import Dubon2026.PolarizedInvolution

/-! An actual odd involution in the source disconnected group determines
a symmetric matrix. This recovers the polarization from the original
universal real-place image during DUB-17's CM trace descent. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The multiplier coordinate of an odd element in the nonidentity
component is one, so it is the involution expression of its actual matrix. -/
theorem polarizedOdd_eq_involution (g : PolarizedGaloisGroup ι R)
    (hc : polarizedComponent g = Multiplicative.ofAdd (1 : ZMod 2))
    (hν : polarizedSimilitude g = -1) : g = polarizedInvolution g.left.1 := by
  have hr : g.right = Multiplicative.ofAdd (1 : ZMod 2) := hc
  have hm : g.left.2 = 1 := by
    change g.left.2 * polarizedComponentSign g.right = -1 at hν
    rw [hr] at hν
    have hs : polarizedComponentSign (R := R) (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
      simp [polarizedComponentSign]
    rw [hs] at hν
    exact mul_right_cancel (hν.trans (one_mul (-1 : Rˣ)).symm)
  exact SemidirectProduct.ext (Prod.ext rfl hm) hr

/-- Squaring the actual source involution expression to one forces its
original matrix to be symmetric. -/
theorem polarizedInvolution_symmetric_of_sq (B : GeneralLinearGroup ι R)
    (h : polarizedInvolution B ^ 2 = 1) : B.val.transpose = B.val := by
  rw [pow_two] at h
  have hm := congrArg (fun g : PolarizedGaloisGroup ι R => g.left.1) h
  change B * (polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) (B, 1)).1 = 1 at hm
  rw [polarizedSwitchAction_generator] at hm
  change B * (GeneralLinearGroup.scalar ι 1 * polarizedContragredient B) = 1 at hm
  rw [map_one, one_mul] at hm
  have he : polarizedContragredient B = B⁻¹ :=
    mul_left_cancel (hm.trans (mul_inv_cancel B).symm)
  exact congrArg (fun U : GeneralLinearGroup ι R => U.inv) he

/-- Every actual odd order-two element has a symmetric original
polarization matrix, with no symmetry certificate assumed. -/
theorem polarizedOddInvolution_matrix_symmetric (g : PolarizedGaloisGroup ι R)
    (hc : polarizedComponent g = Multiplicative.ofAdd (1 : ZMod 2))
    (hν : polarizedSimilitude g = -1) (hsq : g ^ 2 = 1) :
    g.left.1.val.transpose = g.left.1.val := by
  apply polarizedInvolution_symmetric_of_sq
  exact (congrArg (fun x : PolarizedGaloisGroup ι R => x ^ 2)
    (polarizedOdd_eq_involution g hc hν)).symm.trans hsq

end Dubon2026
