import Dubon2026.PolarizedOddInvolutionMatrix
import Dubon2026.PolarizedInvolutionAction

/-! Extract the original matrix conjugate-duality equation from the
actual polarized group law. This is the equation that must descend to
the CM trace algebra for DUB-17's unframed comparison. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- An original point with trivial component is its actual identity-component inclusion. -/
theorem polarizedIdentity_eq (x : PolarizedGaloisGroup ι R)
    (hx : polarizedComponent x = 1) : x = polarizedIdentityComponent x.left :=
  SemidirectProduct.ext rfl hx

/-- On the original identity component, the source similitude is the
literal multiplier coordinate. -/
theorem polarizedIdentity_similitude (x : PolarizedGaloisGroup ι R)
    (hx : polarizedComponent x = 1) : polarizedSimilitude x = x.left.2 := by
  change x.left.2 * polarizedComponentSign x.right = x.left.2
  have hr : x.right = 1 := hx
  rw [hr, map_one, mul_one]

/-- The actual odd component conjugates original identity matrices by
its polarization matrix and the multiplier-twisted inverse transpose. -/
theorem polarizedOdd_conjugate_identity (g x : PolarizedGaloisGroup ι R)
    (hg : polarizedComponent g = Multiplicative.ofAdd (1 : ZMod 2))
    (hν : polarizedSimilitude g = -1) (hx : polarizedComponent x = 1) :
    (g * x * g⁻¹).left.1 = g.left.1 *
      (GeneralLinearGroup.scalar ι (polarizedSimilitude x) * polarizedContragredient x.left.1) *
        g.left.1⁻¹ := by
  have he : g * x * g⁻¹ = polarizedIdentityComponent
      ((g.left.1, 1) * polarizedSwitch x.left * (g.left.1, 1)⁻¹) := by
    conv_lhs => rw [polarizedOdd_eq_involution g hg hν, polarizedIdentity_eq x hx]
    exact polarizedInvolution_conjugate g.left.1 x.left
  have hm := congrArg (fun z : PolarizedGaloisGroup ι R => z.left.1) he
  rw [polarizedIdentity_similitude x hx]
  exact hm

end Dubon2026
