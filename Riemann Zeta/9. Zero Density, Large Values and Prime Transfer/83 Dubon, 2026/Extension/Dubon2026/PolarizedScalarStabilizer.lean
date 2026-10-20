import Dubon2026.PolarizedCoefficientMap
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Ring

/-! The nonidentity polarized component removes strict scalar stabilizers.
Together with native CM matrix spanning, this is the rigidity input for
DUB-17's source unframed polarized deformation comparison. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [CommRing R]

omit [Nonempty ι] in
/-- A polarized matrix stabilizer commutes with every actual identity-component matrix coordinate. -/
theorem polarizedLinear_commute_identity (U : GeneralLinearGroup ι R)
    (g : PolarizedGaloisGroup ι R) (hg : polarizedComponent g = 1)
    (hc : polarizedLinearInclusion U * g = g * polarizedLinearInclusion U) :
    U * g.left.1 = g.left.1 * U := by
  have he := congrArg (fun z : PolarizedGaloisGroup ι R => z.left.1) hc
  change U * g.left.1 = (g.left * polarizedSwitchAction g.right (U, 1)).1 at he
  change g.right = 1 at hg
  rw [hg, map_one] at he
  exact he

/-- Reduction of an original scalar matrix is the identity exactly on its original residue-one unit. -/
theorem polarizedScalar_reduction_eq_one {k : Type} [CommRing k]
    (r : R →+* k) (u : Rˣ)
    (hr : GeneralLinearGroup.map r (GeneralLinearGroup.scalar ι u) = 1) :
    Units.map r.toMonoidHom u = 1 := by
  rw [polarizedScalar_map] at hr
  let i : ι := Classical.choice inferInstance
  apply Units.ext
  have hi := congrArg (fun V : GeneralLinearGroup ι k => V.val i i) hr
  change Matrix.scalar ι (r (u : R)) i i = (1 : Matrix ι ι k) i i at hi
  simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using hi

/-- A scalar matrix stabilizing a nonidentity polarized point equals its own inverse in the original coefficient units. -/
theorem polarizedScalar_eq_inv_of_commute (u : Rˣ) (g : PolarizedGaloisGroup ι R)
    (hg : polarizedComponent g = Multiplicative.ofAdd (1 : ZMod 2))
    (hc : polarizedLinearInclusion (GeneralLinearGroup.scalar ι u) * g =
      g * polarizedLinearInclusion (GeneralLinearGroup.scalar ι u)) : u = u⁻¹ := by
  have he := congrArg (fun z : PolarizedGaloisGroup ι R => z.left.1) hc
  change GeneralLinearGroup.scalar ι u * g.left.1 =
    (g.left * polarizedSwitchAction g.right (GeneralLinearGroup.scalar ι u, 1)).1 at he
  change g.right = Multiplicative.ofAdd (1 : ZMod 2) at hg
  rw [hg, polarizedSwitchAction_generator] at he
  change GeneralLinearGroup.scalar ι u * g.left.1 =
    g.left.1 * (GeneralLinearGroup.scalar ι 1 * polarizedContragredient (GeneralLinearGroup.scalar ι u)) at he
  rw [map_one, one_mul, polarizedContragredient_scalar, (polarizedScalar_commute u g.left.1).eq] at he
  have hs := mul_left_cancel he
  let i : ι := Classical.choice inferInstance
  apply Units.ext
  have hi := congrArg (fun V : GeneralLinearGroup ι R => V.val i i) hs
  change Matrix.scalar ι (u : R) i i = Matrix.scalar ι (↑u⁻¹ : R) i i at hi
  simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using hi

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- An original residue-one unit equal to its inverse is one whenever the residue characteristic is not two. -/
theorem localUnit_eq_one_of_eq_inv {k : Type} [Field k]
    (r : R →+* k) [IsLocalHom r] (h2 : (2 : k) ≠ 0)
    (u : Rˣ) (hr : Units.map r.toMonoidHom u = 1) (hu : u = u⁻¹) : u = 1 := by
  have hrval : r (u : R) = 1 := congrArg Units.val hr
  have hplus : IsUnit ((u : R) + 1) := isUnit_of_map_unit r _ (isUnit_iff_ne_zero.mpr (by
    simpa only [map_add, map_one, hrval, one_add_one_eq_two] using h2))
  have hs : (u : R) * (u : R) = 1 := by
    have h := congrArg (fun v : Rˣ => ((v * u : Rˣ) : R)) hu
    simpa only [Units.val_mul, inv_mul_cancel, Units.val_one] using h
  have hz : ((u : R) - 1) * ((u : R) + 1) = 0 := by
    calc
      _ = (u : R) * (u : R) - 1 := by ring
      _ = 0 := by rw [hs, sub_self]
  apply Units.ext
  exact sub_eq_zero.mp (hplus.mul_left_eq_zero.mp hz)

end
end Dubon2026
