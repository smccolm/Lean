import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Finite characters valued in the original rational circle

DUB-17's relation-obstruction surjectivity can use the proved integral
lattice duality and finite cardinalities. Pinned finite abelian duality
applies to the literal rational circle once its roots are constructed.
This avoids a new character decomposition or a complex-circle comparison.
-/
namespace Dubon2026
noncomputable section

/-- The literal rational circle has enough roots of every positive order;
the generator is the class of one divided by that order. -/
@[implicit_reducible] def originalRationalCircleEnoughRoots (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity (Multiplicative (AddCircle (1 : ℚ))) n := by
  let ζ : Multiplicative (AddCircle (1 : ℚ)) :=
    Multiplicative.ofAdd ((1 / n : ℚ) : AddCircle (1 : ℚ))
  have hζ : IsPrimitiveRoot ζ n :=
    IsPrimitiveRoot.iff_orderOf.mpr (AddCircle.addOrderOf_period_div (NeZero.pos n))
  refine ⟨⟨ζ, hζ⟩, ?_⟩
  refine ⟨hζ.toRootsOfUnity, fun u => ?_⟩
  apply Subgroup.mem_zpowers_iff.mpr
  have hu : n • u.val.val.toAdd = 0 := by
    have h := u.property
    exact congrArg (fun v => (v : Multiplicative (AddCircle (1 : ℚ))).toAdd)
      (congrArg Units.val h)
  obtain ⟨m, _, hm⟩ := (AddCircle.nsmul_eq_zero_iff (NeZero.pos n)).mp hu
  refine ⟨(m : ℤ), ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (m : ℤ) • ((1 / n : ℚ) : AddCircle (1 : ℚ)) = u.val.val.toAdd
  rw [natCast_zsmul]
  exact (AddCircle.natCast_div_mul_eq_nsmul (p := (1 : ℚ)) (q := (n : ℚ)) 1 m).symm.trans hm

/-- Pinned finite abelian duality identifies the cardinality and finite
type of actual integral rational-circle characters with their source. -/
def originalRationalCircleFiniteCharacterEquiv (A : Type) [AddCommGroup A] [hA : Module ℤ A] [Finite A] :
    (A →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ A := by
  let M := Multiplicative (AddCircle (1 : ℚ))
  let G := Multiplicative A
  letI := originalRationalCircleEnoughRoots (Monoid.exponent G)
  let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some
  let e₀ : (A →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ (A →+ AddCircle (1 : ℚ)) := {
    toFun := LinearMap.toAddMonoidHom
    invFun := fun f => {
      toFun := f
      map_add' := f.map_add
      map_smul' := fun n x => by
        change f (hA.smul n x) = n • f x
        rw [int_smul_eq_zsmul hA n x]
        exact f.map_zsmul n x }
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact e₀.trans
    (AddMonoidHom.toMultiplicative.trans
      ((MulEquiv.monoidHomCongrRightEquiv (toUnits (G := M))).trans
        (e.toEquiv.trans ⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩)))

end
end Dubon2026
