import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Extend the actual quotient functional in prime-torsion dévissage

DUB-17's relation reduction needs a functional on the image of H1 of
the induced coefficient to extend to H1 of its literal quotient. Prime
annihilation gives a vector space; the pinned complementary projection
and quotient-kernel isomorphism construct the required integral map.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A functional killing the kernel of a map into a prime-annihilated
module factors through that map on the entire target module. -/
theorem originalPrimeTorsion_functional_extension
    (p : ℕ) [Fact p.Prime] {U V W : Type}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module ℤ U] [Module ℤ V] [Module ℤ W]
    (hp : ∀ v : V, p • v = 0) (f : U →ₗ[ℤ] V) (g : U →ₗ[ℤ] W)
    (hk : f.ker ≤ g.ker) :
    ∃ θ : V →ₗ[ℤ] W, θ.comp f = g := by
  letI : Module (ZMod p) V := AddCommGroup.zmodModule hp
  letI : Module ℤ f.range := f.range.module
  letI : Module ℤ (U ⧸ f.ker) := Submodule.Quotient.module f.ker
  let M : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p f.range.toAddSubgroup
  obtain ⟨M', hMM'⟩ := Submodule.exists_isCompl (K := ZMod p) (V := V) M
  let pr : V →+ V := (M.projection M' hMM').toAddMonoidHom
  let r : V →+ f.range := {
    toFun := fun v => ⟨pr v, Submodule.projection_apply_mem hMM' v⟩
    map_zero' := by apply Subtype.ext; exact pr.map_zero
    map_add' := fun v w => by apply Subtype.ext; exact pr.map_add v w }
  let t : V →ₗ[ℤ] f.range := {
    toFun := r
    map_add' := r.map_add
    map_smul' := fun a v => by
      change r ((inferInstance : Module ℤ V).smul a v) =
        (inferInstance : Module ℤ f.range).smul a (r v)
      rw [int_smul_eq_zsmul (inferInstance : Module ℤ V),
        int_smul_eq_zsmul (inferInstance : Module ℤ f.range)]
      exact r.map_zsmul a v }
  let q := (f.ker.liftQ g hk).comp f.quotKerEquivRange.symm.toLinearMap
  refine ⟨q.comp t, ?_⟩
  apply LinearMap.ext
  intro x
  have ht : t (f x) = ⟨f x, LinearMap.mem_range_self f x⟩ := by
    apply Subtype.ext
    exact Submodule.projection_apply_left hMM' ⟨f x, LinearMap.mem_range_self f x⟩
  change (f.ker.liftQ g hk) (f.quotKerEquivRange.symm (t (f x))) = g x
  rw [ht, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end
end Dubon2026
