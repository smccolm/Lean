import Dubon2026.FiniteGaloisUnitTowerInflation
import Dubon2026.GaloisUnitInvariantBaseDescent
import Mathlib.FieldTheory.Galois.Infinite

/-! Descend the actual local relation morphism from algebraic-closure units
to original completion units. The kernel fixes the source coefficient, so
infinite Galois fixed-field descent supplies the original finite units.
This removes a descent premise in DUB-17's local relation construction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] (A : Rep.{0} ℤ Gal(L/K))

/-- An actual equivariant unit morphism from a coefficient of the specified Galois field
descends to that same original field, with the original inclusion identity. -/
theorem galoisTowerUnitHom_exists_descent
    (φ : Rep.res (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K)) A ⟶
      Rep.ofAlgebraAutOnUnits K Ω) :
    ∃ ψ : A ⟶ Rep.ofAlgebraAutOnUnits K L,
      (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))).map ψ ≫
        finiteGaloisUnitTowerInclusion K L Ω = φ := by
  let π : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let j := finiteGaloisUnitTowerInclusion K L Ω
  have hj : Function.Injective j.hom :=
    galoisUnitsBaseCoefficient_injective (K := L) (L := Ω)
  letI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  have hval (x : A) : ∃ y : Rep.ofAlgebraAutOnUnits K L, j.hom y = φ.hom x := by
    let u : Ωˣ := Additive.toMul (Rep.toAdditive (φ.hom x))
    have hfixed (g : Gal(Ω/L)) : g (u : Ω) = (u : Ω) := by
      have he : π (g.restrictScalars K) = 1 := by
        apply AlgEquiv.ext
        intro z
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L z).trans (g.commutes z)
      have hx := Rep.hom_comm_apply φ (g.restrictScalars K) x
      change φ.hom (A.ρ (π (g.restrictScalars K)) x) = _ at hx
      rw [he, map_one, Module.End.one_apply] at hx
      exact congrArg (fun z : Rep.ofAlgebraAutOnUnits K Ω =>
        ((Additive.toMul (Rep.toAdditive z) : Ωˣ) : Ω)) hx.symm
    obtain ⟨y, hy⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (K := Ω) (u : Ω)).mpr hfixed
    have hy0 : y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hy
      exact Units.ne_zero u hy.symm
    refine ⟨Rep.toAdditive.symm (Additive.ofMul (Units.mk0 y hy0)), ?_⟩
    change Units.map (algebraMap L Ω).toMonoidHom (Units.mk0 y hy0) = u
    exact Units.ext hy
  choose f hf using hval
  let l : A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K L := {
    toFun := f
    map_add' := by
      intro x y
      apply hj
      simp only [hf, map_add]
    map_smul' := by
      intro n x
      apply hj
      exact (hf _).trans ((φ.hom.toLinearMap.map_smul n x).trans
        ((congrArg (fun z : Rep.ofAlgebraAutOnUnits K Ω => n • z) (hf x)).symm.trans
          (j.hom.toLinearMap.map_smul n (f x)).symm)) }
  let ψ : A ⟶ Rep.ofAlgebraAutOnUnits K L := Rep.ofHom {
    toLinearMap := l
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective _
      obtain ⟨t, ht⟩ := hπ g
      apply hj
      change j.hom (f (A.ρ g x)) = j.hom ((Rep.ofAlgebraAutOnUnits K L).ρ g (f x))
      rw [hf, ← ht]
      exact (Rep.hom_comm_apply φ t x).trans
        ((congrArg ((Rep.ofAlgebraAutOnUnits K Ω).ρ t) (hf x)).symm.trans
          (Rep.hom_comm_apply j t (f x)).symm) }
  refine ⟨ψ, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext hf

end
end Dubon2026
