import Dubon2026.FiniteGaloisH2BaseChangeComparison
import Dubon2026.FiniteGaloisUnitH2InflationRestriction

/-! # Actual finite algebraic H2 descent preserves the original torsion

The existing exact original inflation-restriction sequence and injective
inflation turn actual base-change killing into an actual descended class.
Injectivity also retains its original annihilator. This is the descent
step after constructed cyclic killing on DUB-17's invariant sum-zero route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A killed original finite global-unit H2 class descends to an actual class with the same annihilator and identical inflation into the original common field. -/
theorem originalFiniteH2_exists_torsion_descent_of_baseChange_zero
    (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [FiniteDimensional K M] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K L] [IsGalois K M]
    (q : ℕ) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (hkill : groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (galoisUnitBaseChangeInclusion K E L M) 2 x = 0) :
    ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2, q • y = 0 ∧
      groupCohomology.map (AlgEquiv.restrictNormalHom E) (finiteGaloisUnitTowerInclusion K E M) 2 y =
        groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion K L M) 2 x := by
  let iE := groupCohomology.map (AlgEquiv.restrictNormalHom E) (finiteGaloisUnitTowerInclusion K E M) 2
  let iL := groupCohomology.map (AlgEquiv.restrictNormalHom L) (finiteGaloisUnitTowerInclusion K L M) 2
  have hres : galoisUnitTowerH2Restriction K E M (iL x) = 0 := by
    have he := congrArg (fun f : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits E M) 2 => f x)
      (galoisUnitH2_inflation_restriction_baseChange K E L M)
    exact he.trans hkill
  obtain ⟨y, hy⟩ := (finiteGaloisUnitH2_inflation_exists_iff_restriction_zero K E M (iL x)).mpr hres
  refine ⟨y, ?_, hy⟩
  apply (ModuleCat.mono_iff_injective _).mp (finiteGaloisUnitH2Inflation_mono K E M)
  change iE (q • y) = iE 0
  rw [map_nsmul, map_zero, hy, ← map_nsmul, hx]
  exact map_zero iL.hom

end
end Dubon2026
