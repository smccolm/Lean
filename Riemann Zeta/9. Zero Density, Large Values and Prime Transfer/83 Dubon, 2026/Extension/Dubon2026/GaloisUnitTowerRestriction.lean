import Dubon2026.GaloisTowerKernelCohomology

/-! # Original unit H2 restriction when the fixed field is enlarged -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The actual inclusion of automorphisms fixing L among those fixing K. -/
def galoisTowerBaseRestriction : Gal(M/L) →* Gal(M/K) where
  toFun g := g.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original coefficient units and their action agree under the
actual inclusion of the upper fixed-field Galois group. -/
def galoisUnitTowerRestrictionCoefficient :
    Rep.res (galoisTowerBaseRestriction K L M) (Rep.ofAlgebraAutOnUnits K M) ≅
      Rep.ofAlgebraAutOnUnits L M :=
  Rep.mkIso { __ := LinearEquiv.refl ℤ (Additive Mˣ)
              isIntertwining' g := by ext x; rfl }

/-- The actual original H2 restriction induced by literal automorphism
inclusion and the identity on the original extension-field units. -/
def galoisUnitTowerH2Restriction :
    groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits L M) 2 :=
  groupCohomology.map (galoisTowerBaseRestriction K L M)
    (galoisUnitTowerRestrictionCoefficient K L M).hom 2

/-- Actual restriction followed by the genuine kernel identification
is exactly restriction to the original normal subgroup, on the same cochains. -/
theorem galoisUnitTowerH2Restriction_kernel_composition [Normal K L] :
    galoisUnitTowerH2Restriction K L M ≫
      groupCohomology.map (galoisTowerKernelEquiv K L M).toMonoidHom
        (galoisTowerKernelUnitCoefficientIso K L M).hom 2 =
      groupCohomology.map (A := Rep.ofAlgebraAutOnUnits K M)
        (B := Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
          (Rep.ofAlgebraAutOnUnits K M))
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
        (𝟙 _) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains
      (Rep.ofAlgebraAutOnUnits K M) ⟶
      groupCohomology.inhomogeneousCochains
        (Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype
          (Rep.ofAlgebraAutOnUnits K M)) => HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

end
end Dubon2026
