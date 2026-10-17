import Dubon2026.OriginalTrivialHomologyNaturality

/-! # Group change for the actual trivial integral dual

The pinned internal-Hom unit comparison commutes with the actual group
map. Thus the existing norm-index equivalence retains the Galois subgroup
image required for DUB-17's prescribed-support fixed-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- The actual internal-Hom unit comparison commutes with group change on
the trivial integral dual. -/
theorem originalTrivialDual_unit_groupChange
    {G H : Type} [Group G] [Group H] (f : G →* H) :
    (𝟙 (Rep.res f ((Rep.ihom (Rep.trivial ℤ H ℤ)).obj (Rep.trivial ℤ H ℤ)))) ≫
      (Rep.resFunctor f).map (MonoidalClosed.unitIsoSelf (X := Rep.trivial ℤ H ℤ)).hom =
      (MonoidalClosed.unitIsoSelf (X := Rep.trivial ℤ G ℤ)).hom := by
  rfl

/-- Under the existing actual trivial-dual homology equivalence, group
change is the literal induced map on abelianizations. -/
theorem originalTrivialDualHomologyEquiv_map
    {G H : Type} [Group G] [Group H] (f : G →* H)
    (y : groupHomology ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj (Rep.trivial ℤ G ℤ)) 1) :
    originalTrivialDualHomologyEquiv H
      (groupHomology.map f (𝟙 _) 1 y) =
      (Abelianization.map f).toAdditive (originalTrivialDualHomologyEquiv G y) := by
  let uG := MonoidalClosed.unitIsoSelf (X := Rep.trivial ℤ G ℤ)
  let uH := MonoidalClosed.unitIsoSelf (X := Rep.trivial ℤ H ℤ)
  have hc : groupHomology.map
      (A := (Rep.ihom (Rep.trivial ℤ G ℤ)).obj (Rep.trivial ℤ G ℤ))
      (B := (Rep.ihom (Rep.trivial ℤ H ℤ)).obj (Rep.trivial ℤ H ℤ)) f (𝟙 _) 1 ≫
      groupHomology.map (MonoidHom.id H) uH.hom 1 =
      groupHomology.map (MonoidHom.id G) uG.hom 1 ≫
        groupHomology.map (A := Rep.trivial ℤ G ℤ) (B := Rep.trivial ℤ H ℤ)
          f (𝟙 (Rep.trivial ℤ G ℤ)) 1 := by
    rw [← groupHomology.map_comp, ← groupHomology.map_comp]
    exact congrArg (fun t => groupHomology.map f t 1)
      (originalTrivialDual_unit_groupChange f)
  change originalTrivialHomologyAbelianizationEquiv H
    (groupHomology.map (MonoidHom.id H) uH.hom 1 (groupHomology.map f (𝟙 _) 1 y)) =
      (Abelianization.map f).toAdditive
        (originalTrivialHomologyAbelianizationEquiv G
          (groupHomology.map (MonoidHom.id G) uG.hom 1 y))
  exact (congrArg (originalTrivialHomologyAbelianizationEquiv H)
    (congrArg (fun j => j.hom y) hc)).trans
      (originalTrivialHomologyAbelianizationEquiv_map f _)

end
end Dubon2026
