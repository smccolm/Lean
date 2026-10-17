import Dubon2026.OriginalHomologyGroupChangeNaturality

/-! # Coinvariant representatives under actual group change

The pinned degree-zero comparison transports the same representative
through a genuine group homology map. Together with boundary naturality,
this identifies the boundary of a subgroup norm witness in the full group,
as required by DUB-17's prescribed-support fixed-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {A : Rep.{0} k G} {B : Rep.{0} k H} (f : G →* H) (φ : A ⟶ Rep.res f B)

/-- The actual group-change map sends the degree-zero class of a literal
coefficient to the class of its literal coefficient image. -/
theorem originalHomologyH0_groupChange_mk (x : A) :
    (groupHomology.H0Iso B).hom
      (groupHomology.map f φ 0
        ((groupHomology.H0Iso A).inv (Representation.Coinvariants.mk A.ρ x))) =
      Representation.Coinvariants.mk B.ρ (φ.hom x) := by
  have hA := congrArg (fun j => j.hom x)
    (groupHomology.coinvariantsMk_comp_H0Iso_inv A)
  have hmap := congrArg (fun j => j.hom x) (groupHomology.H0π_comp_map f φ)
  have hB := congrArg (fun j => j.hom (φ.hom x))
    (groupHomology.H0π_comp_H0Iso_hom B)
  exact (congrArg (fun t => (groupHomology.H0Iso B).hom (groupHomology.map f φ 0 t)) hA).trans
    ((congrArg (fun t => (groupHomology.H0Iso B).hom t) hmap).trans hB)

/-- A known literal coinvariant representative is preserved by the genuine
group and coefficient map. -/
theorem originalHomologyH0_groupChange_of_mk (z : groupHomology A 0) (x : A)
    (hz : (groupHomology.H0Iso A).hom z = Representation.Coinvariants.mk A.ρ x) :
    (groupHomology.H0Iso B).hom (groupHomology.map f φ 0 z) =
      Representation.Coinvariants.mk B.ρ (φ.hom x) := by
  have he : z = (groupHomology.H0Iso A).inv (Representation.Coinvariants.mk A.ρ x) := by
    rw [← hz]
    exact ((groupHomology.H0Iso A).toLinearEquiv.symm_apply_apply z).symm
  rw [he]
  exact originalHomologyH0_groupChange_mk f φ x

/-- The literal representative of a connecting boundary is transported by
the actual group-change diagram. -/
theorem originalHomology_groupChange_boundary_representative
    {X : ShortComplex (Rep.{0} k G)} {Y : ShortComplex (Rep.{0} k H)}
    (f : G →* H) (ψ : X ⟶ Y.map (Rep.resFunctor f))
    (hX : X.ShortExact) (hY : Y.ShortExact)
    (y : groupHomology X.X₃ 1) (a : X.X₁)
    (hy : (groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl y) =
      Representation.Coinvariants.mk X.X₁.ρ a) :
    (groupHomology.H0Iso Y.X₁).hom
      (groupHomology.δ hY 1 0 rfl (groupHomology.map f ψ.τ₃ 1 y)) =
      Representation.Coinvariants.mk Y.X₁.ρ (ψ.τ₁.hom a) := by
  have hn := congrArg (fun j => j.hom y)
    (originalHomologyGroupChange_delta_naturality f ψ hX hY 1 0 rfl)
  exact (congrArg (fun z => (groupHomology.H0Iso Y.X₁).hom z) hn.symm).trans
    (originalHomologyH0_groupChange_of_mk f ψ.τ₁ _ a hy)

end
end Dubon2026
