import Dubon2026.SourceOriginalGlobalRegionMatching

/-! DUB-17/18 -> original Abel-Jacobi -> the global paired cell family.
The actual global cover has one unique partner arc in a different planar
region. This uses the proved planar two-region incidence, connected actual
arcs and the assembled matching theorem; no pairing hypothesis is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_partner (a : A.Arc) :
    ∃ b : A.Arc, A.regionOf b.1 ≠ A.regionOf a.1 ∧ A.arcPlaces b = A.arcPlaces a := by
  obtain ⟨Z, hsh, hover⟩ := (A.arc_side a).1
  obtain ⟨ρ, hne, hsh', _⟩ := StarProperty.two_regions A.planarData _ Z hsh
  obtain ⟨b, hb, _⟩ := A.exists_unique_arc_in_region hsh'
    (A.arcPlaces_isPreconnected a) (A.arcPlaces_nonempty a) hover
  exact ⟨b, hb.1 ▸ hne, hb.2⟩

theorem partner_unique (a b c : A.Arc)
    (hb : A.regionOf b.1 ≠ A.regionOf a.1) (hc : A.regionOf c.1 ≠ A.regionOf a.1)
    (hba : A.arcPlaces b = A.arcPlaces a) (hca : A.arcPlaces c = A.arcPlaces a) : b = c := by
  obtain ⟨Z, hsh, hover⟩ := (A.arc_side a).1
  obtain ⟨Zb, hshb, hoverb⟩ := (A.arc_side b).1
  obtain ⟨Zc, hshc, hoverc⟩ := (A.arc_side c).1
  have hZb : Zb = Z := (hba ▸ hoverb).eq hover
  have hZc : Zc = Z := (hca ▸ hoverc).eq hover
  subst Zb Zc
  obtain ⟨ρ, _, _, hu⟩ := StarProperty.two_regions A.planarData _ Z hsh
  have hbr : A.regionOf b.1 = ρ := (hu _ hshb).resolve_left hb
  have hcr : A.regionOf c.1 = ρ := (hu _ hshc).resolve_left hc
  exact A.arc_region_ext b c (hbr.trans hcr.symm) (hba.trans hca.symm)

/-- The uniquely determined arc in the other planar region with the same places. -/
def pairArc (a : A.Arc) : A.Arc := Classical.choose (A.exists_partner a)

theorem pairArc_region_ne (a : A.Arc) : A.regionOf (A.pairArc a).1 ≠ A.regionOf a.1 :=
  (Classical.choose_spec (A.exists_partner a)).1

theorem pairArc_places (a : A.Arc) : A.arcPlaces (A.pairArc a) = A.arcPlaces a :=
  (Classical.choose_spec (A.exists_partner a)).2

theorem pairArc_involutive : Function.Involutive A.pairArc := by
  intro a
  apply A.partner_unique (A.pairArc a) (A.pairArc (A.pairArc a)) a
  · exact A.pairArc_region_ne (A.pairArc a)
  · exact (A.pairArc_region_ne a).symm
  · exact A.pairArc_places (A.pairArc a)
  · exact (A.pairArc_places a).symm

theorem pairArc_ne_self (a : A.Arc) : A.pairArc a ≠ a := by
  intro h
  exact A.pairArc_region_ne a (congrArg (fun b => A.regionOf b.1) h)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
