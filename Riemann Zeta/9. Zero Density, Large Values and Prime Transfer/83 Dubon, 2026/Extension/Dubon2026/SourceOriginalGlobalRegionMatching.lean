import Dubon2026.SourceOriginalGlobalArcUniqueness

/-! DUB-17/18 -> original Abel-Jacobi -> the global pairing involution.
Assemble local ordinary, branch and exterior matching into the actual global
index type. Region-and-arc uniqueness removes additional local case analysis.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_arc_over_square {p : ℤ × ℤ} (hp : p ∈ A.G.squares)
    (k : Fin (A.G.region p).N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty) (hover : LiesOver L ((A.G.region p).arcSet k)) :
    ∃ a : A.Arc, A.regionOf a.1 = some p ∧ A.arcPlaces a = L := by
  cases hc : A.G.D.capAt p with
  | none =>
    obtain ⟨⟨i, l⟩, he, _⟩ := A.ordinary_arc_matching p hc k hL hne hover.1 hover.2
    exact ⟨⟨.inl (.inl (⟨⟨p, hp⟩, hc⟩, i)), l⟩, rfl, he.symm⟩
  | some b =>
    obtain ⟨hb, hx, hy⟩ := (A.G.D.cap_exact p b).mp hc
    let b' : ({0, 1728} : Finset ℂ) := ⟨b, hb⟩
    have he : A.G.branchSquare b' = p := Prod.ext hx hy
    subst p
    obtain ⟨⟨v, l⟩, hv, _⟩ := A.branch_arc_matching (A.G.branchSquare b') b'
      (A.G.branch_cap b') k hL hne hover.1 hover.2
    exact ⟨⟨.inl (.inr ⟨b', v⟩), l⟩, rfl, hv.symm⟩

theorem exists_unique_arc_in_region {ρ : Option (ℤ × ℤ)} {Z : Set ℂ} (hsh : A.Shares ρ Z)
    {L : Set (Place ℂ F)} (hL : IsPreconnected L) (hne : L.Nonempty) (hover : LiesOver L Z) :
    ∃! a : A.Arc, A.regionOf a.1 = ρ ∧ A.arcPlaces a = L := by
  have hex : ∃ a : A.Arc, A.regionOf a.1 = ρ ∧ A.arcPlaces a = L := by
    cases ρ with
    | none =>
      obtain ⟨k, rfl⟩ := hsh
      obtain ⟨⟨v, l⟩, hv, _⟩ := A.exterior_arc_matching k hL hne hover.1 hover.2
      exact ⟨⟨.inr v, l⟩, rfl, hv.symm⟩
    | some p =>
      obtain ⟨hp, k, rfl⟩ := hsh
      have hp' : p ∈ A.G.squares := Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr hp.1, Finset.mem_Icc.mpr hp.2⟩
      exact A.exists_arc_over_square hp' k hL hne hover
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, fun b hb => A.arc_region_ext b a (hb.1.trans ha.1.symm) (hb.2.trans ha.2.symm)⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
