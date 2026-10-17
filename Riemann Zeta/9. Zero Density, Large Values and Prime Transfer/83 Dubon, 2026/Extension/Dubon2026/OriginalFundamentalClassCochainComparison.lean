import Dubon2026.OriginalFundamentalSplittingSequence

/-! # A literal cochain from compatibility of fundamental classes

The pinned H2 quotient criterion turns the required group/coefficient
compatibility into an explicit one-cochain. This discharges the cochain
premise of the local/global fundamental-extension diagram needed for
DUB-17's outside-unit inertia comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (C : Rep.{0} k G) (D : Rep.{0} k H) (f : G →* H)
  (ℓ : C ⟶ Rep.res f D) (φ : groupCohomology.cocycles₂ C)
  (ψ : groupCohomology.cocycles₂ D)

/-- Equality of the actual mapped and restricted H2 classes supplies a
literal one-cochain with the precise correction sign. -/
theorem originalFundamentalClass_exists_cochain_comparison
    (hclass : groupCohomology.map (MonoidHom.id G) ℓ 2 (groupCohomology.H2π C φ) =
      groupCohomology.map f (𝟙 (Rep.res f D)) 2 (groupCohomology.H2π D ψ)) :
    ∃ b : G → D, ∀ g h : G,
      ℓ.hom (φ (g, h)) - ψ (f g, f h) = D.ρ (f g) (b h) - b (g * h) + b g := by
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply] at hclass
  obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_iff _ _).mp hclass
  refine ⟨b, fun g h => ?_⟩
  have he := congrFun hb (g, h)
  rw [groupCohomology.d₁₂_hom_apply] at he
  exact he.symm

end
end Dubon2026
