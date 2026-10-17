import Dubon2026.OriginalInvariantConnectingKernel

/-! # H1 of the actual kernel from invariant lifting

The genuine long exact sequence turns invariant lifting and middle H1
vanishing into kernel H1 vanishing. This is used for the infinite actual
fundamental coefficient's free cover in DUB-17's finite duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Literal invariant lifting and middle H1 vanishing kill first cohomology of the actual kernel. -/
theorem originalKernel_first_zero_of_invariant_lifting
    {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hmid : Limits.IsZero (groupCohomology X.X₂ 1))
    (hlift : ∀ z : X.X₃, z ∈ X.X₃.ρ.invariants →
      ∃ x : X.X₂, x ∈ X.X₂.ρ.invariants ∧ X.g.hom x = z) :
    Limits.IsZero (groupCohomology X.X₁ 1) := by
  have hd := groupCohomology.epi_δ_of_isZero hX 0 hmid
  have hs := (ModuleCat.epi_iff_surjective _).mp hd
  have hz : ∀ y : groupCohomology X.X₁ 1, y = 0 := by
    intro y
    obtain ⟨z, rfl⟩ := hs y
    refine groupCohomology.H0_induction_on X.X₃ z ?_
    intro zi
    obtain ⟨x, hx, hg⟩ := hlift zi.val zi.property
    exact originalInvariantConnecting_zero_of_lift hX zi x hx hg
  letI : Subsingleton (groupCohomology X.X₁ 1) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end
end Dubon2026
