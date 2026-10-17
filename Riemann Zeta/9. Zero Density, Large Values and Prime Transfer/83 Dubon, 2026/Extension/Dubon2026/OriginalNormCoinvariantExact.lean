import Dubon2026.OriginalNormCoinvariantTransfer

/-! # Norm injectivity descends through the actual presentation

In an original short exact sequence, a coefficient with injective norm
on coinvariants passes that property to its quotient when the kernel
has invariant norm preimages. This supplies the precise negative-one
vanishing input for DUB-17's integral projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A literal short exact sequence transfers norm injectivity on coinvariants from the middle coefficient to the quotient when kernel invariants are norms. -/
theorem originalNormCoinvariantInjective_of_shortExact
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hmid : OriginalNormCoinvariantInjective X.X₂)
    (hker : ∀ z : X.X₁, z ∈ X.X₁.ρ.invariants → ∃ t : X.X₁, X.X₁.ρ.norm t = z) :
    OriginalNormCoinvariantInjective X.X₃ := by
  intro x hx
  obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective X.g).mp hX.epi_g x
  have hnorm : X.g.hom (X.X₂.ρ.norm y) = 0 := by
    rw [originalCoefficientMorphism_norm, hy, hx]
  have hex := (ShortComplex.moduleCat_exact_iff
    (X.map (forget₂ (Rep k G) (ModuleCat k)))).mp
      (hX.exact.map (forget₂ (Rep k G) (ModuleCat k)))
  obtain ⟨z, hz⟩ := hex (X.X₂.ρ.norm y) hnorm
  change X.f.hom z = X.X₂.ρ.norm y at hz
  have hzinv : z ∈ X.X₁.ρ.invariants := by
    intro g
    apply (Rep.mono_iff_injective X.f).mp hX.mono_f
    rw [Rep.hom_comm_apply]
    change X.X₂.ρ g (X.f.hom z) = X.f.hom z
    rw [hz, Representation.self_norm_apply]
  obtain ⟨t, ht⟩ := hker z hzinv
  have hdiff : X.X₂.ρ.norm (y - X.f.hom t) = 0 := by
    rw [map_sub, ← originalCoefficientMorphism_norm, ht]
    change X.X₂.ρ.norm y - X.f.hom z = 0
    rw [hz, sub_self]
  have hclass := congrArg (Representation.Coinvariants.map X.X₂.ρ X.X₃.ρ X.g.hom)
    (hmid _ hdiff)
  rw [Representation.Coinvariants.map_mk, map_zero] at hclass
  have hfg : X.g.hom (X.f.hom t) = 0 :=
    congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom t) X.zero
  simpa only [map_sub, hy, hfg, sub_zero] using hclass

end
end Dubon2026
