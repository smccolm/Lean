import Dubon2026.OriginalCohomologyGroupChangeNaturality

/-! # Naturality for the actual coefficient connecting maps

This specialization keeps the original coefficient diagrams explicit
on the two-shift route to DUB-17's converse norm criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G : Type} [CommRing k] [Group G]
variable {X Y : ShortComplex (Rep.{0} k G)}

/-- A genuine coefficient diagram commutes with the actual ordinary connecting homomorphism. -/
theorem originalCoefficient_delta_naturality (d : X ⟶ Y)
    (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map (MonoidHom.id G) d.τ₁ j =
      groupCohomology.map (MonoidHom.id G) d.τ₃ i ≫ groupCohomology.δ hY i j hij := by
  exact originalCohomologyGroupChange_delta_naturality (MonoidHom.id G)
    { τ₁ := d.τ₁, τ₂ := d.τ₂, τ₃ := d.τ₃,
      comm₁₂ := d.comm₁₂, comm₂₃ := d.comm₂₃ } hX hY i j hij

end
end Dubon2026
