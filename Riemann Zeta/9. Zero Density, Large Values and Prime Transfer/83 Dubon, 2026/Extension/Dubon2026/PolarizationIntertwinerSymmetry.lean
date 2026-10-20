import Dubon2026.PolarizedSwitch

/-! Two actual conjugate-duality intertwiners differ by a scalar when the
original CM matrices have scalar centralizer. This transfers symmetry
from the original universal polarization to the trace-ring intertwiner
and supplies the scalar needed for DUB-17's full strict comparison. -/

namespace Dubon2026
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Surjective arithmetic conjugation and the original scalar centralizer
force two intertwiners of the same whole conjugate-duality equation to
differ by an actual coefficient unit scalar. -/
theorem polarizationIntertwiner_scalar
    (ρ δ : G →* GeneralLinearGroup ι R) (c : G →* G) (hc : Function.Surjective c)
    (hcent : ∀ U : GeneralLinearGroup ι R, (∀ g, U * ρ g = ρ g * U) →
      ∃ u : Rˣ, U = GeneralLinearGroup.scalar ι u)
    (B₀ B₁ : GeneralLinearGroup ι R)
    (h₀ : ∀ g, ρ (c g) = B₀ * δ g * B₀⁻¹)
    (h₁ : ∀ g, ρ (c g) = B₁ * δ g * B₁⁻¹) :
    ∃ u : Rˣ, B₁ = GeneralLinearGroup.scalar ι u * B₀ := by
  have hcomm : ∀ g, (B₁ * B₀⁻¹) * ρ g = ρ g * (B₁ * B₀⁻¹) := by
    intro g
    obtain ⟨x, rfl⟩ := hc g
    calc
      _ = B₁ * δ x * B₀⁻¹ := by rw [h₀ x]; group
      _ = _ := by rw [h₁ x]; group
  obtain ⟨u, hu⟩ := hcent (B₁ * B₀⁻¹) hcomm
  refine ⟨u, ?_⟩
  calc
    B₁ = (B₁ * B₀⁻¹) * B₀ := by group
    _ = _ := by rw [hu]

/-- Original symmetry passes to every intertwiner of the same equation
through the proved scalar comparison, without a separate form classifier. -/
theorem polarizationIntertwiner_symmetric
    (ρ δ : G →* GeneralLinearGroup ι R) (c : G →* G) (hc : Function.Surjective c)
    (hcent : ∀ U : GeneralLinearGroup ι R, (∀ g, U * ρ g = ρ g * U) →
      ∃ u : Rˣ, U = GeneralLinearGroup.scalar ι u)
    (B₀ B₁ : GeneralLinearGroup ι R)
    (h₀ : ∀ g, ρ (c g) = B₀ * δ g * B₀⁻¹)
    (h₁ : ∀ g, ρ (c g) = B₁ * δ g * B₁⁻¹)
    (hB₀ : B₀.val.transpose = B₀.val) : B₁.val.transpose = B₁.val := by
  obtain ⟨u, hu⟩ := polarizationIntertwiner_scalar ρ δ c hc hcent B₀ B₁ h₀ h₁
  rw [hu]
  change (Matrix.scalar ι (u : R) * B₀.val).transpose = Matrix.scalar ι (u : R) * B₀.val
  have hs : (Matrix.scalar ι (u : R)).transpose = Matrix.scalar ι (u : R) := diagonal_transpose _
  rw [transpose_mul, hs, hB₀]
  exact (Matrix.scalar_commute (u : R) (Commute.all _) B₀.val).eq.symm

end Dubon2026
