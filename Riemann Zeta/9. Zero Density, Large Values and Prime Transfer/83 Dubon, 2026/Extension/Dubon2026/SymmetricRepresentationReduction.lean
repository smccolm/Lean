import Dubon2026.HomogeneousSymmetricContinuity

/-! # The actual symmetric-power representation respects arithmetic coefficient change -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R S : Type*} [Group G] [CommRing R]
    [CommRing S]

/-- The original matrix representation acts through its genuine homogeneous symmetric-power matrices. -/
def symmetricMatrixRepresentation (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    G →* GeneralLinearGroup (Fin (n + 1)) R := (homogeneousSymmetricGL n).comp ρ

/-- Changing the original coefficient ring before or after taking the actual symmetric power gives exactly the same representation. -/
theorem symmetricMatrixRepresentation_map (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (φ : R →+* S) :
    (GeneralLinearGroup.map φ).comp (symmetricMatrixRepresentation n ρ) =
      symmetricMatrixRepresentation n ((GeneralLinearGroup.map φ).comp ρ) := by
  apply MonoidHom.ext
  intro g
  exact homogeneousSymmetricGL_map n φ (ρ g)

/-- An original change of basis induces the literal symmetric-power change of basis, so actual conjugate rank-two representations have conjugate symmetric powers over the same coefficient ring. -/
theorem symmetricMatrixRepresentation_conjugate (n : ℕ)
    (ρ σ : G →* GeneralLinearGroup (Fin 2) R) (A : GeneralLinearGroup (Fin 2) R)
    (h : ∀ g, σ g = A * ρ g * A⁻¹) (g : G) :
    symmetricMatrixRepresentation n σ g =
      homogeneousSymmetricGL n A * symmetricMatrixRepresentation n ρ g *
        (homogeneousSymmetricGL n A)⁻¹ := by
  change homogeneousSymmetricGL n (σ g) = _
  rw [h, map_mul, map_mul, map_inv]
  rfl

/-- Every original continuous rank-two matrix representation has a genuine continuous symmetric-power representation in the same topological coefficient ring. -/
theorem symmetricMatrixRepresentation_continuous [TopologicalSpace G]
    [TopologicalSpace R] [IsTopologicalRing R]
    (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R) (hρ : Continuous ρ) :
    Continuous (symmetricMatrixRepresentation n ρ) :=
  (homogeneousSymmetricGL_continuous n).comp hρ

end
end Dubon2026
