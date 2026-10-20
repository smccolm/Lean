import Dubon2026.PolarizedPointTopology

/-! Extract the actual general linear representation on the identity
component of the polarized target. The CM restriction of the original
universal polarized representation uses this extraction on DUB-17's
unframed trace descent and strict-conjugacy route. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  (ρ : G →* PolarizedGaloisGroup ι R) (hρ : ∀ g, polarizedComponent (ρ g) = 1)

/-- The original matrix coordinate is a group representation when the actual source image lies in the identity component. -/
def polarizedIdentityMatrices : G →* GeneralLinearGroup ι R where
  toFun g := (ρ g).left.1
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by
    rw [map_mul]
    change ((ρ g).left * polarizedSwitchAction (ρ g).right (ρ h).left).1 = _
    have hg : (ρ g).right = 1 := hρ g
    rw [hg, map_one]
    rfl

/-- Extraction retains every actual original matrix entry. -/
theorem polarizedIdentityMatrices_apply (g : G) :
    polarizedIdentityMatrices ρ hρ g = (ρ g).left.1 := rfl

/-- The extracted matrix representation has the original continuous matrix-coordinate topology. -/
theorem polarizedIdentityMatrices_continuous [TopologicalSpace G] [TopologicalSpace R]
    (hc : Continuous ρ) : Continuous (polarizedIdentityMatrices ρ hρ) :=
  ((continuous_polarized_iff_coordinates ρ).mp hc).1

/-- Extraction from the actual identity component commutes with the same original coefficient reduction. -/
theorem polarizedIdentityMatrices_reduction {S : Type} [CommRing S] (f : R →+* S) :
    (GeneralLinearGroup.map f).comp (polarizedIdentityMatrices ρ hρ) =
      polarizedIdentityMatrices ((polarizedCoefficientMap f).comp ρ)
        (fun g => (polarizedCoefficientMap_component f (ρ g)).trans (hρ g)) := rfl

end
end Dubon2026
