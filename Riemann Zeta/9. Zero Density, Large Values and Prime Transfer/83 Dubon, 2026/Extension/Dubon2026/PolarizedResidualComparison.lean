import Dubon2026.PolarizedBlockNaturality

/-! Residual comparison from the original coefficient square and exact matrix
realization. The actual polarized coefficient quotient uses this lemma to
recover its original residual representation on the DUB-17 CM route. -/

namespace Dubon2026
open Matrix

variable {G R Q A ι : Type*} [Group G] [CommRing R] [CommRing Q] [CommRing A]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] [Nontrivial A]

/-- A commuting original coefficient square and its exact matrix comparison
recover the full polarized residual representation by faithfulness. -/
theorem polarizedRepresentation_residue_of_block_diagram
    (q : R →+* Q) (f : Q →+* A) (r : R →+* A)
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (ρ : G →* PolarizedGaloisGroup ι Q) (σ : G →* PolarizedGaloisGroup ι A)
    (hf : f.comp q = r)
    (hb : ∀ g, polarizedBlockRepresentation (ρ g) = GeneralLinearGroup.map q (τ g))
    (hr : ∀ g, GeneralLinearGroup.map r (τ g) = polarizedBlockRepresentation (σ g))
    (g : G) : polarizedCoefficientMap f (ρ g) = σ g := by
  apply polarizedBlockRepresentation_injective
  rw [← polarizedBlockRepresentation_map, hb, ← GeneralLinearGroup.map_comp_apply,
    ← GeneralLinearGroup.map_comp, hf]
  exact hr g

end Dubon2026
