import Dubon2026.PolarizedResidualIdeal

/-! The actual polarized representation over the literal coefficient
quotient. Its matrix, component, similitude and residual compatibilities
are derived from the original relations. Nontriviality is supplied by the
proved residual criterion when this construction is used for DUB-17. -/

namespace Dubon2026
open Matrix

variable {G R A ι : Type*} [Group G] [CommRing R] [CommRing A]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
  (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
  [Nontrivial (R ⧸ representationPolarizedIdeal τ χ ν)]

/-- Quotienting the original matrix coefficients constructs the source polarized representation. -/
noncomputable def representationPolarizedQuotientRepresentation :
    G →* PolarizedGaloisGroup ι (R ⧸ representationPolarizedIdeal τ χ ν) :=
  polarizedRepresentationOfEquations
    ((GeneralLinearGroup.map (Ideal.Quotient.mk (representationPolarizedIdeal τ χ ν))).comp τ)
    χ ((Units.map (Ideal.Quotient.mk (representationPolarizedIdeal τ χ ν)).toMonoidHom).comp ν)
    (representationPolarizedIdeal_quotient_equations τ χ ν)

/-- The constructed quotient representation retains every original matrix modulo the actual ideal. -/
theorem representationPolarizedQuotientRepresentation_block (g : G) :
    polarizedBlockRepresentation (representationPolarizedQuotientRepresentation τ χ ν g) =
      GeneralLinearGroup.map (Ideal.Quotient.mk (representationPolarizedIdeal τ χ ν)) (τ g) :=
  polarizedRepresentationOfEquations_block _ _ _ _ _

/-- The same quotient representation has the original component and fixed source similitude. -/
theorem representationPolarizedQuotientRepresentation_characters (g : G) :
    polarizedComponent (representationPolarizedQuotientRepresentation τ χ ν g) = χ g ∧
      polarizedSimilitude (representationPolarizedQuotientRepresentation τ χ ν g) =
        Units.map (Ideal.Quotient.mk (representationPolarizedIdeal τ χ ν)).toMonoidHom (ν g) :=
  ⟨polarizedRepresentationOfEquations_component _ _ _ _ _,
    polarizedRepresentationOfEquations_similitude _ _ _ _ _⟩

/-- Residual reduction of the actual quotient representation recovers the original polarized point. -/
theorem representationPolarizedQuotientRepresentation_residue [Nontrivial A]
    (f : R →+* A) (σ : G →* PolarizedGaloisGroup ι A)
    (hτ : ∀ g, GeneralLinearGroup.map f (τ g) = polarizedBlockRepresentation (σ g))
    (hχ : ∀ g, polarizedComponent (σ g) = χ g)
    (hν : ∀ g, polarizedSimilitude (σ g) = Units.map f.toMonoidHom (ν g)) (g : G) :
    polarizedCoefficientMap
        (Ideal.Quotient.lift (representationPolarizedIdeal τ χ ν) f
          (representationPolarizedIdeal_le_residual_kernel τ χ ν f σ hτ hχ hν))
        (representationPolarizedQuotientRepresentation τ χ ν g) = σ g := by
  apply polarizedBlockRepresentation_injective
  rw [← polarizedBlockRepresentation_map, representationPolarizedQuotientRepresentation_block]
  change GeneralLinearGroup.map f (τ g) = polarizedBlockRepresentation (σ g)
  exact hτ g

end Dubon2026
