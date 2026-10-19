import Dubon2026.PolarizedRepresentationIdeal
import Mathlib.RingTheory.LocalRing.Quotient

/-! An actual residual polarized representation makes the literal source
equation quotient nontrivial and local. This derives properness rather
than assuming a polarized coefficient ring in DUB-17's deformation chain. -/

namespace Dubon2026
open Matrix

variable {G R A ι : Type*} [Group G] [CommRing R] [CommRing A]
  [Fintype ι] [DecidableEq ι]

/-- Original residual compatibility puts the actual polarized ideal in the reduction kernel. -/
theorem representationPolarizedIdeal_le_residual_kernel
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (f : R →+* A) (σ : G →* PolarizedGaloisGroup ι A)
    (hτ : ∀ g, GeneralLinearGroup.map f (τ g) = polarizedBlockRepresentation (σ g))
    (hχ : ∀ g, polarizedComponent (σ g) = χ g)
    (hν : ∀ g, polarizedSimilitude (σ g) = Units.map f.toMonoidHom (ν g)) :
    representationPolarizedIdeal τ χ ν ≤ RingHom.ker f := by
  apply (representationPolarizedIdeal_le_kernel_iff_relations τ χ ν f).mpr
  intro g
  apply (polarizedRelationMatrix_eq_zero_iff _ _ _).mpr
  exact ⟨σ g, hχ g, hν g, (hτ g).symm⟩

/-- The source-compatible residual representation proves that the original quotient is nontrivial. -/
theorem representationPolarizedQuotient_nontrivial [Nontrivial A]
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (f : R →+* A) (σ : G →* PolarizedGaloisGroup ι A)
    (hτ : ∀ g, GeneralLinearGroup.map f (τ g) = polarizedBlockRepresentation (σ g))
    (hχ : ∀ g, polarizedComponent (σ g) = χ g)
    (hν : ∀ g, polarizedSimilitude (σ g) = Units.map f.toMonoidHom (ν g)) :
    Nontrivial (R ⧸ representationPolarizedIdeal τ χ ν) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top f)
    (representationPolarizedIdeal_le_residual_kernel τ χ ν f σ hτ hχ hν)

/-- The same actual source equation quotient is local when the original coefficient ring is local. -/
theorem representationPolarizedQuotient_isLocal [Nontrivial A] [IsLocalRing R]
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (f : R →+* A) (σ : G →* PolarizedGaloisGroup ι A)
    (hτ : ∀ g, GeneralLinearGroup.map f (τ g) = polarizedBlockRepresentation (σ g))
    (hχ : ∀ g, polarizedComponent (σ g) = χ g)
    (hν : ∀ g, polarizedSimilitude (σ g) = Units.map f.toMonoidHom (ν g)) :
    IsLocalRing (R ⧸ representationPolarizedIdeal τ χ ν) := by
  letI := representationPolarizedQuotient_nontrivial τ χ ν f σ hτ hχ hν
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (representationPolarizedIdeal τ χ ν)) Ideal.Quotient.mk_surjective

end Dubon2026
