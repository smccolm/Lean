import Dubon2026.PolarizedRepresentationIdeal
import Mathlib.Algebra.Algebra.Hom

/-! The exact polarized coefficient ideal under original base-algebra
maps. Its prescribed similitude specializes from the same base character,
as required when restricting native framed universality for DUB-17. -/

namespace Dubon2026
open Matrix

variable {G O R A ι : Type*} [Group G] [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A] [Fintype ι] [DecidableEq ι]

/-- A base-algebra map kills the actual polarized ideal exactly when the original
matrices satisfy the source equations with the same base similitude. -/
theorem representationPolarizedIdeal_le_algebraKernel_iff
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Oˣ) (f : R →ₐ[O] A) :
    representationPolarizedIdeal τ χ ((Units.map (algebraMap O R)).comp ν) ≤ RingHom.ker f.toRingHom ↔
      PolarizedMatrixEquations ((GeneralLinearGroup.map f.toRingHom).comp τ) χ
        ((Units.map (algebraMap O A)).comp ν) := by
  have he : (Units.map f.toRingHom.toMonoidHom).comp ((Units.map (algebraMap O R)).comp ν) =
      (Units.map (algebraMap O A)).comp ν := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact f.commutes (ν g : O)
  rw [representationPolarizedIdeal_le_kernel_iff, he]

end Dubon2026
