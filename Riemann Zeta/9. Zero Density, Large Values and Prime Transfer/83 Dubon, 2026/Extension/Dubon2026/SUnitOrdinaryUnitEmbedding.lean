import Dubon2026.SUnitValuationKernel

/-! # The original ordinary units inside the original S-units

The already proved valuation-kernel equivalence supplies the actual
ordinary-unit embedding and its exact image. This is the entry map
for reducing the S-unit logarithmic lattice near zero to the pinned
Dirichlet unit lattice, needed for DUB-17's S-unit Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The original ordinary units included in the original S-unit group via its proved valuation kernel. -/
def sUnitOrdinaryUnitEmbedding (S : Set (HeightOneSpectrum R)) : Rˣ →* S.unit K :=
  ((sUnitValuations (K := K) S).ker).subtype.comp
    (sUnitValuationKernelBaseEquiv (K := K) S).symm.toMonoidHom

/-- The original unit embedding has the original fraction-field value. -/
theorem sUnitOrdinaryUnitEmbedding_val (S : Set (HeightOneSpectrum R)) (u : Rˣ) :
    (sUnitOrdinaryUnitEmbedding (K := K) S u).val =
      Units.map (algebraMap R K).toMonoidHom u := by
  apply Units.ext
  rfl

/-- The original ordinary-unit embedding is injective. -/
theorem sUnitOrdinaryUnitEmbedding_injective (S : Set (HeightOneSpectrum R)) :
    Function.Injective (sUnitOrdinaryUnitEmbedding (K := K) S) :=
  Subtype.val_injective.comp (sUnitValuationKernelBaseEquiv (K := K) S).symm.injective

/-- The original ordinary units are exactly the kernel of the original S-unit finite valuations. -/
theorem sUnitOrdinaryUnitEmbedding_range (S : Set (HeightOneSpectrum R)) :
    (sUnitOrdinaryUnitEmbedding (K := K) S).range = (sUnitValuations (K := K) S).ker := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ((sUnitValuationKernelBaseEquiv (K := K) S).symm u).property
  · intro hx
    refine ⟨sUnitValuationKernelBaseEquiv S ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((sUnitValuationKernelBaseEquiv S).symm_apply_apply ⟨x, hx⟩)

end
end Dubon2026
