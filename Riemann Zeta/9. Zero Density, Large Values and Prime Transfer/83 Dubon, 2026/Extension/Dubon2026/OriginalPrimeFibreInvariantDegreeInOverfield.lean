import Dubon2026.OriginalPrimeFibreDegreeInOverfield
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Sum the actual normalized invariant contribution over the original
prime fibre of the nonnormal intermediate field. -/
theorem originalPrimeFibre_invariant_degree_in_galois_overfield
    (K E M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M]
    (v : HeightOneSpectrum (𝓞 K)) (z : AddCircle (1 : ℚ)) :
    (∑ᶠ u : OriginalPrimeFibre K E v, originalPrimeFibreCompletionDegree K E v u • z) =
      Module.finrank K E • z := by
  letI : Fintype (OriginalPrimeFibre K E v) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_nsmul_assoc,
    ← finsum_eq_sum_of_fintype, originalPrimeFibreCompletionDegree_sum_in_galois_overfield K E M v]

end
end Dubon2026
