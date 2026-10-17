import Dubon2026.OriginalPrimeFibreCompletionDegree

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- The literal fibre degree is unchanged when its lower prime is written
as the actual contraction of the same upper prime. -/
theorem originalPrimeFibreCompletionDegree_at_contraction
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : OriginalPrimeFibre K L v) :
    originalPrimeFibreCompletionDegree K L v w =
      originalPrimeFibreCompletionDegree K L (originalFinitePrimeBelow K L w.val) ⟨w.val, rfl⟩ := by
  rcases w with ⟨w, hw⟩
  cases hw
  rfl

end
end Dubon2026
