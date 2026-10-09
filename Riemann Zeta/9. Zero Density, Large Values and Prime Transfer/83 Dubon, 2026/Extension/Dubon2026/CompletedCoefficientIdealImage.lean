import Dubon2026.AdicCoefficientCompletionMaps

/-! # The genuine ideal image under the original completed coefficient map -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Extending the original ideal and then applying the actual completed coefficient map gives exactly the extension of its original image ideal. -/
theorem adicCoefficientCompletionMap_ideal_image
    (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (hIJ : I.map f.toRingHom = J) :
    (I.map (algebraMap R (AdicCompletion I R))).map
      (adicCoefficientCompletionMap I J f hf).toRingHom =
        J.map (algebraMap A (AdicCompletion J A)) := by
  have hcomp : (adicCoefficientCompletionMap I J f hf).toRingHom.comp
      (algebraMap R (AdicCompletion I R)) =
      (algebraMap A (AdicCompletion J A)).comp f.toRingHom := by
    apply RingHom.ext
    intro r
    exact adicCoefficientCompletionMap_of I J f hf r
  rw [Ideal.map_map, hcomp, ← Ideal.map_map, hIJ]

end
end Dubon2026
