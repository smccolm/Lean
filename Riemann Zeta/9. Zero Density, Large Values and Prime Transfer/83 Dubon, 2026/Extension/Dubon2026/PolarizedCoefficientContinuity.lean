import Dubon2026.PolarizedPointTopology
import Dubon2026.PolarizedCoefficientMap

/-! Continuity of the actual polarized coefficient functor, needed to
evaluate DUB-17's descended trace-ring representation at original local
coefficient maps. The topology remains the original coordinate topology. -/

namespace Dubon2026
open Matrix

variable {ι R A : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A]
  [TopologicalSpace R] [TopologicalSpace A]

/-- Genuine continuous coefficient maps induce continuous maps on the
entire original disconnected polarized group. -/
theorem polarizedCoefficientMap_continuous (f : R →+* A) (hf : Continuous f) :
    Continuous (polarizedCoefficientMap (ι := ι) f) := by
  have h := (continuous_polarized_iff_coordinates (id : PolarizedGaloisGroup ι R → _)).mp continuous_id
  apply (continuous_polarized_iff_coordinates _).mpr
  refine ⟨?_, ?_, h.2.2⟩
  · have hm : Continuous (GeneralLinearGroup.map (n := ι) f) := by
      apply Units.continuous_map
      apply continuous_matrix
      intro i j
      exact hf.comp (continuous_apply_apply i j)
    exact hm.comp h.1
  · exact (Units.continuous_map hf).comp h.2.1

end Dubon2026
