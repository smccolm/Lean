import Dubon2026.PolarizedTwistedDual
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! Strict changes of basis preserve the actual multiplier-twisted dual.
This transports the CM trace descent to the dual representation, removing
the dual-trace equality hypothesis in DUB-17's polarization descent. -/

namespace Dubon2026
open Matrix

variable {G ι R k : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing k]

/-- A genuine strict matrix conjugator gives its inverse transpose as a
strict conjugator of the source multiplier-twisted duals. -/
theorem matrixStrictlyConjugate_twistedDual (r : R →+* k)
    (ρ τ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ)
    (h : MatrixStrictlyConjugate r ρ τ) :
    MatrixStrictlyConjugate r (polarizedTwistedDual ρ μ) (polarizedTwistedDual τ μ) := by
  obtain ⟨U, hU, he⟩ := h
  refine ⟨polarizedContragredient U, ?_, ?_⟩
  · rw [polarizedContragredient_map, hU, map_one]
  · intro g
    simp only [polarizedTwistedDual_apply, he g, map_mul, map_inv]
    have hc := (polarizedScalar_commute (μ g) (polarizedContragredient U)).eq
    calc
      _ = (GeneralLinearGroup.scalar ι (μ g) * polarizedContragredient U) *
          polarizedContragredient (ρ g) * (polarizedContragredient U)⁻¹ := by
            simp only [mul_assoc]
      _ = _ := by rw [hc]; simp only [mul_assoc]

end Dubon2026
