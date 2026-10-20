import Dubon2026.PolarizedBlockContinuity
import Dubon2026.PolarizedCoefficientMap

/-! The actual multiplier-twisted dual of continuous CM matrices, with
coefficient compatibility. This is the second representation in the
equal-trace comparison required for DUB-17's polarization descent. -/

namespace Dubon2026
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original multiplier times inverse transpose, as a whole matrix representation. -/
def polarizedTwistedDual (ρ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ) :
    G →* GeneralLinearGroup ι R :=
  (MonoidHom.fst _ _).comp (polarizedSwitchAut.toMonoidHom.comp (ρ.prod μ))

/-- The twisted dual retains the source multiplier and literal inverse transpose. -/
theorem polarizedTwistedDual_apply (ρ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ) (g : G) :
    polarizedTwistedDual ρ μ g = GeneralLinearGroup.scalar ι (μ g) * polarizedContragredient (ρ g) := rfl

/-- Continuity follows from the original scalar and inverse-transpose maps. -/
theorem polarizedTwistedDual_continuous [TopologicalSpace G]
    [TopologicalSpace R] [IsTopologicalRing R]
    (ρ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ)
    (hρ : Continuous ρ) (hμ : Continuous μ) : Continuous (polarizedTwistedDual ρ μ) :=
  (polarizedScalar_continuous.comp hμ).mul (polarizedContragredient_continuous.comp hρ)

/-- Actual coefficient change preserves the whole multiplier-twisted dual. -/
theorem polarizedTwistedDual_map {A : Type*} [CommRing A]
    (f : R →+* A) (ρ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ) :
    (GeneralLinearGroup.map f).comp (polarizedTwistedDual ρ μ) =
      polarizedTwistedDual ((GeneralLinearGroup.map f).comp ρ)
        ((Units.map f.toMonoidHom).comp μ) := by
  apply MonoidHom.ext
  intro g
  change GeneralLinearGroup.map f
    (GeneralLinearGroup.scalar ι (μ g) * polarizedContragredient (ρ g)) = _
  rw [map_mul, polarizedScalar_map, polarizedContragredient_map]
  rfl

end Dubon2026
