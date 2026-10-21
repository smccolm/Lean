import Dubon2026.SourceBinaryAdditiveCoefficients
import Dubon2026.SourceBinaryCohomologyChange

/-! Rational coordinates of the actual complex binary cocycle.
DUB-17/18 -> residual modular Galois association -> integral H1 Hecke
character -> spanning the complex cocycle space by integral cocycles.
The existing additive polynomial comparison proves that rational basis
coordinates remain genuine cocycles for the original Gamma0 action.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial CongruenceSubgroup

variable {R S : Type} [CommRing R] [CommRing S]

/-- An additive coefficient projection acts on the actual native binary cocycles. -/
def sourceBinaryAdditiveCocycles (φ : R →+ S) (Q w : ℕ) :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w) →+
      groupCohomology.cocycles₁ (sourceBinaryCoefficientRep S Q w) where
  toFun c := ⟨fun g => sourceHomogeneousAdditiveMap w φ (c g),
    (groupCohomology.mem_cocycles₁_iff _).mpr (by
      intro g h
      rw [(groupCohomology.mem_cocycles₁_iff c).mp c.property, map_add]
      congr 1
      exact sourceHomogeneousAdditiveMap_matrix w φ g.val.val (c h))⟩
  map_zero' := by
    apply groupCohomology.cocycles₁_ext
    intro g
    exact map_zero (sourceHomogeneousAdditiveMap w φ)
  map_add' c d := by
    apply groupCohomology.cocycles₁_ext
    intro g
    exact map_add (sourceHomogeneousAdditiveMap w φ) (c g) (d g)

/-- Each coefficient of the transformed original cocycle is its literal additive projection. -/
theorem sourceBinaryAdditiveCocycles_coeff (φ : R →+ S) (Q w : ℕ)
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w))
    (g : Gamma0 Q) (m : Fin 2 →₀ ℕ) :
    coeff m (sourceBinaryAdditiveCocycles φ Q w c g).val = φ (coeff m (c g).val) := rfl

/-- Rational basis-coordinate projection on the actual complex coefficient field. -/
def sourceComplexRationalCoordinate (i : Module.Basis.ofVectorSpaceIndex ℚ ℂ) : ℂ →+ ℚ where
  toFun z := (Module.Basis.ofVectorSpace ℚ ℂ).repr z i
  map_zero' := by simp
  map_add' z t := by simp

/-- A rational coordinate of an original complex binary cocycle is an actual rational binary cocycle. -/
def sourceComplexBinaryCocycleCoordinate (Q w : ℕ)
    (i : Module.Basis.ofVectorSpaceIndex ℚ ℂ) :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℂ Q w) →+
      groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℚ Q w) :=
  sourceBinaryAdditiveCocycles (sourceComplexRationalCoordinate i) Q w

/-- The rational cocycle coordinate has exactly the coefficient of the original complex scalar
in the fixed rational basis. -/
theorem sourceComplexBinaryCocycleCoordinate_coeff (Q w : ℕ)
    (i : Module.Basis.ofVectorSpaceIndex ℚ ℂ)
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℂ Q w))
    (g : Gamma0 Q) (m : Fin 2 →₀ ℕ) :
    coeff m (sourceComplexBinaryCocycleCoordinate Q w i c g).val =
      (Module.Basis.ofVectorSpace ℚ ℂ).repr (coeff m (c g).val) i := rfl

end
end Dubon2026
