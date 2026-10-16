import Dubon2026.OriginalIdeleLocalUnitAssembly

/-! # An actual single-prime unit in the original full ideles

Reuse the literal restricted-product constructor and the native dependent
single-coordinate family. This is the coefficient inclusion needed to
place a full-order local H2 class at a proved full-decomposition prime on
DUB-17's full-order idele-class construction. No class or order is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
open IsDedekindDomain

variable (L : Type) [Field L] [NumberField L]

/-- The actual original idele with the given unit at one finite prime and identity at every other finite and infinite place. -/
def originalIdeleSingleFinite (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    (NumberField.AdeleRing (𝓞 L) L)ˣ := by
  classical
  exact originalIdeleFromLocalUnits L (fun _ => 1) (Pi.mulSingle w u) (by
    filter_upwards [Filter.eventually_cofinite_ne w] with v hv
    rw [Pi.mulSingle_eq_of_ne hv]
    exact Subgroup.one_mem _)

/-- The original finite coordinate at the chosen prime is precisely the supplied unit. -/
theorem originalIdeleSingleFinite_same (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) :
    numberFieldIdeleFiniteComponent L w (originalIdeleSingleFinite L w u) = u := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletion L)ˣ) w u

/-- Every other actual original finite coordinate of the single-prime idele is the identity. -/
theorem originalIdeleSingleFinite_ne (w v : HeightOneSpectrum (𝓞 L)) (hv : v ≠ w)
    (u : (w.adicCompletion L)ˣ) :
    numberFieldIdeleFiniteComponent L v (originalIdeleSingleFinite L w u) = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletion L)ˣ) hv u

/-- Every original infinite coordinate of the same single-prime idele is the identity. -/
theorem originalIdeleSingleFinite_infinite (w : HeightOneSpectrum (𝓞 L))
    (u : (w.adicCompletion L)ˣ) (v : NumberField.InfinitePlace L) :
    numberFieldIdeleInfiniteComponent L v (originalIdeleSingleFinite L w u) = 1 := rfl

/-- Single-prime insertion into the actual original full ideles preserves the original unit group law. -/
def originalIdeleSingleFiniteHom (w : HeightOneSpectrum (𝓞 L)) :
    (w.adicCompletion L)ˣ →* (NumberField.AdeleRing (𝓞 L) L)ˣ where
  toFun := originalIdeleSingleFinite L w
  map_one' := by
    apply originalIdele_eq_of_components L
    · intro v
      rw [map_one]
      by_cases hv : v = w
      · subst v
        exact originalIdeleSingleFinite_same L w 1
      · exact originalIdeleSingleFinite_ne L w v hv 1
    · intro v
      rw [originalIdeleSingleFinite_infinite, map_one]
  map_mul' u z := by
    apply originalIdele_eq_of_components L
    · intro v
      rw [map_mul]
      by_cases hv : v = w
      · subst v
        simp only [originalIdeleSingleFinite_same]
      · simp only [originalIdeleSingleFinite_ne L w v hv, one_mul]
    · intro v
      simp only [map_mul, originalIdeleSingleFinite_infinite, one_mul]

end
end Dubon2026
