import Dubon2026.SUnitFiniteLogNormalization

/-! # The original full S-unit logarithm in its sum-zero hyperplane

Every coordinate is the logarithm of an original normalized absolute
value. The original S-unit product formula proves hyperplane membership.
This is the full representation whose lattice and Galois action feed
DUB-17's S-unit Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- All original infinite places together with the specified original finite support. -/
abbrev SUnitLogPlace := InfinitePlace K ⊕ S

/-- The real coordinate space on the actual places occurring in the S-unit product formula. -/
abbrev SUnitFullLogSpace := SUnitLogPlace K S → ℝ

/-- Sum of the original all-place logarithmic coordinates. -/
def sUnitLogCoordinateSum : SUnitFullLogSpace K S →ₗ[ℝ] ℝ where
  toFun z := ∑ p, z p
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' c z := by
    change (∑ p, c * z p) = c * ∑ p, z p
    rw [Finset.mul_sum]

/-- The actual sum-zero hyperplane of original all-place logarithmic coordinates. -/
abbrev SUnitLogHyperplane := (sUnitLogCoordinateSum K S).ker

/-- The full original normalized logarithmic map before restricting the codomain. -/
def sUnitFullLogAmbient : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →+
    SUnitFullLogSpace K S where
  toFun x p := match p with
    | Sum.inl w => w.mult * Real.log (w x.toMul.val.val)
    | Sum.inr v => Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.toMul.val.val)
  map_zero' := by
    funext p
    cases p <;> simp
  map_add' x y := by
    funext p
    cases p <;> simp [Real.log_mul, mul_add]

/-- The original product formula places the actual full logarithm in the original sum-zero hyperplane. -/
theorem sUnitFullLogAmbient_mem_hyperplane
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitFullLogAmbient K S x ∈ SUnitLogHyperplane K S := by
  change ∑ p, sUnitFullLogAmbient K S x p = 0
  rw [Fintype.sum_sum_type]
  exact sUnit_sum_log_absoluteValues_eq_zero K S x.toMul

/-- The actual original full logarithm, with codomain in its proved sum-zero hyperplane. -/
def sUnitFullLog : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →+
    SUnitLogHyperplane K S :=
  (sUnitFullLogAmbient K S).codRestrict _ (sUnitFullLogAmbient_mem_hyperplane K S)

/-- Forgetting the hyperplane membership returns the same original absolute-value logarithms. -/
theorem sUnitFullLog_coe
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    (sUnitFullLog K S x).val = sUnitFullLogAmbient K S x := rfl

end
end Dubon2026
