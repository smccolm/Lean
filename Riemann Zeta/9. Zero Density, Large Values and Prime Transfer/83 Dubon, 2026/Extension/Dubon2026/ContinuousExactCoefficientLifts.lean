import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Actual continuous coefficient lifts for discrete short exact sequences -/

namespace Dubon2026
noncomputable section

variable {R A B C : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- A normalized set-theoretic section of the actual surjective coefficient
map. It is not claimed to be linear; its original zero value is exactly zero. -/
def exactCoefficientSection (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ) (c : C) : B :=
  Function.surjInv hψ c - Function.surjInv hψ 0

/-- The chosen normalized section maps back to the original coefficient. -/
theorem exactCoefficientSection_rightInverse (ψ : B →ₗ[R] C)
    (hψ : Function.Surjective ψ) (c : C) : ψ (exactCoefficientSection ψ hψ c) = c := by
  rw [exactCoefficientSection, map_sub, Function.surjInv_eq hψ c, Function.surjInv_eq hψ 0, sub_zero]

/-- Normalization retains the original zero coefficient exactly. -/
theorem exactCoefficientSection_zero (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ) :
    exactCoefficientSection ψ hψ 0 = 0 := by
  exact sub_self _

/-- Invert the original injective coefficient map on its actual range.
The extension outside that range is zero and is not claimed to be linear. -/
def exactCoefficientPreimage (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (b : B) : A := by
  classical
  exact if hb : b ∈ LinearMap.range φ then (LinearEquiv.ofInjective φ hφ).symm ⟨b, hb⟩ else 0

/-- On the genuine coefficient range, the chosen preimage recovers the exact
original coefficient through the original injective map. -/
theorem exactCoefficientPreimage_map (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
    (b : B) (hb : b ∈ LinearMap.range φ) : φ (exactCoefficientPreimage φ hφ b) = b := by
  rw [exactCoefficientPreimage, dif_pos hb]
  exact LinearEquiv.ofInjective_symm_apply φ (h := hφ) ⟨b, hb⟩

/-- The same actual preimage recovers each original source coefficient. -/
theorem exactCoefficientPreimage_image (φ : A →ₗ[R] B) (hφ : Function.Injective φ) (a : A) :
    exactCoefficientPreimage φ hφ (φ a) = a := by
  apply hφ
  exact exactCoefficientPreimage_map φ hφ (φ a) (LinearMap.mem_range_self φ a)

/-- A section is continuous in the original discrete quotient coefficient
topology; continuity is not silently asserted for arbitrary coefficient topologies. -/
theorem exactCoefficientSection_continuous [TopologicalSpace B] [TopologicalSpace C]
    [DiscreteTopology C] (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ) :
    Continuous (exactCoefficientSection ψ hψ) :=
  continuous_of_discreteTopology

/-- The actual range preimage is continuous when the original middle
coefficient space is discrete, with the original source coefficient topology. -/
theorem exactCoefficientPreimage_continuous [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology B] (φ : A →ₗ[R] B) (hφ : Function.Injective φ) :
    Continuous (exactCoefficientPreimage φ hφ) :=
  continuous_of_discreteTopology

end
end Dubon2026
