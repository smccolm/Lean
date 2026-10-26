import Mathlib.RingTheory.Ideal.Maps

/-! DUB-17/18 -> original all-weight adic association -> finite operator
characters. Name the native surjective ring-map descent and its whole-map
evaluation identity before specializing to the original large H1 objects.
The source kernel condition and mathematical construction are unchanged. -/
namespace Dubon2026
noncomputable section
variable {A B C : Type} [Ring A] [Ring B] [Ring C]

/-- Native character descent through the actual surjective operator map. -/
def sourceFiniteOperatorCharacterDescend (θ : A →+* B) (hθ : Function.Surjective θ)
    (χ : A →+* C) (h : RingHom.ker θ ≤ RingHom.ker χ) : B →+* C :=
  θ.liftOfSurjective hθ ⟨χ, h⟩

/-- The descended character pulls back to the entire original character. -/
theorem sourceFiniteOperatorCharacterDescend_comp
    (θ : A →+* B) (hθ : Function.Surjective θ)
    (χ : A →+* C) (h : RingHom.ker θ ≤ RingHom.ker χ) :
    (sourceFiniteOperatorCharacterDescend θ hθ χ h).comp θ = χ :=
  RingHom.liftOfSurjective_comp θ hθ ⟨χ, h⟩

end
end Dubon2026
