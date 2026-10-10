import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Ideal.Over

/-! # Restriction of original integral inertia to actual normal subfields -/

namespace Dubon2026

noncomputable section
open scoped NumberField

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Normal K E]

/-- The original integer-ring inclusion intertwines an actual Galois automorphism with its restriction to the original normal subfield. -/
theorem integral_restrictNormal_smul
    (σ : Gal(L/K)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ.restrictNormal E • x) =
      σ • algebraMap (𝓞 E) (𝓞 L) x := by
  apply NumberField.RingOfIntegers.ext
  exact σ.restrictNormal_commutes E (x : E)

/-- Restricting an actual inertia automorphism gives an inertia automorphism of the actual contracted integer-ring ideal. No finiteness of the whole extension is assumed. -/
theorem integral_inertia_restrictNormal_mem
    (P : Ideal (𝓞 L)) (σ : Gal(L/K)) (hσ : σ ∈ P.inertia Gal(L/K)) :
    σ.restrictNormal E ∈ (P.under (𝓞 E)).inertia Gal(E/K) := by
  intro x
  change algebraMap (𝓞 E) (𝓞 L) (σ.restrictNormal E • x - x) ∈ P
  rw [map_sub, integral_restrictNormal_smul]
  exact hσ (algebraMap (𝓞 E) (𝓞 L) x)

end
end Dubon2026
