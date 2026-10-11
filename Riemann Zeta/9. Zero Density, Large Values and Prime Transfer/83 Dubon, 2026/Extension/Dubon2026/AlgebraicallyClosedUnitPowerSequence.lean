import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # The actual unit power map and root-of-unity coefficient sequence -/

namespace Dubon2026
noncomputable section

variable {Ω : Type} [Field Ω]

/-- The kernel of the original unit nth-power homomorphism is exactly the
original subgroup of nth roots of unity, including its actual unit inclusion. -/
theorem originalUnitPower_kernel (n : ℕ) :
    (powMonoidHom n : Ωˣ →* Ωˣ).ker = rootsOfUnity n Ω := by
  exact (rootsOfUnity_eq_ker (k := n) (M := Ω)).symm

/-- The original root-of-unity inclusion is injective as a map of actual units. -/
theorem originalRootUnitInclusion_injective (n : ℕ) :
    Function.Injective ((rootsOfUnity n Ω).subtype : rootsOfUnity n Ω →* Ωˣ) :=
  Subtype.val_injective

/-- Algebraic closedness supplies an actual unit nth root of every original
unit for each positive n. No divisibility or Kummer exactness is postulated. -/
theorem algebraicallyClosedUnitPower_surjective [IsAlgClosed Ω]
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : Ωˣ →* Ωˣ) := by
  intro u
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (u : Ω) hn
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, zero_pow hn.ne'] at hx
    exact Units.ne_zero u hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact hx

end
end Dubon2026
