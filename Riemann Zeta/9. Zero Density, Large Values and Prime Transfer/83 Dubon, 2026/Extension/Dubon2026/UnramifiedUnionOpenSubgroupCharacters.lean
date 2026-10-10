import Dubon2026.UnramifiedUnionFiniteBaseCharacters
import Dubon2026.FiniteBaseGaloisTopology

/-! # Actual finite prime-character sets on every original open arithmetic subgroup -/

namespace Dubon2026

noncomputable section
open scoped NumberField

variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- Every original open subgroup of the constructed rational arithmetic Galois group has finitely many actual continuous prime-order characters. The finite intermediate field is its genuine fixed field, with the original Krull topology. -/
theorem originalQUnramifiedUnion_openSubgroup_prime_characters_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ H : OpenSubgroup Gal(U/ℚ), Finite (H →ₜ* Multiplicative (ZMod p))) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra ℚ U := U.algebra'
  dsimp only
  intro H
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let C : ClosedSubgroup Gal(U/ℚ) := ⟨H.toSubgroup, H.isClosed⟩
  let E := IntermediateField.fixedField C.toSubgroup
  letI : Algebra ℚ E := E.algebra'
  have hfix : E.fixingSubgroup = H.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField C
  letI : FiniteDimensional ℚ E := (InfiniteGalois.isOpen_iff_finite E).mp (by
    rw [hfix]
    exact H.isOpen)
  letI : Finite (Gal(U/E) →ₜ* Multiplicative (ZMod p)) :=
    originalQUnramifiedUnion_finiteBase_prime_characters_finite a ha p hp hpa E
  have hf := finiteBase_fixingSubgroup_characters_finite
    (T := Multiplicative (ZMod p)) E
  rw [hfix] at hf
  exact hf

end
end Dubon2026
