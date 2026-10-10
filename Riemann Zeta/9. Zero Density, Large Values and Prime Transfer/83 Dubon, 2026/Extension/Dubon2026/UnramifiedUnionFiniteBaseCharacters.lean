import Dubon2026.UnramifiedUnionCyclotomicRoots
import Dubon2026.UnramifiedUnionFiniteRamification
import Dubon2026.FiniteExceptionalIntegerPrimes
import Dubon2026.UnramifiedCyclotomicCharacterDescent

/-! # Actual prime characters over every finite base of the original rational arithmetic union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {Ω : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- Every actual finite intermediate base in the constructed rational arithmetic union has finitely many original continuous prime-order characters, when that prime divides the original exceptional integer. All root, finite-set and ramification inputs are derived for this same union. -/
theorem originalQUnramifiedUnion_finiteBase_prime_characters_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ E : IntermediateField ℚ U,
       letI : Algebra ℚ E := E.algebra'
       ∀ [FiniteDimensional ℚ E], Finite (Gal(U/E) →ₜ* Multiplicative (ZMod p))) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra ℚ U := U.algebra'
  dsimp only
  intro E
  letI : Algebra ℚ E := E.algebra'
  intro hE
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := originalQUnramifiedUnion_exists_primitiveRoot (Ω := Ω) a p hpa
  let S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | a ∈ v.asIdeal}
  have hS : S.Finite := heightOnePrimes_containing_nonzero_finite a ha
  have hunram := originalUnramifiedUnion_finiteGalois_unramified (Ω := Ω) a ha
  exact unramified_prime_characters_finite_of_ambient_root
    {v : HeightOneSpectrum (𝓞 E) | v.under (𝓞 ℚ) ∈ S}
    (heightOneUnder_preimage_finite S hS)
    (fun F v hv => finiteBase_unramified_finite_subextensions S hunram E F v hv)
    p hp hζ

end
end Dubon2026
