import Dubon2026.UnramifiedUnionOpenSubgroupCharacters
import Dubon2026.UnramifiedUnionFiniteFieldCriterion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The actual rational arithmetic Galois group in the chosen algebraic closure -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The original rational unramified union inside the actual chosen algebraic closure of Q. -/
abbrev rationalUnramifiedExtension (a : 𝓞 ℚ) :=
  originalUnramifiedGaloisUnion (Ω := AlgebraicClosure ℚ) a

/-- The actual rational arithmetic extension is Galois by the proved normal-stage construction. -/
instance rationalUnramifiedExtensionGalois (a : 𝓞 ℚ) :
    IsGalois ℚ (rationalUnramifiedExtension a) := by
  let U := rationalUnramifiedExtension a
  have h : @IsGalois ℚ _ U _ U.algebra' := originalUnramifiedGaloisUnion_isGalois a
  have he : U.algebra' = (inferInstance : Algebra ℚ U) := Subsingleton.elim _ _
  exact Eq.mp (congrArg (fun α : Algebra ℚ U => @IsGalois ℚ _ U _ α) he) h

/-- The genuine automorphism group of the constructed rational arithmetic extension with its original Krull topology. -/
def rationalArithmeticGaloisGroup (a : 𝓞 ℚ) : ProfiniteGrp := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact InfiniteGalois.profiniteGalGrp ℚ U

/-- Original finite Galois fields inside the chosen algebraic closure belong to the rational arithmetic extension exactly when their original primes are unramified outside the exceptional integer. -/
theorem rationalUnramifiedExtension_finiteGalois_le_iff
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    (letI : Algebra ℚ F := F.algebra'
     F.toIntermediateField ≤ rationalUnramifiedExtension a ↔
      ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1) :=
  originalUnramifiedUnion_finiteGalois_le_iff a ha F

/-- Every original open subgroup of the actual rational arithmetic Galois group has finitely many original continuous prime-order characters for primes dividing the original exceptional integer. -/
theorem rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (H : OpenSubgroup (rationalArithmeticGaloisGroup a)) :
    Finite (H →ₜ* Multiplicative (ZMod p)) :=
  originalQUnramifiedUnion_openSubgroup_prime_characters_finite a ha p hp hpa H

end
end Dubon2026
