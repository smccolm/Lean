import Dubon2026.LocalIntegralPrimeAction
import Dubon2026.LocalIntegralPrimeBelow
import Dubon2026.ChebotarevCyclotomicPrimes

/-! # Original norm-residue Frobenius has the selected finite Frobenius class

This identifies the actual Frobenius used for tame local deformation
classification with the finite class used in auxiliary prime selection for
Dubon Theorem 2.6. The finite field and its embedding are unchanged.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] algebraicLocalIntegerAction

/-- The original arithmetic residue Frobenius restricts to the actual
Chebotarev class of the same unramified rational prime in the embedded field. -/
theorem algebraicLocal_frobenius_class_of_original_residue
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F] [IsGalois ℚ F]
    (e : F →+* L) (p : ℕ) (hp : p.Prime) (hnorm : ‖(p : L)‖ < 1)
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (σ : Gal(F/ℚ)) (φ : Gal(L/K))
    (he : ∀ x : F, e (σ x) = φ (e x))
    (hφ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), φ • x = x ^ p) :
    Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) = ConjClasses.mk σ := by
  let P := algebraicLocalGlobalPrime e
  let v := rationalOriginalPrimePlace p hp
  letI : P.IsPrime := algebraicLocalGlobalPrime_isPrime e
  letI : v.asIdeal.IsPrime := v.isPrime
  have hunder : P.under (𝓞 ℚ) = v.asIdeal := algebraicLocalGlobalPrime_under e p hp hnorm
  have hcard : Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) = p := by
    rw [hunder, rationalOriginalPrimePlace_eq_span, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      Module.finrank_self, pow_one]
  have hσ : IsArithFrobAt (𝓞 ℚ) σ P := by
    intro x
    change σ • x - x ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) ∈ P
    rw [hcard]
    exact algebraicLocalGlobalPrime_frobenius e σ φ he p hφ x
  have hunr' : Chebotarev.UnramifiedIn ℚ F v.asIdeal := by
    simpa only [v, rationalOriginalPrimePlace_eq_span] using hunr
  have h := Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt ℚ F v.asIdeal hunr' σ P hσ
    (show P.LiesOver v.asIdeal from ⟨hunder.symm⟩)
  simpa only [v, rationalOriginalPrimePlace_eq_span] using h

end
end Dubon2026
