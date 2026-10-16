import Dubon2026.ArithmeticOrbitNormalPrimeAction
import Dubon2026.ArithmeticOrbitNormalRepresentative
import Dubon2026.OriginalRationalPrimeOrbits

/-! # Every original prime of a finite Galois arithmetic stage occurs

Use the pinned integral Galois prime-transitivity theorem and lift its
actual finite-stage automorphism to the original unramified union. The
proved representative and prime-action identities identify the chosen
coset's genuine prime. Descent to arbitrary finite stages remains separate.
This is the finite Galois-cover surjectivity input for DUB-17's prime index.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F] [IsGalois ℚ F]

/-- Every genuine original prime above the chosen rational prime is induced by an actual arithmetic coset of a finite Galois stage. -/
theorem rationalArithmeticOrbitPrime_surjective_of_normal
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : originalIntegerPrimeBelow F w = rationalPrimePlace p hp) :
    ∃ c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F,
      rationalArithmeticOrbitPrime a p hp F c = w := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  let c₀ : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F := QuotientGroup.mk 1
  obtain ⟨σ, hσ⟩ := (originalIntegerPrimeBelow_eq_iff_rationalOrbit F w
    (rationalArithmeticOrbitPrime a p hp F c₀)).mp
    (hw.trans (rationalArithmeticOrbitPrime_below a p hp F c₀).symm)
  let τ : Gal(rationalUnramifiedExtension a / ℚ) := σ.liftNormal (rationalUnramifiedExtension a)
  let t : rationalArithmeticGaloisGroup a := τ
  let c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F := QuotientGroup.mk t
  have hc : (rationalArithmeticOrbitRepresentative a F c).restrictNormal F = σ :=
    (rationalArithmeticOrbitRepresentative_restrictNormal_mk a F t).trans
      (σ.restrict_liftNormal (rationalUnramifiedExtension a))
  have hprime := rationalArithmeticOrbitPrime_normal_action a p hp F c
  rw [hc] at hprime
  exact ⟨c, (numberFieldGaloisPlaceEquiv ℚ F σ).injective (hprime.trans hσ.symm)⟩

end
end Dubon2026
