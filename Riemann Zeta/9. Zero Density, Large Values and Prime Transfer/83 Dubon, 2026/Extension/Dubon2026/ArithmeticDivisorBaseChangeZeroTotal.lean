import Dubon2026.ArithmeticRelativeIdeleBaseChangePrimeValues
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant
import Dubon2026.OriginalPrimeFibreDivisorSum

/-! # The primary scaling has zero total for a mixed-degree target

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- The actual scaled base change has zero canonical prime total when the source values are the reciprocal auxiliary-degree indicator and the prescribed order divides both the original base degree and the auxiliary degree. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_divisor_scaled_total_zero
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (d n : ℕ) (hn : 0 < n) (hdn : d ∣ n)
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      d ∣ Module.finrank K E)
    (hx : ∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x =
        if rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) = v then
          (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) else 0) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    rationalArithmeticRelativeStageIdeleTotalInvariant a E M hEM
      ((n / d) •
        rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  let f : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ) := fun u =>
    (n / d) •
      (Nat.card (OriginalFiniteDecompositionGroup K E u) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)))
  calc
    _ = ∑ᶠ u, if originalFinitePrimeBelow K E u = v then f u else 0 := by
      rw [rationalArithmeticRelativeStageIdeleTotalInvariant_apply]
      apply finsum_congr
      intro u
      rw [map_nsmul, rationalArithmeticRelativeStageIdeleBaseChange_primeValues
        a K E L M hKE hKL hEM hLM x v _ hx u]
      exact smul_ite _ _ _ _ |>.trans (by simp only [smul_zero]; rfl)
    _ = ∑ᶠ u : {u : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
        originalFinitePrimeBelow K E u = v}, f u.val := by
      symm
      simpa only [finsum_eq_if] using
        (finsum_subtype_eq_finsum_cond (f := f) (fun u => originalFinitePrimeBelow K E u = v))
    _ = 0 := originalFinitePrime_divisor_scaled_sum_zero K E v d n hn hdn hd

end
end Dubon2026
