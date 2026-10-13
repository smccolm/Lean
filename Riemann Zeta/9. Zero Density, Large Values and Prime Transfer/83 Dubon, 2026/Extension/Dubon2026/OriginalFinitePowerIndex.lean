import Dubon2026.LocalFieldPowerIndexScalar
import Dubon2026.OriginalAdicScalarQuotientCardinality

/-! # Exact numerical power indices on the original finite completions

The original local field, small-unit inverse, scalar quotient and residue
comparison give the finite factor needed in DUB-17's supported-idele power
product. The defect is the norm of the actual prime-power factor of `(n)`;
no p-adic principal-unit classification or new local model is required.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- A primitive nth root in the original number field gives the exact
power quotient cardinality in each actual finite completion. -/
theorem originalFinitePowerQuotient_card (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) =
      n * (n * Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)}))) := by
  let F := v.adicCompletion K
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  haveI : ProperSpace F := original_adicCompletion_properSpace K v
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := normValuation_isNonarchimedeanLocalField F
  have hnF : (n : F) ≠ 0 := by
    have h := (algebraMap K F).injective.ne (Nat.cast_ne_zero.mpr hn.ne' : (n : K) ≠ 0)
    simpa only [map_natCast, map_zero] using h
  let O := (ValuativeRel.valuation F).integer
  let e := originalAdicIntegerNormEquiv K v
  have hQ : Nat.card (O ⧸ (Ideal.span {(n : O)} : Ideal O)) =
      Nat.card (v.adicCompletionIntegers K ⧸
        (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K))) := by
    apply Nat.card_congr
    exact (Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm.toEquiv
  rw [localField_unitPower_index_scalar_of_primitiveRoot F n hnF
    (algebraMap K F ζ) (hζ.map_of_injective (algebraMap K F).injective), hQ,
    originalAdic_natCast_quotient_card K v n hn.ne']

end
end Dubon2026
