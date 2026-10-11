import Dubon2026.ArithmeticUnframedDeterminantFiniteFlatUniversality
import Dubon2026.RationalPrimeArithmeticRestriction

/-! # The original geometric finite-flat deformation quotient at an actual rational prime

Use the original prime completion, its genuine valuation integer ring and the
constructed continuous arithmetic restriction. A finite-flat model of the actual
residual local representation is the remaining explicit local input.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Consume the actual arithmetic trace-ring universal representation to construct its
complete local quotient classifying the prescribed determinant and geometric finite-flat conditions at the actual rational
prime completion and constructed restriction. Residual determinant compatibility and the
genuine residual local model are explicit inputs. -/
theorem arithmeticPrimeDeterminantFiniteFlatUniversality_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)

    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))) :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
        (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
          matrixHopfModelCoefficientIdeal (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
        ∃ hquot : IsLocalRing (T ⧸ J),
          letI := hquot
          IsNoetherianRing (T ⧸ J) ∧ IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)) ∧
          IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
          ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
            [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
            (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
            (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
            ∃ e : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eT J) eA ≃
              {c : OriginalUnframedDeformationClass eA (rationalArithmeticGaloisGroup a) σ //
                originalUnframedHasDeterminant eA (rationalArithmeticGaloisGroup a) σ δ c ∧
                  originalUnframedFiniteFlatScheme (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) eA (rationalArithmeticGaloisGroup a) σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom c},
              ∀ f, (e f).val = originalCoefficientRepresentationClass eT eA
                (rationalArithmeticGaloisGroup a) σ τ hτ
                (originalQuotientCoefficientRestriction eT eA J f).val) := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  exact arithmeticUnframedDeterminantFiniteFlatUniversality_exists
    (R := rationalPrimeLocalIntegerRing p hp)
    (F := rationalPrimeLocalField p hp) (K := rationalPrimeLocalClosure p hp)
    (L := L) a ha p hp hpa σ hσ i₀ δ hδ
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom m

end
end Dubon2026
