import Dubon2026.ArithmeticDeterminantFiniteFlatCotangent
import Dubon2026.RationalPrimeArithmeticRestriction

/-! # The actual prime-local geometric condition as an arithmetic cotangent image -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- At the actual rational prime completion, the constructed arithmetic trace
quotient's cotangent injects into genuine continuous adjoint cohomology, with image
exactly the original prescribed-determinant, geometric finite-flat condition. The
actual residual model and residual determinant compatibility remain explicit inputs. -/
theorem arithmeticPrimeDeterminantFiniteFlatCotangent_exists
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
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))
    :
    ∃ T : Subalgebra O (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ),
      T = ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ ∧
      (letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
       ∃ hlocal : IsLocalRing T,
         letI := hlocal
         IsNoetherianRing T ∧ ∃ _htop : IsAdic (IsLocalRing.maximalIdeal T),
         IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
         ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
           (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι T)
           (hτ : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
             τ.toMonoidHom = σ),
           (let J := representationDeterminantIdeal τ.toMonoidHom δ ⊔
              matrixHopfModelCoefficientIdeal (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
            ∃ hquot : IsLocalRing (T ⧸ J),
              letI := hquot
              IsNoetherianRing (T ⧸ J) ∧ ∃ hQ : IsAdic (IsLocalRing.maximalIdeal (T ⧸ J)),
                IsAdicComplete (IsLocalRing.maximalIdeal (T ⧸ J)) (T ⧸ J) ∧
                (let eQ := originalLocalQuotientResidueEquiv eT J
                 let τQ := originalCoefficientQuotientRepresentation (rationalArithmeticGaloisGroup a) τ J
                 let hτQ := originalCoefficientQuotientRepresentation_residue eT (rationalArithmeticGaloisGroup a) σ τ hτ J
                 let LQ := originalCotangentCohomologyClassLinearMap hQ eQ (rationalArithmeticGaloisGroup a) σ hσ τQ hτQ
                 Function.Injective LQ ∧ ∀ x : ContinuousMatrixAdjointH1 σ hσ,
                   x ∈ LinearMap.range LQ ↔
                     (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
                        ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
                      ∃ c : OriginalUnframedDeformationClass (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ,
                        (originalUnframedHasDeterminant (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ δ c ∧
                          originalUnframedFiniteFlatScheme (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
                            (relativeDualNumberResidueEquiv O) (rationalArithmeticGaloisGroup a) σ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom c) ∧
                        relativeDualNumberUnframedCohomologyMap (rationalArithmeticGaloisGroup a) σ hσ c = x)))) := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  exact arithmeticDeterminantFiniteFlatCotangent_exists
    (R := rationalPrimeLocalIntegerRing p hp)
    (F := rationalPrimeLocalField p hp) (K := rationalPrimeLocalClosure p hp)
    (L := L) a ha p hp hpa σ hσ i₀ δ hδ
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom m

end
end Dubon2026
