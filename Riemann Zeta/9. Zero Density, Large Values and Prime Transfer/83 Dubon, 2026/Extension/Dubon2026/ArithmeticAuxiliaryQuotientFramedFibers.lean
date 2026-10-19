import Dubon2026.ArithmeticAuxiliaryInertiaRelationIdeal
import Dubon2026.LocalQuotientCoefficientFibers

/-! The original coefficient classification restricts to the genuine
simultaneous auxiliary inertia quotient. This conditional assembly
keeps every original matrix value; its arithmetic universal-ring
consumer supplies the existing classification and evaluation theorem.
The resulting fiber is then compared with original support using the
proved arithmetic descent equivalence. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι O R A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Residual triviality of the actual auxiliary inertia matrices
gives a nontrivial local simultaneous quotient. -/
theorem arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (b : 𝓞 ℚ) (Q : Finset Nat.Primes)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom
        (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1) :
    IsLocalRing (R ⧸ arithmeticAuxiliaryInertiaRelationIdeal b Q τ) :=
  matrixFamilyRelationQuotient_isLocal eR _ _ hI

/-- The actual coefficient quotient classifies exactly the original
framed fixed-determinant lifts with trivial auxiliary inertia. Its
unquotiented coefficient classification and evaluation are the only
classification inputs. -/
def arithmeticAuxiliaryQuotientFramedFiberEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (b : 𝓞 ℚ) (Q : Finset Nat.Primes)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom
        (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1)
    (E : OriginalContinuousCoefficientFiber eR eA ≃
      {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ //
        ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)})
    (heval : ∀ f g, (E f).val.val g = GeneralLinearGroup.map f.val.toRingHom (τ g)) :
    (letI := arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue eR b Q τ hI
     OriginalContinuousCoefficientFiber
       (originalLocalQuotientResidueEquiv eR (arithmeticAuxiliaryInertiaRelationIdeal b Q τ)) eA ≃
       {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ //
         (∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)) ∧
         ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
           f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1}) := by
  let J := arithmeticAuxiliaryInertiaRelationIdeal b Q τ
  letI := arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue eR b Q τ hI
  let eI : {f : OriginalContinuousCoefficientFiber eR eA // J ≤ RingHom.ker f.val.toRingHom} ≃
      {f : {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ //
        ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)} //
        ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
          f.val.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1} :=
    E.subtypeEquiv (fun f => by
      change arithmeticAuxiliaryInertiaRelationIdeal b Q τ ≤ RingHom.ker f.val.toRingHom ↔ _
      rw [arithmeticAuxiliaryInertiaRelationIdeal_le_kernel_iff]
      simp only [heval])
  exact (originalLocalQuotientCoefficientFiberEquiv eR eA J).trans
    (eI.trans (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ =>
        ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g))
      (fun f => ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
        f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1)))

/-- The quotient classification evaluates the original universal
matrix through the literal quotient coefficient map. -/
theorem arithmeticAuxiliaryQuotientFramedFiberEquiv_evaluation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (b : 𝓞 ℚ) (Q : Finset Nat.Primes)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom
        (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1)
    (E : OriginalContinuousCoefficientFiber eR eA ≃
      {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ //
        ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)})
    (heval : ∀ f g, (E f).val.val g = GeneralLinearGroup.map f.val.toRingHom (τ g)) :
    (letI := arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue eR b Q τ hI
     ∀ (f : OriginalContinuousCoefficientFiber
       (originalLocalQuotientResidueEquiv eR (arithmeticAuxiliaryInertiaRelationIdeal b Q τ)) eA) g,
       (arithmeticAuxiliaryQuotientFramedFiberEquiv eR eA b Q σ δ τ hI E heval f).val.val g =
         GeneralLinearGroup.map f.val.toRingHom
           (GeneralLinearGroup.map (Ideal.Quotient.mk (arithmeticAuxiliaryInertiaRelationIdeal b Q τ)) (τ g))) := by
  let J := arithmeticAuxiliaryInertiaRelationIdeal b Q τ
  letI := arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue eR b Q τ hI
  intro f g
  change (E (originalQuotientCoefficientRestriction eR eA J f).val).val.val g = _
  rw [heval]
  change GeneralLinearGroup.map (f.val.toRingHom.comp (Ideal.Quotient.mk J)) (τ g) = _
  rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply]

end
end Dubon2026
