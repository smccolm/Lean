import Dubon2026.ArithmeticAuxiliaryQuotientFramedFibers
import Dubon2026.ArithmeticFixedDeterminantRepresentation

/-! The actual arithmetic universal ring with every original auxiliary
inertia relation imposed. Residual inertia triviality makes its literal
quotient local and preserves the original coefficient residue field.
This is the ring to be specialized by the universal character
augmentation in the Dubon Theorem 2.6 deformation comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  (b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
  (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (ResidueField O))
  (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)

/-- Impose all selected original inertia relations in the actual
arithmetic fixed-determinant universal ring. -/
abbrev ArithmeticAuxiliaryUniversalRing (Q : Finset Nat.Primes) :=
  ArithmeticFixedDeterminantRing b hb q hq hqb σ hσ δ ⧸
    arithmeticAuxiliaryInertiaRelationIdeal b Q
      (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom

variable
  (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
  (Q : Finset Nat.Primes)
  (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
    σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1)

include hδ hI

/-- The actual universal representation satisfies the original
auxiliary inertia equations after reduction to its true residue field. -/
theorem arithmeticFixedDeterminantRepresentation_auxiliary_residue_one :
    (letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
     ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
       GeneralLinearGroup.map
         (localCoefficientReduction (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ)).toRingHom
         (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ
           (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  intro p g hg
  exact (DFunLike.congr_fun (arithmeticFixedDeterminantRepresentation_residue b hb q hq hqb σ hσ δ hδ)
    (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)).trans (hI p g hg)

/-- The original residual auxiliary inertia equations make the
actual universal auxiliary quotient nontrivial and local. -/
theorem arithmeticAuxiliaryUniversalRing_isLocal :
    IsLocalRing (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  exact arithmeticAuxiliaryInertiaRelationQuotient_isLocal_of_residue
    (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ) b Q
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom
    (arithmeticFixedDeterminantRepresentation_auxiliary_residue_one b hb q hq hqb σ hσ δ hδ Q hI)

/-- The true residue field of the literal simultaneous auxiliary
quotient is the original coefficient residue field. -/
def arithmeticAuxiliaryUniversalResidueEquiv :
    (letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
     ResidueField (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) ≃ₐ[O] ResidueField O) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
  exact originalLocalQuotientResidueEquiv
    (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ)
    (arithmeticAuxiliaryInertiaRelationIdeal b Q
      (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom)

end
end Dubon2026
