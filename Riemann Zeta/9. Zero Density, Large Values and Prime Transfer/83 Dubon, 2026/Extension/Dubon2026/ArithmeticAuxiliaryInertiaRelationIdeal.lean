import Dubon2026.MatrixFamilyRelationQuotient
import Dubon2026.ArithmeticSupportInertia

/-! The simultaneous original auxiliary inertia ideal and its genuine
local coefficient quotient. This is the literal ideal identified with
the character augmentation ideal in the universal family theorem. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι O R : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The sum of the actual original local inertia relation ideals at
the selected auxiliary primes. -/
def arithmeticAuxiliaryInertiaRelationIdeal (b : 𝓞 ℚ) (Q : Finset Nat.Primes)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R) : Ideal R :=
  ⨆ p : Q, matrixRepresentationRelationIdeal
    (τ.comp (rationalPrimeArithmeticRestriction b p.val.val p.val.property).toMonoidHom)
    (rationalPrimeNormInertia p.val.val p.val.property)

omit [IsLocalRing R] in
/-- Factoring a coefficient map through the actual auxiliary quotient
is exactly triviality of every original auxiliary inertia matrix. -/
theorem arithmeticAuxiliaryInertiaRelationIdeal_le_kernel_iff
    (b : 𝓞 ℚ) (Q : Finset Nat.Primes)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R)
    {A : Type} [CommRing A] (f : R →+* A) :
    arithmeticAuxiliaryInertiaRelationIdeal b Q τ ≤ RingHom.ker f ↔
      ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
        GeneralLinearGroup.map f (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1 :=
  matrixFamilyRelationIdeal_le_kernel_iff _ _ f

/-- Every lift of residual data pulled back from original support has
a nontrivial local quotient imposing all actual auxiliary inertia
relations. Residual triviality at those primes is derived. -/
theorem arithmeticAuxiliaryInertiaRelationQuotient_isLocal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (a b : 𝓞 ℚ) (hab : a ∣ b) (Q : Finset Nat.Primes)
    (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι R)
    (hτ : ∀ g, GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom (τ g) =
      σ (rationalArithmeticSupportRestriction a b hab g)) :
    IsLocalRing (R ⧸ arithmeticAuxiliaryInertiaRelationIdeal b Q τ) := by
  apply matrixFamilyRelationQuotient_isLocal eR
  intro p g hg
  change GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom
    (τ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = 1
  rw [hτ, rationalArithmeticSupportRestriction_inertia_eq_one a b hab p.val.val p.val.property
    (haway p) g hg, map_one]

end
end Dubon2026
