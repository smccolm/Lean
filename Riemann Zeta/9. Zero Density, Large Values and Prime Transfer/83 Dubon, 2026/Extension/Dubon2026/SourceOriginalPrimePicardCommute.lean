import Dubon2026.SourceOriginalPrimePeriodCommute
import Dubon2026.SourceOriginalTatePrimeHeckeTensor

/-! DUB-17/18 -> the actual rank-two Galois Hecke realization -> commuting
arithmetic Picard correspondences. The analytic commutation theorem descends
to the actual period quotient, and injectivity of the proved Picard
comparison and complex base extension transports it to Qbar.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential OriginalConstantField
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimePeriodLatticeHecke_commute (ell q : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) :
    Commute (originalPrimePeriodLatticeHecke N ell b) (originalPrimePeriodLatticeHecke N q b) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun T : Module.End ℂ (Fin n → ℂ) => T x.val)
    (originalPrimePeriodHecke_commute N ell q b).eq

theorem originalHeckePicard_complex_prime_commute (ell q : Nat.Primes) :
    Function.Commute (originalHeckePicard ℂ N ell.val) (originalHeckePicard ℂ N q.val) := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ V
  let P := originalAnalyticPlace N UpperHalfPlane.I
  intro x
  apply (originalPicardPeriodEquiv N b P).injective
  change originalPicardPeriodEquiv N b P (originalHeckePicard ℂ N ell.val
      (originalHeckePicard ℂ N q.val x)) =
    originalPicardPeriodEquiv N b P (originalHeckePicard ℂ N q.val
      (originalHeckePicard ℂ N ell.val x))
  simp only [originalPicardPeriodEquiv_originalPrimeHecke N ell,
    originalPicardPeriodEquiv_originalPrimeHecke N q]
  exact congrArg (fun T : Module.End ℤ _ => T (originalPicardPeriodEquiv N b P x))
    (originalPrimePeriodQuotientHecke_commute N ell q b).eq

theorem originalHeckePicard_arithmetic_prime_commute (ell q : Nat.Primes) :
    Function.Commute (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)
      (originalHeckePicard (AlgebraicClosure ℚ) N q.val) := by
  intro x
  apply complexPicardMap_injective N
  change complexPicardMap N (originalHeckePicard (AlgebraicClosure ℚ) N ell.val
      (originalHeckePicard (AlgebraicClosure ℚ) N q.val x)) =
    complexPicardMap N (originalHeckePicard (AlgebraicClosure ℚ) N q.val
      (originalHeckePicard (AlgebraicClosure ℚ) N ell.val x))
  simp only [complexPicardMap_originalHeckePicard]
  exact originalHeckePicard_complex_prime_commute N ell q (complexPicardMap N x)

end
end Dubon2026.SourceFunctionField.OriginalChart
