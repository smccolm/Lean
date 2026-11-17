import Dubon2026.SourceAbsoluteCyclotomicLocal
import Dubon2026.SourceRationalLocalValuation
import Dubon2026.SourceOriginalTateInertia

/-! DUB-17/18 -> original rank-two association -> unramified norm inertia.
Reuse the proved valuation-inertia transport and actual cyclotomic inertia.
This discharges the determinant factor in the finite joint trace's
norm-inertia invariance, without rebuilding local root arguments. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- Original local norm inertia acts trivially on the actual finite
cyclotomic character whenever the conductor is prime to that residue prime. -/
theorem sourceAbsoluteCyclotomicCharacter_normInertia (N : ℕ) [NeZero N]
    (q : ℕ) (hq : q.Prime) (haway : ¬q ∣ N)
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
    (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq))
    (hg : g ∈ rationalPrimeNormInertia q hq) :
    sourceAbsoluteCyclotomicCharacter N (embeddedNormalGaloisRestriction e g) = 1 := by
  let A := sourceRationalLocalValuation q hq e
  letI := SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits A q hq
    (sourceRationalLocalValuation_prime q hq e)
  have hN : (N : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ q]
    exact haway
  obtain ⟨d, hd, he⟩ := sourceRationalLocalValuation_inertia q hq e g hg
  rw [← he]
  exact sourceAbsoluteCyclotomicCharacter_inertia A N hN d hd

end
end Dubon2026
