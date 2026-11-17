import Dubon2026.SourceAbsoluteCyclotomicLocal
import Dubon2026.SourceRationalLocalFrobenius
import Dubon2026.SourceOriginalTateInertia

/-! DUB-17/18 -> actual rank-two realization -> original determinant and
oddness. The existing valuation Frobenius bridge gives the cyclotomic
value at every actual norm-residue Frobenius, with the same original
embedding and without a supplied valuation or Frobenius witness. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- The actual cyclotomic character has its original rational-prime value
at every original good-prime norm Frobenius. -/
theorem sourceAbsoluteCyclotomicCharacter_norm_frobenius
    (N q : ℕ) [NeZero N] (hq : q.Prime) (haway : ¬q ∣ N)
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
    (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq))
    (hφ : ∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) :
    (sourceAbsoluteCyclotomicCharacter N (embeddedNormalGaloisRestriction e φ) : ZMod N) = q := by
  let A := sourceRationalLocalValuation q hq e
  letI := SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits A q hq
    (sourceRationalLocalValuation_prime q hq e)
  obtain ⟨hd, hres⟩ := sourceRationalLocalValuation_frobenius q hq e φ hφ
  have hN : (N : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ q]
    exact haway
  exact sourceAbsoluteCyclotomicCharacter_frobenius A N q hN
    ⟨embeddedNormalGaloisRestriction e φ, hd⟩ hres

end
end Dubon2026
