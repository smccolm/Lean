import Dubon2026.SourcePermutationCoefficientQuotient
import Dubon2026.SourceGamma0H1Surjection
import Mathlib.Data.ZMod.Basic

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations. The actual binary coefficient module
modulo every positive prime power is a quotient of a finite permutation
module, and the same evaluation is onto its native Gamma0 H1.
Only a coefficient prime greater than three is needed for this route;
the full source weight range is retained. SourceBinaryPermutationHecke supplies
Hecke compatibility. Geometric realization of the permutation terms and a
compatible adic limit remain open.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

/-- Six is invertible modulo every positive power of a prime greater than three. -/
theorem sourcePrimePower_six_isUnit (p m : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    IsUnit (6 : ZMod (p ^ (m + 1))) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (Nat.succ_pos m)).mpr
  intro h
  rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from h) with htwo | hthree
  · have := Nat.le_of_dvd (by decide : 0 < 2) htwo
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 3) hthree
    omega

/-- The indexing vectors in the original binary coefficient module form a finite set. -/
theorem sourceBinaryPrimePowerCoefficient_finite (p m Q w : ℕ) (hp : p.Prime) :
    Finite (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w) := by
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Module.Finite (ZMod (p ^ (m + 1)))
      (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w) :=
    Module.Finite.of_basis (binaryHomogeneousMonomialBasis w)
  exact Module.finite_of_finite (ZMod (p ^ (m + 1)))

/-- The permutation module on these actual vectors is finite over the same prime-power ring. -/
theorem sourceBinaryPrimePowerPermutation_finite (p m Q w : ℕ) (hp : p.Prime) :
    Module.Finite (ZMod (p ^ (m + 1)))
      (sourceCoefficientPermutationRep
        (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w)) := by
  letI := sourceBinaryPrimePowerCoefficient_finite p m Q w hp
  change Module.Finite (ZMod (p ^ (m + 1)))
    (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w →₀ ZMod (p ^ (m + 1)))
  infer_instance

/-- Every original binary H1 class modulo a positive prime power is the evaluation
of a class with finite permutation coefficients; cohomological surjectivity is derived. -/
theorem sourceBinaryPrimePowerPermutation_H1_surjective
    (p m Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    Function.Surjective
      ((groupCohomology.functor (ZMod (p ^ (m + 1))) (Gamma0 Q) 1).map
        (sourceCoefficientPermutationEvaluation
          (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w))) :=
  sourceGamma0H1_map_surjective Q (sourcePrimePower_six_isUnit p m hp hlarge)
    _ (sourceCoefficientPermutationEvaluation_surjective _)

end
end Dubon2026
