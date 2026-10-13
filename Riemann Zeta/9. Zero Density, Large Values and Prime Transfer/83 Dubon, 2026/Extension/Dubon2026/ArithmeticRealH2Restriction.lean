import Dubon2026.RealPlaceFiniteCoefficientH2
import Dubon2026.ContinuousCohomologyRestriction

/-! # The actual real restriction of original arithmetic H2

The existing original arithmetic embedding into C defines the real restriction.
Its target H2 vanishes by the proved order-two averaging at odd auxiliary primes.
This discharges the real term needed alongside finite support in DUB-17's
global invariant-sum obligation, without assuming global reciprocity.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Restrict the actual real absolute Galois group through the original
arithmetic embedding into C, with its already proved Krull continuity. -/
def rationalRealArithmeticRestriction (a : 𝓞 ℚ) :
    Gal(ℂ/ℝ) →ₜ* rationalArithmeticGaloisGroup a :=
  rationalArithmeticLocalRestrictionContinuous (F := ℝ) (K := ℂ) a

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) (rationalArithmeticGaloisGroup a))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))

/-- The original arithmetic H2 restriction at the actual real place is zero
for every class at an auxiliary coefficient prime greater than two. -/
theorem rationalRealArithmeticH2Restriction_eq_zero (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (rationalRealArithmeticRestriction a).toMonoidHom
      (rationalRealArithmeticRestriction a).continuous x = 0 := by
  exact realPlaceFiniteCoefficientH2_eq_zero q
    (restrictedCoefficientRep A (rationalRealArithmeticRestriction a).toMonoidHom)
    (restrictedCoefficientAction_continuous A (rationalRealArithmeticRestriction a).toMonoidHom
      (rationalRealArithmeticRestriction a).continuous hA) hq _

end
end Dubon2026
