import Dubon2026.SourceGammaOneDiamondCoefficient
import Dubon2026.SourceGammaOneDiamondH1

/-! DUB-17/18 -> original all-weight association -> original finite
Gamma1 arithmetic realization -> diamond coefficient comparison.
The inverse lifted normalizer action fixes the literal restriction of
every original binary cocycle, because the actual diagonal cover acts
trivially on its coefficients. This verifies the convention against
the original cohomology, rather than merely choosing an endomorphism.
Surjective parabolic transfer remains a separate obligation.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology CategoryTheory
variable (Q N w : ℕ) [NeZero N]

theorem sourceGammaOneBinaryRestrictionCocycles_diamond
    (g : Gamma0 (Q * N ^ 2))
    (c : cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w))
    (γ : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneBinaryDiamondCoefficient Q N w g
      (sourceGammaOneBinaryRestrictionCocycles Q N w c
        (sourceGammaOneDiamondConjugation (Q * N ^ 2) g γ)) =
      sourceGammaOneBinaryRestrictionCocycles Q N w c γ := by
  let d := sourceGammaOneDiamondLift Q N g
  let x := sourceGammaOneDiagonalHom Q N γ
  let A := sourceBinaryCoefficientRep (ZMod N) Q w
  have hx : A.ρ x = 1 := sourceGammaOneDiagonalHom_binary_trivial Q N w γ
  have hm := (mem_cocycles₁_iff c).mp c.property
  have hc : c (d * x * d⁻¹) = A.ρ d (c x) := by
    rw [hm, hm, map_mul, Module.End.mul_apply, hx, Module.End.one_apply,
      cocycles₁_map_inv]
    abel
  change A.ρ d⁻¹ (c (sourceGammaOneDiagonalHom Q N
    (sourceGammaOneDiamondConjugation (Q * N ^ 2) g γ))) = c x
  rw [sourceGammaOneDiamondLift_conjugation]
  change A.ρ d⁻¹ (c (d * x * d⁻¹)) = c x
  rw [hc, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem sourceGammaOneBinaryRestrictionH1_diamond
    (g : Gamma0 (Q * N ^ 2))
    (x : H1 (sourceBinaryCoefficientRep (ZMod N) Q w)) :
    sourceGammaOneDiamondH1 (ZMod N) (sourceBinaryCoefficientRep (ZMod N) Q w)
      (Q * N ^ 2) g (sourceGammaOneBinaryDiamondCoefficient Q N w g)
      (sourceGammaOneBinaryRestrictionH1 Q N w x) =
      sourceGammaOneBinaryRestrictionH1 Q N w x := by
  induction x using H1_induction_on with
  | h c =>
    apply (ConcreteCategory.bijective_of_isIso
      (H1IsoOfIsTrivial (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
        (sourceBinaryCoefficientRep (ZMod N) Q w))).hom).injective
    apply AddMonoidHom.ext
    intro γ
    have hγ : γ = Additive.ofMul γ.toMul := rfl
    rw [hγ, sourceGammaOneDiamondH1_hom_apply,
      sourceGammaOneBinaryRestrictionH1_cocycle,
      H1IsoOfIsTrivial_H1π_apply_apply, H1IsoOfIsTrivial_H1π_apply_apply]
    exact sourceGammaOneBinaryRestrictionCocycles_diamond Q N w g c γ.toMul

end
end Dubon2026
