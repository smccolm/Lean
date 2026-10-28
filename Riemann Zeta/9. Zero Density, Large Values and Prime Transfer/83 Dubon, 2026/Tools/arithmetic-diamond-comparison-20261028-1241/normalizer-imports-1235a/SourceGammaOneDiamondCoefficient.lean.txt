import Dubon2026.SourceGammaOneDiagonalHom
import Dubon2026.SourceGammaOneDiamondConjugation
import Dubon2026.SourceGammaOneBinaryRestriction

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
arithmetic realization -> original diamond coefficient convention.
Extend the existing diagonal cover map to its actual Gamma0 normalizer.
Literal conjugation then fixes the inverse coefficient action required
by the original binary representation. No new coefficient model is used.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable (Q N w : ℕ) [NeZero N]

/-- The original level-raising map on the actual cover normalizer. -/
def sourceGammaOneDiamondLift : Gamma0 (Q * N ^ 2) →* Gamma0 Q :=
  (sourceRaisedLevelConjugation Q N).comp
    (Subgroup.inclusion (Gamma0_le_of_dvd
      (Nat.mul_dvd_mul_left Q (dvd_pow_self N (by decide : 2 ≠ 0)))))

theorem sourceGammaOneDiamondLift_gammaOne (γ : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneDiamondLift Q N
      ⟨γ.val, Gamma1_in_Gamma0 _ γ.property⟩ = sourceGammaOneDiagonalHom Q N γ := rfl

theorem sourceGammaOneDiamondLift_conjugation (g : Gamma0 (Q * N ^ 2))
    (γ : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneDiagonalHom Q N (sourceGammaOneDiamondConjugation (Q * N ^ 2) g γ) =
      sourceGammaOneDiamondLift Q N g * sourceGammaOneDiagonalHom Q N γ *
        (sourceGammaOneDiamondLift Q N g)⁻¹ := by
  let γ₀ : Gamma0 (Q * N ^ 2) := ⟨γ.val, Gamma1_in_Gamma0 _ γ.property⟩
  change sourceGammaOneDiamondLift Q N (g * γ₀ * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, sourceGammaOneDiamondLift_gammaOne]

/-- The inverse normalizer action on the original homogeneous coefficients. -/
def sourceGammaOneBinaryDiamondCoefficient (g : Gamma0 (Q * N ^ 2)) :
    Module.End (ZMod N) (sourceBinaryCoefficientRep (ZMod N) Q w) :=
  (sourceBinaryCoefficientRep (ZMod N) Q w).ρ (sourceGammaOneDiamondLift Q N g)⁻¹

theorem sourceGammaOneBinaryDiamondCoefficient_conjugation
    (g : Gamma0 (Q * N ^ 2)) (γ : Gamma1 (Q * N ^ 2)) :
    (sourceGammaOneBinaryDiamondCoefficient Q N w g).comp
      ((sourceBinaryCoefficientRep (ZMod N) Q w).ρ
        (sourceGammaOneDiagonalHom Q N
          (sourceGammaOneDiamondConjugation (Q * N ^ 2) g γ))) =
      ((sourceBinaryCoefficientRep (ZMod N) Q w).ρ
        (sourceGammaOneDiagonalHom Q N γ)).comp
        (sourceGammaOneBinaryDiamondCoefficient Q N w g) := by
  change (sourceBinaryCoefficientRep (ZMod N) Q w).ρ _ *
      (sourceBinaryCoefficientRep (ZMod N) Q w).ρ _ =
    (sourceBinaryCoefficientRep (ZMod N) Q w).ρ _ *
      (sourceBinaryCoefficientRep (ZMod N) Q w).ρ _
  rw [← map_mul, ← map_mul, sourceGammaOneDiamondLift_conjugation]
  congr 1
  group

end
end Dubon2026
