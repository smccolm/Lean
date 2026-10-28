import Dubon2026.SourceGammaOneHeckeDiamondWords
import Dubon2026.SourceBinaryH1ModulusKernel
import Dubon2026.SourceFiniteOperatorCharacterDescent

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
arithmetic characters -> original diamond-one character. Reuse the native
surjective-transfer operator descent on the actual algebra enlarged by
original normalizer diamonds. Its proved whole-word transfer identifies
every such diamond with one in the original finite operator algebra.
This is full H1 descent; parabolic lifting remains a separate obligation. -/
namespace Dubon2026
noncomputable section

/-- Every relation among the actual Gamma1 Hecke and diamond operators is a relation
on the original coefficient-reduced integral H1 operator module. -/
theorem sourceGammaOneHeckeDiamondWord_modulus_zero
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N))
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N) ⊕ CongruenceSubgroup.Gamma0 (Q * N ^ 2)))
    (ha : FreeAlgebra.lift ℤ (sourceGammaOneHeckeDiamondOperators Q N w) a = 0) :
    sourceBinaryH1ModulusOperatorMap Q w N (sourceGammaOneOriginalHeckeDiamondWord Q N w a) = 0 := by
  apply sourceBinaryH1ModulusOperatorMap_zero_of_coefficients Q w N (NeZero.ne N)
  intro x
  obtain ⟨y, hy⟩ := sourceGammaOneConstantH1Transfer_surjective Q N w h6
    (sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w x)
  rw [sourceGammaOneOriginalHeckeDiamondWord_change, ← hy,
    ← sourceGammaOneHeckeDiamondWord_transfer, ha, LinearMap.zero_apply]
  exact map_zero (sourceGammaOneConstantH1Transfer Q N w)

/-- The actual Gamma1 word-action kernel is contained in the original
finite tensor-operator kernel on the same good-prime and normalizer words. -/
theorem sourceGammaOneHeckeDiamondWord_modulus_kernel
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    RingHom.ker (FreeAlgebra.lift ℤ (sourceGammaOneHeckeDiamondOperators Q N w)).rangeRestrict.toRingHom ≤
      RingHom.ker (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
        (sourceGammaOneOriginalHeckeDiamondWord Q N w)).toRingHom := by
  intro a ha
  apply RingHom.mem_ker.mpr
  apply Subtype.ext
  exact sourceGammaOneHeckeDiamondWord_modulus_zero Q N w h6 a
    (congrArg Subtype.val (RingHom.mem_ker.mp ha))

/-- The canonical map from genuine Gamma1 prime and diamond operators into the
original finite tensor-operator algebra. The prime generators are away from level and
modulus and all original normalizer diamonds are included; surjectivity onto the entire original algebra is not asserted. -/
def sourceGammaOneDiamondToModulus
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    sourceGammaOneHeckeDiamondAlgebra Q N w →+* sourceBinaryH1ModulusOperatorAlgebra Q w N := by
  have hker := sourceGammaOneHeckeDiamondWord_modulus_kernel Q N w h6
  exact sourceFiniteOperatorCharacterDescend
    (A := FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N) ⊕ CongruenceSubgroup.Gamma0 (Q * N ^ 2)))
    (B := sourceGammaOneHeckeDiamondAlgebra Q N w)
    (C := sourceBinaryH1ModulusOperatorAlgebra Q w N)
    (FreeAlgebra.lift ℤ (sourceGammaOneHeckeDiamondOperators Q N w)).rangeRestrict.toRingHom
    (FreeAlgebra.lift ℤ (sourceGammaOneHeckeDiamondOperators Q N w)).rangeRestrict_surjective
    (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
      (sourceGammaOneOriginalHeckeDiamondWord Q N w)).toRingHom hker

/-- Pullback of the descended operator map is the same entire original
integral word action with diamonds acting as one at the prescribed coefficient modulus. -/
theorem sourceGammaOneDiamondToModulus_comp
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    (sourceGammaOneDiamondToModulus Q N w h6).comp
      (FreeAlgebra.lift ℤ (sourceGammaOneHeckeDiamondOperators Q N w)).rangeRestrict.toRingHom =
      (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
        (sourceGammaOneOriginalHeckeDiamondWord Q N w)).toRingHom :=
  sourceFiniteOperatorCharacterDescend_comp _ _ _ _

end
end Dubon2026
