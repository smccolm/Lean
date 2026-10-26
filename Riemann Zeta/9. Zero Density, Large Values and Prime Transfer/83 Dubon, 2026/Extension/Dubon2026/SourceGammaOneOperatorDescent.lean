import Dubon2026.SourceGammaOneHeckeWords
import Dubon2026.SourceBinaryH1ModulusKernel
import Dubon2026.SourceFiniteOperatorCharacterDescent

/-! DUB-17/18 -> original all-weight adic association -> actual finite Gamma1
Hecke characters. The original surjective transfer and full word naturality
force every Gamma1 operator relation to hold in the original finite tensor
operator image. Native ring-map descent retains the exact original words. -/
namespace Dubon2026
noncomputable section

/-- Every relation among the actual Gamma1 Hecke operators is a relation
on the original coefficient-reduced integral H1 operator module. -/
theorem sourceGammaOneHeckeWord_modulus_zero
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N))
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N)))
    (ha : FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w) a = 0) :
    sourceBinaryH1ModulusOperatorMap Q w N (sourceGammaOneOriginalHeckeWord Q N w a) = 0 := by
  apply sourceBinaryH1ModulusOperatorMap_zero_of_coefficients Q w N (NeZero.ne N)
  intro x
  obtain ⟨y, hy⟩ := sourceGammaOneConstantH1Transfer_surjective Q N w h6
    (sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w x)
  rw [sourceGammaOneOriginalHeckeWord_change, ← hy,
    ← sourceGammaOneHeckeWord_transfer, ha, LinearMap.zero_apply]
  exact map_zero (sourceGammaOneConstantH1Transfer Q N w)

/-- The actual Gamma1 word-action kernel is contained in the original
finite tensor-operator kernel on the same good-prime words. -/
theorem sourceGammaOneHeckeWord_modulus_kernel
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    RingHom.ker (FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w)).rangeRestrict.toRingHom ≤
      RingHom.ker (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
        (sourceGammaOneOriginalHeckeWord Q N w)).toRingHom := by
  intro a ha
  apply RingHom.mem_ker.mpr
  apply Subtype.ext
  exact sourceGammaOneHeckeWord_modulus_zero Q N w h6 a
    (congrArg Subtype.val (RingHom.mem_ker.mp ha))

/-- The canonical map from genuine Gamma1 good-prime operators into the
original finite tensor-operator algebra. Only primes away from level and
modulus are used; surjectivity onto the entire original algebra is not asserted. -/
def sourceGammaOneToModulus
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    sourceGammaOneHeckeAlgebra Q N w →+* sourceBinaryH1ModulusOperatorAlgebra Q w N := by
  have hker := sourceGammaOneHeckeWord_modulus_kernel Q N w h6
  exact sourceFiniteOperatorCharacterDescend
    (A := FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N)))
    (B := sourceGammaOneHeckeAlgebra Q N w)
    (C := sourceBinaryH1ModulusOperatorAlgebra Q w N)
    (FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w)).rangeRestrict.toRingHom
    (FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w)).rangeRestrict_surjective
    (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
      (sourceGammaOneOriginalHeckeWord Q N w)).toRingHom hker

/-- Pullback of the descended operator map is the same entire original
integral word action at the prescribed coefficient modulus. -/
theorem sourceGammaOneToModulus_comp
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    (sourceGammaOneToModulus Q N w h6).comp
      (FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w)).rangeRestrict.toRingHom =
      (((sourceBinaryH1ModulusOperatorMap Q w N).rangeRestrict).comp
        (sourceGammaOneOriginalHeckeWord Q N w)).toRingHom :=
  sourceFiniteOperatorCharacterDescend_comp _ _ _ _

end
end Dubon2026
