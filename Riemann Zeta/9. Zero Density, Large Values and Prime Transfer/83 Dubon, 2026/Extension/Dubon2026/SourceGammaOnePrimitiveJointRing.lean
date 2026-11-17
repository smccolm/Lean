import Dubon2026.SourceGammaOnePrimitiveHeckeDiamondWords
import Dubon2026.SourceGammaOnePrimitiveBoundaryDescent
import Dubon2026.SourceGammaOneDiamondQuotientGalois
import Dubon2026.SourceGammaOneDiamondQuotientWords
import Mathlib.Algebra.Algebra.Prod

/-! DUB-17/18 -> original all-weight association -> arithmetic joint
character. The actual geometric diamond quotient and explicit primitive
boundary carry the prime/diamond word pair. This literal finite product
retains the boundary arithmetic action and the original diamond generator. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup groupCohomology SourceCuspBoundary
private def productWord {ι A B : Type} [Ring A] [Ring B]
    [Algebra ℤ A] [Algebra ℤ B] (F : ι → A) (G : ι → B) :
    FreeAlgebra ℤ ι →+* A × B :=
  (FreeAlgebra.lift ℤ F).toRingHom.prod (FreeAlgebra.lift ℤ G).toRingHom

private theorem finite_end {R X : Type} [Semiring R] [AddCommMonoid X] [Module R X]
    [Finite X] : Finite (Module.End R X) :=
  Finite.of_injective (fun f : Module.End R X => (f : X → X)) DFunLike.coe_injective

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "C" => Rep.trivial (ZMod N) (Gamma1 M) V
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance

local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "B" => P M → V
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- The literal product of the two actual endomorphism rings. -/
def binaryPrimitiveJointOperatorRing : Type :=
  Module.End (ZMod N) J × Module.End (ZMod N) B

/-- The ordinary product ring on the actual joint operators. -/
instance instRingBinaryPrimitiveJointOperatorRing : Ring (binaryPrimitiveJointOperatorRing Q p n w) :=
  inferInstanceAs (Ring (Module.End (ZMod N) J × Module.End (ZMod N) B))

/-- The original pair of Hecke-word actions in its fixed product ring. -/
def binaryPrimitiveJointHeckeDiamondWord (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J) :
    FreeAlgebra ℤ S →+* binaryPrimitiveJointOperatorRing Q p n w :=
  productWord (Sum.elim Hq (fun _ : Gamma0 M => 1))
    (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w)

/-- Zero in the joint image is exactly zero in both actual operator spaces. -/
theorem binaryPrimitiveJointHeckeDiamondWord_eq_zero_iff (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (a : FreeAlgebra ℤ S) :
    binaryPrimitiveJointHeckeDiamondWord Q p n w Hq a = 0 ↔
      FreeAlgebra.lift ℤ (Sum.elim Hq (fun _ : Gamma0 M => 1)) a = 0 ∧
        FreeAlgebra.lift ℤ (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w) a = 0 := by
  change (_, _) = (0, 0) ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hq, hb⟩
    exact Prod.ext hq hb

/-- The actual geometric/primitive-boundary operator product is finite,
reusing the proved native geometric and homogeneous boundary finiteness. -/
theorem binaryPrimitiveJointOperatorRing_finite :
    Finite (binaryPrimitiveJointOperatorRing Q p n w) := by
  unfold binaryPrimitiveJointOperatorRing
  letI : Finite J := binaryDiamondQuotient_finite Q p n w
  letI : Finite (Module.End (ZMod N) J) := finite_end
  letI : Finite (Module.End (ZMod N) B) := binaryPrimitiveColumnOperators_finite Q N w
  infer_instance

end
end Dubon2026.SourceFunctionField.GammaOne
