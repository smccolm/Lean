import Dubon2026.SourceGammaOnePrimitiveUnitDiamond
import Dubon2026.SourceGammaOnePrimitiveJointFrobenius

/-! DUB-17/18 -> original all-weight association -> compatible character/trace
specialization. The genuine unit-labelled diamond lies in the same finite
joint Hecke image carrying the original character. This is the diamond part
of its global determinant term; no trace spreading or realization is claimed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary ToricCoordinates
variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- The coefficient algebra on the literal pair of original operator rings. -/
instance instAlgebraBinaryPrimitiveJointOperatorRing :
    Algebra (ZMod N) (binaryPrimitiveJointOperatorRing Q p n w) :=
  inferInstanceAs (Algebra (ZMod N)
    (Module.End (ZMod N) J × Module.End (ZMod N) (P M → V)))

/-- The genuine unit-labelled diamond on the exact joint operator space. -/
def binaryPrimitiveJointUnitDiamond :
    (ZMod M)ˣ →* binaryPrimitiveJointOperatorRing Q p n w :=
  (1 : (ZMod M)ˣ →* Module.End (ZMod N) J).prod (binaryPrimitiveColumnUnitDiamond Q N w)

/-- Every native Gamma0 diamond is exactly its unit-labelled joint action. -/
theorem binaryPrimitiveJointUnitDiamond_gamma0
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J) (g : Gamma0 M) :
    binaryPrimitiveJointUnitDiamond Q p n w (gamma0Unit M g) =
      binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inr g)) := by
  have hp : binaryPrimitiveJointUnitDiamond Q p n w (gamma0Unit M g) =
      (1, binaryPrimitiveColumnDiamond Q N w g) :=
    Prod.ext rfl (binaryPrimitiveColumnUnitDiamond_gamma0 Q N w g)
  exact hp.trans (binaryPrimitiveJointHeckeDiamondWord_ι Q p n w Hq (Sum.inr g)).symm

/-- Every unit diamond lies in the literal original word image, by the
proved original Gamma0 label lift. -/
theorem binaryPrimitiveJointUnitDiamond_mem_range
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J) (u : (ZMod M)ˣ) :
    binaryPrimitiveJointUnitDiamond Q p n w u ∈
      (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range := by
  obtain ⟨g, hg⟩ := sourceGammaOneDiamondLabel_lift M u
  have hu : gamma0Unit M g = u := Units.ext hg
  exact ⟨FreeAlgebra.ι ℤ (Sum.inr g),
    (binaryPrimitiveJointUnitDiamond_gamma0 Q p n w Hq g).symm.trans
      (congrArg (binaryPrimitiveJointUnitDiamond Q p n w) hu)⟩

end
end Dubon2026.SourceFunctionField.GammaOne
