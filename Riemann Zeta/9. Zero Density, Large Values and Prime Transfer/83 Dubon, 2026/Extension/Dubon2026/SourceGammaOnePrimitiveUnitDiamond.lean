import Dubon2026.SourceGammaOnePrimitiveUnitActions
import Dubon2026.SourceGammaOneDiamondLabels

/-! DUB-17/18 -> original all-weight association -> compatible character/trace
specialization. The exact boundary diamond extends to the finite residue-unit
group. This supplies the multiplicative diamond term required before spreading
the proved local Frobenius polynomial by Chebotarev. Neither that spreading nor
a characteristic-zero realization is assumed or asserted here. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary ToricCoordinates
variable (Q N w : ℕ)
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "F" => P M → V

/-- The original homogeneous diagonal action of a residue unit and its inverse. -/
def binaryPrimitiveDiamondCoefficientUnits : (ZMod M)ˣ →* Module.End (ZMod N) V :=
  (homogeneousGLRepresentation w).comp
    (sourceDiagonalUnitPair (binaryPrimitiveUnitReduction Q N) (binaryPrimitiveUnitReduction Q N)⁻¹)

/-- The coefficient representation retains the literal original diagonal entries. -/
theorem binaryPrimitiveDiamondCoefficientUnits_eq (u : (ZMod M)ˣ) :
    binaryPrimitiveDiamondCoefficientUnits Q N w u =
      homogeneousMatrixAction w (Matrix.diagonal
        ![(binaryPrimitiveUnitReduction Q N u : ZMod N),
          ((binaryPrimitiveUnitReduction Q N u)⁻¹ : (ZMod N)ˣ)]) := by
  change homogeneousMatrixAction w
    (sourceDiagonalUnitPair (binaryPrimitiveUnitReduction Q N) (binaryPrimitiveUnitReduction Q N)⁻¹ u).val = _
  rw [sourceDiagonalUnitPair_val]
  rfl

/-- The actual primitive-column diamond as a representation of the full unit group. -/
def binaryPrimitiveColumnUnitDiamond : (ZMod M)ˣ →* Module.End (ZMod N) F where
  toFun u := LinearMap.pi fun c => (binaryPrimitiveDiamondCoefficientUnits Q N w u) ∘ₗ
    (LinearMap.proj (scale u⁻¹ u c) : F →ₗ[ZMod N] V)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext c
    change binaryPrimitiveDiamondCoefficientUnits Q N w 1 (f (scale 1⁻¹ 1 c)) = f c
    rw [map_one, inv_one, scale_one]
    rfl
  map_mul' u v := by
    apply LinearMap.ext
    intro f
    funext c
    change binaryPrimitiveDiamondCoefficientUnits Q N w (u * v) (f (scale (u * v)⁻¹ (u * v) c)) =
      binaryPrimitiveDiamondCoefficientUnits Q N w u
        (binaryPrimitiveDiamondCoefficientUnits Q N w v (f (scale v⁻¹ v (scale u⁻¹ u c))))
    rw [map_mul, scale_scale, mul_inv_rev, mul_comm v u]
    rfl

/-- The full unit action equals the actual native normalizer diamond;
reduction preserves both original diagonal entries. -/
theorem binaryPrimitiveColumnUnitDiamond_gamma0 [NeZero N] (g : Gamma0 M) :
    binaryPrimitiveColumnUnitDiamond Q N w (gamma0Unit M g) =
      binaryPrimitiveColumnDiamond Q N w g := by
  have hu : (binaryPrimitiveUnitReduction Q N (gamma0Unit M g) : ZMod N) =
      (g.val 1 1 : ZMod N) := by
    change ZMod.castHom _ (ZMod N) (gamma0Unit M g : ZMod M) = _
    rw [coe_gamma0Unit, map_intCast]
  have hi : (((binaryPrimitiveUnitReduction Q N (gamma0Unit M g))⁻¹ : (ZMod N)ˣ) : ZMod N) =
      (g.val 0 0 : ZMod N) := by
    rw [← map_inv]
    change ZMod.castHom _ (ZMod N) (((gamma0Unit M g)⁻¹ : (ZMod M)ˣ) : ZMod M) = _
    rw [coe_inv_gamma0Unit, map_intCast]
  have hc : binaryPrimitiveDiamondCoefficientUnits Q N w (gamma0Unit M g) =
      sourceGammaOneBinaryDiamondCoefficient Q N w g := by
    rw [binaryPrimitiveDiamondCoefficientUnits_eq, sourceGammaOneBinaryDiamondCoefficient_eq_diagonal,
      hu, hi]
  apply LinearMap.ext
  intro f
  funext c
  exact LinearMap.congr_fun hc (f (scale (gamma0Unit M g)⁻¹ (gamma0Unit M g) c))

end
end Dubon2026.SourceFunctionField.GammaOne
