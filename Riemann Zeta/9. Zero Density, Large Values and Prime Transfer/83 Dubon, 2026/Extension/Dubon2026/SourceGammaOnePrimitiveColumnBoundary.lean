import Dubon2026.SourceGammaOnePrimitiveCuspValues
import Dubon2026.SourceGammaOneFiniteBinaryBoundary
import Dubon2026.SourceFiniteCuspBoundary

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive boundary Frobenius. The actual homogeneous H1
boundary is placed on the existing finite primitive-column carrier.
The native primitive-generator kernel theorem proves its kernel is
exactly parabolic H1. This is the precise faithful comparison needed
before the unit-coordinate Hecke formula can supply arithmetic operators. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary groupCohomology
open scoped MatrixGroups
variable (Q N w : ℕ) [NeZero Q] [NeZero N]
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "C" => Rep.trivial (ZMod N) (Gamma1 M) V

/-- The literal original primitive cusp values on the native finite residue columns. -/
def binaryPrimitiveColumnBoundary : H1 C →ₗ[ZMod N] (P M → V) where
  toFun x a := primitiveCuspValue M ((H1IsoOfIsTrivial C).hom x) (lift a)
  map_add' x y := by
    funext a
    dsimp only [primitiveCuspValue]
    rw [map_add]
    rfl
  map_smul' c x := by
    funext a
    dsimp only [primitiveCuspValue]
    rw [map_smul]
    rfl

/-- Evaluation at any actual integral column recovers the existing
primitive-generator boundary, without multiplying by the level. -/
theorem binaryPrimitiveColumnBoundary_toP (x : H1 C) (δ : SL(2, ℤ)) :
    binaryPrimitiveColumnBoundary Q N w x (toP δ) =
      binaryPrimitiveCuspBoundary Q N w x
        ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) := by
  have hc := colRed_lift (toP (N := M) δ)
  have h0 := congrArg Prod.fst hc
  have h1 := congrArg Prod.snd hc
  exact (primitiveCuspValue_congr M ((H1IsoOfIsTrivial C).hom x)
    (lift (toP δ)) δ h0 h1).trans
      (primitiveCuspValue_generator M ((H1IsoOfIsTrivial C).hom x) δ)

/-- Vanishing on the finite columns is exactly the independently defined
parabolic condition, reusing the native primitive-generator theorem. -/
theorem binaryPrimitiveColumnBoundary_eq_zero_iff (h2 : IsUnit (2 : ZMod N))
    (x : H1 C) :
    binaryPrimitiveColumnBoundary Q N w x = 0 ↔ x ∈ binaryParabolicH1 Q N w := by
  have he : binaryPrimitiveColumnBoundary Q N w x = 0 ↔
      binaryPrimitiveCuspBoundary Q N w x = 0 := by
    constructor
    · intro hx
      funext q
      have hv := congrFun hx (toP q.out⁻¹)
      rw [binaryPrimitiveColumnBoundary_toP] at hv
      simpa only [inv_inv, Quotient.out_eq', Pi.zero_apply] using hv
    · intro hx
      funext a
      change primitiveCuspValue M ((H1IsoOfIsTrivial C).hom x) (lift a) = 0
      rw [primitiveCuspValue_generator]
      exact congrFun hx _
  exact he.trans (binaryPrimitiveCuspBoundary_eq_zero_iff Q N w h2 x)

/-- The faithful finite-column boundary has exactly the original parabolic kernel. -/
theorem binaryPrimitiveColumnBoundary_ker (h2 : IsUnit (2 : ZMod N)) :
    (binaryPrimitiveColumnBoundary Q N w).ker = binaryParabolicH1 Q N w := by
  ext x
  exact binaryPrimitiveColumnBoundary_eq_zero_iff Q N w h2 x

end
end Dubon2026.SourceFunctionField.GammaOne
