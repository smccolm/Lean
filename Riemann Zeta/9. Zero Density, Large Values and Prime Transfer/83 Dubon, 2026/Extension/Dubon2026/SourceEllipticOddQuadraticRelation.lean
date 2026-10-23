import Dubon2026.SourceEllipticOddFixedField
import Dubon2026.SourceEllipticIntegralQuadraticRelation
import Mathlib.FieldTheory.Minpoly.Finite

/-! The actual literal odd Velu y-coordinate satisfies a monic quadratic
relation with polynomial coefficients in the actual literal x-coordinate.
Its integrality and the actual translation fixed-field degree discharge
both inputs. Identification of those coefficients with the explicit quotient
curve remains the next equation obligation for the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped IntermediateField

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd y-coordinate has minimal-polynomial degree at most two over its x-field. -/
theorem minpoly_odd_genericVeluY_degree_le (hQ : addOrderOf Q = 2 * n + 1) :
    (minpoly F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯
      (genericVeluY W (oddOrderSummingSet W Q n))).natDegree ≤ 2 := by
  let A := F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯
  let L := translationFixedField W.toAffine (AddSubgroup.zmultiples Q)
  have hle : A ≤ L :=
    IntermediateField.adjoin_simple_le_iff.mpr (genericVeluX_mem_oddFixedField W hQ)
  let L' := IntermediateField.extendScalars hle
  have hd : Module.finrank A L' = 2 :=
    (IntermediateField.relfinrank_eq_finrank_of_le hle).symm.trans
      (relfinrank_odd_coordinate_fixedField W hQ)
  letI : FiniteDimensional A L' := .of_finrank_pos (by rw [hd]; norm_num)
  let z : L' := ⟨genericVeluY W (oddOrderSummingSet W Q n), genericVeluY_mem_oddFixedField W hQ⟩
  have hb := minpoly.natDegree_le (A := A) z
  rw [hd] at hb
  have he := minpoly.algHom_eq L'.val L'.val.injective z
  exact (congrArg Polynomial.natDegree he).trans_le hb

/-- Actual odd Velu coordinates have a monic quadratic relation over the polynomial x-ring. -/
theorem exists_odd_genericVelu_quadratic_relation (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ p q : F[X],
      genericVeluY W (oddOrderSummingSet W Q n) ^ 2 +
        aeval (genericVeluX W (oddOrderSummingSet W Q n)) p *
          genericVeluY W (oddOrderSummingSet W Q n) +
        aeval (genericVeluX W (oddOrderSummingSet W Q n)) q = 0 :=
  exists_quadratic_relation_of_integral (transcendental_genericVeluX W _)
    (isIntegral_genericVeluY hQ) (minpoly_odd_genericVeluY_degree_le W hQ)

end Dubon2026.SourceEllipticFunctionField
