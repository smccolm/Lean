import Dubon2026.SourceEllipticAbscissaVariableCoefficients

/-! Intrinsic quotient abscissae commute with the original coordinate change.
These formulas, together with the proved exact kernels, suffice for equality
of actual image subgroups; full ordinate comparison is unnecessary for the
composite quotient transport on the DUB-17/18 inertia-census chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable (C : VariableChange F) (W : WeierstrassCurve F) (S : Finset F)

/-- The original odd quotient abscissa transforms by the original affine coordinate. -/
theorem variableChange_abscissaQuotientX (x : F) :
    abscissaQuotientX (C • W) (S.image (vcXInv C)) (vcXInv C x) =
      vcXInv C (abscissaQuotientX W S x) := by
  have hinj : Function.Injective (vcXInv C) :=
    (show Function.LeftInverse (vcX C) (vcXInv C) from fun x => vcX_vcXInv x).injective
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hterm (r : F) :
      abscissaVeluT (C • W) (vcXInv C r) / (vcXInv C x - vcXInv C r) +
        (C • W).Ψ₂Sq.eval (vcXInv C r) / (vcXInv C x - vcXInv C r) ^ 2 =
      ((C.u⁻¹ : Fˣ) : F) ^ 2 *
        (abscissaVeluT W r / (x - r) + W.Ψ₂Sq.eval r / (x - r) ^ 2) := by
    by_cases hx : x = r
    · simp [hx]
    · have hd : x - r ≠ 0 := sub_ne_zero.mpr hx
      rw [variableChange_abscissaVeluT, variableChange_secondDivision_eval]
      have he : vcXInv C x - vcXInv C r = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - r) := by
        simp only [vcXInv]
        ring
      rw [he]
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  simp only [abscissaQuotientX, Finset.sum_image hinj.injOn]
  simp only [hterm, ← Finset.mul_sum]
  simp only [vcXInv]
  ring

/-- The original degree-two quotient abscissa transforms by the same affine coordinate. -/
theorem variableChange_twoAbscissaQuotientX (h2 : (2 : F) ≠ 0) (x : F) :
    twoAbscissaQuotientX (C • W) (S.image (vcXInv C)) (vcXInv C x) =
      vcXInv C (twoAbscissaQuotientX W S x) := by
  have hinj : Function.Injective (vcXInv C) :=
    (show Function.LeftInverse (vcX C) (vcXInv C) from fun x => vcX_vcXInv x).injective
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hterm (r : F) :
      twoAbscissaG (C • W) (vcXInv C r) / (vcXInv C x - vcXInv C r) =
      ((C.u⁻¹ : Fˣ) : F) ^ 2 * (twoAbscissaG W r / (x - r)) := by
    by_cases hx : x = r
    · simp [hx]
    · have hd : x - r ≠ 0 := sub_ne_zero.mpr hx
      rw [variableChange_twoAbscissaG C W h2]
      have he : vcXInv C x - vcXInv C r = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - r) := by
        simp only [vcXInv]
        ring
      rw [he]
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  simp only [twoAbscissaQuotientX, Finset.sum_image hinj.injOn]
  simp only [hterm, ← Finset.mul_sum]
  simp only [vcXInv]
  ring

end
end Dubon2026.SourceEllipticVelu
