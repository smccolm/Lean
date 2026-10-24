import Dubon2026.SourceCurveFixedFieldDerivativeBound

/-! Equal-order fixed-field parameters have equal differential orders.
For DUB-17/18's wild different estimate, this identifies the derivative of
the conjugate polynomial's constant coefficient. A shorter route than the
FLT source's second residue expansion writes z = x*u, with u a unit, and
applies the already proved fixed-field derivative bound to u. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem coordinateDerivation_ne_zero_and_ord_eq_of_order_gap
    (Z : IntermediateField K F) (x : F) (hxZ : x ∈ Z) (hx : 0 < v.ord x)
    (hgap : ∀ z ∈ Z, v.ord x ∣ v.ord z)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (hDx : v.coordinateDerivation x ≠ 0)
    {z : F} (hzZ : z ∈ Z) (hz : v.ord z = v.ord x) :
    v.coordinateDerivation z ≠ 0 ∧
      v.ord (v.coordinateDerivation z) = v.ord (v.coordinateDerivation x) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hz0 : z ≠ 0 := by rintro rfl; simp only [ord_zero] at hz; omega
  let u := z * x⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hz0 (inv_ne_zero hx0)
  have huZ : u ∈ Z := mul_mem hzZ (inv_mem hxZ)
  have huord : v.ord u = 0 := by
    dsimp [u]
    rw [v.ord_mul hz0 (inv_ne_zero hx0), v.ord_inv, hz, add_neg_cancel]
  have hDu := v.ordGe_coordinateDerivation_of_order_gap Z x hxZ hx hgap hres huZ
    (v.mem_of_ord_nonneg huord.ge)
  have he : z = x * u := by dsimp [u]; field_simp
  have hdz : v.coordinateDerivation z =
      u * v.coordinateDerivation x + x * v.coordinateDerivation u := by
    conv_lhs => rw [he]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, add_comm]
  rw [hdz]
  refine ord_add_eq_of_ordGe (mul_ne_zero hu0 hDx) ?_ ?_
  · rw [v.ord_mul hu0 hDx, huord, zero_add]
  · exact (OrdGe.mul (v := v) (m := v.ord x) (Or.inr le_rfl) hDu).mono (by omega)

end
end Dubon2026.SourceCurve.Place
