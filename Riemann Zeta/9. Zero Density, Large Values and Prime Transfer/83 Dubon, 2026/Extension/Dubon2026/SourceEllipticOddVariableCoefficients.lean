import Dubon2026.SourceEllipticOddVariableEmbedding

/-! Transport the explicit odd quotient under actual variable changes.
The existing point-group additive equivalence transports the odd kernel;
coefficient and discriminant scaling transport its exact identity. This
discharges model-normalization inputs to the all-characteristic quotient
ellipticity needed by cyclic quotient products, inertia census and good
reduction for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the actual point
equivalence; no duplicate addition-law or point-map foundation is built. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve Dubon2026.SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K]
section PerPoint

variable (C : VariableChange K) (W : WeierstrassCurve K)

theorem variableChange_veluGy (x y : K) :
    (veluGy (C • W)) (vcXInv C x) (vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 3 * (veluGy W) x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGy, vcXInv, vcYInv, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem variableChange_veluT (x y : K) :
    (veluT (C • W)) (vcXInv C x) (vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (veluT W) x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluT, veluGx, veluGy, vcXInv, vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem variableChange_veluU (x y : K) :
    (veluU (C • W)) (vcXInv C x) (vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (veluU W) x y := by
  rw [veluU, variableChange_veluGy, mul_pow, veluU]
  ring

theorem variableChange_veluW (x y : K) :
    (veluW (C • W)) (vcXInv C x) (vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * ((veluW W) x y - C.r * (veluT W) x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  rw [veluW, variableChange_veluU, variableChange_veluT, veluW, vcXInv]
  simp only [Units.val_inv_eq_inv_val]
  field_simp
  ring

end PerPoint


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
