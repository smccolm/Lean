import Dubon2026.SourceEllipticVariableAddEquiv

/-! Exact coordinate compatibility for the existing variable-change map
and the actual residue map. This connects the proved integral Galois
cocycle to prime-to-characteristic torsion specialization, needed for the
exceptional-fiber census in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite inertia-reduction proof.
Only integral coordinate reduction is needed on the required torsion;
no homomorphism on arbitrary nonintegral points is developed. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section
section Coord

variable {K : Type*} [Field K]

lemma vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

lemma vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

variable {K' : Type*} [Field K'] (φ : K →+* K')

lemma map_vcXInv (C : VariableChange K) (x : K) :
    φ (vcXInv C x) = vcXInv (C.map φ) (φ x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

lemma map_vcYInv (C : VariableChange K) (x y : K) :
    φ (vcYInv C x y) = vcYInv (C.map φ) (φ x) (φ y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

end Coord


end
end Dubon2026.SourceEllipticReduction
