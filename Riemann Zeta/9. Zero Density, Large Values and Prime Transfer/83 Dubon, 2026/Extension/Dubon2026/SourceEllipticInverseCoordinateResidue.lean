import Dubon2026.SourceEllipticInverseCoordinateNaturality
import Mathlib.RingTheory.Valuation.ValuationSubring

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
section IntegralCoord

variable {M : Type*} [Field M] {A : ValuationSubring M}

lemma coe_map_u_inv (C₀ : VariableChange A) :
    (((C₀.map A.subtype).u⁻¹ : Mˣ) : M) = ((C₀.u⁻¹ : Aˣ) : A) := by
  simp only [VariableChange.map, Units.coe_map_inv]; rfl

lemma vcXInv_map_subtype (C₀ : VariableChange A) (x : M) :
    vcXInv (C₀.map A.subtype) x = ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (x - (C₀.r : M)) := by
  rw [vcXInv, coe_map_u_inv]; rfl

lemma vcYInv_map_subtype (C₀ : VariableChange A) (x y : M) :
    vcYInv (C₀.map A.subtype) x y =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (y - (C₀.t : M) - (C₀.s : M) * (x - (C₀.r : M))) := by
  rw [vcYInv, coe_map_u_inv]; rfl

lemma vcXInv_mem (C₀ : VariableChange A) {x : M} (hx : x ∈ A) :
    vcXInv (C₀.map A.subtype) x ∈ A := by
  rw [vcXInv_map_subtype]
  exact mul_mem (pow_mem (SetLike.coe_mem _) 2) (sub_mem hx (SetLike.coe_mem C₀.r))

lemma vcYInv_mem (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    vcYInv (C₀.map A.subtype) x y ∈ A := by
  rw [vcYInv_map_subtype]
  exact mul_mem (pow_mem (SetLike.coe_mem _) 3)
    (sub_mem (sub_mem hy (SetLike.coe_mem C₀.t))
      (mul_mem (SetLike.coe_mem C₀.s) (sub_mem hx (SetLike.coe_mem C₀.r))))

lemma residue_vcXInv (C₀ : VariableChange A) {x : M} (hx : x ∈ A)
    (h : vcXInv (C₀.map A.subtype) x ∈ A) :
    residue A ⟨vcXInv (C₀.map A.subtype) x, h⟩ =
      vcXInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) := by
  have hA : (⟨vcXInv (C₀.map A.subtype) x, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (⟨x, hx⟩ - C₀.r) := by
    apply Subtype.ext
    show vcXInv (C₀.map A.subtype) x = _
    rw [vcXInv_map_subtype]
    push_cast
    ring
  rw [hA, vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

lemma residue_vcYInv (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A)
    (h : vcYInv (C₀.map A.subtype) x y ∈ A) :
    residue A ⟨vcYInv (C₀.map A.subtype) x y, h⟩ =
      vcYInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
  have hA : (⟨vcYInv (C₀.map A.subtype) x y, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (⟨y, hy⟩ - C₀.t - C₀.s * (⟨x, hx⟩ - C₀.r)) := by
    apply Subtype.ext
    show vcYInv (C₀.map A.subtype) x y = _
    rw [vcYInv_map_subtype]
    push_cast
    ring
  rw [hA, vcYInv, VariableChange.map, Units.coe_map_inv]
  simp only [map_mul, map_pow, map_sub]
  rfl

end IntegralCoord


end
end Dubon2026.SourceEllipticReduction
