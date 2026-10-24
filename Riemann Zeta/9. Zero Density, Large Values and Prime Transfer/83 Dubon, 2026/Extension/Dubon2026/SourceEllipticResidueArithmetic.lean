import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Valuation and residue arithmetic for integral-point addition. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, ReductionMap, TorsionIntegral
and ReduceHom. Only the arithmetic used by reduction on prime-to-residue
torsion is retained; formal groups and nonintegral-point addition are deferred.
This serves DUB-17/18 through integral odd quotient reduction. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: mul_mem_nonunits. -/
theorem mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: add_notMem. -/
theorem add_notMem {x a : L} (hx : x ∉ A) (ha : a ∈ A) : x + a ∉ A := fun h =>
  hx (by simpa using A.toSubring.sub_mem h ha)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: mul_notMem. -/
theorem mul_notMem {x y : L} (hx : x ∉ A) (hy : y ∉ A) : x * y ∉ A := fun h => by
  rcases A.mem_or_inv_mem x with hx' | hx'
  · exact hx hx'
  · have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
    exact hy (by simpa [inv_mul_cancel_left₀ hx0] using A.toSubring.mul_mem hx' h)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: div_notMem. -/
theorem div_notMem {a b : L} (ha' : a ∉ A.nonunits) (hb : b ∈ A.nonunits) (hb0 : b ≠ 0) :
    a / b ∉ A := fun h => by
  refine ha' ?_
  rw [show a = a / b * b from (div_mul_cancel₀ a hb0).symm]
  exact mul_mem_nonunits A h hb

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: coe_mem_nonunits_iff_residue_eq_zero. -/
theorem coe_mem_nonunits_iff_residue_eq_zero (e : A) :
    (e : L) ∈ A.nonunits ↔ residue A e = 0 := by
  rw [A.coe_mem_nonunits_iff, residue_eq_zero_iff]

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: ne_zero_of_notMem_nonunits. -/
theorem ne_zero_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a ≠ 0 := fun h =>
  ha (h ▸ A.nonunits.zero_mem)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: inv_mem_of_notMem_nonunits. -/
theorem inv_mem_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or] at ha
  push Not at ha
  exact ha.2

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: div_mem_of_mem_of_notMem_nonunits. -/
theorem div_mem_of_mem_of_notMem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∉ A.nonunits) :
    a / b ∈ A := by
  rw [div_eq_mul_inv]
  exact A.toSubring.mul_mem ha (inv_mem_of_notMem_nonunits A hb)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: residue_ne_zero_of_notMem_nonunits. -/
theorem residue_ne_zero_of_notMem_nonunits {b : L} (hb : b ∈ A) (hb' : b ∉ A.nonunits) :
    residue A ⟨b, hb⟩ ≠ 0 := fun h =>
  hb' ((coe_mem_nonunits_iff_residue_eq_zero A ⟨b, hb⟩).mpr h)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: residue_eq_of_coe_eq. -/
theorem residue_eq_of_coe_eq {a : L} (ha : a ∈ A) {v : A} (hav : a = (v : L)) :
    residue A ⟨a, ha⟩ = residue A v :=
  congrArg (residue A) (Subtype.ext hav)

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: residue_div. -/
theorem residue_div {a b : L} (ha : a ∈ A) (hb : b ∈ A) (hb' : b ∉ A.nonunits)
    (hq : a / b ∈ A) :
    residue A ⟨a / b, hq⟩ = residue A ⟨a, ha⟩ / residue A ⟨b, hb⟩ := by
  have hb0 : b ≠ 0 := ne_zero_of_notMem_nonunits A hb'
  have hbres : residue A ⟨b, hb⟩ ≠ 0 := residue_ne_zero_of_notMem_nonunits A hb hb'
  rw [eq_div_iff hbres, ← map_mul]
  refine congrArg (residue A) (Subtype.ext ?_)
  push_cast
  exact div_mul_cancel₀ a hb0

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: residue_eq_div_of_eq_div. -/
theorem residue_eq_div_of_eq_div {a c d : L} (ha : a ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hd' : d ∉ A.nonunits) (hacd : a = c / d) :
    residue A ⟨a, ha⟩ = residue A ⟨c, hc⟩ / residue A ⟨d, hd⟩ := by
  rw [residue_eq_of_coe_eq A ha
    (v := ⟨c / d, div_mem_of_mem_of_notMem_nonunits A hc hd'⟩) hacd]
  exact residue_div A hc hd hd' _

/-- Valuation or residue arithmetic used in the actual integral-point reduction proof: residue_eq_residue_iff_sub_mem_nonunits. -/
theorem residue_eq_residue_iff_sub_mem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    residue A ⟨a, ha⟩ = residue A ⟨b, hb⟩ ↔ a - b ∈ A.nonunits := by
  constructor
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 := by rw [map_sub, h, sub_self]
    have := (coe_mem_nonunits_iff_residue_eq_zero A _).mpr h0
    simpa using this
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 :=
      (coe_mem_nonunits_iff_residue_eq_zero A _).mp (by simpa using h)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end Dubon2026.SourceEllipticReduction
