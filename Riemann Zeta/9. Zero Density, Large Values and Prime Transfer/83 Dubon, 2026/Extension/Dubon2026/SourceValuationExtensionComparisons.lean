import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
identification of extending residue fields. Finite valuation approximation
and the actual extension degree force each residue extension to have degree
one when the number of incomparable valuations reaches the field degree.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2; no valuation coarsening is used. -/
namespace Dubon2026.SourceCurve.ValuationApproximation
noncomputable section
open Polynomial ValuationSubring

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

theorem mul_lt_one_aux {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  calc a * b ≤ 1 * b := mul_le_mul' ha le_rfl
    _ = b := one_mul b
    _ < 1 := hb

section Over

variable {O : ValuationSubring F} {V : ValuationSubring F'}
  (hV : V.comap (algebraMap F F') = O)
include hV

theorem mem_iff (x : F) : algebraMap F F' x ∈ V ↔ x ∈ O := by
  rw [← ValuationSubring.mem_comap (A := V) (f := algebraMap F F'), hV]

theorem algebraMap_mem (x : O) : algebraMap F F' (x : F) ∈ V := (mem_iff hV _).mpr x.2

theorem lt_one_iff (x : F) : V.valuation (algebraMap F F' x) < 1 ↔ O.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero,
    ← map_inv₀, mem_iff hV]

theorem le_one (x : O) : V.valuation (algebraMap F F' (x : F)) ≤ 1 :=
  (V.valuation_le_one_iff _).mpr (algebraMap_mem hV x)

theorem eq_one_iff (x : F) : V.valuation (algebraMap F F' x) = 1 ↔ O.valuation x = 1 := by
  constructor
  · intro h
    have hle : O.valuation x ≤ 1 :=
      (O.valuation_le_one_iff x).mpr ((mem_iff hV x).mp ((V.valuation_le_one_iff _).mp h.le))
    have hnlt : ¬ O.valuation x < 1 := fun hlt => (ne_of_lt ((lt_one_iff hV x).mpr hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)
  · intro h
    have hle : V.valuation (algebraMap F F' x) ≤ 1 :=
      (V.valuation_le_one_iff _).mpr ((mem_iff hV x).mpr ((O.valuation_le_one_iff x).mp h.le))
    have hnlt : ¬ V.valuation (algebraMap F F' x) < 1 := fun hlt =>
      (ne_of_lt ((lt_one_iff hV x).mp hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)

end Over


end
end Dubon2026.SourceCurve.ValuationApproximation
