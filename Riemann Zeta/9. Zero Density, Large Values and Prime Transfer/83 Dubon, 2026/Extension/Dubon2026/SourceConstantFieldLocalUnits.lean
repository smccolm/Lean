import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> Qbar torsion comparison -> exact constant-field place orders.
A unit plus a uniformizer multiple is a unit, using the native strict valuation
inequality. This computes the first residue term in the local extension.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

theorem ne_zero_and_inv_mem_of_add {L : Type*} [Field L] (V : ValuationSubring L) {a m p : L}
    (ha : a ∈ V) (hai : a⁻¹ ∈ V) (ha0 : a ≠ 0) (hm : m ∈ V) (hp : p ∈ V) (hpi : p⁻¹ ∉ V) :
    a + p * m ≠ 0 ∧ (a + p * m)⁻¹ ∈ V := by
  have hva : V.valuation a = 1 := by
    refine le_antisymm ((V.valuation_le_one_iff a).2 ha) ?_
    have h := (V.valuation_le_one_iff _).2 hai
    rw [map_inv₀] at h
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))).1 h
  have hvp : V.valuation p < 1 :=
    lt_of_le_of_ne ((V.valuation_le_one_iff p).2 hp)
      (fun h => hpi (by rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]))
  have hvm : V.valuation m ≤ 1 := (V.valuation_le_one_iff m).2 hm
  have hlt : V.valuation (p * m) < V.valuation a := by
    rw [map_mul, hva]
    calc V.valuation p * V.valuation m ≤ V.valuation p * 1 := by gcongr
      _ = V.valuation p := mul_one _
      _ < 1 := hvp
  have hve : V.valuation (a + p * m) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hva]
  refine ⟨(Valuation.ne_zero_iff _).1 (by rw [hve]; exact one_ne_zero), ?_⟩
  rw [← V.valuation_le_one_iff, map_inv₀, hve, inv_one]

theorem ord_eq_zero_of_mem_of_inv_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P : Place K F) {f : F} (hf : f ∈ P.toValuationSubring)
    (hfi : f⁻¹ ∈ P.toValuationSubring) : P.ord f = 0 := by
  have h := P.ord_nonneg_of_mem hf
  have hi := P.ord_nonneg_of_mem hfi
  rw [P.ord_inv] at hi
  omega

end
end Dubon2026.SourceCurve.ConstantField
