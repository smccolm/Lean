import Dubon2026.SourceConjugateSlotValues

/-! DUB-17/18 -> numerical modular genus -> all-level j-map degree.
The explicit primitive triangular Laurent product is monic of degree
dedekindPsi and has distinct roots. Its identification with the mapped
minimal polynomial remains the next obligation; these conclusions alone
do not claim the modular field degree.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open Polynomial
variable {K : Type*} [Field K]

/-- Product over the actual primitive triangular Laurent conjugate candidates. -/
def slotProduct (N : ℕ) (ζ : Kˣ) : Polynomial (LaurentSeries K) :=
  ∏ s ∈ indices N, (X - C (slotValue ζ s.1 s.2))

theorem slotProduct_monic (N : ℕ) (ζ : Kˣ) : (slotProduct N ζ).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

theorem slotProduct_natDegree (N : ℕ) (hN : N ≠ 0) (ζ : Kˣ) :
    (slotProduct N ζ).natDegree = SourceLevelProjective.dedekindPsi N := by
  rw [slotProduct, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_indices N hN]

theorem slotProduct_roots (N : ℕ) (ζ : Kˣ) :
    (slotProduct N ζ).roots = (indices N).val.map (fun s => slotValue ζ s.1 s.2) := by
  rw [slotProduct, Finset.prod_eq_multiset_prod]
  have he : ((indices N).val.map (fun s => X - C (slotValue ζ s.1 s.2))) =
      ((indices N).val.map (fun s => slotValue ζ s.1 s.2)).map (fun x => X - C x) := by
    rw [Multiset.map_map]
    rfl
  rw [he, Polynomial.roots_multiset_prod_X_sub_C]

theorem slotProduct_roots_nodup {N : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N) :
    (slotProduct N ζ).roots.Nodup := by
  rw [slotProduct_roots]
  exact (indices N).nodup.map_on (slotValue_injOn_indices hζ)

end
end Dubon2026.SourceFunctionField.ConjugateSlots
