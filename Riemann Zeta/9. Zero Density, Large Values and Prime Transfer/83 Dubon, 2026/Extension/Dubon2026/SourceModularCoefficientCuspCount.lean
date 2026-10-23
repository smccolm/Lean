import Dubon2026.SourceModularCoefficientCuspFamily
import Dubon2026.SourceModularCoefficientJDegreeSums

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> cusp count.
The actual labeled coefficient-field poles exhaust the full pole set:
their positive widths sum to the already proved total j-pole order.
This gives cuspCount(N) in every characteristic not dividing N, without
assuming a cusp classification or extension-of-places theorem. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [IsAlgClosed L]
variable (hNL : (N : L) ≠ 0)

include hNL

theorem coeff_cusp_family_exhaustive (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (S : Finset (Place L (modularFunctionFieldCoeff N L)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jCoeff N L) < 0) :
    S = @Finset.image _ _ (Classical.decEq _) (CoefficientCuspLabels.place N L hNL ζ hζ) Finset.univ := by
  classical
  let T := Finset.univ.image (CoefficientCuspLabels.place N L hNL ζ hζ)
  have hTS : T ⊆ S := by
    intro v hv
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hv
    exact (hS _).mpr (CoefficientCuspLabels.place_is_pole N L hNL ζ hζ s)
  have hT : (∑ v ∈ T, -v.ord (jCoeff N L)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) := by
    rw [Finset.sum_image (fun _ _ _ _ he => CoefficientCuspLabels.place_injective N L hNL ζ hζ he)]
    calc
      _ = ∑ s : {s // s ∈ CuspLabels.labels N},
          ((N / s.1.1 / Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [(CoefficientCuspLabels.embedding_spec N L hNL ζ hζ s).2.2.2.1, neg_neg]
      _ = ((∑ s ∈ CuspLabels.labels N, N / s.1 / Nat.gcd s.1 (N / s.1)) : ℕ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_coe_sort (CuspLabels.labels N)
          (fun s => ((N / s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ))
      _ = _ := by rw [CuspLabels.sum_label_widths]
  have hsum := sum_coeff_j_pole_orders_finset N L hNL S hS
  apply Finset.Subset.antisymm ?_ hTS
  intro v hv
  by_contra hvt
  have hlt := Finset.sum_lt_sum_of_subset hTS hv hvt
    (show 0 < -v.ord (jCoeff N L) from neg_pos.mpr ((hS v).mp hv))
    (fun w hw _ => le_of_lt (neg_pos.mpr ((hS w).mp hw)))
  rw [hT, hsum] at hlt
  exact lt_irrefl _ hlt

theorem card_coeff_j_poles_eq_cuspCount
    (S : Finset (Place L (modularFunctionFieldCoeff N L)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jCoeff N L) < 0) :
    S.card = SourceLevelProjective.cuspCount N := by
  classical
  haveI : NeZero (N : L) := ⟨hNL⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  have hu := hz.isUnit (NeZero.ne N)
  have hζ : IsPrimitiveRoot (hu.unit : L) N := by rw [hu.unit_spec]; exact hz
  rw [coeff_cusp_family_exhaustive N L hNL hu.unit hζ S hS,
    Finset.card_image_of_injective _ (CoefficientCuspLabels.place_injective N L hNL hu.unit hζ),
    Finset.card_univ, Fintype.card_coe, CuspLabels.card_labels]

theorem natCard_coeff_j_poles_eq_cuspCount :
    Nat.card {v : Place L (modularFunctionFieldCoeff N L) // v.ord (jCoeff N L) < 0} =
      SourceLevelProjective.cuspCount N := by
  classical
  have hs : {v : Place L (modularFunctionFieldCoeff N L) | v.ord (jCoeff N L) < 0}.Finite :=
    (finite_coeff_divisor_support N L (jCoeff N L)).subset fun _ hv => ne_of_lt hv
  calc
    _ = Nat.card ↥hs.toFinset := Nat.card_congr
      (Equiv.subtypeEquivRight fun v => (hs.mem_toFinset (a := v)).symm)
    _ = hs.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := card_coeff_j_poles_eq_cuspCount N L hNL hs.toFinset fun v => hs.mem_toFinset

end
end Dubon2026.SourceFunctionField
