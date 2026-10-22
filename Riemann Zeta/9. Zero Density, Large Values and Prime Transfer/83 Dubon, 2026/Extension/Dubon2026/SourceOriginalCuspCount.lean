import Dubon2026.SourceOriginalCuspFamily
import Dubon2026.SourceOriginalJDegreeSums

/-! DUB-17/18 -> numerical modular genus -> exact cusp count. The
constructed labeled poles have positive widths whose sum is the full
j-coordinate degree. Injectivity and positivity therefore exclude any
additional pole. This discharges exhaustiveness using the existing
degree formula, without an additional extension-of-places construction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_cusp_family_exhaustive (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (S : Finset (Place L (modularFunctionFieldOver N L)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jOver N L) < 0) :
    S = @Finset.image _ _ (Classical.decEq _) (CuspLabels.place N L ζ hζ) Finset.univ := by
  classical
  let T := Finset.univ.image (CuspLabels.place N L ζ hζ)
  have hTS : T ⊆ S := by
    intro v hv
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hv
    exact (hS _).mpr (CuspLabels.place_is_pole N L ζ hζ s)
  have hT : (∑ v ∈ T, -v.ord (jOver N L)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) := by
    rw [Finset.sum_image (fun _ _ _ _ he => CuspLabels.place_injective N L ζ hζ he)]
    calc
      _ = ∑ s : {s // s ∈ CuspLabels.labels N},
          ((N / s.1.1 / Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [(CuspLabels.embedding_spec N L ζ hζ s).2.2.2.1, neg_neg]
      _ = ((∑ s ∈ CuspLabels.labels N, N / s.1 / Nat.gcd s.1 (N / s.1)) : ℕ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_coe_sort (CuspLabels.labels N)
          (fun s => ((N / s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ))
      _ = _ := by rw [CuspLabels.sum_label_widths]
  have hsum := sum_original_j_pole_orders_finset N L S hS
  apply Finset.Subset.antisymm ?_ hTS
  intro v hv
  by_contra hvt
  have hlt := Finset.sum_lt_sum_of_subset hTS hv hvt
    (show 0 < -v.ord (jOver N L) from neg_pos.mpr ((hS v).mp hv))
    (fun w hw _ => le_of_lt (neg_pos.mpr ((hS w).mp hw)))
  rw [hT, hsum] at hlt
  exact lt_irrefl _ hlt

theorem card_original_j_poles_eq_cuspCount
    (S : Finset (Place L (modularFunctionFieldOver N L)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jOver N L) < 0) :
    S.card = SourceLevelProjective.cuspCount N := by
  classical
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : NeZero (N : L) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  have hu := hz.isUnit (NeZero.ne N)
  have hζ : IsPrimitiveRoot (hu.unit : L) N := by rw [hu.unit_spec]; exact hz
  rw [original_cusp_family_exhaustive N L hu.unit hζ S hS,
    Finset.card_image_of_injective _ (CuspLabels.place_injective N L hu.unit hζ),
    Finset.card_univ, Fintype.card_coe, CuspLabels.card_labels]

theorem natCard_original_j_poles_eq_cuspCount :
    Nat.card {v : Place L (modularFunctionFieldOver N L) // v.ord (jOver N L) < 0} =
      SourceLevelProjective.cuspCount N := by
  classical
  have hs : {v : Place L (modularFunctionFieldOver N L) | v.ord (jOver N L) < 0}.Finite :=
    (finite_original_divisor_support N L (jOver N L)).subset fun _ hv => ne_of_lt hv
  calc
    _ = Nat.card ↥hs.toFinset := Nat.card_congr
      (Equiv.subtypeEquivRight fun v => (hs.mem_toFinset (a := v)).symm)
    _ = hs.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := card_original_j_poles_eq_cuspCount N L hs.toFinset fun v => hs.mem_toFinset

end
end Dubon2026.SourceFunctionField
