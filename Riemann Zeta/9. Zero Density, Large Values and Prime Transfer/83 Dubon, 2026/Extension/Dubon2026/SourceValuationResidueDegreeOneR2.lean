import Dubon2026.SourceValuationExtensionComparisons
import Dubon2026.SourceValuationResidueApproximationR2

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
identification of extending residue fields. Finite valuation approximation
and the actual extension degree force each residue extension to have degree
one when the number of incomparable valuations reaches the field degree.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2; no valuation coarsening is used. -/
namespace Dubon2026.SourceCurve.ValuationApproximation
noncomputable section
open ValuationSubring

theorem residue_degree_one_of_finrank_le_card
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hR : ∀ k l, O' k ≤ O' l → k = l) (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (x : F') (hx : x ∈ O' i) :
    ∃ y ∈ O, x - algebraMap F F' y ∈ (O' i).nonunits := by
  classical
  by_contra! hno

  have hz : ∀ k : ι, ∃ z : F', ∀ l, z ∈ O' l ∧ z - (if l = k then 1 else 0) ∈ (O' l).nonunits :=
    fun k => exists_forall_mem_and_sub_mem_nonunits' O' hR
      (fun l => if l = k then 1 else 0)
      (fun l => by
        show (if l = k then (1 : F') else 0) ∈ O' l
        split_ifs
        · exact ValuationSubring.one_mem _
        · exact ValuationSubring.zero_mem _)
  choose z hz using hz
  obtain ⟨w, hw⟩ := exists_forall_mem_and_sub_mem_nonunits' O' hR
    (fun l => if l = i then x else 0)
    (fun l => by
      show (if l = i then x else 0) ∈ O' l
      split_ifs with h
      · rw [h]; exact hx
      · exact ValuationSubring.zero_mem _)

  have hxv : (O' i).valuation x ≤ 1 := ((O' i).valuation_le_one_iff x).mpr hx
  have hli : LinearIndependent F (fun o : Option ι => o.elim w z) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra! hne
    obtain ⟨o1, ho1⟩ := hne
    obtain ⟨o0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun o => O.valuation (c o))
      Finset.univ_nonempty
    have hc0 : c o0 ≠ 0 := by
      intro h
      have h1 := hmax o1 (Finset.mem_univ o1)
      rw [h, map_zero] at h1
      exact ho1 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le'))
    have hv0 : O.valuation (c o0) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0

    obtain ⟨d, hdO, hd0, hdsum⟩ : ∃ d : Option ι → F, (∀ o, d o ∈ O) ∧ d o0 = 1 ∧
        algebraMap F F' (d none) * w + ∑ k, algebraMap F F' (d (some k)) * z k = 0 := by
      refine ⟨fun o => (c o0)⁻¹ * c o, fun o => ?_, inv_mul_cancel₀ hc0, ?_⟩
      · rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
        calc (O.valuation (c o0))⁻¹ * O.valuation (c o)
            ≤ (O.valuation (c o0))⁻¹ * O.valuation (c o0) :=
              mul_le_mul' le_rfl (hmax o (Finset.mem_univ o))
          _ = 1 := inv_mul_cancel₀ hv0
      · have h1 : ∑ o, ((c o0)⁻¹ * c o) • (o.elim w z : F') = 0 := by
          calc ∑ o, ((c o0)⁻¹ * c o) • (o.elim w z : F')
              = ∑ o, (c o0)⁻¹ • (c o • (o.elim w z : F')) :=
                Finset.sum_congr rfl fun o _ => (smul_smul _ _ _).symm
            _ = (c o0)⁻¹ • ∑ o, c o • (o.elim w z : F') := Finset.smul_sum.symm
            _ = 0 := by rw [hc, smul_zero]
        rw [Fintype.sum_option] at h1
        simpa only [Option.elim_none, Option.elim_some, Algebra.smul_def] using h1

    have key : ∀ l : ι, (O' l).valuation
        (algebraMap F F' (d none) * (if l = i then x else 0) + algebraMap F F' (d (some l))) < 1 := by
      intro l
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun k => algebraMap F F' (d (some k)) * z k) (Finset.mem_univ l)
      rw [← hsplit] at hdsum
      have hrel : algebraMap F F' (d none) * (if l = i then x else 0) + algebraMap F F' (d (some l)) =
          algebraMap F F' (d none) * ((if l = i then x else 0) - w)
            - algebraMap F F' (d (some l)) * (z l - 1)
            - ∑ k ∈ Finset.univ.erase l, algebraMap F F' (d (some k)) * z k := by
        linear_combination hdsum
      rw [hrel]
      refine Valuation.map_sub_lt _ (Valuation.map_sub_lt _ ?_ ?_) ?_
      · rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO none⟩) ?_
        rw [Valuation.map_sub_swap]
        exact (hw l).2
      · rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO (some l)⟩) ?_
        have h := (hz l l).2
        rwa [if_pos rfl] at h
      · refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
        have hkl : k ≠ l := Finset.ne_of_mem_erase hk
        rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO (some k)⟩) ?_
        have h := (hz k l).2
        rwa [if_neg (fun h' => hkl h'.symm), sub_zero] at h

    rcases o0 with _ | k0
    ·
      have hk := key i
      rw [if_pos rfl, hd0, map_one, one_mul] at hk
      refine hno (-(d (some i))) (neg_mem (hdO (some i))) ?_
      rw [map_neg, sub_neg_eq_add]
      exact hk
    · by_cases hk0 : k0 = i
      ·
        rw [hk0] at hd0
        have hk := key i
        rw [if_pos rfl, hd0, map_one] at hk
        by_cases hdn : O.valuation (d none) < 1
        · have h1 : (O' i).valuation (algebraMap F F' (d none) * x) < 1 := by
            rw [map_mul]
            calc (O' i).valuation (algebraMap F F' (d none)) * (O' i).valuation x
                ≤ (O' i).valuation (algebraMap F F' (d none)) * 1 := mul_le_mul' le_rfl hxv
              _ = (O' i).valuation (algebraMap F F' (d none)) := mul_one _
              _ < 1 := (lt_one_iff (hO' i) _).mpr hdn
          have h2 := Valuation.map_sub_lt _ hk h1
          rw [add_sub_cancel_left, map_one] at h2
          exact lt_irrefl 1 h2
        · have hdn1 : O.valuation (d none) = 1 :=
            le_antisymm ((O.valuation_le_one_iff _).mpr (hdO none)) (not_lt.mp hdn)
          have hdn0 : d none ≠ 0 := by
            intro h
            rw [h, map_zero] at hdn1
            exact zero_ne_one hdn1
          have hne : algebraMap F F' (d none) ≠ 0 := (_root_.map_ne_zero _).mpr hdn0
          have hyO : -(d none)⁻¹ ∈ O :=
            neg_mem ((O.valuation_le_one_iff _).mp (by rw [map_inv₀, hdn1, inv_one]))
          refine hno _ hyO ?_
          have hxe : x - algebraMap F F' (-(d none)⁻¹) =
              algebraMap F F' (d none)⁻¹ * (algebraMap F F' (d none) * x + 1) := by
            rw [map_neg, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, map_inv₀,
              inv_mul_cancel₀ hne, one_mul]
          show (O' i).valuation (x - algebraMap F F' (-(d none)⁻¹)) < 1
          have hv1 : (O' i).valuation (algebraMap F F' (d none)) = 1 :=
            (eq_one_iff (hO' i) _).mpr hdn1
          rw [hxe, map_mul, map_inv₀, map_inv₀, hv1, inv_one, one_mul]
          exact hk
      ·
        have hk := key k0
        rw [if_neg hk0, mul_zero, zero_add, hd0, map_one] at hk
        exact lt_irrefl 1 hk

  have hcard' := hli.fintype_card_le_finrank
  rw [Fintype.card_option] at hcard'
  omega

end
end Dubon2026.SourceCurve.ValuationApproximation
