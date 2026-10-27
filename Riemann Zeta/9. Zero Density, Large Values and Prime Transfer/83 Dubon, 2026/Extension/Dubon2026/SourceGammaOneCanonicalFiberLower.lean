import Dubon2026.SourceGammaOneCanonicalCoordinates
import Dubon2026.SourceGammaOneJDegreeFinsets

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> genus lower
bound. Sum the actual zero, 1728 and pole fibers. All omitted finite
places have nonnegative canonical coefficient. This uses only the lower
bound required by the period comparison, without an exact genus formula. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve IntermediateField
open scoped MatrixGroups IntermediateField
variable {Γ : Subgroup SL(2, ℤ)}

theorem j_fiber_nonneg (v : Place ℂ (functionFieldOver Γ ℂ)) (c : ℂ)
    (hc : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)) :
    0 ≤ v.ord (jCoordinateOver Γ ℂ) := by
  apply v.ord_nonneg_of_mem
  have h := add_mem (v.mem_of_ord_nonneg hc.le) (v.algebraMap_mem' c)
  simpa only [sub_add_cancel] using h

variable [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

include hT in
theorem j_fiber_value_unique (v : Place ℂ (functionFieldOver Γ ℂ)) (c d : ℂ)
    (hc : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c))
    (hd : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) d)) :
    c = d := by
  obtain ⟨a, _, ha⟩ := v.exists_unique_coordinate_value (place_residue_bijective hT v).surjective
    (transcendental_jCoordinateOver Γ ℂ) (v.mem_of_ord_nonneg (j_fiber_nonneg v c hc))
  exact (ha c hc).trans (ha d hd).symm

theorem jCanonical_degree_lower_finsets
    (S0 S1728 Spole : Finset (Place ℂ (functionFieldOver Γ ℂ)))
    (h0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jCoordinateOver Γ ℂ))
    (h1728 : ∀ v, v ∈ S1728 ↔
      0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 1728))
    (hpole : ∀ v, v ∈ Spole ↔ v.ord (jCoordinateOver Γ ℂ) < 0) :
    (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) -
      S0.card - S1728.card - Spole.card ≤ Divisor.degree (jCanonicalDivisor hT) := by
  classical
  let K := jCanonicalDivisor hT
  have hd01 : Disjoint S0 S1728 := by
    apply Finset.disjoint_left.mpr
    intro v hv0 hv1
    have hz : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 0) := by
      simpa only [map_zero, sub_zero] using (h0 v).mp hv0
    have he := j_fiber_value_unique hT v 0 1728 hz ((h1728 v).mp hv1)
    norm_num at he
  have hdp : Disjoint (S0 ∪ S1728) Spole := by
    apply Finset.disjoint_left.mpr
    intro v hv hvp
    have hp := (hpole v).mp hvp
    rcases Finset.mem_union.mp hv with h | h
    · exact (not_lt_of_ge ((h0 v).mp h).le) hp
    · exact (not_lt_of_ge (j_fiber_nonneg v 1728 ((h1728 v).mp h))) hp
  have hdeg : (∑ v ∈ S0 ∪ S1728 ∪ Spole, K v) ≤ Divisor.degree K := by
    rw [Divisor.degree_eq_sum_support]
    have hr (v : Place ℂ (functionFieldOver Γ ℂ)) : Module.finrank ℂ v.ResidueField = 1 :=
      Module.finrank_of_bijective_algebraMap (place_residue_bijective hT v)
    simp_rw [hr, Nat.cast_one, mul_one]
    calc
      _ ≤ ∑ v ∈ (S0 ∪ S1728 ∪ Spole) ∪ K.support, K v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        intro v _ hv
        apply jCanonicalDivisor_nonneg_of_j_nonneg hT v
        by_contra hn
        have hp := (hpole v).mpr (lt_of_not_ge hn)
        exact hv (Finset.mem_union_right _ hp)
      _ = ∑ v ∈ K.support, K v := by
        symm
        exact Finset.sum_subset Finset.subset_union_right
          (fun v _ hv => Finsupp.notMem_support_iff.mp hv)
  have hs0 : (∑ v ∈ S0, K v) = (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) - S0.card := by
    have hv : ∀ v ∈ S0, K v = v.ord (jCoordinateOver Γ ℂ) - 1 := by
      intro v hv
      have hz : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 0) := by
        simpa only [map_zero, sub_zero] using (h0 v).mp hv
      simpa only [map_zero, sub_zero] using jCanonicalDivisor_at_value hT v 0 hz
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib]
    have hs := sum_j_fiber_orders_finset hT 0 S0
      (fun v => by simpa only [map_zero, sub_zero] using h0 v)
    simp only [map_zero, sub_zero] at hs
    simp only [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hs1 : (∑ v ∈ S1728, K v) = (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) - S1728.card := by
    have hv : ∀ v ∈ S1728,
        K v = v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 1728) - 1 :=
      fun v hv => jCanonicalDivisor_at_value hT v 1728 ((h1728 v).mp hv)
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib,
      sum_j_fiber_orders_finset hT 1728 S1728 h1728]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsp : (∑ v ∈ Spole, K v) = -(Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) - Spole.card := by
    have hv : ∀ v ∈ Spole, K v = v.ord (jCoordinateOver Γ ℂ) - 1 :=
      fun v hv => jCanonicalDivisor_at_pole hT v ((hpole v).mp hv)
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib]
    have hs := sum_j_pole_orders_finset hT Spole hpole
    rw [Finset.sum_neg_distrib] at hs
    have hsum : ∑ v ∈ Spole, v.ord (jCoordinateOver Γ ℂ) = -(Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) := by omega
    simp only [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_union hdp, Finset.sum_union hd01, hs0, hs1, hsp] at hdeg
  dsimp only [K] at hdeg
  linarith

end
end Dubon2026.SourceFunctionField.GammaOne
