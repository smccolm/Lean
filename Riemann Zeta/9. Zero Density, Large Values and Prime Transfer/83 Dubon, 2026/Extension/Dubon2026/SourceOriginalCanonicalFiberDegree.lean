import Dubon2026.SourceOriginalCanonicalFiberSupport
import Dubon2026.SourceOriginalCuspCount
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> matching cusp-form dimension -> numerical modular genus.
Sum the actual canonical divisor over its three proved exceptional fibers.
The existing exact j-degree identities supply all multiplicity sums.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped BigOperators

theorem original_jCanonical_degree_fiber_finsets (N : ℕ) [NeZero N]
    (S0 S1728 Spole : Finset (Place ℂ (modularFunctionFieldOver N ℂ)))
    (h0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jOver N ℂ))
    (h1728 : ∀ v, v ∈ S1728 ↔
      0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728))
    (hpole : ∀ v, v ∈ Spole ↔ v.ord (jOver N ℂ) < 0) :
    Divisor.degree (originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) - S0.card - S1728.card - Spole.card := by
  classical
  let K := originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ)
  have hd01 : Disjoint S0 S1728 := by
    apply Finset.disjoint_left.mpr
    intro v hv0 hv1
    have hz : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 0) := by
      simpa only [map_zero, sub_zero] using (h0 v).mp hv0
    have he := original_j_fiber_value_unique N v 0 1728 hz ((h1728 v).mp hv1)
    norm_num at he
  have hdp : Disjoint (S0 ∪ S1728) Spole := by
    apply Finset.disjoint_left.mpr
    intro v hv hvp
    have hp := (hpole v).mp hvp
    rcases Finset.mem_union.mp hv with h | h
    · exact (not_lt_of_ge ((h0 v).mp h).le) hp
    · exact (not_lt_of_ge (original_j_fiber_nonneg N v 1728 ((h1728 v).mp h))) hp
  have hsupp := original_jCanonical_support_subset_fibers N S0 S1728 Spole h0 h1728 hpole
  have hdeg : Divisor.degree K = ∑ v ∈ S0 ∪ S1728 ∪ Spole, K v := by
    rw [Divisor.degree_eq_sum_support]
    have hr : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), Module.finrank ℂ v.ResidueField = 1 :=
      fun v => Module.finrank_of_bijective_algebraMap
        (original_place_residue_algebraMap_bijective N ℂ v)
    simp_rw [hr, Nat.cast_one, mul_one]
    exact Finset.sum_subset hsupp (fun v _ hv => Finsupp.notMem_support_iff.mp hv)
  have hs0 : (∑ v ∈ S0, K v) = (SourceLevelProjective.dedekindPsi N : ℤ) - S0.card := by
    have hv : ∀ v ∈ S0, K v = v.ord (jOver N ℂ) - 1 := by
      intro v hv
      have hz : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 0) := by
        simpa only [map_zero, sub_zero] using (h0 v).mp hv
      simpa only [map_zero, sub_zero] using original_jCanonical_at_value N ℂ v 0 hz
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib]
    have hs := sum_original_j_fiber_orders_finset N ℂ 0 S0
      (fun v => by simpa only [map_zero, sub_zero] using h0 v)
    simp only [map_zero, sub_zero] at hs
    simp only [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hs1 : (∑ v ∈ S1728, K v) = (SourceLevelProjective.dedekindPsi N : ℤ) - S1728.card := by
    have hv : ∀ v ∈ S1728,
        K v = v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) - 1 :=
      fun v hv => original_jCanonical_at_value N ℂ v 1728 ((h1728 v).mp hv)
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib,
      sum_original_j_fiber_orders_finset N ℂ 1728 S1728 h1728]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsp : (∑ v ∈ Spole, K v) = -(SourceLevelProjective.dedekindPsi N : ℤ) - Spole.card := by
    have hv : ∀ v ∈ Spole, K v = v.ord (jOver N ℂ) - 1 :=
      fun v hv => original_jCanonical_at_pole N ℂ v ((hpole v).mp hv)
    rw [Finset.sum_congr rfl hv, Finset.sum_sub_distrib]
    have hs := sum_original_j_pole_orders_finset N ℂ Spole hpole
    rw [Finset.sum_neg_distrib] at hs
    have hsum : ∑ v ∈ Spole, v.ord (jOver N ℂ) = -(SourceLevelProjective.dedekindPsi N : ℤ) := by omega
    simp only [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hdeg, Finset.sum_union hdp, Finset.sum_union hd01, hs0, hs1, hsp]
  ring

theorem original_jCanonical_degree_eq_fiber_cards (N : ℕ) [NeZero N] :
    Divisor.degree (originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) -
        Nat.card {v : Place ℂ (modularFunctionFieldOver N ℂ) // 0 < v.ord (jOver N ℂ)} -
        Nat.card {v : Place ℂ (modularFunctionFieldOver N ℂ) //
          0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)} -
        SourceLevelProjective.cuspCount N := by
  classical
  have hz := finite_original_places_positive N ℂ (jOver N ℂ)
  have he := finite_original_places_positive N ℂ
    (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)
  have hp : {v : Place ℂ (modularFunctionFieldOver N ℂ) | v.ord (jOver N ℂ) < 0}.Finite :=
    (finite_original_divisor_support N ℂ (jOver N ℂ)).subset fun _ hv => ne_of_lt hv
  have hcard {P : Place ℂ (modularFunctionFieldOver N ℂ) → Prop}
      (h : {v | P v}.Finite) : Nat.card {v // P v} = h.toFinset.card := by
    calc
      _ = Nat.card ↥h.toFinset := Nat.card_congr
        (Equiv.subtypeEquivRight fun v => (h.mem_toFinset (a := v)).symm)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard hz, hcard he]
  have hc := card_original_j_poles_eq_cuspCount N ℂ hp.toFinset (fun v => hp.mem_toFinset)
  rw [← hc]
  exact original_jCanonical_degree_fiber_finsets N hz.toFinset he.toFinset hp.toFinset
    (fun v => hz.mem_toFinset) (fun v => he.mem_toFinset) (fun v => hp.mem_toFinset)

end
end Dubon2026.SourceFunctionField
