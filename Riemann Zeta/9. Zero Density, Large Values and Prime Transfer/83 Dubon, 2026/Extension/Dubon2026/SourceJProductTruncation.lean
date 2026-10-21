import Dubon2026.SourceModularJSeries
import Mathlib.Tactic

/-! DUB-17/18 -> matching modular dimension -> numerical modular genus ->
exact j-map degree -> prime nonmembership. Nonzero positive coefficients
of the actual j series rule out a polynomial identity j(q^p)=P(j(q))
through the root-of-unity orbit sum. This proof uses the literal integral
Eisenstein and eta series already in the original function field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean. Only the coefficient
positivity chain is selected; no external proof options are imported.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
open scoped PowerSeries.WithPiTopology
open PowerSeries Finset

theorem coeff_one_sub_X_pow_of_lt {R : Type*} [CommRing R] {e m : ℕ} (h : m < e) :
    PowerSeries.coeff m ((1 : PowerSeries R) - X ^ e) = if m = 0 then 1 else 0 := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, if_neg (Nat.ne_of_lt h),
    sub_zero]

theorem coeff_prod_one_sub_X_pow_eq_coeff_one {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, n < e i) :
    ∀ m ≤ n, PowerSeries.coeff m (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) =
      if m = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _; simp [PowerSeries.coeff_one]
  | @insert a s ha ih =>
    intro m hm
    rw [Finset.prod_insert ha, PowerSeries.coeff_mul]
    have hea : n < e a := he a (Finset.mem_insert_self a s)
    have hsum :
        ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          PowerSeries.coeff p.1 ((1 : PowerSeries R) - X ^ e a) *
              PowerSeries.coeff p.2 (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) =
            if p.1 = 0 then
              PowerSeries.coeff p.2 (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) else 0 := by
      intro p hp
      have hp1 : p.1 ≤ m := Finset.antidiagonal.fst_le hp
      rw [coeff_one_sub_X_pow_of_lt (lt_of_le_of_lt (le_trans hp1 hm) hea)]
      by_cases h0 : p.1 = 0
      · rw [if_pos h0, if_pos h0, one_mul]
      · rw [if_neg h0, if_neg h0, zero_mul]
    rw [Finset.sum_congr rfl hsum]
    rw [Finset.sum_eq_single_of_mem (0, m) (by simp)]
    · rw [if_pos rfl]
      exact ih (fun i hi => he i (Finset.mem_insert_of_mem hi)) m hm
    · rintro ⟨b₁, b₂⟩ hb hne
      have hb' : b₁ + b₂ = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have : b₁ ≠ 0 := by
        rintro rfl
        exact hne (by simp [← hb'])
      rw [if_neg this]

theorem coeff_prod_one_sub_pow_le {R : Type*} [CommRing R] (k n : ℕ) (h : n ≤ k) :
    PowerSeries.coeff n
        (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) := by
  classical
  have hsplit :
      (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) *
          ∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1)) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.prod_Ico_consecutive _ (Nat.zero_le _) (Nat.succ_le_succ h)]
  rw [hsplit, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ ?_
    intro i hi
    have : n + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.antidiagonal.snd_le hb
    have : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, if_neg this, mul_zero]

theorem coeff_etaProd_eq_coeff_partialProd (n : ℕ) :
    PowerSeries.coeff n etaProd =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) := by
  classical
  have hconv : Filter.Tendsto
      (fun s : Finset ℕ =>
        PowerSeries.coeff n (∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ)))
      Filter.atTop (nhds (PowerSeries.coeff n etaProd)) := by
    have h0 : Filter.Tendsto
        (fun s : Finset ℕ => ∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ))
        Filter.atTop (nhds etaProd) :=
      (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
    exact (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mp h0 n
  rw [show nhds (PowerSeries.coeff n etaProd) = pure (PowerSeries.coeff n etaProd) from
      congrFun (nhds_discrete ℤ) _,
    Filter.tendsto_pure] at hconv
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hconv
  rw [← ht₀ (t₀ ∪ Finset.range (n + 1)) Finset.subset_union_left]
  rw [show t₀ ∪ Finset.range (n + 1)
        = Finset.range (n + 1) ∪ (t₀ \ Finset.range (n + 1)) by
      rw [Finset.union_sdiff_self_eq_union, Finset.union_comm],
    Finset.prod_union Finset.disjoint_sdiff, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ t₀ \ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ (fun i hi => ?_)
    have hi' : ¬ i < n + 1 := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h)
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, if_neg h2, mul_zero]

theorem coeff_jq_eq_coeff_jNum (n : ℕ) :
    jq.coeff ((n : ℤ) - 1) = ((PowerSeries.coeff n jNum : ℤ) : ℚ) := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul,
    show ((n : ℤ) - 1 - (-1) : ℤ) = ((n : ℕ) : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff, jNumQ, PowerSeries.coeff_map]
  simp


end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
