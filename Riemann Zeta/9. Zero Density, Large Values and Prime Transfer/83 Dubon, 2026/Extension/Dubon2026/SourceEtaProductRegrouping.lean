import Dubon2026.SourceEtaProductTransport

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> discriminant norm identity.
These proofs establish the literal product of root-of-unity twists of the eta
series, regrouping divisible and nondivisible indices. Only the topology and
product identities required for this exact norm calculation are selected.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_deltaNorm. The existing q-substitution/power-series
identity is reused; repeated first-coefficient proofs are omitted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped PowerSeries.WithPiTopology

/-- The eta factors at indices multiplied by k. -/
def uFam (K : Type*) [CommRing K] (k n : ℕ) : PowerSeries K := 1 - PowerSeries.X ^ (k * (n + 1))

/-- The factors at indices not divisible by p. -/
def hFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 else 1 - PowerSeries.X ^ (p * (n + 1))

/-- The p-th powers of factors at indices divisible by p. -/
def gFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1

/-- The factors with doubled p-substitution at divisible indices. -/
def g'Fam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 - PowerSeries.X ^ (p * (n + 1)) else 1

/-- The actual factor produced by the root-of-unity product. -/
def cFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1 - PowerSeries.X ^ (p * (n + 1))

theorem cFam_eq (K : Type*) [CommRing K] (p n : ℕ) : cFam K p n = hFam K p n * gFam K p n := by
  unfold cFam hFam gFam
  split_ifs <;> ring

theorem uFam_eq (K : Type*) [CommRing K] (p n : ℕ) : uFam K p n = hFam K p n * g'Fam K p n := by
  unfold uFam hFam g'Fam
  split_ifs <;> ring

theorem one_le_index {p : ℕ} (hp : 0 < p) (m : ℕ) : 1 ≤ p * (m + 1) :=
  Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne' (Nat.succ_ne_zero m))

theorem index_injective {p : ℕ} (hp : 0 < p) : Function.Injective fun m : ℕ => p * (m + 1) - 1 := by
  intro a b hab
  have h := (tsub_left_inj (one_le_index hp a) (one_le_index hp b)).1 hab
  have h' := Nat.eq_of_mul_eq_mul_left hp h
  omega

theorem mulSupport_subset_range {K : Type*} [CommRing K] {p : ℕ} (F : ℕ → PowerSeries K)
    (hF : ∀ n, ¬ p ∣ n + 1 → F n = 1) :
    Function.mulSupport F ⊆ Set.range fun m : ℕ => p * (m + 1) - 1 := by
  intro n hn
  rw [Function.mem_mulSupport] at hn
  by_cases hd : p ∣ n + 1
  · obtain ⟨k, hk⟩ := hd
    cases k with
    | zero => simp at hk
    | succ m => exact ⟨m, (Nat.eq_sub_of_add_eq hk).symm⟩
  · exact absurd (hF n hd) hn

section Multipliable

variable (K : Type*) [CommRing K] [TopologicalSpace K]

theorem multipliable_uFam {k : ℕ} (hk : 0 < k) : Multipliable (uFam K k) :=
  multipliable_of_X_pow_dvd _ fun n => by
    rw [uFam, sub_sub_cancel_left, dvd_neg]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hk)

theorem multipliable_hFam {p : ℕ} (hp : 0 < p) : Multipliable (hFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold hFam
    split_ifs
    · simp
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)

theorem multipliable_gFam (p : ℕ) : Multipliable (gFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold gFam
    split_ifs
    · have h1 : (PowerSeries.X : PowerSeries K) ^ (n + 1) ∣ (1 - PowerSeries.X ^ (n + 1)) - 1 :=
        ⟨-1, by ring⟩
      have h2 := sub_dvd_pow_sub_pow ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) 1 p
      rw [one_pow] at h2
      exact h1.trans h2
    · simp

theorem multipliable_g'Fam {p : ℕ} (hp : 0 < p) : Multipliable (g'Fam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold g'Fam
    split_ifs
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)
    · simp

end Multipliable

section Topological

variable (K : Type*) [CommRing K] [TopologicalSpace K] [DiscreteTopology K]

theorem tprod_gFam {p : ℕ} (hp : 0 < p) : ∏' n, gFam K p n = (∏' n, uFam K p n) ^ p := by
  have hsupp := mulSupport_subset_range (gFam K p) fun n hd => by
    unfold gFam; rw [if_neg hd]
  rw [← (index_injective hp).tprod_eq hsupp, ← (multipliable_uFam K hp).tprod_pow]
  exact tprod_congr fun m => by
    show gFam K p (p * (m + 1) - 1) = uFam K p m ^ p
    unfold gFam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), if_pos (dvd_mul_right p (m + 1))]

omit [DiscreteTopology K] in

theorem tprod_g'Fam {p : ℕ} (hp : 0 < p) : ∏' n, g'Fam K p n = ∏' n, uFam K (p * p) n := by
  have hsupp := mulSupport_subset_range (g'Fam K p) fun n hd => by
    unfold g'Fam; rw [if_neg hd]
  rw [← (index_injective hp).tprod_eq hsupp]
  exact tprod_congr fun m => by
    show g'Fam K p (p * (m + 1) - 1) = uFam K (p * p) m
    unfold g'Fam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), if_pos (dvd_mul_right p (m + 1)), mul_assoc]

theorem regroup {p : ℕ} (hp : 0 < p) :
    (∏' n, cFam K p n) * (∏' n, uFam K (p * p) n) = (∏' n, uFam K p n) ^ (p + 1) := by
  have hc : ∏' n, cFam K p n = (∏' n, hFam K p n) * ∏' n, gFam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_gFam K p)]
    exact tprod_congr fun n => cFam_eq K p n
  have hu : ∏' n, uFam K p n = (∏' n, hFam K p n) * ∏' n, g'Fam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_g'Fam K hp)]
    exact tprod_congr fun n => uFam_eq K p n
  rw [hc, tprod_gFam K hp, ← tprod_g'Fam K hp]
  calc (∏' n, hFam K p n) * (∏' n, uFam K p n) ^ p * ∏' n, g'Fam K p n
      = (∏' n, uFam K p n) ^ p * ((∏' n, hFam K p n) * ∏' n, g'Fam K p n) := by ring
    _ = (∏' n, uFam K p n) ^ (p + 1) := by rw [← hu, pow_succ]

end Topological


end
end Dubon2026.SourceFunctionField
