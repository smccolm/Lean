import Dubon2026.SeparableRootQuotient

/-! # Exact open-interval root counts from the signed Euclidean algorithm -/

namespace Dubon2026

open Polynomial

noncomputable section

theorem separable_root_count_Ioc {P : ℝ[X]} (hP : P.Separable) {l u : ℝ} (hlu : l < u) :
    (P.roots.filter (fun t => t ∈ Set.Ioc l u)).card =
      realPolynomialRootCount P l u + if P.eval u = 0 then 1 else 0 := by
  classical
  have hs := Multiset.filter_add_not (fun t : ℝ => t < u)
    (P.roots.filter (fun t => t ∈ Set.Ioc l u))
  rw [Multiset.filter_filter, Multiset.filter_filter] at hs
  have h1 : P.roots.filter (fun t => t < u ∧ t ∈ Set.Ioc l u) =
      P.roots.filter (fun t => l < t ∧ t < u) := by
    apply Multiset.filter_congr
    intro t _
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le⟩⟩
  have h2 : P.roots.filter (fun t => ¬ t < u ∧ t ∈ Set.Ioc l u) =
      P.roots.filter (fun t => t = u) := by
    apply Multiset.filter_congr
    intro t _
    constructor
    · intro h
      exact le_antisymm h.2.2 (le_of_not_gt h.1)
    · rintro rfl
      exact ⟨lt_irrefl _, hlu, le_rfl⟩
  rw [h1, h2] at hs
  have he := congrArg Multiset.card hs
  rw [Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate] at he
  have hc : P.roots.count u = if P.eval u = 0 then 1 else 0 := by
    by_cases hr : P.eval u = 0
    · rw [if_pos hr]
      exact Multiset.count_eq_one_of_mem (Polynomial.nodup_roots hP)
        ((Polynomial.mem_roots hP.ne_zero).mpr hr)
    · rw [if_neg hr]
      exact Multiset.count_eq_zero.mpr (fun h => hr ((Polynomial.mem_roots hP.ne_zero).mp h))
  rw [hc] at he
  exact he.symm

/-- A finite Euclidean sign-variation formula, including the open upper endpoint. -/
def sturmOpenCount (P : ℝ[X]) (l u : ℝ) : ℕ :=
  if l < u then
    if P.derivative = 0 then 0 else
      Sturm.sturmVar (euclideanSturmChain P) l -
        Sturm.sturmVar (euclideanSturmChain P) u - if P.eval u = 0 then 1 else 0
  else 0

theorem sturmOpenCount_eq_root_count {P : ℝ[X]} (hP : P.Separable) (l u : ℝ) :
    sturmOpenCount P l u = realPolynomialRootCount P l u := by
  classical
  by_cases hlu : l < u
  · by_cases hd : P.derivative = 0
    · rw [sturmOpenCount, if_pos hlu, if_pos hd]
      rw [realPolynomialRootCount, Polynomial.eq_C_of_derivative_eq_zero hd, Polynomial.roots_C]
      rfl
    · rw [sturmOpenCount, if_pos hlu, if_neg hd]
      have hc := euclideanSturmChain_count_Ioc hP hd hlu.le
      rw [separable_root_count_Ioc hP hlu] at hc
      omega
  · rw [sturmOpenCount, if_neg hlu]
    unfold realPolynomialRootCount
    have hz : P.roots.filter (fun t => l < t ∧ t < u) = 0 := by
      rw [Multiset.filter_eq_nil]
      exact fun t _ ht => hlu (ht.1.trans ht.2)
    rw [hz]
    rfl

/-- The actual finite Sturm computation of multiplicity-weighted roots. -/
def sturmMultiplicityCount (P : ℝ[X]) (l u : ℝ) : ℕ :=
  ∑ k ∈ Finset.range P.natDegree,
    sturmOpenCount (derivativeRootQuotient (derivativeGcdLayer P k)) l u

theorem sturmMultiplicityCount_eq_root_count {P : ℝ[X]} (hP : P ≠ 0) (l u : ℝ) :
    sturmMultiplicityCount P l u = realPolynomialRootCount P l u := by
  rw [realPolynomialRootCount_eq_sum_distinct_layers hP]
  unfold sturmMultiplicityCount
  apply Finset.sum_congr rfl
  intro k _
  rw [sturmOpenCount_eq_root_count
    (derivativeRootQuotient_separable (derivativeGcdLayer_ne_zero hP k)),
    distinct_count_eq_derivativeRootQuotient_count (derivativeGcdLayer_ne_zero hP k)]

end

end Dubon2026
