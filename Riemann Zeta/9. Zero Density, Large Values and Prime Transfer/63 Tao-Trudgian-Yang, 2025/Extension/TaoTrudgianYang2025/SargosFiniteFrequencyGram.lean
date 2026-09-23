import TaoTrudgianYang2025.SargosSymmetricDifferencing

/-! Exact finite Gram expansion and frequency-diagonal grouping. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_finite_gram {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖^2 = ∑ q ∈ S ×ˢ S, (f q.1*conj (f q.2)).re := by
  have h : ((‖∑ i ∈ S, f i‖^2 : ℝ):ℂ) =
      ∑ q ∈ S ×ˢ S, f q.1*conj (f q.2) := by
    rw [Complex.ofReal_pow,← Complex.mul_conj',map_sum,Finset.sum_mul_sum,Finset.sum_product]
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re,Complex.re_sum] using hr

theorem sargos_frequency_diagonal_sum {ι κ A : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid A]
    (T : Finset ι) (K : Finset κ) (v : ι → κ)
    (hv : ∀ t ∈ T, v t ∈ K) (f : ι × ι → A) :
    (∑ k ∈ K, ∑ q ∈ (T.filter (fun t => v t=k)) ×ˢ
      (T.filter (fun t => v t=k)), f q) =
      ∑ q ∈ (T ×ˢ T).filter (fun q => v q.1=v q.2), f q := by
  have hfilter (k : κ) :
      (T.filter (fun t => v t=k)) ×ˢ (T.filter (fun t => v t=k)) =
        (T ×ˢ T).filter (fun q => v q.1=k ∧ v q.2=k) := by
    ext q
    simp only [Finset.mem_product,Finset.mem_filter]
    tauto
  simp_rw [hfilter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 := (Finset.mem_product.mp hq).1
  rw [Finset.sum_eq_single (v q.1)]
  · by_cases he : v q.1=v q.2
    · simp [he]
    · simp [he,Ne.symm he]
  · intro k hk hne
    simp [Ne.symm hne]
  · intro hk
    exact False.elim (hk (hv _ hq1))

theorem sargos_grouped_gram {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (T : Finset ι) (K : Finset κ) (v : ι → κ)
    (hv : ∀ t ∈ T, v t ∈ K) (f : ι → ℂ) :
    (∑ k ∈ K, ‖∑ t ∈ T with v t=k, f t‖^2) =
      ∑ q ∈ (T ×ˢ T).filter (fun q => v q.1=v q.2),
        (f q.1*conj (f q.2)).re := by
  simp_rw [sargos_finite_gram]
  exact sargos_frequency_diagonal_sum T K v hv _

end TaoTrudgianYang2025
