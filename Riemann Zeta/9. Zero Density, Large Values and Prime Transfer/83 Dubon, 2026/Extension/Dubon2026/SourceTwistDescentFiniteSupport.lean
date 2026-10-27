import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> descent of the proved coefficient-twist-stable cusp image. Finite scalar
support and original-field fixed coefficients yield descent of the actual
stable subspace. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_WLight_span_inter_rational_of_twist_stable. Only its necessary abstract
descent argument is retained; the already proved actual coefficient twist
replaces the separate external flatness/twist construction. -/
namespace Dubon2026.SourceFunctionField.TwistDescent
noncomputable section

theorem descent_core {k K E : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup E]
    [Module K E] {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → E)
    (V : Submodule K E) (P : ι → Prop) [DecidablePred P] (hP : ∀ i, P i → e i ∈ V)
    (key : ∀ a : ι → k, (∑ i, algebraMap k K (a i) • e i) ∈ V → ∀ i, ¬ P i → a i = 0)
    (T : (K ≃ₐ[k] K) → E → E)
    (hT : ∀ (σ : K ≃ₐ[k] K) (c : ι → K), T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i)
    (hTV : ∀ σ, ∀ v ∈ V, T σ v ∈ V)
    (G1 : ∀ c : K, (∀ σ : K ≃ₐ[k] K, σ c = c) → ∃ a : k, algebraMap k K a = c)
    (c : ι → K) (hc : (∑ i, c i • e i) ∈ V) : ∀ i, ¬ P i → c i = 0 := by
  classical
  suffices h : ∀ (n : ℕ) (c : ι → K),
      (Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0).card ≤ n → (∑ i, c i • e i) ∈ V →
        ∀ i, ¬ P i → c i = 0 from h _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hn hc i hi
    by_contra h
    have : i ∈ Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0 := by simp [hi, h]
    rw [Nat.le_zero, Finset.card_eq_zero] at hn
    simp [hn] at this
  | succ n ih =>
    intro c hn hc
    by_contra hex
    push Not at hex
    obtain ⟨i₀, hi₀, hci₀⟩ := hex
    set c' : ι → K := fun i ↦ (c i₀)⁻¹ * c i with hc'def
    have hc' : (∑ i, c' i • e i) ∈ V := by
      have : (∑ i, c' i • e i) = (c i₀)⁻¹ • ∑ i, c i • e i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
      rw [this]; exact V.smul_mem _ hc
    have hc'i₀ : c' i₀ = 1 := inv_mul_cancel₀ hci₀
    have hc'supp : ∀ i, c' i ≠ 0 → c i ≠ 0 := fun i h h0 ↦ h (by simp [hc'def, h0])
    have hfix : ∀ (σ : K ≃ₐ[k] K) (i : ι), ¬ P i → σ (c' i) = c' i := by
      intro σ
      set d : ι → K := fun i ↦ σ (c' i) - c' i with hddef
      have hd : (∑ i, d i • e i) ∈ V := by
        have : (∑ i, d i • e i) = T σ (∑ i, c' i • e i) - ∑ i, c' i • e i := by
          rw [hT, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [sub_smul]
        rw [this]; exact V.sub_mem (hTV σ _ hc') hc'
      have hsub : (Finset.univ.filter fun i ↦ ¬ P i ∧ d i ≠ 0) ⊆
          (Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0).erase i₀ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_erase, Finset.mem_filter]
        refine ⟨?_, Finset.mem_univ _, hi.1, hc'supp i fun h0 ↦ hi.2 (by simp [hddef, h0])⟩
        rintro rfl
        exact hi.2 (by simp [hddef, hc'i₀])
      have hcard : (Finset.univ.filter fun i ↦ ¬ P i ∧ d i ≠ 0).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        have h2 : i₀ ∈ Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0 := by simp [hi₀, hci₀]
        rw [Finset.card_erase_of_mem h2] at h1
        omega
      intro i hi
      exact sub_eq_zero.mp (ih d hcard hd i hi)
    have hk : ∀ i, ¬ P i → ∃ a : k, algebraMap k K a = c' i := fun i hi ↦
      G1 (c' i) fun σ ↦ hfix σ i hi
    choose a ha using hk
    let a' : ι → k := fun i ↦ if h : ¬ P i then a i h else 0
    have ha' : ∀ i, algebraMap k K (a' i) = if P i then 0 else c' i := by
      intro i
      by_cases h : P i
      · simp [a', h]
      · simp [a', h, ha i h]
    have hm : (∑ i, algebraMap k K (a' i) • e i) ∈ V := by
      have : (∑ i, algebraMap k K (a' i) • e i) =
          (∑ i, c' i • e i) - ∑ i, (if P i then c' i else 0) • e i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ha', ← sub_smul]
        by_cases h : P i <;> simp [h]
      rw [this]
      refine V.sub_mem hc' (V.sum_mem fun i _ ↦ ?_)
      by_cases h : P i
      · simp only [h, if_true]; exact V.smul_mem _ (hP i h)
      · simp [h]
    have := key a' hm i₀ hi₀
    have h1 : algebraMap k K (a' i₀) = 1 := by rw [ha', if_neg hi₀, hc'i₀]
    rw [this, map_zero] at h1
    exact zero_ne_one h1

end
end Dubon2026.SourceFunctionField.TwistDescent
