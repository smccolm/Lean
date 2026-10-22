import Dubon2026.SourceMeromorphicPoleBound

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Meromorphic functions with a fixed effective
pole bound satisfy a linear relation once their number exceeds its degree
plus one. Removing one leading coefficient reduces the allowed pole degree;
compact holomorphic constancy supplies degree zero. This is the analytic
dimension bound required to identify functions with original field elements.
Adapted from S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M] [ConnectedSpace M]

/-- Sum of the allowed pole multiplicities. -/
abbrev degN (D : M →₀ ℕ) : ℕ := D.sum fun _ n => n

omit [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M]
  [ConnectedSpace M] in
theorem degN_eq_zero_iff (D : M →₀ ℕ) : degN D = 0 ↔ D = 0 := by
  constructor
  · intro h
    rw [degN, Finsupp.sum, Finset.sum_eq_zero_iff] at h
    ext x
    by_cases hx : x ∈ D.support
    · exact h x hx
    · exact Finsupp.notMem_support_iff.1 hx
  · rintro rfl; rfl

omit [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M]
  [ConnectedSpace M] in
theorem degN_sub_single {D : M →₀ ℕ} {x₀ : M} (hx₀ : 1 ≤ D x₀) :
    degN (D - Finsupp.single x₀ 1) + 1 = degN D := by
  classical
  have hle : Finsupp.single x₀ 1 ≤ D := by
    intro x
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst h; exact hx₀
    · exact Nat.zero_le _
  have hD : D = (D - Finsupp.single x₀ 1) + Finsupp.single x₀ 1 := (tsub_add_cancel_of_le hle).symm
  conv_rhs => rw [hD]
  rw [degN, degN, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

theorem base {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ) (hψ : ∀ i, Bdd 0 (ψ i))
    (hcard : 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x, rd (∑ i, c i • ψ i) x =ᶠ[𝓝[≠] (ctr x)] 0 := by
  classical
  have hconst : ∀ i, ∃ C : ℂ, ∀ x, rd (ψ i) x =ᶠ[𝓝[≠] (ctr x)] fun _ => C := fun i =>
    exists_const_germs_of_nonneg_order (ψ i)
      (fun x => (hψ i x).1) (fun x => by have h__af := (hψ i x).2; simp at h__af; exact h__af)
  choose C hC using hconst
  obtain ⟨i₁, i₂, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
  by_cases h1 : C i₁ = 0
  · refine ⟨Pi.single i₁ (1 : ℂ), fun h => one_ne_zero (α := ℂ) (by simpa using congrFun h i₁),
      fun x => ?_⟩
    have : rd (∑ i, (Pi.single i₁ (1 : ℂ) : ι → ℂ) i • ψ i) x = rd (ψ i₁) x := by
      funext z
      simp only [rd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this]
    filter_upwards [hC i₁ x] with z hz
    rw [hz, h1, Pi.zero_apply]
  · refine ⟨Pi.single i₁ (C i₂) - Pi.single i₂ (C i₁), fun h => h1 ?_, fun x => ?_⟩
    · have := congrFun h i₂
      simp only [Pi.sub_apply, Pi.single_apply, if_neg hne.symm, zero_sub,
        Pi.zero_apply, neg_eq_zero] at this
      exact this
    · have : rd (∑ i, (Pi.single i₁ (C i₂) - Pi.single i₂ (C i₁) : ι → ℂ) i • ψ i) x =
          C i₂ • rd (ψ i₁) x - C i₁ • rd (ψ i₂) x := by
        funext z
        simp only [rd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
          Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
      filter_upwards [hC i₁ x, hC i₂ x] with z h₁ h₂
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h₁, h₂, Pi.zero_apply]
      ring



end
end Dubon2026.SourceFunctionField.MeromorphicCompact
