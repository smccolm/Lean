import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite auxiliary families for the DUB-17 dual Selmer argument.
Pointwise detection outside arbitrary finite sets gives an injective joint
restriction with at most the dimension many primes. -/

namespace Dubon2026
noncomputable section

/-- A family detecting every nonzero vector outside any finite forbidden set
has a finite detecting subfamily of cardinality at most the dimension.
The conclusion retains each member's prescribed arithmetic property. -/
theorem finite_detecting_family_of_pointwise
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : I → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (L : ∀ i, V →ₗ[K] W i) (Good : I → Prop)
    (hdetect : ∀ S : Finset I, ∀ x : V, x ≠ 0 →
      ∃ i, i ∉ S ∧ Good i ∧ L i x ≠ 0)
    (S : Finset I) :
    ∃ Q : Finset I, Q.card ≤ Module.finrank K V ∧
      (∀ i ∈ Q, i ∉ S ∧ Good i) ∧
      (∀ x : V, (∀ i ∈ Q, L i x = 0) → x = 0) := by
  classical
  have aux : ∀ d : ℕ, ∀ P : Submodule K V, Module.finrank K P = d →
      ∀ T : Finset I, ∃ Q : Finset I, Q.card ≤ d ∧
        (∀ i ∈ Q, i ∉ T ∧ Good i) ∧
        (∀ x ∈ P, (∀ i ∈ Q, L i x = 0) → x = 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hd T
      by_cases hP : P = ⊥
      · refine ⟨∅, by simp, by simp, ?_⟩
        intro x hx _
        simpa [hP] using hx
      obtain ⟨x, hxP, hx⟩ := P.ne_bot_iff.mp hP
      obtain ⟨i, hiT, hiGood, hix⟩ := hdetect T x hx
      let P' := P ⊓ LinearMap.ker (L i)
      have hlt : P' < P := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hx' : x ∈ P' := heq.symm ▸ hxP
        exact hix hx'.2
      have hdim : Module.finrank K P' < d := by
        rw [← hd]
        exact Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨Q, hcard, hQ, hzero⟩ := ih _ hdim P' rfl (insert i T)
      have hiQ : i ∉ Q := by
        intro hi
        exact (hQ i hi).1 (Finset.mem_insert_self i T)
      refine ⟨insert i Q, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hiQ]
        omega
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨hiT, hiGood⟩
        · exact ⟨fun hjT => (hQ j hj).1 (Finset.mem_insert_of_mem hjT), (hQ j hj).2⟩
      · intro y hy hLy
        exact hzero y ⟨hy, hLy i (Finset.mem_insert_self i Q)⟩
          (fun j hj => hLy j (Finset.mem_insert_of_mem hj))
  obtain ⟨Q, hcard, hQ, hzero⟩ := aux (Module.finrank K V) ⊤
    (finrank_top K V) S
  exact ⟨Q, hcard, hQ, fun x hx => hzero x (Submodule.mem_top) hx⟩

end
end Dubon2026
