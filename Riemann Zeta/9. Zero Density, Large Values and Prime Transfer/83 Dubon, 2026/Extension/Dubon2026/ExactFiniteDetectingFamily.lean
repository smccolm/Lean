import Dubon2026.FiniteDetectingFamily

/-! A fixed number of genuine auxiliary directions is needed for the
common parameter algebra in DUB-17's arithmetic patching system. Fresh
pointwise detecting primes extend the existing dimension-bounded family
to the exact dimension while preserving every arithmetic condition. -/

namespace Dubon2026
noncomputable section

/-- Pointwise detection supplies exactly the dimension many genuine
indices with the original arithmetic property and zero common kernel. -/
theorem finite_detecting_family_exact_card_of_pointwise
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : I → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (L : ∀ i, V →ₗ[K] W i) (Good : I → Prop)
    (hdetect : ∀ S : Finset I, ∀ x : V, x ≠ 0 →
      ∃ i, i ∉ S ∧ Good i ∧ L i x ≠ 0)
    (S : Finset I) :
    ∃ Q : Finset I, Q.card = Module.finrank K V ∧
      (∀ i ∈ Q, i ∉ S ∧ Good i) ∧
      (∀ x : V, (∀ i ∈ Q, L i x = 0) → x = 0) := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · letI := hV
    exact ⟨∅, by simp only [Finset.card_empty, Module.finrank_zero_of_subsingleton],
      by simp, fun x _ => Subsingleton.elim x 0⟩
  · letI := hV
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨Q, hcard, hQ, hzero⟩ := finite_detecting_family_of_pointwise L Good hdetect S
    have hfill : ∀ n : ℕ, ∃ T : Finset I, Q ⊆ T ∧ T.card = Q.card + n ∧
        (∀ i ∈ T, i ∉ S ∧ Good i) := by
      intro n
      induction n with
      | zero => exact ⟨Q, Finset.Subset.refl Q, by omega, hQ⟩
      | succ n ih =>
        obtain ⟨T, hQT, hT, hgoodT⟩ := ih
        obtain ⟨i, hi, hgood, _⟩ := hdetect (S ∪ T) x hx
        have hi' := Finset.notMem_union.mp hi
        refine ⟨insert i T, fun j hj => Finset.mem_insert_of_mem (hQT hj), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hi'.2, hT]
          omega
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ⟨hi'.1, hgood⟩
          · exact hgoodT j hj
    obtain ⟨T, hQT, hT, hgoodT⟩ := hfill (Module.finrank K V - Q.card)
    refine ⟨T, by omega, hgoodT, ?_⟩
    intro y hy
    exact hzero y (fun j hj => hy j (hQT hj))

end
end Dubon2026
