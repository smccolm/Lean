import Dubon2026.FiniteDetectingFamily
import Mathlib.Data.Nat.Prime.Defs

/-! The natural-prime indexing step of DUB-17's original detecting-family
consumer. Reuse the native dimension induction without a second induction. -/
namespace Dubon2026
noncomputable section

/-- Detection outside finite sets of natural primes yields a bounded
family retaining the given prime property and original restriction maps. -/
theorem finite_detecting_prime_family_of_pointwise
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Nat.Primes → Type} [∀ q, AddCommGroup (W q)] [∀ q, Module K (W q)]
    (L : ∀ q, V →ₗ[K] W q) (Good : Nat.Primes → Prop)
    (hdetect : ∀ x : V, x ≠ 0 → ∀ S : Finset ℕ,
      ∃ q : Nat.Primes, q.val ∉ S ∧ Good q ∧ L q x ≠ 0) (S : Finset ℕ) :
    ∃ Q : Finset Nat.Primes, Q.card ≤ Module.finrank K V ∧
      (∀ q ∈ Q, q.val ∉ S ∧ Good q) ∧
      (∀ x : V, (∀ q ∈ Q, L q x = 0) → x = 0) := by
  classical
  have hpoint : ∀ T : Finset Nat.Primes, ∀ x : V, x ≠ 0 →
      ∃ q, q ∉ T ∧ (q.val ∉ S ∧ Good q) ∧ L q x ≠ 0 := by
    intro T x hx
    obtain ⟨q, hq, hgood, hne⟩ := hdetect x hx (S ∪ T.image Subtype.val)
    have hq' := Finset.notMem_union.mp hq
    exact ⟨q, fun hqT => hq'.2 (Finset.mem_image.mpr ⟨q, hqT, rfl⟩),
      ⟨hq'.1, hgood⟩, hne⟩
  obtain ⟨Q, hcard, hQ, hzero⟩ := finite_detecting_family_of_pointwise L
    (fun q => q.val ∉ S ∧ Good q) hpoint ∅
  exact ⟨Q, hcard, fun q hq => (hQ q hq).2, hzero⟩

end
end Dubon2026
