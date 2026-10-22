import Dubon2026.SourceCuspConjugateDistinction
import Dubon2026.SourceLevelGenusNumerics

/-! DUB-17/18 -> numerical modular genus -> cusp count. Primitive cusp
labels use a divisor a and a reduced invertible phase modulo gcd(a,N/a).
Their count is the already defined arithmetic cuspCount. Each label is
an actual conjugate index. Reduction of arbitrary conjugate indices to
these labels will express total cusp width as the known conjugate count.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open ConjugateSlots

/-- Primitive divisor/phase labels for the original cusp family. -/
def labels (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  N.divisors.sigma fun a => (Finset.range (Nat.gcd a (N / a))).filter
    (fun b => Nat.Coprime (Nat.gcd a (N / a)) b)

theorem mem_labels (N : ℕ) [NeZero N] (s : Σ _ : ℕ, ℕ) :
    s ∈ labels N ↔ s.1 ∣ N ∧ s.2 < Nat.gcd s.1 (N / s.1) ∧
      Nat.Coprime (Nat.gcd s.1 (N / s.1)) s.2 := by
  rcases s with ⟨a, b⟩
  simp only [labels, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun ⟨⟨h1, _⟩, h2, h3⟩ => ⟨h1, h2, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨⟨h1, NeZero.ne N⟩, h2, h3⟩⟩

theorem label_mem_indices (N : ℕ) [NeZero N] (s : Σ _ : ℕ, ℕ) (hs : s ∈ labels N) :
    s ∈ indices N := by
  obtain ⟨ha, hb, hc⟩ := (mem_labels N s).mp hs
  have ha0 : 0 < s.1 := Nat.pos_of_ne_zero fun h =>
    NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  have hd0 : 0 < N / s.1 := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) ha) ha0
  exact (mem_indices N s.1 s.2).mpr ⟨ha, NeZero.ne N,
    lt_of_lt_of_le hb (Nat.gcd_le_right s.1 hd0), (slotCond_iff _ _ _).mpr hc⟩

theorem card_labels (N : ℕ) : (labels N).card = SourceLevelProjective.cuspCount N := by
  rw [labels, Finset.card_sigma, SourceLevelProjective.cuspCount]
  exact Finset.sum_congr rfl fun a _ => (Nat.totient_eq_card_coprime (Nat.gcd a (N / a))).symm

/-- Reduce a primitive conjugate phase to its cusp-label modulus. -/
def reduceLabel (N : ℕ) (s : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨s.1, s.2 % Nat.gcd s.1 (N / s.1)⟩

theorem reduceLabel_mem (N : ℕ) [NeZero N] (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    reduceLabel N s ∈ labels N := by
  obtain ⟨ha, _, _, hc⟩ := (mem_indices N s.1 s.2).mp hs
  have hg : 0 < Nat.gcd s.1 (N / s.1) :=
    Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (index_fst_ne_zero hs))
  rw [mem_labels]
  refine ⟨ha, Nat.mod_lt _ hg, ?_⟩
  change Nat.gcd (Nat.gcd s.1 (N / s.1)) (s.2 % Nat.gcd s.1 (N / s.1)) = 1
  rw [gcd_eq_of_modEq (Nat.mod_modEq s.2 (Nat.gcd s.1 (N / s.1)))]
  exact (slotCond_iff _ _ _).mp hc

end
end Dubon2026.SourceFunctionField.CuspLabels
