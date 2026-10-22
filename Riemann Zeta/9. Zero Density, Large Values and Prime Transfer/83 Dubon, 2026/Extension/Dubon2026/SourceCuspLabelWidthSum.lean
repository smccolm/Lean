import Dubon2026.SourceCuspPrimitiveLabels
import Mathlib.Data.Int.CardIntervalMod

/-! DUB-17/18 -> numerical modular genus -> exhaustiveness of the cusp
family. Reducing primitive conjugate indices to cusp labels has exactly
the proved cusp width as each fiber size. Native finite fiber counting
therefore shows that the sum of label widths is dedekindPsi(N), the
already proved total pole degree. This is the count needed to exclude
additional poles by positivity, without a separate place-extension proof.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open ConjugateSlots

theorem card_range_modEq {g d : ℕ} (hg : 0 < g) (hgd : g ∣ d) (b : ℕ) :
    ((Finset.range d).filter (fun x => Nat.ModEq g x b)).card = d / g := by
  obtain ⟨c, rfl⟩ := hgd
  have h := Nat.count_modEq_card (b := g * c) (r := g) hg b
  rw [Nat.count_eq_card_filter_range, Nat.mul_mod_right] at h
  simpa using h

theorem card_reduceLabel_fiber (N : ℕ) [NeZero N]
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ labels N) :
    ((indices N).filter (fun t => reduceLabel N t = s)).card =
      N / s.1 / Nat.gcd s.1 (N / s.1) := by
  obtain ⟨ha, hb, hc⟩ := (mem_labels N s).mp hs
  have ha0 := index_fst_ne_zero (label_mem_indices N s hs)
  let g := Nat.gcd s.1 (N / s.1)
  have hg : 0 < g := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left ha0)
  refine (Finset.card_nbij (fun b => (⟨s.1, b⟩ : Σ _ : ℕ, ℕ))
    (s := (Finset.range (N / s.1)).filter (fun b => Nat.ModEq g b s.2))
    (t := (indices N).filter (fun t => reduceLabel N t = s)) ?_ ?_ ?_).symm.trans
      (card_range_modEq hg (Nat.gcd_dvd_right _ _) s.2)
  · intro b hb'
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb'
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · apply (mem_indices N s.1 b).mpr
      refine ⟨ha, NeZero.ne N, hb'.1, ?_⟩
      rw [slotCond_iff]
      change Nat.gcd g b = 1
      rw [gcd_eq_of_modEq hb'.2]
      exact hc
    · change (⟨s.1, b % g⟩ : Σ _ : ℕ, ℕ) = s
      have he : b % g = s.2 := Eq.trans hb'.2 (Nat.mod_eq_of_lt hb)
      rw [he]
  · intro b _ b' _ he
    exact congrArg (fun t : Σ _ : ℕ, ℕ => t.2) he
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    have hat : t.1 = s.1 := by
      simpa only [reduceLabel] using congrArg (fun u : Σ _ : ℕ, ℕ => u.1) ht.2
    have hbt : t.2 % Nat.gcd t.1 (N / t.1) = s.2 :=
      congrArg (fun u : Σ _ : ℕ, ℕ => u.2) ht.2
    have ht' := (mem_indices N t.1 t.2).mp ht.1
    refine ⟨t.2, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨by rw [← hat]; exact ht'.2.2.1, ?_⟩
      change t.2 % g = s.2 % g
      rw [Nat.mod_eq_of_lt hb]
      simpa only [hat] using hbt
    · exact Sigma.ext hat.symm (heq_of_eq rfl)

theorem sum_label_widths (N : ℕ) [NeZero N] :
    (∑ s ∈ labels N, N / s.1 / Nat.gcd s.1 (N / s.1)) =
      SourceLevelProjective.dedekindPsi N := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := reduceLabel N) (s := indices N) (t := labels N)
    (fun s hs => reduceLabel_mem N s hs)
  rw [card_indices N (NeZero.ne N)] at h
  rw [h]
  exact Finset.sum_congr rfl fun s hs => (card_reduceLabel_fiber N s hs).symm

end
end Dubon2026.SourceFunctionField.CuspLabels
