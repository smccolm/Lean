import TaoTrudgianYang2025.SargosPrefixFourthMajorant
import Mathlib.Topology.Order.Lattice

/-! The actual finite maximum over every prefix, with an attained endpoint. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosFinitePrefixMaximum {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  (Finset.range (N+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
    (fun H => ‖sargosFinitePrefix f H‖)

theorem sargosFinitePrefixMaximum_attained {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∃ H : ℕ, H ≤ N ∧ sargosFinitePrefixMaximum f = ‖sargosFinitePrefix f H‖ := by
  obtain ⟨H,hH,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N)) (fun H => ‖sargosFinitePrefix f H‖)
  exact ⟨H,Nat.le_of_lt_succ (Finset.mem_range.mp hH),he⟩

theorem sargosFinitePrefixMaximum_nonneg {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    0 ≤ sargosFinitePrefixMaximum f := by
  obtain ⟨H,hH,he⟩ := sargosFinitePrefixMaximum_attained f
  rw [he]
  exact norm_nonneg _

theorem norm_sargosFinitePrefix_le_maximum {N H : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖ ≤ sargosFinitePrefixMaximum f := by
  exact Finset.le_sup' (fun H => ‖sargosFinitePrefix f H‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hH))

theorem sargosFinitePrefixMaximum_pow_four_le {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) :
    (sargosFinitePrefixMaximum f)^4 ≤ sargosFourierFourthMajorant f := by
  obtain ⟨H,hH,he⟩ := sargosFinitePrefixMaximum_attained f
  rw [he]
  exact norm_sargosFinitePrefix_pow_four_le f hH

theorem continuous_sargosFinitePrefixMaximum {X : Type*} [TopologicalSpace X]
    {N : ℕ} [NeZero N] (f : X → ZMod N → ℂ)
    (hf : ∀ k, Continuous (fun x => f x k)) :
    Continuous (fun x => sargosFinitePrefixMaximum (f x)) := by
  unfold sargosFinitePrefixMaximum
  apply Continuous.finset_sup'_apply
  intro H hH
  unfold sargosFinitePrefix
  exact (continuous_finsetSum _ (fun j hj => hf _)).norm

end TaoTrudgianYang2025
