import Dubon2026.SourceCuspClassification
import Dubon2026.SourceLevelGenusNumerics

/-! DUB-17/18 -> parabolic Hecke realization -> matching period dimensions
-> exact arithmetic genus bound -> count of original rational cusp orbits.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount.lean.
The quotient and its level action are the previously proved SourceManin
objects. Cusp widths and unrelated geometric infrastructure are omitted.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups

namespace CuspSpace
open SourceLevelProjective
open Finset

variable {N : ℕ}

theorem card_sigma_units :
    Nat.card ((d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ) = cuspCount N := by
  have hgcd : ∀ d : N.divisors, NeZero (Nat.gcd (d : ℕ) (N / (d : ℕ))) := by
    rintro ⟨d, hd⟩
    rw [Nat.mem_divisors] at hd
    exact ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero
      (fun h => hd.2 (Nat.eq_zero_of_zero_dvd (h ▸ hd.1))))).ne'⟩
  rw [Nat.card_sigma]
  simp only [cuspCount]
  rw [← Finset.sum_attach N.divisors fun d => Nat.totient (Nat.gcd d (N / d)),
    ← Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := hgcd d
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem card_eq_cuspCount_of_classification (hcl : Classification N) :
    Nat.card (CuspSpace N) = cuspCount N := by
  obtain ⟨e⟩ := hcl
  rw [Nat.card_congr e, card_sigma_units]

theorem card_cuspSpace_eq_cuspCount {N : ℕ} (hN : N ≠ 0) :
    Nat.card (Dubon2026.SourceManin.CuspSpace N) = SourceLevelProjective.cuspCount N :=
  Dubon2026.SourceManin.CuspSpace.card_eq_cuspCount_of_classification (Dubon2026.SourceManin.CuspSpace.classification hN)

end CuspSpace

end
end Dubon2026.SourceManin
