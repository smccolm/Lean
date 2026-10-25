import Dubon2026.SourceEllipticCharTwoCensusSum
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> characteristic-two genus/Picard -> weighted exceptional
census. Combine the actual cyclic action's local marks and global fixed counts
using the native finite-fiber sum. Finiteness comes from the existing exact
elliptic cyclic-subgroup cardinality. Only the actual place-classifier and
order identification remain inputs here; the modular consumer supplies them.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, characteristic-two census solution. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve MulAction SourceLevelProjective
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2] [IsAlgClosed K]
attribute [local instance] charTwoSignSubgroup_normal

theorem cyclic_order_census (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    {ι : Type*} [DecidableEq ι] (f : CyclicSubgroup K N → ι) (S : Finset ι) (ord : ι → ℤ)
    (hf1 : ∀ H, f H ∈ S) (hf2 : ∀ P ∈ S, ∃ H, f H = P)
    (horb : ∀ H T, f H = f T ↔
      T ∈ orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H)
    (he : ∀ H, ord (f H) =
      (Nat.card (orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H) : ℤ)) :
    (∀ P ∈ S, ord P = 1 ∨ ord P = 3 ∨ ord P = 4 ∨ ord P = 6 ∨ ord P = 12) ∧
    (S.filter fun P => ord P = 1).card + 3 * (S.filter fun P => ord P = 3).card +
      2 * (S.filter fun P => ord P = 6).card = nuTwo N ∧
    (S.filter fun P => ord P = 1).card + (S.filter fun P => ord P = 4).card = nuThree N := by
  classical
  letI : Fact (IsUnit (3 : K)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
  have hcard : Nat.card (CyclicSubgroup K N) = dedekindPsi N := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (F := K) (K := K) (ofJ0 K) hNK
  haveI : Finite (CyclicSubgroup K N) := Nat.finite_of_card_ne_zero
    (hcard.trans_ne (dedekindPsi_pos (NeZero.ne N)).ne')
  obtain ⟨hA₂, hA₃⟩ := char_two_cyclic_action_fixed_counts ω hω N hNK
  have h1 : ∀ P ∈ S, ord P = 1 ∨ ord P = 3 ∨ ord P = 4 ∨ ord P = 6 ∨ ord P = 12 := by
    intro P hP
    obtain ⟨H, rfl⟩ := hf2 P hP
    rw [he H]
    rcases (cyclic_orbit_marks ω hω H).1 with h | h | h | h | h <;> rw [h] <;> norm_num
  have h2 : ∑ P ∈ S, ((if ord P = 1 then 1 else 0) + (if ord P = 3 then 3 else 0) +
      (if ord P = 6 then 2 else 0)) = nuTwo N := by
    rw [← hA₂]
    apply fixed_cyclic_card_eq_sum _ f S hf1 hf2 horb
    intro H
    rw [he H]
    have hm := (cyclic_orbit_marks ω hω H).2.1
    exact_mod_cast hm
  have h3 : ∑ P ∈ S, ((if ord P = 1 then 1 else 0) + (if ord P = 4 then 1 else 0)) = nuThree N := by
    rw [← hA₃]
    apply fixed_cyclic_card_eq_sum _ f S hf1 hf2 horb
    intro H
    rw [he H]
    have hm := (cyclic_orbit_marks ω hω H).2.2
    exact_mod_cast hm
  refine ⟨h1, ?_, ?_⟩
  · rw [← h2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.card_filter,
      Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum]
    congr 1; congr 1
    · exact Finset.sum_congr rfl fun P _ => by split_ifs <;> rfl
    · exact Finset.sum_congr rfl fun P _ => by split_ifs <;> rfl
  · rw [← h3, Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]

end
end Dubon2026.SourceEllipticCharTwo
