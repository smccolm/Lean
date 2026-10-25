import Dubon2026.SourceEllipticCharTwoOrbitMarks

/-! DUB-17/18 -> characteristic-two weighted exceptional census. Sum the
fixed points over the actual cyclic-subgroup orbits using Mathlib's finite
fiber-cardinality theorem. This is exactly the two marked-element sum needed
by the source census; no additional group classification is developed. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve MulAction
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal

theorem fixed_cyclic_card_eq_sum {N : ℕ} [Finite (CyclicSubgroup K N)]
    {ι : Type*} [DecidableEq ι]
    (g : (stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)
    (f : CyclicSubgroup K N → ι) (S : Finset ι)
    (hf1 : ∀ H, f H ∈ S) (hf2 : ∀ P ∈ S, ∃ H, f H = P)
    (horb : ∀ H T, f H = f T ↔
      T ∈ orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H)
    (μ : ι → ℕ)
    (hμ : ∀ H, Nat.card (fixedBy
      (orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H) g) = μ (f H)) :
    ∑ P ∈ S, μ P = Nat.card (fixedBy (CyclicSubgroup K N) g) := by
  classical
  letI : Fintype (CyclicSubgroup K N) := Fintype.ofFinite _
  have hRHS : Nat.card (fixedBy (CyclicSubgroup K N) g) =
      (Finset.univ.filter fun H : CyclicSubgroup K N => g • H = H).card :=
    Nat.subtype_card _ (fun H => by simp [mem_fixedBy])
  rw [hRHS, Finset.card_eq_sum_card_fiberwise (t := S) (f := f) (fun H _ => hf1 H)]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨H, rfl⟩ := hf2 P hP
  rw [← hμ H]
  have he : Nat.card (fixedBy
      (orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H) g) =
      Nat.card {T : CyclicSubgroup K N //
        T ∈ orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H ∧ g • T = T} := by
    refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _))
    intro T
    rw [mem_fixedBy, Subtype.ext_iff, orbit.coe_smul]
  rw [he]
  refine Nat.subtype_card _ fun T => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← horb, eq_comm]
  tauto

end
end Dubon2026.SourceEllipticCharTwo
