import Dubon2026.SourcePrimePowerChainContradiction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> numerical modular genus -> all-level j-map degree.
Strong induction discharges every earlier-stage premise in the spread
embedding argument. Only the initial prime-series nonmembership in the
original level-M field remains; for M = 1 this is already proved.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section

theorem prime_power_next_not_mem_chain (M : ℕ) [NeZero M]
    (p : ℕ) [Fact p.Prime] (a : ℕ)
    (hbase : qExpand ℚ p jq ∉ modularFunctionFieldFull M) :
    qExpand ℚ (p ^ (a + 2)) jq ∉ chainField M p (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have hnot : ∀ i : ℕ, i ≤ a → qExpand ℚ (p ^ i * p) jq ∉ chainField M p i := by
      intro i hi
      rw [qExpand_congr (pow_succ p i).symm jq]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [chainField_zero, qExpand_congr (pow_one p) jq]
        exact hbase
      · have he : p ^ (i + 1) = p ^ (i - 1 + 2) := by congr 1; omega
        have hf : chainField M p i = chainField M p (i - 1 + 1) := by congr 1; omega
        rw [qExpand_congr he jq, hf]
        exact ih (i - 1) (by omega)
    let K := AlgebraicClosure ℚ
    haveI : NeZero ((M * p ^ (a + 2) : ℕ) : ℚ) :=
      ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (M * p ^ (a + 2))
    have hzu := hz.isUnit (NeZero.ne (M * p ^ (a + 2)))
    have hζ : IsPrimitiveRoot (hzu.unit : K) (M * p ^ (a + 2)) := by
      rw [hzu.unit_spec]
      exact hz
    exact chain_next_not_mem_of_earlier M p a hzu.unit hζ hnot

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
