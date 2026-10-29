import Dubon2026.SourceGammaOneAdjacentJNonmembership
import Dubon2026.SourceGammaOneHeckePrimeDegree
import Dubon2026.SourceRationalPrimeStepDegree
import Dubon2026.SourcePrimePowerRelativeStep

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> explicit embedding
census. The proved adjacent-j nonmembership feeds the existing rational
prime-step theorem. Comparing that degree with the actual correspondence
degree proves equality with the simple extension, without a supplied
generator or scalar-extension hypothesis. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
open scoped MatrixGroups

theorem gammaOne_adjacentJ_finrank (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcop : Nat.Coprime M p) :
    Module.finrank (x1FunctionField M) (IntermediateField.adjoin (x1FunctionField M)
      ({qExpand ℚ p jq} : Set (LaurentSeries ℚ))) = p + 1 :=
  rational_prime_step_finrank_eq_of_not_mem (x1FunctionField M)
    (jq_mem_qExpFunctionField (Gamma1 M)) p (prime_j_not_mem_gammaOne M p hcop)

theorem gammaOne_adjacentJ_generation (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcop : Nat.Coprime M p) :
    x1x0FunctionFieldC ℚ M (p * M) = IntermediateField.adjoin ℚ
      ((x1FunctionField M : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ p jq}) := by
  let F := x1FunctionField M
  let G := x1x0FunctionFieldC ℚ M (p * M)
  let S := IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ p jq})
  have hFS : F ≤ S := fun _ hx => subset_adjoin ℚ _ (Or.inl hx)
  have hFG : F ≤ G := x1FunctionFieldC_le_x1x0 ℚ M (p * M)
  have hjG : qExpand ℚ p jq ∈ G := gamma1_degeneracy_map_le ℚ M p
    ⟨jq, jq_mem_qExpFunctionField (Gamma1 M), rfl⟩
  have hSG : S ≤ G := adjoin_le_iff.mpr (by
    rintro z (hz | hz)
    · exact hFG hz
    · rcases hz with rfl
      exact hjG)
  have hdegree : relfinrank F G = p + 1 := by
    have h := gammaOne_over_prime_relfinrank ℚ M p hcop.symm
    change relfinrank (laurentBaseChange ℚ F) (laurentBaseChange ℚ G) = p + 1 at h
    rwa [laurentBaseChange_rat, laurentBaseChange_rat] at h
  have hsimple : relfinrank F S = p + 1 := by
    rw [relfinrank_adjoin_union_singleton]
    exact gammaOne_adjacentJ_finrank M p hcop
  have hmul := relfinrank_mul_relfinrank hFS hSG
  rw [hsimple, hdegree] at hmul
  have hlast : relfinrank S G = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos p) (by simpa only [Nat.mul_one] using hmul)
  exact le_antisymm (relfinrank_eq_one_iff.mp hlast) hSG

end
end Dubon2026.SourceFunctionField.GammaOne
