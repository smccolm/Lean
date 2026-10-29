import Dubon2026.SourceGammaOneDegreeBaseChange
import Dubon2026.SourceGammaOneHeckeJDegree
import Dubon2026.SourceGammaOneExactRamification

/-! DUB-17/18 -> original Gamma1 Frobenius norm identity -> complete
embedding census -> actual Hecke field degree. Reuse the native Laurent
degree transport and the proved complex j-fiber degrees. The same two
original fields therefore have their signed subgroup indices over every
characteristic-zero coefficient field. This is not a residue-degree
preservation theorem.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
open scoped MatrixGroups

theorem coordinate_finrank_eq_relfinrank
    (Γ : Subgroup SL(2, ℤ)) (L : Type*) [Field L] [Algebra ℚ L] :
    Module.finrank (IntermediateField.adjoin L
      ({jCoordinateOver Γ L} : Set (functionFieldOver Γ L))) (functionFieldOver Γ L) =
      relfinrank (DegreeTransport.K L jq) (functionFieldOver Γ L) := by
  let F := functionFieldOver Γ L
  let B : IntermediateField L F := IntermediateField.adjoin L {jCoordinateOver Γ L}
  have hB : lift B = DegreeTransport.K L jq := lift_adjoin_simple L F (jCoordinateOver Γ L)
  have ht : lift (⊤ : IntermediateField L F) = F := lift_top L F
  have h := relfinrank_map_map B (⊤ : IntermediateField L F) F.val
  change relfinrank (lift B) (lift (⊤ : IntermediateField L F)) = _ at h
  rw [hB, ht, relfinrank_top_right] at h
  exact h.symm

theorem coordinate_relfinrank_baseChange
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (DegreeTransport.K L jq) (functionFieldOver Γ L) =
      relfinrank (DegreeTransport.K ℂ jq) (functionFieldOver Γ ℂ) := by
  letI := finite_rational_coordinate hT
  exact (DegreeTransport.relfinrank_eq_of_finite L
    (jq_mem_qExpFunctionField Γ) (transcendental_jqModC ℚ)).trans
      (DegreeTransport.relfinrank_eq_of_finite ℂ
        (jq_mem_qExpFunctionField Γ) (transcendental_jqModC ℚ)).symm

theorem gammaOne_coordinate_relfinrank_eq_index (M : ℕ) [NeZero M]
    (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (DegreeTransport.K L jq) (functionFieldOver (Gamma1 M) L) =
      (plusMinus (Gamma1 M)).index := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  rw [coordinate_relfinrank_baseChange _ hT L, ← coordinate_finrank_eq_relfinrank]
  exact finrank_over_j_eq_index M hT

theorem gammaOne_hecke_coordinate_relfinrank_eq_index (M d : ℕ) [NeZero M] [NeZero d]
    (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (DegreeTransport.K L jq) (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) L) =
      (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index := by
  have hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M) := by
    simp [Subgroup.mem_inf, Gamma1_mem, Gamma0_mem, ModularGroup.T]
  rw [coordinate_relfinrank_baseChange _ hT L, ← coordinate_finrank_eq_relfinrank]
  exact HeckeFiberOrbits.finrank_over_j_eq_index M d hT

end
end Dubon2026.SourceFunctionField.GammaOne
