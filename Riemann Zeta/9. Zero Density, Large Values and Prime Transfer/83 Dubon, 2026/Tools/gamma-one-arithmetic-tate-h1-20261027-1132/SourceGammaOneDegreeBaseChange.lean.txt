import Dubon2026.SourceGammaOneFunctionFieldBaseChange

/-! DUB17/18 -> actual Gamma1 arithmetic Picard injectivity -> principal
descent -> corresponding coordinate bases. The existing Laurent degree
transport gives the same actual j-coordinate degree over Qbar and C.
Only the Gamma1 consumer is added; no coordinate degree is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem finrank_over_j_baseChange :
    Module.finrank (IntermediateField.adjoin L
      ({jCoordinateOver (Gamma1 N) L} : Set (functionFieldOver (Gamma1 N) L)))
      (functionFieldOver (Gamma1 N) L) =
    relfinrank (DegreeTransport.K₀ jq) (qExpFunctionFieldC ℚ (Gamma1 N)) := by
  let F := functionFieldOver (Gamma1 N) L
  let B : IntermediateField L F := IntermediateField.adjoin L {jCoordinateOver (Gamma1 N) L}
  have hB : lift B = DegreeTransport.K L jq :=
    lift_adjoin_simple L F (jCoordinateOver (Gamma1 N) L)
  have ht : lift (⊤ : IntermediateField L F) = F := lift_top L F
  have h := relfinrank_map_map B (⊤ : IntermediateField L F) F.val
  change relfinrank (lift B) (lift (⊤ : IntermediateField L F)) = _ at h
  rw [hB, ht, relfinrank_top_right] at h
  rw [← h]
  letI := finite_rational_coordinate (Γ := Gamma1 N)
    (by simp [Gamma1_mem, ModularGroup.T])
  exact DegreeTransport.relfinrank_eq_of_finite L
    (jq_mem_qExpFunctionField (Gamma1 N)) (transcendental_jqModC ℚ)

end
end Dubon2026.SourceFunctionField.GammaOne
