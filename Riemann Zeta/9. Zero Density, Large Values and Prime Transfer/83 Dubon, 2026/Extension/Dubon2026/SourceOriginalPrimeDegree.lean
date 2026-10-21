import Dubon2026.SourceOriginalPrimeGeneration
import Dubon2026.SourcePrimeExactFieldDegree
import Dubon2026.SourceLevelPsi

/-! DUB-17/18 -> numerical modular genus -> original j-map degree.
The exact prime degree is transported to the literal internal j coordinate
of the original full field. The already proved arithmetic level factor
identifies this degree with dedekindPsi at prime level. Composite levels,
modular ramification and fiber counts remain required for numerical genus.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem finrank_original_over_j_prime (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    Module.finrank (IntermediateField.adjoin L
      ({jOver p L} : Set (modularFunctionFieldOver p L)))
      (modularFunctionFieldOver p L) = p + 1 := by
  let F := modularFunctionFieldOver p L
  let B₀ : IntermediateField L F := IntermediateField.adjoin L {jOver p L}
  let B := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
  let S := IntermediateField.adjoin B
    ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))
  have hF : F = S.restrictScalars L := original_prime_field_eq_simple_restrict p L
  have hB : lift B₀ = B := by
    exact lift_adjoin_simple L F (jOver p L)
  have htop : lift (⊤ : IntermediateField L F) = F := lift_top L F
  have hrel : relfinrank B F = Module.finrank B₀ F := by
    have h := relfinrank_map_map B₀ (⊤ : IntermediateField L F) F.val
    change relfinrank (lift B₀) (lift (⊤ : IntermediateField L F)) = _ at h
    rwa [hB, htop, relfinrank_top_right] at h
  have hle : B ≤ F := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (jOver p L).2
  have hs : extendScalars hle = S := by
    apply restrictScalars_injective L
    exact (extendScalars_restrictScalars hle).trans hF
  change Module.finrank B₀ F = p + 1
  rw [← hrel, relfinrank_eq_finrank_of_le hle, hs]
  exact prime_j_extension_finrank_eq L p

theorem finrank_original_over_j_prime_eq_psi (p : ℕ) [hp : Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    Module.finrank (IntermediateField.adjoin L
      ({jOver p L} : Set (modularFunctionFieldOver p L)))
      (modularFunctionFieldOver p L) = SourceLevelProjective.dedekindPsi p := by
  rw [finrank_original_over_j_prime]
  have h := SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out one_ne_zero
  simpa using h.symm

end
end Dubon2026.SourceFunctionField
