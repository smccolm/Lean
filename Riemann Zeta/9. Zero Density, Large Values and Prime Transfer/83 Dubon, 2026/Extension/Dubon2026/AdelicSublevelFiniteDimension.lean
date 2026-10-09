import Dubon2026.AdelicSublevelClassicalFamily

/-! # Genuine fixed finite-adelic cores are finite dimensional at every finite-index sublevel -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine original fixed algebraic cores increase when the prescribed sublevel decreases. -/
theorem adelicAlgebraicSublevelFiniteSpan_antitone
    {L M : Subgroup (finiteAdeleGL2Gamma0 N)} (h : L ≤ M) :
    adelicAlgebraicSublevelFiniteSpan f M ≤ adelicAlgebraicSublevelFiniteSpan f L := by
  intro v hv
  exact ⟨hv.1, adelicSublevelFixedSpace_antitone f h hv.2⟩

/-- The actual finite-index normal core reduces arbitrary sublevels to the already proved genuine classical finite family. -/
theorem adelicAlgebraicSublevelFiniteSpan_finiteDimensional_of_finiteIndex
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.FiniteIndex] :
    FiniteDimensional ℂ (adelicAlgebraicSublevelFiniteSpan f L) := by
  have h := adelicAlgebraicSublevelFiniteSpan_antitone f L.normalCore_le
  let T : adelicAlgebraicSublevelFiniteSpan f L →ₗ[ℂ]
      adelicAlgebraicSublevelFiniteSpan f L.normalCore := Submodule.inclusion h
  have hT : Function.Injective T := Submodule.inclusion_injective h
  exact @FiniteDimensional.of_injective ℂ (adelicAlgebraicSublevelFiniteSpan f L)
    inferInstance inferInstance inferInstance (adelicAlgebraicSublevelFiniteSpan f L.normalCore)
    inferInstance inferInstance T hT inferInstance

/-- The original faithful Hilbert embedding identifies the actual fixed algebraic core with the genuine fixed finite-adelic Hilbert span. -/
theorem adelicAlgebraicSublevelFiniteSpan_map (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    (adelicAlgebraicSublevelFiniteSpan f L).map (adelicCyclicHilbertEmbedding f) =
      adelicFiniteCyclicSpan f ⊓ adelicSublevelFixedSpace f L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(adelicAlgebraicFiniteSpan_map f) ▸ (show adelicCyclicHilbertEmbedding f w ∈
      (adelicAlgebraicFiniteSpan f).map (adelicCyclicHilbertEmbedding f) from ⟨w, hw.1, rfl⟩), hw.2⟩
  · rintro ⟨hv, hl⟩
    obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hv
    refine ⟨w, ⟨hw, ?_⟩, he⟩
    change adelicCyclicHilbertEmbedding f w ∈ adelicSublevelFixedSpace f L
    rw [he]
    exact hl

/-- The actual finite-adelic Hilbert core fixed by any genuine finite-index sublevel is finite dimensional. -/
instance adelicSublevelFixedFiniteSpan_finiteDimensional
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.FiniteIndex] :
    FiniteDimensional ℂ ↥(adelicFiniteCyclicSpan f ⊓ adelicSublevelFixedSpace f L :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  letI := adelicAlgebraicSublevelFiniteSpan_finiteDimensional_of_finiteIndex f L
  rw [← adelicAlgebraicSublevelFiniteSpan_map f L]
  infer_instance

end
end Dubon2026
