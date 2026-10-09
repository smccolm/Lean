import Dubon2026.AdelicClassicalReconstruction
import Dubon2026.ModularFiniteDimension

/-! # Finite dimensionality of the actual fixed-level finite-adelic core -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The original classical cusp space maps linearly to its literal real-group lifts. -/
def cuspRealWeightLiftLinear (N : ℕ) (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ] (SL(2, ℝ) → ℂ) where
  toFun F := realWeightLiftLinear k F
  map_add' F G := (realWeightLiftLinear k).map_add F G
  map_smul' c F := (realWeightLiftLinear k).map_smul c F

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual finite-adelic algebraic vectors whose original Hilbert images are fixed by the original finite level subgroup. -/
def adelicAlgebraicFixedFiniteSpan :
    Submodule ℂ (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  adelicAlgebraicFiniteSpan f ⊓ (adelicLevelFixedSpace f).comap (adelicCyclicHilbertEmbedding f)

/-- The original real restriction is faithful on the actual fixed-level finite-adelic core. -/
theorem adelicAlgebraicFixedFiniteSpan_restriction_injective :
    Function.Injective ((adelicCyclicRealRestriction f).domRestrict (adelicAlgebraicFixedFiniteSpan f)) := by
  intro v w he
  obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_classical_cusp f v.val v.property.1 v.property.2
  have ev := adelicCyclic_classical_reconstruction f v.val v.property.2 F hF
  have ew := adelicCyclic_classical_reconstruction f w.val w.property.2 F (hF.trans he)
  apply Subtype.ext
  apply Subtype.ext
  exact ev.trans ew.symm

/-- The original fixed finite-adelic core embeds in the genuine finite-dimensional original-level cusp space through its actual real lift. -/
instance adelicAlgebraicFixedFiniteSpan_finiteDimensional :
    FiniteDimensional ℂ (adelicAlgebraicFixedFiniteSpan f) := by
  letI := ModularDimension.cuspForm_finiteDimensional (Gamma0 N) k
  let T := (adelicCyclicRealRestriction f).domRestrict (adelicAlgebraicFixedFiniteSpan f)
  have hT (v : adelicAlgebraicFixedFiniteSpan f) : T v ∈ (cuspRealWeightLiftLinear N k).range := by
    obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_classical_cusp f v.val v.property.1 v.property.2
    exact ⟨F, hF⟩
  let U := T.codRestrict (cuspRealWeightLiftLinear N k).range hT
  have hU : Function.Injective U := by
    intro v w h
    exact adelicAlgebraicFixedFiniteSpan_restriction_injective f (congrArg Subtype.val h)
  exact FiniteDimensional.of_injective U hU

/-- The faithful original Hilbert embedding maps the actual fixed algebraic core onto the genuine fixed finite-adelic Hilbert span. -/
theorem adelicAlgebraicFixedFiniteSpan_map :
    (adelicAlgebraicFixedFiniteSpan f).map (adelicCyclicHilbertEmbedding f) =
      adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(adelicAlgebraicFiniteSpan_map f) ▸ (show adelicCyclicHilbertEmbedding f w ∈
      (adelicAlgebraicFiniteSpan f).map (adelicCyclicHilbertEmbedding f) from ⟨w, hw.1, rfl⟩), hw.2⟩
  · rintro ⟨hv, hl⟩
    obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hv
    refine ⟨w, ⟨hw, ?_⟩, he⟩
    change adelicCyclicHilbertEmbedding f w ∈ adelicLevelFixedSpace f
    rw [he]
    exact hl

/-- The actual fixed-level finite-adelic span in the original Hilbert space is finite dimensional. -/
instance adelicFixedFiniteSpan_finiteDimensional :
    FiniteDimensional ℂ ↥(adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f : Submodule ℂ (AdelicCyclicHilbert f)) := by
  rw [← adelicAlgebraicFixedFiniteSpan_map f]
  infer_instance

end
end Dubon2026
