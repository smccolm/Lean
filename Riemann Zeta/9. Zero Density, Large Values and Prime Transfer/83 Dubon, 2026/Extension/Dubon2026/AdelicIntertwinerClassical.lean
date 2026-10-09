import Dubon2026.AdelicFixedLowestClassical

/-! # Actual full adelic intertwiners send the original generator to genuine classical cusp lifts -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Commutation with the original full group preserves its actual simultaneous rotation eigenspace. -/
theorem adelicIntertwiner_preserves_rotationWeight
    (A : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f g v) = adelicCyclicHilbertRepresentation f g (A v))
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRotationWeightSpace f) :
    A v ∈ adelicRotationWeightSpace f := by
  apply (mem_adelicRotationWeightSpace f _).mpr
  intro t
  rw [← hA, (mem_adelicRotationWeightSpace f v).mp hv t, map_smul]

/-- Commutation with the original finite-place subgroup preserves every actual fixed-level vector. -/
theorem adelicIntertwiner_preserves_level
    (A : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f g v) = adelicCyclicHilbertRepresentation f g (A v))
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicLevelFixedSpace f) :
    A v ∈ adelicLevelFixedSpace f := by
  apply (mem_adelicLevelFixedSpace f _).mpr
  intro a
  rw [← hA, (mem_adelicLevelFixedSpace f v).mp hv a]

/-- The image of the original cusp generator under every genuine bounded full-adelic intertwiner is the actual full lift of a unique original-level classical cusp form. -/
theorem adelicIntertwiner_generator_classical
    (hf : f ≠ 0) (hk : 0 < k)
    (A : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f g v) = adelicCyclicHilbertRepresentation f g (A v)) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f,
      adelicCyclicHilbertEmbedding f w = A (adelicCyclicHilbertGenerator f) ∧
      ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
        w.val = canonicalAdelicGL2CuspLift N k F :=
  adelicFixedLowest_classical_reconstruction f hf hk _
    (adelicIntertwiner_preserves_rotationWeight f A hA _
      (adelicCyclicHilbertGenerator_mem_rotationWeight f hf))
    (adelicIntertwiner_preserves_level f A hA _
      (adelicCyclicHilbertGenerator_finite_level f))

end
end Dubon2026
