import Dubon2026.AdelicCyclicHilbertGenerator

/-! # Actual scalar character and genuine finite stabilizers in the completed adelic representation -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open MeasureTheory UniformSpace
open scoped MatrixGroups

/-- The original adelic scalar acts trivially on every actual algebraic cyclic vector. -/
theorem adelicLiftCyclic_scalar_action (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (u : (AdeleRing ℤ ℚ)ˣ) (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation (GeneralLinearGroup.scalar (Fin 2) u) v = v := by
  apply Subtype.ext
  funext g
  change v.val (g * GeneralLinearGroup.scalar (Fin 2) u) = v.val g
  rw [← gl2Scalar_mul_comm]
  exact adelicLiftCyclic_scalar_invariant N f v.property u g

/-- The genuine completed original adelic representation has trivial full adelic scalar character. -/
theorem adelicCyclicHilbert_scalar_action {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (u : (AdeleRing ℤ ℚ)ˣ) (v : AdelicCyclicHilbert f) :
    adelicCyclicHilbertRepresentation f (GeneralLinearGroup.scalar (Fin 2) u) v = v := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (adelicCyclicHilbertOperator f _).continuous continuous_id
  | ih x =>
    obtain ⟨w, rfl⟩ := (adelicCyclicRangeEquiv f).surjective x
    change adelicCyclicHilbertRepresentation f _ (adelicCyclicHilbertEmbedding f w) = _
    rw [adelicCyclicHilbertEmbedding_intertwines, adelicLiftCyclic_scalar_action]
    rfl

/-- The original algebraic cusp generator is fixed by its actual embedded finite level group. -/
theorem adelicCyclicGenerator_finite_level (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (u : finiteAdeleGL2Gamma0 N) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation
      (rationalAdelicFiniteGL2Embedding u.val) (adelicCyclicGenerator N f) = adelicCyclicGenerator N f := by
  apply Subtype.ext
  funext g
  exact canonicalAdelicGL2CuspLift_level_invariant N f g u

/-- The actual completed original generator remains fixed by the genuine finite level subgroup. -/
theorem adelicCyclicHilbertGenerator_finite_level {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (u : finiteAdeleGL2Gamma0 N) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding u.val)
      (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f := by
  rw [adelicCyclicHilbertGenerator, adelicCyclicHilbertEmbedding_intertwines,
    adelicCyclicGenerator_finite_level]

/-- Each actual original vector in the dense completed cyclic core retains a genuine compact open finite stabilizer. -/
theorem adelicCyclicHilbert_finite_smooth_core {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    ∃ K : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)),
      IsCompact (K : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      IsOpen (K : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      ∀ a ∈ K, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertEmbedding f v) = adelicCyclicHilbertEmbedding f v := by
  obtain ⟨K, hKc, hKo, hK⟩ := adelicLiftCyclic_finite_smooth N f v.property
  refine ⟨K, hKc, hKo, ?_⟩
  intro a ha
  rw [adelicCyclicHilbertEmbedding_intertwines]
  apply congrArg (adelicCyclicHilbertEmbedding f)
  apply Subtype.ext
  funext g
  exact hK g a ha

end
end Dubon2026
