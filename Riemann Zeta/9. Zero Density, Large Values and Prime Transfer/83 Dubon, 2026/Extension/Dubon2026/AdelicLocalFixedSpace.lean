import Dubon2026.AdelicLocalBoundedHecke
import Dubon2026.ClosedRepresentationInvariants

/-! # The genuine original local integral fixed Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual original local level-fixed Hilbert subspace. -/
def adelicLocalFixedSpace (v : HeightOneSpectrum ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  Representation.invariants ((adelicCyclicLocalRepresentation f v).comp (finitePlaceGL2Gamma0 N v).subtype)

/-- The actual local fixed space inherits the original complex Hilbert inner product. -/
instance adelicLocalFixedSpaceInnerProduct (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (adelicLocalFixedSpace f v) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalFixedSpace f v)

/-- Membership means the literal original fixed-vector equations for every actual local level matrix. -/
theorem mem_adelicLocalFixedSpace (v : HeightOneSpectrum ℤ) (x : AdelicCyclicHilbert f) :
    x ∈ adelicLocalFixedSpace f v ↔ ∀ g : finitePlaceGL2Gamma0 N v,
      adelicCyclicLocalRepresentation f v g.val x = x := Iff.rfl

/-- The original local level-fixed subspace is closed in its genuine ambient Hilbert topology. -/
theorem adelicLocalFixedSpace_isClosed (v : HeightOneSpectrum ℤ) :
    IsClosed (adelicLocalFixedSpace f v : Set (AdelicCyclicHilbert f)) :=
  @representation_invariants_isClosed (finitePlaceGL2Gamma0 N v) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance
    ((adelicCyclicLocalRepresentation f v).comp (finitePlaceGL2Gamma0 N v).subtype)
    (fun g => adelicCyclicLocalOperator f v g.val) (fun _ _ => rfl)

/-- The actual original local fixed space is a complete Hilbert subspace. -/
instance adelicLocalFixedSpace_complete (v : HeightOneSpectrum ℤ) :
    CompleteSpace (adelicLocalFixedSpace f v) :=
  (adelicLocalFixedSpace_isClosed f v).isComplete.completeSpace_coe

/-- The original cusp generator lies in its actual local fixed space, derived by genuine single-place level insertion. -/
theorem adelicCyclicHilbertGenerator_mem_localFixed (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicLocalFixedSpace f v := by
  intro g
  exact adelicCyclicHilbertGenerator_finite_level f ⟨_, finiteAdelicLocal_level_mem N v g⟩

end
end Dubon2026
