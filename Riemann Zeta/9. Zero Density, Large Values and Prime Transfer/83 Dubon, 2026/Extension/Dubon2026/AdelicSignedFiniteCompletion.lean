import Dubon2026.AdelicSignedFiniteAction
import Dubon2026.AdelicFullFiniteCoreCompletion

/-! # The original finite Hilbert factor realized at every actual signed real weight -/

namespace Dubon2026

noncomputable section
open UniformSpace IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Completion of the genuine original finite-core isometry into an actual signed real-character space. -/
def adelicSignedFiniteCompletionIsometry (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    AdelicFullFiniteCoreCompletion f →ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  @linearIsometryCompletion (adelicFullFiniteUnitCore f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicSignedFiniteCoreIsometry f hf hk i)

/-- The actual completed signed isometry has precisely the entire original signed global weight space as its range. -/
theorem adelicSignedFiniteCompletionIsometry_range (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicSignedFiniteCompletionIsometry f hf hk i).toLinearMap.range =
      adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) :=
  (@linearIsometryCompletion_range (adelicFullFiniteUnitCore f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicSignedFiniteCoreIsometry f hf hk i)).trans
    (adelicSignedFiniteCoreIsometry_range_closure f hf hk i)

/-- The actual original finite-core completion is isometrically equivalent to each entire original signed real-character space. -/
def adelicSignedFiniteCompletionEquiv (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    AdelicFullFiniteCoreCompletion f ≃ₗᵢ[ℂ] adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) :=
  (adelicSignedFiniteCompletionIsometry f hf hk i).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (adelicSignedFiniteCompletionIsometry_range f hf hk i))

/-- The genuine completed signed isometry intertwines every actual finite-adelic action. -/
theorem adelicSignedFiniteCompletionIsometry_intertwines (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicFullFiniteCoreCompletion f) :
    adelicSignedFiniteCompletionIsometry f hf hk i (adelicFullFiniteCoreCompletionRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicSignedFiniteCompletionIsometry f hf hk i x) :=
  @isometricRepresentationCompletion_intertwines
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicFullFiniteUnitCore f)
    inferInstance inferInstance inferInstance (adelicFullFiniteUnitCoreRepresentation f)
    (adelicFullFiniteUnitCoreRepresentation_norm f)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance (adelicSignedFiniteCoreIsometry f hf hk i) a
    (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a))
    (adelicSignedFiniteCoreIsometry_intertwines f hf hk i a) x

end
end Dubon2026
