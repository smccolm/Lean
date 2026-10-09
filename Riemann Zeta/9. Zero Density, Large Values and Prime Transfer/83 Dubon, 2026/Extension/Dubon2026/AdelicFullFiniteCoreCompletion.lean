import Dubon2026.AdelicFullFiniteAdmissible
import Dubon2026.IsometricRepresentationCompletion
import Dubon2026.FiniteHilbertTensor

/-! # Completion of the actual full finite algebraic core and its original admissible Hilbert factor -/

namespace Dubon2026

noncomputable section
open UniformSpace IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original finite unit-reference core with its explicitly inherited Hilbert structures. -/
def adelicFullFiniteInnerCarrier : ComplexInnerCarrier :=
  @ComplexInnerCarrier.of (adelicFullFiniteUnitCore f) inferInstance (adelicFullFiniteUnitCoreInner f)

/-- The genuine Hilbert completion of the original finite unit-reference cyclic core. -/
abbrev AdelicFullFiniteCoreCompletion := Completion (adelicFullFiniteInnerCarrier f)

/-- The original inherited finite-core inclusion extended continuously to its actual completion. -/
def adelicFullFiniteCoreCompletionInclusion :
    AdelicFullFiniteCoreCompletion f →ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  @linearIsometryCompletion (adelicFullFiniteUnitCore f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicFullFiniteUnitCore f).subtypeₗᵢ

/-- The actual finite-core completion has precisely the original lowest-weight Hilbert factor as its range. -/
theorem adelicFullFiniteCoreCompletionInclusion_range (hf : f ≠ 0) (hk : 0 < k) :
    (adelicFullFiniteCoreCompletionInclusion f).toLinearMap.range = adelicRotationWeightSpace f := by
  have he := @linearIsometryCompletion_range (adelicFullFiniteUnitCore f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicFullFiniteUnitCore f).subtypeₗᵢ
  have hr : (adelicFullFiniteUnitCore f).subtypeₗᵢ.toLinearMap.range = adelicFullFiniteUnitCore f :=
    Submodule.range_subtype _
  exact he.trans ((congrArg Submodule.topologicalClosure hr).trans
    (adelicFullFiniteUnitCore_closure_eq_weight f hf hk))

/-- The genuine finite-core completion is isometrically equivalent to its original admissible Hilbert factor. -/
def adelicFullFiniteCoreCompletionEquiv (hf : f ≠ 0) (hk : 0 < k) :
    AdelicFullFiniteCoreCompletion f ≃ₗᵢ[ℂ] adelicRotationWeightSpace f :=
  (adelicFullFiniteCoreCompletionInclusion f).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (adelicFullFiniteCoreCompletionInclusion_range f hf hk))

/-- The original algebraic finite representation preserves its actual inherited norm. -/
theorem adelicFullFiniteUnitCoreRepresentation_norm
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : adelicFullFiniteUnitCore f) :
    ‖adelicFullFiniteUnitCoreRepresentation f a x‖ = ‖x‖ :=
  adelicCyclicHilbertOperator_norm f (rationalAdelicFiniteGL2Embedding a) x.val

/-- The original finite-core action completed by its genuine continuous operators. -/
def adelicFullFiniteCoreCompletionRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (AdelicFullFiniteCoreCompletion f) :=
  isometricRepresentationCompletion (adelicFullFiniteUnitCoreRepresentation f)
    (adelicFullFiniteUnitCoreRepresentation_norm f)

/-- The actual completed inclusion is equivariant for the independently completed original finite action. -/
theorem adelicFullFiniteCoreCompletionInclusion_intertwines
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (x : AdelicFullFiniteCoreCompletion f) :
    adelicFullFiniteCoreCompletionInclusion f (adelicFullFiniteCoreCompletionRepresentation f a x) =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicFullFiniteCoreCompletionInclusion f x) :=
  @isometricRepresentationCompletion_intertwines
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicFullFiniteUnitCore f)
    inferInstance inferInstance inferInstance (adelicFullFiniteUnitCoreRepresentation f)
    (adelicFullFiniteUnitCoreRepresentation_norm f)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance (adelicFullFiniteUnitCore f).subtypeₗᵢ a
    (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a)) (fun _ => rfl) x

end
end Dubon2026
