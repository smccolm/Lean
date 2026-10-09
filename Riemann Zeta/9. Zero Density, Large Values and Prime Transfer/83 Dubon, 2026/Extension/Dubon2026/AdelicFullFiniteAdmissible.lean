import Dubon2026.AdelicRealFiniteTensorAction
import Dubon2026.AdelicFiniteOpenLowestAdmissible
import Dubon2026.AdelicFiniteLowestClosure

/-! # Admissibility of the actual full finite adelic factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original normalized finite orbit core lies in the actual lowest-weight Hilbert space. -/
theorem adelicFullFiniteUnitCore_le_weight (hf : f ≠ 0) :
    adelicFullFiniteUnitCore f ≤ adelicRotationWeightSpace f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply adelicRotationWeightSpace_finite_invariant f a
  exact (adelicRotationWeightSpace f).smul_mem _ (adelicCyclicHilbertGenerator_mem_rotationWeight f hf)

/-- Normalizing the original generator does not alter its actual finite adelic cyclic closure. -/
theorem adelicFullFiniteUnitCore_closure (hf : f ≠ 0) :
    (adelicFullFiniteUnitCore f).topologicalClosure = adelicFiniteCyclicClosedSpan f := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicCyclicHilbertGenerator f) (MulEquiv.refl _) _ hn
  have hs : adelicFullFiniteUnitCore f = Submodule.span ℂ (Set.range
      (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
        adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicHilbertGenerator f))) := by
    simpa only [adelicFullFiniteUnitCore, adelicCyclicUnitReference, map_smul, MulEquiv.refl_apply,
      MonoidHom.comp_apply] using he
  exact congrArg Submodule.topologicalClosure hs

/-- The genuine finite tensor factor has precisely the original lowest-weight Hilbert space as its completion inside the original representation. -/
theorem adelicFullFiniteUnitCore_closure_eq_weight (hf : f ≠ 0) (hk : 0 < k) :
    (adelicFullFiniteUnitCore f).topologicalClosure = adelicRotationWeightSpace f :=
  (adelicFullFiniteUnitCore_closure f hf).trans (adelicRotationWeightSpace_eq_finiteClosure f hf hk).symm

/-- The actual full finite adelic representation on the original complete lowest-weight Hilbert space. -/
def adelicFullFiniteHilbertRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicRotationWeightSpace f) :=
  Representation.subrepresentation ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicRotationWeightSpace f) (adelicRotationWeightSpace_finite_invariant f)

/-- Every original open finite adelic subgroup has finite-dimensional fixed vectors in the genuine full finite cyclic core. -/
theorem adelicFullFiniteUnitCoreRepresentation_admissible (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicFullFiniteUnitCoreRepresentation f).comp J.subtype)) := by
  letI := adelicFiniteOpenLowest_finiteDimensional f hf hk J hJ
  let T : Representation.invariants ((adelicFullFiniteUnitCoreRepresentation f).comp J.subtype) →ₗ[ℂ]
      (adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J : Submodule ℂ (AdelicCyclicHilbert f)) := {
    toFun := fun x => ⟨x.val.val, ⟨adelicFullFiniteUnitCore_le_weight f hf x.val.property,
      fun g => congrArg Subtype.val (x.property g)⟩⟩
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }
  have hT : Function.Injective T := by
    intro x y he
    have h := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext h)
  exact FiniteDimensional.of_injective T hT

/-- Every original open finite adelic subgroup has finite-dimensional fixed vectors in the full genuine finite Hilbert factor. -/
theorem adelicFullFiniteHilbertRepresentation_admissible (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (Representation.invariants ((adelicFullFiniteHilbertRepresentation f).comp J.subtype)) := by
  letI := adelicFiniteOpenLowest_finiteDimensional f hf hk J hJ
  let T : Representation.invariants ((adelicFullFiniteHilbertRepresentation f).comp J.subtype) →ₗ[ℂ]
      (adelicRotationWeightSpace f ⊓ adelicFiniteSubgroupFixedSpace f J : Submodule ℂ (AdelicCyclicHilbert f)) := {
    toFun := fun x => ⟨x.val.val, ⟨x.val.property, fun g => congrArg Subtype.val (x.property g)⟩⟩
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }
  have hT : Function.Injective T := by
    intro x y he
    have h := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext h)
  exact FiniteDimensional.of_injective T hT

end
end Dubon2026
