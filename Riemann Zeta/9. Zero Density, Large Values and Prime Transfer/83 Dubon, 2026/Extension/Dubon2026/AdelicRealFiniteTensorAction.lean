import Dubon2026.AdelicRealFiniteTensor
import Dubon2026.AdelicLocalFullAwayTensorAction

/-! # Independent external real/finite action and its actual original tensor intertwiner -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original real action preserves its actual normalized real orbit core. -/
theorem adelicFullRealUnitCore_invariant (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFullRealUnitCore f) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) x ∈ adelicFullRealUnitCore f :=
  @representationOrbitSpan_invariant (GeneralLinearGroup (Fin 2) ℝ) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealGL2Embedding) (adelicCyclicUnitReference f) g x hx

/-- The original finite action preserves its actual normalized finite orbit core. -/
theorem adelicFullFiniteUnitCore_invariant (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFullFiniteUnitCore f) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x ∈ adelicFullFiniteUnitCore f :=
  @representationOrbitSpan_invariant (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) (adelicCyclicUnitReference f) a x hx

/-- The actual original full real action on its genuine algebraic orbit core. -/
def adelicFullRealUnitCoreRepresentation : Representation ℂ (GeneralLinearGroup (Fin 2) ℝ) (adelicFullRealUnitCore f) :=
  Representation.subrepresentation ((adelicCyclicHilbertRepresentation f).comp adelicRealGL2Embedding)
    (adelicFullRealUnitCore f) (adelicFullRealUnitCore_invariant f)

/-- The actual original full finite action on its genuine algebraic orbit core. -/
def adelicFullFiniteUnitCoreRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicFullFiniteUnitCore f) :=
  Representation.subrepresentation ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicFullFiniteUnitCore f) (adelicFullFiniteUnitCore_invariant f)

/-- The actual original real core action multiplies the genuine real orbit coordinate. -/
theorem adelicFullRealUnitOrbit_action (g h : GeneralLinearGroup (Fin 2) ℝ) :
    adelicFullRealUnitCoreRepresentation f g (adelicFullRealUnitOrbit f h) = adelicFullRealUnitOrbit f (g * h) := by
  apply Subtype.ext
  exact (representation_hom_mul_apply (adelicCyclicHilbertRepresentation f) adelicRealGL2Embedding g h
    (adelicCyclicUnitReference f)).symm

/-- The actual original finite core action multiplies the genuine finite orbit coordinate. -/
theorem adelicFullFiniteUnitOrbit_action (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicFullFiniteUnitCoreRepresentation f a (adelicFullFiniteUnitOrbit f b) = adelicFullFiniteUnitOrbit f (a * b) := by
  apply Subtype.ext
  exact (representation_hom_mul_apply (adelicCyclicHilbertRepresentation f) rationalAdelicFiniteGL2Embedding a b
    (adelicCyclicUnitReference f)).symm

/-- The independently constructed external tensor action of the original real and finite core representations. -/
def adelicRealFiniteTensorRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
      (AdelicRealFiniteTensor f) :=
  Representation.tprod ((adelicFullRealUnitCoreRepresentation f).comp (MonoidHom.fst _ _))
    ((adelicFullFiniteUnitCoreRepresentation f).comp (MonoidHom.snd _ _))

/-- The true external tensor action transforms its original pure orbit family by coordinate multiplication. -/
theorem adelicRealFiniteTensorFamily_action
    (b a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicRealFiniteTensorRepresentation f b (adelicRealFiniteTensorFamily f a) =
      adelicRealFiniteTensorFamily f (b * a) := by
  change TensorProduct.map (adelicFullRealUnitCoreRepresentation f b.1) (adelicFullFiniteUnitCoreRepresentation f b.2)
    (adelicFullRealUnitOrbit f a.1 ⊗ₜ[ℂ] adelicFullFiniteUnitOrbit f a.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
    (adelicFullRealUnitOrbit_action f b.1 a.1) (adelicFullFiniteUnitOrbit_action f b.2 a.2)

/-- The original full adelic action expressed in its actual real/finite coordinates. -/
def adelicRealFiniteJointRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom

/-- The original real/finite mixed family transforms under the actual full original adelic action. -/
theorem adelicRealFiniteMixedFamily_action
    (b a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicRealFiniteJointRepresentation f b (adelicRealFiniteMixedFamily f a) =
      adelicRealFiniteMixedFamily f (b * a) :=
  (representation_hom_mul_apply (adelicCyclicHilbertRepresentation f)
    rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom b a (adelicCyclicUnitReference f)).symm

/-- The genuine original tensor isometry intertwines the independently constructed external action on every real/finite tensor vector. -/
theorem adelicRealFiniteTensorIsometry_intertwines (hf : f ≠ 0) (hk : 0 < k)
    (b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (x : AdelicRealFiniteTensor f) :
    adelicRealFiniteTensorIsometry f hf hk (adelicRealFiniteTensorRepresentation f b x) =
      adelicRealFiniteJointRepresentation f b (adelicRealFiniteTensorIsometry f hf hk x) :=
  @linearMap_intertwines_of_spanning_family
    (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicRealFiniteTensor f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicRealFiniteTensorRepresentation f) (adelicRealFiniteJointRepresentation f)
    (adelicRealFiniteTensorIsometry f hf hk).toLinearMap
    (adelicRealFiniteTensorFamily f) (adelicRealFiniteMixedFamily f)
    (adelicRealFiniteTensorFamily_span f) (adelicRealFiniteTensorIsometry_family f hf hk)
    (adelicRealFiniteTensorFamily_action f) (adelicRealFiniteMixedFamily_action f) b x

end
end Dubon2026
