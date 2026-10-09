import Dubon2026.AdelicRealFiniteCoefficient
import Dubon2026.GramSpanningIsometry
import Dubon2026.TensorOrbitSpanning
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! # The genuine tensor of the original full real and full finite cyclic cores -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual full real orbit core of the original unit cusp reference, including both determinant components. -/
def adelicFullRealUnitCore : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun g : GeneralLinearGroup (Fin 2) ℝ =>
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicUnitReference f)))

/-- The actual full finite adelic orbit core of the original unit cusp reference. -/
def adelicFullFiniteUnitCore : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicUnitReference f)))

/-- The genuine real core retains the original Hilbert inner product. -/
instance adelicFullRealUnitCoreInner : InnerProductSpace ℂ (adelicFullRealUnitCore f) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance _

/-- The genuine finite core retains the original Hilbert inner product. -/
instance adelicFullFiniteUnitCoreInner : InnerProductSpace ℂ (adelicFullFiniteUnitCore f) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance _

/-- The actual original full real unit-reference orbit in its own original algebraic core. -/
def adelicFullRealUnitOrbit (g : GeneralLinearGroup (Fin 2) ℝ) : adelicFullRealUnitCore f :=
  ⟨adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicUnitReference f),
    Submodule.subset_span ⟨g, rfl⟩⟩

/-- The actual original full finite unit-reference orbit in its own original algebraic core. -/
def adelicFullFiniteUnitOrbit (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : adelicFullFiniteUnitCore f :=
  ⟨adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicUnitReference f),
    Submodule.subset_span ⟨a, rfl⟩⟩

/-- The actual real orbit spans the entire genuine real core. -/
theorem adelicFullRealUnitOrbit_span : Submodule.span ℂ (Set.range (adelicFullRealUnitOrbit f)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (adelicFullRealUnitCore f) _).mpr rfl

/-- The actual finite orbit spans the entire genuine finite core. -/
theorem adelicFullFiniteUnitOrbit_span : Submodule.span ℂ (Set.range (adelicFullFiniteUnitOrbit f)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (adelicFullFiniteUnitCore f) _).mpr rfl

/-- The genuine algebraic tensor of the original full real and finite orbit cores. -/
abbrev AdelicRealFiniteTensor := adelicFullRealUnitCore f ⊗[ℂ] adelicFullFiniteUnitCore f

/-- The actual tensor norm is the independent product norm from the original two factors. -/
instance adelicRealFiniteTensorNormed : NormedAddCommGroup (AdelicRealFiniteTensor f) :=
  @TensorProduct.instNormedAddCommGroup ℂ (adelicFullRealUnitCore f) (adelicFullFiniteUnitCore f)
    inferInstance inferInstance (adelicFullRealUnitCoreInner f) inferInstance (adelicFullFiniteUnitCoreInner f)

/-- The actual tensor inner product is the independent product inner product from the two original factors. -/
instance adelicRealFiniteTensorInner : InnerProductSpace ℂ (AdelicRealFiniteTensor f) :=
  @TensorProduct.instInnerProductSpace ℂ (adelicFullRealUnitCore f) (adelicFullFiniteUnitCore f)
    inferInstance inferInstance (adelicFullRealUnitCoreInner f) inferInstance (adelicFullFiniteUnitCoreInner f)

/-- The original pure real/finite orbit tensors. -/
def adelicRealFiniteTensorFamily
    (a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : AdelicRealFiniteTensor f :=
  adelicFullRealUnitOrbit f a.1 ⊗ₜ[ℂ] adelicFullFiniteUnitOrbit f a.2

/-- The genuine original joint real/finite unit-reference orbit. -/
def adelicRealFiniteMixedFamily
    (a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f (rationalAdelicGL2RealFiniteEquiv.symm a) (adelicCyclicUnitReference f)

/-- Genuine pure orbit tensors span the entire actual real/finite algebraic tensor. -/
theorem adelicRealFiniteTensorFamily_span : Submodule.span ℂ (Set.range (adelicRealFiniteTensorFamily f)) = ⊤ :=
  @tensorFamily_span_eq_top (GeneralLinearGroup (Fin 2) ℝ)
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicFullRealUnitCore f) (adelicFullFiniteUnitCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicFullRealUnitOrbit f) (adelicFullFiniteUnitOrbit f)
    (adelicFullRealUnitOrbit_span f) (adelicFullFiniteUnitOrbit_span f)

/-- The proved original coefficient factorization gives exactly the independently defined tensor Gram matrix. -/
theorem adelicRealFiniteTensorFamily_gram (hf : f ≠ 0) (hk : 0 < k)
    (a b : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    inner ℂ (adelicRealFiniteTensorFamily f a) (adelicRealFiniteTensorFamily f b) =
      inner ℂ (adelicRealFiniteMixedFamily f a) (adelicRealFiniteMixedFamily f b) := by
  exact (adelicCyclicUnitReference_realFinite_gram f hf hk a b).symm

/-- The genuine original real/finite tensor embeds isometrically into the actual cusp Hilbert space. -/
def adelicRealFiniteTensorIsometry (hf : f ≠ 0) (hk : 0 < k) :
    AdelicRealFiniteTensor f →ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  gramSpanningIsometry (adelicRealFiniteTensorFamily f) (adelicRealFiniteMixedFamily f)
    (adelicRealFiniteTensorFamily_gram f hf hk) (adelicRealFiniteTensorFamily_span f)

/-- The actual real/finite tensor map sends every genuine pure orbit tensor to its literal original mixed translate. -/
theorem adelicRealFiniteTensorIsometry_family (hf : f ≠ 0) (hk : 0 < k)
    (a : GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicRealFiniteTensorIsometry f hf hk (adelicRealFiniteTensorFamily f a) = adelicRealFiniteMixedFamily f a :=
  gramSpanningIsometry_family _ _ _ _ a

end
end Dubon2026
