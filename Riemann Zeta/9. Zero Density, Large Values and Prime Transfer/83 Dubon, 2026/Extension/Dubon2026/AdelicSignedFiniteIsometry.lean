import Dubon2026.AdelicRealFiniteClosureGram
import Dubon2026.AdelicIntegerWeightFiniteClosure
import Dubon2026.AdelicRealFiniteTensorAction

/-! # The actual finite cyclic representations of signed raising vectors have the original finite Gram matrix -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Each normalized original signed raising vector belongs to the actual full real Hilbert factor. -/
theorem adelicNormalizedSignedRaisingJet_mem_realClosure (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    adelicNormalizedSignedRaisingJet f i ∈ (adelicFullRealUnitCore f).topologicalClosure := by
  rw [← adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf]
  exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩))

/-- The genuine finite-adelic orbit of an original normalized signed raising vector. -/
def adelicSignedFiniteOrbit (i : ℕ ⊕ ℕ) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicNormalizedSignedRaisingJet f i)

/-- The finite orbits of every original normalized signed raising vector have exactly the original unit-reference Gram matrix. -/
theorem adelicSignedFiniteOrbit_gram (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    inner ℂ (adelicFullFiniteUnitOrbit f a) (adelicFullFiniteUnitOrbit f b) =
      inner ℂ (adelicSignedFiniteOrbit f i a) (adelicSignedFiniteOrbit f i b) := by
  have hx := adelicNormalizedSignedRaisingJet_mem_realClosure f hf i
  have he := adelicFullRealClosure_finite_gram f hf hk a b
    (adelicNormalizedSignedRaisingJet f i) (adelicNormalizedSignedRaisingJet f i) hx hx
  have hi : inner ℂ (adelicNormalizedSignedRaisingJet f i) (adelicNormalizedSignedRaisingJet f i) = 1 := by
    simpa only [ite_true] using
      (orthonormal_iff_ite.mp (adelicNormalizedSignedRaisingJet_orthonormal f hf hk)) i i
  rw [hi, one_mul] at he
  exact he.symm

/-- The actual finite cyclic core maps isometrically to the original signed raising-vector finite orbit span. -/
def adelicSignedFiniteCoreIsometry (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    adelicFullFiniteUnitCore f →ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  gramSpanningIsometry (adelicFullFiniteUnitOrbit f) (adelicSignedFiniteOrbit f i)
    (adelicSignedFiniteOrbit_gram f hf hk i) (adelicFullFiniteUnitOrbit_span f)

/-- The genuine signed finite isometry retains each prescribed original finite orbit vector. -/
theorem adelicSignedFiniteCoreIsometry_family (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicSignedFiniteCoreIsometry f hf hk i (adelicFullFiniteUnitOrbit f a) = adelicSignedFiniteOrbit f i a :=
  gramSpanningIsometry_family _ _ _ _ a

/-- The range of the actual signed finite-core isometry is precisely its original signed finite orbit span. -/
theorem adelicSignedFiniteCoreIsometry_range (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicSignedFiniteCoreIsometry f hf hk i).toLinearMap.range = Submodule.span ℂ (Set.range (adelicSignedFiniteOrbit f i)) :=
  gramSpanningIsometry_range _ _ _ _

/-- Normalizing the original signed vector leaves its actual finite cyclic algebraic span unchanged. -/
theorem adelicSignedFiniteOrbit_span (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    Submodule.span ℂ (Set.range (adelicSignedFiniteOrbit f i)) =
      Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
        adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicSignedRaisingJet f i))) := by
  have hn : ((‖adelicSignedRaisingJet f i‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr (adelicSignedRaisingJet_ne_zero f hf hk i))
  have he := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicSignedRaisingJet f i) (MulEquiv.refl _) _ hn
  change Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (((‖adelicSignedRaisingJet f i‖⁻¹ : ℝ) : ℂ) • adelicSignedRaisingJet f i))) = _
  simp only [map_smul]
  simpa only [MulEquiv.refl_apply, MonoidHom.comp_apply] using he

/-- The actual signed finite isometry has the entire original signed integer-character space as its closed range. -/
theorem adelicSignedFiniteCoreIsometry_range_closure (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicSignedFiniteCoreIsometry f hf hk i).toLinearMap.range.topologicalClosure =
      adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) := by
  rw [adelicSignedFiniteCoreIsometry_range, adelicSignedFiniteOrbit_span f hf hk i]
  exact (adelicIntegerRotationWeightSpace_eq_signedFiniteClosure f hf hk i).symm

end
end Dubon2026
