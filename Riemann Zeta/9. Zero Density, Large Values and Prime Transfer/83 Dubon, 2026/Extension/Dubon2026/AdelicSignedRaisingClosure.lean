import Dubon2026.AdelicSignedRaisingFamily
import Dubon2026.AdelicRealFiniteTensor
import Dubon2026.AdelicLocalFullAwayTensorRange

/-! # The original full real cyclic Hilbert space is exactly the signed raising closure -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual closed span of both signed original raising families. -/
def adelicSignedRaisingClosedSpan : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (adelicSignedRaisingJet f))).topologicalClosure

/-- The full real core has exactly the same span for the original generator and its normalized reference. -/
theorem adelicFullRealUnitCore_eq_generatorSpan (hf : f ≠ 0) :
    adelicFullRealUnitCore f = Submodule.span ℂ (Set.range (fun g : GeneralLinearGroup (Fin 2) ℝ =>
      adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f))) := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) ℝ) (GeneralLinearGroup (Fin 2) ℝ)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealGL2Embedding)
    (adelicCyclicHilbertGenerator f) (MulEquiv.refl _) _ hn
  simpa only [adelicFullRealUnitCore, adelicCyclicUnitReference, map_smul,
    MulEquiv.refl_apply, MonoidHom.comp_apply] using he

/-- The original full real Hilbert closure is invariant under every original real general-linear matrix. -/
theorem adelicFullRealClosure_invariant (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) x ∈
      (adelicFullRealUnitCore f).topologicalClosure :=
  @closedCyclicSpan_invariant (GeneralLinearGroup (Fin 2) ℝ) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealGL2Embedding)
    (fun g => adelicCyclicHilbertOperator f (adelicRealGL2Embedding g)) (fun _ _ => rfl)
    (adelicCyclicUnitReference f) g x hx

/-- The original positive real component is contained in the actual full real Hilbert closure. -/
theorem adelicRealCyclic_le_fullRealClosure (hf : f ≠ 0) :
    adelicRealCyclicClosedSpan f ≤ (adelicFullRealUnitCore f).topologicalClosure := by
  rw [adelicRealCyclicClosedSpan, adelicFullRealUnitCore_eq_generatorSpan f hf]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact Submodule.subset_span ⟨toGL g, rfl⟩

/-- The positive original real component belongs to the signed raising closure. -/
theorem adelicRealCyclic_le_signedRaisingClosure (hf : f ≠ 0) :
    adelicRealCyclicClosedSpan f ≤ adelicSignedRaisingClosedSpan f := by
  rw [← adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact Submodule.subset_span ⟨Sum.inl n, rfl⟩

/-- Reflecting the whole original positive real component stays in the genuine signed raising closure. -/
theorem adelicReflectedReal_mem_signedRaisingClosure (hf : f ≠ 0)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicRealCyclicClosedSpan f) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)) x ∈
      adelicSignedRaisingClosedSpan f := by
  rw [← adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf] at hx
  let T := adelicCyclicHilbertOperator f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection))
  have hs : Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) ≤
      (adelicSignedRaisingClosedSpan f).comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Sum.inr n, rfl⟩)
  exact closure_minimal hs
    ((Submodule.isClosed_topologicalClosure _).preimage T.continuous) hx

/-- Every genuine real determinant component of the original generator lies in the signed raising closure. -/
theorem adelicFullRealOrbit_mem_signedRaisingClosure (hf : f ≠ 0)
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f) ∈
      adelicSignedRaisingClosedSpan f := by
  by_cases hg : g ∈ GLPos (Fin 2) ℝ
  · rw [adelicCyclicHilbert_positive_normalize f (⟨g, hg⟩ : GL(2, ℝ)⁺)]
    exact adelicRealCyclic_le_signedRaisingClosure f hf
      (adelicRealCyclicClosedSpan_orbit_mem f (realPositiveNormalize ⟨g, hg⟩))
  · change ¬0 < (GeneralLinearGroup.det g).val at hg
    have he : g = rationalGL2ToReal rationalGL2Reflection * (realGL2PositivePart g).val := by
      change g = rationalGL2ToReal rationalGL2Reflection *
        ((rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g)
      rw [realGL2RationalSign, if_neg hg]
      simp only [mul_inv_cancel_left]
    rw [he, map_mul, map_mul, Module.End.mul_apply,
      adelicCyclicHilbert_positive_normalize f (realGL2PositivePart g)]
    exact adelicReflectedReal_mem_signedRaisingClosure f hf _
      (adelicRealCyclicClosedSpan_orbit_mem f (realPositiveNormalize (realGL2PositivePart g)))

/-- The closure of the actual full real factor is precisely the closed span of both original signed raising families. -/
theorem adelicSignedRaisingClosedSpan_eq_fullRealClosure (hf : f ≠ 0) :
    adelicSignedRaisingClosedSpan f = (adelicFullRealUnitCore f).topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl n => exact adelicRealCyclic_le_fullRealClosure f hf (adelicRaisingJet_mem_realCyclicClosedSpan f n)
      | inr n =>
        exact adelicFullRealClosure_invariant f _ _
          (adelicRealCyclic_le_fullRealClosure f hf (adelicRaisingJet_mem_realCyclicClosedSpan f n))
    · exact Submodule.isClosed_topologicalClosure _
  · rw [adelicFullRealUnitCore_eq_generatorSpan f hf]
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact adelicFullRealOrbit_mem_signedRaisingClosure f hf g
    · exact Submodule.isClosed_topologicalClosure _

end
end Dubon2026
