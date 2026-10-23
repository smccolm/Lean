import Dubon2026.SourceCurveCompletionIntegrality
import Dubon2026.SourceCurveCompletionSeparable
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! The actual integral basis needed for local residue/field-trace
compatibility. Spectral integrality, original separability and the native
finite integral-closure theorem give finite freeness. Localizing that
literal integral basis gives a field basis whose integral coordinates are
exactly the completed valuation ring. No integral basis is postulated. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E) [FiniteDimensional F E]
  [Algebra.IsSeparable F E]

/-- An actual field basis of the completion that exactly detects its valuation ring. -/
structure CompletionIntegralBasis where
  /-- The field basis, indexed by the actual local extension degree. -/
  basis : Module.Basis (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion))
    (w.restrict F).adicCompletion w.adicCompletion
  /-- Every basis element belongs to the actual completed valuation ring. -/
  basis_mem : ∀ i, basis i ∈ w.adicCompletionIntegers
  /-- Membership in that ring is equivalent to integrality of every coordinate. -/
  mem_iff : ∀ y, y ∈ w.adicCompletionIntegers ↔
    ∀ i, basis.repr y i ∈ (w.restrict F).adicCompletionIntegers

/-- The actual completed extension integers form a finite free module over the base integers. -/
theorem completionIntegers_finite_free :
    Module.Finite (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers ∧
      Module.Free (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers := by
  haveI := w.finiteDimensional_completion (F := F)
  haveI := w.isSeparable_completion (F := F)
  haveI := w.isIntegralClosure_completionIntegers (F := F)
  haveI : IsDiscreteValuationRing (w.restrict F).adicCompletionIntegers :=
    inferInstanceAs (IsDiscreteValuationRing (w.restrict F).completionPlace.toValuationSubring)
  haveI : Module.Finite (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers :=
    IsIntegralClosure.finite (w.restrict F).adicCompletionIntegers
      (w.restrict F).adicCompletion w.adicCompletion w.adicCompletionIntegers
  haveI := w.torsionFree_completionIntegers (F := F)
  exact ⟨inferInstance, Module.free_of_finite_type_torsion_free'⟩

omit [Algebra.IsSeparable F E] in
/-- The literal extension integral ring localizes to its actual completed field. -/
theorem completionIntegers_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid w.adicCompletionIntegers
      (nonZeroDivisors (w.restrict F).adicCompletionIntegers)) w.adicCompletion := by
  haveI := w.finiteDimensional_completion (F := F)
  haveI := w.isIntegralClosure_completionIntegers (F := F)
  exact IsIntegralClosure.isLocalization (w.restrict F).adicCompletionIntegers
    (w.restrict F).adicCompletion w.adicCompletion w.adicCompletionIntegers

/-- A constructed completed field basis detects integrality coefficient by coefficient. -/
theorem exists_completion_integral_basis :
    ∃ b : Module.Basis (Fin (Module.finrank (w.restrict F).adicCompletion w.adicCompletion))
      (w.restrict F).adicCompletion w.adicCompletion,
      (∀ i, b i ∈ w.adicCompletionIntegers) ∧
      ∀ y, y ∈ w.adicCompletionIntegers ↔
        ∀ i, b.repr y i ∈ (w.restrict F).adicCompletionIntegers := by
  classical
  haveI : IsDiscreteValuationRing (w.restrict F).adicCompletionIntegers :=
    inferInstanceAs (IsDiscreteValuationRing (w.restrict F).completionPlace.toValuationSubring)
  haveI := w.finiteDimensional_completion (F := F)
  haveI := w.isSeparable_completion (F := F)
  haveI := w.isIntegralClosure_completionIntegers (F := F)
  haveI := w.completionIntegers_isLocalization (F := F)
  haveI : Module.IsTorsionFree (w.restrict F).adicCompletionIntegers w.adicCompletion :=
    .trans_faithfulSMul (w.restrict F).adicCompletionIntegers (w.restrict F).adicCompletion
      w.adicCompletion
  obtain ⟨hfin, hfree⟩ := w.completionIntegers_finite_free (F := F)
  haveI := hfin
  haveI := hfree
  let c := Module.finBasis (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers
  let c' := c.localizationLocalization (w.restrict F).adicCompletion
    (nonZeroDivisors (w.restrict F).adicCompletionIntegers) w.adicCompletion
  have hrank : Module.finrank (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers =
      Module.finrank (w.restrict F).adicCompletion w.adicCompletion :=
    IsIntegralClosure.rank (w.restrict F).adicCompletionIntegers
      (w.restrict F).adicCompletion w.adicCompletion w.adicCompletionIntegers
  let e := finCongr hrank
  let b := c'.reindex e
  have hb (i) : b i ∈ w.adicCompletionIntegers := by
    rw [show b i = c' (e.symm i) from Module.Basis.reindex_apply c' e i,
      Module.Basis.localizationLocalization_apply]
    exact (c (e.symm i)).2
  refine ⟨b, hb, fun y => ⟨?_, ?_⟩⟩
  · intro hy i
    let z : w.adicCompletionIntegers := ⟨y, hy⟩
    change b.repr (algebraMap w.adicCompletionIntegers w.adicCompletion z) i ∈ _
    rw [Module.Basis.repr_reindex_apply, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (c.repr z (e.symm i)).2
  · intro hrepr
    rw [← b.sum_repr y]
    apply sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact mul_mem (w.adicCompletionComap_mem_integers (hrepr i)) (hb i)

/-- The integral-closure construction supplies all fields of the exact integral-basis data. -/
theorem completionIntegralBasis_nonempty : Nonempty (w.CompletionIntegralBasis (F := F)) := by
  obtain ⟨b, hb, h⟩ := w.exists_completion_integral_basis (F := F)
  exact ⟨⟨b, hb, h⟩⟩

end Dubon2026.SourceCurve.Place
