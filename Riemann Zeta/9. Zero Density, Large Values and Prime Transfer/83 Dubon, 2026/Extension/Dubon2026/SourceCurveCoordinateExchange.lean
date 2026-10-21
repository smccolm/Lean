import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> local regular differential orders -> finite extension over
the genuine place uniformizer. Only the transcendence-basis exchange needed
for this change of coordinate is selected. Essential finite type and pinned
algebraicity-to-finiteness supply the finite extension downstream.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Set Cardinal

theorem isAlgebraic_adjoin_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hx : Transcendental K x := by
    intro hxalg
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    haveI : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)
  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg
  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind
  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

end
end Dubon2026.SourceCurve
