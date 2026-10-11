import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Galois.Basic

/-! # The original integral root generates its actual fraction field -/

namespace Dubon2026
noncomputable section

open Polynomial

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  (f : R[X]) [Algebra (AdjoinRoot f) L]
  [IsScalarTower R (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]

/-- The actual image of the original adjoined root generates the entire
original fraction field, since every original integral element is polynomial
in that root and every original fraction is a quotient of integral elements. -/
theorem adjoinRootFraction_adjoin_eq_top :
    IntermediateField.adjoin K
      ({algebraMap (AdjoinRoot f) L (AdjoinRoot.root f)} : Set L) = ⊤ := by
  let E := IntermediateField.adjoin K
    ({algebraMap (AdjoinRoot f) L (AdjoinRoot.root f)} : Set L)
  have hb (b : AdjoinRoot f) : algebraMap (AdjoinRoot f) L b ∈ E := by
    have h : (⊤ : Subalgebra R (AdjoinRoot f)) ≤
        (E.toSubalgebra.restrictScalars R).comap
          (IsScalarTower.toAlgHom R (AdjoinRoot f) L) := by
      rw [← AdjoinRoot.adjoinRoot_eq_top (f := f)]
      apply Algebra.adjoin_le
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
    exact h (by trivial)
  apply top_unique
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (AdjoinRoot f) x
  exact E.div_mem (hb a) (hb b)

/-- Once the original polynomial is proved to split, the genuine fraction
field is its splitting field. Root generation is proved from the original
root quotient and fraction representation, rather than assumed. -/
theorem adjoinRootFraction_isSplittingField
    [Algebra.IsAlgebraic K L] (hf : f.Monic)
    (hs : ((f.map (algebraMap R K)).map (algebraMap K L)).Splits) :
    (f.map (algebraMap R K)).IsSplittingField K L := by
  have hgen : (IntermediateField.adjoin K
      ({algebraMap (AdjoinRoot f) L (AdjoinRoot.root f)} : Set L)).toSubalgebra = ⊤ :=
    congrArg (fun E : IntermediateField K L => E.toSubalgebra)
      (adjoinRootFraction_adjoin_eq_top R K L f)
  rw [IntermediateField.adjoin_toSubalgebra] at hgen
  refine ⟨hs, top_unique ?_⟩
  rw [← hgen]
  apply Algebra.adjoin_mono
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply (hf.map (algebraMap R K)).mem_rootSet.mpr
  rw [aeval_map_algebraMap]
  change aeval ((IsScalarTower.toAlgHom R (AdjoinRoot f) L) (AdjoinRoot.root f)) f = 0
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

end
end Dubon2026
