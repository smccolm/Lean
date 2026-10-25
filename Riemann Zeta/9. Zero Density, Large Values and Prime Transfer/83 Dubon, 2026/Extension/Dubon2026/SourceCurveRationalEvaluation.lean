import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> Weil reciprocity and Hecke adjointness -> norm evaluation
on rational place fibers. Use the actual residue field and its specified
constant-map bijection. The original modular fields already prove this
bijection; the later original consumer will discharge it. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Evaluation of regular functions through the actual rational residue field. -/
def rationalRegularEval (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) :
    v.toValuationSubring →+* K :=
  (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).symm.toRingHom.comp
    (residue v.toValuationSubring)

theorem residue_rationalRegularEval (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) (f : v.toValuationSubring) :
    algebraMap K v.ResidueField (v.rationalRegularEval hv f) = residue v.toValuationSubring f :=
  (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).apply_symm_apply _

theorem rationalRegularEval_algebraMap (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField)) (a : K) :
    v.rationalRegularEval hv (algebraMap K v.toValuationSubring a) = a :=
  (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).symm_apply_apply a

theorem sub_rationalRegularEval_mem_center
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (v : Place K F)
    (hv : Function.Bijective (algebraMap K v.ResidueField))
    (hmem : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring) (c : R) :
    c - algebraMap K R (v.rationalRegularEval hv ⟨algebraMap R F c, hmem c⟩) ∈
      center R v hmem := by
  rw [mem_center_iff, ← residue_eq_zero_iff]
  have he : (⟨algebraMap R F
      (c - algebraMap K R (v.rationalRegularEval hv ⟨algebraMap R F c, hmem c⟩)),
      hmem _⟩ : v.toValuationSubring) =
      ⟨algebraMap R F c, hmem c⟩ - algebraMap K v.toValuationSubring
        (v.rationalRegularEval hv ⟨algebraMap R F c, hmem c⟩) := by
    apply Subtype.ext
    change algebraMap R F (c - algebraMap K R _) = algebraMap R F c - algebraMap K F _
    rw [map_sub, ← IsScalarTower.algebraMap_apply K R F]
  rw [he]
  change residue v.toValuationSubring
    (⟨algebraMap R F c, hmem c⟩ - algebraMap K v.toValuationSubring
      (v.rationalRegularEval hv ⟨algebraMap R F c, hmem c⟩)) = 0
  rw [map_sub]
  change residue v.toValuationSubring ⟨algebraMap R F c, hmem c⟩ -
    algebraMap K v.ResidueField (v.rationalRegularEval hv ⟨algebraMap R F c, hmem c⟩) = 0
  rw [residue_rationalRegularEval, sub_self]

end
end Dubon2026.SourceCurve.Place
