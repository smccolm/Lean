import Dubon2026.FiniteAdelicCompactLevel
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.SigmaCompact

/-! # The genuine finite adelic projective general-linear group and its compact open levels -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Set Topology TopologicalSpace MeasureTheory
open scoped MatrixGroups

/-- The actual projective general-linear group of canonical finite rational adeles. -/
abbrev RationalFiniteProjectiveGL2 := PGL(2, FiniteAdeleRing ℤ ℚ)

instance rationalFiniteProjectiveGL2TopologicalSpace : TopologicalSpace RationalFiniteProjectiveGL2 :=
  inferInstanceAs (TopologicalSpace (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) ⧸
    Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))

instance rationalFiniteProjectiveGL2IsTopologicalGroup : IsTopologicalGroup RationalFiniteProjectiveGL2 := by
  change IsTopologicalGroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) ⧸
    Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
  infer_instance

/-- The actual center of the finite adelic general-linear group is closed in its original topology. -/
instance rationalFiniteGL2CenterIsClosed : IsClosed
    (Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
      Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
  have he : (Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
      Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) =
      ⋂ h : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ), {g | h * g = g * h} := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, mem_iInter, mem_setOf_eq]
  rw [he]
  exact isClosed_iInter fun h => isClosed_eq (continuous_const.mul continuous_id)
    (continuous_id.mul continuous_const)

instance rationalFiniteProjectiveGL2T2Space : T2Space RationalFiniteProjectiveGL2 := by
  change T2Space (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) ⧸
    Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
  infer_instance

instance rationalFiniteProjectiveGL2LocallyCompactSpace : LocallyCompactSpace RationalFiniteProjectiveGL2 := by
  change LocallyCompactSpace (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) ⧸
    Subgroup.center (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
  infer_instance

instance rationalFiniteProjectiveGL2MeasurableSpace : MeasurableSpace RationalFiniteProjectiveGL2 := borel _

instance rationalFiniteProjectiveGL2BorelSpace : BorelSpace RationalFiniteProjectiveGL2 := ⟨rfl⟩

/-- The actual projectivization of finite adelic matrices is continuous. -/
theorem finiteProjectivizeGL2_continuous : Continuous
    (ProjGenLinGroup.mk : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) → RationalFiniteProjectiveGL2) :=
  QuotientGroup.continuous_mk

/-- The genuine finite projective level is the image of the original general-linear level subgroup. -/
def finiteProjectiveGL2Level (N : ℕ) : Subgroup RationalFiniteProjectiveGL2 :=
  (finiteAdeleGL2Gamma0 N).map ProjGenLinGroup.mk

/-- The original projective finite level group is compact and open at every nonzero level. -/
theorem finiteProjectiveGL2Level_compact_open (N : ℕ) [NeZero N] :
    IsCompact (finiteProjectiveGL2Level N : Set RationalFiniteProjectiveGL2) ∧
      IsOpen (finiteProjectiveGL2Level N : Set RationalFiniteProjectiveGL2) := by
  rw [finiteProjectiveGL2Level, Subgroup.coe_map]
  exact ⟨(finiteAdeleGL2Gamma0_isCompact N).image finiteProjectivizeGL2_continuous,
    QuotientGroup.isOpenMap_coe _ (finiteAdeleGL2Gamma0_isOpen N)⟩

/-- The original full-level compact subgroup provides an actual Haar normalization set. -/
def finiteProjectiveGL2Normalization : PositiveCompacts RationalFiniteProjectiveGL2 where
  carrier := finiteProjectiveGL2Level 1
  isCompact' := (finiteProjectiveGL2Level_compact_open 1).1
  interior_nonempty' := by
    rw [(finiteProjectiveGL2Level_compact_open 1).2.interior_eq]
    exact ⟨1, (finiteProjectiveGL2Level 1).one_mem⟩

/-- Actual Haar measure on the genuine finite projective group, normalized at the original full-level subgroup. -/
def finiteProjectiveGL2Measure : Measure RationalFiniteProjectiveGL2 :=
  Measure.haarMeasure finiteProjectiveGL2Normalization

instance finiteProjectiveGL2MeasureIsHaarMeasure : finiteProjectiveGL2Measure.IsHaarMeasure := by
  unfold finiteProjectiveGL2Measure
  infer_instance

/-- The actual finite projective Haar measure assigns volume one to the original full-level compact subgroup. -/
theorem finiteProjectiveGL2Measure_level_one :
    finiteProjectiveGL2Measure (finiteProjectiveGL2Level 1) = 1 :=
  Measure.haarMeasure_self (K₀ := finiteProjectiveGL2Normalization)

/-- Genuine rational strong approximation covers the original finite projective group by countably many translates of its compact full-level subgroup. -/
instance rationalFiniteProjectiveGL2SigmaCompactSpace : SigmaCompactSpace RationalFiniteProjectiveGL2 := by
  letI : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  letI : Countable GL(2, ℚ)⁺ :=
    (show Function.Injective (fun r : GL(2, ℚ)⁺ => r.val.val) from
      fun _ _ h => Subtype.ext (Units.ext h)).countable
  let C (r : GL(2, ℚ)⁺) : Set RationalFiniteProjectiveGL2 :=
    (fun x => ProjGenLinGroup.mk (rationalPositiveGL2ToFinite r) * x) '' finiteProjectiveGL2Level 1
  have hc (r : GL(2, ℚ)⁺) : IsCompact (C r) :=
    (finiteProjectiveGL2Level_compact_open 1).1.image
      (continuous_const_mul (ProjGenLinGroup.mk (rationalPositiveGL2ToFinite r)))
  have he : ⋃ r : GL(2, ℚ)⁺, C r = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
    obtain ⟨r, u, hu⟩ := rationalGL2_finiteAdeles_gamma0_factorization 1 g
    refine ⟨r, ProjGenLinGroup.mk u.val, ?_, ?_⟩
    · exact ⟨u.val, u.property, rfl⟩
    · change ProjGenLinGroup.mk (rationalPositiveGL2ToFinite r) * ProjGenLinGroup.mk u.val =
        ProjGenLinGroup.mk g
      rw [← map_mul]
      exact congrArg ProjGenLinGroup.mk hu.symm
  refine ⟨?_⟩
  rw [← he]
  exact isSigmaCompact_iUnion_of_isCompact C hc

instance finiteProjectiveGL2MeasureSigmaFinite : SigmaFinite finiteProjectiveGL2Measure := by
  infer_instance

end
end Dubon2026
