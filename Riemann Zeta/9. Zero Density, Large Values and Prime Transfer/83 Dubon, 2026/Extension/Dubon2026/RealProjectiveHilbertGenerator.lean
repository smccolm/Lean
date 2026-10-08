import Dubon2026.RealProjectiveHilbertL2

/-! # The original cusp generator and its exact completed cyclic realization -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The literal original cusp lift in its faithful completed Hilbert representation. -/
def realProjectiveHilbertGenerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) : RealProjectiveHilbert f :=
  realProjectiveHilbertEmbedding f ⟨realWeightLift k f, realWeightLift_mem_cyclic k f⟩

/-- The completed original generator retains its exact classical Petersson norm. -/
theorem realProjectiveHilbertGenerator_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    inner ℂ (realProjectiveHilbertGenerator f) (realProjectiveHilbertGenerator f) =
      cuspPetersson f f := by
  rw [← realProjectiveHilbertToL2_inner]
  simp only [realProjectiveHilbertGenerator, realProjectiveHilbertToL2_embedding,
    realProjectiveCyclicToL2_inner]
  exact (cuspPetersson_eq_projectiveGroup_integral f f).symm

/-- A nonzero original cusp form gives a nonzero vector in the genuine completed representation. -/
theorem realProjectiveHilbertGenerator_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) :
    realProjectiveHilbertGenerator f ≠ 0 := by
  intro he
  have hz : (⟨realWeightLift k f, realWeightLift_mem_cyclic k f⟩ :
      (realLiftCyclicRepresentation k f).toSubmodule) = 0 :=
    realProjectiveHilbertEmbedding_injective f (by simpa [realProjectiveHilbertGenerator] using he)
  have hl : realWeightLift k (⇑f) = realWeightLift k 0 := by
    ext g
    have ht := congrFun (congrArg Subtype.val hz) g
    simpa only [realWeightLift_apply, Pi.zero_apply, zero_mul] using ht
  have hfun := realWeightLift_injective k hl
  apply hf
  ext z
  exact congrFun hfun z

/-- The exact original compact weight survives in the actual completed representation. -/
theorem realProjectiveHilbertGenerator_compact_weight {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (a : realCompactSubgroup) :
    realProjectiveHilbertRepresentation f (QuotientGroup.mk a.val)
      (realProjectiveHilbertGenerator f) =
      (realCompactWeight k a : ℂ) • realProjectiveHilbertGenerator f := by
  rw [realProjectiveHilbertGenerator, realProjectiveHilbertEmbedding_intertwines,
    ← map_smul]
  apply congrArg (realProjectiveHilbertEmbedding f)
  apply Subtype.ext
  exact realWeightLift_rightRegular k f a

/-- The original cusp generator is cyclic in its actual completed unitary representation. -/
theorem realProjectiveHilbertGenerator_cyclic {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    closure ((Submodule.span ℂ (Set.range (fun a : PSL(2, ℝ) =>
      realProjectiveHilbertRepresentation f a (realProjectiveHilbertGenerator f)))) :
        Set (RealProjectiveHilbert f)) = Set.univ := by
  let S := Submodule.span ℂ (Set.range (fun a : PSL(2, ℝ) =>
    realProjectiveHilbertRepresentation f a (realProjectiveHilbertGenerator f)))
  have hm (v : (realLiftCyclicRepresentation k f).toSubmodule) :
      realProjectiveHilbertEmbedding f v ∈ S := by
    obtain ⟨v, hv⟩ := v
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      change realProjectiveHilbertEmbedding f
        (realProjectiveCyclicRepresentation f (QuotientGroup.mk a)
          ⟨realWeightLift k f, realWeightLift_mem_cyclic k f⟩) ∈ S
      rw [← realProjectiveHilbertEmbedding_intertwines]
      exact Submodule.subset_span ⟨QuotientGroup.mk a, rfl⟩
    | zero =>
      change realProjectiveHilbertEmbedding f 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    | add x y hx hy hix hiy =>
      exact (map_add (realProjectiveHilbertEmbedding f) ⟨x, hx⟩ ⟨y, hy⟩).symm ▸
        S.add_mem hix hiy
    | smul c x hx hix =>
      exact (map_smul (realProjectiveHilbertEmbedding f) c ⟨x, hx⟩).symm ▸ S.smul_mem c hix
  have hi : Set.range (realProjectiveHilbertEmbedding f) ⊆ (S : Set (RealProjectiveHilbert f)) := by
    rintro _ ⟨v, rfl⟩
    exact hm v
  have hc := closure_mono hi
  rw [(realProjectiveHilbertEmbedding_dense f).closure_range] at hc
  exact Set.eq_univ_of_univ_subset hc

end
end Dubon2026
