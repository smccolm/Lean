import Dubon2026.AdelicCyclicHilbertL2
import Dubon2026.AdelicGeneratorPetersson

/-! # The original adelic cusp generator retains its exact norm and dense cyclic span -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The original full adelic cusp function in its faithful actual Hilbert completion. -/
def adelicCyclicHilbertGenerator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : AdelicCyclicHilbert f :=
  adelicCyclicHilbertEmbedding f (adelicCyclicGenerator N f)

/-- The completed original generator retains the exact classical Petersson norm times the genuine finite-level Haar factor. -/
theorem adelicCyclicHilbertGenerator_inner {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    inner ℂ (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator f) =
      cuspPetersson f f * (finiteProjectiveGL2Measure (finiteProjectiveGL2Level N)).toReal := by
  rw [← adelicCyclicHilbertToL2_inner]
  simp only [adelicCyclicHilbertGenerator, adelicCyclicHilbertToL2_embedding]
  exact adelicCyclicGenerator_l2_inner N f

/-- Every nonzero original cusp form gives a nonzero vector in its genuine completed adelic representation. -/
theorem adelicCyclicHilbertGenerator_ne_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    adelicCyclicHilbertGenerator f ≠ 0 := by
  intro he
  have hz : adelicCyclicGenerator N f = 0 :=
    adelicCyclicHilbertEmbedding_injective f (by simpa [adelicCyclicHilbertGenerator] using he)
  have hc : canonicalAdelicGL2CuspLift N k f = 0 := congrArg Subtype.val hz
  have hr : realWeightLift k f = 0 := by
    funext r
    have hh := canonicalAdelicGL2CuspLift_real_restriction N f (toGLPos r)
    rw [realPositiveUnitaryLift_toGLPos] at hh
    exact hh.symm.trans (congrFun hc (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, 1)))
  have hfun : (f : ℍ → ℂ) = 0 := by
    apply realWeightLift_injective k
    rw [hr]
    funext r
    simp [realWeightLift_apply]
  apply hf
  ext z
  exact congrFun hfun z

/-- The original full adelic cusp generator is cyclic in its actual completed unitary representation. -/
theorem adelicCyclicHilbertGenerator_cyclic {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    closure ((Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f)))) :
        Set (AdelicCyclicHilbert f)) = Set.univ := by
  let S := Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
    adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f)))
  have hm (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
      adelicCyclicHilbertEmbedding f v ∈ S := by
    obtain ⟨v, hv⟩ := v
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      change adelicCyclicHilbertEmbedding f
        ((adelicLiftCyclicRepresentation N k f).toRepresentation a (adelicCyclicGenerator N f)) ∈ S
      rw [← adelicCyclicHilbertEmbedding_intertwines]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero =>
      change adelicCyclicHilbertEmbedding f 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    | add x y hx hy hix hiy =>
      exact (map_add (adelicCyclicHilbertEmbedding f) ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ S.add_mem hix hiy
    | smul c x hx hix =>
      exact (map_smul (adelicCyclicHilbertEmbedding f) c ⟨x, hx⟩).symm ▸ S.smul_mem c hix
  have hi : Set.range (adelicCyclicHilbertEmbedding f) ⊆ (S : Set (AdelicCyclicHilbert f)) := by
    rintro _ ⟨v, rfl⟩
    exact hm v
  have hc := closure_mono hi
  rw [(adelicCyclicHilbertEmbedding_dense f).closure_range] at hc
  exact Set.eq_univ_of_univ_subset hc

end
end Dubon2026
