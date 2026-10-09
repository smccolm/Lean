import Dubon2026.AdelicLocalCyclicClosure
import Dubon2026.FiniteOrbitOfEigenSpan
import Dubon2026.AdelicHilbertCentralLevel
import Dubon2026.FinitePlaceLevelTopology

/-! # The genuine smooth algebraic core of the original local cyclic action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual algebraic span of the original single-place orbit of the original cusp generator. -/
def adelicLocalCyclicCore (v : HeightOneSpectrum ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) =>
    adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f)))

/-- The genuine local cyclic Hilbert space is exactly the closure of the original algebraic local core. -/
theorem adelicLocalCyclicCore_closure (v : HeightOneSpectrum ℤ) :
    (adelicLocalCyclicCore f v).topologicalClosure = adelicLocalCyclicClosedSpan f v := rfl

/-- The original generator belongs to the genuine algebraic local core. -/
theorem adelicLocalCyclicCore_generator_mem (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicLocalCyclicCore f v := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- The actual algebraic local core is invariant under the original local action. -/
theorem adelicLocalCyclicCore_invariant (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f)
    (hx : x ∈ adelicLocalCyclicCore f v) :
    adelicCyclicLocalRepresentation f v g x ∈ adelicLocalCyclicCore f v :=
  @representationOrbitSpan_invariant (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation f v) (adelicCyclicHilbertGenerator f) g x hx

/-- Every original algebraic local orbit vector has a genuine preimage in the original full algebraic cusp core. -/
theorem adelicLocalCyclicCore_le_embedding_range (v : HeightOneSpectrum ℤ) :
    adelicLocalCyclicCore f v ≤ (adelicCyclicHilbertEmbedding f).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  refine ⟨(adelicLiftCyclicRepresentation N k f).toRepresentation
    (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicCyclicGenerator N f), ?_⟩
  exact (adelicCyclicHilbertEmbedding_intertwines f
    (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicCyclicGenerator N f)).symm

/-- Every actual algebraic local core vector has a genuine open stabilizer in the original local group. -/
theorem adelicLocalCyclicCore_smooth (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicCore f v) :
    ∃ H : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (H : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ H, adelicCyclicLocalRepresentation f v g x = x := by
  obtain ⟨u, hu⟩ := adelicLocalCyclicCore_le_embedding_range f v hx
  obtain ⟨K, _, hKo, hK⟩ := adelicCyclicHilbert_finite_smooth_core f u
  refine ⟨K.comap (finiteAdelicLocalGL2Hom v), hKo.preimage (finiteAdelicLocalGL2_continuous v), ?_⟩
  intro g hg
  rw [← hu]
  exact hK (finiteAdelicLocalGL2 v g) hg

end
end Dubon2026
