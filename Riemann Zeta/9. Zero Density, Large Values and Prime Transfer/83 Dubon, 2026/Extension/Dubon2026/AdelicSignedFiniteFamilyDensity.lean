import Dubon2026.AdelicIntegerWeightFiniteClosure

/-! # Density of the actual finite translates of all original signed raising vectors -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original finite translates of every signed raising vector, without normalization or a replacement representation. -/
def adelicSignedFiniteFamily
    (q : (ℕ ⊕ ℕ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding q.2) (adelicSignedRaisingJet f q.1)

/-- Each actual translated signed vector has its original simultaneous integer rotation weight. -/
theorem adelicSignedFiniteFamily_mem_weight (hf : f ≠ 0)
    (q : (ℕ ⊕ ℕ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicSignedFiniteFamily f q ∈ adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k q.1) :=
  adelicIntegerRotationWeightSpace_finite_invariant f _ q.2 _ (adelicSignedRaisingJet_mem_integerWeight f hf q.1)

/-- All original finite translates of the signed raising family densely span the entire original adelic Hilbert space. -/
theorem adelicSignedFiniteFamily_dense (hf : f ≠ 0) :
    (Submodule.span ℂ (Set.range (adelicSignedFiniteFamily f))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℂ (Set.range (adelicSignedFiniteFamily f))).topologicalClosure
  have hfin (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
      (x : AdelicCyclicHilbert f) (hx : x ∈ adelicSignedRaisingClosedSpan f) :
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x ∈ S := by
    have hs : Submodule.span ℂ (Set.range (adelicSignedRaisingJet f)) ≤
        S.comap (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, a), rfl⟩)
    exact closure_minimal hs ((Submodule.isClosed_topologicalClosure _).preimage
      (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a)).continuous) hx
  have ho (g : RationalAdelicGL2) :
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f) ∈ S := by
    let a := (rationalAdelicGL2RealFiniteEquiv g).2
    let r := (rationalAdelicGL2RealFiniteEquiv g).1
    have he : g = rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding r := by
      apply rationalAdelicGL2RealFiniteEquiv.injective
      simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates,
        adelicRealGL2Embedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]
      exact (Prod.eta _).symm
    have hr := adelicFullRealOrbit_mem_signedRaisingClosure f hf r
    rw [he, map_mul, Module.End.mul_apply]
    exact hfin a _ hr
  apply top_unique
  intro x _
  have hx : x ∈ closure ((Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)))) : Set (AdelicCyclicHilbert f)) := by
    rw [adelicCyclicHilbertGenerator_cyclic]
    exact Set.mem_univ x
  exact closure_minimal (Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact ho g))
    (Submodule.isClosed_topologicalClosure _) hx

end
end Dubon2026
