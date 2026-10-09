import Dubon2026.AdelicIntegerProjectionReal

/-! # The actual original adelic representation has no integer rotation weights outside its signed raising spectrum -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine global projector for a missing integer weight vanishes on the entire original full real Hilbert factor. -/
theorem adelicMissingIntegerWeightProjection_realClosure (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, m ≠ adelicSignedRaisingWeight k i)
    (x : AdelicCyclicHilbert f) (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    adelicIntegerRotationWeightProjection f m x = 0 := by
  rw [← adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf] at hx
  have hs : Submodule.span ℂ (Set.range (adelicSignedRaisingJet f)) ≤
      LinearMap.ker (adelicIntegerRotationWeightProjection f m).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact adelicIntegerRotationWeightProjection_other f hf m i (hm i)
  exact closure_minimal hs (adelicIntegerRotationWeightProjection f m).isClosed_ker hx

/-- The missing-weight projector annihilates every original full adelic generator orbit vector. -/
theorem adelicMissingIntegerWeightProjection_fullOrbit (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, m ≠ adelicSignedRaisingWeight k i) (g : RationalAdelicGL2) :
    adelicIntegerRotationWeightProjection f m
      (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) = 0 := by
  let a := (rationalAdelicGL2RealFiniteEquiv g).2
  let r := (rationalAdelicGL2RealFiniteEquiv g).1
  have he : g = rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding r := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates,
      adelicRealGL2Embedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]
    exact (Prod.eta _).symm
  have hx : adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding r) (adelicCyclicHilbertGenerator f) ∈
      (adelicFullRealUnitCore f).topologicalClosure := by
    rw [adelicFullRealUnitCore_eq_generatorSpan f hf]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨r, rfl⟩)
  rw [he, map_mul, Module.End.mul_apply, adelicIntegerRotationWeightProjection_finite,
    adelicMissingIntegerWeightProjection_realClosure f hf m hm _ hx, map_zero]

/-- Density of the original full adelic generator orbit forces a missing integer-character projector to vanish everywhere. -/
theorem adelicMissingIntegerWeightProjection_zero (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, m ≠ adelicSignedRaisingWeight k i) (x : AdelicCyclicHilbert f) :
    adelicIntegerRotationWeightProjection f m x = 0 := by
  have hs : Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f))) ≤
      LinearMap.ker (adelicIntegerRotationWeightProjection f m).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact adelicMissingIntegerWeightProjection_fullOrbit f hf m hm g
  have hx : x ∈ closure ((Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)))) : Set (AdelicCyclicHilbert f)) := by
    rw [adelicCyclicHilbertGenerator_cyclic]
    exact Set.mem_univ x
  exact closure_minimal hs (adelicIntegerRotationWeightProjection f m).isClosed_ker hx

/-- The entire actual simultaneous integer-character space is zero outside the original signed raising weights. -/
theorem adelicIntegerRotationWeightSpace_eq_bot (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, m ≠ adelicSignedRaisingWeight k i) : adelicIntegerRotationWeightSpace f m = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have he : adelicIntegerRotationWeightProjection f m x = x :=
    (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
      (adelicIntegerRotationWeightSpace f m) inferInstance x).mpr hx
  exact he.symm.trans (adelicMissingIntegerWeightProjection_zero f hf m hm x)

end
end Dubon2026
