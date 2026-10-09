import Dubon2026.AdelicFullOrbitWeightProjection

/-! # Identification of the full original lowest-weight Hilbert space with its genuine finite-adelic cyclic closure -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual closed span of the original finite-adelic translates of the original cusp generator. -/
def adelicFiniteCyclicClosedSpan : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicHilbertGenerator f)))).topologicalClosure

/-- The original finite-adelic cyclic closure lies in the actual original lowest rotation-character space. -/
theorem adelicFiniteCyclicClosedSpan_le_weight (hf : f ≠ 0) :
    adelicFiniteCyclicClosedSpan f ≤ adelicRotationWeightSpace f := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicRotationWeightSpace_finite_invariant f a _
      (adelicCyclicHilbertGenerator_mem_rotationWeight f hf)
  · exact adelicRotationWeightSpace_isClosed f

/-- The genuine lowest-weight projector maps every original Hilbert vector into the actual finite-adelic cyclic closure. -/
theorem adelicRotationWeightProjection_mem_finiteClosure (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) :
    adelicRotationWeightProjection f v ∈ adelicFiniteCyclicClosedSpan f := by
  have hs : ∀ w ∈ Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f))),
      adelicRotationWeightProjection f w ∈ adelicFiniteCyclicClosedSpan f := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨g, rfl⟩ := hw
        obtain ⟨c, hc⟩ := adelicRotationWeightProjection_fullOrbit f hf hk g
        rw [hc]
        apply (adelicFiniteCyclicClosedSpan f).smul_mem
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simpa only [map_zero] using (adelicFiniteCyclicClosedSpan f).zero_mem
    | add w z hw hz ihw ihz => simpa only [map_add] using (adelicFiniteCyclicClosedSpan f).add_mem ihw ihz
    | smul c w hw ih => simpa only [map_smul] using (adelicFiniteCyclicClosedSpan f).smul_mem c ih
  have hv : v ∈ closure ((Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)))) : Set (AdelicCyclicHilbert f)) := by
    rw [adelicCyclicHilbertGenerator_cyclic]
    exact Set.mem_univ v
  exact closure_minimal hs ((Submodule.isClosed_topologicalClosure _).preimage
    (adelicRotationWeightProjection f).continuous) hv

/-- The entire original lowest rotation-character space is exactly the actual finite-adelic cyclic Hilbert closure. -/
theorem adelicRotationWeightSpace_eq_finiteClosure (hf : f ≠ 0) (hk : 0 < k) :
    adelicRotationWeightSpace f = adelicFiniteCyclicClosedSpan f := by
  apply le_antisymm
  · intro v hv
    have he : adelicRotationWeightProjection f v = v :=
      (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f)
        inferInstance inferInstance inferInstance (adelicRotationWeightSpace f) inferInstance v).mpr hv
    exact he ▸ adelicRotationWeightProjection_mem_finiteClosure f hf hk v
  · exact adelicFiniteCyclicClosedSpan_le_weight f hf

end
end Dubon2026
