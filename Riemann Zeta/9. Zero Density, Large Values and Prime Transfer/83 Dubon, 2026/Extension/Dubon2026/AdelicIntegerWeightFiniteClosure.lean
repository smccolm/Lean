import Dubon2026.AdelicIntegerProjectionReal

/-! # Every original signed rotation weight is the actual finite-adelic cyclic closure of its raising vector -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

private theorem projection_product_vector {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (P : V →ₗ[ℂ] V) (a b : G) (v w : V) (c : ℂ)
    (hp : ∀ z, P (ρ a z) = ρ a (P z)) (hc : P (ρ b v) = c • w) :
    P (ρ (a * b) v) = c • ρ a w := by
  rw [map_mul, Module.End.mul_apply, hp, hc, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original finite-adelic cyclic closure of a genuine signed raising vector. -/
def adelicSignedFiniteCyclicClosedSpan (i : ℕ ⊕ ℕ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicSignedRaisingJet f i)))).topologicalClosure

/-- The actual signed finite cyclic closure lies in its exact original simultaneous real-character space. -/
theorem adelicSignedFiniteCyclicClosedSpan_le_weight (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    adelicSignedFiniteCyclicClosedSpan f i ≤ adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicIntegerRotationWeightSpace_finite_invariant f _ a _ (adelicSignedRaisingJet_mem_integerWeight f hf i)
  · exact adelicIntegerRotationWeightSpace_isClosed f _

/-- Every original full adelic generator orbit projects to its actual finite-coordinate translate of the original signed raising line. -/
theorem adelicIntegerRotationWeightProjection_fullOrbit (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (g : RationalAdelicGL2) :
    ∃ c : ℂ, adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i)
      (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) =
      c • adelicCyclicHilbertRepresentation f
        (rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv g).2) (adelicSignedRaisingJet f i) := by
  let a := (rationalAdelicGL2RealFiniteEquiv g).2
  let r := (rationalAdelicGL2RealFiniteEquiv g).1
  have he : g = rationalAdelicFiniteGL2Embedding a * adelicRealGL2Embedding r := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates,
      adelicRealGL2Embedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]
    exact (Prod.eta _).symm
  obtain ⟨c, hc⟩ := adelicIntegerRotationWeightProjection_realOrbit f hf hk i r
  refine ⟨c, ?_⟩
  change adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i)
    (adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)) =
      c • adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicSignedRaisingJet f i)
  have hz := @projection_product_vector RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i)).toLinearMap
    (rationalAdelicFiniteGL2Embedding a) (adelicRealGL2Embedding r)
    (adelicCyclicHilbertGenerator f) (adelicSignedRaisingJet f i) c
    (adelicIntegerRotationWeightProjection_finite f _ a) hc
  exact (congrArg (fun h : RationalAdelicGL2 => adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i)
    (adelicCyclicHilbertRepresentation f h (adelicCyclicHilbertGenerator f))) he).trans hz

/-- The original global signed-weight projector sends every original Hilbert vector into the genuine signed finite cyclic closure. -/
theorem adelicIntegerRotationWeightProjection_mem_finiteClosure (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (x : AdelicCyclicHilbert f) :
    adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) x ∈ adelicSignedFiniteCyclicClosedSpan f i := by
  have hs : ∀ y ∈ Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f))),
      adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) y ∈ adelicSignedFiniteCyclicClosedSpan f i := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨c, hc⟩ := adelicIntegerRotationWeightProjection_fullOrbit f hf hk i g
      rw [hc]
      apply (adelicSignedFiniteCyclicClosedSpan f i).smul_mem
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simpa only [map_zero] using (adelicSignedFiniteCyclicClosedSpan f i).zero_mem
    | add y z hy hz ihy ihz => simpa only [map_add] using (adelicSignedFiniteCyclicClosedSpan f i).add_mem ihy ihz
    | smul c y hy ih => simpa only [map_smul] using (adelicSignedFiniteCyclicClosedSpan f i).smul_mem c ih
  have hx : x ∈ closure ((Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f)))) : Set (AdelicCyclicHilbert f)) := by
    rw [adelicCyclicHilbertGenerator_cyclic]
    exact Set.mem_univ x
  exact closure_minimal hs ((Submodule.isClosed_topologicalClosure _).preimage
    (adelicIntegerRotationWeightProjection f _).continuous) hx

/-- Every exact original signed real-character space equals its genuine finite-adelic cyclic Hilbert closure. -/
theorem adelicIntegerRotationWeightSpace_eq_signedFiniteClosure (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) = adelicSignedFiniteCyclicClosedSpan f i := by
  apply le_antisymm
  · intro x hx
    have he : adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) x = x :=
      (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f)
        inferInstance inferInstance inferInstance (adelicIntegerRotationWeightSpace f _) inferInstance x).mpr hx
    exact he ▸ adelicIntegerRotationWeightProjection_mem_finiteClosure f hf hk i x
  · exact adelicSignedFiniteCyclicClosedSpan_le_weight f hf i

end
end Dubon2026
