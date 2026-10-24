import Dubon2026.SourceRationalCoordinateEmbeddingAction

/-! DUB-17/18 -> reverse genus -> normalized embedding-fiber counts.
The stabilizer of an actual coordinate embedding inside inertia is the
actual decomposition group over that embedded field. This identifies
the group counted by orbit-stabilizer with the group in the proved
normalized ramification formula. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

/-- The literal stabilizer/decomposition equivalence for a fixed embedding. -/
def coordinateEmbeddingStabilizerEquiv (x : F) (hx : Transcendental K x)
    (w : Place K M)
    (ψ : {ψ : F →ₐ[K] M // ψ x = algebraMap (RatFunc K) M RatFunc.X}) :
    letI := coordinateEmbeddingAction (K := K) (M := M) x
    letI := algebraAlong ψ.val
    MulAction.stabilizer (w.toValuationSubring.inertiaSubgroup (RatFunc K)) ψ ≃
      w.toValuationSubring.decompositionSubgroup F := by
  letI := coordinateEmbeddingAction (K := K) (M := M) x
  letI := algebraAlong ψ.val
  haveI := scalarTower_along ψ.val
  letI := algebraAlong (rationalCoordinateEmbedding K x hx)
  haveI : IsScalarTower (RatFunc K) F M :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun e => e r) (coordinateEmbedding_comp_eq x hx ψ.val ψ.property)).symm
  haveI := (finite_galois_coordinateField K (M := M)).1
  let A := MulAction.stabilizer (w.toValuationSubring.inertiaSubgroup (RatFunc K)) ψ
  have hfix (d : A) (f : F) : d.val.val.val (ψ.val f) = ψ.val f :=
    congrArg (fun e : {ψ : F →ₐ[K] M //
      ψ x = algebraMap (RatFunc K) M RatFunc.X} => e.val f)
      (MulAction.mem_stabilizer_iff.mp d.property)
  let fwd : A → w.toValuationSubring.decompositionSubgroup F := fun d =>
    ⟨AlgEquiv.ofRingEquiv (f := d.val.val.val.toRingEquiv) (hfix d), by
      apply (mem_decomposition_iff_comapEquiv_eq w _).mpr
      exact (mem_decomposition_iff_comapEquiv_eq w d.val.val.val).mp d.val.val.property⟩
  let bwd : w.toValuationSubring.decompositionSubgroup F → A := fun u => by
    let σ := u.val.restrictScalars (RatFunc K)
    have hσ : σ ∈ w.toValuationSubring.decompositionSubgroup (RatFunc K) := by
      apply (mem_decomposition_iff_comapEquiv_eq w σ).mpr
      exact (mem_decomposition_iff_comapEquiv_eq w u.val).mp u.property
    let i : w.toValuationSubring.inertiaSubgroup (RatFunc K) :=
      ⟨⟨σ, hσ⟩, mem_inertia_of_decomposition_of_finite_coordinate
        (algebraMap (RatFunc K) M RatFunc.X) w hσ⟩
    refine ⟨i, MulAction.mem_stabilizer_iff.mpr ?_⟩
    exact Subtype.ext (AlgHom.ext fun f => u.val.commutes f)
  exact
    { toFun := fwd
      invFun := bwd
      left_inv := fun d => Subtype.ext (Subtype.ext (Subtype.ext (AlgEquiv.ext fun _ => rfl)))
      right_inv := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl) }

end
end Dubon2026.SourceCurve.Place
