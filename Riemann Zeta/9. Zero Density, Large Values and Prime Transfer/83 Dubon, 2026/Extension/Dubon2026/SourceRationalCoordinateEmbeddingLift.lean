import Dubon2026.SourceRationalCoordinateEmbeddingTower

/-! DUB-17/18 -> reverse genus -> actual embedding fibers.
Two embeddings at the same rational coordinate differ by an automorphism
of the original normal extension. The native normal-extension lift is
applied over the fixed rational-function base, with its commutation
hypotheses proved from the literal coordinate equation. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]

theorem exists_galois_postcomp_of_coordinate [Normal (RatFunc K) M]
    (x : F) (hx : Transcendental K x) (ψ ψ' : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X)
    (hψ' : ψ' x = algebraMap (RatFunc K) M RatFunc.X) :
    ∃ σ : M ≃ₐ[RatFunc K] M,
      ψ' = (σ.toAlgHom.restrictScalars K).comp ψ := by
  letI := algebraAlong ψ
  letI := algebraAlong (rationalCoordinateEmbedding K x hx)
  haveI : IsScalarTower (RatFunc K) F M :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun e => e r) (coordinateEmbedding_comp_eq x hx ψ hψ)).symm
  let φ : F →ₐ[RatFunc K] M :=
    { ψ'.toRingHom with
      commutes' := fun r =>
        congrArg (fun e => e r) (coordinateEmbedding_comp_eq x hx ψ' hψ') }
  let σh := φ.liftNormal M
  let σ : M ≃ₐ[RatFunc K] M :=
    AlgEquiv.ofBijective σh (AlgHom.normal_bijective (RatFunc K) M M σh)
  refine ⟨σ, AlgHom.ext fun f => ?_⟩
  exact (φ.liftNormal_commutes M f).symm

end
end Dubon2026.SourceCurve
