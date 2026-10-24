import Dubon2026.SourceRationalCoordinateEmbeddingLift
import Dubon2026.SourceCurveFiniteEmbeddingRestriction
import Dubon2026.SourceCurveGaloisFiberTransitivity
import Dubon2026.SourceCurveClosedConstantResidue
import Dubon2026.SourceRatFuncGaloisCoordinate

/-! DUB-17/18 -> reverse genus -> actual exceptional fibers.
Two rational-coordinate embeddings induce the same restricted place
exactly when they differ by the actual decomposition group. Normal lifting
and prime/place transitivity discharge both implications. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

theorem restrictAlongFinite_eq_iff_decomposition
    (x : F) (hx : Transcendental K x) (ψ ψ' : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X)
    (hψ' : ψ' x = algebraMap (RatFunc K) M RatFunc.X)
    (w : Place K M) :
    restrictAlongFinite ψ' (finite_galois_along_coordinate x hx ψ' hψ').1 w =
      restrictAlongFinite ψ (finite_galois_along_coordinate x hx ψ hψ).1 w ↔
    ∃ σ : M ≃ₐ[RatFunc K] M,
      σ ∈ w.toValuationSubring.decompositionSubgroup (RatFunc K) ∧
        ψ' = (σ.toAlgHom.restrictScalars K).comp ψ := by
  let hfin := (finite_galois_along_coordinate x hx ψ hψ).1
  let hfin' := (finite_galois_along_coordinate x hx ψ' hψ').1
  constructor
  · intro he
    obtain ⟨τ, hτ⟩ := exists_galois_postcomp_of_coordinate x hx ψ ψ' hψ hψ'
    letI := algebraAlong ψ
    haveI := scalarTower_along ψ
    letI := algebraAlong (rationalCoordinateEmbedding K x hx)
    haveI : IsScalarTower (RatFunc K) F M :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (congrArg (fun e => e r) (coordinateEmbedding_comp_eq x hx ψ hψ)).symm
    haveI : FiniteDimensional F M := hfin
    haveI : IsGalois F M := (finite_galois_along_coordinate x hx ψ hψ).2
    have hres : (w.comapEquiv (τ.restrictScalars K)).restrict F = w.restrict F := by
      calc
        _ = restrictAlongFinite ψ' hfin' w := by
          apply Place.ext
          ext f
          change τ (ψ f) ∈ w.toValuationSubring ↔ ψ' f ∈ w.toValuationSubring
          rw [hτ]
          rfl
        _ = _ := he
    obtain ⟨υ, hυ⟩ := exists_comapEquiv_of_restrict_eq
      (w.comapEquiv (τ.restrictScalars K)) w hres.symm
    let σ : M ≃ₐ[RatFunc K] M := τ * υ.restrictScalars (RatFunc K)
    refine ⟨σ, (mem_decomposition_iff_comapEquiv_eq w σ).mpr ?_, ?_⟩
    · have hc : w.comapEquiv (σ.restrictScalars K) =
          (w.comapEquiv (τ.restrictScalars K)).comapEquiv (υ.restrictScalars K) := by
        apply Place.ext
        ext f
        rfl
      exact hc.trans hυ
    · apply AlgHom.ext
      intro f
      change ψ' f = τ (υ (ψ f))
      have hu : υ (ψ f) = ψ f := υ.commutes f
      rw [hu, hτ]
      rfl
  · rintro ⟨σ, hσ, hcomp⟩
    have hw := (mem_decomposition_iff_comapEquiv_eq w σ).mp hσ
    calc
      _ = restrictAlongFinite ψ hfin (w.comapEquiv (σ.restrictScalars K)) := by
        apply Place.ext
        ext f
        change ψ' f ∈ w.toValuationSubring ↔ σ (ψ f) ∈ w.toValuationSubring
        rw [hcomp]
        rfl
      _ = _ := congrArg (restrictAlongFinite ψ hfin) hw

theorem restrictAlongFinite_eq_iff_inertia [IsAlgClosed K]
    (x : F) (hx : Transcendental K x) (ψ ψ' : F →ₐ[K] M)
    (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X)
    (hψ' : ψ' x = algebraMap (RatFunc K) M RatFunc.X)
    (w : Place K M) :
    restrictAlongFinite ψ' (finite_galois_along_coordinate x hx ψ' hψ').1 w =
      restrictAlongFinite ψ (finite_galois_along_coordinate x hx ψ hψ).1 w ↔
    ∃ σ : w.toValuationSubring.inertiaSubgroup (RatFunc K),
      ψ' = (σ.val.val.toAlgHom.restrictScalars K).comp ψ := by
  rw [restrictAlongFinite_eq_iff_decomposition x hx ψ ψ' hψ hψ' w]
  constructor
  · rintro ⟨σ, hσ, he⟩
    haveI := (finite_galois_coordinateField K (M := M)).1
    exact ⟨⟨⟨σ, hσ⟩, mem_inertia_of_decomposition_of_finite_coordinate
      (algebraMap (RatFunc K) M RatFunc.X) w hσ⟩, he⟩
  · rintro ⟨σ, he⟩
    exact ⟨σ.val.val, σ.val.property, he⟩

end
end Dubon2026.SourceCurve.Place
