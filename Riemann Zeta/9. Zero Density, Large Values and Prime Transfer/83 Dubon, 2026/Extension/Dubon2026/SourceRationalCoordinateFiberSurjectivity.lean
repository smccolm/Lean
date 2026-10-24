import Dubon2026.SourceRationalFinitePlaceUniqueness
import Dubon2026.SourceRationalCoordinatePlaceOrbits

/-! DUB-17/18 -> reverse genus -> exceptional place fibers.
Every place above a prescribed finite coordinate value is obtained by
restricting the fixed upper place along an actual coordinate-preserving
embedding. Lying over, normalized orders and Galois transitivity supply
the embedding; no surjectivity certificate is assumed. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]
variable [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

omit [FiniteDimensional (RatFunc K) M] in
theorem restrict_rational_finite_value_eq (w w' : Place K M) (a : K)
    (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a))
    (hw' : 0 < w'.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)) :
    w'.restrict (RatFunc K) = w.restrict (RatFunc K) := by
  have hpos (u : Place K M)
      (hu : 0 < u.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)) :
      0 < (u.restrict (RatFunc K)).ord (RatFunc.X - algebraMap K (RatFunc K) a) := by
    have ho := u.ord_algebraMap_restrict (RatFunc.X - algebraMap K (RatFunc K) a)
    rw [map_sub, ← IsScalarTower.algebraMap_apply K (RatFunc K) M] at ho
    rw [ho] at hu
    exact (mul_pos_iff_of_pos_right (u.ord_restricted_uniformizer_pos (F := RatFunc K))).mp hu
  exact rational_finite_value_place_unique a _ _ (hpos w' hw') (hpos w hw)

theorem exists_coordinate_embedding_restrict_eq
    (x : F) (hx : Transcendental K x) (ι : F →ₐ[K] M)
    (hι : ι x = algebraMap (RatFunc K) M RatFunc.X)
    (w : Place K M) (a : K)
    (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a))
    (v : Place K F) (hv : 0 < v.ord (x - algebraMap K F a)) :
    ∃ (ψ : F →ₐ[K] M) (hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X),
      restrictAlongFinite ψ (finite_galois_along_coordinate x hx ψ hψ).1 w = v := by
  let hfin := (finite_galois_along_coordinate x hx ι hι).1
  have hsep : letI := algebraAlong ι; Algebra.IsSeparable F M := by
    letI := algebraAlong ι
    haveI := (finite_galois_along_coordinate x hx ι hι).2
    infer_instance
  obtain ⟨W, hW⟩ := restrictAlongFinite_surjective ι hfin hsep v
  have hWpos : 0 < W.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a) := by
    have ho := ord_restrictAlongFinite ι hfin W (x - algebraMap K F a)
    rw [map_sub, hι, ι.commutes, hW] at ho
    rw [ho]
    have hr := ord_restrictAlongFinite_uniformizer_pos ι hfin W
    rw [hW] at hr
    exact mul_pos hv hr
  obtain ⟨σ, hσ⟩ := exists_comapEquiv_of_restrict_eq w W
    (restrict_rational_finite_value_eq w W a hw hWpos)
  let ψ := (σ.toAlgHom.restrictScalars K).comp ι
  have hψ : ψ x = algebraMap (RatFunc K) M RatFunc.X := by
    change σ (ι x) = _
    rw [hι, σ.commutes]
  refine ⟨ψ, hψ, ?_⟩
  calc
    _ = restrictAlongFinite ι hfin (w.comapEquiv (σ.restrictScalars K)) :=
      restrictAlongFinite_postcomp ι (σ.restrictScalars K) hfin
        (finite_galois_along_coordinate x hx ψ hψ).1 w
    _ = v := by rw [hσ, hW]

end
end Dubon2026.SourceCurve.Place
