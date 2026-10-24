import Dubon2026.SourceRationalCoordinateEmbeddingTower
import Dubon2026.SourceCurveFiberResidueConstants
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> reverse genus -> exceptional place fibers.
Restrict the actual valuation place along a finite embedding in arbitrary
characteristic. All order statements reuse the proved normalized
restriction formula; existence of upper places reuses the chart theorem.
Finiteness and separability are derived for the modular embeddings by the
rational-coordinate Galois tower theorem. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M]

/-- Actual valuation restriction along a finite field embedding. -/
def restrictAlongFinite (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.Finite)
    (w : Place K M) : Place K F :=
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F M := hψ
  w.restrict F

theorem mem_restrictAlongFinite_iff (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.Finite)
    (w : Place K M) (f : F) :
    f ∈ (restrictAlongFinite ψ hψ w).toValuationSubring ↔
      ψ f ∈ w.toValuationSubring := Iff.rfl

theorem ord_restrictAlongFinite (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.Finite)
    (w : Place K M) (f : F) :
    w.ord (ψ f) = (restrictAlongFinite ψ hψ w).ord f *
      w.ord (ψ (restrictAlongFinite ψ hψ w).uniformizer) := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F M := hψ
  exact w.ord_algebraMap_restrict f

theorem ord_restrictAlongFinite_uniformizer_pos
    (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.Finite) (w : Place K M) :
    0 < w.ord (ψ (restrictAlongFinite ψ hψ w).uniformizer) := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F M := hψ
  exact w.ord_restricted_uniformizer_pos (F := F)

theorem restrictAlongFinite_postcomp (ψ : F →ₐ[K] M) (σ : M ≃ₐ[K] M)
    (hψ : ψ.toRingHom.Finite)
    (hσψ : (σ.toAlgHom.comp ψ).toRingHom.Finite) (w : Place K M) :
    restrictAlongFinite (σ.toAlgHom.comp ψ) hσψ w =
      restrictAlongFinite ψ hψ (w.comapEquiv σ) := by
  apply Place.ext
  ext f
  rw [mem_restrictAlongFinite_iff, mem_restrictAlongFinite_iff, mem_comapEquiv_iff]
  rfl

theorem restrictAlongFinite_surjective (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.Finite)
    (hsep : letI := algebraAlong ψ; Algebra.IsSeparable F M) :
    Function.Surjective (restrictAlongFinite ψ hψ) := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F M := hψ
  haveI : Algebra.IsSeparable F M := hsep
  intro v
  exact v.exists_fiberPlace (E := M)

end
end Dubon2026.SourceCurve.Place
