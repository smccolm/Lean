import Dubon2026.PolarizedRepresentationStrictConjugacy
import Dubon2026.DescendedTraceCoefficientGeneration

/-! The actual CM traces determine every coefficient map whenever the
whole polarized specializations are strictly equivalent. This reuses the
existing trace-generation proof for DUB-17 unframed injectivity. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {G H ι O R A k l : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [Algebra O A] [TopologicalSpace A] [T2Space A] [CommRing k] [CommRing l]

/-- Strict equivalence of the actual whole polarized representations
forces equality of the original continuous maps from their CM trace ring. -/
theorem polarizedTraceCoefficientMaps_eq
    (rR : R →+* k) (ρ : H →* GeneralLinearGroup ι R) (q : H →* G)
    (σ : G →* PolarizedGaloisGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (hσ : ∀ h, polarizedComponent (σ (q h)) = 1)
    (hdesc : MatrixStrictlyConjugate rR
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp
        (polarizedIdentityMatrices (σ.comp q) hσ)) ρ)
    (f g : closedMatrixTraceAlgebra (O := O) ρ →ₐ[O] A)
    (hf : Continuous f) (hg : Continuous g) (rA : A →+* l)
    (hfg : PolarizedStrictlyConjugate rA ((polarizedCoefficientMap f.toRingHom).comp σ)
      ((polarizedCoefficientMap g.toRingHom).comp σ)) : f = g := by
  have hm := polarizedStrictlyConjugate_identityMatrices rA
    (((polarizedCoefficientMap f.toRingHom).comp σ).comp q)
    (((polarizedCoefficientMap g.toRingHom).comp σ).comp q)
    (fun h => (polarizedCoefficientMap_component f.toRingHom (σ (q h))).trans (hσ h))
    (fun h => (polarizedCoefficientMap_component g.toRingHom (σ (q h))).trans (hσ h))
    (polarizedStrictlyConjugate_comp rA _ _ hfg q)
  exact descendedTraceCoefficientMaps_eq rR ρ (polarizedIdentityMatrices (σ.comp q) hσ) hdesc
    f g hf hg rA hm

end
end Dubon2026
