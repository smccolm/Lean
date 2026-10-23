import Dubon2026.SourceCurveLocalTateDerivation
import Dubon2026.SourceCurveTateResidueAgreement
import Dubon2026.SourceCurveGlobalResidueMap
import Dubon2026.SourceCurveResidueSumEquiv

/-! The actual Tate pairing equals the canonical differential residue,
and its global support is finite when the already constructed principal
and differential divisors have finite support. This connects the local
trace proof to the global residue sum required for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The Tate pairing is exactly the canonical residue of the literal differential. -/
theorem Place.tateResidue_eq_canonical_differential (v : Place K F)
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates]
    (d : v.CanonicalLocalResidueDataK)
    (hres : Function.Bijective (algebraMap K v.ResidueField)) (f g : F) :
    v.tateResidue f g = Algebra.trace K v.ResidueField
      (d.res (f * v.differentialCoeff (D K F g))) := by
  rw [v.tateResidue_eq_differentialCoeff hres.surjective,
    v.tateResidue_uniformizer hres.surjective, v.trace_canonicalResidue_eq_scalar d hres]

/-- The finite divisor supports bound the support of the actual Tate pairing. -/
theorem tateResidue_support_finite [Nontrivial Ω[F⁄K]]
    [∀ v : Place K F, v.DCoordGenerates]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (f g : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite)
    (hg : {v : Place K F | v.ordDifferential (D K F g) ≠ 0}.Finite) :
    (Function.support (fun v : Place K F => v.tateResidue f g)).Finite := by
  have he : (fun v : Place K F => v.tateResidue f g) =
      kaehlerResidueTermKFam Rfam (D K F g) (diagonalHom K F f) := by
    funext v
    exact v.tateResidue_eq_canonical_differential (Rfam v) (hres v) f g
  rw [he]
  exact diagonal_residue_support_finite Rfam _ f hf hg

end Dubon2026.SourceCurve
