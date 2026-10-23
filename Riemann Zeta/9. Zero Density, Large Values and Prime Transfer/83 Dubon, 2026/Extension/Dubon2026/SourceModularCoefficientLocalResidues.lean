import Dubon2026.SourceCurveCanonicalResidueData
import Dubon2026.SourceModularCoefficientResidue

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> canonical
degree and residue duality. Reuse the existing local-residue and Weil-rank
proofs on the actual modular coefficient field. The residue constants,
canonical support and finite divisor-space maxima are proved in every
characteristic. Global residue vanishing remains a separate obligation;
no such vanishing is assumed or claimed here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [IsAlgClosed L]

/-- The actual canonical local residue data at a coefficient-field place. -/
def coeffCanonicalLocalResidueData (v : Place L (modularFunctionFieldCoeff N L)) :
    v.CanonicalLocalResidueDataK :=
  v.canonicalLocalResidueData (coeff_place_residue_algebraMap_bijective N L v).surjective

theorem coeff_canonicalLocalResidue_unique
    (v : Place L (modularFunctionFieldCoeff N L)) (d : v.CanonicalLocalResidueDataK) :
    d.res = (coeffCanonicalLocalResidueData N L v).res :=
  v.canonicalLocalResidueData_res_unique (coeff_place_residue_algebraMap_bijective N L v) d

theorem coeff_canonicalLocalResidue_simplePole
    (v : Place L (modularFunctionFieldCoeff N L)) (f : modularFunctionFieldCoeff N L)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    (coeffCanonicalLocalResidueData N L v).res f =
      IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ :=
  (coeffCanonicalLocalResidueData N L v).res_simplePole f hf

end
end Dubon2026.SourceFunctionField
