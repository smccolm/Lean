import Dubon2026.SourceCurveCanonicalResidueData
import Dubon2026.SourceOriginalResidueFinite

/-! DUB-17/18 -> actual regular differential dimension -> Riemann--Roch
-> residue duality. Every actual original place has its canonical residue
map, uniquely determined by the source normalization. The proved bijective
base-to-residue map supplies rationality; no residue section or completion
is assumed. The global sum-of-residues theorem remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

/-- The actual canonical local residue data at an original-field place. -/
def originalCanonicalLocalResidueData (v : Place L (modularFunctionFieldOver N L)) :
    v.CanonicalLocalResidueDataK :=
  v.canonicalLocalResidueData (original_place_residue_algebraMap_bijective N L v).surjective

theorem original_canonicalLocalResidue_unique
    (v : Place L (modularFunctionFieldOver N L)) (d : v.CanonicalLocalResidueDataK) :
    d.res = (originalCanonicalLocalResidueData N L v).res :=
  v.canonicalLocalResidueData_res_unique (original_place_residue_algebraMap_bijective N L v) d

theorem original_canonicalLocalResidue_simplePole
    (v : Place L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver N L)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    (originalCanonicalLocalResidueData N L v).res f =
      IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ :=
  (originalCanonicalLocalResidueData N L v).res_simplePole f hf

end
end Dubon2026.SourceFunctionField
