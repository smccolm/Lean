import Dubon2026.SourceCurveRegularProlongation
import Dubon2026.SourceCurveRepartitions
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
reduction on divisor classes. This is the source constant-reduction object:
the actual coefficient valuation and residue map together with a degree-
preserving place map compatible with all principal order divisors.
The actual modular construction is proved separately; this structure alone
does not establish existence or genus preservation. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_ConstantReduction. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- Actual coefficient reduction with a compatible degree-preserving map of places. -/
structure ConstantReduction extends RegularProlongation A F Fbar where
  /-- Reduction of original normalized places. -/
  placeMap : Place L F → Place (ResidueField A) Fbar
  /-- The map preserves the actual residue-field degree of every place. -/
  deg_placeMap : ∀ P, Module.finrank (ResidueField A) (placeMap P).ResidueField =
    Module.finrank L P.ResidueField
  /-- Principal divisors push forward to the divisor of the actual reduced function. -/
  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

variable {A F Fbar}

/-- Construct a constant reduction from its actual place map and closed place residues. -/
def ConstantReduction.ofPlaceMap (R : RegularProlongation A F Fbar)
    (r : Place L F → Place (ResidueField A) Fbar)
    (hF : ∀ P : Place L F, Function.Bijective (algebraMap L P.ResidueField))
    (hFb : ∀ Q : Place (ResidueField A) Fbar,
      Function.Bijective (algebraMap (ResidueField A) Q.ResidueField))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F,
      (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f)) :
    ConstantReduction A F Fbar where
  toRegularProlongation := R
  placeMap := r
  deg_placeMap := fun P => (Module.finrank_of_bijective_algebraMap (hFb (r P))).trans
    (Module.finrank_of_bijective_algebraMap (hF P)).symm
  mapDomain_placeMap := hdiv


end
end Dubon2026.SourceCurve
