import Dubon2026.PolarizedQuotientRepresentation
import Dubon2026.PolarizedLocalCoefficientQuotient
import Dubon2026.FixedResidualFramedUniversality

/-! The literal polarized quotient of the existing all-relation framed
coefficient ring for the original residual representation. This is an
actual consumer of native framed universality for DUB-17's CM route.
The original profinite group, residual representation, generating set
and residual-compatible similitude remain explicit arithmetic inputs. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  (p : ℕ) (H : ProfiniteGrp.{u})
  (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)

/-- The actual native framed coefficient ring modulo its literal polarized source relations. -/
@[irreducible] def FixedResidualPolarizedCoefficientRing : Type u :=
  FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S ⧸
    representationPolarizedIdeal
      (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
      (polarizedComponent.comp σ)
      ((Units.map (algebraMap O
        (FixedResidualFramedCoefficientRing p H (polarizedBlockRepresentation.comp σ) hσ S))).comp ν)

/-- The original quotient ring operations on the polarized coefficient ring. -/
instance fixedResidualPolarizedCommRing :
    CommRing (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing
  infer_instance

/-- The original coefficient-base algebra structure of the same quotient. -/
instance fixedResidualPolarizedAlgebra :
    Algebra O (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
  exact Ideal.Quotient.algebra O

/-- The original quotient topology, retained on the same polarized coefficient type. -/
instance fixedResidualPolarizedTopologicalSpace :
    TopologicalSpace (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing
  infer_instance

/-- The source quotient operations are continuous in its original quotient topology. -/
instance fixedResidualPolarizedIsTopologicalRing :
    IsTopologicalRing (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedTopologicalSpace
  exact topologicalRing_quotient _

/-- Original residual compatibility derives locality and nontriviality of this same polarized quotient. -/
theorem fixedResidualPolarizedCoefficientRing_isLocal
    (hν : ∀ g, polarizedSimilitude (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g)) :
    IsLocalRing (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν) := by
  unfold FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
  letI := fixedResidualFramedCoefficientRing_isLocal p H (polarizedBlockRepresentation.comp σ) hσ S
  let eR := fixedResidualFramedCoefficientResidueEquiv p H (polarizedBlockRepresentation.comp σ) hσ S
  exact representationPolarizedQuotient_isLocal_of_residue eR
    (fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS)
    σ (fun g => DFunLike.congr_fun
      (fixedResidualFramedUniversalRepresentation_residue p H
        (polarizedBlockRepresentation.comp σ) hσ S hS) g) ν hν

end
end Dubon2026
