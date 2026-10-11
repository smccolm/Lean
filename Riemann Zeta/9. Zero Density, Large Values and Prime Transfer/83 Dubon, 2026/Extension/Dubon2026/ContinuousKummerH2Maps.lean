import Dubon2026.DiscreteKummerCoefficientContinuity
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # The actual continuous H2 maps of the original Kummer coefficient sequence -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Original continuous H2 of the actual discrete Galois unit representation,
with joint action continuity proved from its original Krull topology. -/
abbrev GaloisUnitContinuousH2 :=
  ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

/-- Original continuous H2 of the actual root-of-unity representation,
retaining its genuine discrete topology and original Galois action. -/
abbrev GaloisRootContinuousH2 :=
  ContinuousRepresentationH2 (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)

/-- The original root inclusion induces its actual map on continuous H2. -/
def galoisKummerH2Inclusion : GaloisRootContinuousH2 (K := K) (Ω := Ω) n →ₗ[ℤ]
    GaloisUnitContinuousH2 (K := K) (Ω := Ω) :=
  continuousCoefficientH2Map
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (Rep.ofAlgebraAutOnUnits K Ω)
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
    (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

/-- The original unit power map induces its actual continuous H2 endomorphism. -/
def galoisKummerH2Power : GaloisUnitContinuousH2 (K := K) (Ω := Ω) →ₗ[ℤ]
    GaloisUnitContinuousH2 (K := K) (Ω := Ω) :=
  continuousCoefficientH2Map (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω)
    (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerPower_continuous (K := K) (Ω := Ω) n)
    (Rep.hom_comm_apply (galoisKummerPower (K := K) (Ω := Ω) n))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

omit [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)] in
/-- The original H2 unit power map is exactly multiplication by n on the
original cohomology group, proved on the original continuous representatives. -/
theorem galoisKummerH2Power_eq_nsmul (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisKummerH2Power (K := K) (Ω := Ω) n x = n • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change (Submodule.Quotient.mk
      (continuousCoefficientCocycleTwoMap (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω)
        (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap
        (galoisKummerPower_continuous (K := K) (Ω := Ω) n)
        (Rep.hom_comm_apply (galoisKummerPower (K := K) (Ω := Ω) n)) c) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) = n • Submodule.Quotient.mk c
    have he : continuousCoefficientCocycleTwoMap
        (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω)
        (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap
        (galoisKummerPower_continuous (K := K) (Ω := Ω) n)
        (Rep.hom_comm_apply (galoisKummerPower (K := K) (Ω := Ω) n)) c = n • c := by
      apply Subtype.ext
      apply Subtype.ext
      funext z
      rfl
    rw [he, Submodule.Quotient.mk_smul]
    rfl

end
end Dubon2026
