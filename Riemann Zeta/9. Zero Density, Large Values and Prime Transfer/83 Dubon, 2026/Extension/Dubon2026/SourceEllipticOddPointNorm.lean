import Dubon2026.SourceEllipticOddIntermediateFinite
import Dubon2026.SourceEllipticClassExtensionNorm
import Dubon2026.SourceEllipticClassSurjective

/-! An actual additive point map for the odd quotient, constructed by extending
ideals into the proved common ring and taking their relative norm. Every ring
action and finiteness property comes from the actual quotient. The downstream
SourceEllipticOddPointNormFormula and SourceEllipticOddKernelGeometry modules
prove its literal formulas and cyclic kernel on the DUB-17/18 dependency. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual quotient class norm, using its canonical source and target embeddings. -/
noncomputable def oddClassNorm (hQ : addOrderOf Q = 2 * n + 1) :
    ClassGroup W.toAffine.CoordinateRing →* ClassGroup (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing := by
  letI := isDedekindDomain_of_isAlgClosed' (W := W.toAffine)
  letI := isDedekindDomain_oddCoordinate W hQ
  letI := isDedekindDomain_oddIntermediateRing W hQ
  letI := oddIntermediateAlgebra W hQ
  letI := moduleFinite_oddIntermediateRing W hQ
  letI := isTorsionFree_oddIntermediateRing W hQ
  exact extendedClassNorm
    (R := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing)
    (oddSourceToIntermediate W hQ) (oddSourceToIntermediate_injective W hQ)

/-- The actual additive map on points induced by the odd quotient ideal norm. -/
noncomputable def oddPointNorm (hQ : addOrderOf Q = 2 * n + 1) :
    W.toAffine.Point →+ (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.Point := by
  letI := odd_quotient_isElliptic W Q hQ
  exact ((toClassEquiv (W := (veluQuotient W (oddOrderSummingSet W Q n)).toAffine)).symm.toAddMonoidHom.comp
    (oddClassNorm W hQ).toAdditive).comp (toClassEquiv (W := W.toAffine)).toAddMonoidHom

/-- The ideal class of the actual norm image is the actual extended relative ideal-class norm. -/
theorem toClass_oddPointNorm (hQ : addOrderOf Q = 2 * n + 1) (P : W.toAffine.Point) :
    (oddPointNorm W hQ P).toClass =
      Additive.ofMul (oddClassNorm W hQ (Additive.toMul P.toClass)) := by
  letI := odd_quotient_isElliptic W Q hQ
  rw [← toClassEquiv_apply]
  exact AddEquiv.apply_symm_apply _ _

/-- Equality of the norm image with a specified point is characterized by its actual ideal-class norm. -/
theorem oddPointNorm_eq_iff (hQ : addOrderOf Q = 2 * n + 1) (P : W.toAffine.Point)
    (R : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.Point) :
    oddPointNorm W hQ P = R ↔
      Additive.ofMul (oddClassNorm W hQ (Additive.toMul P.toClass)) = R.toClass := by
  letI := odd_quotient_isElliptic W Q hQ
  rw [← toClass_oddPointNorm]
  exact WeierstrassCurve.Affine.Point.toClass_injective.eq_iff.symm

end Dubon2026.SourceEllipticFunctionField
