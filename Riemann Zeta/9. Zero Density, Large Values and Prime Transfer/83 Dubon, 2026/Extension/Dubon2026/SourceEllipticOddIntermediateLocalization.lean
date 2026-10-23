import Dubon2026.SourceEllipticKernelLocalCoordinates
import Dubon2026.SourceEllipticOddIntermediateFinite

/-! The actual common integral closure is precisely the original affine
coordinate ring with the actual kernel denominator inverted. This permits
evaluation away from the kernel and identifies the point ideals that vanish
under extension. It supplies the ring input to the proved norm-map coordinate
formula and exact cyclic kernel (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Dubon2026.SourceEllipticClassGroup

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- Every actual quotient coordinate function is regular on the original kernel localization. -/
theorem oddCoordinatePullback_mem_kernelLocalRing (hQ : addOrderOf Q = 2 * n + 1)
    (z : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing) :
    oddCoordinatePullback W hQ z ∈ kernelLocalRing W (oddOrderSummingSet W Q n) := by
  let T := (kernelLocalRing W (oddOrderSummingSet W Q n)).restrictScalars F
  have hr := coordinateAlgHom_range (oddCoordinatePullback W hQ)
  rw [oddCoordinatePullback_X, oddCoordinatePullback_Y] at hr
  have hle : Algebra.adjoin F ({genericVeluX W (oddOrderSummingSet W Q n),
      genericVeluY W (oddOrderSummingSet W Q n)} : Set W.toAffine.FunctionField) ≤ T := by
    apply Algebra.adjoin_le
    rintro _ (rfl | rfl)
    · exact genericVeluX_mem_kernelLocalRing W _
    · exact genericVeluY_mem_kernelLocalRing W _
  apply hle
  rw [← hr]
  exact ⟨z, rfl⟩

/-- The concrete kernel localization embeds in the actual common integral closure. -/
theorem kernelLocalRing_le_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    (kernelLocalRing W (oddOrderSummingSet W Q n)).toSubring ≤ oddIntermediateRing W hQ := by
  letI := oddCoordinateAlgebra W hQ
  let T : Subalgebra W.toAffine.CoordinateRing W.toAffine.FunctionField :=
    { oddIntermediateRing W hQ with
      algebraMap_mem' := isIntegral_coordinate_oddCoordinate W hQ }
  have hi : (aeval (genericX W.toAffine) (hP (oddOrderSummingSet W Q n) Prod.fst))⁻¹ ∈ T :=
    isIntegral_oddCoordinate_of_polynomial W hQ (isIntegral_odd_kernel_inverse hQ)
  exact kernelLocalRing_le W _ T hi

variable [IsAlgClosed F]

/-- The actual common integral closure is exactly the original coordinate ring localized away from the kernel. -/
theorem oddIntermediateRing_eq_kernelLocalRing (hQ : addOrderOf Q = 2 * n + 1) :
    oddIntermediateRing W hQ = (kernelLocalRing W (oddOrderSummingSet W Q n)).toSubring := by
  apply le_antisymm _ (kernelLocalRing_le_oddIntermediateRing W hQ)
  letI := oddCoordinateAlgebra W hQ
  let T := kernelLocalRing W (oddOrderSummingSet W Q n)
  letI := isDedekindDomain_of_isAlgClosed' (W := W.toAffine)
  letI := isLocalization_kernelLocalRing W (oddOrderSummingSet W Q n)
  letI : IsIntegrallyClosed T := isIntegrallyClosed_of_isLocalization T
    (Submonoid.powers (kernelCoordinate W (oddOrderSummingSet W Q n)))
    (kernelCoordinate_powers_le W (oddOrderSummingSet W Q n))
  intro z hz
  change IsIntegral (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing z at hz
  have hi : IsIntegral T z := hz.map_of_comp_eq
    ((oddCoordinatePullback W hQ).toRingHom.codRestrict T (oddCoordinatePullback_mem_kernelLocalRing W hQ))
    (RingHom.id W.toAffine.FunctionField) rfl
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hu ▸ u.property

end Dubon2026.SourceEllipticFunctionField
