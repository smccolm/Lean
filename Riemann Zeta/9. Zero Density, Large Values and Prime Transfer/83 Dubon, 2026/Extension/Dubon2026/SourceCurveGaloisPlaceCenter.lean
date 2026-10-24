import Dubon2026.SourceCurveFiberPrimes
import Dubon2026.SourceCurvePlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! Identify the actual Galois action on an extension place with the
action on its center in the integral-closure chart. The existing place
transport and exact center/prime correspondence are reused. This is the
necessary bridge from the native ideal decomposition-group cardinality
theorem to the actual inertia group in DUB-17/18 specialization; it does
not assume that group cardinality equals the normalized place order. -/
namespace Dubon2026.SourceCurve.Place
open IsDedekindDomain IsLocalRing
open scoped Pointwise
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

theorem restrict_comapEquiv_galois (w : Place K E) (σ : E ≃ₐ[F] E)
    [Algebra.IsIntegral F E] :
    (w.comapEquiv (σ.restrictScalars K)).restrict F = w.restrict F := by
  apply Place.ext
  ext x
  change σ (algebraMap F E x) ∈ w.toValuationSubring ↔
    algebraMap F E x ∈ w.toValuationSubring
  rw [σ.commutes]

theorem mem_decomposition_iff_comapEquiv_eq (w : Place K E) (σ : E ≃ₐ[F] E) :
    σ ∈ w.toValuationSubring.decompositionSubgroup F ↔
      w.comapEquiv (σ.restrictScalars K) = w := by
  have he : (w.comapEquiv (σ.restrictScalars K)).toValuationSubring =
      σ⁻¹ • w.toValuationSubring := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    rfl
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    apply Place.ext
    rw [he, inv_smul_eq_iff, h]
  · intro h
    have h' := congrArg Place.toValuationSubring h
    rw [he, inv_smul_eq_iff] at h'
    exact h'.symm

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem fiberCenter_comapEquiv_galois
    (w : Place K E) (σ : E ≃ₐ[F] E) :
    (fiberCenter E (restrict_comapEquiv_galois w σ)).asIdeal =
      ((fiberCenter E (w := w) rfl).asIdeal).comap
        (galRestrict (w.restrict F).toValuationSubring F E
          (integralClosureAt E (w.restrict F)) σ).toRingHom := by
  let v := w.restrict F
  let R := integralClosureAt E v
  let τ := galRestrict v.toValuationSubring F E R σ
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hτx : τ x ≠ 0 := by simpa only [map_zero] using τ.injective.ne hx
  change x ∈ center R (w.comapEquiv (σ.restrictScalars K)) _ ↔ τ x ∈ center R w _
  rw [(w.comapEquiv (σ.restrictScalars K)).mem_center_iff_ord_pos _ hx,
    w.mem_center_iff_ord_pos _ hτx, w.ord_comapEquiv]
  rw [algebraMap_galRestrict_apply]
  rfl

end
end Dubon2026.SourceCurve.Place
