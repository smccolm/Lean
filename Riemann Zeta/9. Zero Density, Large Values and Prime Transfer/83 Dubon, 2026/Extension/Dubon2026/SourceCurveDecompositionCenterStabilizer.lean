import Dubon2026.SourceCurveGaloisPlaceCenter

/-! The native decomposition group of the actual valuation ring is the
stabilizer of its center on the actual integral-closure chart. This exact
group identification lets the pinned Dedekind Galois cardinality theorem
serve the missing inertia/order comparison in DUB-17/18. -/
namespace Dubon2026.SourceCurve.Place
open IsDedekindDomain IsLocalRing
open scoped Pointwise
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem decomposition_eq_center_stabilizer (w : Place K E) :
    letI := IsIntegralClosure.MulSemiringAction (w.restrict F).toValuationSubring F E
      (integralClosureAt E (w.restrict F))
    w.toValuationSubring.decompositionSubgroup F =
      MulAction.stabilizer (E ≃ₐ[F] E) (fiberCenter (F := F) E (w := w) rfl).asIdeal := by
  let v := w.restrict F
  let R := integralClosureAt E v
  letI := IsIntegralClosure.MulSemiringAction v.toValuationSubring F E R
  let P := (fiberCenter (F := F) E (w := w) rfl).asIdeal
  ext σ
  rw [mem_decomposition_iff_comapEquiv_eq, MulAction.mem_stabilizer_iff]
  have hcomp : P.comap (galRestrict v.toValuationSubring F E R σ).toRingHom = σ⁻¹ • P := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    rfl
  have hcenter : (fiberCenter E (restrict_comapEquiv_galois w σ)).asIdeal = P ↔
      w.comapEquiv (σ.restrictScalars K) = w := by
    constructor
    · intro h
      have h' : fiberCenter E (restrict_comapEquiv_galois w σ) =
          fiberCenter (F := F) E (w := w) rfl := HeightOneSpectrum.ext h
      have hh := congrArg (fiberPrimePlace E v) h'
      simpa only [fiberPrimePlace_fiberCenter] using hh
    · intro h
      change center R (w.comapEquiv (σ.restrictScalars K)) _ = center R w _
      ext x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rw [(w.comapEquiv (σ.restrictScalars K)).mem_center_iff_ord_pos _ hx,
        w.mem_center_iff_ord_pos _ hx, h]
  rw [← hcenter, fiberCenter_comapEquiv_galois, hcomp, inv_smul_eq_iff, eq_comm]

end
end Dubon2026.SourceCurve.Place
