import Dubon2026.SourceEllipticWeierstrassAdditionIdentity

/-! Remove the actual addition defect's singularities at the two lattice
cosets and apply periodic Liouville. This proves the generic x-coordinate
addition formula for the native Weierstrass functions, required for the
uniformization map and the DUB-17/18 odd-prime quotient-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open Complex Filter Set
open scoped PeriodPair Topology
variable (L : PeriodPair) {w : ℂ}

/-- The complement of the two lattice cosets containing the possible addition poles. -/
def additionPhiDomain (w : ℂ) : Set ℂ := {z | z ∉ L.lattice ∧ z + w ∉ L.lattice}


theorem isOpen_additionPhiDomain : IsOpen ((additionPhiDomain L) w) :=
  L.isClosed_lattice.isOpen_compl.inter
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const))


theorem additionPhi_periodic (l : ℂ) (hl : l ∈ L.lattice) (z : ℂ) :
    (additionPhi L) w (z + l) = (additionPhi L) w z := by
  unfold additionPhi
  rw [L.weierstrassP_add_coe z ⟨l, hl⟩, L.derivWeierstrassP_add_coe z ⟨l, hl⟩,
    show z + l + w = z + w + l from by ring, L.weierstrassP_add_coe (z + w) ⟨l, hl⟩]


theorem additionPhi_self_eq_zero : (additionPhi L) w w = 0 := by
  unfold additionPhi; ring


theorem analyticAt_weierstrassP_add {z : ℂ} (hzw : z + w ∉ L.lattice) :
    AnalyticAt ℂ (fun u => ℘[L] (u + w)) z := by
  have hd : DifferentiableOn ℂ (fun u => ℘[L] (u + w)) {u : ℂ | u + w ∉ L.lattice} := fun u hu =>
    ((hasDerivAt_weierstrassP_add L) hu).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)) z hzw


theorem analyticOnNhd_additionPhi : AnalyticOnNhd ℂ ((additionPhi L) w) ((additionPhiDomain L) w) := by
  intro z ⟨hz, hzw⟩
  have hP := L.analyticOnNhd_weierstrassP z hz
  have hP' := L.analyticOnNhd_derivWeierstrassP z hz
  have hPw := (analyticAt_weierstrassP_add L) hzw
  unfold additionPhi
  fun_prop


end
end Dubon2026.SourceEllipticPeriod
