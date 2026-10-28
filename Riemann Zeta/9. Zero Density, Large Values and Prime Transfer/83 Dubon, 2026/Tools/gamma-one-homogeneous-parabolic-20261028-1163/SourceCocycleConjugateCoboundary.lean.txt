import Dubon2026.SourceSemilinearCohomology
import Mathlib.Tactic

/-! DUB17/18 -> original all-weight association -> integral parabolic
character descent -> one denominator over the finite original cusp
orbits. Transport the actual local coboundary witness by conjugation.
The later cusp-orbit consumer uses this with the original binary action
over Z, preserving integrality of the transported witness. -/
namespace Dubon2026
noncomputable section
open groupCohomology

theorem sourceCocycle_conjugate_coboundary
    {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (c : cocycles₁ A) (h g : G) (v : A) (hv : c g = A.ρ g v - v) :
    c (h * g * h⁻¹) =
      A.ρ (h * g * h⁻¹) (A.ρ h v - c h) - (A.ρ h v - c h) := by
  have hi := congrArg (A.ρ h⁻¹) (cocycles₁_map_inv c h)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply, map_neg] at hi
  rw [(mem_cocycles₁_iff c).mp c.property,
    (mem_cocycles₁_iff c).mp c.property, hv, hi]
  simp only [map_sub, map_neg, ← Module.End.mul_apply, ← map_mul,
    mul_assoc, inv_mul_cancel, mul_one]
  abel

end
end Dubon2026
