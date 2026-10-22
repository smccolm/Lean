import Dubon2026.SourceOriginalHeckeFiberOrbits
import Dubon2026.SourceHeckeCosetFiberCount

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
divisor formula. The actual quotient representatives enumerate each beta
fiber with multiplicity equal to its proved normalized ramification order.
This includes elliptic points and does not assume a free group action.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups Classical
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :=
  sourceHeckeUpperFintype N ℓ

/-- The actual inverse-dilation point attached to an upper Hecke coset. -/
def originalHeckeCosetPoint (τ : ℍ) (q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) : ℍ :=
  (levelRaiseMatrix ℓ)⁻¹ • (q.out.val⁻¹ • τ)

omit [NeZero N] in
theorem originalHeckeCosetPoint_dilation (τ : ℍ) (q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :
    levelRaiseMatrix ℓ • originalHeckeCosetPoint N ℓ τ q = q.out.val⁻¹ • τ :=
  smul_inv_smul _ _

theorem originalHeckeCosetPoint_restrict_beta (τ : ℍ)
    (q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :
    Place.restrictAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
      (originalAnalyticPlace (N * ℓ) (originalHeckeCosetPoint N ℓ τ q)) =
        originalAnalyticPlace N τ := by
  rw [originalAnalyticPlace_restrict_heckeBeta, originalHeckeCosetPoint_dilation]
  exact originalAnalyticPlace_smul N q.out⁻¹ τ

theorem originalHeckeBeta_ramification_eq_coset_card (τ w : ℍ)
    (g₀ : Gamma0 N) (hg₀ : g₀ • τ = levelRaiseMatrix ℓ • w) :
    Place.ramificationAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
        (originalAnalyticPlace (N * ℓ) w) =
      ((Finset.univ.filter fun q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ =>
        originalAnalyticPlace (N * ℓ) (originalHeckeCosetPoint N ℓ τ q) =
          originalAnalyticPlace (N * ℓ) w).card : ℤ) := by
  classical
  have hc := HeckeFiber.card_stabilizer_eq_coset_filter_mul
    (heckeUpperSubgroup N ℓ) τ (levelRaiseMatrix ℓ • w) g₀ hg₀
  have he : (Finset.univ.filter fun q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ =>
      originalAnalyticPlace (N * ℓ) (originalHeckeCosetPoint N ℓ τ q) =
        originalAnalyticPlace (N * ℓ) w) =
      Finset.univ.filter fun q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ =>
        q.out⁻¹ • τ ∈ MulAction.orbit (heckeUpperSubgroup N ℓ) (levelRaiseMatrix ℓ • w) := by
    apply Finset.filter_congr
    intro q _
    rw [originalAnalyticPlace_eq_iff_heckeUpper_orbit, originalHeckeCosetPoint_dilation]
    rfl
  rw [he]
  have hr := originalHeckeBeta_stabilizer_ramification N ℓ w
  have hp : 0 < (Nat.card (MulAction.stabilizer (heckeUpperSubgroup N ℓ)
      (levelRaiseMatrix ℓ • w)) : ℤ) := by
    rw [← originalHecke_stabilizer_card N ℓ,
      ← original_two_mul_ramification_eq_stabilizer_card (N * ℓ)]
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) (originalAnalyticRamification_pos (N * ℓ) w)
  have hc' := congrArg (fun n : ℕ => (n : ℤ)) hc
  push_cast at hc'
  nlinarith

end
end Dubon2026.SourceFunctionField
