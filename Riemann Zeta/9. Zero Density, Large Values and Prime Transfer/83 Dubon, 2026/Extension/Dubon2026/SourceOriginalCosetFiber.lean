import Dubon2026.SourceOriginalAnalyticRamification
import Dubon2026.SourceLevelEllipticCosets
import Dubon2026.SourceLevelProjectiveCosets
import Mathlib.GroupTheory.GroupAction.Quotient

/-! DUB-17/18 -> numerical modular genus -> exceptional finite fibers.
Map actual level cosets to original finite places at a chosen analytic
j-value. Exhaustion and full j-orbit separation prove surjectivity.
The full stabilizer acts inside each fiber. Its orbit sizes will be
compared with the already proved original place orders and total degree,
avoiding an independent modular-form point-separation construction.
-/
namespace Dubon2026.SourceFunctionField.FiberOrbits
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

/-- Actual level cosets, with the full modular group acting on the left. -/
abbrev X (N : ℕ) := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

/-- The actual positive original j-fiber at the chosen analytic value. -/
abbrev Fiber (N : ℕ) (τ : ℍ) :=
  {P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) //
    0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf τ))}

/-- The original analytic place of the inverse translate lies in this fiber. -/
def point (N : ℕ) [NeZero N] (τ : ℍ) (g : SL(2, ℤ)) : Fiber N τ :=
  ⟨originalAnalyticPlace N (g⁻¹ • τ), by
    have h := originalAnalyticPlace_j_sub_pos N (g⁻¹ • τ)
    change 0 < (originalAnalyticPlace N (g⁻¹ • τ)).ord
      (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) (JMultiplicity.jf (g⁻¹ • τ))) at h
    rwa [JMultiplicity.jf_smul] at h⟩

theorem point_eq_of_leftRel (N : ℕ) [NeZero N] (τ : ℍ) (a b : SL(2, ℤ))
    (hab : QuotientGroup.leftRel (CongruenceSubgroup.Gamma0 N) a b) :
    point N τ a = point N τ b := by
  have hmem := QuotientGroup.leftRel_apply.mp hab
  let δ : CongruenceSubgroup.Gamma0 N := ⟨a⁻¹ * b, hmem⟩
  have he : b⁻¹ • τ = ((δ⁻¹ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • (a⁻¹ • τ) := by
    simp only [δ, Subgroup.coe_inv, mul_inv_rev, inv_inv, ← mul_smul, mul_assoc,
      mul_inv_cancel, mul_one]
  apply Subtype.ext
  change originalAnalyticPlace N (a⁻¹ • τ) = originalAnalyticPlace N (b⁻¹ • τ)
  rw [he, originalAnalyticPlace_smul]

/-- Map the actual level coset to its original finite place. -/
def toFiber (N : ℕ) [NeZero N] (τ : ℍ) : X N → Fiber N τ :=
  Quotient.lift (point N τ) (point_eq_of_leftRel N τ)

theorem toFiber_mk (N : ℕ) [NeZero N] (τ : ℍ) (g : SL(2, ℤ)) :
    toFiber N τ (g : X N) = point N τ g := rfl

theorem toFiber_surjective (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Surjective (toFiber N τ) := by
  rintro ⟨P, hP⟩
  obtain ⟨g, hg⟩ := original_finite_fiber_full_orbit N P τ hP
  refine ⟨(g⁻¹ : SL(2, ℤ)), ?_⟩
  apply Subtype.ext
  change originalAnalyticPlace N ((g⁻¹)⁻¹ • τ) = P
  simpa only [inv_inv] using hg

scoped instance fiberFinite (N : ℕ) [NeZero N] (τ : ℍ) : Finite (Fiber N τ) :=
  Finite.of_surjective (toFiber N τ) (toFiber_surjective N τ)

theorem toFiber_stabilizer_smul (N : ℕ) [NeZero N] (τ : ℍ)
    (k : MulAction.stabilizer SL(2, ℤ) τ) (x : X N) :
    toFiber N τ ((k : SL(2, ℤ)) • x) = toFiber N τ x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    change originalAnalyticPlace N (((k : SL(2, ℤ)) * g)⁻¹ • τ) =
      originalAnalyticPlace N (g⁻¹ • τ)
    have hk : (k : SL(2, ℤ))⁻¹ • τ = τ := inv_smul_eq_iff.mpr k.2.symm
    rw [mul_inv_rev, mul_smul, hk]

end
end Dubon2026.SourceFunctionField.FiberOrbits
