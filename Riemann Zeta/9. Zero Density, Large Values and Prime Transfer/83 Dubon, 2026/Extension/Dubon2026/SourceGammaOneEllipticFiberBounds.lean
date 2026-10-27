import Dubon2026.SourceGammaOneEllipticCosetFiber
import Dubon2026.SourceGammaOneRealManinDimension
import Dubon2026.SourceEllipticStabilizerOrbits

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> genus lower
bound. The actual elliptic fibers are quotients of the already counted
S and ST orbits on signed cosets. Only the cardinal upper bounds required
by the genus inequality are proved; all counts refer to the original field. -/
namespace Dubon2026.SourceFunctionField.GammaOne.EllipticCounting
noncomputable section
open UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped MatrixGroups GammaOne
variable (N : ℕ) [NeZero N] (hT : T ∈ Gamma1 N)

include hT in
theorem two_mul_card_fiber_I_le :
    2 * Nat.card (AnalyticFiberOrbits.Fiber N UpperHalfPlane.I) ≤
      (plusMinus (Gamma1 N)).index +
        Nat.card {x : CuspCounting.Cosets (Gamma1 N) // S • x = x} := by
  have hS : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    change S ∈ MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I
    rw [FiberOrbits.stabilizer_I_eq_zpowers]
    exact Subgroup.mem_zpowers _
  have hc := card_fiber_le_cyclic_orbits N hT UpperHalfPlane.I S hS
  change Nat.card (AnalyticFiberOrbits.Fiber N UpperHalfPlane.I) ≤
    Nat.card (SourceManin.Orb (RealManin.sig2 (plusMinus (Gamma1 N)))) at hc
  have hr := SourceManin.two_mul_natCard_orb (RealManin.sig2 (plusMinus (Gamma1 N)))
    (RealManin.sig2_sq _ (neg_one_mem_plusMinus (Gamma1 N)))
  change 2 * Nat.card (SourceManin.Orb (RealManin.sig2 (plusMinus (Gamma1 N)))) =
    (plusMinus (Gamma1 N)).index +
      Nat.card {x : CuspCounting.Cosets (Gamma1 N) // S • x = x} at hr
  omega

include hT in
theorem three_mul_card_fiber_rho_le :
    3 * Nat.card (AnalyticFiberOrbits.Fiber N ρ) ≤
      (plusMinus (Gamma1 N)).index +
        2 * Nat.card {x : CuspCounting.Cosets (Gamma1 N) // (S * T) • x = x} := by
  have hST : (S * T) • ρ = ρ := by
    change (S * T) ∈ MulAction.stabilizer SL(2, ℤ) ρ
    rw [FiberOrbits.stabilizer_rho_eq_zpowers]
    exact Subgroup.mem_zpowers _
  have hc := card_fiber_le_cyclic_orbits N hT ρ (S * T) hST
  change Nat.card (AnalyticFiberOrbits.Fiber N ρ) ≤
    Nat.card (SourceManin.Orb (RealManin.sig3 (plusMinus (Gamma1 N)))) at hc
  have hr := SourceManin.three_mul_natCard_orb (RealManin.sig3 (plusMinus (Gamma1 N)))
    (RealManin.sig3_cube _ (neg_one_mem_plusMinus (Gamma1 N)))
  change 3 * Nat.card (SourceManin.Orb (RealManin.sig3 (plusMinus (Gamma1 N)))) =
    (plusMinus (Gamma1 N)).index +
      2 * Nat.card {x : CuspCounting.Cosets (Gamma1 N) // (S * T) • x = x} at hr
  omega

include hT in
theorem two_mul_card_j_1728_fiber_le :
    2 * Nat.card {P : SourceCurve.Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
      0 < P.ord (jCoordinateOver (Gamma1 N) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 N) ℂ) 1728)} ≤
      (plusMinus (Gamma1 N)).index +
        Nat.card {x : CuspCounting.Cosets (Gamma1 N) // S • x = x} := by
  have h := two_mul_card_fiber_I_le N hT
  change 2 * Nat.card {P : SourceCurve.Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
    0 < P.ord (jCoordinateOver (Gamma1 N) ℂ -
      algebraMap ℂ (functionFieldOver (Gamma1 N) ℂ) (JMultiplicity.jf UpperHalfPlane.I))} ≤ _ at h
  rwa [JMultiplicity.jf_eq_of_E₆_eq_zero JMultiplicity.E₆_I] at h

include hT in
theorem three_mul_card_j_zero_fiber_le :
    3 * Nat.card {P : SourceCurve.Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
      0 < P.ord (jCoordinateOver (Gamma1 N) ℂ)} ≤
      (plusMinus (Gamma1 N)).index +
        2 * Nat.card {x : CuspCounting.Cosets (Gamma1 N) // (S * T) • x = x} := by
  have h := three_mul_card_fiber_rho_le N hT
  change 3 * Nat.card {P : SourceCurve.Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
    0 < P.ord (jCoordinateOver (Gamma1 N) ℂ -
      algebraMap ℂ (functionFieldOver (Gamma1 N) ℂ) (JMultiplicity.jf ρ))} ≤ _ at h
  simpa only [JMultiplicity.jf_ρ, map_zero, sub_zero] using h

end
end Dubon2026.SourceFunctionField.GammaOne.EllipticCounting
