import Dubon2026.SourceEllipticStabilizerOrbits

/-! DUB-17/18 -> numerical modular genus -> exact exceptional fibers.
The original finite-place bijection transfers the already proved Manin
orbit counts and literal quadratic-root fixed-coset counts to the actual
j-fibers at zero and 1728. No fiber cardinality premise is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane FiberOrbits
open scoped MatrixGroups

theorem two_mul_card_analytic_fiber_I (N : ℕ) [NeZero N] :
    2 * Nat.card (Fiber N UpperHalfPlane.I) =
      SourceLevelProjective.dedekindPsi N + SourceLevelProjective.nuTwo N := by
  have hc : Nat.card (Fiber N UpperHalfPlane.I) = Nat.card (SourceManin.Orb (SourceManin.sig2 N)) :=
    (Nat.card_congr (Equiv.ofBijective _ (orbitToFiber_bijective N UpperHalfPlane.I))).symm.trans
      (Nat.card_congr (orbitEquivSigTwo N))
  have h := SourceManin.two_mul_natCard_orb (SourceManin.sig2 N) (SourceManin.sig2_sq N)
  have hi : Nat.card (SourceManin.X N) = SourceLevelProjective.dedekindPsi N :=
    SourceLevelProjective.gamma0_index N
  have hf : Nat.card {x : SourceManin.X N // SourceManin.sig2 N x = x} =
      SourceLevelProjective.nuTwo N := SourceElliptic.card_fixed_S N
  rwa [← hc, hi, hf] at h

theorem three_mul_card_analytic_fiber_rho (N : ℕ) [NeZero N] :
    3 * Nat.card (Fiber N ρ) =
      SourceLevelProjective.dedekindPsi N + 2 * SourceLevelProjective.nuThree N := by
  have hc : Nat.card (Fiber N ρ) = Nat.card (SourceManin.Orb (SourceManin.sig3 N)) :=
    (Nat.card_congr (Equiv.ofBijective _ (orbitToFiber_bijective N ρ))).symm.trans
      (Nat.card_congr (orbitEquivSigThree N))
  have h := SourceManin.three_mul_natCard_orb (SourceManin.sig3 N) (SourceManin.sig3_cube N)
  have hi : Nat.card (SourceManin.X N) = SourceLevelProjective.dedekindPsi N :=
    SourceLevelProjective.gamma0_index N
  have hf : Nat.card {x : SourceManin.X N // SourceManin.sig3 N x = x} =
      SourceLevelProjective.nuThree N := SourceElliptic.card_fixed_ST N
  rwa [← hc, hi, hf] at h

theorem two_mul_card_original_j_1728_fiber (N : ℕ) [NeZero N] :
    2 * Nat.card {P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) //
      0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)} =
      SourceLevelProjective.dedekindPsi N + SourceLevelProjective.nuTwo N := by
  have h := two_mul_card_analytic_fiber_I N
  change 2 * Nat.card {P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) //
    0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (JMultiplicity.jf UpperHalfPlane.I))} = _ at h
  rwa [JMultiplicity.jf_eq_of_E₆_eq_zero JMultiplicity.E₆_I] at h

theorem three_mul_card_original_j_zero_fiber (N : ℕ) [NeZero N] :
    3 * Nat.card {P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) //
      0 < P.ord (jOver N ℂ)} =
      SourceLevelProjective.dedekindPsi N + 2 * SourceLevelProjective.nuThree N := by
  have h := three_mul_card_analytic_fiber_rho N
  change 3 * Nat.card {P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ) //
    0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (JMultiplicity.jf ρ))} = _ at h
  simpa only [JMultiplicity.jf_ρ, map_zero, sub_zero] using h

end
end Dubon2026.SourceFunctionField
