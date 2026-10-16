import Dubon2026.OriginalGlobalOddH2Detection

/-! # Finite-place detection for actual odd-primary global H2

Induction on the annihilating prime power reuses the proved prime-torsion
detection theorem. This is the missing detection input for extending the
constructed rational splitting stage to the prime-power classes used in
DUB-17's full-order finite class-invariant construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

/-- An actual odd-primary global unit H2 class is detected by its literal
finite-prime localizations, with no infinite-place vanishing premise. -/
theorem originalGlobalUnitH2_zero_of_finite_at_odd_prime_power
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (n : ℕ)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hxq : q ^ n • x = 0)
    (hx : ∀ w : HeightOneSpectrum (𝓞 L), originalGlobalAdicH2 K L w x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa only [pow_zero, one_smul] using hxq
  | succ n ih =>
    have hqx : q • x = 0 := ih (q • x)
      (by rwa [← mul_smul, ← pow_succ])
      (by intro w; rw [map_nsmul, hx w, smul_zero])
    exact originalGlobalUnitH2_zero_of_finite_at_odd_prime K L q hq hq2 x hqx hx

end
end Dubon2026
