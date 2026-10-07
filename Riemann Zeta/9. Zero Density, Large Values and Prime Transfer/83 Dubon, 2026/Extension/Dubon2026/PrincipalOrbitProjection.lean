import Dubon2026.PrincipalCyclicProjection

/-! # Orthogonal divisor projections on actual finite cusp orbits -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

/-- The orbit projection retains precisely the Fourier coefficients at divisible indices. -/
theorem principalOrbitDivisorProjection_coeff {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k)
    (v : principalCuspOrbit N k f) (n : ℕ) :
    principalCuspCoefficients (principalOrbitDivisorProjection hd k f v).val n =
      if d ∣ n then principalCuspCoefficients v.val n else 0 := by
  rw [principalOrbitDivisorProjection_val, principalDivisorProjection_coeff hd]

/-- These actual restricted operators are idempotent. -/
theorem principalOrbitDivisorProjection_idempotent {N d : ℕ} [NeZero d]
    (hd : d ∣ N) (k : ℤ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    IsIdempotentElem (principalOrbitDivisorProjection hd k f) :=
  finiteGroupProjection_idempotent _

/-- Actual divisor averages commute on the finite-dimensional orbit as well as on cusp forms. -/
theorem principalOrbitDivisorProjection_commute {N d e : ℕ}
    [NeZero N] [NeZero d] [NeZero e] (hd : d ∣ N) (he : e ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    Commute (principalOrbitDivisorProjection hd k f) (principalOrbitDivisorProjection he k f) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (principalOrbitDivisorProjection hd k f
    (principalOrbitDivisorProjection he k f v)).val =
      (principalOrbitDivisorProjection he k f (principalOrbitDivisorProjection hd k f v)).val
  simp only [principalOrbitDivisorProjection_val]
  exact LinearMap.congr_fun (principalDivisorProjection_commute hd he k).eq v.val

/-- One positive invariant core makes all actual divisor averages symmetric simultaneously.
This auxiliary inner product is obtained from the genuine finite slash orbit. -/
theorem principalOrbitDivisorProjection_commonCore (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ∃ c : InnerProductSpace.Core ℂ (principalCuspOrbit N k f),
      ∀ (d : ℕ) [NeZero d] (hd : d ∣ N) (x y : principalCuspOrbit N k f),
        c.inner (principalOrbitDivisorProjection hd k f x) y =
          c.inner x (principalOrbitDivisorProjection hd k f y) := by
  obtain ⟨c, hc⟩ := principalCuspOrbit_invariantCore N k f
  refine ⟨c, ?_⟩
  intro d _ hd x y
  letI := c
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := principalCuspOrbit N k f)
  letI := InnerProductSpace.ofCore c.toCore
  exact (finiteCyclicProjection_symmetric (principalCuspOrbitRepresentation N k f)
    hc d (principalCyclicGenerator N d) (principalCyclicGenerator_pow hd)).isSymmetric x y

end
end Dubon2026
