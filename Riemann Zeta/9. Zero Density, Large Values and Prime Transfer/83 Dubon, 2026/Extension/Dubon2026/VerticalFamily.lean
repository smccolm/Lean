import Dubon2026.LogTruncation

/-! # The compact family of actual prime twists of a Dirichlet polynomial -/

namespace Dubon2026

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Actual coefficient twist by the prime-factorization character, without changing support. -/
def twistedCoefficients (a : ℕ → ℂ) (N : ℕ) (z : PrimeTorus N) (n : ℕ) : ℂ :=
  a n * bohrMonomial N n (fun p => fourier 1 (z p))

theorem twistedCoefficients_one (a : ℕ → ℂ) (N : ℕ) (z : PrimeTorus N) :
    twistedCoefficients a N z 1 = a 1 := by
  simp [twistedCoefficients, bohrMonomial]

theorem bohrMonomial_mul (N n : ℕ) (z w : PrimeCoordinate N → ℂ) :
    bohrMonomial N n (fun p => z p * w p) = bohrMonomial N n z * bohrMonomial N n w := by
  simp only [bohrMonomial, mul_pow, Finset.prod_mul_distrib]

theorem fourier_one_add (z w : UnitAddCircle) :
    fourier 1 (z + w) = fourier 1 z * fourier 1 w := by
  simp only [fourier_one, AddCircle.toCircle_add, Circle.coe_mul]

theorem bohrOnTorus_add_twist (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z w : PrimeTorus N) :
    bohrOnTorus a N σ (z + w) = bohrOnTorus (twistedCoefficients a N z) N σ w := by
  simp only [bohrOnTorus, ContinuousMap.coe_mk, bohrLift, Pi.add_apply, fourier_one_add,
    bohrMonomial_mul, twistedCoefficients]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Vertical restriction for every prime twist, using the original complex powers. -/
def verticalFamily (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) : ℂ :=
  dirichletSum (twistedCoefficients a N z) N ((σ : ℂ) + Complex.I * t)

theorem verticalFamily_eq_torus_translate (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (z : PrimeTorus N) (t : ℝ) :
    verticalFamily a N σ z t = bohrOnTorus a N σ (z + primeTorusFlow N t) := by
  rw [bohrOnTorus_add_twist, bohrOnTorus_verticalFlow]
  rfl

theorem analyticAt_verticalFamily (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    AnalyticAt ℝ (verticalFamily a N σ z) t :=
  analyticAt_vertical_dirichletSum (twistedCoefficients a N z) N σ t

theorem verticalFamily_ne_zero_ae {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (σ : ℝ) (z : PrimeTorus N) : ∀ᵐ t : ℝ, verticalFamily a N σ z t ≠ 0 := by
  apply vertical_dirichletSum_ne_zero_ae hN
  rwa [twistedCoefficients_one]

theorem analyticOrderAt_verticalFamily_ne_top {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    analyticOrderAt (verticalFamily a N σ z) t ≠ ⊤ := by
  intro h
  have han : AnalyticOnNhd ℝ (verticalFamily a N σ z) Set.univ :=
    fun u _ => analyticAt_verticalFamily a N σ z u
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ t) (analyticOrderAt_eq_top.mp h)
  obtain ⟨u, hu⟩ := (verticalFamily_ne_zero_ae hN ha σ z).exists
  exact hu (hz (Set.mem_univ u))

theorem exists_nonzero_verticalFamily_jet {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    ∃ k : ℕ, iteratedDeriv k (verticalFamily a N σ z) t ≠ 0 := by
  by_contra h
  push Not at h
  apply analyticOrderAt_verticalFamily_ne_top hN ha σ z t
  apply ENat.eq_top_iff_forall_ge.mpr
  intro k
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (analyticAt_verticalFamily a N σ z t)).mpr (fun i _ => h i)

end

end Dubon2026
