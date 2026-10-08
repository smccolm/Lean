import Dubon2026.SpectralEulerLogDerivative
import Dubon2026.PrimitiveSpectralBoundary

/-! # The actual incomplete symmetric-power Euler L-function and its boundary criterion

The function is constructed from the primitive form's own Hecke roots.
The local bound and nonvanishing holomorphic continuation are explicit
arithmetic inputs; their analytic Sato--Tate consequences are proved.
-/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The genuine incomplete symmetric-power Euler L-function of the primitive form, with only ramified primes omitted. -/
def primitiveSymmetricLFunction {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (s : ℂ) : ℂ :=
  spectralGlobalLSeries (primitiveSymmetricSpectralRoots f r) s

/-- The actual primitive symmetric-power Euler L-function is holomorphic in its convergence half-plane under the displayed local bound. -/
theorem primitiveSymmetricLFunction_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) :
    AnalyticOnNhd ℂ (primitiveSymmetricLFunction f r) {s : ℂ | 1 < s.re} :=
  spectralGlobalLSeries_analyticOnNhd (norm_primitiveSymmetricSpectralRoots_le f hbound r)

/-- No actual primitive symmetric-power Euler L-function vanishes on its genuine convergence half-plane. -/
theorem primitiveSymmetricLFunction_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) : primitiveSymmetricLFunction f r s ≠ 0 :=
  spectralGlobalLSeries_ne_zero (norm_primitiveSymmetricSpectralRoots_le f hbound r) hs

/-- The negative logarithmic derivative of the actual global primitive Euler L-function equals the already constructed genuine local derivative series. -/
theorem primitiveSymmetricLFunction_logDeriv {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (primitiveSymmetricLFunction f r) s = primitiveSymmetricLogSeries f r s :=
  spectralGlobalLSeries_logDeriv_eq_local (norm_primitiveSymmetricSpectralRoots_le f hbound r) hs

/-- A genuine nonvanishing holomorphic continuation of every actual positive symmetric-power Euler L-function gives the primitive Sato--Tate law, with the local bound and continuation displayed separately. -/
theorem primitive_satoTate_of_symmetric_L_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hcontinuation : ∀ r : ℕ, 0 < r → ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
      Set.EqOn F (primitiveSymmetricLFunction f r) {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  apply primitive_satoTate_of_symmetric_log_boundary f hbound
  intro r hr
  obtain ⟨F,hF,hne,hmatch⟩ := hcontinuation r hr
  refine ⟨fun s => -logDeriv F s, ?_, ?_⟩
  · have hd : ContinuousOn (deriv F) {s : ℂ | 1 ≤ s.re} := hF.deriv.continuousOn
    exact (hd.div hF.continuousOn hne).neg
  · intro s hs
    have he : F =ᶠ[𝓝 s] primitiveSymmetricLFunction f r :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
        (fun t ht => hmatch ht)
    change -logDeriv F s = primitiveSymmetricLogSeries f r s
    rw [logDeriv_apply, he.deriv_eq, hmatch hs]
    exact primitiveSymmetricLFunction_logDeriv f hbound r hs

end
end Dubon2026
