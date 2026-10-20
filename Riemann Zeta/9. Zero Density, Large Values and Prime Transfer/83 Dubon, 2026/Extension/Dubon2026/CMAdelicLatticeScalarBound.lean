import Dubon2026.CMHermitianTraceScalarBound
import Dubon2026.CMAdelicTraceFiniteGramClasses

/-! # A uniform scalar-action bound on every original integral trace lattice

The bound from the original complex embeddings transfers through the
proved exact cast of each integral trace restriction. No bound depending
on the adelic element or on a reduced basis is introduced. This supplies
the finite-column argument for DUB-17's compatible CM action matrices.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fixed original integral scalar has the same integral trace-form bound on every attached lattice. -/
theorem cmAdelicLattice_scalar_bound (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (d : ℤ) (hd : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j)) (a : 𝓞 K) :
    ∃ c : ℤ, 0 ≤ c ∧ ∀ (g : cmFiniteAdelicUnitaryGroup K H)
      (x : numberFieldAdelicLattice K ι g.val),
      cmAdelicLatticeIntegralTraceForm K H d hIntegral g (a • x) (a • x) ≤
        c * cmAdelicLatticeIntegralTraceForm K H d hIntegral g x x := by
  obtain ⟨c, hc, hscalar⟩ := cmHermitianTraceForm_scalar_bound K H hH (a : K)
  refine ⟨c, hc, ?_⟩
  intro g x
  have hs := mul_le_mul_of_nonneg_left (hscalar x.val)
    (show (0 : ℚ) ≤ (d : ℚ) by exact_mod_cast hd.le)
  have hcast :
      (cmAdelicLatticeIntegralTraceForm K H d hIntegral g (a • x) (a • x) : ℚ) ≤
        (c * cmAdelicLatticeIntegralTraceForm K H d hIntegral g x x : ℤ) := by
    rw [Int.cast_mul, cmAdelicLatticeIntegralTraceForm_cast,
      cmAdelicLatticeIntegralTraceForm_cast]
    change (d : ℚ) * cmHermitianRationalTraceForm K H ((a : K) • x.val) ((a : K) • x.val) ≤ _
    nlinarith
  exact_mod_cast hcast

end
end Dubon2026
