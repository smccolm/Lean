import Dubon2026.ContinuousFiniteCohomologyVanishing
import Dubon2026.RationalArithmeticLocalRestrictionContinuity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Instances.ZMod

/-! # Vanishing of the actual real-place H2 at odd coefficient primes

The actual absolute Galois group is Gal(C/R), whose order is proved to be two.
Existing continuous averaging supplies the coboundary. This removes the real
H2 term for odd auxiliary primes in the DUB-17 reciprocity/Selmer chain; no
claim is made at characteristic two.
-/

namespace Dubon2026
noncomputable section

variable (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(ℂ/ℝ))
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(ℂ/ℝ) × A => A.ρ z.1 z.2))

/-- Every original continuous real-place H2 class vanishes when the actual
coefficient prime exceeds two, using the actual order-two Galois group. -/
theorem realPlaceFiniteCoefficientH2_eq_zero (hq : 2 < q)
    (x : ContinuousRepresentationH2 A hA) : x = 0 := by
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℝ ℂ := {}
  letI : Fintype Gal(ℂ/ℝ) := Fintype.ofFinite _
  have hc : Fintype.card Gal(ℂ/ℝ) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]
  have hn : (Fintype.card Gal(ℂ/ℝ) : ZMod q) ≠ 0 := by
    rw [hc]
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hq ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  exact continuousFiniteH2_eq_zero A hA hn x

end
end Dubon2026
