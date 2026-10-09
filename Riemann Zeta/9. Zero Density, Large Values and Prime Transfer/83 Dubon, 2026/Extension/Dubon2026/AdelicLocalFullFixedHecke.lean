import Dubon2026.AdelicLocalFixedFullAwayClosure
import Dubon2026.AdelicLocalBoundedHecke
import Dubon2026.AdelicDistinctLocalHecke

/-! # Actual Hecke scalar action on the entire global local-fixed Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original normalized local Hecke operator commutes with the entire actual real-plus-away action. -/
theorem adelicLocalNormalizedHecke_fullAway_commute (p : ℕ) [NeZero p]
    (hp : p.Prime) (hpN : p.Coprime N)
    (a : AdelicFullAwayGroup (rationalPrimePlace p hp)) (x : AdelicCyclicHilbert f) :
    adelicLocalNormalizedHecke f p hp hpN (adelicCyclicFullAwayRepresentation f _ a x) =
      adelicCyclicFullAwayRepresentation f _ a (adelicLocalNormalizedHecke f p hp hpN x) := by
  simp only [adelicLocalNormalizedHecke, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  apply congrArg (fun y : AdelicCyclicHilbert f => (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • y)
  apply Finset.sum_congr rfl
  intro i _
  exact adelicCyclicLocal_fullAway_commute f _ _ a x

/-- The genuine local Hecke operator acts by the original Fourier eigenvalue on the whole actual full-complement cyclic closure. -/
theorem adelicLocalNormalizedHecke_fullAway_closure {p : ℕ} [NeZero p]
    (F : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p hp)).topologicalClosure) :
    adelicLocalNormalizedHecke F.toCuspForm p hp hpN x = normalizedCuspCoefficients F.toCuspForm p • x := by
  rw [← adelicBoundedLocalNormalizedHecke_apply]
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert F.toCuspForm)
    (AdelicFullAwayGroup (rationalPrimePlace p hp)) inferInstance inferInstance
    (adelicBoundedLocalNormalizedHecke F.toCuspForm p hp hpN) (normalizedCuspCoefficients F.toCuspForm p)
    (fun a => adelicCyclicFullAwayRepresentation F.toCuspForm _ a (adelicCyclicHilbertGenerator F.toCuspForm))
  · intro a
    rw [adelicBoundedLocalNormalizedHecke_apply, adelicLocalNormalizedHecke_fullAway_commute,
      adelicLocalNormalizedHecke_primitive_generator, map_smul]
  · exact hx

/-- Every vector in the entire original global local-integral-fixed space has the actual primitive Fourier Hecke eigenvalue. -/
theorem adelicLocalNormalizedHecke_full_fixed {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalNormalizedHecke F.toCuspForm p (Fact.out : p.Prime) hpN x =
      normalizedCuspCoefficients F.toCuspForm p • x := by
  apply adelicLocalNormalizedHecke_fullAway_closure F (Fact.out : p.Prime) hpN x
  exact (adelicLocalFixedSpace_eq_fullAwayClosure F hpN) ▸ hx

end
end Dubon2026
