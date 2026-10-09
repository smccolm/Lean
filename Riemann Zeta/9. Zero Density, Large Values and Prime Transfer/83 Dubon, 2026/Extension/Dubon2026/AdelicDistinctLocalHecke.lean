import Dubon2026.AdelicHeckeLocalBridge
import Dubon2026.AdelicLocalAwayFixed

/-! # Genuine local Hecke eigenbehavior on every distinct original cyclic component -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Original actions supported at distinct genuine finite places commute on the entire actual Hilbert space. -/
theorem adelicCyclicLocal_distinct_commute (v w : HeightOneSpectrum ℤ) (hvw : v ≠ w)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a : GeneralLinearGroup (Fin 2) (w.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f w a (adelicCyclicLocalRepresentation f v g x) =
      adelicCyclicLocalRepresentation f v g (adelicCyclicLocalRepresentation f w a x) := by
  have hc := ((finiteAdelicLocalGL2_commute_of_place_one v (finiteAdelicLocalGL2 w a)
    (finiteAdelicLocalGL2_ne w v hvw a) g).map rationalAdelicFiniteGL2Embedding).map
    (adelicCyclicHilbertRepresentation f)
  exact LinearMap.congr_fun hc.eq x

/-- The literal original normalized local Hecke sum as a bounded operator on the genuine Hilbert space. -/
def adelicBoundedLocalNormalizedHecke (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) •
    ∑ i : Option (ZMod p), adelicCyclicHilbertOperator f
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p hp)
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
          ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
            (finiteAdelicHeckeDiagonal p)⁻¹))))

/-- The bounded local Hecke sum has exactly the original algebraic normalized local Hecke values. -/
theorem adelicBoundedLocalNormalizedHecke_apply (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) :
    adelicBoundedLocalNormalizedHecke f p hp hpN x = adelicLocalNormalizedHecke f p hp hpN x := by
  simp only [adelicBoundedLocalNormalizedHecke, adelicLocalNormalizedHecke,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- The genuine normalized local Hecke sum commutes with the actual action at every distinct original place. -/
theorem adelicLocalNormalizedHecke_distinct_commute (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N)
    (v : HeightOneSpectrum ℤ) (hv : v ≠ rationalPrimePlace p hp)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicLocalNormalizedHecke f p hp hpN (adelicCyclicLocalRepresentation f v g x) =
      adelicCyclicLocalRepresentation f v g (adelicLocalNormalizedHecke f p hp hpN x) := by
  simp only [adelicLocalNormalizedHecke, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  apply congrArg (fun y : AdelicCyclicHilbert f => (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • y)
  apply Finset.sum_congr rfl
  intro i _
  exact adelicCyclicLocal_distinct_commute f v (rationalPrimePlace p hp) hv g _ x

/-- The whole actual cyclic Hilbert component at a distinct place retains the original good-prime Fourier eigenvalue. -/
theorem adelicLocalNormalizedHecke_distinct_component {p : ℕ} [NeZero p]
    (F : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N)
    (v : HeightOneSpectrum ℤ) (hv : v ≠ rationalPrimePlace p hp)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v) :
    adelicLocalNormalizedHecke F.toCuspForm p hp hpN x = normalizedCuspCoefficients F.toCuspForm p • x := by
  rw [← adelicBoundedLocalNormalizedHecke_apply]
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert F.toCuspForm)
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) inferInstance inferInstance
    (adelicBoundedLocalNormalizedHecke F.toCuspForm p hp hpN) (normalizedCuspCoefficients F.toCuspForm p)
    (fun g => adelicCyclicLocalRepresentation F.toCuspForm v g (adelicCyclicHilbertGenerator F.toCuspForm))
  · intro g
    rw [adelicBoundedLocalNormalizedHecke_apply, adelicLocalNormalizedHecke_distinct_commute _ _ _ _ _ hv,
      adelicLocalNormalizedHecke_primitive_generator, map_smul]
  · exact hx

end
end Dubon2026
