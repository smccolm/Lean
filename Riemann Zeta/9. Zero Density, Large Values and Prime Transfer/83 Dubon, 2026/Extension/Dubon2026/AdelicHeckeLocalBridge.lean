import Dubon2026.FiniteAdelicHeckeLocalSupport
import Dubon2026.AdelicLocalRepresentation
import Dubon2026.AdelicNormalizedHecke

/-! # Exact localization of the original finite-adelic Hecke action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem scaled_sum_congr {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (a b : ι → Module.End ℂ V) (c : ℂ) (x : V) (h : ∀ i, a i x = b i x) :
    c • (∑ i, a i) x = (c • ∑ i, b i) x := by
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  exact congrArg (fun y : V => c • y) (Finset.sum_congr rfl (fun i _ => h i))

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- On a genuine original level-fixed vector, an adelic element integral at all other places acts exactly by its actual single-place coordinate. -/
theorem adelicLevelFixed_action_local (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (ha : ∀ w, w ≠ v → GeneralLinearGroup.map (finiteAdelePlace w) a ∈ finitePlaceGL2Gamma0 N w)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLevelFixedSpace f) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) x =
      adelicCyclicLocalRepresentation f v (GeneralLinearGroup.map (finiteAdelePlace v) a) x := by
  have he := congrArg (fun b => adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b) x)
    (finiteAdelicLocal_mul_removal v a)
  simp only [map_mul, Module.End.mul_apply] at he
  rw [(mem_adelicLevelFixedSpace f x).mp hx ⟨_, finiteAdelicPlaceRemoval_mem_level N v a ha⟩] at he
  exact he.symm

/-- The literal normalized Hecke sum in the original actual p-local representation, using the genuine local coordinates of the proved original transversal. -/
def adelicLocalNormalizedHecke (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N) :
    Module.End ℂ (AdelicCyclicHilbert f) :=
  (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) •
    ∑ i : Option (ZMod p), adelicCyclicLocalRepresentation f (rationalPrimePlace p hp)
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹))

/-- The actual normalized adelic Hecke operator equals the genuine single-prime local sum on every original level-fixed Hilbert vector. -/
theorem adelicNormalizedHecke_eq_local (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLevelFixedSpace f) :
    adelicNormalizedHecke f p hpN x = adelicLocalNormalizedHecke f p hp hpN x := by
  rw [adelicNormalizedHecke, ContinuousLinearMap.smul_apply, adelicBoundedHeckeTrace_apply]
  apply @scaled_sum_congr (AdelicCyclicHilbert f) (Option (ZMod p))
    inferInstance inferInstance inferInstance
  intro i
  exact adelicLevelFixed_action_local f (rationalPrimePlace p hp) _
    (finiteAdelicHeckeRepresentative_local_level N p hp hpN i) x hx

/-- The original primitive generator has its exact original Fourier eigenvalue for the genuine normalized single-prime local Hecke sum. -/
theorem adelicLocalNormalizedHecke_primitive_generator {p : ℕ} [NeZero p]
    (F : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N) :
    adelicLocalNormalizedHecke F.toCuspForm p hp hpN (adelicCyclicHilbertGenerator F.toCuspForm) =
      normalizedCuspCoefficients F.toCuspForm p • adelicCyclicHilbertGenerator F.toCuspForm := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← adelicNormalizedHecke_eq_local F.toCuspForm p hp hpN _
    ((mem_adelicLevelFixedSpace F.toCuspForm _).mpr (adelicCyclicHilbertGenerator_finite_level F.toCuspForm))]
  exact adelicNormalizedHecke_primitive_generator F hpN

end
end Dubon2026
