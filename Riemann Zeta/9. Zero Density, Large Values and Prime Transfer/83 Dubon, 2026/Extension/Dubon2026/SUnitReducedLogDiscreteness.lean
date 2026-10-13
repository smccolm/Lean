/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Discreteness argument adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/LogLattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitReducedLogKernel
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Discreteness of the original S-unit logarithmic image

Small original finite coordinates vanish because they are integral.
The resulting original ordinary unit lies in the pinned discrete
Dirichlet lattice. This supplies discreteness for the actual S-unit
lattice comparison required by DUB-17's Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The integer-linear form of the original reduced S-unit logarithm. -/
def sUnitReducedLogLinearMap : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →ₗ[ℤ]
    SUnitReducedLogSpace K S := (sUnitReducedLog K S).toIntLinearMap

/-- The actual original S-unit logarithmic image as an integer submodule. -/
def sUnitReducedLogLattice : Submodule ℤ (SUnitReducedLogSpace K S) :=
  (sUnitReducedLogLinearMap K S).range

/-- Original finite logarithmic coordinates vanish when the full original vector has norm less than one. -/
theorem sUnitReducedLog_finite_zero_of_norm_lt_one
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (hx : ‖sUnitReducedLog K S x‖ < 1) : (sUnitReducedLog K S x).2 = 0 := by
  classical
  funext v
  have hv : ‖(sUnitReducedLog K S x).2 v‖ < 1 :=
    (norm_le_pi_norm _ v).trans_lt ((norm_snd_le (sUnitReducedLog K S x)).trans_lt hx)
  change |(sUnitValuationLinearMap (R := 𝓞 K) (K := K) S x v : ℝ)| < 1 at hv
  change (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S x v : ℝ) = 0
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hv
  exact_mod_cast Int.abs_lt_one_iff.mp hv

/-- The actual original S-unit logarithmic image is discrete in its original real ambient space. -/
theorem sUnitReducedLogLattice_discrete : DiscreteTopology (sUnitReducedLogLattice K S) := by
  classical
  letI : DiscreteTopology {x : Units.dirichletUnitTheorem.logSpace K //
      x ∈ Units.unitLattice K} := inferInstanceAs (DiscreteTopology (Units.unitLattice K))
  obtain ⟨ε, hεpos, hε⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete
    (s := (Units.unitLattice K : Set (Units.dirichletUnitTheorem.logSpace K)))
    DiscreteTopology.isDiscrete (show (0 : Units.dirichletUnitTheorem.logSpace K) ∈
      Units.unitLattice K by simp)
  have hδpos : 0 < min ε 1 := lt_min hεpos zero_lt_one
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨Metric.ball 0 (min ε 1), Metric.isOpen_ball, ?_⟩
  ext z
  constructor
  · intro hz
    have hzlt : ‖(z : SUnitReducedLogSpace K S)‖ < min ε 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨x, hx⟩ := z.property
    have hxlog : sUnitReducedLog K S x = (z : SUnitReducedLogSpace K S) := hx
    have hfin : (sUnitReducedLog K S x).2 = 0 :=
      sUnitReducedLog_finite_zero_of_norm_lt_one K S x
        (hxlog ▸ hzlt.trans_le (min_le_right _ _))
    obtain ⟨u, hu⟩ := sUnitReducedLog_finite_zero_ordinary K S x hfin
    have hxu : x = Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u) :=
      congrArg Additive.ofMul hu.symm
    have hinf : Units.logEmbedding K (Additive.ofMul u) =
        (z : SUnitReducedLogSpace K S).1 := by
      rw [← hxlog, hxu, sUnitReducedLog_ordinary_fst]
    have hunitmem : Units.logEmbedding K (Additive.ofMul u) ∈ Units.unitLattice K :=
      ⟨Additive.ofMul u, trivial, rfl⟩
    have hunitball : Units.logEmbedding K (Additive.ofMul u) ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right, hinf]
      exact (norm_fst_le (z : SUnitReducedLogSpace K S)).trans_lt
        (hzlt.trans_le (min_le_left _ _))
    have hunitzero : Units.logEmbedding K (Additive.ofMul u) = 0 := by
      have hmem := Set.mem_inter hunitball hunitmem
      rw [hε] at hmem
      exact hmem
    apply Subtype.ext
    rw [← hxlog]
    apply Prod.ext
    · rw [hxu, sUnitReducedLog_ordinary_fst]
      exact hunitzero
    · exact hfin
  · intro hz
    have hz0 : z = 0 := hz
    subst z
    simp [Metric.mem_ball, hδpos]

end
end Dubon2026
