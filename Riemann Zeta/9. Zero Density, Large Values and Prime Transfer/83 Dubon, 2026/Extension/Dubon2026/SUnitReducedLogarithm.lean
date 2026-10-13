/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Reduced logarithmic construction adapted from NYLL ClassFieldTheory,
commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/LogLattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitOrdinaryUnitEmbedding
import Dubon2026.NumberFieldSUnitCoordinateVectors
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! # The original reduced S-unit logarithm

The finite coordinates are the already proved original valuation
exponents (negative principal-divisor orders). The infinite coordinates
are the pinned Dirichlet logarithms. This original image is used to prove
the actual S-unit lattice comparison for DUB-17's Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original reduced archimedean logarithmic space with its original finite coordinates. -/
abbrev SUnitReducedLogSpace := Units.dirichletUnitTheorem.logSpace K × (S → ℝ)

/-- The original S-unit logarithm with its existing integer valuation coordinates. -/
def sUnitReducedLog : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →+
    SUnitReducedLogSpace K S where
  toFun x := (fun w => w.val.mult * Real.log (w.val x.toMul.val.val),
    fun v => (sUnitValuationLinearMap (R := 𝓞 K) (K := K)
      (S : Set (HeightOneSpectrum (𝓞 K))) x v : ℝ))
  map_zero' := by
    apply Prod.ext
    · funext w
      simp
    · funext v
      simp
  map_add' x y := by
    apply Prod.ext
    · funext w
      simp [Real.log_mul, mul_add]
    · funext v
      simp

/-- The reduced logarithm restricts to the original Dirichlet logarithm on original ordinary units. -/
theorem sUnitReducedLog_ordinary_fst (u : (𝓞 K)ˣ) :
    (sUnitReducedLog K S (Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u))).1 =
      Units.logEmbedding K (Additive.ofMul u) := by
  funext w
  change w.val.mult * Real.log (w.val (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u).val.val) = _
  rw [sUnitOrdinaryUnitEmbedding_val]
  rfl

/-- All original finite logarithmic coordinates vanish on original ordinary units. -/
theorem sUnitReducedLog_ordinary_snd (u : (𝓞 K)ˣ) :
    (sUnitReducedLog K S (Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u))).2 = 0 := by
  funext v
  have h : sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u ∈ (sUnitValuations (R := 𝓞 K) (K := K) S).ker := by
    rw [← sUnitOrdinaryUnitEmbedding_range]
    exact ⟨u, rfl⟩
  have hv := congrArg Multiplicative.toAdd (congrFun h v)
  change ((sUnitValuations (R := 𝓞 K) (K := K) S (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u) v).toAdd : ℝ) = 0
  exact_mod_cast hv

/-- Vanishing of the original finite coordinates identifies an actual original ordinary unit. -/
theorem sUnitReducedLog_finite_zero_ordinary
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (hx : (sUnitReducedLog K S x).2 = 0) :
    ∃ u : (𝓞 K)ˣ, sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul := by
  have hk : x.toMul ∈ (sUnitValuations (R := 𝓞 K) (K := K) S).ker := by
    funext v
    change (sUnitValuations (R := 𝓞 K) (K := K) S x.toMul v).toAdd = 0
    have hv := congrFun hx v
    change ((sUnitValuations (R := 𝓞 K) (K := K) S x.toMul v).toAdd : ℝ) = 0 at hv
    exact_mod_cast hv
  rw [← sUnitOrdinaryUnitEmbedding_range] at hk
  exact hk

end
end Dubon2026
