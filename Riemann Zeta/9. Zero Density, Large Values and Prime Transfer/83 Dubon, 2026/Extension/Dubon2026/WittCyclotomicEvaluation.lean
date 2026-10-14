/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The evaluation/substitution proof is adapted to the actual monic root algebra
from Nyll/ClassFieldTheory/LubinTate/Padic/CompletedLevel.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/
import Dubon2026.WittCyclotomicRootAlgebra
import Dubon2026.AdicRootPowerEvaluation
import Dubon2026.PrimeWittIntertwinerInverse
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Genuine convergent evaluation in the actual Witt cyclotomic algebra

Its original prime-adic completeness and the proved root power bound
supply analytic evaluation. Pinned substitution compatibility evaluates
both inverse identities of the constructed semilinear series. This is
the actual torsion-evaluation step for DUB-17's auxiliary finite extension.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology

/-- Formal Witt coefficients carry the discrete coefficient topology used for power-series substitution. -/
local instance wittCyclotomicCoefficientUniformSpace (p : ℕ) [Fact p.Prime] :
    UniformSpace (WittVector p (AlgebraicClosure (ZMod p))) := ⊥

/-- The actual root algebra carries its original extended prime ideal. -/
local instance wittCyclotomicRootWithIdeal (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal (wittCyclotomicRootAlgebra p n) :=
  ⟨(Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
    (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n))⟩

/-- Completeness is derived from the original monic root algebra's proved adic completeness. -/
local instance wittCyclotomicRootCompleteSpace (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace (wittCyclotomicRootAlgebra p n) :=
  ((show IsAdic (WithIdeal.i : Ideal (wittCyclotomicRootAlgebra p n)) from rfl).isAdicComplete_iff.mp
    (wittCyclotomicRoot_isAdicComplete p n)).1

/-- The same proved adic completeness gives Hausdorff separation. -/
local instance wittCyclotomicRootT2Space (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space (wittCyclotomicRootAlgebra p n) :=
  ((show IsAdic (WithIdeal.i : Ideal (wittCyclotomicRootAlgebra p n)) from rfl).isAdicComplete_iff.mp
    (wittCyclotomicRoot_isAdicComplete p n)).2

/-- The actual translated cyclotomic root is a convergent evaluation point. -/
theorem wittCyclotomicRoot_hasEval (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.HasEval
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) :=
  adic_hasEval_of_pow_mem _ _ (wittCyclotomicRoot_pow_mem_prime p n)

/-- Genuine convergent evaluation of Witt series in the actual integral cyclotomic root algebra. -/
def wittCyclotomicPowerSeriesEval (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) →+* wittCyclotomicRootAlgebra p n :=
  PowerSeries.eval₂Hom (φ := algebraMap _ _) continuous_of_discreteTopology hx

/-- This actual evaluation sends the formal variable to the original point. -/
theorem wittCyclotomicPowerSeriesEval_X (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    wittCyclotomicPowerSeriesEval p n x hx PowerSeries.X = x := by
  rw [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- Actual evaluation is continuous for the power-series and original prime-adic topologies. -/
theorem wittCyclotomicPowerSeriesEval_continuous (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    Continuous (wittCyclotomicPowerSeriesEval p n x hx) := by
  rw [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom]
  exact PowerSeries.continuous_eval₂ continuous_of_discreteTopology hx

/-- A zero-constant formal substitution series evaluates to another genuine convergent point. -/
theorem wittCyclotomicPowerSeriesEval_hasEval (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x)
    (f : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))) (hf : PowerSeries.HasSubst f) :
    PowerSeries.HasEval (wittCyclotomicPowerSeriesEval p n x hx f) :=
  hf.hasEval.map (wittCyclotomicPowerSeriesEval_continuous p n x hx)

/-- Actual convergent evaluation preserves formal substitution. -/
theorem wittCyclotomicPowerSeriesEval_subst (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x)
    (a f : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (ha : PowerSeries.HasSubst a) :
    wittCyclotomicPowerSeriesEval p n x hx (PowerSeries.subst a f) =
      wittCyclotomicPowerSeriesEval p n (wittCyclotomicPowerSeriesEval p n x hx a)
        (wittCyclotomicPowerSeriesEval_hasEval p n x hx a ha) f := by
  simp only [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom]
  simpa only [PowerSeries.eval₂, PowerSeries.subst, Function.const_apply] using
    (MvPowerSeries.eval₂_subst (R := WittVector p (AlgebraicClosure (ZMod p)))
      (S := WittVector p (AlgebraicClosure (ZMod p))) (T := wittCyclotomicRootAlgebra p n)
      (a := fun _ : Unit => a) ha.const (PowerSeries.hasEval hx) f)

end
end Dubon2026
