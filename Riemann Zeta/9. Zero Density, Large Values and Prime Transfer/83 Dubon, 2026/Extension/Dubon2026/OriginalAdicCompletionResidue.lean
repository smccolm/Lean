/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Dubon2026.OriginalFinitePlaceApproximation
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! # Original finite-place completion residue field

Adapted from Naganori Yamaguchi's Apache-2.0 ClassFieldTheory,
commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1, original Idele/LocallyCompact.
Only the original finite-place residue comparison and local compactness
are ported. They establish the actual local-field input needed for the
local stabilizer H2 order in DUB-17's original idele Herbrand formula.
The global duality, numerical Selmer and automorphy/descent chain remains open.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Valued
variable (K : Type*) [Field K] [NumberField K]

/-- The residue field of the adic completion at `v` is the global
ring-of-integers quotient by `v`. -/
noncomputable def originalRingOfIntegersQuotientEquivAdicResidueField
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      Valued.ResidueField (v.adicCompletion K) := by
  let integerMap :
      𝓞 K →+* Valued.integer (v.adicCompletion K) := {
    toFun r :=
      ⟨algebraMap (𝓞 K) (v.adicCompletion K) r, by
        change
          Valued.v
            (algebraMap
              (𝓞 K) (v.adicCompletion K) r) ≤ 1
        rw [show
          Valued.v
              (algebraMap
                (𝓞 K) (v.adicCompletion K) r) =
            v.valuation K
              (algebraMap (𝓞 K) K r) from
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation
            (v := v) r]
        exact v.valuation_le_one r⟩
    map_one' := by
      ext
      simp
    map_mul' _ _ := by
      ext
      simp
    map_zero' := by
      ext
      simp
    map_add' _ _ := by
      ext
      simp
  }
  let residueMap :
      𝓞 K →+*
        Valued.ResidueField (v.adicCompletion K) :=
    (IsLocalRing.residue
      (Valued.integer
        (v.adicCompletion K))).comp integerMap
  have hker :
      RingHom.ker residueMap = v.asIdeal := by
    ext r
    change residueMap r = 0 ↔ r ∈ v.asIdeal
    change
      IsLocalRing.residue
          (Valued.integer (v.adicCompletion K))
          (integerMap r) = 0 ↔
        r ∈ v.asIdeal
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (integerMap r) ↔ r ∈ v.asIdeal
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change
      Valued.v
          (algebraMap
            (𝓞 K) (v.adicCompletion K) r) < 1 ↔
        r ∈ v.asIdeal
    rw [show
      Valued.v
          (algebraMap
            (𝓞 K) (v.adicCompletion K) r) =
        v.valuation K
          (algebraMap (𝓞 K) K r) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation
        (v := v) r]
    exact v.valuation_lt_one_iff_mem (K := K) r
  have hsur : Function.Surjective residueMap := by
    intro z
    obtain ⟨x, hx⟩ :=
      (IsLocalRing.residue_surjective
        (R :=
          Valued.integer
            (v.adicCompletion K))) z
    obtain ⟨y, hy⟩ :=
      (v.denseRange_algebraMap K).exists_dist_lt
        (x : v.adicCompletion K) zero_lt_one
    have hxy :
        Valued.v
            ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) < 1 := by
      rw [← Valued.toNormedField.norm_lt_one_iff]
      simpa only [dist_eq_norm] using hy
    have hy_integral : v.valuation K y ≤ 1 := by
      rw [show
        v.valuation K y =
          Valued.v
            (algebraMap K
              (v.adicCompletion K) y) from
        (HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (v := v) y).symm]
      rw [show
        algebraMap K (v.adicCompletion K) y =
          (x : v.adicCompletion K) -
            ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) by
        ring]
      exact Valued.v.map_sub_le x.2 hxy.le
    obtain ⟨r, hyr⟩ :=
      original_exists_ringOfIntegers_approximation
        K v y hy_integral
    have hyr' :
        Valued.v
            (algebraMap K
                (v.adicCompletion K) y -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) < 1 := by
      rw [IsScalarTower.algebraMap_apply
        (𝓞 K) K, ← map_sub]
      rw [show
        Valued.v
            (algebraMap K
              (v.adicCompletion K)
              (y - algebraMap (𝓞 K) K r)) =
          v.valuation K
            (y - algebraMap (𝓞 K) K r) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (v := v)
          (y - algebraMap (𝓞 K) K r)]
      exact hyr
    have hxr :
        Valued.v
            ((x : v.adicCompletion K) -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) < 1 := by
      rw [show
        (x : v.adicCompletion K) -
            algebraMap (𝓞 K)
              (v.adicCompletion K) r =
          ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) +
            (algebraMap K
                (v.adicCompletion K) y -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) by
        ring]
      exact Valued.v.map_add_lt hxy hyr'
    refine ⟨r, ?_⟩
    rw [← hx]
    change
      IsLocalRing.residue
          (Valued.integer
            (v.adicCompletion K))
          (integerMap r) =
        IsLocalRing.residue
          (Valued.integer
            (v.adicCompletion K)) x
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (integerMap r - x)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change
      Valued.v
          ((integerMap r : v.adicCompletion K) -
            (x : v.adicCompletion K)) < 1
    rw [Valued.v.map_sub_swap]
    exact hxr
  exact
    (Ideal.quotEquivOfEq hker).symm.trans
      (RingHom.quotientKerEquivOfSurjective hsur)

/-- The residue field of a number-field completion at a finite place is
finite. -/
theorem original_finite_adicCompletion_residueField
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  let : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (originalRingOfIntegersQuotientEquivAdicResidueField
      (K := K) v).toEquiv

open _root_.Valued.integer in
/-- Every nonarchimedean completion of a number field is a proper metric
space. -/
theorem original_adicCompletion_properSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  apply
    properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
  refine ⟨inferInstance, ?_, original_finite_adicCompletion_residueField K v⟩
  change IsDiscreteValuationRing (v.adicCompletionIntegers K)
  infer_instance


end
end Dubon2026
