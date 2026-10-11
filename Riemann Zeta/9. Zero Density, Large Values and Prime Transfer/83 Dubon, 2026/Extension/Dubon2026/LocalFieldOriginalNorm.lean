import Mathlib.NumberTheory.LocalField.Basic

/-! # A compatible norm on the original local field and original uniform space

The rank-one construction reuses the value-group embedding employed in pinned
Mathlib `NumberTheory/LocalField/Basic.lean` (Andrew Yang, 2025, Apache 2.0).
The actual `Valued.toNontriviallyNormedField` retains the original uniform space.
-/

namespace Dubon2026
noncomputable section

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- A genuine rank-one embedding of the original valuation value group. -/
@[reducible]
def localFieldOriginalRankOne : (ValuativeRel.valuation K).RankOne where
  hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

/-- The original field with a compatible nontrivial norm, using its actual
uniform structure rather than replacing its topology. -/
@[reducible]
def localFieldOriginalNorm : NontriviallyNormedField K := by
  letI : (Valued.v (R := K)).RankOne := localFieldOriginalRankOne K
  exact Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)

/-- The constructed norm retains the original uniform structure exactly. -/
theorem localFieldOriginalNorm_uniformSpace :
    (localFieldOriginalNorm K).toUniformSpace = (inferInstance : UniformSpace K) := by
  rfl

/-- Comparison of original norms is precisely comparison by the original
valuation, so the original integer ring is preserved. -/
theorem localFieldOriginalNorm_le_iff (x y : K) :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    ‖x‖ ≤ ‖y‖ ↔ ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y := by
  letI : (Valued.v (R := K)).RankOne := localFieldOriginalRankOne K
  exact Valued.toNormedField.norm_le_iff (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- The compatible original norm is ultrametric. -/
theorem localFieldOriginalNorm_isUltrametric :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    IsUltrametricDist K := by
  letI : (Valued.v (R := K)).RankOne := localFieldOriginalRankOne K
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  infer_instance

/-- The actual norm valuation represents the original valuative relation. -/
theorem localFieldOriginalNorm_compatible :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    letI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
    (NormedField.valuation (K := K)).Compatible := by
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  letI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  constructor
  intro x y
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔ ‖x‖₊ ≤ ‖y‖₊
  rw [← NNReal.coe_le_coe]
  exact (localFieldOriginalNorm_le_iff K x y).symm

/-- Completeness of the original local uniform field is retained by the
compatible norm. -/
theorem localFieldOriginalNorm_complete :
    letI : NontriviallyNormedField K := localFieldOriginalNorm K
    CompleteSpace K := by
  exact inferInstanceAs (CompleteSpace K)

end
end Dubon2026
