/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Converse.TangentCriterion
import TateCurvesTheta.TateCurve.SplitReduction

/-!
# Split multiplicative reduction ⟺ `γ` is a square, in every residue characteristic

Let `K` be a complete ultrametric field. A Weierstrass curve `W` over `K` is **integral**
(`IsIntegral`) when its coefficients lie in the ring of integers `𝒪 = integerRing K`; it then has
an integral model `integralModel W` over `𝒪` and a **reduction** `reduction W` over the residue
field `𝒪/𝔪`. Using the repository's notion `WeierstrassCurve.IsSplitMultiplicative` of a split
node in nodal-normalized position (`TateCurve/SplitReduction.lean`), we say that `W` **has split
multiplicative reduction** (`HasSplitMultiplicativeReduction`) when some change of variables over
`K` carries `W` to an integral model whose reduction is split multiplicative: nodal (`Δ̄ = 0`,
`c̄₄ ≠ 0`), with node at the origin (`ā₃ = ā₄ = ā₆ = 0`) and tangent cone `T² + ā₁T - ā₂`
splitting into two distinct rational factors. (Such a model is automatically minimal, since
`c₄` is a unit.)

## Main results

* `isSquare_gammaInvariant_of_isSplitMultiplicative` (`2 ≠ 0` in `K`, **any residue
  characteristic**): if an integral model has split multiplicative reduction, `γ(W)` is a square.
  The tangent cone `T² + a₁T - a₂` has a simple root modulo `𝔪`, so `b₂ = a₁² + 4a₂ = s² + 4e`
  with `‖s‖ = 1`, `‖e‖ < 1` is a square `σ²` (`isSquare_sq_add_four_mul`, Hensel's lemma at the
  precision `‖4‖`, which covers residue characteristic `2`); then
  `-c₄c₆ = b₂⁵ + 4m = (σ⁵)² + 4m` with `‖m‖ < 1`, again a square.
* `TateParameter.hasSplitMultiplicativeReduction` : the Tate curve has split multiplicative
  reduction (its integral model reduces to the nodal cubic `y² + xy = x³`).
* `hasSplitMultiplicativeReduction_iff` (`12 ≠ 0`): `W` has split multiplicative reduction iff
  `‖j(W)‖ > 1` and `γ(W)` is a square, iff `W` is `K`-isomorphic to a Tate curve
  (`hasSplitMultiplicativeReduction_iff_exists_tateCurve`).
* `hasSplitMultiplicativeReduction_iff_exists_tangent_root` (`12 ≠ 0`, any residue
  characteristic): for an integral model with multiplicative reduction (`‖c₄‖ = 1`, `‖Δ‖ < 1`),
  split multiplicative reduction ⟺ the tangent quadratic `f = c₄T² + a₁c₄T - (…)` (discriminant
  `-c₄c₆`) has an integral root modulo `𝔪`, i.e. its reduction splits over `𝒪/𝔪`
  ⟺ `γ(W)` is a square.
-/

noncomputable section

namespace TateCurvesTheta

open WeierstrassCurve

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Integral models and their reduction -/

/-- A Weierstrass curve over `K` is **integral** if all its coefficients have norm `≤ 1`. -/
def IsIntegral (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

/-- The **integral model** over the ring of integers `integerRing K` of an integral curve. -/
def integralModel (W : WeierstrassCurve K) (h : IsIntegral W) :
    WeierstrassCurve (integerRing K) :=
  ⟨⟨W.a₁, h.1⟩, ⟨W.a₂, h.2.1⟩, ⟨W.a₃, h.2.2.1⟩, ⟨W.a₄, h.2.2.2.1⟩, ⟨W.a₆, h.2.2.2.2⟩⟩

lemma integralModel_map_subtype (W : WeierstrassCurve K) (h : IsIntegral W) :
    (integralModel W h).map (integerRing K).subtype = W := rfl

/-- The **reduction** of an integral curve: its integral model modulo the maximal ideal. -/
def reduction (W : WeierstrassCurve K) (h : IsIntegral W) :
    WeierstrassCurve (integerRing K ⧸ integerIdeal K) :=
  (integralModel W h).map (Ideal.Quotient.mk (integerIdeal K))

/-- `W` **has split multiplicative reduction** if some change of variables over `K` carries it to
an integral model whose reduction is split multiplicative (nodal-normalized, with split node). -/
def HasSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop :=
  ∃ C : VariableChange K, ∃ h : IsIntegral (C • W), (reduction (C • W) h).IsSplitMultiplicative

lemma mk_eq_zero_iff {x : integerRing K} :
    Ideal.Quotient.mk (integerIdeal K) x = 0 ↔ ‖(x : K)‖ < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

lemma norm_eq_one_of_mk_ne_zero {x : integerRing K}
    (hx : Ideal.Quotient.mk (integerIdeal K) x ≠ 0) :
    ‖(x : K)‖ = 1 :=
  le_antisymm x.2 (not_lt.mp fun h => hx (mk_eq_zero_iff.mpr h))

section Coe

variable (W : WeierstrassCurve K) (h : IsIntegral W)

lemma coe_integralModel_b₂ : ((integralModel W h).b₂ : K) = W.b₂ := by
  conv_rhs => rw [← integralModel_map_subtype W h, map_b₂]
  rfl

lemma coe_integralModel_b₄ : ((integralModel W h).b₄ : K) = W.b₄ := by
  conv_rhs => rw [← integralModel_map_subtype W h, map_b₄]
  rfl

lemma coe_integralModel_b₆ : ((integralModel W h).b₆ : K) = W.b₆ := by
  conv_rhs => rw [← integralModel_map_subtype W h, map_b₆]
  rfl

lemma coe_integralModel_c₄ : ((integralModel W h).c₄ : K) = W.c₄ := by
  conv_rhs => rw [← integralModel_map_subtype W h, map_c₄]
  rfl

lemma coe_integralModel_Δ : ((integralModel W h).Δ : K) = W.Δ := by
  conv_rhs => rw [← integralModel_map_subtype W h, map_Δ]
  rfl

lemma reduction_c₄ : (reduction W h).c₄ = Ideal.Quotient.mk _ (integralModel W h).c₄ := map_c₄ _ _

lemma reduction_Δ : (reduction W h).Δ = Ideal.Quotient.mk _ (integralModel W h).Δ := map_Δ _ _

end Coe

/-! ### Split reduction gives a square `γ` (every residue characteristic) -/

variable [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `-c₄c₆ = b₂⁵ + 4 m` with `m = -15 b₂³b₄ + 54 b₂²b₆ + 216 b₂b₄² - 1296 b₄b₆`. -/
lemma neg_c₄_mul_c₆_eq_b (W : WeierstrassCurve K) :
    -(W.c₄ * W.c₆) = W.b₂ ^ 5 + 4 * (-15 * W.b₂ ^ 3 * W.b₄ + 54 * W.b₂ ^ 2 * W.b₆ +
      216 * W.b₂ * W.b₄ ^ 2 - 1296 * W.b₄ * W.b₆) := by
  rw [c₄, c₆]
  ring

omit [CompleteSpace K] in
private lemma norm_ofNat_le_one'' (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

/-- **Split multiplicative reduction gives a square `γ`, in every residue characteristic**
(`2 ≠ 0` in `K`): if an integral model `W` has split multiplicative reduction, `γ(W)` is a square
in `K`. -/
theorem isSquare_gammaInvariant_of_isSplitMultiplicative (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) (h : IsIntegral W) (hs : (reduction W h).IsSplitMultiplicative) :
    IsSquare (gammaInvariant W) := by
  obtain ⟨ha₃, ha₄, ha₆, α, β, hαβ, hpoly⟩ := hs.hasSplitNodeAtOrigin
  set A := integralModel W h
  set mk := Ideal.Quotient.mk (integerIdeal K)
  have hA₁ : (reduction W h).a₁ = mk A.a₁ := rfl
  have hA₂ : (reduction W h).a₂ = mk A.a₂ := rfl
  -- the reduced tangent cone vanishes at `α` and `β`, so `α + β + ā₁ = 0`
  have hev : ∀ x, x * x + mk A.a₁ * x - mk A.a₂ = (x - α) * (x - β) := fun x => by
    have := congrArg (Polynomial.eval x) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hA₁, hA₂] at this
    rw [← sq]
    exact this
  have hsum : α + β + mk A.a₁ = 0 := by
    have hα := hev α
    have hβ := hev β
    rw [sub_self, zero_mul] at hα
    rw [sub_self, mul_zero] at hβ
    have : (α - β) * (α + β + mk A.a₁) = 0 := by linear_combination hα - hβ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hαβ)
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective α
  -- `g(ρ) = ρ² + a₁ρ - a₂ ∈ 𝔪` and `s = 2ρ + a₁` is a unit
  have hg : ‖(ρ : K) * ρ + W.a₁ * ρ - W.a₂‖ < 1 := by
    have : ‖((ρ * ρ + A.a₁ * ρ - A.a₂ : integerRing K) : K)‖ < 1 := by
      rw [← mk_eq_zero_iff, map_sub, map_add, map_mul, map_mul, hev, sub_self, zero_mul]
    exact this
  have hs1 : ‖(ρ : K) + ρ + W.a₁‖ = 1 := by
    have : ‖((ρ + ρ + A.a₁ : integerRing K) : K)‖ = 1 := by
      refine norm_eq_one_of_mk_ne_zero ?_
      rw [map_add, map_add]
      intro h0
      apply hαβ
      linear_combination h0 - hsum
    exact this
  have hlt : ∀ {x y : K}, ‖x‖ < 1 → ‖y‖ ≤ 1 → ‖y * x‖ < 1 := fun hx hy => by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hy (norm_nonneg _) hx
  have hadd : ∀ {x y : K}, ‖x‖ < 1 → ‖y‖ < 1 → ‖x + y‖ < 1 := fun hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  have hadd1 : ∀ {x y : K}, ‖x‖ = 1 → ‖y‖ < 1 → ‖x + y‖ = 1 := fun hx hy => by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne'), hx,
      max_eq_left (by rw [hx] at *; exact hy.le)]
  -- `b₂ = s² + 4(-g)` is a square `σ²`, with `‖σ‖ = 1`
  have hb₂ : W.b₂ = ((ρ : K) + ρ + W.a₁) ^ 2 + 4 * -((ρ : K) * ρ + W.a₁ * ρ - W.a₂) := by
    rw [b₂]
    ring
  have hg4 : ‖4 * -((ρ : K) * ρ + W.a₁ * ρ - W.a₂)‖ < 1 :=
    hlt (by rw [norm_neg]; exact hg) (norm_ofNat_le_one'' 4)
  obtain ⟨σ, hσ⟩ := hb₂ ▸ isSquare_sq_add_four_mul h2 hs1 (by rw [norm_neg]; exact hg)
  have hb₂1 : ‖W.b₂‖ = 1 := by
    rw [hb₂]
    exact hadd1 (by rw [norm_pow, hs1, one_pow]) hg4
  have hσ1 : ‖σ‖ = 1 := by
    have : ‖σ‖ ^ 2 = 1 := by rw [← norm_pow, sq, ← hσ, hb₂1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  -- `‖b₄‖, ‖b₆‖ < 1`, `‖b₂‖ ≤ 1`
  have h3 : ‖W.a₃‖ < 1 := mk_eq_zero_iff.mp ha₃
  have h4 : ‖W.a₄‖ < 1 := mk_eq_zero_iff.mp ha₄
  have h6 : ‖W.a₆‖ < 1 := mk_eq_zero_iff.mp ha₆
  have hb₄ : ‖W.b₄‖ < 1 := by
    rw [b₄]
    exact hadd (hlt h4 (norm_ofNat_le_one'' 2)) (hlt h3 h.1)
  have hb₆ : ‖W.b₆‖ < 1 := by
    rw [b₆, sq]
    exact hadd (hlt h3 h3.le) (hlt h6 (norm_ofNat_le_one'' 4))
  have hb₂le : ‖W.b₂‖ ≤ 1 := hb₂1.le
  have hm : ‖-15 * W.b₂ ^ 3 * W.b₄ + 54 * W.b₂ ^ 2 * W.b₆ + 216 * W.b₂ * W.b₄ ^ 2 -
      1296 * W.b₄ * W.b₆‖ < 1 := by
    have hc : ∀ {c x : K}, ‖c‖ ≤ 1 → ‖x‖ < 1 → ‖c * x‖ < 1 := fun hc hx => hlt hx hc
    have hpow : ∀ n : ℕ, ‖W.b₂ ^ n‖ ≤ 1 := fun n => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hb₂le
    have h15 : ‖-15 * W.b₂ ^ 3‖ ≤ 1 := by
      rw [norm_mul, norm_neg]
      exact mul_le_one₀ (norm_ofNat_le_one'' 15) (norm_nonneg _) (hpow 3)
    have h54 : ‖54 * W.b₂ ^ 2‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one'' 54) (norm_nonneg _) (hpow 2)
    have h216 : ‖216 * W.b₂ * W.b₄‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (norm_ofNat_le_one'' 216) (norm_nonneg _) hb₂le)
        (norm_nonneg _) hb₄.le
    have h1296 : ‖1296 * W.b₄‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ (norm_ofNat_le_one'' 1296) (norm_nonneg _) hb₄.le
    rw [sub_eq_add_neg]
    refine hadd (hadd (hadd (hc h15 hb₄) (hc h54 hb₆)) ?_) ?_
    · rw [sq, ← mul_assoc]
      exact hc h216 hb₄
    · rw [norm_neg]
      exact hc h1296 hb₆
  -- `-c₄c₆ = (σ⁵)² + 4m` is a square
  have hsq := isSquare_sq_add_four_mul h2 (by rw [norm_pow, hσ1, one_pow] : ‖σ ^ 5‖ = 1) hm
  rw [show (σ ^ 5) ^ 2 = W.b₂ ^ 5 by rw [hσ]; ring, ← neg_c₄_mul_c₆_eq_b] at hsq
  have hne : -(W.c₄ * W.c₆) ≠ 0 := by
    rw [neg_c₄_mul_c₆_eq_b]
    intro h0
    have h1 : ‖W.b₂ ^ 5 + 4 * (-15 * W.b₂ ^ 3 * W.b₄ + 54 * W.b₂ ^ 2 * W.b₆ +
        216 * W.b₂ * W.b₄ ^ 2 - 1296 * W.b₄ * W.b₆)‖ = 1 := by
      exact hadd1 (by rw [norm_pow, hb₂1, one_pow]) (hlt hm (norm_ofNat_le_one'' 4))
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hc₆ : W.c₆ ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, neg_zero])
  exact (isSquare_gammaInvariant_iff W hc₆).mpr hsq

omit [CompleteSpace K] in
/-- A split multiplicative integral model has `‖c₄‖ = 1` and `‖Δ‖ < 1`. -/
lemma norm_c₄_eq_one_and_norm_Δ_lt_one (W : WeierstrassCurve K) (h : IsIntegral W)
    (hs : (reduction W h).IsSplitMultiplicative) : ‖W.c₄‖ = 1 ∧ ‖W.Δ‖ < 1 := by
  refine ⟨?_, ?_⟩
  · rw [← coe_integralModel_c₄ W h]
    exact norm_eq_one_of_mk_ne_zero (reduction_c₄ W h ▸ hs.c₄_ne_zero)
  · rw [← coe_integralModel_Δ W h]
    exact mk_eq_zero_iff.mp (reduction_Δ W h ▸ hs.Δ_eq_zero)

/-- **Split multiplicative reduction gives a square `γ`** (`2 ≠ 0`, any residue characteristic).
-/
theorem HasSplitMultiplicativeReduction.isSquare_gammaInvariant (h2 : (2 : K) ≠ 0)
    {W : WeierstrassCurve K} (hW : HasSplitMultiplicativeReduction W) :
    IsSquare (gammaInvariant W) := by
  obtain ⟨C, h, hs⟩ := hW
  have := isSquare_gammaInvariant_of_isSplitMultiplicative h2 _ h hs
  rw [gammaInvariant_variableChange] at this
  have := this.div (IsSquare.sq (C.u : K))
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero 2 C.u.ne_zero)] at this

omit [CompleteSpace K] in
/-- **Split multiplicative reduction gives a non-integral `j`.** -/
theorem HasSplitMultiplicativeReduction.one_lt_norm_j {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : HasSplitMultiplicativeReduction W) : 1 < ‖W.j‖ := by
  obtain ⟨C, h, hs⟩ := hW
  obtain ⟨hc₄, hΔ⟩ := norm_c₄_eq_one_and_norm_Δ_lt_one _ h hs
  rw [← variableChange_j W C]
  exact TateCurvesTheta.one_lt_norm_j _ hc₄ hΔ

/-! ### The Tate curve has split multiplicative reduction -/

namespace TateParameter

variable (t : TateParameter K) (h12 : (12 : K) ≠ 0)
include h12

lemma isIntegral_tateCurve : IsIntegral t.tateCurve :=
  ⟨by simp [tateCurve], by simp [tateCurve], by simp [tateCurve],
    (t.norm_a₄_le.trans_lt t.norm_lt_one).le, ((t.norm_a₆_le h12).trans_lt t.norm_lt_one).le⟩

lemma integralModel_tateCurve :
    integralModel t.tateCurve (t.isIntegral_tateCurve h12) = t.tateCurveInt h12 := rfl

/-- **The Tate curve has split multiplicative reduction.** -/
theorem hasSplitMultiplicativeReduction : HasSplitMultiplicativeReduction t.tateCurve :=
  ⟨1, by rw [one_smul]; exact t.isIntegral_tateCurve h12, by
    simp only [one_smul]
    exact t.isSplitMultiplicative_reduction h12⟩

end TateParameter

/-! ### The characterisation -/

variable (h12 : (12 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic]
include h12

omit [CompleteSpace K] h12 [W.IsElliptic] in
lemma hasSplitMultiplicativeReduction_of_smul_eq {C : VariableChange K} {W' : WeierstrassCurve K}
    (hC : C • W = W') (hW' : HasSplitMultiplicativeReduction W') :
    HasSplitMultiplicativeReduction W := by
  obtain ⟨D, h, hs⟩ := hW'
  refine ⟨D * C, ?_⟩
  rw [mul_smul, hC]
  exact ⟨h, hs⟩

/-- **Split multiplicative reduction ⟺ `‖j‖ > 1` and `γ` is a square**, in every residue
characteristic (`12 ≠ 0` in `K`). -/
theorem hasSplitMultiplicativeReduction_iff :
    HasSplitMultiplicativeReduction W ↔ 1 < ‖W.j‖ ∧ IsSquare (gammaInvariant W) := by
  refine ⟨fun hW => ⟨hW.one_lt_norm_j, hW.isSquare_gammaInvariant
    (two_ne_zero_of_twelve h12)⟩, fun ⟨hj, hγ⟩ => ?_⟩
  obtain ⟨C, hC⟩ := exists_variableChange_tateCurve h12 W hj hγ
  exact hasSplitMultiplicativeReduction_of_smul_eq W hC
    ((TateParameter.ofJ h12 hj).hasSplitMultiplicativeReduction h12)

/-- **Silverman V.5.3, reduction-type form**: `W` has split multiplicative reduction iff it is
isomorphic over `K` to a Tate curve (every residue characteristic, `12 ≠ 0` in `K`). -/
theorem hasSplitMultiplicativeReduction_iff_exists_tateCurve :
    HasSplitMultiplicativeReduction W ↔
      ∃ (t : TateParameter K) (C : VariableChange K), C • W = t.tateCurve := by
  rw [hasSplitMultiplicativeReduction_iff h12, exists_tateParameter_variableChange_iff h12]

omit [CompleteSpace K] h12 [W.IsElliptic] in
/-- A root of the tangent quadratic of an integral model with `‖c₄‖ = 1` is integral. -/
lemma norm_le_one_of_tangentQuadratic_eq_zero (h : IsIntegral W) (hc₄ : ‖W.c₄‖ = 1) {r : K}
    (hr : tangentQuadratic W r = 0) : ‖r‖ ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set A := integralModel W h
  have he : ‖54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄‖ ≤ 1 := by
    rw [← coe_integralModel_b₂ W h, ← coe_integralModel_b₄ W h, ← coe_integralModel_b₆ W h,
      ← coe_integralModel_c₄ W h]
    exact (54 * A.b₆ - 3 * A.b₂ * A.b₄ + A.a₂ * A.c₄).2
  have hlin : ‖W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)‖ ≤ ‖r‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by
      rw [norm_neg]; exact he.trans hlt.le))
    rw [norm_mul, norm_mul, hc₄, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h.1
  have hquad : ‖W.c₄ * r ^ 2‖ = ‖r‖ ^ 2 := by rw [norm_mul, hc₄, one_mul, norm_pow]
  have hgt : ‖r‖ < ‖r‖ ^ 2 := by nlinarith
  have : ‖tangentQuadratic W r‖ = ‖r‖ ^ 2 := by
    rw [tangentQuadratic, add_sub_assoc, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm,
      hquad, max_eq_left (hlin.trans hgt.le)]
    rw [hquad]
    exact (hlin.trans_lt hgt).ne'
  rw [hr, norm_zero] at this
  nlinarith

/-- **Split multiplicative reduction via the tangent quadratic, every residue characteristic**
(`12 ≠ 0` in `K`): for an integral model with multiplicative reduction (`‖c₄‖ = 1`, `‖Δ‖ < 1`),
`W` has split multiplicative reduction iff the tangent quadratic has an integral root modulo the
maximal ideal (i.e. its reduction over `𝒪/𝔪`, whose leading coefficient `c̄₄` is nonzero, splits),
iff `γ(W)` is a square in `K`. -/
theorem hasSplitMultiplicativeReduction_iff_exists_tangent_root (h : IsIntegral W)
    (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    HasSplitMultiplicativeReduction W ↔ ∃ r : K, ‖r‖ ≤ 1 ∧ ‖tangentQuadratic W r‖ < 1 := by
  have h2 := two_ne_zero_of_twelve h12
  rw [hasSplitMultiplicativeReduction_iff h12, and_iff_right (one_lt_norm_j W hc₄ hΔ)]
  refine ⟨fun hγ => ?_, fun ⟨r, _, hr⟩ =>
    isSquare_gammaInvariant_of_tangent_root' h2 W hc₄ hΔ ⟨r, hr⟩⟩
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  have hne : ∀ {x : K}, ‖x‖ = 1 → x ≠ 0 := fun hx h0 => by
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  rw [isSquare_gammaInvariant_iff W (hne hc₆)] at hγ
  obtain ⟨r, hr⟩ := exists_tangentQuadratic_eq_zero W h2 (hne hc₄) hγ
  exact ⟨r, norm_le_one_of_tangentQuadratic_eq_zero W h hc₄ hr,
    by rw [hr, norm_zero]; exact zero_lt_one⟩

end TateCurvesTheta
