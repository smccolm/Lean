import Tao2026.QuadraticIdealDivisors

/-!
# Counting boxed solutions in the nonsquare quadratic branch

This module assembles the two quantitative halves of Tao's Lemma 2.10:
the sharp `d(|N|)^2` count of ideal-divisor orbits and the uniform logarithmic
count of bounded-height units inside each orbit.
-/

namespace Tao2026

open scoped NumberField

/-- A boxed square-relation solution, as a finite type. -/
def squareRelationSolutionType (a b h x y : ℕ) :=
  {nm : ℕ × ℕ // nm ∈ squareRelationSolutionsBox a b h x y}

noncomputable instance squareRelationSolutionTypeFintype
    (a b h x y : ℕ) : Fintype (squareRelationSolutionType a b h x y) :=
  Fintype.ofFinset (squareRelationSolutionsBox a b h x y)
    (by intro nm; rfl)

/-- The norm-fiber point attached to a boxed solution. -/
def squareRelationSolutionNormFiberPoint
    {a b c D h x y : ℕ} (hdisc : a * b = D * c ^ 2)
    (nm : squareRelationSolutionType a b h x y) :
    zsqrtdNormFiber (D : ℤ) ((b * h : ℕ) : ℤ) :=
  squareRelationNormFiberPoint hdisc
    (mem_squareRelationSolutionsBox.mp nm.2).2.2.2.2

/-- With positive coefficients, the solution-to-norm-point map is injective. -/
theorem squareRelationSolutionNormFiberPoint_injective
    {a b c D h x y : ℕ} (hdisc : a * b = D * c ^ 2)
    (hb : 0 < b) (hc : 0 < c) :
    Function.Injective
      (squareRelationSolutionNormFiberPoint
        (h := h) (x := x) (y := y) hdisc) := by
  intro nm₁ nm₂ hnm
  apply Subtype.ext
  apply squareRelationNormPoint_injective hb hc
  exact congrArg Subtype.val hnm

/-- The maximal-order principal ideal attached to a boxed solution. -/
noncomputable def squareRelationSolutionIdeal
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (nm : squareRelationSolutionType a b h x y) :
    Ideal (𝓞 (quadraticField D)) :=
  maximalOrderNormFiberIdealDivisor
    (squareRelationSolutionNormFiberPoint
      (h := h) (x := x) (y := y) hdisc nm)

/-- The finite image of boxed solutions in the ideal-divisor set. -/
noncomputable def squareRelationSolutionIdeals
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2) :
    Finset (Ideal (𝓞 (quadraticField D))) :=
  Finset.univ.image
    (squareRelationSolutionIdeal (h := h) (x := x) (y := y) hdisc)

/-- An ideal index carrying the proof that it is realized by a solution. -/
noncomputable def squareRelationSolutionIdealIndex
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (nm : squareRelationSolutionType a b h x y) :
    {I : Ideal (𝓞 (quadraticField D)) //
      I ∈ squareRelationSolutionIdeals
        (h := h) (x := x) (y := y) hdisc} :=
  ⟨squareRelationSolutionIdeal (h := h) (x := x) (y := y) hdisc nm, by
    exact Finset.mem_image.mpr ⟨nm, Finset.mem_univ _, rfl⟩⟩

/-- A canonical anchor solution in every realized ideal fiber. -/
noncomputable def squareRelationSolutionAnchor
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (I : {I : Ideal (𝓞 (quadraticField D)) //
      I ∈ squareRelationSolutionIdeals
        (h := h) (x := x) (y := y) hdisc}) :
    squareRelationSolutionType a b h x y :=
  Classical.choose (Finset.mem_image.mp I.2)

theorem squareRelationSolutionAnchor_ideal
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (I : {I : Ideal (𝓞 (quadraticField D)) //
      I ∈ squareRelationSolutionIdeals
        (h := h) (x := x) (y := y) hdisc}) :
    squareRelationSolutionIdeal (h := h) (x := x) (y := y) hdisc
        (squareRelationSolutionAnchor
          (h := h) (x := x) (y := y) hdisc I) = I.1 := by
  exact (Classical.choose_spec (Finset.mem_image.mp I.2)).2

/-- Equality of the canonical anchor's ideal with the ideal of the indexed
solution. -/
theorem squareRelationSolutionAnchor_sameIdeal
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (nm : squareRelationSolutionType a b h x y) :
    maximalOrderNormFiberIdealDivisor
        (squareRelationSolutionNormFiberPoint
          (h := h) (x := x) (y := y) hdisc
          (squareRelationSolutionAnchor
            (h := h) (x := x) (y := y) hdisc
            (squareRelationSolutionIdealIndex
              (h := h) (x := x) (y := y) hdisc nm))) =
      maximalOrderNormFiberIdealDivisor
        (squareRelationSolutionNormFiberPoint
          (h := h) (x := x) (y := y) hdisc nm) := by
  apply Subtype.ext
  exact squareRelationSolutionAnchor_ideal
    (h := h) (x := x) (y := y) hdisc
    (squareRelationSolutionIdealIndex
      (h := h) (x := x) (y := y) hdisc nm)

/-- Unit coordinate of a solution relative to the canonical anchor of its
ideal-divisor fiber. -/
noncomputable def squareRelationSolutionAssociatedUnit
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2)
    (nm : squareRelationSolutionType a b h x y) :
    (𝓞 (quadraticField D))ˣ :=
  maximalOrderNormFiberAssociatedUnit
    (squareRelationSolutionAnchor_sameIdeal
      (h := h) (x := x) (y := y) hdisc nm)

/-- Every solution's anchor-relative unit lies in the single uniform
bounded-height candidate family attached to the box. -/
theorem squareRelationSolutionAssociatedUnit_mem_uniformCandidates
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hh : 0 < h)
    (nm : squareRelationSolutionType a b h x y) :
    squareRelationSolutionAssociatedUnit hdisc nm ∈
      quadraticUnitsUpToLogBound D
        (quadraticUnitLogCutoff (squareRelationBoxEnvelope b c D x y)) := by
  let I := squareRelationSolutionIdealIndex
    (h := h) (x := x) (y := y) hdisc nm
  let z := squareRelationSolutionAnchor
    (h := h) (x := x) (y := y) hdisc I
  have hz := mem_squareRelationSolutionsBox.mp z.2
  have hnm := mem_squareRelationSolutionsBox.mp nm.2
  exact squareRelationAssociatedUnit_mem_uniformCandidates
    hdisc hz.2.2.2.2 hnm.2.2.2.2 hb hh hz.2.2.1 hnm.2.2.1
      hz.2.1 hz.2.2.2.1 hnm.2.1 hnm.2.2.2.1
      (squareRelationSolutionAnchor_sameIdeal
        (h := h) (x := x) (y := y) hdisc nm)

/-- The pair consisting of the realized ideal and its anchor-relative unit
uniquely determines a boxed solution. -/
theorem squareRelationSolutionIdealIndex_unit_injective
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective fun nm : squareRelationSolutionType a b h x y ↦
      (squareRelationSolutionIdealIndex hdisc nm,
        squareRelationSolutionAssociatedUnit hdisc nm) := by
  intro nm₁ nm₂ hcode
  have hI := congrArg Prod.fst hcode
  have hU := congrArg Prod.snd hcode
  let I₁ := squareRelationSolutionIdealIndex
    (h := h) (x := x) (y := y) hdisc nm₁
  let I₂ := squareRelationSolutionIdealIndex
    (h := h) (x := x) (y := y) hdisc nm₂
  have hI' : I₁ = I₂ := by simpa only [I₁, I₂] using hI
  let z := squareRelationSolutionAnchor
    (h := h) (x := x) (y := y) hdisc I₂
  have hideal₁ :
      maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc z) =
        maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc nm₁) := by
    simpa only [z, I₁, I₂, hI'] using
      (squareRelationSolutionAnchor_sameIdeal hdisc nm₁)
  have hideal₂ :
      maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc z) =
        maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc nm₂) := by
    exact squareRelationSolutionAnchor_sameIdeal hdisc nm₂
  let w₁ : {w : zsqrtdNormFiber (D : ℤ) ((b * h : ℕ) : ℤ) //
      maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc z) =
        maximalOrderNormFiberIdealDivisor w} :=
    ⟨squareRelationSolutionNormFiberPoint hdisc nm₁, hideal₁⟩
  let w₂ : {w : zsqrtdNormFiber (D : ℤ) ((b * h : ℕ) : ℤ) //
      maximalOrderNormFiberIdealDivisor
          (squareRelationSolutionNormFiberPoint hdisc z) =
        maximalOrderNormFiberIdealDivisor w} :=
    ⟨squareRelationSolutionNormFiberPoint hdisc nm₂, hideal₂⟩
  have hw : w₁ = w₂ := by
    apply maximalOrderNormFiberAssociatedUnit_injective
      (squareRelationSolutionNormFiberPoint hdisc z)
    simpa only [w₁, w₂, squareRelationSolutionAssociatedUnit,
      z, I₁, I₂, hI'] using hU
  apply squareRelationSolutionNormFiberPoint_injective hdisc hb hc
  exact congrArg Subtype.val hw

/-- A solution's principal ideal, now indexed in the full finite set of
ideal divisors of `(b h)`. -/
noncomputable def squareRelationSolutionDivisorIndex
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)]
    (hdisc : a * b = D * c ^ 2) (hN : ((b * h : ℕ) : ℤ) ≠ 0)
    (nm : squareRelationSolutionType a b h x y) :
    {I : {J : Ideal (𝓞 (quadraticField D)) //
        J ∣ Ideal.span ({(((b * h : ℕ) : ℤ) :
          𝓞 (quadraticField D))} : Set (𝓞 (quadraticField D)))} //
      I ∈ maximalOrderIdealDivisors D ((b * h : ℕ) : ℤ) hN} :=
  ⟨maximalOrderNormFiberIdealDivisor
      (squareRelationSolutionNormFiberPoint
        (h := h) (x := x) (y := y) hdisc nm),
    maximalOrderNormFiberIdealDivisor_mem hN _⟩

/-- A solution's anchor-relative unit, indexed in the common finite
bounded-height candidate family. -/
noncomputable def squareRelationSolutionUnitIndex
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hh : 0 < h)
    (nm : squareRelationSolutionType a b h x y) :
    {u : (𝓞 (quadraticField D))ˣ //
      u ∈ quadraticUnitsUpToLogBound D
        (quadraticUnitLogCutoff (squareRelationBoxEnvelope b c D x y))} :=
  ⟨squareRelationSolutionAssociatedUnit hdisc nm,
    squareRelationSolutionAssociatedUnit_mem_uniformCandidates
      hdisc hb hh nm⟩

/-- The source orbit code: an ideal divisor together with one of the
uniformly bounded unit coordinates. -/
noncomputable def squareRelationSolutionOrbitCode
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hh : 0 < h)
    (hN : ((b * h : ℕ) : ℤ) ≠ 0)
    (nm : squareRelationSolutionType a b h x y) :=
  (squareRelationSolutionDivisorIndex hdisc hN nm,
    squareRelationSolutionUnitIndex hdisc hb hh nm)

/-- The full ideal-divisor/unit orbit code is injective. -/
theorem squareRelationSolutionOrbitCode_injective
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) (hN : ((b * h : ℕ) : ℤ) ≠ 0) :
    Function.Injective
      (squareRelationSolutionOrbitCode
        (h := h) (x := x) (y := y) hdisc hb hh hN) := by
  intro nm₁ nm₂ hcode
  apply squareRelationSolutionIdealIndex_unit_injective hdisc hb hc
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun q => q.1.1) (congrArg Prod.fst hcode)
  · exact congrArg (fun q => q.1) (congrArg Prod.snd hcode)

/-- Raw finite orbit count: the boxed solutions inject into the product of
the ideal-divisor family and the bounded-height unit family. -/
theorem card_squareRelationSolutionsBox_le_ideal_mul_unit
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) (hN : ((b * h : ℕ) : ℤ) ≠ 0) :
    (squareRelationSolutionsBox a b h x y).card ≤
      (maximalOrderIdealDivisors D ((b * h : ℕ) : ℤ) hN).card *
        (quadraticUnitsUpToLogBound D
          (quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y))).card := by
  let idealFamily :=
    maximalOrderIdealDivisors D ((b * h : ℕ) : ℤ) hN
  let unitFamily :=
    quadraticUnitsUpToLogBound D
      (quadraticUnitLogCutoff (squareRelationBoxEnvelope b c D x y))
  calc
    (squareRelationSolutionsBox a b h x y).card =
        Fintype.card (squareRelationSolutionType a b h x y) := by
      exact (Fintype.card_ofFinset
        (squareRelationSolutionsBox a b h x y) (by intro nm; rfl)).symm
    _ ≤ Fintype.card (↥idealFamily × ↥unitFamily) := by
      exact Fintype.card_le_of_injective
        (squareRelationSolutionOrbitCode
          (h := h) (x := x) (y := y) hdisc hb hh hN)
        (squareRelationSolutionOrbitCode_injective hdisc hb hc hh hN)
    _ = idealFamily.card * unitFamily.card := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]
    _ = (maximalOrderIdealDivisors D ((b * h : ℕ) : ℤ) hN).card *
        (quadraticUnitsUpToLogBound D
          (quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y))).card := rfl

/-- Explicit positive-shift nonsquare-branch estimate.  This is the exact
`d(bh)^2` ideal factor from Tao's proof, multiplied by the uniform
`2(2B+1)` count of unit exponents at the explicit logarithmic cutoff. -/
theorem card_squareRelationSolutionsBox_le_divisors_sq_mul_logCutoff
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) :
    (squareRelationSolutionsBox a b h x y).card ≤
      (b * h).divisors.card ^ 2 *
        (2 * (2 * quadraticUnitLogCutoff
          (squareRelationBoxEnvelope b c D x y) + 1)) := by
  have hbh : b * h ≠ 0 := Nat.mul_ne_zero
    (Nat.ne_of_gt hb) (Nat.ne_of_gt hh)
  have hN : ((b * h : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hbh
  calc
    (squareRelationSolutionsBox a b h x y).card ≤
        (maximalOrderIdealDivisors D ((b * h : ℕ) : ℤ) hN).card *
          (quadraticUnitsUpToLogBound D
            (quadraticUnitLogCutoff
              (squareRelationBoxEnvelope b c D x y))).card :=
      card_squareRelationSolutionsBox_le_ideal_mul_unit
        hdisc hb hc hh hN
    _ ≤ (((b * h : ℕ) : ℤ).natAbs.divisors.card ^ 2) *
        (2 * (2 * quadraticUnitLogCutoff
          (squareRelationBoxEnvelope b c D x y) + 1)) :=
      Nat.mul_le_mul
        (card_maximalOrderIdealDivisors_le_card_divisors_sq
          D ((b * h : ℕ) : ℤ) hN)
        (card_quadraticUnitsUpToLogBound_le D
          (quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y)))
    _ = (b * h).divisors.card ^ 2 *
        (2 * (2 * quadraticUnitLogCutoff
          (squareRelationBoxEnvelope b c D x y) + 1)) := by
      rw [Int.natAbs_natCast]

/-- Epsilon-power form of the positive-shift nonsquare estimate before the
polynomial parameter bounds are substituted. -/
theorem card_squareRelationSolutionsBox_le_epsilon_factors
    {a b c D h x y : ℕ} [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) {δ : ℝ} (hδ : 0 < δ)
    (hE : 1 ≤ squareRelationBoxEnvelope b c D x y) :
    ((squareRelationSolutionsBox a b h x y).card : ℝ) ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((b * h : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D x y) ^ δ) := by
  have hbh : b * h ≠ 0 := Nat.mul_ne_zero hb.ne' hh.ne'
  calc
    ((squareRelationSolutionsBox a b h x y).card : ℝ) ≤
        (((b * h).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y) + 1)) : ℕ) : ℝ) := by
      exact_mod_cast
        card_squareRelationSolutionsBox_le_divisors_sq_mul_logCutoff
          hdisc hb hc hh
    _ = ((b * h).divisors.card : ℝ) ^ 2 *
        ((2 * (2 * quadraticUnitLogCutoff
          (squareRelationBoxEnvelope b c D x y) + 1) : ℕ) : ℝ) := by
      norm_num
    _ ≤ (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((b * h : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D x y) ^ δ) := by
      gcongr
      · exact RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow
          hδ hbh
      · exact unitLogCutoffFactor_cast_le_const_mul_rpow hE hδ

/-! ## Restoring the source's nonzero integer shift -/

/-- For a nonnegative shift, the literal integer-shift solution box is the
natural-number solution box used by the norm construction. -/
theorem squareRelationSolutionsBoxInt_natCast_eq
    (a b h x y : ℕ) :
    squareRelationSolutionsBoxInt a b (h : ℤ) x y =
      squareRelationSolutionsBox a b h x y := by
  ext nm
  rw [mem_squareRelationSolutionsBoxInt, mem_squareRelationSolutionsBox]
  constructor
  · rintro ⟨hn, hnx, hm, hmy, heq⟩
    refine ⟨hn, hnx, hm, hmy, ?_⟩
    exact_mod_cast heq
  · rintro ⟨hn, hnx, hm, hmy, heq⟩
    refine ⟨hn, hnx, hm, hmy, ?_⟩
    exact_mod_cast heq

/-- Negating the shift exchanges the two variables and the two
coefficients.  The box endpoints are exchanged at the same time. -/
theorem card_squareRelationSolutionsBoxInt_neg_natCast_eq_swap
    (a b h x y : ℕ) :
    (squareRelationSolutionsBoxInt a b (-(h : ℤ)) x y).card =
      (squareRelationSolutionsBox b a h y x).card := by
  apply Finset.card_bij (fun nm _ ↦ nm.swap)
  · intro nm hnm
    obtain ⟨hn, hnx, hm, hmy, heq⟩ :=
      mem_squareRelationSolutionsBoxInt.mp hnm
    apply mem_squareRelationSolutionsBox.mpr
    refine ⟨hm, hmy, hn, hnx, ?_⟩
    exact_mod_cast (show
      (b : ℤ) * (nm.2 : ℤ) ^ 2 + h =
        (a : ℤ) * (nm.1 : ℤ) ^ 2 by linarith)
  · intro nm₁ hnm₁ nm₂ hnm₂ hswap
    exact Prod.swap_injective hswap
  · intro nm hnm
    refine ⟨nm.swap, ?_, nm.swap_swap⟩
    obtain ⟨hm, hmy, hn, hnx, heq⟩ :=
      mem_squareRelationSolutionsBox.mp hnm
    apply mem_squareRelationSolutionsBoxInt.mpr
    refine ⟨hn, hnx, hm, hmy, ?_⟩
    have heqZ :
        (b : ℤ) * (nm.1 : ℤ) ^ 2 + h =
          (a : ℤ) * (nm.2 : ℤ) ^ 2 := by
      exact_mod_cast heq
    change (a : ℤ) * (nm.2 : ℤ) ^ 2 + -(h : ℤ) =
      (b : ℤ) * (nm.1 : ℤ) ^ 2
    linarith

/-- Exact finite nonsquare-discriminant estimate for Tao's literal nonzero
integer shift.  The two summands record the positive and negative shift
orientations; exactly one is used in the proof. -/
theorem card_squareRelationSolutionsBoxInt_le_nonsquare_explicit
    {a b c D x y : ℕ} {h : ℤ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hh : h ≠ 0) :
    (squareRelationSolutionsBoxInt a b h x y).card ≤
      (b * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y) + 1)) +
        (a * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope a c D y x) + 1)) := by
  by_cases hpos : 0 < h
  · have hhNat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    have hcast : (h.natAbs : ℤ) = h :=
      Int.natAbs_of_nonneg hpos.le
    calc
      (squareRelationSolutionsBoxInt a b h x y).card =
          (squareRelationSolutionsBox a b h.natAbs x y).card := by
        calc
          (squareRelationSolutionsBoxInt a b h x y).card =
              (squareRelationSolutionsBoxInt a b
                (h.natAbs : ℤ) x y).card :=
            congrArg
              (fun k : ℤ =>
                (squareRelationSolutionsBoxInt a b k x y).card)
              hcast.symm
          _ = (squareRelationSolutionsBox a b h.natAbs x y).card := by
            rw [squareRelationSolutionsBoxInt_natCast_eq]
      _ ≤ (b * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x y) + 1)) :=
        card_squareRelationSolutionsBox_le_divisors_sq_mul_logCutoff
          hdisc hb hc hhNat
      _ ≤ (b * h.natAbs).divisors.card ^ 2 *
            (2 * (2 * quadraticUnitLogCutoff
              (squareRelationBoxEnvelope b c D x y) + 1)) +
          (a * h.natAbs).divisors.card ^ 2 *
            (2 * (2 * quadraticUnitLogCutoff
              (squareRelationBoxEnvelope a c D y x) + 1)) :=
        Nat.le_add_right _ _
  · have hneg : h < 0 := by omega
    have hhNat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    have hcast : -(h.natAbs : ℤ) = h := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
      ring
    have hdiscSwap : b * a = D * c ^ 2 := by
      simpa only [Nat.mul_comm] using hdisc
    calc
      (squareRelationSolutionsBoxInt a b h x y).card =
          (squareRelationSolutionsBox b a h.natAbs y x).card := by
        calc
          (squareRelationSolutionsBoxInt a b h x y).card =
              (squareRelationSolutionsBoxInt a b
                (-(h.natAbs : ℤ)) x y).card :=
            congrArg
              (fun k : ℤ =>
                (squareRelationSolutionsBoxInt a b k x y).card)
              hcast.symm
          _ = (squareRelationSolutionsBox b a h.natAbs y x).card :=
            card_squareRelationSolutionsBoxInt_neg_natCast_eq_swap
              a b h.natAbs x y
      _ ≤ (a * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope a c D y x) + 1)) :=
        card_squareRelationSolutionsBox_le_divisors_sq_mul_logCutoff
          hdiscSwap ha hc hhNat
      _ ≤ (b * h.natAbs).divisors.card ^ 2 *
            (2 * (2 * quadraticUnitLogCutoff
              (squareRelationBoxEnvelope b c D x y) + 1)) +
          (a * h.natAbs).divisors.card ^ 2 *
            (2 * (2 * quadraticUnitLogCutoff
              (squareRelationBoxEnvelope a c D y x) + 1)) :=
        Nat.le_add_left _ _

/-- Epsilon-power form of the literal signed nonsquare estimate.  This is
the analytic `x^{o(1)}` engine: divisor factors and the logarithmic unit
factor may all be assigned an arbitrarily small positive exponent. -/
theorem card_squareRelationSolutionsBoxInt_le_nonsquare_epsilon_factors
    {a b c D x y : ℕ} {h : ℤ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hh : h ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hEpos : 1 ≤ squareRelationBoxEnvelope b c D x y)
    (hEneg : 1 ≤ squareRelationBoxEnvelope a c D y x) :
    ((squareRelationSolutionsBoxInt a b h x y).card : ℝ) ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((b * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D x y) ^ δ) +
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((a * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope a c D y x) ^ δ) := by
  by_cases hpos : 0 < h
  · have hhNat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    have hcast : (h.natAbs : ℤ) = h :=
      Int.natAbs_of_nonneg hpos.le
    have hcard :
        (squareRelationSolutionsBoxInt a b h x y).card =
          (squareRelationSolutionsBox a b h.natAbs x y).card := by
      calc
        (squareRelationSolutionsBoxInt a b h x y).card =
            (squareRelationSolutionsBoxInt a b
              (h.natAbs : ℤ) x y).card :=
          congrArg
            (fun k : ℤ =>
              (squareRelationSolutionsBoxInt a b k x y).card)
            hcast.symm
        _ = (squareRelationSolutionsBox a b h.natAbs x y).card := by
          rw [squareRelationSolutionsBoxInt_natCast_eq]
    rw [hcard]
    exact (card_squareRelationSolutionsBox_le_epsilon_factors
      hdisc hb hc hhNat hδ hEpos).trans
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _)
          (mul_nonneg (quadraticUnitEpsilonConstant_pos hδ).le
            (Real.rpow_nonneg (by
              unfold squareRelationBoxEnvelope
              positivity) _))))
  · have hneg : h < 0 := by omega
    have hhNat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    have hcast : -(h.natAbs : ℤ) = h := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
      ring
    have hdiscSwap : b * a = D * c ^ 2 := by
      simpa only [Nat.mul_comm] using hdisc
    have hcard :
        (squareRelationSolutionsBoxInt a b h x y).card =
          (squareRelationSolutionsBox b a h.natAbs y x).card := by
      calc
        (squareRelationSolutionsBoxInt a b h x y).card =
            (squareRelationSolutionsBoxInt a b
              (-(h.natAbs : ℤ)) x y).card :=
          congrArg
            (fun k : ℤ =>
              (squareRelationSolutionsBoxInt a b k x y).card)
            hcast.symm
        _ = (squareRelationSolutionsBox b a h.natAbs y x).card :=
          card_squareRelationSolutionsBoxInt_neg_natCast_eq_swap
            a b h.natAbs x y
    rw [hcard]
    exact (card_squareRelationSolutionsBox_le_epsilon_factors
      hdiscSwap ha hc hhNat hδ hEneg).trans
        (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _)
          (mul_nonneg (quadraticUnitEpsilonConstant_pos hδ).le
            (Real.rpow_nonneg (by
              unfold squareRelationBoxEnvelope
              positivity) _))))

/-! ## Removing the auxiliary bound on `m` -/

/-- The literal finite set in Tao's Lemma 2.10.  Only `n ≤ x` appears in
the source.  The displayed `m` cutoff is a proved redundant polynomial
bound, chosen solely to represent the set as a `Finset`. -/
noncomputable def squareRelationSolutionsUpTo
    (a b : ℕ) (h : ℤ) (x : ℕ) : Finset (ℕ × ℕ) :=
  squareRelationSolutionsBoxInt a b h x (a * x ^ 2 + h.natAbs)

theorem mem_squareRelationSolutionsUpTo
    {a b : ℕ} {h : ℤ} {x : ℕ} {nm : ℕ × ℕ}
    (hb : 0 < b) :
    nm ∈ squareRelationSolutionsUpTo a b h x ↔
      1 ≤ nm.1 ∧ nm.1 ≤ x ∧ 1 ≤ nm.2 ∧
        (a : ℤ) * (nm.1 : ℤ) ^ 2 + h =
          (b : ℤ) * (nm.2 : ℤ) ^ 2 := by
  rw [squareRelationSolutionsUpTo, mem_squareRelationSolutionsBoxInt]
  constructor
  · rintro ⟨hn, hnx, hm, hmy, heq⟩
    exact ⟨hn, hnx, hm, heq⟩
  · rintro ⟨hn, hnx, hm, heq⟩
    refine ⟨hn, hnx, hm, ?_, heq⟩
    have hnSq : nm.1 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hnx 2
    have han : a * nm.1 ^ 2 ≤ a * x ^ 2 :=
      Nat.mul_le_mul_left a hnSq
    have hhAbs : h ≤ (h.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self h
    have hbm : b * nm.2 ^ 2 ≤ a * nm.1 ^ 2 + h.natAbs := by
      exact_mod_cast (show
        (b : ℤ) * (nm.2 : ℤ) ^ 2 ≤
          (a : ℤ) * (nm.1 : ℤ) ^ 2 + (h.natAbs : ℤ) by
        linarith)
    have hm_le_bm : nm.2 ≤ b * nm.2 ^ 2 := by
      nlinarith
    omega

/-- In a positive squarefree-discriminant decomposition, the discriminant
is no larger than the original coefficient product. -/
theorem squareRelationDiscriminant_le_product
    {a b c D : ℕ} (hdisc : a * b = D * c ^ 2) (hc : 0 < c) :
    D ≤ a * b := by
  rw [hdisc]
  exact Nat.le_mul_of_pos_right D (pow_pos hc 2)

/-- The square scale in the same decomposition is also bounded by the
coefficient product. -/
theorem squareRelationScale_le_product
    {a b c D : ℕ} (hdisc : a * b = D * c ^ 2)
    (hc : 0 < c) (hD : 0 < D) :
    c ≤ a * b := by
  rw [hdisc]
  calc
    c ≤ c ^ 2 := by nlinarith
    _ ≤ D * c ^ 2 := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right (c ^ 2) hD

/-- A common bound for all five natural parameters gives a cubic bound for
the real place envelope. -/
theorem squareRelationBoxEnvelope_le_three_mul_cube
    {b c D x y T : ℕ} (hT : 1 ≤ T)
    (hb : b ≤ T) (hc : c ≤ T) (hD : D ≤ T)
    (hx : x ≤ T) (hy : y ≤ T) :
    squareRelationBoxEnvelope b c D x y ≤ 3 * (T : ℝ) ^ 3 := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hbR : (b : ℝ) ≤ T := by exact_mod_cast hb
  have hcR : (c : ℝ) ≤ T := by exact_mod_cast hc
  have hDR : (D : ℝ) ≤ T := by exact_mod_cast hD
  have hxR : (x : ℝ) ≤ T := by exact_mod_cast hx
  have hyR : (y : ℝ) ≤ T := by exact_mod_cast hy
  unfold squareRelationBoxEnvelope
  calc
    (b : ℝ) * y + (c : ℝ) * x * ((D : ℝ) + 1) ≤
        (T : ℝ) * T + (T : ℝ) * T * ((T : ℝ) + 1) := by
      gcongr
    _ ≤ 3 * (T : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (T : ℝ))
        (sub_nonneg.mpr hTR)]

/-- Under one common `X^K` bound for the coefficients, both signed
orientations of the source box have a single explicit polynomial height
majorant. -/
theorem squareRelationSourceEnvelopes_le_polynomial
    {a b c D H X K : ℕ} (hX : 0 < X)
    (ha : a ≤ X ^ K) (hb : b ≤ X ^ K) (hH : H ≤ X ^ K)
    (hdisc : a * b = D * c ^ 2) (hc : 0 < c) (hD : 0 < D) :
    squareRelationBoxEnvelope b c D X (a * X ^ 2 + H) ≤
        3 * ((2 * X ^ (2 * K + 2) : ℕ) : ℝ) ^ 3 ∧
      squareRelationBoxEnvelope a c D (a * X ^ 2 + H) X ≤
        3 * ((2 * X ^ (2 * K + 2) : ℕ) : ℝ) ^ 3 := by
  let T := 2 * X ^ (2 * K + 2)
  have hXOne : 1 ≤ X := hX
  have hpowK : X ^ K ≤ X ^ (2 * K + 2) :=
    Nat.pow_le_pow_right hX (by omega)
  have hpowK2 : X ^ (K + 2) ≤ X ^ (2 * K + 2) :=
    Nat.pow_le_pow_right hX (by omega)
  have hpow2K : X ^ (2 * K) ≤ X ^ (2 * K + 2) :=
    Nat.pow_le_pow_right hX (by omega)
  have hbaseT : X ^ (2 * K + 2) ≤ T := by
    dsimp [T]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hT : 1 ≤ T := by
    have hTpos : 0 < T := by
      dsimp [T]
      exact mul_pos (by omega) (pow_pos hX _)
    omega
  have haT : a ≤ T := ha.trans (hpowK.trans hbaseT)
  have hbT : b ≤ T := hb.trans (hpowK.trans hbaseT)
  have hXT : X ≤ T := by
    have hxp : X ^ 1 ≤ X ^ (2 * K + 2) :=
      Nat.pow_le_pow_right hX (by omega)
    simpa only [pow_one] using hxp.trans hbaseT
  have hab : a * b ≤ X ^ (2 * K) := by
    calc
      a * b ≤ X ^ K * X ^ K := Nat.mul_le_mul ha hb
      _ = X ^ (2 * K) := by
        rw [← pow_add]
        congr 1
        omega
  have hcT : c ≤ T :=
    (squareRelationScale_le_product hdisc hc hD).trans
      (hab.trans (hpow2K.trans hbaseT))
  have hDT : D ≤ T :=
    (squareRelationDiscriminant_le_product hdisc hc).trans
      (hab.trans (hpow2K.trans hbaseT))
  have haX2 : a * X ^ 2 ≤ X ^ (K + 2) := by
    calc
      a * X ^ 2 ≤ X ^ K * X ^ 2 := Nat.mul_le_mul_right _ ha
      _ = X ^ (K + 2) := by rw [pow_add]
  have hHK2 : H ≤ X ^ (K + 2) :=
    hH.trans (Nat.pow_le_pow_right hX (by omega))
  have hySmall : a * X ^ 2 + H ≤ 2 * X ^ (K + 2) := by
    omega
  have hyT : a * X ^ 2 + H ≤ T := by
    dsimp [T]
    exact hySmall.trans (Nat.mul_le_mul_left 2 hpowK2)
  constructor
  · simpa only [T] using squareRelationBoxEnvelope_le_three_mul_cube
      hT hbT hcT hDT hXT hyT
  · simpa only [T] using squareRelationBoxEnvelope_le_three_mul_cube
      hT haT hcT hDT hyT hXT

theorem three_mul_squareRelationMasterCube_eq
    (X K : ℕ) :
    3 * ((2 * X ^ (2 * K + 2) : ℕ) : ℝ) ^ 3 =
      24 * ((X ^ (6 * K + 6) : ℕ) : ℝ) := by
  norm_cast
  calc
    3 * (2 * X ^ (2 * K + 2)) ^ 3 =
        24 * (X ^ (2 * K + 2)) ^ 3 := by ring
    _ = 24 * X ^ ((2 * K + 2) * 3) := by rw [pow_mul]
    _ = 24 * X ^ (6 * K + 6) := by
      congr 2
      omega

/-- Exact nonsquare estimate for the source-facing set, with the redundant
`m` cutoff instantiated by its proved polynomial value. -/
theorem card_squareRelationSolutionsUpTo_le_nonsquare_explicit
    {a b c D x : ℕ} {h : ℤ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hh : h ≠ 0) :
    (squareRelationSolutionsUpTo a b h x).card ≤
      (b * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope b c D x
              (a * x ^ 2 + h.natAbs)) + 1)) +
        (a * h.natAbs).divisors.card ^ 2 *
          (2 * (2 * quadraticUnitLogCutoff
            (squareRelationBoxEnvelope a c D
              (a * x ^ 2 + h.natAbs) x) + 1)) := by
  exact card_squareRelationSolutionsBoxInt_le_nonsquare_explicit
    hdisc ha hb hc hh

/-- Epsilon-factor estimate for the literal set in Lemma 2.10. -/
theorem card_squareRelationSolutionsUpTo_le_nonsquare_epsilon_factors
    {a b c D x : ℕ} {h : ℤ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hh : h ≠ 0) (hx : 0 < x)
    {δ : ℝ} (hδ : 0 < δ) :
    ((squareRelationSolutionsUpTo a b h x).card : ℝ) ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((b * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D x
            (a * x ^ 2 + h.natAbs)) ^ δ) +
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((a * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope a c D
            (a * x ^ 2 + h.natAbs) x) ^ δ) := by
  have hhAbs : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  have hy : 0 < a * x ^ 2 + h.natAbs := by omega
  have hEpos : 1 ≤ squareRelationBoxEnvelope b c D x
      (a * x ^ 2 + h.natAbs) := by
    have hby : 1 ≤ b * (a * x ^ 2 + h.natAbs) :=
      Nat.mul_pos hb hy
    calc
      (1 : ℝ) ≤ (b * (a * x ^ 2 + h.natAbs) : ℕ) := by
        exact_mod_cast hby
      _ ≤ squareRelationBoxEnvelope b c D x
          (a * x ^ 2 + h.natAbs) := by
        unfold squareRelationBoxEnvelope
        push_cast
        apply le_add_of_nonneg_right
        positivity
  have hEneg : 1 ≤ squareRelationBoxEnvelope a c D
      (a * x ^ 2 + h.natAbs) x := by
    have hax : 1 ≤ a * x := Nat.mul_pos ha hx
    calc
      (1 : ℝ) ≤ (a * x : ℕ) := by exact_mod_cast hax
      _ ≤ squareRelationBoxEnvelope a c D
          (a * x ^ 2 + h.natAbs) x := by
        unfold squareRelationBoxEnvelope
        push_cast
        apply le_add_of_nonneg_right
        positivity
  exact card_squareRelationSolutionsBoxInt_le_nonsquare_epsilon_factors
    hdisc ha hb hc hh hδ hEpos hEneg

/-- A single polynomial majorant for the nonsquare branch when
`a,b,|h| ≤ X^K`. -/
noncomputable def squareRelationNonsquarePolynomialMajorant
    (X K : ℕ) (δ : ℝ) : ℝ :=
  2 *
    (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
      (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
    (quadraticUnitEpsilonConstant δ *
      ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ)

theorem card_squareRelationSolutionsUpTo_le_nonsquare_polynomialMajorant
    {a b c D X K : ℕ} {h : ℤ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hh : h ≠ 0) (hX : 0 < X)
    (haX : a ≤ X ^ K) (hbX : b ≤ X ^ K)
    (hhX : h.natAbs ≤ X ^ K) {δ : ℝ} (hδ : 0 < δ) :
    ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤
      squareRelationNonsquarePolynomialMajorant X K δ := by
  have hprodA : a * h.natAbs ≤ X ^ (2 * K) := by
    calc
      a * h.natAbs ≤ X ^ K * X ^ K := Nat.mul_le_mul haX hhX
      _ = X ^ (2 * K) := by
        rw [← pow_add]
        congr 1
        omega
  have hprodB : b * h.natAbs ≤ X ^ (2 * K) := by
    calc
      b * h.natAbs ≤ X ^ K * X ^ K := Nat.mul_le_mul hbX hhX
      _ = X ^ (2 * K) := by
        rw [← pow_add]
        congr 1
        omega
  obtain ⟨hEpos, hEneg⟩ := squareRelationSourceEnvelopes_le_polynomial
    hX haX hbX hhX hdisc hc Fact.out
  rw [three_mul_squareRelationMasterCube_eq] at hEpos hEneg
  have hbaseA :
      (((a * h.natAbs : ℕ) : ℝ) ^ δ) ≤
        (((X ^ (2 * K) : ℕ) : ℝ) ^ δ) := by
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hprodA) hδ.le
  have hbaseB :
      (((b * h.natAbs : ℕ) : ℝ) ^ δ) ≤
        (((X ^ (2 * K) : ℕ) : ℝ) ^ δ) := by
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hprodB) hδ.le
  have hheightPos :
      (squareRelationBoxEnvelope b c D X
        (a * X ^ 2 + h.natAbs)) ^ δ ≤
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ := by
    apply Real.rpow_le_rpow
      (by unfold squareRelationBoxEnvelope; positivity) hEpos hδ.le
  have hheightNeg :
      (squareRelationBoxEnvelope a c D
        (a * X ^ 2 + h.natAbs) X) ^ δ ≤
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ := by
    apply Real.rpow_le_rpow
      (by unfold squareRelationBoxEnvelope; positivity) hEneg hδ.le
  have hraw :=
    card_squareRelationSolutionsUpTo_le_nonsquare_epsilon_factors
      hdisc ha hb hc hh hX hδ
  have hCd : 0 ≤ RiemannZeta.GuthMaynard.divisorEpsilonConstant δ :=
    (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ).le
  have hCu : 0 ≤ quadraticUnitEpsilonConstant δ :=
    (quadraticUnitEpsilonConstant_pos hδ).le
  have hdivA :
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        (((a * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 := by
    gcongr
  have hdivB :
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        (((b * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 := by
    gcongr
  have hunitPos :
      quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D X
            (a * X ^ 2 + h.natAbs)) ^ δ ≤
        quadraticUnitEpsilonConstant δ *
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ :=
    mul_le_mul_of_nonneg_left hheightPos hCu
  have hunitNeg :
      quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope a c D
            (a * X ^ 2 + h.natAbs) X) ^ δ ≤
        quadraticUnitEpsilonConstant δ *
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ :=
    mul_le_mul_of_nonneg_left hheightNeg hCu
  have htermPos :
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((b * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope b c D X
            (a * X ^ 2 + h.natAbs)) ^ δ) ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ) := by
    exact mul_le_mul hdivB hunitPos
      (mul_nonneg hCu (Real.rpow_nonneg (by
        unfold squareRelationBoxEnvelope
        positivity) _)) (sq_nonneg _)
  have htermNeg :
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((a * h.natAbs : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          (squareRelationBoxEnvelope a c D
            (a * X ^ 2 + h.natAbs) X) ^ δ) ≤
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ) := by
    exact mul_le_mul hdivA hunitNeg
      (mul_nonneg hCu (Real.rpow_nonneg (by
        unfold squareRelationBoxEnvelope
        positivity) _)) (sq_nonneg _)
  unfold squareRelationNonsquarePolynomialMajorant
  calc
    ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤ _ := hraw
    _ ≤
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
            (quadraticUnitEpsilonConstant δ *
              ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ) +
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
            (quadraticUnitEpsilonConstant δ *
              ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ) :=
      add_le_add htermPos htermNeg
    _ = 2 *
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ^ 2 *
        (quadraticUnitEpsilonConstant δ *
          ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ) := by ring

/-- One uniform majorant covering both the split and nonsquare
discriminant branches. -/
noncomputable def squareRelationPolynomialMajorant
    (X K : ℕ) (δ : ℝ) : ℝ :=
  2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
      (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) +
    squareRelationNonsquarePolynomialMajorant X K δ

theorem natPow_cast_rpow_eq_rpow_mul
    (X n : ℕ) (δ : ℝ) :
    (((X ^ n : ℕ) : ℝ) ^ δ) =
      (X : ℝ) ^ ((n : ℝ) * δ) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact (Real.rpow_mul (by positivity) (n : ℝ) δ).symm

theorem rpow_sq_mul_rpow
    {X u v : ℝ} (hX : 0 < X) :
    (X ^ u) ^ 2 * X ^ v = X ^ (2 * u + v) := by
  rw [← Real.rpow_mul_natCast hX.le, ← Real.rpow_add hX]
  congr 1
  ring

/-- Constant in the final common-power majorant for Lemma 2.10. -/
noncomputable def squareRelationPolynomialEpsilonConstant (δ : ℝ) : ℝ :=
  2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ +
    2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
      quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ

theorem squareRelationPolynomialEpsilonConstant_pos
    {δ : ℝ} (hδ : 0 < δ) :
    0 < squareRelationPolynomialEpsilonConstant δ := by
  unfold squareRelationPolynomialEpsilonConstant
  have hCd := RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ
  apply add_pos_of_pos_of_nonneg
  · exact mul_pos (by norm_num) hCd
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (quadraticUnitEpsilonConstant_pos hδ).le)
      (Real.rpow_nonneg (by norm_num) _)

/-- The explicit branchwise majorant is a constant times the common power
`X^((10K+6)δ)`. -/
theorem squareRelationPolynomialMajorant_le_const_mul_rpow
    {X K : ℕ} {δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    squareRelationPolynomialMajorant X K δ ≤
      squareRelationPolynomialEpsilonConstant δ *
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp :
      ((2 * K : ℕ) : ℝ) * δ ≤ ((10 * K + 6 : ℕ) : ℝ) * δ := by
    push_cast
    nlinarith
  have hsmallPower :
      (X : ℝ) ^ (((2 * K : ℕ) : ℝ) * δ) ≤
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) :=
    Real.rpow_le_rpow_of_exponent_le hXR hexp
  have hsplit :
      2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) ≤
      (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ) *
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) := by
    rw [natPow_cast_rpow_eq_rpow_mul]
    calc
      2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (X : ℝ) ^ (((2 * K : ℕ) : ℝ) * δ)) =
        (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ) *
          (X : ℝ) ^ (((2 * K : ℕ) : ℝ) * δ) := by ring
      _ ≤ (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ) *
          (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hsmallPower
          (mul_pos (show (0 : ℝ) < 2 by norm_num)
            (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ)).le
  have hheightPower :
      ((24 : ℝ) * ((X ^ (6 * K + 6) : ℕ) : ℝ)) ^ δ =
        (24 : ℝ) ^ δ *
          (X : ℝ) ^ (((6 * K + 6 : ℕ) : ℝ) * δ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      natPow_cast_rpow_eq_rpow_mul]
  have hexponent :
      2 * (((2 * K : ℕ) : ℝ) * δ) +
          ((6 * K + 6 : ℕ) : ℝ) * δ =
        ((10 * K + 6 : ℕ) : ℝ) * δ := by
    push_cast
    ring
  have hnonsquare :
      squareRelationNonsquarePolynomialMajorant X K δ =
        (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
          quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) := by
    unfold squareRelationNonsquarePolynomialMajorant
    rw [natPow_cast_rpow_eq_rpow_mul, hheightPower]
    calc
      2 *
          (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
            (X : ℝ) ^ (((2 * K : ℕ) : ℝ) * δ)) ^ 2 *
          (quadraticUnitEpsilonConstant δ *
            ((24 : ℝ) ^ δ *
              (X : ℝ) ^ (((6 * K + 6 : ℕ) : ℝ) * δ))) =
        (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
          quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
          (((X : ℝ) ^ (((2 * K : ℕ) : ℝ) * δ)) ^ 2 *
            (X : ℝ) ^ (((6 * K + 6 : ℕ) : ℝ) * δ)) := by ring
      _ = (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
          quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
          (X : ℝ) ^
            (2 * (((2 * K : ℕ) : ℝ) * δ) +
              ((6 * K + 6 : ℕ) : ℝ) * δ) := by
        rw [rpow_sq_mul_rpow hXpos]
      _ = (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
          quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
          (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) := by
        rw [hexponent]
  unfold squareRelationPolynomialMajorant
    squareRelationPolynomialEpsilonConstant
  rw [hnonsquare]
  calc
    2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) +
        (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
            quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
          (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) ≤
      (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ) *
          (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) +
        (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
            quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
          (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) :=
      add_le_add hsplit (le_refl _)
    _ = (2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ +
          2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant δ ^ 2 *
            quadraticUnitEpsilonConstant δ * (24 : ℝ) ^ δ) *
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) := by ring

/-- Pointwise uniform form of Tao's Lemma 2.10 under the literal polynomial
parameter hypothesis `a,b,|h| ≤ X^K`.  No discriminant decomposition remains
in the statement. -/
theorem card_squareRelationSolutionsUpTo_le_polynomialMajorant
    {a b X K : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hh : h ≠ 0) (hX : 0 < X)
    (haX : a ≤ X ^ K) (hbX : b ≤ X ^ K)
    (hhX : h.natAbs ≤ X ^ K) {δ : ℝ} (hδ : 0 < δ) :
    ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤
      squareRelationPolynomialMajorant X K δ := by
  obtain ⟨c, D, hc, hD, hDsquarefree, hdisc⟩ :=
    exists_squarefree_discriminant ha hb
  by_cases hDone : D = 1
  · have hcSq : c ^ 2 = a * b := by
      simpa only [hDone, one_mul] using hdisc.symm
    have hprodA : a * h.natAbs ≤ X ^ (2 * K) := by
      calc
        a * h.natAbs ≤ X ^ K * X ^ K := Nat.mul_le_mul haX hhX
        _ = X ^ (2 * K) := by
          rw [← pow_add]
          congr 1
          omega
    have hdiv := RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow
      hδ (Nat.mul_ne_zero ha.ne' (Int.natAbs_pos.mpr hh).ne')
    have hpow :
        (((a * h.natAbs : ℕ) : ℝ) ^ δ) ≤
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hprodA) hδ.le
    unfold squareRelationPolynomialMajorant
    calc
      ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤
          (2 * (a * h.natAbs).divisors.card : ℕ) := by
        exact_mod_cast
          card_squareRelationSolutionsBoxInt_le_two_mul_divisors_of_mul_isSquare
            ha hc hh hcSq
      _ = 2 * ((a * h.natAbs).divisors.card : ℝ) := by norm_num
      _ ≤ 2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((a * h.natAbs : ℕ) : ℝ) ^ δ)) := by gcongr
      _ ≤ 2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
          (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) := by
        gcongr
        exact (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ).le
      _ ≤ 2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
            (((X ^ (2 * K) : ℕ) : ℝ) ^ δ)) +
          squareRelationNonsquarePolynomialMajorant X K δ :=
        le_add_of_nonneg_right (by
          unfold squareRelationNonsquarePolynomialMajorant
          exact mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg _))
            (mul_nonneg (quadraticUnitEpsilonConstant_pos hδ).le
              (Real.rpow_nonneg (by positivity) _)))
  · have hDgt : 1 < D := by omega
    have hnotSquare : ¬IsSquare D := by
      intro hs
      exact not_isSquare_intCast_of_squarefree_of_one_lt hDsquarefree hDgt
        ((Int.isSquare_natCast_iff).2 hs)
    letI : Fact (¬IsSquare D) := ⟨hnotSquare⟩
    letI : Fact (0 < D) := ⟨hD⟩
    unfold squareRelationPolynomialMajorant
    exact (card_squareRelationSolutionsUpTo_le_nonsquare_polynomialMajorant
      hdisc ha hb hc hh hX haX hbX hhX hδ).trans
        (le_add_of_nonneg_left (by
          exact mul_nonneg
            (by positivity)
            (mul_nonneg
              (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ).le
              (Real.rpow_nonneg (by positivity) _))))

/-- Fully absorbed pointwise epsilon estimate.  For each polynomial exponent
`K` and each `ε>0`, the implied constant is independent of `a,b,h,X`. -/
theorem card_squareRelationSolutionsUpTo_le_const_mul_rpow
    {a b X K : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hh : h ≠ 0) (hX : 0 < X)
    (haX : a ≤ X ^ K) (hbX : b ≤ X ^ K)
    (hhX : h.natAbs ≤ X ^ K) {ε : ℝ} (hε : 0 < ε) :
    ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤
      squareRelationPolynomialEpsilonConstant
          (ε / ((10 * K + 6 : ℕ) : ℝ)) *
        (X : ℝ) ^ ε := by
  let δ : ℝ := ε / ((10 * K + 6 : ℕ) : ℝ)
  have hden : (0 : ℝ) < ((10 * K + 6 : ℕ) : ℝ) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  calc
    ((squareRelationSolutionsUpTo a b h X).card : ℝ) ≤
        squareRelationPolynomialMajorant X K δ :=
      card_squareRelationSolutionsUpTo_le_polynomialMajorant
        ha hb hh hX haX hbX hhX hδ
    _ ≤ squareRelationPolynomialEpsilonConstant δ *
        (X : ℝ) ^ (((10 * K + 6 : ℕ) : ℝ) * δ) :=
      squareRelationPolynomialMajorant_le_const_mul_rpow hX hδ
    _ = squareRelationPolynomialEpsilonConstant
          (ε / ((10 * K + 6 : ℕ) : ℝ)) *
        (X : ℝ) ^ ε := by
      have hexp : ((10 * K + 6 : ℕ) : ℝ) * δ = ε := by
        dsimp [δ]
        field_simp
      rw [hexp]

/-! ## Source asymptotic contract -/

/-- A natural-valued parameter is eventually bounded by one fixed power of
the asymptotic variable.  Eventual omission of a multiplicative constant is
equivalent to the paper's `≪ X^{O(1)}` convention after increasing the
integer exponent. -/
def PolynomiallyBoundedNatSequence (f : ℕ → ℕ) : Prop :=
  ∃ K : ℕ, ∀ᶠ X : ℕ in Filter.atTop, f X ≤ X ^ K

/-- Integer-valued version, measured by absolute value as in the source. -/
def PolynomiallyBoundedIntSequence (f : ℕ → ℤ) : Prop :=
  PolynomiallyBoundedNatSequence fun X => (f X).natAbs

/-- Source-faithful family form of Lemma 2.10: uniformly for positive
natural coefficients and a nonzero integer shift that are polynomially
bounded in `X`, the number of positive solutions with `n ≤ X` is
`X^{o(1)}`. -/
theorem squareRelationSolutionsUpTo_powerUpperBound
    (a b : ℕ → ℕ) (h : ℕ → ℤ)
    (haPoly : PolynomiallyBoundedNatSequence a)
    (hbPoly : PolynomiallyBoundedNatSequence b)
    (hhPoly : PolynomiallyBoundedIntSequence h)
    (haPos : ∀ᶠ X : ℕ in Filter.atTop, 0 < a X)
    (hbPos : ∀ᶠ X : ℕ in Filter.atTop, 0 < b X)
    (hhNe : ∀ᶠ X : ℕ in Filter.atTop, h X ≠ 0) :
    PowerUpperBound
      (fun X : ℕ =>
        ((squareRelationSolutionsUpTo (a X) (b X) (h X) X).card : ℝ))
      0 := by
  obtain ⟨Ka, haBound⟩ := haPoly
  obtain ⟨Kb, hbBound⟩ := hbPoly
  obtain ⟨Kh, hhBound⟩ := hhPoly
  let K := max Ka (max Kb Kh)
  intro ε hε
  let C := squareRelationPolynomialEpsilonConstant
    (ε / ((10 * K + 6 : ℕ) : ℝ))
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [haBound, hbBound, hhBound, haPos, hbPos, hhNe,
    Filter.eventually_ge_atTop 1] with X haX hbX hhX haXPos hbXPos hhXNe hX
  have hXPos : 0 < X := by omega
  have hKaK : Ka ≤ K := le_max_left _ _
  have hKbK : Kb ≤ K := le_trans (le_max_left _ _)
    (le_max_right _ _)
  have hKhK : Kh ≤ K := le_trans (le_max_right _ _)
    (le_max_right _ _)
  have haXK : a X ≤ X ^ K :=
    haX.trans (Nat.pow_le_pow_right hXPos hKaK)
  have hbXK : b X ≤ X ^ K :=
    hbX.trans (Nat.pow_le_pow_right hXPos hKbK)
  have hhXK : (h X).natAbs ≤ X ^ K :=
    hhX.trans (Nat.pow_le_pow_right hXPos hKhK)
  have hmain := card_squareRelationSolutionsUpTo_le_const_mul_rpow
    haXPos hbXPos hhXNe hXPos haXK hbXK hhXK hε
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), zero_add,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact hmain

end Tao2026
