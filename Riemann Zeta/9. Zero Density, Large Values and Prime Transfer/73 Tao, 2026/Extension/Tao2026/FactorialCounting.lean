import Tao2026.FactorialExtraction
import Tao2026.QuadraticSolutionCount

/-!
# Finite counting reduction for Tao's Theorem 1.9

This file turns Lemma 4.3 into an exact finite encoding of non-one-term
type-`F₃` endpoints.  It keeps interval witnesses separate from endpoint
values, chooses one bounded smooth square-relation certificate for each
interval, and records the interval length and selected-element offset.  These
data recover the interval start, so no multiplicity is lost before the source
case split is applied.
-/

open Filter Asymptotics

namespace Tao2026

noncomputable section

/-! ## Nontrivial endpoints and their interval witnesses -/

/-- The literal finite set counted by `nontrivialFactorialThreeCount`. -/
noncomputable def nontrivialFactorialThreeNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n =>
    n ∈ factorialThreeSet \ factorialThreeOneTermSet

@[simp]
theorem card_nontrivialFactorialThreeNumbersUpTo (x : ℕ) :
    (nontrivialFactorialThreeNumbersUpTo x).card =
      nontrivialFactorialThreeCount x := by
  classical
  unfold nontrivialFactorialThreeNumbersUpTo
    nontrivialFactorialThreeCount countUpTo
  congr

theorem mem_nontrivialFactorialThreeNumbersUpTo {x n : ℕ} :
    n ∈ nontrivialFactorialThreeNumbersUpTo x ↔
      1 ≤ n ∧ n ≤ x ∧ n ∈ factorialThreeSet ∧
        n ∉ factorialThreeOneTermSet := by
  classical
  simp [nontrivialFactorialThreeNumbersUpTo, and_assoc]

/-- All length-at-least-two type-`F₃` interval witnesses whose right endpoint
is at most `x`. -/
noncomputable def nontrivialFactorialThreeIntervalsUpTo (x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 0 x).product (Finset.Icc 2 x)).filter fun t =>
    t.1 + t.2 ≤ x ∧ IsFactorialThreeInterval t.1 t.2

theorem mem_nontrivialFactorialThreeIntervalsUpTo
    {x : ℕ} {t : ℕ × ℕ} :
    t ∈ nontrivialFactorialThreeIntervalsUpTo x ↔
      t.1 ≤ x ∧ 2 ≤ t.2 ∧ t.2 ≤ x ∧
        t.1 + t.2 ≤ x ∧ IsFactorialThreeInterval t.1 t.2 := by
  classical
  simp [nontrivialFactorialThreeIntervalsUpTo, and_assoc]

/-- Every non-one-term endpoint has a length-at-least-two interval witness in
the finite family. -/
theorem nontrivialFactorialThreeNumbersUpTo_subset_endpointImage (x : ℕ) :
    nontrivialFactorialThreeNumbersUpTo x ⊆
      (nontrivialFactorialThreeIntervalsUpTo x).image fun t => t.1 + t.2 := by
  classical
  intro n hn
  have hn' := mem_nontrivialFactorialThreeNumbersUpTo.mp hn
  rcases hn'.2.2.1 with ⟨N, H, rfl, hf3⟩
  have hHTwo : 2 ≤ H := by
    by_contra hH
    have hHPos : 1 ≤ H := hf3.length_pos
    have hHOne : H = 1 := by omega
    subst H
    exact hn'.2.2.2 ⟨N, rfl, hf3⟩
  have hNle : N ≤ x := by
    have hHPos : 1 ≤ H := hf3.length_pos
    omega
  have hHle : H ≤ x := by omega
  rw [Finset.mem_image]
  exact ⟨(N, H),
    mem_nontrivialFactorialThreeIntervalsUpTo.mpr
      ⟨hNle, hHTwo, hHle, hn'.2.1, hf3⟩, rfl⟩

/-- First exact finite reduction: endpoint values are no more numerous than
their interval witnesses. -/
theorem nontrivialFactorialThreeCount_le_intervalCount (x : ℕ) :
    nontrivialFactorialThreeCount x ≤
      (nontrivialFactorialThreeIntervalsUpTo x).card := by
  rw [← card_nontrivialFactorialThreeNumbersUpTo]
  calc
    (nontrivialFactorialThreeNumbersUpTo x).card ≤
        ((nontrivialFactorialThreeIntervalsUpTo x).image
          fun t => t.1 + t.2).card :=
      Finset.card_le_card
        (nontrivialFactorialThreeNumbersUpTo_subset_endpointImage x)
    _ ≤ (nontrivialFactorialThreeIntervalsUpTo x).card :=
      Finset.card_image_le

/-! ## Structured Lemma 4.3 certificates -/

/-- The arithmetic data selected by Lemma 4.3 for one interval. -/
structure FactorialRelationCertificate where
  factorialIndex : ℕ
  coeffLeft : ℕ
  coeffRight : ℕ
  rootLeft : ℕ
  rootRight : ℕ
  shift : ℕ
deriving DecidableEq

/-- A certificate retains the full bounded smooth square-relation conclusion
and the two actual interval elements. -/
def FactorialRelationCertificate.Certifies
    (c : FactorialRelationCertificate) (N H : ℕ) : Prop :=
  1 ≤ c.factorialIndex ∧ c.factorialIndex < N ∧
    squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent c.factorialIndex.factorial ∧
    0 < c.coeffLeft ∧ 0 < c.coeffRight ∧
    0 < c.rootLeft ∧ 0 < c.rootRight ∧
    Squarefree c.coeffLeft ∧ Squarefree c.coeffRight ∧
    (∀ p : ℕ, p.Prime → p ∣ c.coeffLeft →
      p ≤ max c.factorialIndex H) ∧
    (∀ p : ℕ, p.Prime → p ∣ c.coeffRight →
      p ≤ max c.factorialIndex H) ∧
    (c.coeffLeft : ℝ) ≤ Real.exp
      (factorialCoefficientSelectionLogBound H
        (max c.factorialIndex H)) ∧
    (c.coeffRight : ℝ) ≤ Real.exp
      (factorialCoefficientSelectionLogBound H
        (max c.factorialIndex H)) ∧
    0 < c.shift ∧ c.shift < H ∧
    c.coeffLeft * c.rootLeft ^ 2 + c.shift =
      c.coeffRight * c.rootRight ^ 2 ∧
    c.coeffLeft * c.rootLeft ^ 2 ∈ consecutiveInterval N H ∧
    c.coeffRight * c.rootRight ^ 2 ∈ consecutiveInterval N H

/-- Lemma 4.3 repackaged as one structured certificate. -/
theorem exists_factorialRelationCertificate
    {N H : ℕ} (hf3 : IsFactorialThreeInterval N H) (hH : 2 ≤ H) :
    ∃ c : FactorialRelationCertificate, c.Certifies N H := by
  obtain ⟨a, c₁, c₂, n₁, n₂, h, ha, haN, hcomponent,
      hc₁, hc₂, hn₁, hn₂, hc₁sf, hc₂sf, hc₁smooth, hc₂smooth,
      hc₁Bound, hc₂Bound, hh, hhH, heq, hleft, hright⟩ :=
    factorialThreeInterval_exists_bounded_smooth_squareRelation hf3 hH
  exact ⟨⟨a, c₁, c₂, n₁, n₂, h⟩,
    ha, haN, hcomponent, hc₁, hc₂, hn₁, hn₂, hc₁sf, hc₂sf,
    hc₁smooth, hc₂smooth, hc₁Bound, hc₂Bound, hh, hhH,
    heq, hleft, hright⟩

/-- A deterministic Lemma 4.3 certificate for every interval witness. -/
noncomputable def chosenFactorialRelationCertificate (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    FactorialRelationCertificate := by
  have ht := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  exact Classical.choose
    (exists_factorialRelationCertificate ht.2.2.2.2 ht.2.1)

theorem chosenFactorialRelationCertificate_spec (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    (chosenFactorialRelationCertificate x t).Certifies t.1.1 t.1.2 := by
  have ht := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  exact Classical.choose_spec
    (exists_factorialRelationCertificate ht.2.2.2.2 ht.2.1)

/-- The two selected roots lie in the exact Lemma 2.10 relation set at cutoff
`x`. -/
theorem chosenFactorialRelationPair_mem (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    let c := chosenFactorialRelationCertificate x t
    (c.rootLeft, c.rootRight) ∈
      squareRelationSolutionsUpTo c.coeffLeft c.coeffRight
        (c.shift : ℤ) x := by
  dsimp only
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have ht := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  rcases hspec with ⟨_ha, _haN, _hcomponent, hc₁, hc₂, hn₁, hn₂,
    _hc₁sf, _hc₂sf, _hc₁smooth, _hc₂smooth, _hc₁Bound, _hc₂Bound,
    _hh, _hhH, heq, hleft, hright⟩
  have hleftLe : c.coeffLeft * c.rootLeft ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hleft).2.trans ht.2.2.2.1
  have hrightLe : c.coeffRight * c.rootRight ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hright).2.trans ht.2.2.2.1
  have hn₁LeMul : c.rootLeft ≤ c.coeffLeft * c.rootLeft ^ 2 := by
    nlinarith
  have hn₂LeMul : c.rootRight ≤ c.coeffRight * c.rootRight ^ 2 := by
    nlinarith
  rw [mem_squareRelationSolutionsUpTo hc₂]
  refine ⟨hn₁, hn₁LeMul.trans hleftLe, hn₂, ?_⟩
  exact_mod_cast heq

/-! ## Injective interval codes -/

/-- A Lemma 4.3 certificate, interval length, and selected-element offset
recover the interval start. -/
structure FactorialIntervalCode where
  certificate : FactorialRelationCertificate
  intervalLength : ℕ
  leftOffset : ℕ
deriving DecidableEq

noncomputable def chosenFactorialIntervalCode (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    FactorialIntervalCode :=
  let c := chosenFactorialRelationCertificate x t
  ⟨c, t.1.2, c.coeffLeft * c.rootLeft ^ 2 - t.1.1 - 1⟩

theorem chosenFactorialIntervalCode_length_le (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    (chosenFactorialIntervalCode x t).intervalLength ≤ x := by
  change t.1.2 ≤ x
  exact (mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property).2.2.1

theorem chosenFactorialIntervalCode_offset_lt_length (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    (chosenFactorialIntervalCode x t).leftOffset <
      (chosenFactorialIntervalCode x t).intervalLength := by
  let c := chosenFactorialRelationCertificate x t
  have hleft :=
    (chosenFactorialRelationCertificate_spec x t).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  change c.coeffLeft * c.rootLeft ^ 2 ∈
    consecutiveInterval t.1.1 t.1.2 at hleft
  have hmem := Finset.mem_Ioc.mp hleft
  change c.coeffLeft * c.rootLeft ^ 2 - t.1.1 - 1 < t.1.2
  omega

/-- No two interval witnesses have the same chosen relation certificate,
length, and selected-element offset. -/
theorem injective_chosenFactorialIntervalCode (x : ℕ) :
    Function.Injective (chosenFactorialIntervalCode x) := by
  intro t u hcode
  have hcert := congrArg FactorialIntervalCode.certificate hcode
  have hlength := congrArg FactorialIntervalCode.intervalLength hcode
  have hoffset := congrArg FactorialIntervalCode.leftOffset hcode
  change chosenFactorialRelationCertificate x t =
    chosenFactorialRelationCertificate x u at hcert
  change t.1.2 = u.1.2 at hlength
  change
    (chosenFactorialRelationCertificate x t).coeffLeft *
          (chosenFactorialRelationCertificate x t).rootLeft ^ 2 - t.1.1 - 1 =
      (chosenFactorialRelationCertificate x u).coeffLeft *
          (chosenFactorialRelationCertificate x u).rootLeft ^ 2 - u.1.1 - 1
    at hoffset
  have hproduct :
      (chosenFactorialRelationCertificate x t).coeffLeft *
          (chosenFactorialRelationCertificate x t).rootLeft ^ 2 =
        (chosenFactorialRelationCertificate x u).coeffLeft *
          (chosenFactorialRelationCertificate x u).rootLeft ^ 2 :=
    congrArg (fun c => c.coeffLeft * c.rootLeft ^ 2) hcert
  have htStart : t.1.1 <
      (chosenFactorialRelationCertificate x t).coeffLeft *
        (chosenFactorialRelationCertificate x t).rootLeft ^ 2 :=
    (Finset.mem_Ioc.mp
      (chosenFactorialRelationCertificate_spec x t).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
  have huStart : u.1.1 <
      (chosenFactorialRelationCertificate x u).coeffLeft *
        (chosenFactorialRelationCertificate x u).rootLeft ^ 2 :=
    (Finset.mem_Ioc.mp
      (chosenFactorialRelationCertificate_spec x u).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
  apply Subtype.ext
  apply Prod.ext
  · omega
  · exact hlength

/-! ## Explicit finite ambient ranges -/

/-- A coarse finite ambient family for all Lemma 4.3 certificates below
`x`.  Later case-specific families replace the four `[1,x]` parameter ranges
by the source's subpolynomial or smooth ranges. -/
noncomputable def factorialRelationCertificatesUpTo (x : ℕ) :
    Finset FactorialRelationCertificate := by
  classical
  exact (Finset.Icc 1 x).biUnion fun a =>
    ((Finset.Icc 1 x).product (Finset.Icc 1 x)).biUnion fun cs =>
      (Finset.Icc 1 x).biUnion fun h =>
        (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
          ⟨a, cs.1, cs.2, nm.1, nm.2, h⟩

/-- Every chosen Lemma 4.3 certificate belongs to the coarse finite ambient
family. -/
theorem chosenFactorialRelationCertificate_mem (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    chosenFactorialRelationCertificate x t ∈
      factorialRelationCertificatesUpTo x := by
  classical
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have ht := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  rcases hspec with ⟨ha, haN, _hcomponent, hc₁, hc₂, hn₁, hn₂,
    _hc₁sf, _hc₂sf, _hc₁smooth, _hc₂smooth, _hc₁Bound, _hc₂Bound,
    hh, hhH, _heq, hleft, hright⟩
  have haLe : c.factorialIndex ≤ x := by omega
  have hleftLe : c.coeffLeft * c.rootLeft ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hleft).2.trans ht.2.2.2.1
  have hrightLe : c.coeffRight * c.rootRight ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hright).2.trans ht.2.2.2.1
  have hc₁Le : c.coeffLeft ≤ x := by
    have hrootSq : 1 ≤ c.rootLeft ^ 2 := by nlinarith
    exact (Nat.le_mul_of_pos_right c.coeffLeft hrootSq).trans hleftLe
  have hc₂Le : c.coeffRight ≤ x := by
    have hrootSq : 1 ≤ c.rootRight ^ 2 := by nlinarith
    exact (Nat.le_mul_of_pos_right c.coeffRight hrootSq).trans hrightLe
  have hhLe : c.shift ≤ x := by omega
  rw [factorialRelationCertificatesUpTo, Finset.mem_biUnion]
  refine ⟨c.factorialIndex, Finset.mem_Icc.mpr ⟨ha, haLe⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨(c.coeffLeft, c.coeffRight),
    Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hc₁, hc₁Le⟩,
        Finset.mem_Icc.mpr ⟨hc₂, hc₂Le⟩⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨c.shift, Finset.mem_Icc.mpr ⟨hh, hhLe⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(c.rootLeft, c.rootRight),
    chosenFactorialRelationPair_mem x t, rfl⟩

/-- Finite ambient range for the injective interval code. -/
noncomputable def factorialIntervalCodesUpTo (x : ℕ) :
    Finset FactorialIntervalCode := by
  classical
  exact (factorialRelationCertificatesUpTo x).product
      ((Finset.Icc 2 x).product (Finset.range x)) |>.image fun q =>
    ⟨q.1, q.2.1, q.2.2⟩

theorem chosenFactorialIntervalCode_mem (x : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    chosenFactorialIntervalCode x t ∈ factorialIntervalCodesUpTo x := by
  classical
  rw [factorialIntervalCodesUpTo, Finset.mem_image]
  refine ⟨(chosenFactorialRelationCertificate x t,
      ((chosenFactorialIntervalCode x t).intervalLength,
        (chosenFactorialIntervalCode x t).leftOffset)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨chosenFactorialRelationCertificate_mem x t, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨(mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property).2.1,
        chosenFactorialIntervalCode_length_le x t⟩,
      Finset.mem_range.mpr ?_⟩
    exact (chosenFactorialIntervalCode_offset_lt_length x t).trans_le
      (chosenFactorialIntervalCode_length_le x t)
  · rfl

/-- The injective code embeds every relevant interval into its explicit
finite ambient range. -/
theorem card_nontrivialFactorialThreeIntervalsUpTo_le_codes (x : ℕ) :
    (nontrivialFactorialThreeIntervalsUpTo x).card ≤
      (factorialIntervalCodesUpTo x).card := by
  classical
  let s := nontrivialFactorialThreeIntervalsUpTo x
  have himage : s.attach.image (chosenFactorialIntervalCode x) ⊆
      factorialIntervalCodesUpTo x := by
    intro c hc
    rw [Finset.mem_image] at hc
    rcases hc with ⟨t, _ht, rfl⟩
    exact chosenFactorialIntervalCode_mem x t
  calc
    (nontrivialFactorialThreeIntervalsUpTo x).card = s.attach.card := by
      simp [s]
    _ = (s.attach.image (chosenFactorialIntervalCode x)).card := by
      rw [Finset.card_image_iff.mpr
        (injective_chosenFactorialIntervalCode x).injOn]
    _ ≤ (factorialIntervalCodesUpTo x).card := Finset.card_le_card himage

/-- The two interval parameters outside the relation certificate cost at
most `x²` in the coarse finite encoding. -/
theorem card_factorialIntervalCodesUpTo_le (x : ℕ) :
    (factorialIntervalCodesUpTo x).card ≤
      (factorialRelationCertificatesUpTo x).card * (x * x) := by
  classical
  have hIcc : (Finset.Icc 2 x).card ≤ x := by simp
  calc
    (factorialIntervalCodesUpTo x).card ≤
        ((factorialRelationCertificatesUpTo x).product
          ((Finset.Icc 2 x).product (Finset.range x))).card :=
      Finset.card_image_le
    _ = (factorialRelationCertificatesUpTo x).card *
        ((Finset.Icc 2 x).card * x) := by simp
    _ ≤ (factorialRelationCertificatesUpTo x).card * (x * x) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right x hIcc)

/-- Exact coarse finite reduction of the nontrivial endpoint count to
Lemma 4.3 relation certificates. -/
theorem nontrivialFactorialThreeCount_le_square_mul_relationCertificates
    (x : ℕ) :
    nontrivialFactorialThreeCount x ≤
      x ^ 2 * (factorialRelationCertificatesUpTo x).card := by
  calc
    nontrivialFactorialThreeCount x ≤
        (nontrivialFactorialThreeIntervalsUpTo x).card :=
      nontrivialFactorialThreeCount_le_intervalCount x
    _ ≤ (factorialIntervalCodesUpTo x).card :=
      card_nontrivialFactorialThreeIntervalsUpTo_le_codes x
    _ ≤ (factorialRelationCertificatesUpTo x).card * (x * x) :=
      card_factorialIntervalCodesUpTo_le x
    _ = x ^ 2 * (factorialRelationCertificatesUpTo x).card := by ring

/-! ## Case-specific budgeted certificate families -/

/-- Certificates with independent factorial-index, coefficient, and
length/shift budgets.  This is the finite family used in both easy cases of
the source proof. -/
noncomputable def factorialRelationCertificatesUpToBudgets
    (x A C G : ℕ) : Finset FactorialRelationCertificate := by
  classical
  exact (Finset.Icc 1 A).biUnion fun a =>
    ((Finset.Icc 1 C).product (Finset.Icc 1 C)).biUnion fun cs =>
      (Finset.Icc 1 G).biUnion fun h =>
        (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
          ⟨a, cs.1, cs.2, nm.1, nm.2, h⟩

/-- A rounded uniform Lemma 2.10 bound at polynomial exponent one. -/
noncomputable def factorialSquareRelationCountBudget
    (ε : ℝ) (x : ℕ) : ℕ :=
  ⌈squareRelationPolynomialEpsilonConstant (ε / 16) * (x : ℝ) ^ ε⌉₊

theorem card_squareRelationSolutionsUpTo_le_factorialBudget
    {a b h x : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hx : 1 ≤ x) (haX : a ≤ x) (hbX : b ≤ x) (hhX : h ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    (squareRelationSolutionsUpTo a b (h : ℤ) x).card ≤
      factorialSquareRelationCountBudget ε x := by
  have hpoint := card_squareRelationSolutionsUpTo_le_const_mul_rpow
    (K := 1) (h := (h : ℤ)) ha hb (by exact_mod_cast hh.ne')
    (by omega : 0 < x)
    (by simpa using haX) (by simpa using hbX)
    (by simpa using hhX) hε
  have hpoint' :
      ((squareRelationSolutionsUpTo a b (h : ℤ) x).card : ℝ) ≤
        squareRelationPolynomialEpsilonConstant (ε / 16) *
          (x : ℝ) ^ ε := by
    norm_num at hpoint ⊢
    exact hpoint
  have hceil :
      squareRelationPolynomialEpsilonConstant (ε / 16) *
          (x : ℝ) ^ ε ≤
        (factorialSquareRelationCountBudget ε x : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hpoint'.trans hceil

/-- For fixed positive `δ`, the rounded uniform Lemma 2.10 envelope has
power upper exponent `δ`. -/
theorem factorialSquareRelationCountBudget_powerUpperBound
    {δ : ℝ} (hδ : 0 < δ) :
    PowerUpperBound
      (fun x => (factorialSquareRelationCountBudget δ x : ℝ)) δ := by
  intro ε hε
  let q : ℝ := δ + ε
  let C : ℝ := squareRelationPolynomialEpsilonConstant (δ / 16)
  let K : ℝ := C + 1
  have hδ16 : 0 < δ / 16 := by positivity
  have hC : 0 ≤ C := by
    exact (squareRelationPolynomialEpsilonConstant_pos hδ16).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hxreal : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxnonneg : (0 : ℝ) ≤ x := hxreal.trans' zero_le_one
  have hδq : δ ≤ q := by dsimp only [q]; linarith
  have hxpow : (x : ℝ) ^ δ ≤ (x : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le hxreal hδq
  have honepow : (1 : ℝ) ≤ (x : ℝ) ^ q :=
    Real.one_le_rpow hxreal (by dsimp only [q]; linarith)
  have hceil : (factorialSquareRelationCountBudget δ x : ℝ) <
      C * (x : ℝ) ^ δ + 1 := by
    simpa only [factorialSquareRelationCountBudget, C] using
      Nat.ceil_lt_add_one
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hxnonneg _)]
  calc
    (factorialSquareRelationCountBudget δ x : ℝ) ≤
        C * (x : ℝ) ^ δ + 1 := hceil.le
    _ ≤ C * (x : ℝ) ^ q + (x : ℝ) ^ q := by gcongr
    _ = K * (x : ℝ) ^ q := by
      dsimp only [K]
      ring
    _ = K * (x : ℝ) ^ (δ + ε) := rfl

/-- The budgeted certificate family costs only its four finite parameter
ranges times one uniform Lemma 2.10 relation count. -/
theorem card_factorialRelationCertificatesUpToBudgets_le
    (x A C G : ℕ) (hx : 1 ≤ x)
    (hC : C ≤ x) (hG : G ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    (factorialRelationCertificatesUpToBudgets x A C G).card ≤
      A * C ^ 2 * G * factorialSquareRelationCountBudget ε x := by
  classical
  let R := factorialSquareRelationCountBudget ε x
  let CS := (Finset.Icc 1 C).product (Finset.Icc 1 C)
  have hCS : CS.card ≤ C ^ 2 := by
    dsimp only [CS]
    simp [pow_two]
  have hshift : ∀ a, ∀ cs ∈ CS,
      ((Finset.Icc 1 G).biUnion fun h =>
        (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
          (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
            FactorialRelationCertificate)).card ≤ G * R := by
    intro a cs hcs
    have hcs' := Finset.mem_product.mp hcs
    calc
      ((Finset.Icc 1 G).biUnion fun h =>
          (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
            (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
              FactorialRelationCertificate)).card ≤
          ∑ h ∈ Finset.Icc 1 G,
            ((squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
              (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
                FactorialRelationCertificate)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _h ∈ Finset.Icc 1 G, R := by
        apply Finset.sum_le_sum
        intro h hhmem
        exact Finset.card_image_le.trans
          (card_squareRelationSolutionsUpTo_le_factorialBudget
            (Finset.mem_Icc.mp hcs'.1).1
            (Finset.mem_Icc.mp hcs'.2).1
            (Finset.mem_Icc.mp hhmem).1 hx
            ((Finset.mem_Icc.mp hcs'.1).2.trans hC)
            ((Finset.mem_Icc.mp hcs'.2).2.trans hC)
            ((Finset.mem_Icc.mp hhmem).2.trans hG) hε)
      _ = (Finset.Icc 1 G).card * R := by simp
      _ ≤ G * R := Nat.mul_le_mul_right R (by simp)
  have hcoeff : ∀ a ∈ Finset.Icc 1 A,
      (CS.biUnion fun cs =>
        (Finset.Icc 1 G).biUnion fun h =>
          (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
            (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
              FactorialRelationCertificate)).card ≤ C ^ 2 * (G * R) := by
    intro a haMem
    calc
      (CS.biUnion fun cs =>
          (Finset.Icc 1 G).biUnion fun h =>
            (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
              (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
                FactorialRelationCertificate)).card ≤
          ∑ cs ∈ CS,
            ((Finset.Icc 1 G).biUnion fun h =>
              (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
                (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
                  FactorialRelationCertificate)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _cs ∈ CS, G * R := by
        apply Finset.sum_le_sum
        intro cs hcs
        exact hshift a cs hcs
      _ = CS.card * (G * R) := by simp
      _ ≤ C ^ 2 * (G * R) := Nat.mul_le_mul_right _ hCS
  rw [factorialRelationCertificatesUpToBudgets]
  change ((Finset.Icc 1 A).biUnion _).card ≤ _
  calc
    ((Finset.Icc 1 A).biUnion fun a =>
        CS.biUnion fun cs =>
          (Finset.Icc 1 G).biUnion fun h =>
            (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
              (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
                FactorialRelationCertificate)).card ≤
        ∑ a ∈ Finset.Icc 1 A,
          (CS.biUnion fun cs =>
            (Finset.Icc 1 G).biUnion fun h =>
              (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
                (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
                  FactorialRelationCertificate)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Finset.Icc 1 A, C ^ 2 * (G * R) :=
      Finset.sum_le_sum hcoeff
    _ = (Finset.Icc 1 A).card * (C ^ 2 * (G * R)) := by simp
    _ ≤ A * (C ^ 2 * (G * R)) :=
      Nat.mul_le_mul_right _ (by simp)
    _ = A * C ^ 2 * G * factorialSquareRelationCountBudget ε x := by
      dsimp only [R]
      ring

/-- A chosen certificate enters the case-specific family as soon as its
factorial index, two coefficients, and interval length satisfy the supplied
budgets. -/
theorem chosenFactorialRelationCertificate_mem_budgets
    (x A C G : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x))
    (hA : (chosenFactorialRelationCertificate x t).factorialIndex ≤ A)
    (hC : (chosenFactorialRelationCertificate x t).coeffLeft ≤ C ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤ C)
    (hG : t.1.2 ≤ G) :
    chosenFactorialRelationCertificate x t ∈
      factorialRelationCertificatesUpToBudgets x A C G := by
  classical
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  change c.factorialIndex ≤ A at hA
  change c.coeffLeft ≤ C ∧ c.coeffRight ≤ C at hC
  rcases hspec with ⟨ha, _haN, _hcomponent, hc₁, hc₂, _hn₁, _hn₂,
    _hc₁sf, _hc₂sf, _hc₁smooth, _hc₂smooth, _hc₁Bound, _hc₂Bound,
    hh, hhH, _heq, _hleft, _hright⟩
  have hhG : c.shift ≤ G := hhH.le.trans hG
  rw [factorialRelationCertificatesUpToBudgets, Finset.mem_biUnion]
  refine ⟨c.factorialIndex, Finset.mem_Icc.mpr ⟨ha, hA⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨(c.coeffLeft, c.coeffRight),
    Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hc₁, hC.1⟩,
        Finset.mem_Icc.mpr ⟨hc₂, hC.2⟩⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨c.shift, Finset.mem_Icc.mpr ⟨hh, hhG⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(c.rootLeft, c.rootRight),
    chosenFactorialRelationPair_mem x t, rfl⟩

/-- Case-specific finite range for the injective interval code. -/
noncomputable def factorialIntervalCodesUpToBudgets
    (x A C G : ℕ) : Finset FactorialIntervalCode := by
  classical
  exact (factorialRelationCertificatesUpToBudgets x A C G).product
      ((Finset.Icc 2 G).product (Finset.range G)) |>.image fun q =>
    ⟨q.1, q.2.1, q.2.2⟩

theorem chosenFactorialIntervalCode_mem_budgets
    (x A C G : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x))
    (hA : (chosenFactorialRelationCertificate x t).factorialIndex ≤ A)
    (hC : (chosenFactorialRelationCertificate x t).coeffLeft ≤ C ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤ C)
    (hG : t.1.2 ≤ G) :
    chosenFactorialIntervalCode x t ∈
      factorialIntervalCodesUpToBudgets x A C G := by
  classical
  rw [factorialIntervalCodesUpToBudgets, Finset.mem_image]
  refine ⟨(chosenFactorialRelationCertificate x t,
      ((chosenFactorialIntervalCode x t).intervalLength,
        (chosenFactorialIntervalCode x t).leftOffset)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨chosenFactorialRelationCertificate_mem_budgets
      x A C G t hA hC hG, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr
      ⟨(mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property).2.1,
        hG⟩, Finset.mem_range.mpr ?_⟩
    exact (chosenFactorialIntervalCode_offset_lt_length x t).trans_le hG
  · rfl

theorem card_factorialIntervalCodesUpToBudgets_le
    (x A C G : ℕ) :
    (factorialIntervalCodesUpToBudgets x A C G).card ≤
      (factorialRelationCertificatesUpToBudgets x A C G).card * (G * G) := by
  classical
  have hIcc : (Finset.Icc 2 G).card ≤ G := by simp
  calc
    (factorialIntervalCodesUpToBudgets x A C G).card ≤
        ((factorialRelationCertificatesUpToBudgets x A C G).product
          ((Finset.Icc 2 G).product (Finset.range G))).card :=
      Finset.card_image_le
    _ = (factorialRelationCertificatesUpToBudgets x A C G).card *
        ((Finset.Icc 2 G).card * G) := by simp
    _ ≤ (factorialRelationCertificatesUpToBudgets x A C G).card *
        (G * G) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right G hIcc)

/-- Generic exact finite endpoint estimate for either source easy case.  All
analytic work is isolated in the three uniform budget hypotheses. -/
theorem nontrivialFactorialThreeCount_le_of_certificate_budgets
    (x A C G : ℕ) (hx : 1 ≤ x) (hC : C ≤ x) (hGx : G ≤ x)
    (hbudgets : ∀ t : ↥(nontrivialFactorialThreeIntervalsUpTo x),
      (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
      (chosenFactorialRelationCertificate x t).coeffLeft ≤ C ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤ C ∧
      t.1.2 ≤ G)
    {ε : ℝ} (hε : 0 < ε) :
    nontrivialFactorialThreeCount x ≤
      A * C ^ 2 * G ^ 3 * factorialSquareRelationCountBudget ε x := by
  classical
  let s := nontrivialFactorialThreeIntervalsUpTo x
  have himage : s.attach.image (chosenFactorialIntervalCode x) ⊆
      factorialIntervalCodesUpToBudgets x A C G := by
    intro code hcode
    rw [Finset.mem_image] at hcode
    rcases hcode with ⟨t, _ht, rfl⟩
    have hb := hbudgets t
    exact chosenFactorialIntervalCode_mem_budgets x A C G t
      hb.1 ⟨hb.2.1, hb.2.2.1⟩ hb.2.2.2
  have hinterval :
      (nontrivialFactorialThreeIntervalsUpTo x).card ≤
        (factorialIntervalCodesUpToBudgets x A C G).card := by
    calc
      (nontrivialFactorialThreeIntervalsUpTo x).card = s.attach.card := by
        simp [s]
      _ = (s.attach.image (chosenFactorialIntervalCode x)).card := by
        rw [Finset.card_image_iff.mpr
          (injective_chosenFactorialIntervalCode x).injOn]
      _ ≤ (factorialIntervalCodesUpToBudgets x A C G).card :=
        Finset.card_le_card himage
  calc
    nontrivialFactorialThreeCount x ≤
        (nontrivialFactorialThreeIntervalsUpTo x).card :=
      nontrivialFactorialThreeCount_le_intervalCount x
    _ ≤ (factorialIntervalCodesUpToBudgets x A C G).card := hinterval
    _ ≤ (factorialRelationCertificatesUpToBudgets x A C G).card *
        (G * G) := card_factorialIntervalCodesUpToBudgets_le x A C G
    _ ≤ (A * C ^ 2 * G * factorialSquareRelationCountBudget ε x) *
        (G * G) := Nat.mul_le_mul_right _
      (card_factorialRelationCertificatesUpToBudgets_le
        x A C G hx hC hGx hε)
    _ = A * C ^ 2 * G ^ 3 *
        factorialSquareRelationCountBudget ε x := by ring

/-! ## The actual budgeted source subfamily -/

/-- Interval witnesses whose chosen Lemma 4.3 data obey one specified set of
case budgets.  Keeping this as a finset of attached interval witnesses avoids
identifying distinct witnesses with a common endpoint too early. -/
noncomputable def factorialBudgetedIntervalsUpTo
    (x A C G : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) := by
  classical
  exact (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
    (chosenFactorialRelationCertificate x t).coeffLeft ≤ C ∧
    (chosenFactorialRelationCertificate x t).coeffRight ≤ C ∧
    t.1.2 ≤ G

theorem mem_factorialBudgetedIntervalsUpTo
    {x A C G : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialBudgetedIntervalsUpTo x A C G ↔
      (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
      (chosenFactorialRelationCertificate x t).coeffLeft ≤ C ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤ C ∧
      t.1.2 ≤ G := by
  classical
  simp [factorialBudgetedIntervalsUpTo]

/-- The endpoint values represented by the budgeted interval subfamily. -/
noncomputable def factorialBudgetedEndpointsUpTo
    (x A C G : ℕ) : Finset ℕ :=
  (factorialBudgetedIntervalsUpTo x A C G).image fun t => t.1.1 + t.1.2

theorem card_factorialBudgetedEndpointsUpTo_le_intervals
    (x A C G : ℕ) :
    (factorialBudgetedEndpointsUpTo x A C G).card ≤
      (factorialBudgetedIntervalsUpTo x A C G).card := by
  exact Finset.card_image_le

/-- The budgeted interval subfamily injects into the corresponding explicit
code range. -/
theorem card_factorialBudgetedIntervalsUpTo_le_codes
    (x A C G : ℕ) :
    (factorialBudgetedIntervalsUpTo x A C G).card ≤
      (factorialIntervalCodesUpToBudgets x A C G).card := by
  classical
  let s := factorialBudgetedIntervalsUpTo x A C G
  let encode : ↥s → FactorialIntervalCode := fun t =>
    chosenFactorialIntervalCode x t.1
  have hencode : Function.Injective encode := by
    intro t u htu
    apply Subtype.ext
    exact injective_chosenFactorialIntervalCode x htu
  have himage : s.attach.image encode ⊆
      factorialIntervalCodesUpToBudgets x A C G := by
    intro code hcode
    rw [Finset.mem_image] at hcode
    rcases hcode with ⟨t, _ht, rfl⟩
    have htBudget : t.1 ∈ factorialBudgetedIntervalsUpTo x A C G := by
      simpa only [s] using t.property
    have hb := mem_factorialBudgetedIntervalsUpTo.mp htBudget
    exact chosenFactorialIntervalCode_mem_budgets x A C G t.1
      hb.1 ⟨hb.2.1, hb.2.2.1⟩ hb.2.2.2
  calc
    (factorialBudgetedIntervalsUpTo x A C G).card = s.attach.card := by
      simp [s]
    _ = (s.attach.image encode).card := by
      rw [Finset.card_image_iff.mpr hencode.injOn]
    _ ≤ (factorialIntervalCodesUpToBudgets x A C G).card :=
      Finset.card_le_card himage

/-- Exact finite count for either budget-defined source subfamily. -/
theorem card_factorialBudgetedEndpointsUpTo_le
    (x A C G : ℕ) (hx : 1 ≤ x) (hC : C ≤ x) (hG : G ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    (factorialBudgetedEndpointsUpTo x A C G).card ≤
      A * C ^ 2 * G ^ 3 * factorialSquareRelationCountBudget ε x := by
  calc
    (factorialBudgetedEndpointsUpTo x A C G).card ≤
        (factorialBudgetedIntervalsUpTo x A C G).card :=
      card_factorialBudgetedEndpointsUpTo_le_intervals x A C G
    _ ≤ (factorialIntervalCodesUpToBudgets x A C G).card :=
      card_factorialBudgetedIntervalsUpTo_le_codes x A C G
    _ ≤ (factorialRelationCertificatesUpToBudgets x A C G).card *
        (G * G) := card_factorialIntervalCodesUpToBudgets_le x A C G
    _ ≤ (A * C ^ 2 * G * factorialSquareRelationCountBudget ε x) *
        (G * G) := Nat.mul_le_mul_right _
      (card_factorialRelationCertificatesUpToBudgets_le
        x A C G hx hC hG hε)
    _ = A * C ^ 2 * G ^ 3 *
        factorialSquareRelationCountBudget ε x := by ring

/-! ## Exact easy/hard source partition -/

/-- The finite version of Tao's first case: the chosen factorial index is at
most `L*H`, or the interval length is at most the fixed cutoff `B`. -/
def FactorialEasyCaseAt (x L B : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) : Prop :=
  (chosenFactorialRelationCertificate x t).factorialIndex ≤ L * t.1.2 ∨
    t.1.2 ≤ B

noncomputable def factorialEasyIntervalsUpTo
    (x L B : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) := by
  classical
  exact (nontrivialFactorialThreeIntervalsUpTo x).attach.filter
    (FactorialEasyCaseAt x L B)

noncomputable def factorialHardIntervalsUpTo
    (x L B : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) := by
  classical
  exact (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    ¬FactorialEasyCaseAt x L B t

theorem mem_factorialEasyIntervalsUpTo
    {x L B : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialEasyIntervalsUpTo x L B ↔
      FactorialEasyCaseAt x L B t := by
  classical
  simp [factorialEasyIntervalsUpTo]

theorem mem_factorialHardIntervalsUpTo
    {x L B : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialHardIntervalsUpTo x L B ↔
      ¬FactorialEasyCaseAt x L B t := by
  classical
  simp [factorialHardIntervalsUpTo]

/-- The two case families partition all relevant interval witnesses exactly. -/
theorem factorialEasyIntervalsUpTo_union_factorialHardIntervalsUpTo
    (x L B : ℕ) :
    factorialEasyIntervalsUpTo x L B ∪
      factorialHardIntervalsUpTo x L B =
        (nontrivialFactorialThreeIntervalsUpTo x).attach := by
  classical
  ext t
  simp [mem_factorialEasyIntervalsUpTo, mem_factorialHardIntervalsUpTo]
  exact Classical.em _

noncomputable def factorialEasyEndpointsUpTo
    (x L B : ℕ) : Finset ℕ :=
  (factorialEasyIntervalsUpTo x L B).image fun t => t.1.1 + t.1.2

noncomputable def factorialHardEndpointsUpTo
    (x L B : ℕ) : Finset ℕ :=
  (factorialHardIntervalsUpTo x L B).image fun t => t.1.1 + t.1.2

/-- Endpoint images respect the exact interval case partition. -/
theorem factorialEasyEndpointsUpTo_union_factorialHardEndpointsUpTo
    (x L B : ℕ) :
    factorialEasyEndpointsUpTo x L B ∪
      factorialHardEndpointsUpTo x L B =
        (nontrivialFactorialThreeIntervalsUpTo x).image fun t => t.1 + t.2 := by
  classical
  rw [factorialEasyEndpointsUpTo, factorialHardEndpointsUpTo,
    ← Finset.image_union,
    factorialEasyIntervalsUpTo_union_factorialHardIntervalsUpTo]
  ext n
  simp

/-- Every nontrivial endpoint lies in the union of the two source cases. -/
theorem nontrivialFactorialThreeNumbersUpTo_subset_easy_union_hard
    (x L B : ℕ) :
    nontrivialFactorialThreeNumbersUpTo x ⊆
      factorialEasyEndpointsUpTo x L B ∪
        factorialHardEndpointsUpTo x L B := by
  rw [factorialEasyEndpointsUpTo_union_factorialHardEndpointsUpTo]
  exact nontrivialFactorialThreeNumbersUpTo_subset_endpointImage x

/-- Exact additive counting reduction for the source easy/hard split. -/
theorem nontrivialFactorialThreeCount_le_easy_add_hard
    (x L B : ℕ) :
    nontrivialFactorialThreeCount x ≤
      (factorialEasyEndpointsUpTo x L B).card +
        (factorialHardEndpointsUpTo x L B).card := by
  rw [← card_nontrivialFactorialThreeNumbersUpTo]
  calc
    (nontrivialFactorialThreeNumbersUpTo x).card ≤
        (factorialEasyEndpointsUpTo x L B ∪
          factorialHardEndpointsUpTo x L B).card :=
      Finset.card_le_card
        (nontrivialFactorialThreeNumbersUpTo_subset_easy_union_hard x L B)
    _ ≤ (factorialEasyEndpointsUpTo x L B).card +
        (factorialHardEndpointsUpTo x L B).card :=
      Finset.card_union_le _ _

end

end Tao2026
