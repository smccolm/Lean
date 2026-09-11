import Tao2026.FactorialCounting
import Tao2026.SmoothNumberBounds

/-!
# Smooth-coefficient counting for Tao's Theorem 1.9

This file is the exact finite consumer of Proposition 2.1(ii) in the easy
branch of Tao's proof.  Lemma 4.3 makes both squarefree coefficients
`max a H`-smooth.  We therefore replace the two crude coefficient intervals
in `FactorialCounting` by two copies of the literal smooth-number finset.

No smooth-number asymptotic is assumed or restated here: the resulting bound
is expressed exactly in terms of `psiNat`.  Thus the remaining analytic input
is visible at the boundary rather than hidden in the finite encoding.
-/

open Filter Asymptotics

namespace Tao2026

noncomputable section

/-! ## The exact smooth coefficient range -/

/-- Ordered pairs of positive `P`-smooth coefficients at most `x`. -/
def factorialSmoothCoefficientPairsUpTo (x P : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.smoothNumbersUpTo x (P + 1)).product
    (Nat.smoothNumbersUpTo x (P + 1))

@[simp]
theorem card_factorialSmoothCoefficientPairsUpTo (x P : ℕ) :
    (factorialSmoothCoefficientPairsUpTo x P).card = psiNat x P ^ 2 := by
  simp [factorialSmoothCoefficientPairsUpTo, psiNat, pow_two]

theorem mem_factorialSmoothCoefficientPairsUpTo {x P : ℕ} {cs : ℕ × ℕ} :
    cs ∈ factorialSmoothCoefficientPairsUpTo x P ↔
      cs.1 ≤ x ∧ IsSmooth cs.1 P ∧
        cs.2 ≤ x ∧ IsSmooth cs.2 P := by
  simp [factorialSmoothCoefficientPairsUpTo,
    mem_smoothNumbersUpTo_source, and_assoc]

/-! ## Smooth relation certificates -/

/-- Certificates whose two coefficients range over the exact set counted by
`psiNat x P`, with independent factorial-index and length/shift budgets. -/
def factorialSmoothRelationCertificatesUpTo
    (x A P G : ℕ) : Finset FactorialRelationCertificate :=
  (Finset.Icc 1 A).biUnion fun a =>
    (factorialSmoothCoefficientPairsUpTo x P).biUnion fun cs =>
      (Finset.Icc 1 G).biUnion fun h =>
        (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
          ⟨a, cs.1, cs.2, nm.1, nm.2, h⟩

/-- The smooth certificate family costs two exact smooth-number factors,
besides the factorial-index and shift ranges and Lemma 2.10's relation
budget. -/
theorem card_factorialSmoothRelationCertificatesUpTo_le
    (x A P G : ℕ) (hx : 1 ≤ x) (hG : G ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    (factorialSmoothRelationCertificatesUpTo x A P G).card ≤
      A * psiNat x P ^ 2 * G * factorialSquareRelationCountBudget ε x := by
  classical
  let R := factorialSquareRelationCountBudget ε x
  let CS := factorialSmoothCoefficientPairsUpTo x P
  have hCS : CS.card = psiNat x P ^ 2 := by
    simp [CS]
  have hshift : ∀ a, ∀ cs ∈ CS,
      ((Finset.Icc 1 G).biUnion fun h =>
        (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
          (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
            FactorialRelationCertificate)).card ≤ G * R := by
    intro a cs hcs
    have hcs' := mem_factorialSmoothCoefficientPairsUpTo.mp hcs
    have hc₁ : 0 < cs.1 :=
      Nat.pos_of_ne_zero (isSmooth_iff.mp hcs'.2.1).1
    have hc₂ : 0 < cs.2 :=
      Nat.pos_of_ne_zero (isSmooth_iff.mp hcs'.2.2.2).1
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
            hc₁ hc₂ (Finset.mem_Icc.mp hhmem).1 hx
            hcs'.1 hcs'.2.2.1
            ((Finset.mem_Icc.mp hhmem).2.trans hG) hε)
      _ = (Finset.Icc 1 G).card * R := by simp
      _ ≤ G * R := Nat.mul_le_mul_right R (by simp)
  have hcoeff : ∀ a ∈ Finset.Icc 1 A,
      (CS.biUnion fun cs =>
        (Finset.Icc 1 G).biUnion fun h =>
          (squareRelationSolutionsUpTo cs.1 cs.2 (h : ℤ) x).image fun nm =>
            (⟨a, cs.1, cs.2, nm.1, nm.2, h⟩ :
              FactorialRelationCertificate)).card ≤
        psiNat x P ^ 2 * (G * R) := by
    intro a ha
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
      _ = psiNat x P ^ 2 * (G * R) := by rw [hCS]
  rw [factorialSmoothRelationCertificatesUpTo]
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
    _ ≤ ∑ _a ∈ Finset.Icc 1 A, psiNat x P ^ 2 * (G * R) :=
      Finset.sum_le_sum hcoeff
    _ = (Finset.Icc 1 A).card * (psiNat x P ^ 2 * (G * R)) := by simp
    _ ≤ A * (psiNat x P ^ 2 * (G * R)) :=
      Nat.mul_le_mul_right _ (by simp)
    _ = A * psiNat x P ^ 2 * G *
        factorialSquareRelationCountBudget ε x := by
      dsimp only [R]
      ring

/-! ## Membership of the chosen Lemma 4.3 data -/

/-- Both chosen coefficients are at most the endpoint cutoff. -/
theorem chosenFactorialRelationCertificate_coefficients_le
    (x : ℕ) (t : ↥(nontrivialFactorialThreeIntervalsUpTo x)) :
    (chosenFactorialRelationCertificate x t).coeffLeft ≤ x ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤ x := by
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have ht := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  rcases hspec with ⟨_ha, _haN, _hcomponent, _hc₁, _hc₂, hn₁, hn₂,
    _hc₁sf, _hc₂sf, _hc₁smooth, _hc₂smooth, _hc₁Bound, _hc₂Bound,
    _hh, _hhH, _heq, hleft, hright⟩
  have hleftLe : c.coeffLeft * c.rootLeft ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hleft).2.trans ht.2.2.2.1
  have hrightLe : c.coeffRight * c.rootRight ^ 2 ≤ x :=
    (Finset.mem_Ioc.mp hright).2.trans ht.2.2.2.1
  constructor
  · have hrootSq : 1 ≤ c.rootLeft ^ 2 := by nlinarith
    exact (Nat.le_mul_of_pos_right c.coeffLeft hrootSq).trans hleftLe
  · have hrootSq : 1 ≤ c.rootRight ^ 2 := by nlinarith
    exact (Nat.le_mul_of_pos_right c.coeffRight hrootSq).trans hrightLe

/-- Lemma 4.3's prime-factor conclusion puts both chosen coefficients in the
literal `P`-smooth range whenever `max a H ≤ P`. -/
theorem chosenFactorialRelationCertificate_coefficients_smooth
    (x P : ℕ) (t : ↥(nontrivialFactorialThreeIntervalsUpTo x))
    (hP : max (chosenFactorialRelationCertificate x t).factorialIndex
      t.1.2 ≤ P) :
    IsSmooth (chosenFactorialRelationCertificate x t).coeffLeft P ∧
      IsSmooth (chosenFactorialRelationCertificate x t).coeffRight P := by
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  change max c.factorialIndex t.1.2 ≤ P at hP
  rcases hspec with ⟨_ha, _haN, _hcomponent, hc₁, hc₂, _hn₁, _hn₂,
    _hc₁sf, _hc₂sf, hc₁smooth, hc₂smooth, _hc₁Bound, _hc₂Bound,
    _hh, _hhH, _heq, _hleft, _hright⟩
  constructor
  · rw [isSmooth_iff]
    exact ⟨Nat.ne_of_gt hc₁, fun p hp hdvd =>
      (hc₁smooth p hp hdvd).trans hP⟩
  · rw [isSmooth_iff]
    exact ⟨Nat.ne_of_gt hc₂, fun p hp hdvd =>
      (hc₂smooth p hp hdvd).trans hP⟩

theorem chosenFactorialRelationCertificate_mem_smooth
    (x A P G : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x))
    (hA : (chosenFactorialRelationCertificate x t).factorialIndex ≤ A)
    (hP : max (chosenFactorialRelationCertificate x t).factorialIndex
      t.1.2 ≤ P)
    (hG : t.1.2 ≤ G) :
    chosenFactorialRelationCertificate x t ∈
      factorialSmoothRelationCertificatesUpTo x A P G := by
  classical
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  change c.factorialIndex ≤ A at hA
  change max c.factorialIndex t.1.2 ≤ P at hP
  have hcoeffLe := chosenFactorialRelationCertificate_coefficients_le x t
  have hcoeffSmooth :=
    chosenFactorialRelationCertificate_coefficients_smooth x P t hP
  rcases hspec with ⟨ha, _haN, _hcomponent, _hc₁, _hc₂, _hn₁, _hn₂,
    _hc₁sf, _hc₂sf, _hc₁smooth, _hc₂smooth, _hc₁Bound, _hc₂Bound,
    hh, hhH, _heq, _hleft, _hright⟩
  have hhG : c.shift ≤ G := hhH.le.trans hG
  rw [factorialSmoothRelationCertificatesUpTo, Finset.mem_biUnion]
  refine ⟨c.factorialIndex, Finset.mem_Icc.mpr ⟨ha, hA⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨(c.coeffLeft, c.coeffRight),
    mem_factorialSmoothCoefficientPairsUpTo.mpr
      ⟨hcoeffLe.1, hcoeffSmooth.1, hcoeffLe.2, hcoeffSmooth.2⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨c.shift, Finset.mem_Icc.mpr ⟨hh, hhG⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(c.rootLeft, c.rootRight),
    chosenFactorialRelationPair_mem x t, rfl⟩

/-! ## Injective smooth codes and endpoint count -/

def factorialSmoothIntervalCodesUpTo
    (x A P G : ℕ) : Finset FactorialIntervalCode :=
  (factorialSmoothRelationCertificatesUpTo x A P G).product
      ((Finset.Icc 2 G).product (Finset.range G)) |>.image fun q =>
    ⟨q.1, q.2.1, q.2.2⟩

theorem chosenFactorialIntervalCode_mem_smooth
    (x A P G : ℕ)
    (t : ↥(nontrivialFactorialThreeIntervalsUpTo x))
    (hA : (chosenFactorialRelationCertificate x t).factorialIndex ≤ A)
    (hP : max (chosenFactorialRelationCertificate x t).factorialIndex
      t.1.2 ≤ P)
    (hG : t.1.2 ≤ G) :
    chosenFactorialIntervalCode x t ∈
      factorialSmoothIntervalCodesUpTo x A P G := by
  classical
  rw [factorialSmoothIntervalCodesUpTo, Finset.mem_image]
  refine ⟨(chosenFactorialRelationCertificate x t,
      ((chosenFactorialIntervalCode x t).intervalLength,
        (chosenFactorialIntervalCode x t).leftOffset)), ?_, rfl⟩
  apply Finset.mem_product.mpr
  refine ⟨chosenFactorialRelationCertificate_mem_smooth
    x A P G t hA hP hG, ?_⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr
    ⟨(mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property).2.1,
      hG⟩, Finset.mem_range.mpr ?_⟩
  exact (chosenFactorialIntervalCode_offset_lt_length x t).trans_le hG

theorem card_factorialSmoothIntervalCodesUpTo_le
    (x A P G : ℕ) :
    (factorialSmoothIntervalCodesUpTo x A P G).card ≤
      (factorialSmoothRelationCertificatesUpTo x A P G).card * (G * G) := by
  classical
  have hIcc : (Finset.Icc 2 G).card ≤ G := by simp
  calc
    (factorialSmoothIntervalCodesUpTo x A P G).card ≤
        ((factorialSmoothRelationCertificatesUpTo x A P G).product
          ((Finset.Icc 2 G).product (Finset.range G))).card :=
      Finset.card_image_le
    _ = (factorialSmoothRelationCertificatesUpTo x A P G).card *
        ((Finset.Icc 2 G).card * G) := by simp
    _ ≤ (factorialSmoothRelationCertificatesUpTo x A P G).card * (G * G) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right G hIcc)

/-- The actual subfamily on which `a ≤ A`, `max a H ≤ P`, and `H ≤ G`.
This is the finite object to which Proposition 2.1(ii) is applied. -/
def factorialSmoothBudgetedIntervalsUpTo
    (x A P G : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
      max (chosenFactorialRelationCertificate x t).factorialIndex t.1.2 ≤ P ∧
      t.1.2 ≤ G

theorem mem_factorialSmoothBudgetedIntervalsUpTo
    {x A P G : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialSmoothBudgetedIntervalsUpTo x A P G ↔
      (chosenFactorialRelationCertificate x t).factorialIndex ≤ A ∧
      max (chosenFactorialRelationCertificate x t).factorialIndex t.1.2 ≤ P ∧
      t.1.2 ≤ G := by
  simp [factorialSmoothBudgetedIntervalsUpTo]

def factorialSmoothBudgetedEndpointsUpTo
    (x A P G : ℕ) : Finset ℕ :=
  (factorialSmoothBudgetedIntervalsUpTo x A P G).image fun t =>
    t.1.1 + t.1.2

theorem card_factorialSmoothBudgetedIntervalsUpTo_le_codes
    (x A P G : ℕ) :
    (factorialSmoothBudgetedIntervalsUpTo x A P G).card ≤
      (factorialSmoothIntervalCodesUpTo x A P G).card := by
  classical
  let s := factorialSmoothBudgetedIntervalsUpTo x A P G
  let encode : ↥s → FactorialIntervalCode := fun t =>
    chosenFactorialIntervalCode x t.1
  have hencode : Function.Injective encode := by
    intro t u htu
    apply Subtype.ext
    exact injective_chosenFactorialIntervalCode x htu
  have himage : s.attach.image encode ⊆
      factorialSmoothIntervalCodesUpTo x A P G := by
    intro code hcode
    rw [Finset.mem_image] at hcode
    rcases hcode with ⟨t, _ht, rfl⟩
    have htBudget : t.1 ∈ factorialSmoothBudgetedIntervalsUpTo x A P G := by
      simpa only [s] using t.property
    have hb := mem_factorialSmoothBudgetedIntervalsUpTo.mp htBudget
    exact chosenFactorialIntervalCode_mem_smooth x A P G t.1
      hb.1 hb.2.1 hb.2.2
  calc
    (factorialSmoothBudgetedIntervalsUpTo x A P G).card = s.attach.card := by
      simp [s]
    _ = (s.attach.image encode).card := by
      rw [Finset.card_image_iff.mpr hencode.injOn]
    _ ≤ (factorialSmoothIntervalCodesUpTo x A P G).card :=
      Finset.card_le_card himage

/-- Exact endpoint estimate for the smooth-coefficient subfamily.  Its only
analytic smooth-number term is the explicit factor `psiNat x P ^ 2`. -/
theorem card_factorialSmoothBudgetedEndpointsUpTo_le
    (x A P G : ℕ) (hx : 1 ≤ x) (hG : G ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    (factorialSmoothBudgetedEndpointsUpTo x A P G).card ≤
      A * psiNat x P ^ 2 * G ^ 3 *
        factorialSquareRelationCountBudget ε x := by
  calc
    (factorialSmoothBudgetedEndpointsUpTo x A P G).card ≤
        (factorialSmoothBudgetedIntervalsUpTo x A P G).card :=
      Finset.card_image_le
    _ ≤ (factorialSmoothIntervalCodesUpTo x A P G).card :=
      card_factorialSmoothBudgetedIntervalsUpTo_le_codes x A P G
    _ ≤ (factorialSmoothRelationCertificatesUpTo x A P G).card * (G * G) :=
      card_factorialSmoothIntervalCodesUpTo_le x A P G
    _ ≤ (A * psiNat x P ^ 2 * G *
        factorialSquareRelationCountBudget ε x) * (G * G) :=
      Nat.mul_le_mul_right _
        (card_factorialSmoothRelationCertificatesUpTo_le
          x A P G hx hG hε)
    _ = A * psiNat x P ^ 2 * G ^ 3 *
        factorialSquareRelationCountBudget ε x := by ring

/-! ## Asymptotic bounded-length consumer -/

/-- With subpolynomial index and length budgets, the concrete logarithmic
smoothness range has a subpolynomial endpoint count.  This is the asymptotic
closure needed after Lemma 4.1 has bounded `a` by `O(log x)` on a
bounded-length family. -/
theorem factorialSmoothBudgetedEndpointCount_powerUpperBound_zero
    (A G : ℕ → ℕ)
    (hA : PowerUpperBound (fun x => (A x : ℝ)) 0)
    (hG : PowerUpperBound (fun x => (G x : ℝ)) 0)
    (hGx : ∀ᶠ x : ℕ in atTop, G x ≤ x)
    {C : ℝ} (hC : 0 < C) :
    PowerUpperBound
      (fun x => ((factorialSmoothBudgetedEndpointsUpTo x (A x)
        (logarithmicSmoothnessBudget C x) (G x)).card : ℝ)) 0 := by
  have hpsi := psiNat_logarithmicSmoothnessBudget_powerUpperBound_zero hC
  have hpsiSq : PowerUpperBound
      (fun x => (psiNat x (logarithmicSmoothnessBudget C x) : ℝ) ^ 2) 0 := by
    simpa [pow_two] using hpsi.mul hpsi
  have hGSq : PowerUpperBound (fun x => (G x : ℝ) ^ 2) 0 := by
    simpa [pow_two] using hG.mul hG
  have hGCube : PowerUpperBound (fun x => (G x : ℝ) ^ 3) 0 := by
    simpa [pow_succ, mul_assoc] using hGSq.mul hG
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hrelation := factorialSquareRelationCountBudget_powerUpperBound hhalf
  have hproduct : PowerUpperBound
      (fun x => (A x : ℝ) *
        (psiNat x (logarithmicSmoothnessBudget C x) : ℝ) ^ 2 *
        (G x : ℝ) ^ 3 *
        (factorialSquareRelationCountBudget (ε / 2) x : ℝ))
      (ε / 2) := by
    simpa [add_zero, zero_add, mul_assoc] using
      ((hA.mul hpsiSq).mul hGCube).mul hrelation
  have hdom :
      (fun x => ((factorialSmoothBudgetedEndpointsUpTo x (A x)
        (logarithmicSmoothnessBudget C x) (G x)).card : ℝ))
        =O[atTop]
      (fun x => (A x : ℝ) *
        (psiNat x (logarithmicSmoothnessBudget C x) : ℝ) ^ 2 *
        (G x : ℝ) ^ 3 *
        (factorialSquareRelationCountBudget (ε / 2) x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ), hGx] with x hx hxG
    have hfinite := card_factorialSmoothBudgetedEndpointsUpTo_le
      x (A x) (logarithmicSmoothnessBudget C x) (G x) hx hxG hhalf
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (by positivity)]
    exact_mod_cast hfinite
  exact hdom.trans (by
    simpa [add_assoc] using hproduct (ε / 2) hhalf)

/-! ## The actual bounded-length source branch -/

/-- Source intervals in the second easy case, where the length is bounded by
one fixed natural constant. -/
def factorialBoundedLengthIntervalsUpTo (x B : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    t.1.2 ≤ B

theorem mem_factorialBoundedLengthIntervalsUpTo
    {x B : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialBoundedLengthIntervalsUpTo x B ↔ t.1.2 ≤ B := by
  simp [factorialBoundedLengthIntervalsUpTo]

def factorialBoundedLengthEndpointsUpTo (x B : ℕ) : Finset ℕ :=
  (factorialBoundedLengthIntervalsUpTo x B).image fun t => t.1.1 + t.1.2

/-- One fixed logarithmic constant large enough to dominate both `a` and
`H` when `H ≤ B`, using the chosen uniform constant in Lemma 4.1. -/
noncomputable def factorialBoundedLengthLogConstant (B : ℕ) : ℝ :=
  taoLemma41Constant * B + B / Real.log 2 + 1

theorem factorialBoundedLengthLogConstant_pos (B : ℕ) :
    0 < factorialBoundedLengthLogConstant B := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlemma : 0 < taoLemma41Constant := taoLemma41Constant_pos
  simp only [factorialBoundedLengthLogConstant]
  positivity

/-- Every bounded-length interval enters the concrete logarithmic smooth
family.  This is the point where Lemma 4.1 supplies `a = O(log x)` and Lemma
4.3 supplies smoothness. -/
theorem factorialBoundedLengthIntervalsUpTo_subset_smoothBudget
    (x B : ℕ) (hx : 2 ≤ x) :
    factorialBoundedLengthIntervalsUpTo x B ⊆
      factorialSmoothBudgetedIntervalsUpTo x
        (logarithmicSmoothnessBudget
          (factorialBoundedLengthLogConstant B) x)
        (logarithmicSmoothnessBudget
          (factorialBoundedLengthLogConstant B) x) B := by
  intro t ht
  have hB := mem_factorialBoundedLengthIntervalsUpTo.mp ht
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have htBase := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  have h41 := taoLemma41_chosenConstant
    (N := t.1.1) (H := t.1.2) (a := c.factorialIndex)
    (by omega) hspec.1 hspec.2.1 hspec.2.2.1
  have hNpos : 0 < t.1.1 := by omega
  have hlogN : 0 ≤ Real.log t.1.1 :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t.1.1))
  have hlogShift : 0 < Real.log (x + 2) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x + 2))
  have hlogLe : Real.log t.1.1 ≤ Real.log (x + 2) := by
    apply Real.log_le_log (by exact_mod_cast hNpos)
    exact_mod_cast (by omega : t.1.1 ≤ x + 2)
  let D := factorialBoundedLengthLogConstant B
  have hDpos : 0 < D := factorialBoundedLengthLogConstant_pos B
  have hDBound : taoLemma41Constant * (B : ℝ) ≤ D := by
    dsimp only [D, factorialBoundedLengthLogConstant]
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : 0 ≤ (B : ℝ) / Real.log 2 := by positivity
    linarith
  have haReal : (c.factorialIndex : ℝ) ≤ D * Real.log (x + 2) := by
    calc
      (c.factorialIndex : ℝ) ≤
          taoLemma41Constant * (t.1.2 : ℝ) * Real.log t.1.1 := h41.2
      _ ≤ taoLemma41Constant * (B : ℝ) * Real.log t.1.1 := by
        gcongr
        exact taoLemma41Constant_pos.le
      _ ≤ taoLemma41Constant * (B : ℝ) * Real.log (x + 2) :=
        mul_le_mul_of_nonneg_left hlogLe
          (mul_nonneg taoLemma41Constant_pos.le (Nat.cast_nonneg _))
      _ ≤ D * Real.log (x + 2) :=
        mul_le_mul_of_nonneg_right hDBound hlogShift.le
  have hHReal : (t.1.2 : ℝ) ≤ D * Real.log (x + 2) := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogTwoLe : Real.log 2 ≤ Real.log (x + 2) :=
      Real.log_le_log (by norm_num)
        (by exact_mod_cast (by omega : 2 ≤ x + 2))
    have hBTerm : (B : ℝ) ≤ (B / Real.log 2) * Real.log (x + 2) := by
      calc
        (B : ℝ) = (B / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ (B / Real.log 2) * Real.log (x + 2) := by gcongr
    calc
      (t.1.2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      _ ≤ (B / Real.log 2) * Real.log (x + 2) := hBTerm
      _ ≤ D * Real.log (x + 2) := by
        gcongr
        dsimp only [D, factorialBoundedLengthLogConstant]
        have hlemma := taoLemma41Constant_pos
        have hprod : 0 ≤ taoLemma41Constant * (B : ℝ) := by positivity
        linarith
  have haBudget : c.factorialIndex ≤ logarithmicSmoothnessBudget D x := by
    have hcast : (c.factorialIndex : ℝ) ≤
        (logarithmicSmoothnessBudget D x : ℝ) := by
      exact haReal.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  have hHBudget : t.1.2 ≤ logarithmicSmoothnessBudget D x := by
    have hcast : (t.1.2 : ℝ) ≤
        (logarithmicSmoothnessBudget D x : ℝ) := by
      exact hHReal.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  apply mem_factorialSmoothBudgetedIntervalsUpTo.mpr
  exact ⟨haBudget, max_le haBudget hHBudget, hB⟩

theorem factorialBoundedLengthEndpointsUpTo_subset_smoothBudget
    (x B : ℕ) (hx : 2 ≤ x) :
    factorialBoundedLengthEndpointsUpTo x B ⊆
      factorialSmoothBudgetedEndpointsUpTo x
        (logarithmicSmoothnessBudget
          (factorialBoundedLengthLogConstant B) x)
        (logarithmicSmoothnessBudget
          (factorialBoundedLengthLogConstant B) x) B := by
  intro n hn
  rw [factorialBoundedLengthEndpointsUpTo, Finset.mem_image] at hn
  rcases hn with ⟨t, ht, rfl⟩
  rw [factorialSmoothBudgetedEndpointsUpTo, Finset.mem_image]
  exact ⟨t,
    factorialBoundedLengthIntervalsUpTo_subset_smoothBudget x B hx ht, rfl⟩

/-- The complete bounded-`H` source branch is subpolynomial.  This proves the
specialized smooth-number input directly, rather than assuming Proposition
2.1(ii). -/
theorem factorialBoundedLengthEndpointCount_powerUpperBound_zero (B : ℕ) :
    PowerUpperBound
      (fun x => ((factorialBoundedLengthEndpointsUpTo x B).card : ℝ)) 0 := by
  let D := factorialBoundedLengthLogConstant B
  have hD : 0 < D := factorialBoundedLengthLogConstant_pos B
  have hBudget := logarithmicSmoothnessBudget_powerUpperBound_zero hD
  have hConst : PowerUpperBound (fun _x : ℕ => (B : ℝ)) 0 := by
    intro ε hε
    refine IsBigO.of_bound (B : ℝ) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _)
      (Real.one_le_rpow hxOne (by linarith))
  have hBx : ∀ᶠ x : ℕ in atTop, B ≤ x := eventually_ge_atTop B
  have hsmooth := factorialSmoothBudgetedEndpointCount_powerUpperBound_zero
    (logarithmicSmoothnessBudget D) (fun _x => B)
    hBudget hConst hBx hD
  intro ε hε
  have hdom :
      (fun x => ((factorialBoundedLengthEndpointsUpTo x B).card : ℝ))
        =O[atTop]
      (fun x => ((factorialSmoothBudgetedEndpointsUpTo x
        (logarithmicSmoothnessBudget D x)
        (logarithmicSmoothnessBudget D x) B).card : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Finset.card_le_card
      (factorialBoundedLengthEndpointsUpTo_subset_smoothBudget x B hx)
  exact hdom.trans (hsmooth ε hε)

end

end Tao2026
