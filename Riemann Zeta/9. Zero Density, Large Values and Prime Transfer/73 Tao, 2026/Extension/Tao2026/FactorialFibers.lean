import Tao2026.FactorialIntervals
import Tao2026.VeryBadIntervals

/-!
# Fibers of factorial squarefree components

This file isolates the exact arithmetic bridge through which the
Erdős--Selfridge theorem enters Tao's proof of Theorem 1.10.  Equality of two
factorial squarefree components is equivalent to the intervening product of
consecutive integers being a square.  The adjacent case is therefore exactly
the case in which the new endpoint itself is a square.
-/

namespace Tao2026

/-- For `a ≤ b`, two factorials have the same squarefree component exactly
when `(a+1)⋯b` is a square. -/
theorem squarefreeComponent_factorial_eq_iff_consecutiveProduct_square
    {a b : ℕ} (hab : a ≤ b) :
    squarefreeComponent a.factorial = squarefreeComponent b.factorial ↔
      ∃ r : ℕ, consecutiveProduct a (b - a) = r ^ 2 := by
  have hfactorial :
      a.factorial * consecutiveProduct a (b - a) = b.factorial := by
    simpa only [Nat.add_sub_of_le hab] using
      factorial_mul_consecutiveProduct a (b - a)
  constructor
  · intro hcomponents
    obtain ⟨m, hm⟩ :=
      (squarefreeComponent_eq_iff_mul_eq_sq
        (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)).mp hcomponents
    have htotal : a.factorial ^ 2 * consecutiveProduct a (b - a) = m ^ 2 := by
      calc
        a.factorial ^ 2 * consecutiveProduct a (b - a) =
            a.factorial *
              (a.factorial * consecutiveProduct a (b - a)) := by ring
        _ = a.factorial * b.factorial := by rw [hfactorial]
        _ = m ^ 2 := hm
    exact exists_eq_sq_of_sq_mul_eq_sq (Nat.factorial_ne_zero a)
      (consecutiveProduct_ne_zero a (b - a)) htotal
  · rintro ⟨r, hr⟩
    apply (squarefreeComponent_eq_iff_mul_eq_sq
      (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)).mpr
    refine ⟨a.factorial * r, ?_⟩
    calc
      a.factorial * b.factorial =
          a.factorial *
            (a.factorial * consecutiveProduct a (b - a)) := by rw [hfactorial]
      _ = a.factorial ^ 2 * consecutiveProduct a (b - a) := by ring
      _ = a.factorial ^ 2 * r ^ 2 := by rw [hr]
      _ = (a.factorial * r) ^ 2 := by ring

/-- Adjacent factorial squarefree components repeat exactly when the larger
index is a square. -/
theorem squarefreeComponent_factorial_succ_eq_iff_square (a : ℕ) :
    squarefreeComponent a.factorial =
        squarefreeComponent (a + 1).factorial ↔
      ∃ r : ℕ, a + 1 = r ^ 2 := by
  simpa only [Nat.add_sub_cancel_left, consecutiveProduct_one] using
    (squarefreeComponent_factorial_eq_iff_consecutiveProduct_square
      (Nat.le_add_right a 1))

/-- The long-interval part of the square case of the Erdős--Selfridge input.
If `N≤H` and the right endpoint is at least two, Bertrand's postulate supplies
a prime in the endpoint's upper half.  That prime occurs exactly once in the
consecutive product, so the product is not a square.  The remaining
Erdős--Selfridge difficulty is therefore confined to `2≤H<N`. -/
theorem not_exists_consecutiveProduct_eq_square_of_start_le_length
    {N H : ℕ} (hsumTwo : 2 ≤ N + H) (hNLeH : N ≤ H) :
    ¬∃ r : ℕ, consecutiveProduct N H = r ^ 2 := by
  obtain ⟨p, hp, hpLower, hpUpper⟩ := taoProposition23i hsumTwo
  have hNltp : N < p := by omega
  have hsumLt : N + H < 2 * p := by omega
  obtain ⟨hpDvd, hpSqNotDvd⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLt
  rintro ⟨r, hr⟩
  have hpDvdR : p ∣ r := hp.dvd_of_dvd_pow (hr ▸ hpDvd)
  apply hpSqNotDvd
  rw [hr]
  exact pow_dvd_pow_of_dvd hpDvdR 2

@[simp]
theorem consecutiveProduct_two (N : ℕ) :
    consecutiveProduct N 2 = (N + 1) * (N + 2) := by
  norm_num [consecutiveProduct, consecutiveInterval,
    Finset.prod_Ioc_succ_top]

/-- The length-two Erdős--Selfridge square case is elementary: the product
lies strictly between the squares of its two consecutive factors. -/
theorem not_exists_consecutiveProduct_eq_square_two (N : ℕ) :
    ¬∃ r : ℕ, consecutiveProduct N 2 = r ^ 2 := by
  rintro ⟨r, hr⟩
  rw [consecutiveProduct_two] at hr
  have hlower : (N + 1) ^ 2 < r ^ 2 := by nlinarith
  have hupper : r ^ 2 < (N + 2) ^ 2 := by nlinarith
  have hNr : N + 1 < r := by nlinarith
  have hrN : r < N + 2 := by nlinarith
  omega

/-- The unconditional first conclusion of Tao's Lemma `abound`: every type
`F₃` interval is shorter than its starting point.  In the complementary
range Bertrand supplies a prime above `N` which occurs exactly once in the
interval product.  Its odd valuation puts it in the squarefree component,
but the defining factorial index is below `N`, so the same prime cannot occur
in that factorial. -/
theorem IsFactorialThreeInterval.length_lt_start {N H : ℕ}
    (hf3 : IsFactorialThreeInterval N H) : H < N := by
  obtain ⟨hH, a, ha, haN, hcomponent⟩ := hf3
  by_contra hnot
  have hNLeH : N ≤ H := by omega
  have hsumTwo : 2 ≤ N + H := by omega
  obtain ⟨p, hp, hpLower, hpUpper⟩ := taoProposition23i hsumTwo
  have hNltp : N < p := by omega
  have hsumLt : N + H < 2 * p := by omega
  obtain ⟨hpDvd, hpSqNotDvd⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLt
  have hproduct0 : consecutiveProduct N H ≠ 0 :=
    consecutiveProduct_ne_zero N H
  have hfacOne : (consecutiveProduct N H).factorization p = 1 := by
    have hone : 1 ≤ (consecutiveProduct N H).factorization p :=
      (hp.pow_dvd_iff_le_factorization hproduct0).mp (by
        simpa using hpDvd)
    have hnotTwo : ¬2 ≤ (consecutiveProduct N H).factorization p := by
      intro htwo
      exact hpSqNotDvd
        ((hp.pow_dvd_iff_le_factorization hproduct0).mpr htwo)
    omega
  have hpMemProduct : p ∈ (consecutiveProduct N H).primeFactors :=
    hp.mem_primeFactors hpDvd hproduct0
  have hpMemComponent :
      p ∈ (squarefreeComponent (consecutiveProduct N H)).primeFactors :=
    mem_primeFactors_squarefreeComponent_iff.mpr
      ⟨hpMemProduct, by simp [hfacOne]⟩
  have hpMemFactorialComponent :
      p ∈ (squarefreeComponent a.factorial).primeFactors := by
    rw [← hcomponent]
    exact hpMemComponent
  have hpDvdFactorial : p ∣ a.factorial :=
    Nat.dvd_of_mem_primeFactors
      (mem_primeFactors_squarefreeComponent_iff.mp
        hpMemFactorialComponent).1
  have hpLeA : p ≤ a := hp.dvd_factorial.mp hpDvdFactorial
  omega

/-- A type-`F₃` interval contains no prime.  Once `H<N`, any prime in
`(N,N+H]` occurs exactly once in the interval product.  It therefore occurs
in its squarefree component, contradicting equality with the squarefree
component of `a!` for `a<N<p`. -/
theorem IsFactorialThreeInterval.not_prime_of_mem {N H p : ℕ}
    (hf3 : IsFactorialThreeInterval N H)
    (hpMem : p ∈ consecutiveInterval N H) : ¬p.Prime := by
  intro hp
  have hHltN : H < N := hf3.length_lt_start
  obtain ⟨hH, a, ha, haN, hcomponent⟩ := hf3
  have hpBounds : N < p ∧ p ≤ N + H := by
    simpa only [consecutiveInterval, Finset.mem_Ioc] using hpMem
  have hNltp : N < p := hpBounds.1
  have hpUpper : p ≤ N + H := hpBounds.2
  have hsumLt : N + H < 2 * p := by omega
  obtain ⟨hpDvd, hpSqNotDvd⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLt
  have hproduct0 : consecutiveProduct N H ≠ 0 :=
    consecutiveProduct_ne_zero N H
  have hfacOne : (consecutiveProduct N H).factorization p = 1 := by
    have hone : 1 ≤ (consecutiveProduct N H).factorization p :=
      (hp.pow_dvd_iff_le_factorization hproduct0).mp (by
        simpa using hpDvd)
    have hnotTwo : ¬2 ≤ (consecutiveProduct N H).factorization p := by
      intro htwo
      exact hpSqNotDvd
        ((hp.pow_dvd_iff_le_factorization hproduct0).mpr htwo)
    omega
  have hpMemProduct : p ∈ (consecutiveProduct N H).primeFactors :=
    hp.mem_primeFactors hpDvd hproduct0
  have hpMemComponent :
      p ∈ (squarefreeComponent (consecutiveProduct N H)).primeFactors :=
    mem_primeFactors_squarefreeComponent_iff.mpr
      ⟨hpMemProduct, by simp [hfacOne]⟩
  have hpMemFactorialComponent :
      p ∈ (squarefreeComponent a.factorial).primeFactors := by
    rw [← hcomponent]
    exact hpMemComponent
  have hpDvdFactorial : p ∣ a.factorial :=
    Nat.dvd_of_mem_primeFactors
      (mem_primeFactors_squarefreeComponent_iff.mp
        hpMemFactorialComponent).1
  have hpLeA : p ≤ a := hp.dvd_factorial.mp hpDvdFactorial
  omega

/-- Triple form of the first `abound` conclusion: the factorial tail length
`a₃-a₂` is strictly smaller than its middle index. -/
theorem IsFactorialSquareTriple.tail_gap_lt_middle {a₁ a₂ a₃ : ℕ}
    (htriple : IsFactorialSquareTriple a₁ a₂ a₃) :
    a₃ - a₂ < a₂ := by
  have hf3 : IsFactorialThreeInterval a₂ (a₃ - a₂) := by
    rw [isFactorialThreeInterval_iff_factorialSquare]
    obtain ⟨m, hm⟩ := htriple.2.2.2
    refine ⟨Nat.sub_pos_of_lt htriple.2.2.1, a₁, m,
      htriple.1, htriple.2.1, ?_⟩
    simpa only [Nat.add_sub_of_le htriple.2.2.1.le] using hm
  exact hf3.length_lt_start

/-- Equal squarefree components of two distinct positive-index factorials
cannot be separated by a long interval.  This is the unconditional Bertrand
range of the factorial-fiber argument; the desired two-element fiber theorem
still requires excluding square products in the residual range `b-a < a`. -/
theorem squarefreeComponent_factorial_eq_imp_gap_lt_start
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (heq : squarefreeComponent a.factorial =
      squarefreeComponent b.factorial) :
    b - a < a := by
  by_contra hgap
  have haLeGap : a ≤ b - a := by omega
  exact not_exists_consecutiveProduct_eq_square_of_start_le_length (by omega) haLeGap
    ((squarefreeComponent_factorial_eq_iff_consecutiveProduct_square hab).mp heq)

/-- The exact square specialization of Erdős--Selfridge needed by Tao.  It is
kept as a proposition (not an axiom): the theorems below prove all remaining
factorial-fiber bookkeeping from any kernel-checked proof of this statement. -/
def ErdosSelfridgeSquareConclusion : Prop :=
  ∀ (N H : ℕ), 2 ≤ H → ¬∃ r : ℕ, consecutiveProduct N H = r ^ 2

/-- The exact residual range left after the Bertrand argument. -/
def ErdosSelfridgeSquareShortConclusion : Prop :=
  ∀ (N H : ℕ), 2 ≤ H → H < N →
    ¬∃ r : ℕ, consecutiveProduct N H = r ^ 2

/-- After the long-interval and length-two arguments, this is the exact
remaining arithmetic core. -/
def ErdosSelfridgeSquareCoreConclusion : Prop :=
  ∀ (N H : ℕ), 3 ≤ H → H < N →
    ¬∃ r : ℕ, consecutiveProduct N H = r ^ 2

/-- The short-range square theorem implies the full square specialization:
its complementary range is precisely the Bertrand theorem proved above. -/
theorem erdosSelfridgeSquareConclusion_of_short
    (hshort : ErdosSelfridgeSquareShortConclusion) :
    ErdosSelfridgeSquareConclusion := by
  intro N H hH
  by_cases hHN : H < N
  · exact hshort N H hH hHN
  · exact not_exists_consecutiveProduct_eq_square_of_start_le_length
      (by omega) (by omega)

theorem erdosSelfridgeSquareConclusion_iff_short :
    ErdosSelfridgeSquareConclusion ↔
      ErdosSelfridgeSquareShortConclusion := by
  constructor
  · intro hfull N H hH _
    exact hfull N H hH
  · exact erdosSelfridgeSquareConclusion_of_short

/-- The full square theorem is equivalent to just its short cases of length
at least three. -/
theorem erdosSelfridgeSquareConclusion_of_core
    (hcore : ErdosSelfridgeSquareCoreConclusion) :
    ErdosSelfridgeSquareConclusion := by
  intro N H hH
  by_cases htwo : H = 2
  · subst H
    exact not_exists_consecutiveProduct_eq_square_two N
  by_cases hHN : H < N
  · exact hcore N H (by omega) hHN
  · exact not_exists_consecutiveProduct_eq_square_of_start_le_length
      (by omega) (by omega)

theorem erdosSelfridgeSquareConclusion_iff_core :
    ErdosSelfridgeSquareConclusion ↔
      ErdosSelfridgeSquareCoreConclusion := by
  constructor
  · intro hfull N H _ _
    exact hfull N H (by omega)
  · exact erdosSelfridgeSquareConclusion_of_core

/-- The finite fiber of the factorial squarefree-component map on `[0,x]`. -/
def factorialSquarefreeFiberUpTo (x d : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    (fun a => squarefreeComponent a.factorial = d)

theorem mem_factorialSquarefreeFiberUpTo {x d a : ℕ} :
    a ∈ factorialSquarefreeFiberUpTo x d ↔
      a ≤ x ∧ squarefreeComponent a.factorial = d := by
  simp [factorialSquarefreeFiberUpTo]

/-- Erdős--Selfridge forces any two ordered indices in one factorial fiber to
be equal or adjacent. -/
theorem factorialSquarefreeFiber_pair_gap_lt_two
    (hES : ErdosSelfridgeSquareConclusion)
    {x d a b : ℕ} (ha : a ∈ factorialSquarefreeFiberUpTo x d)
    (hb : b ∈ factorialSquarefreeFiberUpTo x d) (hab : a ≤ b) :
    b - a < 2 := by
  rw [mem_factorialSquarefreeFiberUpTo] at ha hb
  by_contra hgap
  have htwo : 2 ≤ b - a := by omega
  have heq : squarefreeComponent a.factorial =
      squarefreeComponent b.factorial := ha.2.trans hb.2.symm
  exact hES a (b - a) htwo
    ((squarefreeComponent_factorial_eq_iff_consecutiveProduct_square hab).mp heq)

/-- A finite set of naturals whose ordered pairs differ by less than two has
at most two elements. -/
theorem card_le_two_of_ordered_pair_sub_lt_two {s : Finset ℕ}
    (hgap : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → b - a < 2) :
    s.card ≤ 2 := by
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := s.min'_mem hs
    have hsubset : s ⊆ {a, a + 1} := by
      intro b hb
      have hab : a ≤ b := s.min'_le b hb
      have hlt : b - a < 2 := hgap a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsubset).trans (by simp)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- The complete finite combinatorial consequence used after Tao's Theorem
1.10: the square specialization of Erdős--Selfridge bounds every factorial
squarefree-component fiber by two. -/
theorem factorialSquarefreeFiberUpTo_card_le_two
    (hES : ErdosSelfridgeSquareConclusion) (x d : ℕ) :
    (factorialSquarefreeFiberUpTo x d).card ≤ 2 := by
  apply card_le_two_of_ordered_pair_sub_lt_two
  intro a ha b hb hab
  exact factorialSquarefreeFiber_pair_gap_lt_two hES ha hb hab

/-- A source-useful global form of the two-element fiber result: parity
distinguishes the only possible repeated indices, which must be adjacent. -/
theorem eq_of_squarefreeComponent_factorial_eq_of_mod_two_eq
    (hES : ErdosSelfridgeSquareConclusion) {a b : ℕ}
    (hcomponent : squarefreeComponent a.factorial =
      squarefreeComponent b.factorial) (hmod : a % 2 = b % 2) :
    a = b := by
  rcases le_total a b with hab | hba
  · by_contra hne
    have hgap : 2 ≤ b - a := by omega
    exact hES a (b - a) hgap
      ((squarefreeComponent_factorial_eq_iff_consecutiveProduct_square hab).mp
        hcomponent)
  · by_contra hne
    have hgap : 2 ≤ a - b := by omega
    exact hES b (a - b) hgap
      ((squarefreeComponent_factorial_eq_iff_consecutiveProduct_square hba).mp
        hcomponent.symm)

/-- Equivalently, factorial squarefree component together with index parity is
an injective encoding of the index. -/
theorem injective_factorialComponentParity
    (hES : ErdosSelfridgeSquareConclusion) :
    Function.Injective
      (fun a : ℕ => (squarefreeComponent a.factorial, a % 2)) := by
  intro a b hab
  exact eq_of_squarefreeComponent_factorial_eq_of_mod_two_eq hES
    (Prod.mk.inj hab).1 (Prod.mk.inj hab).2

/-- In a factorial-square triple, the first factorial has the same squarefree
component as the product of the two tail factorials. -/
theorem squarefreeComponent_factorial_eq_tail_of_triple
    {a₁ a₂ a₃ : ℕ} (htriple : IsFactorialSquareTriple a₁ a₂ a₃) :
    squarefreeComponent a₁.factorial =
      squarefreeComponent (a₂.factorial * a₃.factorial) := by
  apply (squarefreeComponent_eq_iff_mul_eq_sq
    (Nat.factorial_ne_zero a₁)
    (mul_ne_zero (Nat.factorial_ne_zero a₂)
      (Nat.factorial_ne_zero a₃))).mpr
  obtain ⟨m, hm⟩ := htriple.2.2.2
  exact ⟨m, by simpa [mul_assoc] using hm⟩

/-- Tao's exact finite counting key: retain the endpoint, encode the tail
length by a zero-based offset, and retain one parity bit for the first index. -/
def factorialSquareTripleCountingKey (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.2.2, (t.2.2 - t.2.1 - 1, t.1 % 2))

/-- Erdős--Selfridge makes the counting key injective on the finite triple
set.  The endpoint and offset recover `a₂,a₃`; the common tail then fixes the
squarefree component of `a₁`, and its parity fixes `a₁` itself. -/
theorem injOn_factorialSquareTripleCountingKey
    (hES : ErdosSelfridgeSquareConclusion) (x : ℕ) :
    Set.InjOn factorialSquareTripleCountingKey
      (factorialSquareTriplesUpTo x : Set (ℕ × ℕ × ℕ)) := by
  intro t ht u hu hkey
  change t ∈ factorialSquareTriplesUpTo x at ht
  change u ∈ factorialSquareTriplesUpTo x at hu
  rw [mem_factorialSquareTriplesUpTo] at ht hu
  have ha₃ : t.2.2 = u.2.2 := congrArg (fun k => k.1) hkey
  have hoffset : t.2.2 - t.2.1 - 1 = u.2.2 - u.2.1 - 1 :=
    congrArg (fun k => k.2.1) hkey
  have hparity : t.1 % 2 = u.1 % 2 :=
    congrArg (fun k => k.2.2) hkey
  have htTriple : IsFactorialSquareTriple t.1 t.2.1 t.2.2 := ht.2.2.2
  have huTriple : IsFactorialSquareTriple u.1 u.2.1 u.2.2 := hu.2.2.2
  have htOrder : t.2.1 < t.2.2 := htTriple.2.2.1
  have huOrder : u.2.1 < u.2.2 := huTriple.2.2.1
  have ha₂ : t.2.1 = u.2.1 := by omega
  have htComponent :=
    squarefreeComponent_factorial_eq_tail_of_triple htTriple
  have huComponent :=
    squarefreeComponent_factorial_eq_tail_of_triple huTriple
  have hcomponent : squarefreeComponent t.1.factorial =
      squarefreeComponent u.1.factorial := by
    calc
      squarefreeComponent t.1.factorial =
          squarefreeComponent (t.2.1.factorial * t.2.2.factorial) :=
        htComponent
      _ = squarefreeComponent (u.2.1.factorial * u.2.2.factorial) := by
        rw [ha₂, ha₃]
      _ = squarefreeComponent u.1.factorial := huComponent.symm
  have ha₁ : t.1 = u.1 :=
    eq_of_squarefreeComponent_factorial_eq_of_mod_two_eq
      hES hcomponent hparity
  exact Prod.ext ha₁ (Prod.ext ha₂ ha₃)

/-- The finite box of possible counting keys when every tail length is at
most `g`. -/
noncomputable def factorialSquareTripleCountingKeyBox (x g : ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  (factorialThreeNumbersUpTo x).product
    ((Finset.range g).product (Finset.range 2))

/-- Under a uniform tail-length bound, every actual key lies in the expected
endpoint-by-offset-by-parity box. -/
theorem image_factorialSquareTripleCountingKey_subset_box
    {x g : ℕ}
    (hgap : ∀ t ∈ factorialSquareTriplesUpTo x,
      t.2.2 - t.2.1 ≤ g) :
    (factorialSquareTriplesUpTo x).image
        factorialSquareTripleCountingKey ⊆
      factorialSquareTripleCountingKeyBox x g := by
  classical
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨t, ht, rfl⟩ := hk
  have htEndpoint : t.2.2 ∈ factorialThreeNumbersUpTo x := by
    rw [← image_factorialSquareTriplesUpTo_endpoint]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  change (t.2.2, (t.2.2 - t.2.1 - 1, t.1 % 2)) ∈
    (factorialThreeNumbersUpTo x).product
      ((Finset.range g).product (Finset.range 2))
  apply Finset.mem_product.mpr
  refine ⟨htEndpoint, Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr
    (Nat.mod_lt _ (by omega))⟩⟩
  apply Finset.mem_range.mpr
  change t.2.2 - t.2.1 - 1 < g
  rw [mem_factorialSquareTriplesUpTo] at ht
  have horder : t.2.1 < t.2.2 := ht.2.2.2.2.2.1
  have hlength := hgap t (mem_factorialSquareTriplesUpTo.mpr ht)
  omega

/-- Exact finite form of Tao's final Theorem 1.10 counting step.  If every
factorial-square triple up to `x` has tail length at most `g`, then
Erdős--Selfridge, endpoint projection, the zero-based tail offset, and one
parity bit give the sharp cardinal bound `2g·#F₃(x)`. -/
theorem factorialSquareTripleCount_le_two_mul_gap_mul_factorialThreeCount
    (hES : ErdosSelfridgeSquareConclusion) {x g : ℕ}
    (hgap : ∀ t ∈ factorialSquareTriplesUpTo x,
      t.2.2 - t.2.1 ≤ g) :
    factorialSquareTripleCount x ≤ 2 * g * factorialThreeCount x := by
  classical
  change (factorialSquareTriplesUpTo x).card ≤
    2 * g * (factorialThreeNumbersUpTo x).card
  calc
    (factorialSquareTriplesUpTo x).card =
        ((factorialSquareTriplesUpTo x).image
          factorialSquareTripleCountingKey).card :=
      (Finset.card_image_of_injOn
        (injOn_factorialSquareTripleCountingKey hES x)).symm
    _ ≤ (factorialSquareTripleCountingKeyBox x g).card :=
      Finset.card_le_card
        (image_factorialSquareTripleCountingKey_subset_box hgap)
    _ = 2 * g * (factorialThreeNumbersUpTo x).card := by
      simp [factorialSquareTripleCountingKeyBox]
      ring

end Tao2026
