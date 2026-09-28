import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import TaoTrudgianYang2025.IntegerIntervalCount

/-!
# Huxley's finite linear-form and Farey-sector estimates

Huxley, *Exponential Sums and the Riemann Zeta Function IV* (1993),
Section 2: the complete Lemma 2.1 dichotomy and the two displayed bounds
of Lemma 2.5. The Farey neighbor is constructed from Bezout coefficients;
no rational approximation, counting estimate or adjacency is assumed.

The printed words "both integers" in Lemma 2.5 are false for positive
error. The original PDF is preserved, and
`printed_exact_integrality_counterexample` records the discrepancy.
Only the quantitative near-integer conclusions are asserted here.
Lemmas 2.3/2.6 and the parameter-family fifth moment remain separate
obligations; this module does not prove a Huxley beta bound.
-/

noncomputable section
open Set

namespace TaoTrudgianYang2025.HuxleyLinearForm

/-- The small-denominator branch of Huxley (1993), Lemma 2.1 starts
with this exact integer identity. Both error estimates are upstream
rational/near-integer data, not a conclusion-shaped counting assumption. -/
theorem small_denominator_integer_identity
    {N q n : ℕ} {a b : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hn : n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hsmall : (q:ℝ)*δ < 1/2)
    (hnear : |(n:ℝ)*α-b| ≤ δ) :
    (n:ℤ)*a = (q:ℤ)*b := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hnR : (n:ℝ) ≤ N := Nat.cast_le.mpr hn
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hterm : (n:ℝ)*|(q:ℝ)*α-a| ≤ 1/2 := by
    calc
      _ ≤ (N:ℝ)*(1/(2*(N:ℝ))) :=
        mul_le_mul hnR happrox (abs_nonneg _) hNR.le
      _ = _ := by field_simp
  have he : |(((n:ℤ)*a-(q:ℤ)*b:ℤ):ℝ)| < 1 := by
    have hident : (((n:ℤ)*a-(q:ℤ)*b:ℤ):ℝ) =
        (q:ℝ)*((n:ℝ)*α-b)-(n:ℝ)*((q:ℝ)*α-a) := by
      push_cast
      ring
    rw [hident]
    calc
      _ ≤ |(q:ℝ)*((n:ℝ)*α-b)|+|(n:ℝ)*((q:ℝ)*α-a)| := abs_sub _ _
      _ = (q:ℝ)*|(n:ℝ)*α-b|+(n:ℝ)*|(q:ℝ)*α-a| := by
        simp only [abs_mul,abs_of_pos hqR,
          abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ ≤ (q:ℝ)*δ+1/2 := add_le_add (mul_le_mul_of_nonneg_left hnear hqR.le) hterm
      _ < 1 := by linarith
  have he' : |(n:ℤ)*a-(q:ℤ)*b| < 1 := by exact_mod_cast he
  have hab := abs_lt.mp he'
  omega

theorem card_mul_le_of_dvd
    (S : Finset ℕ) {q N : ℕ} (hq : 0 < q)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hdvd : ∀ n ∈ S, q ∣ n) : q*S.card ≤ N := by
  have hmap : Set.MapsTo (fun n : ℕ => n/q) S (Finset.Icc 1 (N/q)) := by
    intro n hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.le_div_iff_mul_le hq).mpr
        (by simpa using Nat.le_of_dvd (hS n hn).1 (hdvd n hn))
    · exact Nat.div_le_div_right (hS n hn).2
  have hinj : Set.InjOn (fun n : ℕ => n/q) S := by
    intro n hn m hm he
    change n/q=m/q at he
    calc
      n = (n/q)*q := (Nat.div_mul_cancel (hdvd n hn)).symm
      _ = (m/q)*q := by rw [he]
      _ = m := Nat.div_mul_cancel (hdvd m hm)
  have hc : S.card ≤ N/q := by
    have h := Finset.card_le_card_of_injOn (fun n : ℕ => n/q) hmap hinj
    simpa using h
  exact (Nat.mul_le_mul_left q hc).trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self N q)

theorem small_denominator_branch
    (S : Finset ℕ) {N q : ℕ} {a : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hδ : 0 ≤ δ)
    (hcop : IsCoprime a (q:ℤ))
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hsmall : (q:ℝ)*δ < 1/2)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (∀ n ∈ S, q ∣ n) ∧ q*S.card ≤ N ∧
      |(q:ℝ)*α-a| * (S.card:ℝ) ≤ δ := by
  have hdvd : ∀ n ∈ S, q ∣ n := by
    intro n hn
    obtain ⟨b,hb⟩ := hnear n hn
    have he := small_denominator_integer_identity hN hq (hS n hn).2 happrox hsmall hb
    have hdiv : (q:ℤ) ∣ (n:ℤ)*a := ⟨b,he⟩
    exact_mod_cast hcop.symm.dvd_of_dvd_mul_right hdiv
  refine ⟨hdvd,card_mul_le_of_dvd S hq hS hdvd,?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hδ
  let n := S.max' hne
  have hn : n ∈ S := Finset.max'_mem S hne
  have hcard : q*S.card ≤ n := card_mul_le_of_dvd S hq
    (fun m hm => ⟨(hS m hm).1,Finset.le_max' S m hm⟩) hdvd
  obtain ⟨b,hb⟩ := hnear n hn
  have he := small_denominator_integer_identity hN hq (hS n hn).2 happrox hsmall hb
  have heR : (n:ℝ)*((q:ℝ)*α-a) = (q:ℝ)*((n:ℝ)*α-b) := by
    have h : (n:ℝ)*(a:ℝ) = (q:ℝ)*(b:ℝ) := by exact_mod_cast he
    nlinarith only [h]
  have hbound : (n:ℝ)*|(q:ℝ)*α-a| ≤ (q:ℝ)*δ := by
    calc
      _ = |(n:ℝ)*((q:ℝ)*α-a)| := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ = (q:ℝ)*|(n:ℝ)*α-b| := by
        rw [heR,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ q from Nat.cast_nonneg q)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)
  have hcardR : (q:ℝ)*(S.card:ℝ) ≤ n := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_right hcardR (abs_nonneg ((q:ℝ)*α-a))
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  nlinarith only [hbound,hm,hqR]

/-- The actual reduced Dirichlet approximation at the scale used in Lemma 2.1. -/
theorem exists_reduced_approximation (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ a : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ 2*N-1 ∧ IsCoprime a (q:ℤ) ∧
      |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)) := by
  obtain ⟨r,hr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α
    (show 0 < 2*N-1 by omega)
  have hd : (0:ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hscale : ((2*N-1:ℕ):ℝ)+1 = 2*(N:ℝ) := by
    have he : (2*N-1)+1=2*N := by omega
    exact_mod_cast he
  refine ⟨r.num,r.den,r.pos,hden,r.isCoprime_num_den,?_⟩
  rw [hscale] at hr
  have h := mul_le_mul_of_nonneg_right hr hd.le
  have he : |α-(r:ℝ)| * (r.den:ℝ) = |(r.den:ℝ)*α-r.num| := by
    calc
      _ = |(α-(r:ℝ))*(r.den:ℝ)| := by rw [abs_mul,abs_of_pos hd]
      _ = _ := by
        congr 1
        rw [Rat.cast_def]
        field_simp
  rw [he] at h
  convert h using 1
  field_simp

theorem fixed_residual_separated {q n m : ℕ} {a e : ℤ}
    (b : ℕ → ℤ) (hq : 0 < q) (hcop : IsCoprime a (q:ℤ))
    (hn : a*(n:ℤ)-(q:ℤ)*b n=e) (hm : a*(m:ℤ)-(q:ℤ)*b m=e)
    (hne : n ≠ m) : (q:ℝ) ≤ |(n:ℝ)-(m:ℝ)| := by
  have hdiv : (q:ℤ) ∣ a*((n:ℤ)-(m:ℤ)) :=
    ⟨b n-b m,by nlinarith only [hn,hm]⟩
  obtain ⟨k,hk⟩ := hcop.symm.dvd_of_dvd_mul_left hdiv
  have hk0 : k ≠ 0 := by
    intro he
    rw [he,mul_zero] at hk
    exact hne (by exact_mod_cast sub_eq_zero.mp hk)
  have hk1 : (1:ℤ) ≤ |k| := by have h := abs_pos.mpr hk0; omega
  have hkr : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast hk1
  have he : (n:ℝ)-(m:ℝ) = (q:ℝ)*(k:ℝ) := by exact_mod_cast hk
  rw [he,abs_mul,abs_of_pos (show (0:ℝ) < q from Nat.cast_pos.mpr hq)]
  exact le_mul_of_one_le_right (Nat.cast_nonneg q) hkr

theorem fixed_residual_card_bound (S : Finset ℕ) (b : ℕ → ℤ)
    {N q : ℕ} {a e : ℤ} (hN : 0 < N) (hq : 0 < q)
    (hcop : IsCoprime a (q:ℤ)) (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (he : ∀ n ∈ S, a*(n:ℤ)-(q:ℤ)*b n=e) :
    (S.card:ℝ) ≤ ((N:ℝ)-1)/q+1 := by
  classical
  let W := S.image (fun n : ℕ => (n:ℝ)/q)
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hy
    have hnm : n ≠ m := by intro h; exact hxy (by rw [h])
    have hd := fixed_residual_separated b hq hcop (he n hn) (he m hm) hnm
    rw [← sub_div,abs_div,abs_of_pos hqR]
    exact (le_div_iff₀ hqR).mpr (by simpa using hd)
  have hmem : ∀ x ∈ W, 1/(q:ℝ) ≤ x ∧ x ≤ (N:ℝ)/q := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast (hS n hn).1) hqR.le,
      div_le_div_of_nonneg_right (by exact_mod_cast (hS n hn).2) hqR.le⟩
  have hlen : 0 ≤ (N:ℝ)/q-1/q := sub_nonneg.mpr
    (div_le_div_of_nonneg_right (by exact_mod_cast hN) hqR.le)
  have hc := oneSeparated_card_cast_le_interval_length_add_one W hsep hlen hmem
  have hcard : W.card=S.card := Finset.card_image_of_injective S
    (fun _ _ h => Nat.cast_injective ((div_left_inj' hqR.ne').mp h))
  rw [hcard,← sub_div] at hc
  exact hc

theorem large_denominator_branch
    (S : Finset ℕ) {N q : ℕ} {a : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hqN : q ≤ 2*N) (hδ : 0 ≤ δ)
    (hcop : IsCoprime a (q:ℤ))
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hlarge : 1/2 ≤ (q:ℝ)*δ)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N := by
  classical
  let b : ℕ → ℤ := fun n => if hn : n ∈ S then Classical.choose (hnear n hn) else 0
  have hb (n : ℕ) (hn : n ∈ S) : |(n:ℝ)*α-b n| ≤ δ := by
    simpa only [b,dif_pos hn] using Classical.choose_spec (hnear n hn)
  let e : ℕ → ℤ := fun n => a*(n:ℤ)-(q:ℤ)*b n
  let E := S.image e
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have he (n : ℕ) (hn : n ∈ S) : |(e n:ℝ)| ≤ 2*(q:ℝ)*δ := by
    have hterm : (n:ℝ)*|(q:ℝ)*α-a| ≤ 1/2 := by
      calc
        _ ≤ (N:ℝ)*(1/(2*(N:ℝ))) :=
          mul_le_mul (by exact_mod_cast (hS n hn).2) happrox (abs_nonneg _) hNR.le
        _ = _ := by field_simp
    have hid : (e n:ℝ) =
        (q:ℝ)*((n:ℝ)*α-b n)-(n:ℝ)*((q:ℝ)*α-a) := by
      dsimp [e]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(q:ℝ)*((n:ℝ)*α-b n)|+|(n:ℝ)*((q:ℝ)*α-a)| := abs_sub _ _
      _ = (q:ℝ)*|(n:ℝ)*α-b n|+(n:ℝ)*|(q:ℝ)*α-a| := by
        simp only [abs_mul,abs_of_pos hqR,
          abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ ≤ (q:ℝ)*δ+1/2 := add_le_add (mul_le_mul_of_nonneg_left (hb n hn) hqR.le) hterm
      _ ≤ _ := by linarith
  have hE : (E.card:ℝ) ≤ 6*(q:ℝ)*δ := by
    have hcount := integer_card_le_of_abs_sub_le E (a := 0)
      (by positivity : 0 ≤ 2*(q:ℝ)*δ) (fun z hz => by
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
        simpa only [sub_zero] using he n hn)
    linarith
  let B : ℝ := if q ≤ N then 2*(N:ℝ)/q else 1
  have hB : 0 ≤ B := by dsimp only [B]; split <;> positivity
  have hfiber (z : ℤ) : ((S.filter (fun n => e n=z)).card:ℝ) ≤ B := by
    let T := S.filter (fun n => e n=z)
    have hc := fixed_residual_card_bound T b hN hq hcop
      (fun n hn => hS n (Finset.mem_filter.mp hn).1)
      (fun n hn => (Finset.mem_filter.mp hn).2)
    by_cases hqN' : q ≤ N
    · dsimp only [B]
      rw [if_pos hqN']
      have hqr : (q:ℝ) ≤ N := by exact_mod_cast hqN'
      have hcomp : ((N:ℝ)-1)/q+1 ≤ 2*(N:ℝ)/q := by
        apply (le_div_iff₀ hqR).mpr
        rw [add_mul,div_mul_cancel₀ _ hqR.ne']
        linarith
      exact hc.trans hcomp
    · dsimp only [B]
      rw [if_neg hqN']
      have hqr : (N:ℝ) < q := by exact_mod_cast Nat.lt_of_not_ge hqN'
      have hlt : ((N:ℝ)-1)/q < 1 := (div_lt_one hqR).mpr (by linarith)
      have hn : T.card < 2 := by exact_mod_cast (show (T.card:ℝ) < 2 by linarith)
      exact_mod_cast (show T.card ≤ 1 by omega)
  have hmaps : Set.MapsTo e S E := fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩
  have hcard : (S.card:ℝ) = ∑ z ∈ E, ((S.filter (fun n => e n=z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : (S.card:ℝ) ≤ (6*(q:ℝ)*δ)*B := by
    calc
      _ = _ := hcard
      _ ≤ ∑ _z ∈ E, B := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (E.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE hB
  apply hbound.trans
  dsimp only [B]
  split
  · have heq : 6*(q:ℝ)*δ*(2*(N:ℝ)/q)=12*δ*N := by field_simp; ring
    exact heq.le
  · have hqr : (q:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hqN
    have hmul := mul_le_mul_of_nonneg_right hqr hδ
    nlinarith only [hmul]

/-- Huxley (1993), Lemma 2.1, with cardinality R represented by S.card.
The rational approximation is constructed, not assumed. -/
theorem linear_form_dichotomy
    (S : Finset ℕ) {N : ℕ} {α δ : ℝ}
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N ∨
      ∃ q : ℕ, 0 < q ∧ q*S.card ≤ N ∧ (∀ n ∈ S, q ∣ n) ∧
        ∃ a : ℤ, |(q:ℝ)*α-a| * (S.card:ℝ) ≤ δ := by
  obtain ⟨a,q,hq,hqN,hcop,happrox⟩ := exists_reduced_approximation α hN
  by_cases hsmall : (q:ℝ)*δ < 1/2
  · obtain ⟨hdvd,hcard,hclose⟩ := small_denominator_branch S hN hq hδ hcop
      hS happrox hsmall hnear
    exact Or.inr ⟨q,hq,hcard,hdvd,a,hclose⟩
  · exact Or.inl (large_denominator_branch S hN hq (by omega) hδ hcop
      hS happrox (le_of_not_gt hsmall) hnear)

/-- Literal nearest-integer form of Lemma 2.1 for a nonempty subsequence. -/
theorem linear_form_dichotomy_round
    (S : Finset ℕ) {N : ℕ} {α δ : ℝ}
    (hne : S.Nonempty) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hnear : ∀ n ∈ S, |(n:ℝ)*α-(round ((n:ℝ)*α):ℤ)| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N ∨
      ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ (N:ℝ)/S.card ∧
        |(q:ℝ)*α-(round ((q:ℝ)*α):ℤ)| ≤ δ/S.card ∧
        ∀ n ∈ S, q ∣ n := by
  rcases linear_form_dichotomy S hN hδ hS
    (fun n hn => ⟨round ((n:ℝ)*α),hnear n hn⟩) with h | ⟨q,hq,hqN,hdvd,a,ha⟩
  · exact Or.inl h
  · have hR : (0:ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
    refine Or.inr ⟨q,hq,?_,?_,hdvd⟩
    · exact (le_div_iff₀ hR).mpr (by exact_mod_cast hqN)
    · apply (round_le ((q:ℝ)*α) a).trans
      exact (le_div_iff₀ hR).mpr ha

/-- The determinant labels in the proof of Lemma 2.5 are injective when
the primitive reference point has maximal positive denominator. -/
theorem maximal_denominator_determinant_injective
    {m₀ n₀ : ℤ} (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    Set.InjOn (fun p : ℤ × ℤ => m₀*p.2-n₀*p.1)
      {p | 1 ≤ p.2 ∧ p.2 ≤ n₀} := by
  intro p hp q hq he
  have hdiv : n₀ ∣ m₀*(p.2-q.2) := ⟨p.1-q.1,by dsimp at he; nlinarith only [he]⟩
  obtain ⟨k,hk⟩ := hcop.symm.dvd_of_dvd_mul_left hdiv
  have hk0 : k=0 := by
    by_contra hne
    have hd : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hd with hd | hd <;> nlinarith [hp.1,hp.2,hq.1,hq.2]
  have hden : p.2=q.2 := by rw [hk0,mul_zero] at hk; exact sub_eq_zero.mp hk
  have hnum : p.1=q.1 := by
    have he' : n₀*(p.1-q.1)=0 := by dsimp at he; rw [hden] at he; nlinarith only [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left hn₀.ne')
  exact Prod.ext hnum hden

/-- Each determinant has a genuine near-integer alpha constraint, with
the original pair of approximation errors retained. -/
theorem determinant_alpha_near
    (m₀ n₀ m n b₀ b : ℤ) {α β δ N : ℝ}
    (hn : |(n:ℝ)| ≤ N) (hn₀ : |(n₀:ℝ)| ≤ N)
    (hzero : |(m₀:ℝ)*α+(n₀:ℝ)*β-b₀| ≤ δ)
    (hpoint : |(m:ℝ)*α+(n:ℝ)*β-b| ≤ δ) :
    |((m₀*n-n₀*m:ℤ):ℝ)*α-((n*b₀-n₀*b:ℤ):ℝ)| ≤ 2*N*δ := by
  have he : ((m₀*n-n₀*m:ℤ):ℝ)*α-((n*b₀-n₀*b:ℤ):ℝ) =
      (n:ℝ)*((m₀:ℝ)*α+(n₀:ℝ)*β-b₀)-(n₀:ℝ)*((m:ℝ)*α+(n:ℝ)*β-b) := by
    push_cast
    ring
  rw [he]
  have hN : 0 ≤ N := (abs_nonneg _).trans hn
  calc
    _ ≤ |(n:ℝ)*((m₀:ℝ)*α+(n₀:ℝ)*β-b₀)|+
        |(n₀:ℝ)*((m:ℝ)*α+(n:ℝ)*β-b)| := abs_sub _ _
    _ ≤ N*δ+N*δ := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hn hzero (abs_nonneg _) hN)
        (mul_le_mul hn₀ hpoint (abs_nonneg _) hN)
    _ = _ := by ring

theorem determinant_beta_near
    (m₀ n₀ m n b₀ b : ℤ) {α β δ M : ℝ}
    (hm : |(m:ℝ)| ≤ M) (hm₀ : |(m₀:ℝ)| ≤ M)
    (hzero : |(m₀:ℝ)*α+(n₀:ℝ)*β-b₀| ≤ δ)
    (hpoint : |(m:ℝ)*α+(n:ℝ)*β-b| ≤ δ) :
    |((m₀*n-n₀*m:ℤ):ℝ)*β-((m₀*b-m*b₀:ℤ):ℝ)| ≤ 2*M*δ := by
  have h := determinant_alpha_near n₀ m₀ n m b₀ b hm hm₀
    (α := β) (β := α) (by simpa only [add_comm] using hzero)
    (by simpa only [add_comm] using hpoint)
  have he : ((m₀*n-n₀*m:ℤ):ℝ)*β-((m₀*b-m*b₀:ℤ):ℝ) =
      -(((n₀*m-m₀*n:ℤ):ℝ)*β-((m*b₀-m₀*b:ℤ):ℝ)) := by
    push_cast
    ring
  rw [he,abs_neg]
  exact h

/-- A right Farey neighbor at the reference denominator, constructed from
Bezout coefficients. The last clause proves that no smaller-denominator
fraction can lie strictly between the reference and this neighbor. -/
theorem exists_right_neighbor {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = -1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → m₀*n < n₀*m → a*n ≤ m*b := by
  obtain ⟨u,v,huv⟩ := hcop
  let k : ℤ := (-u-1)/n₀
  let b : ℤ := (-u-1)%n₀+1
  let a : ℤ := v-k*m₀
  have hb : 1 ≤ b ∧ b ≤ n₀ := by
    have hlow := Int.emod_nonneg (-u-1) hn₀.ne'
    have hhigh := Int.emod_lt_of_pos (-u-1) hn₀
    dsimp [b]
    omega
  have hbform : b = -u-k*n₀ := by
    have he := Int.emod_add_mul_ediv (-u-1) n₀
    dsimp [b,k]
    nlinarith only [he]
  have hdet : m₀*b-n₀*a = -1 := by
    dsimp [a]
    rw [hbform]
    nlinarith only [huv]
  refine ⟨a,b,hb.1,hb.2,⟨n₀,-m₀,by nlinarith only [hdet]⟩,hdet,?_⟩
  intro m n _hn hnmax hright
  have hd : 1 ≤ n₀*m-m₀*n := by omega
  have hprod : 1 ≤ (n₀*m-m₀*n)*b := one_le_mul_of_one_le_of_one_le hd hb.1
  have he : n-(n₀*m-m₀*n)*b = n₀*(a*n-m*b) := by
    have h := congrArg (fun z : ℤ => z*n) hdet
    nlinarith only [h]
  by_contra hbad
  have hc : 1 ≤ a*n-m*b := by omega
  have hlarge := mul_le_mul_of_nonneg_left hc hn₀.le
  nlinarith only [he,hprod,hnmax,hlarge]

theorem exists_left_neighbor {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = 1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → n₀*m < m₀*n → m*b ≤ a*n := by
  obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_right_neighbor hn₀ hcop.neg_left
  refine ⟨-a,b,hb,hbmax,hcop'.neg_left,by nlinarith only [hdet],?_⟩
  intro m n hn hnmax hleft
  have h := hclose (-m) n hn hnmax (by nlinarith only [hleft])
  nlinarith only [h]

/-- All reduced fractions in the closed positive sector, as in (2.3).
The finite set is not an arbitrary selected subsequence of the sector. -/
def fareySector (N : ℕ) (l μ : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc 1 ⌊μ*(N:ℝ)⌋) ×ˢ (Finset.Icc 1 (N:ℤ))).filter
    (fun p => IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2)

theorem mem_fareySector_iff {N : ℕ} {l μ : ℝ} {p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ) :
    p ∈ fareySector N l μ ↔ 1 ≤ p.2 ∧ p.2 ≤ N ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2 := by
  classical
  simp only [fareySector,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_hm,hn⟩,hc,hlower,hu⟩
    exact ⟨hn.1,hn.2,hc,hlower,hu⟩
  · rintro ⟨hn,hnmax,hc,hlower,hu⟩
    have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hmR : (0:ℝ) < p.1 := (mul_pos hl hnR).trans_le hlower
    have hm : 1 ≤ p.1 := by
      have h : 0 < p.1 := by exact_mod_cast hmR
      omega
    have hmmax : p.1 ≤ ⌊μ*(N:ℝ)⌋ := Int.le_floor.mpr
      (hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnmax) hμ))
    exact ⟨⟨⟨hm,hmmax⟩,hn,hnmax⟩,hc,hlower,hu⟩

/-- The actual complete sector contains a determinant-one neighbor of a
maximal-denominator reference point as soon as it contains another point.
No Farey adjacency or divisor-one condition is assumed. -/
theorem fareySector_exists_unit_determinant
    {N : ℕ} {l μ : ℝ} {p₀ p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ)
    (hp₀ : p₀ ∈ fareySector N l μ) (hp : p ∈ fareySector N l μ)
    (hne : p ≠ p₀) (hmax : p.2 ≤ p₀.2) :
    ∃ r ∈ fareySector N l μ, |p₀.1*r.2-p₀.2*r.1|=1 := by
  obtain ⟨hn₀,hn₀N,hcop₀,hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ).mp hp₀
  obtain ⟨hn,_hnN,_hcop,hlp,hup⟩ := (mem_fareySector_iff hl hμ).mp hp
  have hn₀pos : 0 < p₀.2 := by omega
  have hn₀R : (0:ℝ) < p₀.2 := by exact_mod_cast hn₀pos
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hdetne : p₀.1*p.2 ≠ p₀.2*p.1 := by
    intro he
    apply hne
    apply maximal_denominator_determinant_injective hn₀pos hcop₀
      (show 1 ≤ p.2 ∧ p.2 ≤ p₀.2 from ⟨hn,hmax⟩)
      (show 1 ≤ p₀.2 ∧ p₀.2 ≤ p₀.2 from ⟨hn₀,le_rfl⟩)
    nlinarith only [he]
  rcases lt_or_gt_of_ne hdetne with hright | hleft
  · obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_right_neighbor hn₀pos hcop₀
    have hbR : (0:ℝ) ≤ b := by exact_mod_cast (show 0 ≤ b by omega)
    have hdetR : (p₀.1:ℝ)*b-(p₀.2:ℝ)*a = -1 := by exact_mod_cast hdet
    have hcloseR : (a:ℝ)*p.2 ≤ (p.1:ℝ)*b := by
      exact_mod_cast hclose p.1 p.2 hn hmax hright
    refine ⟨(a,b),(mem_fareySector_iff hl hμ).mpr ⟨hb,hbmax.trans hn₀N,hcop',?_,?_⟩,?_⟩
    · apply (mul_le_mul_iff_right₀ hn₀R).mp
      nlinarith only [mul_le_mul_of_nonneg_right hl₀ hbR,hdetR]
    · apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith only [mul_le_mul_of_nonneg_right hup hbR,hcloseR]
    · simp only [hdet,abs_neg,abs_one]
  · obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_left_neighbor hn₀pos hcop₀
    have hbR : (0:ℝ) ≤ b := by exact_mod_cast (show 0 ≤ b by omega)
    have hdetR : (p₀.1:ℝ)*b-(p₀.2:ℝ)*a = 1 := by exact_mod_cast hdet
    have hcloseR : (p.1:ℝ)*b ≤ (a:ℝ)*p.2 := by
      exact_mod_cast hclose p.1 p.2 hn hmax hleft
    refine ⟨(a,b),(mem_fareySector_iff hl hμ).mpr ⟨hb,hbmax.trans hn₀N,hcop',?_,?_⟩,?_⟩
    · apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith only [mul_le_mul_of_nonneg_right hlp hbR,hcloseR]
    · apply (mul_le_mul_iff_right₀ hn₀R).mp
      nlinarith only [mul_le_mul_of_nonneg_right hu₀ hbR,hdetR]
    · simp only [hdet,abs_one]

/-- Taking absolute values loses at most a factor two, apart from zero. -/
theorem card_le_two_mul_nonzero_abs_card_add_one (D : Finset ℤ) :
    D.card ≤ 2*((D.erase 0).image Int.natAbs).card+1 := by
  classical
  let P := (D.erase 0).image Int.natAbs
  have hsub : D.erase 0 ⊆ (P.image (fun n : ℕ => (n:ℤ))) ∪
      (P.image (fun n : ℕ => -(n:ℤ))) := by
    intro d hd
    have habs : d.natAbs ∈ P := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    rcases Int.natAbs_eq d with he | he
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.natAbs,habs,he.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.natAbs,habs,he.symm⟩)
  have hc : (D.erase 0).card ≤ 2*P.card := by
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ P.card+P.card := add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = _ := by omega
  have hD : D ⊆ insert 0 (D.erase 0) := by
    intro d hd
    by_cases he : d=0
    · simp only [he,Finset.mem_insert_self]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hd⟩)
  change D.card ≤ 2*P.card+1
  exact (Finset.card_le_card hD).trans ((Finset.card_insert_le _ _).trans (by omega))

/-- A dense determinant set containing a unit forces a small linear-form
coefficient near an integer. The one-dimensional dichotomy is consumed,
not restated as an assumption. -/
theorem small_error_integer_of_unit_determinant
    (D : Finset ℤ) {B ε α : ℝ}
    (hε : 0 ≤ ε) (hunit : ∃ d ∈ D, d.natAbs=1)
    (hsize : ∀ d ∈ D, (d.natAbs:ℝ) ≤ B*(D.card:ℝ))
    (hsmall : 36*B*ε < 1)
    (hnear : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*α-b| ≤ ε) :
    |α-(round α:ℤ)| ≤ 3*ε/(D.card:ℝ) := by
  classical
  let P := (D.erase 0).image Int.natAbs
  obtain ⟨d₁,hd₁,hone⟩ := hunit
  have hd₁ne : d₁ ≠ 0 := by intro he; simp only [he,Int.natAbs_zero] at hone; omega
  have h1 : 1 ∈ P := Finset.mem_image.mpr ⟨d₁,Finset.mem_erase.mpr ⟨hd₁ne,hd₁⟩,hone⟩
  have hPne : P.Nonempty := ⟨1,h1⟩
  have hDR : (0:ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨d₁,hd₁⟩)
  have hcard : (D.card:ℝ) ≤ 3*(P.card:ℝ) := by
    have h := card_le_two_mul_nonzero_abs_card_add_one D
    change D.card ≤ 2*P.card+1 at h
    have hp : 1 ≤ P.card := Finset.card_pos.mpr hPne
    exact_mod_cast (show D.card ≤ 3*P.card by omega)
  let L := P.max' hPne
  have hL : L ∈ P := Finset.max'_mem _ _
  have hLN : 0 < L := by have h := Finset.le_max' P 1 h1; omega
  have hPL : ∀ n ∈ P, 1 ≤ n ∧ n ≤ L := by
    intro n hn
    refine ⟨?_,Finset.le_max' P n hn⟩
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
    have hdne := (Finset.mem_erase.mp hd).1
    exact Nat.pos_of_ne_zero (by simpa using hdne)
  have hLsize : (L:ℝ) ≤ B*(D.card:ℝ) := by
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hL
    rw [← he]
    exact hsize d (Finset.mem_erase.mp hd).2
  have hPnear : ∀ n ∈ P, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ ε := by
    intro n hn
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨b,hb⟩ := hnear d (Finset.mem_erase.mp hd).2
    rcases Int.natAbs_eq d with he | he
    · refine ⟨b,?_⟩
      have heR : (d:ℝ) = (d.natAbs:ℝ) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
      rwa [← heR]
    · refine ⟨-b,?_⟩
      have heR : (d:ℝ) = -(d.natAbs:ℝ) := by
        simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℝ)) he
      have hid : (d.natAbs:ℝ)*α-((-b:ℤ):ℝ) = -((d:ℝ)*α-b) := by
        rw [heR,Int.cast_neg]
        ring
      rwa [hid,abs_neg]
  rcases linear_form_dichotomy P hLN hε hPL hPnear with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · have hbound := mul_le_mul_of_nonneg_left hLsize (by positivity : 0 ≤ 12*ε)
    have hstrict := mul_lt_mul_of_pos_right hsmall hDR
    nlinarith only [hc,hbound,hcard,hstrict]
  · have hq : q=1 := Nat.dvd_one.mp (hdvd 1 h1)
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have hr := round_le α a
    have hbound := mul_le_mul_of_nonneg_right hcard (abs_nonneg (α-(a:ℝ)))
    have hfinal : |α-(a:ℝ)| * (D.card:ℝ) ≤ 3*ε := by nlinarith only [hbound,ha]
    exact hr.trans ((le_div_iff₀ hDR).mpr hfinal)

theorem fareySector_determinant_bound
    {N : ℕ} {l μ : ℝ} {p₀ p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ)
    (hp₀ : p₀ ∈ fareySector N l μ) (hp : p ∈ fareySector N l μ) :
    |((p₀.1*p.2-p₀.2*p.1:ℤ):ℝ)| ≤ (μ-l)*(N:ℝ)^2 := by
  obtain ⟨hn₀,hn₀N,_hc₀,hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ).mp hp₀
  obtain ⟨hn,hnN,_hc,hlp,hup⟩ := (mem_fareySector_iff hl hμ).mp hp
  have hn₀R : (0:ℝ) < p₀.2 := by exact_mod_cast (show 0 < p₀.2 by omega)
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hn₀NR : (p₀.2:ℝ) ≤ N := by exact_mod_cast hn₀N
  have hnNR : (p.2:ℝ) ≤ N := by exact_mod_cast hnN
  have hlμ : l ≤ μ := (mul_le_mul_iff_left₀ hn₀R).mp (by nlinarith only [hl₀,hu₀])
  have hlocal : |(p₀.1:ℝ)*p.2-(p₀.2:ℝ)*p.1| ≤ (μ-l)*((p.2:ℝ)*p₀.2) := by
    apply abs_le.mpr
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl₀ hnR.le,
        mul_le_mul_of_nonneg_right hup hn₀R.le]
    · nlinarith only [mul_le_mul_of_nonneg_right hu₀ hnR.le,
        mul_le_mul_of_nonneg_right hlp hn₀R.le]
  have hprod : (p.2:ℝ)*p₀.2 ≤ (N:ℝ)^2 := by
    nlinarith only [mul_le_mul hnNR hn₀NR hn₀R.le (Nat.cast_nonneg N)]
  push_cast
  exact hlocal.trans (mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hlμ))

/-- The two quantitative conclusions of Huxley (1993), Lemma 2.5,
for the actual complete sector (2.3). The printed phrase "both integers"
is not asserted: positive approximation error implies closeness, not
exact integrality. The displayed constants and hypotheses are retained. -/
theorem fareySector_small_error_bounds
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  have hμ0 : 0 ≤ μ := by linarith
  have hB0 : 0 < B := by linarith
  have hR2 : 2 ≤ S.card := by
    exact_mod_cast (le_trans (le_max_right ((μ-l)*(N:ℝ)^2/B) 2) hR)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hSne
  obtain ⟨p,hp,hne⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hrunit⟩ := fareySector_exists_unit_determinant hl hμ0 hp₀ hp hne (hmax p hp)
  obtain ⟨hn₀,hn₀N,hcop₀,_hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ0).mp hp₀
  have hn₀pos : 0 < p₀.2 := by omega
  let f : ℤ × ℤ → ℤ := fun t => p₀.1*t.2-p₀.2*t.1
  let D := S.image f
  have hinj : Set.InjOn f S := by
    intro t ht u hu he
    exact maximal_denominator_determinant_injective hn₀pos hcop₀
      ⟨((mem_fareySector_iff hl hμ0).mp ht).1,hmax t ht⟩
      ⟨((mem_fareySector_iff hl hμ0).mp hu).1,hmax u hu⟩ he
  have hDcard : D.card=S.card := Finset.card_image_of_injOn hinj
  have hunit : ∃ d ∈ D, d.natAbs=1 := by
    refine ⟨f r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_⟩
    have h : |f r|=1 := hrunit
    exact Int.ofNat_inj.mp ((Int.natCast_natAbs (f r)).trans h)
  have hsize : ∀ d ∈ D, (d.natAbs:ℝ) ≤ B*(D.card:ℝ) := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    have hb := fareySector_determinant_bound hl hμ0 hp₀ ht
    have hw : (μ-l)*(N:ℝ)^2 ≤ B*(S.card:ℝ) := by
      have h := le_trans (le_max_left ((μ-l)*(N:ℝ)^2/B) 2) hR
      have hd := (div_le_iff₀ hB0).mp h
      nlinarith only [hd]
    rw [hDcard,Nat.cast_natAbs,Int.cast_abs]
    exact hb.trans hw
  have hNleM : (N:ℝ) ≤ μ*(N:ℝ) := by nlinarith only [mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg N)]
  have hbase : 96*B*(μ*(N:ℝ))*δ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 96*B)).mp hsmall
    nlinarith only [h]
  have hsmallα : 36*B*(2*(N:ℝ)*δ) < 1 := by
    have h := mul_le_mul_of_nonneg_left hNleM (by positivity : 0 ≤ B*δ)
    nlinarith only [h,hbase]
  have hsmallβ : 36*B*(2*(μ*(N:ℝ))*δ) < 1 := by nlinarith only [hbase]
  obtain ⟨b₀,hb₀⟩ := hnear p₀ hp₀
  have hnearα : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*α-b| ≤ 2*(N:ℝ)*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    obtain ⟨hn,hnN,_hc,_hl,_hu⟩ := (mem_fareySector_iff hl hμ0).mp ht
    have htn : |(t.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ t.2 by omega))]
      exact_mod_cast hnN
    have htn₀ : |(p₀.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast hn₀pos.le)]
      exact_mod_cast hn₀N
    exact ⟨t.2*b₀-p₀.2*b,determinant_alpha_near p₀.1 p₀.2 t.1 t.2 b₀ b htn htn₀ hb₀ hb⟩
  have hnum : ∀ t ∈ S, |(t.1:ℝ)| ≤ μ*(N:ℝ) := by
    intro t ht
    obtain ⟨hn,hnN,_hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ0).mp ht
    have hnR : (0:ℝ) ≤ t.2 := by exact_mod_cast (show 0 ≤ t.2 by omega)
    have htpos : (0:ℝ) ≤ t.1 := (mul_nonneg hl.le hnR).trans hlower
    rw [abs_of_nonneg htpos]
    exact hupper.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
  have hnearβ : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*β-b| ≤ 2*(μ*(N:ℝ))*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    exact ⟨p₀.1*b-t.1*b₀,determinant_beta_near p₀.1 p₀.2 t.1 t.2 b₀ b
      (hnum t ht) (hnum p₀ hp₀) hb₀ hb⟩
  have ha := small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallα hnearα
  have hb := small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallβ hnearβ
  rw [hDcard] at ha hb
  constructor
  · apply ha.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (Nat.cast_nonneg N) hδ]
  · apply hb.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (mul_nonneg hμ0 (Nat.cast_nonneg N)) hδ]

theorem fareySector_one_one_two : fareySector 1 1 2 = {(1,1),(2,1)} := by
  classical
  ext p
  rw [mem_fareySector_iff (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨hn,hnmax,_hc,hl,hu⟩
    have hn1 : p.2=1 := by norm_num at hnmax; omega
    rw [hn1] at hl hu
    norm_num at hl hu
    have hm1 : (1:ℤ) ≤ p.1 := by exact_mod_cast hl
    have hm2 : p.1 ≤ (2:ℤ) := by exact_mod_cast hu
    have hm : p.1=1 ∨ p.1=2 := by omega
    rcases hm with hm | hm <;> simp [Prod.ext_iff,hm,hn1]
  · intro hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num

/-- Counterexample to the literal words "both integers" on printed page 6.
Here N=l=B=1, mu=2, delta=1/1000, alpha=1/2000 and beta=0.
All sector-count and approximation hypotheses hold, but alpha is not an
integer. This does not contradict either displayed quantitative bound. -/
theorem printed_exact_integrality_counterexample :
    max (((2:ℝ)-1)*1^2/1) 2 ≤ ((fareySector 1 1 2).card:ℝ) ∧
    (2:ℝ)*1*(1/1000) ≤ 1/(96*1) ∧
    (∀ p ∈ fareySector 1 1 2,
      ∃ b : ℤ, |(p.1:ℝ)*(1/2000)+(p.2:ℝ)*0-b| ≤ 1/1000) ∧
    ¬∃ k : ℤ, (1/2000:ℝ)=k := by
  rw [fareySector_one_one_two]
  refine ⟨by norm_num,by norm_num,?_,?_⟩
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> exact ⟨0,by norm_num⟩
  · rintro ⟨k,hk⟩
    have hkpos : (0:ℝ) < k := by rw [← hk]; norm_num
    have hklt : (k:ℝ) < 1 := by rw [← hk]; norm_num
    have h0 : 0 < k := by exact_mod_cast hkpos
    have h1 : k < 1 := by exact_mod_cast hklt
    omega


end TaoTrudgianYang2025.HuxleyLinearForm
