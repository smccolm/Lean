import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import TaoTrudgianYang2025.IntegerIntervalCount
import TaoTrudgianYang2025.FiniteSmoothThirdDerivative
import TaoTrudgianYang2025.ReciprocalSecondDerivativeBounds
import TaoTrudgianYang2025.HeathBrownPhysicalPhase
import TaoTrudgianYang2025.IntegerFourierTails

/-!
# Huxley's linear forms, rational phase and long-block analytic core

Huxley, *Exponential Sums and the Riemann Zeta Function IV* (1993),
Section 2: the complete Lemma 2.1 dichotomy and the two displayed bounds
of Lemma 2.5. The Farey neighbor is constructed from Bezout coefficients;
no rational approximation, counting estimate or adjacency is assumed.

The alternate bounded-density-constant Lemma 2.6 dichotomy is also proved:
the size branch has constant `1536*B`, alpha has `8`, and beta has `20*B`
rather than the printed universal `161`. Its exact integer-label consumer
is proved for the actual complete sector. This is not a proof of the sharper
printed constants or a family fifth-moment bound.

The HuxleyRationalPhase namespace implements the literal phase (4.9),
its sector Taylor consumer and the eight-point long-block analytic core.
The determinant saving `1024*K*Kμ*R^4/(L^3*N^2)` is derived from (6.1),
actual G-coordinate spacing, dyadic denominator bounds and the phase scale.
The middle-interval Third-Condition core and its actual model-phase
coefficient perturbation are proved. Integer centres are constructed by
rounding actual curvature preimages, giving the discrete-to-continuous
error O(1+n^2/M). The Section 5 cancellation retains the base-curvature
correction, absorbs its error using T*N*R^2=M^3 and |n|^3<=M*R^2,
and proves (5.4)--(5.6) for actual paired rounded physical phases.
Its consumer derives exact sector integer labels from the actual Fourth
Condition and the explicit geometric/Third-Condition inputs. Complete
sector/eight-point geometry, enlarged-domain entry, mixed-parameter and
scalar/family counts remain open.

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


/-- Exact numerator count on one genuine denominator fiber of (2.3).
This is an elementary upper bound, not the missing Farey density lower bound. -/
theorem denominator_fiber_card
    {N : ℕ} {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ)
    {n : ℤ} (hn : 0 ≤ n) :
    (((fareySector N l μ).filter (fun p => p.2=n)).card:ℝ) ≤ (μ-l)*(n:ℝ)+1 := by
  classical
  let T := (fareySector N l μ).filter (fun p => p.2=n)
  let A := T.image Prod.fst
  have hcard : A.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm))
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  have hnR : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hrad : 0 ≤ (μ-l)*(n:ℝ)/2 := by positivity
  have hnear : ∀ m ∈ A, |(m:ℝ)-(l+μ)*(n:ℝ)/2| ≤ (μ-l)*(n:ℝ)/2 := by
    intro m hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hpS,hpn⟩ := Finset.mem_filter.mp hp
    obtain ⟨_hpn,_hpN,_hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ).mp hpS
    rw [hpn] at hlower hupper
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have h := integer_card_le_of_abs_sub_le A hrad hnear
  rw [hcard] at h
  change (T.card:ℝ) ≤ _
  linarith


/-- Summing the actual denominator fibers gives the triangular, rather
than rectangular, sector upper bound used in the large-sector branch. -/
theorem fareySector_card_le (N : ℕ) {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) :
    ((fareySector N l μ).card:ℝ) ≤ (μ-l)*(N:ℝ)*((N:ℝ)+1)/2+(N:ℝ) := by
  classical
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  induction N with
  | zero =>
    have hS : fareySector 0 l μ=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := (mem_fareySector_iff hl hμ).mp hp
      norm_num at h
      omega
    simp [hS]
  | succ N ih =>
    let T := (fareySector (N+1) l μ).filter (fun p => p.2=((N+1:ℕ):ℤ))
    have hsub : fareySector (N+1) l μ ⊆ fareySector N l μ ∪ T := by
      intro p hp
      obtain ⟨hn,hnN,hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ).mp hp
      by_cases hnold : p.2 ≤ (N:ℤ)
      · exact Finset.mem_union_left _ ((mem_fareySector_iff hl hμ).mpr
          ⟨hn,hnold,hc,hlower,hupper⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hp,?_⟩
        push_cast at hnN ⊢
        omega
    have hc : ((fareySector (N+1) l μ).card:ℝ) ≤
        (fareySector N l μ).card+(T.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hf : (T.card:ℝ) ≤ (μ-l)*((N:ℝ)+1)+1 := by
      simpa only [T,Nat.cast_add,Nat.cast_one,Int.cast_natCast,Int.cast_add,Int.cast_one] using
        denominator_fiber_card (N := N+1) hl hlμ (n := (N+1:ℕ)) (by positivity)
    push_cast at hc ⊢
    nlinarith only [ih,hc,hf]

theorem large_sector_width
    {N : ℕ} {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) (hN : 4 ≤ N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    3*((fareySector N l μ).card:ℝ) ≤ 2*(μ-l)*(N:ℝ)^2 := by
  have hc := fareySector_card_le N hl hlμ
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hmul : 0 ≤ (μ-l)*(N:ℝ)*((N:ℝ)-4) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlμ) (Nat.cast_nonneg N)) (sub_nonneg.mpr hNR)
  nlinarith only [hc,hR,hmul]

theorem prime_coprime_consecutive {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (a : ℕ) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ a+2 ∧ p.Coprime m ∧ p.Coprime (m+1) := by
  have h1 : ¬p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  by_cases ha : p ∣ a
  · refine ⟨a+1,by omega,by omega,hp.coprime_iff_not_dvd.mpr ?_,hp.coprime_iff_not_dvd.mpr ?_⟩
    · intro h; exact h1 ((Nat.dvd_add_right ha).mp h)
    · intro h
      exact h2 ((Nat.dvd_add_right ha).mp (by simpa only [Nat.add_assoc] using h))
  · by_cases ha1 : p ∣ a+1
    · refine ⟨a+2,by omega,by omega,hp.coprime_iff_not_dvd.mpr ?_,hp.coprime_iff_not_dvd.mpr ?_⟩
      · intro h
        exact h1 ((Nat.dvd_add_right ha1).mp (by convert h using 1))
      · intro h
        exact h2 ((Nat.dvd_add_right ha1).mp (by convert h using 1))
    · exact ⟨a,le_rfl,by omega,hp.coprime_iff_not_dvd.mpr ha,hp.coprime_iff_not_dvd.mpr ha1⟩


/-- A wide complete sector contains two primitive points with the same
denominator and consecutive numerators. Bertrand's postulate supplies a
prime denominator; no adjacency hypothesis is supplied by the caller. -/
theorem large_sector_consecutive_numerators {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 4 ≤ N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ := by
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  obtain ⟨p,hp,hpl,hpu⟩ := Nat.exists_prime_lt_and_le_two_mul (N/2) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hpN : p ≤ N := by omega
  have hNp : (N:ℝ) ≤ 2*(p:ℝ) := by exact_mod_cast (show N ≤ 2*p by omega)
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw := large_sector_width hl hlμ hN hR
  have hwN : 24 ≤ (μ-l)*(N:ℝ) := by
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hw,hR]
  have hwp : 4 ≤ (μ-l)*(p:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNp (sub_nonneg.mpr hlμ)
    nlinarith only [hwN,h]
  let a := ⌊l*(p:ℝ)⌋₊+1
  obtain ⟨m,ham,hma,hcm,hcm1⟩ := prime_coprime_consecutive hp hp3 a
  have hlow : l*(p:ℝ) ≤ (m:ℝ) := by
    have hf := Nat.lt_floor_add_one (l*(p:ℝ))
    have hm : (⌊l*(p:ℝ)⌋₊:ℝ)+1 ≤ m := by exact_mod_cast ham
    linarith
  have hupp : (m:ℝ)+1 ≤ μ*(p:ℝ) := by
    have hf := Nat.floor_le (mul_nonneg hl.le (Nat.cast_nonneg p))
    have hm : (m:ℝ) ≤ (⌊l*(p:ℝ)⌋₊:ℝ)+3 := by exact_mod_cast hma
    linarith
  have hm0 : (m:ℝ) ≤ (m:ℝ)+1 := by linarith
  refine ⟨m,p,?_,?_⟩
  · apply (mem_fareySector_iff hl hμ).mpr
    refine ⟨by dsimp; exact_mod_cast hp.one_lt.le,by dsimp; exact_mod_cast hpN,hcm.symm.isCoprime,?_,?_⟩
    · simpa only [Int.cast_natCast] using hlow
    · simpa only [Int.cast_natCast] using hm0.trans hupp
  · apply (mem_fareySector_iff hl hμ).mpr
    refine ⟨by dsimp; exact_mod_cast hp.one_lt.le,by dsimp; exact_mod_cast hpN,?_,?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using hcm1.symm.isCoprime
    · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hlow.trans hm0
    · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hupp


/-- The small denominator orders are handled by actual denominator-one
points, so the large-sector unit difference has no hidden `N ≥ 4` restriction. -/
theorem sector_consecutive_numerators {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ := by
  by_cases hN4 : 4 ≤ N
  · exact large_sector_consecutive_numerators hl hlμ hN4 hR
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hN3 : (N:ℝ) ≤ 3 := by exact_mod_cast (show N ≤ 3 by omega)
  have hupper := fareySector_card_le N hl hlμ
  have hw : 4 ≤ μ-l := by
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hlμ) hNR.le) (sub_nonneg.mpr hN3)
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hupper,hR,hh]
  let m : ℤ := ⌊l⌋+1
  have hlow : l ≤ (m:ℝ) := by
    have hh := Int.lt_floor_add_one l
    simpa only [m,Int.cast_add,Int.cast_one] using hh.le
  have hupp : (m:ℝ)+1 ≤ μ := by
    have hh := Int.floor_le l
    dsimp [m]
    push_cast
    linarith
  have hN1 : (1:ℤ) ≤ N := by exact_mod_cast hN
  have hμ0 := hl.le.trans hlμ
  refine ⟨m,1,?_,?_⟩
  · apply (mem_fareySector_iff hl hμ0).mpr
    refine ⟨le_rfl,hN1,isCoprime_one_right,?_,?_⟩
    · simpa only [Int.cast_one,mul_one] using hlow
    · simp only [Int.cast_one,mul_one]; linarith
  · apply (mem_fareySector_iff hl hμ0).mpr
    refine ⟨le_rfl,hN1,isCoprime_one_right,?_,?_⟩
    · simp only [Int.cast_one,Int.cast_add,mul_one]; linarith
    · simpa only [Int.cast_one,Int.cast_add,mul_one] using hupp


/-- The large-sector alpha estimate uses all signs of one actual fiber's
differences, together with a constructed unit difference. The factor two
from subtraction is retained explicitly. -/
theorem large_sector_alpha_bound {N : ℕ} {l μ α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) (hδ : 0 ≤ δ)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 96*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  have hμ0 : 0 ≤ μ := by linarith
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hSR : (0:ℝ) < S.card := by dsimp [S]; nlinarith only [hR,hNR]
  have hmaps : ∀ p ∈ S, p.2 ∈ Finset.Icc (1:ℤ) N := by
    intro p hp
    have h := (mem_fareySector_iff hl hμ0).mp hp
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩
  have hI : (Finset.Icc (1:ℤ) N).card=N := by simp
  have hIne : (Finset.Icc (1:ℤ) N).Nonempty := by
    exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by exact_mod_cast (show 1 ≤ N by omega)⟩⟩
  obtain ⟨n,_hn,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps hIne (b := (S.card:ℝ)/(N:ℝ)) (by rw [hI,nsmul_eq_mul]; exact le_of_eq (mul_div_cancel₀ _ hNR.ne'))
  let T := S.filter (fun p => p.2=n)
  change (S.card:ℝ)/(N:ℝ) ≤ (T.card:ℝ) at hcount
  have hTne : T.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((div_pos hSR hNR).trans_le hcount))
  obtain ⟨p₀,hp₀⟩ := hTne
  let D := T.image (fun p => p.1-p₀.1)
  let P := insert 1 ((D.erase 0).image Int.natAbs)
  have hDcard : D.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    apply Prod.ext (by dsimp at he; omega)
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  have hTP : (T.card:ℝ) ≤ 2*(P.card:ℝ)+1 := by
    have hc := card_le_two_mul_nonzero_abs_card_add_one D
    have hsub : (D.erase 0).image Int.natAbs ⊆ P := Finset.subset_insert _ _
    have hh := Finset.card_le_card hsub
    rw [hDcard] at hc
    exact_mod_cast (show T.card ≤ 2*P.card+1 by omega)
  have hcard : (S.card:ℝ) ≤ 4*(N:ℝ)*(P.card:ℝ) := by
    have hc := (div_le_iff₀ hNR).mp hcount
    have ht := mul_le_mul_of_nonneg_left hTP hNR.le
    change 16*(N:ℝ) ≤ (S.card:ℝ) at hR
    nlinarith only [hc,ht,hR]
  have hPne : P.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let L := P.max' hPne
  have hL : L ∈ P := Finset.max'_mem _ _
  have hLpos : 0 < L := by have hh := Finset.le_max' P 1 (Finset.mem_insert_self _ _); omega
  have hnum (p : ℤ × ℤ) (hp : p ∈ S) : 0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ μ*(N:ℝ) := by
    obtain ⟨hn,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
    have hnR : (0:ℝ) ≤ p.2 := by exact_mod_cast (show 0 ≤ p.2 by omega)
    exact ⟨(mul_nonneg hl.le hnR).trans hlo,
      hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)⟩
  have hPsize : ∀ k ∈ P, 1 ≤ k ∧ (k:ℝ) ≤ μ*(N:ℝ) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · refine ⟨le_rfl,?_⟩
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      simpa only [one_mul,Nat.cast_one] using mul_le_mul hμ hN1 (by norm_num : (0:ℝ) ≤ 1) hμ0
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hd0,hd⟩ := Finset.mem_erase.mp hd
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
      refine ⟨Nat.pos_of_ne_zero (by simpa using hd0),?_⟩
      rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
      have hpnum := hnum p (Finset.mem_filter.mp hp).1
      have hp₀num := hnum p₀ (Finset.mem_filter.mp hp₀).1
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hdiff (p r : ℤ × ℤ) (hp : p ∈ S) (hr : r ∈ S) (he : p.2=r.2) :
      ∃ b : ℤ, |((p.1-r.1:ℤ):ℝ)*α-b| ≤ 2*δ := by
    obtain ⟨bp,hbp⟩ := hnear p hp
    obtain ⟨br,hbr⟩ := hnear r hr
    refine ⟨bp-br,?_⟩
    have hid : ((p.1-r.1:ℤ):ℝ)*α-((bp-br:ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-bp)-((r.1:ℝ)*α+(r.2:ℝ)*β-br) := by
      rw [he]; push_cast; ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hPnear : ∀ k ∈ P, ∃ b : ℤ, |(k:ℝ)*α-b| ≤ 2*δ := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · obtain ⟨m,n,hm,hm1⟩ := sector_consecutive_numerators hl hlμ hN hR
      simpa only [Prod.fst,add_sub_cancel_left,Int.cast_one,Nat.cast_one,one_mul] using
        hdiff (m+1,n) (m,n) hm1 hm rfl
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hd).2
      obtain ⟨b,hb⟩ := hdiff p p₀ (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp₀).1
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp₀).2.symm)
      rcases Int.natAbs_eq (p.1-p₀.1) with he | he
      · refine ⟨b,?_⟩
        have heR : ((p.1-p₀.1:ℤ):ℝ) = ((p.1-p₀.1).natAbs:ℝ) := by
          simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
        rwa [← heR]
      · refine ⟨-b,?_⟩
        have heR : ((p.1-p₀.1:ℤ):ℝ) = -((p.1-p₀.1).natAbs:ℝ) := by
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℝ)) he
        have hid : ((p.1-p₀.1).natAbs:ℝ)*α-((-b:ℤ):ℝ) = -(((p.1-p₀.1:ℤ):ℝ)*α-b) := by
          rw [heR,Int.cast_neg]; ring
        rwa [hid,abs_neg]
  rcases linear_form_dichotomy P hLpos (by positivity)
    (fun k hk => ⟨(hPsize k hk).1,Finset.le_max' P k hk⟩) hPnear with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · left
    have hm := mul_le_mul_of_nonneg_left (hPsize L hL).2 (show 0 ≤ 24*δ by positivity)
    have hc' : (P.card:ℝ) ≤ 24*δ*(μ*(N:ℝ)) := by nlinarith only [hc,hm]
    have ht := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 4*(N:ℝ) by positivity)
    -- The symmetric-difference count costs a factor two: retain it visibly.
    nlinarith only [hcard,ht]
  · right
    have hq : q=1 := Nat.dvd_one.mp (hdvd 1 (Finset.mem_insert_self _ _))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have ht := mul_le_mul_of_nonneg_left hcard (abs_nonneg (α-(a:ℝ)))
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*(N:ℝ) by positivity)
    apply (round_le α a).trans
    apply (le_div_iff₀ hSR).mpr
    nlinarith only [ht,hh]


theorem sector_denominator_card_lower {N : ℕ} {l μ B : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) :
    (N:ℝ) ≤ (B+1)*((fareySector N l μ).image Prod.snd).card := by
  classical
  let S := fareySector N l μ
  let E := S.image Prod.snd
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hSR : (0:ℝ) < S.card := hNR.trans_le hR
  have hwidth : (μ-l)*(N:ℝ)+1 ≤ (B+1)*(S.card:ℝ)/(N:ℝ) := by
    apply (le_div_iff₀ hNR).mpr
    nlinarith only [hdensity,hR]
  have hfiber : ∀ n ∈ E, ((S.filter (fun p => p.2=n)).card:ℝ) ≤
      (B+1)*(S.card:ℝ)/(N:ℝ) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hs := (mem_fareySector_iff hl (hl.le.trans hlμ)).mp hp
    apply (denominator_fiber_card hl hlμ (by omega : 0 ≤ p.2)).trans
    apply le_trans _ hwidth
    have hnN : (p.2:ℝ) ≤ N := by exact_mod_cast hs.2.1
    nlinarith only [mul_le_mul_of_nonneg_left hnN (sub_nonneg.mpr hlμ)]
  have heq : (S.card:ℝ) = ∑ n ∈ E, ((S.filter (fun p => p.2=n)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.snd hp)
  have hsum := Finset.sum_le_sum hfiber
  rw [← heq,Finset.sum_const,nsmul_eq_mul] at hsum
  have hprod := (le_div_iff₀ hNR).mp (show (S.card:ℝ) ≤
      ((E.card:ℝ)*((B+1)*(S.card:ℝ)))/(N:ℝ) by simpa only [mul_div_assoc] using hsum)
  apply (mul_le_mul_iff_right₀ hSR).mp
  nlinarith only [hprod]

theorem sector_denominator_common_divisor {N q : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hR : 2 ≤ (fareySector N l μ).card)
    (hdvd : ∀ p ∈ fareySector N l μ, q ∣ p.2.natAbs) : q=1 := by
  classical
  let S := fareySector N l μ
  change 2 ≤ S.card at hR
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hne
  obtain ⟨p,hp,hneq⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hunit⟩ := fareySector_exists_unit_determinant hl hμ hp₀ hp hneq (hmax p hp)
  have hd₀ : (q:ℤ) ∣ p₀.2 := Int.natCast_dvd.mpr (hdvd p₀ hp₀)
  have hdr : (q:ℤ) ∣ r.2 := Int.natCast_dvd.mpr (hdvd r hr)
  have hd : (q:ℤ) ∣ p₀.1*r.2-p₀.2*r.1 := dvd_sub (dvd_mul_of_dvd_right hdr _) (dvd_mul_of_dvd_left hd₀ _)
  have hh : q ∣ (p₀.1*r.2-p₀.2*r.1).natAbs := Int.natCast_dvd.mp hd
  have hu : (p₀.1*r.2-p₀.2*r.1).natAbs=1 :=
    Int.ofNat_inj.mp ((Int.natCast_natAbs _).trans hunit)
  rw [hu] at hh
  exact Nat.dvd_one.mp hh


theorem sector_card_le_twice_rectangle {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hN : 0 < N) :
    ((fareySector N l μ).card:ℝ) ≤ 2*μ*(N:ℝ)^2 := by
  have hu := fareySector_card_le N hl hlμ
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hμ0 : 0 ≤ μ := by linarith
  have ha := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hμ0 hN0)
  have hb := mul_le_mul_of_nonneg_left hN1 hN0
  have hc := mul_le_mul_of_nonneg_right hμ (sq_nonneg (N:ℝ))
  have hd : 0 ≤ l*(N:ℝ)*((N:ℝ)+1) := by positivity
  nlinarith only [hu,ha,hb,hc,hd]

/-- Beta's large-sector branch, with its dependence on the actual supplied
density constant retained. No independent denominator count is assumed. -/
theorem sector_beta_bound {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hB : 1 ≤ B) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card) (hR2 : 2 ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) (hδ : 0 ≤ δ)
    (hα : |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 240*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  let E := S.image Prod.snd
  let D := E.image Int.natAbs
  let ε := 10*δ*μ*(N:ℝ)^2/(S.card:ℝ)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hSR : (0:ℝ) < S.card := hNR.trans_le hR
  have hμ0 : 0 ≤ μ := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hden : ∀ n ∈ E, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have h := (mem_fareySector_iff hl hμ0).mp hp
    exact ⟨h.1,h.2.1⟩
  have hDcard : D.card=E.card := Finset.card_image_of_injOn (by
    intro n hn m hm he
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (by have hh := hden n hn; omega)
      (by have hh := hden m hm; omega)).mp he)
  have hdens := sector_denominator_card_lower hl hlμ hN hR hdensity
  change (N:ℝ) ≤ (B+1)*(E.card:ℝ) at hdens
  rw [← hDcard] at hdens
  have hDsize : ∀ n ∈ D, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    have hh := hden m hm
    have he : (m.natAbs:ℤ)=m := (Int.natCast_natAbs m).trans (abs_of_nonneg (by omega))
    constructor <;> exact_mod_cast (show _ by omega)
  have hDnear : ∀ n ∈ D, ∃ b : ℤ, |(n:ℝ)*β-b| ≤ ε := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hn₁,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
    have hn0 : (0:ℝ) ≤ p.2 := by exact_mod_cast (show 0 ≤ p.2 by omega)
    have hm0 : (0:ℝ) ≤ p.1 := (mul_nonneg hl.le hn0).trans hlo
    have hmM : (p.1:ℝ) ≤ μ*(N:ℝ) :=
      hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
    obtain ⟨b,hb⟩ := hnear p hp
    refine ⟨b-p.1*(round α),?_⟩
    have he : (p.2.natAbs:ℝ)=(p.2:ℝ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg hn0]
    rw [he]
    have hid : (p.2:ℝ)*β-((b-p.1*(round α):ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-b)-(p.1:ℝ)*(α-(round α:ℤ)) := by push_cast; ring
    rw [hid]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hm0]
    have ha := mul_le_mul hmM hα (abs_nonneg _) (mul_nonneg hμ0 hNR.le)
    have hs := mul_le_mul_of_nonneg_left (sector_card_le_twice_rectangle hl hμ hlμ hN) hδ
    have hαR := (le_div_iff₀ hSR).mp (show (p.1:ℝ)*|α-(round α:ℤ)| ≤
        (μ*(N:ℝ)*(8*(N:ℝ)*δ))/(S.card:ℝ) by simpa only [mul_div_assoc] using ha)
    apply (le_div_iff₀ hSR).mpr
    have hbR := mul_le_mul_of_nonneg_right hb hSR.le
    nlinarith only [hs,hαR,hbR]
  rcases linear_form_dichotomy D hN (show 0 ≤ ε by dsimp [ε]; positivity)
    hDsize hDnear with hc | ⟨q,_hq,_hqN,hdvd,a,ha⟩
  · left
    have hcR : (D.card:ℝ)*(S.card:ℝ) ≤ 120*δ*μ*(N:ℝ)^3 := by
      have h := (le_div_iff₀ hSR).mp (show (D.card:ℝ) ≤
          (120*δ*μ*(N:ℝ)^3)/(S.card:ℝ) by convert hc using 1; dsimp [ε]; ring)
      exact h
    have hdR := mul_le_mul_of_nonneg_right hdens hSR.le
    have hcB := mul_le_mul_of_nonneg_left hcR (show 0 ≤ B+1 by linarith)
    have hB1 : B+1 ≤ 2*B := by linarith
    have hBB := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ 120*δ*μ*(N:ℝ)^3 by positivity)
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hdR,hcB,hBB]
  · right
    have hq : q=1 := sector_denominator_common_divisor hl hμ0 hR2 (by
      intro p hp
      exact hdvd p.2.natAbs (Finset.mem_image_of_mem Int.natAbs (Finset.mem_image_of_mem Prod.snd hp)))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have haR := (le_div_iff₀ hSR).mp ha
    have hdA := mul_le_mul_of_nonneg_left hdens (abs_nonneg (β-(a:ℝ)))
    have hdAR := mul_le_mul_of_nonneg_right hdA hSR.le
    have haB := mul_le_mul_of_nonneg_left haR (show 0 ≤ B+1 by linarith)
    have hBB := mul_le_mul_of_nonneg_right (show B+1 ≤ 2*B by linarith)
      (show 0 ≤ 10*δ*μ*(N:ℝ)^2 by positivity)
    apply (round_le β a).trans
    apply (le_div_iff₀ hSR).mpr
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hdAR,haB,hBB]


/-- Alternate complete-sector form of Huxley's Lemma 2.6. The size branch
and alpha constant are unchanged; beta has the explicit constant `20*B`,
not the printed `161`. This supplies the bounded-density-constant use in
Section 5 without claiming the sharper universal printed beta constant. -/
theorem fareySector_bounded_density_dichotomy
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card) := by
  have hB0 : 0 < B := by linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hR2R : (2:ℝ) ≤ (fareySector N l μ).card := (le_max_right _ _).trans hR
  have hR2 : 2 ≤ (fareySector N l μ).card := by exact_mod_cast hR2R
  have hSne : (fareySector N l μ).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp⟩ := hSne
  obtain ⟨hn,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
  have hN : 0 < N := by omega
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hlμ : l ≤ μ := (mul_le_mul_iff_left₀ hnR).mp (hlo.trans hu)
  have hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card := by
    have hh := (div_le_iff₀ hB0).mp ((le_max_left _ _).trans hR)
    nlinarith only [hh]
  by_cases hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B)
  · obtain ⟨ha,hb⟩ := fareySector_small_error_bounds hl hμ hB hδ hR hsmall hnear
    refine Or.inr ⟨ha,hb.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ (μ*(N:ℝ))*δ by positivity)
    nlinarith only [hh,mul_nonneg (mul_nonneg hμ0 (Nat.cast_nonneg N)) hδ]
  by_cases hsize : ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ)
  · exact Or.inl hsize
  have hbase : 1 < 96*B*((μ*(N:ℝ))*δ) := by
    have hh := (div_lt_iff₀ (show 0 < 96*B by positivity)).mp (lt_of_not_ge hsmall)
    nlinarith only [hh]
  have hlarge : 16*(N:ℝ) ≤ (fareySector N l μ).card := by
    have hh := mul_le_mul_of_nonneg_right hbase.le (show 0 ≤ 16*(N:ℝ) by positivity)
    nlinarith only [hh,lt_of_not_ge hsize]
  have hRgeN : (N:ℝ) ≤ (fareySector N l μ).card := by
    nlinarith only [hlarge,(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hprod : 0 ≤ δ*(μ*(N:ℝ))*(N:ℝ) := by positivity
  rcases large_sector_alpha_bound hl hμ hlμ hN hlarge hδ hnear with hbad | ha
  · exact (hsize (by nlinarith only [hbad,mul_le_mul_of_nonneg_right hB hprod,hprod])).elim
  · rcases sector_beta_bound hl hμ hlμ hB hN hRgeN hR2 hdensity hδ ha hnear with hbad | hb
    · have hh : 0 ≤ B*(δ*(μ*(N:ℝ))*(N:ℝ)) := mul_nonneg hB0.le hprod
      exact (hsize (by nlinarith only [hbad,hh])).elim
    · exact Or.inr ⟨ha,hb⟩


/-- Exact integer-label rigidity, the consequence needed after (5.11)--(5.12).
The real coefficients need not be integers: every integer within `δ` of
the original linear form equals the linear form in their nearest integers. -/
theorem fareySector_integer_labels
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hlarge : 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) < (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p ∈ fareySector N l μ, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) := by
  have hbnd := fareySector_bounded_density_dichotomy hl hμ hB hδ hR hnear
  obtain ⟨ha,hb⟩ := hbnd.resolve_left (not_le.mpr hlarge)
  intro p hp b hpnear
  have hμ0 : 0 ≤ μ := by linarith
  obtain ⟨hn,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
  have hN : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hlμ : l ≤ μ := (mul_le_mul_iff_left₀ hnR).mp (hlo.trans hu)
  have hp0 : (0:ℝ) ≤ p.1 := (mul_nonneg hl.le hnR.le).trans hlo
  have hpM : (p.1:ℝ) ≤ μ*(N:ℝ) :=
    hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
  let R : ℝ := (fareySector N l μ).card
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) ((le_max_right _ _).trans hR)
  have hrect : R ≤ 2*μ*(N:ℝ)^2 := sector_card_le_twice_rectangle hl hμ hlμ hN
  have hδR := mul_le_mul_of_nonneg_left hrect hδ
  have hprod : 0 ≤ δ*μ*(N:ℝ)^2 := by positivity
  have hBprod := mul_le_mul_of_nonneg_right hB hprod
  have herrR : (δ+(8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R)*R < R := by
    have hcancel : (δ+(8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R)*R =
        δ*R+(8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ := by field_simp
    rw [hcancel]
    change 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) < R at hlarge
    nlinarith only [hlarge,hδR,hBprod,hprod]
  have herr : δ+(8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R < 1 :=
    (mul_lt_mul_iff_left₀ hR0).mp (by simpa only [one_mul] using herrR)
  let z : ℤ := b-(p.1*(round α)+p.2*(round β))
  have hz : |(z:ℝ)| ≤ δ+(8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R := by
    have hid : (z:ℝ) = -((p.1:ℝ)*α+(p.2:ℝ)*β-b)+
        ((p.1:ℝ)*(α-(round α:ℤ))+(p.2:ℝ)*(β-(round β:ℤ))) := by
      dsimp [z]; push_cast; ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_neg]
    have ht := abs_add_le ((p.1:ℝ)*(α-(round α:ℤ))) ((p.2:ℝ)*(β-(round β:ℤ)))
    rw [abs_mul,abs_mul,abs_of_nonneg hp0,abs_of_nonneg hnR.le] at ht
    have hpa := mul_le_mul hpM ha (abs_nonneg _) (mul_nonneg hμ0 hNR.le)
    have hpb := mul_le_mul (show (p.2:ℝ) ≤ N by exact_mod_cast hnN) hb (abs_nonneg _) hNR.le
    have hab : (μ*(N:ℝ))*(8*(N:ℝ)*δ/R)+(N:ℝ)*(20*B*(μ*(N:ℝ))*δ/R) =
        (8+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R := by ring
    change (p.1:ℝ)*|α-(round α:ℤ)| ≤ (μ*(N:ℝ))*(8*(N:ℝ)*δ/R) at hpa
    change (p.2:ℝ)*|β-(round β:ℤ)| ≤ (N:ℝ)*(20*B*(μ*(N:ℝ))*δ/R) at hpb
    linarith only [hpnear,ht,hpa,hpb,hab]
  have hzsmall : |z| < 1 := by exact_mod_cast hz.trans_lt herr
  have hz0 : z=0 := by have hh := abs_lt.mp hzsmall; omega
  dsimp [z] at hz0
  exact sub_eq_zero.mp hz0

end TaoTrudgianYang2025.HuxleyLinearForm

namespace TaoTrudgianYang2025.HuxleyRationalPhase

/-- The literal single reciprocal branch in Huxley (1993), (4.9).
The nonlinear phase is the difference of two such branches. -/
noncomputable def rationalBranch (μ r s x : ℝ) : ℝ := 1/(3*μ*r^2*(r*x+s))

theorem rationalBranch_hasDerivAt {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    HasDerivAt (rationalBranch μ r s) (-1/(3*μ*r*(r*x+s)^2)) x := by
  have hd := (((hasDerivAt_id x).const_mul r).add_const s).inv hx
  convert hd.const_mul (1/(3*μ*r^2)) using 1
  · ext y
    change 1/(3*μ*r^2*(r*y+s)) = (1/(3*μ*r^2))*(r*y+s)⁻¹
    rw [div_mul_eq_div_div,div_eq_mul_inv]
  · dsimp
    field_simp

/-- Exact first-order remainder for the source reciprocal branch. This
retains the geometric denominators instead of assuming a Taylor error. -/
theorem rationalBranch_linear_remainder {μ r s x x₀ : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) (hx₀ : r*x₀+s ≠ 0) :
    rationalBranch μ r s x-rationalBranch μ r s x₀-
      deriv (rationalBranch μ r s) x₀*(x-x₀) =
      (x-x₀)^2/(3*μ*(r*x+s)*(r*x₀+s)^2) := by
  rw [(rationalBranch_hasDerivAt hμ hr hx₀).deriv]
  dsimp [rationalBranch]
  field_simp
  ring


/-- The second derivative of the actual branch, reusing the already
proved reciprocal-calculus theorem rather than a new calculus framework. -/
theorem rationalBranch_second {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (rationalBranch μ r s) x = 2/(3*μ*(r*x+s)^3) := by
  let f : ℝ → ℝ := fun y => 3*μ*r^2*(r*y+s)
  have hd : deriv f = fun _ => 3*μ*r^3 := by
    funext y
    have hh := (((hasDerivAt_id y).const_mul r).add_const s).const_mul (3*μ*r^2)
    have he : HasDerivAt f (3*μ*r^3) y := by
      convert hh using 1
      dsimp
      ring
    exact he.deriv
  have hne : f x ≠ 0 := by dsimp [f]; positivity
  have he := TaoTrudgianYang2025.iteratedDeriv_two_real_inv
    (show ContDiffAt ℝ 2 f x by dsimp [f]; fun_prop) hne
  have hbranch : rationalBranch μ r s = fun y => (f y)⁻¹ := by
    funext y
    simp only [rationalBranch,f,one_div]
  rw [hbranch,he,iteratedDeriv_succ,iteratedDeriv_one,hd]
  simp only [deriv_const,zero_div,sub_zero,f]
  field_simp

noncomputable def rationalPhase (μ r s μ₁ r₁ s₁ x : ℝ) : ℝ :=
  rationalBranch μ r s x-rationalBranch μ₁ r₁ s₁ x

/-- Exact nonlinear Taylor remainder of (4.9), retaining cancellation
between the two reciprocal branches. No triangle-inequality loss occurs. -/
theorem rationalPhase_linear_remainder {μ r s μ₁ r₁ s₁ x x₀ : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₀ : r*x₀+s ≠ 0)
    (hx₁ : r₁*x+s₁ ≠ 0) (hx₀₁ : r₁*x₀+s₁ ≠ 0) :
    rationalPhase μ r s μ₁ r₁ s₁ x-rationalPhase μ r s μ₁ r₁ s₁ x₀-
      deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀*(x-x₀) =
      (x-x₀)^2*(1/(3*μ*(r*x+s)*(r*x₀+s)^2)-
        1/(3*μ₁*(r₁*x+s₁)*(r₁*x₀+s₁)^2)) := by
  have ha := rationalBranch_linear_remainder hμ hr hx hx₀
  have hb := rationalBranch_linear_remainder hμ₁ hr₁ hx₁ hx₀₁
  have hd := ((rationalBranch_hasDerivAt hμ hr hx₀).sub
    (rationalBranch_hasDerivAt hμ₁ hr₁ hx₀₁)).deriv
  change deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀ = _ at hd
  rw [(rationalBranch_hasDerivAt hμ hr hx₀).deriv] at ha
  rw [(rationalBranch_hasDerivAt hμ₁ hr₁ hx₀₁).deriv] at hb
  rw [hd]
  dsimp only [rationalPhase]
  linear_combination ha-hb


/-- The actual homogeneous substitution in (5.7)--(5.8), with the complete
nonlinear error and its branch cancellation left explicit. -/
theorem rationalPhase_homogeneous_linearization
    {μ r s μ₁ r₁ s₁ x₀ u t α β : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0) (ht : t ≠ 0)
    (hx : r*(u/t)+s ≠ 0) (hx₀ : r*x₀+s ≠ 0)
    (hx₁ : r₁*(u/t)+s₁ ≠ 0) (hx₀₁ : r₁*x₀+s₁ ≠ 0) :
    (α-deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀)*u+
      (β-rationalPhase μ r s μ₁ r₁ s₁ x₀+x₀*deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀)*t-
      (α*u+β*t-t*rationalPhase μ r s μ₁ r₁ s₁ (u/t)) =
    t*(u/t-x₀)^2*(1/(3*μ*(r*(u/t)+s)*(r*x₀+s)^2)-
      1/(3*μ₁*(r₁*(u/t)+s₁)*(r₁*x₀+s₁)^2)) := by
  have he := rationalPhase_linear_remainder hμ hr hμ₁ hr₁ hx hx₀ hx₁ hx₀₁
  calc
    _ = t*(rationalPhase μ r s μ₁ r₁ s₁ (u/t)-rationalPhase μ r s μ₁ r₁ s₁ x₀-
        deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀*(u/t-x₀)) := by field_simp; ring
    _ = _ := by rw [he]; ring


theorem rationalPhase_second {μ r s μ₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x =
      2/(3*μ*(r*x+s)^3)-2/(3*μ₁*(r₁*x+s₁)^3) := by
  have ha : ContDiffAt ℝ 2 (rationalBranch μ r s) x := by
    dsimp [rationalBranch]
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  have hb : ContDiffAt ℝ 2 (rationalBranch μ₁ r₁ s₁) x := by
    dsimp [rationalBranch]
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  unfold rationalPhase
  rw [iteratedDeriv_fun_sub ha hb,
    rationalBranch_second hμ hr hx,rationalBranch_second hμ₁ hr₁ hx₁]

/-- Curvature is controlled by the actual cubic ratio in the Third
Condition, preserving the cancellation needed for (4.12) and (6.9). -/
theorem rationalPhase_curvature_of_cubic_ratio
    {μ r s μ₁ r₁ s₁ x ε : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : 0 < μ₁) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : 0 < r₁*x+s₁)
    (hratio : |μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1| ≤ ε) :
    |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x| ≤
      (2/(3*μ₁*(r₁*x+s₁)^3))*ε := by
  rw [rationalPhase_second hμ hr hμ₁.ne' hr₁ hx hx₁.ne']
  have he : 2/(3*μ*(r*x+s)^3)-2/(3*μ₁*(r₁*x+s₁)^3) =
      (2/(3*μ₁*(r₁*x+s₁)^3))*(μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1) := by
    have haux (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
        2/(3*a)-2/(3*b) = (2/(3*b))*(b/a-1) := by field_simp
    simpa only [mul_assoc] using haux (μ*(r*x+s)^3) (μ₁*(r₁*x+s₁)^3)
      (mul_ne_zero hμ (pow_ne_zero 3 hx)) (mul_ne_zero hμ₁.ne' (pow_ne_zero 3 hx₁.ne'))
  rw [he,abs_mul,abs_of_pos (by positivity : 0 < 2/(3*μ₁*(r₁*x+s₁)^3))]
  exact mul_le_mul_of_nonneg_left hratio (by positivity)


/-- Quantitative source-phase Taylor entry from the cubic coincidence
ratio and genuine affine-denominator bounds on the whole segment.
Obtaining these geometric hypotheses from model-phase minor arcs is a
separate, still open source-entry obligation. -/
theorem rationalPhase_taylor_of_cubic_ratio
    {μ r s μ₁ r₁ s₁ x x₀ d ε : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : 0 < μ₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d)
    (hden : ∀ y ∈ Set.uIcc x₀ x, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.uIcc x₀ x, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.uIcc x₀ x, |μ₁*(r₁*y+s₁)^3/(μ*(r*y+s)^3)-1| ≤ ε) :
    |rationalPhase μ r s μ₁ r₁ s₁ x-rationalPhase μ r s μ₁ r₁ s₁ x₀-
      deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀*(x-x₀)| ≤
      ε*|x-x₀|^2/(3*μ₁*d^3) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hratio x₀ Set.left_mem_uIcc)
  have hs : ∀ y ∈ Set.uIcc x₀ x, ContDiffAt ℝ 2 (rationalPhase μ r s μ₁ r₁ s₁) y := by
    intro y hy
    have ha := hden y hy
    have hb : r₁*y+s₁ ≠ 0 := (hd.trans_le (hden₁ y hy)).ne'
    change ContDiffAt ℝ 2 (fun z => 1/(3*μ*r^2*(r*z+s))-1/(3*μ₁*r₁^2*(r₁*z+s₁))) y
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hcurv : ∀ y ∈ Set.uIcc x₀ x,
      |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) y| ≤ 2*ε/(3*μ₁*d^3) := by
    intro y hy
    apply (rationalPhase_curvature_of_cubic_ratio hμ hr hμ₁ hr₁ (hden y hy)
      (hd.trans_le (hden₁ y hy)) (hratio y hy)).trans
    calc
      _ = (2*ε)/(3*μ₁*(r₁*y+s₁)^3) := by ring
      _ ≤ _ := by gcongr; exact hden₁ y hy
  have ht := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 1 hs hcurv
  have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (rationalPhase μ r s μ₁ r₁ s₁) 1 x₀ x =
      rationalPhase μ r s μ₁ r₁ s₁ x₀+deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀*(x-x₀) := by
    simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at ht
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at ht
  convert ht using 1
  · congr 1
    ring
  · ring


/-- The Taylor bound is consumed on actual primitive sector points.
The height and sector width are linked to the same denominator and ratio;
no independent linearisation-error hypothesis is supplied. -/
theorem sector_homogeneous_taylor_bound
    {N : ℕ} {l v ν r s ν₁ r₁ s₁ x₀ d ε α β : ℝ}
    (hl : 0 < l) (hv : l ≤ v) (hx₀ : x₀ ∈ Set.Icc l v)
    (hν : ν ≠ 0) (hr : r ≠ 0) (hν₁ : 0 < ν₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d)
    (hden : ∀ y ∈ Set.Icc l v, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l v, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.Icc l v, |ν₁*(r₁*y+s₁)^3/(ν*(r*y+s)^3)-1| ≤ ε)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v) :
    let g := rationalPhase ν r s ν₁ r₁ s₁
    |(α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
      ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ)))| ≤
      (N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3) := by
  let g := rationalPhase ν r s ν₁ r₁ s₁
  change |(α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
      ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ)))| ≤ _
  obtain ⟨hn,hnN,_hc,hlo,hu⟩ :=
    (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hv)).mp hp
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  let x : ℝ := (p.1:ℝ)/(p.2:ℝ)
  have hx : x ∈ Set.Icc l v := ⟨(le_div_iff₀ hnR).mpr hlo,(div_le_iff₀ hnR).mpr hu⟩
  have hseg : Set.uIcc x₀ x ⊆ Set.Icc l v := Set.uIcc_subset_Icc hx₀ hx
  have ht := rationalPhase_taylor_of_cubic_ratio hν hr hν₁ hr₁ hd
    (fun y hy => hden y (hseg hy)) (fun y hy => hden₁ y (hseg hy))
    (fun y hy => hratio y (hseg hy))
  change |g x-g x₀-deriv g x₀*(x-x₀)| ≤ ε*|x-x₀|^2/(3*ν₁*d^3) at ht
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hratio x₀ hx₀)
  have hdist : |x-x₀| ≤ v-l := abs_le.mpr ⟨by linarith [hx.1,hx₀.2],by linarith [hx.2,hx₀.1]⟩
  have hid : (α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
      ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g x) =
      (p.2:ℝ)*(g x-g x₀-deriv g x₀*(x-x₀)) := by
    dsimp [x]
    field_simp
    ring
  change |(α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
      ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g x)| ≤ _
  rw [hid,abs_mul,abs_of_pos hnR]
  calc
    _ ≤ (p.2:ℝ)*(ε*|x-x₀|^2/(3*ν₁*d^3)) := mul_le_mul_of_nonneg_left ht hnR.le
    _ ≤ (N:ℝ)*(ε*(v-l)^2/(3*ν₁*d^3)) := by
      gcongr
      exact_mod_cast hnN
    _ = _ := by ring


/-- The literal reciprocal nonlinear phase feeds the production sector
rigidity theorem with its derived, linked Taylor budget. The cubic-ratio
and denominator hypotheses remain explicitly upstream geometric inputs. -/
theorem sector_nonlinear_integer_labels
    {N : ℕ} {l v B ν r s ν₁ r₁ s₁ x₀ d ε α β δ : ℝ}
    (hl : 0 < l) (hv : 1 ≤ v) (hlv : l ≤ v) (hB : 1 ≤ B) (hx₀ : x₀ ∈ Set.Icc l v)
    (hν : ν ≠ 0) (hr : r ≠ 0) (hν₁ : 0 < ν₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d) (hδ : 0 ≤ δ)
    (hden : ∀ y ∈ Set.Icc l v, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l v, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.Icc l v, |ν₁*(r₁*y+s₁)^3/(ν*(r*y+s)^3)-1| ≤ ε)
    (hR : max ((v-l)*(N:ℝ)^2/B) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v).card)
    (hnear : ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-
        (p.2:ℝ)*rationalPhase ν r s ν₁ r₁ s₁ ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ) :
    let g := rationalPhase ν r s ν₁ r₁ s₁
    let η := δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3)
    1536*B*η*(v*(N:ℝ))*(N:ℝ) <
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v).card →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ →
      b=p.1*(round (α-deriv g x₀))+p.2*(round (β-g x₀+x₀*deriv g x₀)) := by
  let g := rationalPhase ν r s ν₁ r₁ s₁
  let η := δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3)
  change 1536*B*η*(v*(N:ℝ))*(N:ℝ) < _ → _
  intro hlarge
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hratio x₀ hx₀)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hpoint (p : ℤ × ℤ) (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v)
      (b : ℤ) (hb : |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ) :
      |(p.1:ℝ)*(α-deriv g x₀)+(p.2:ℝ)*(β-g x₀+x₀*deriv g x₀)-b| ≤ η := by
    have ht := sector_homogeneous_taylor_bound (α := α) (β := β) hl hlv hx₀
      hν hr hν₁ hr₁ hd hden hden₁ hratio hp
    change |(α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
      ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ)))| ≤ _ at ht
    have hid : (p.1:ℝ)*(α-deriv g x₀)+(p.2:ℝ)*(β-g x₀+x₀*deriv g x₀)-b =
        ((α-deriv g x₀)*(p.1:ℝ)+(β-g x₀+x₀*deriv g x₀)*(p.2:ℝ)-
          ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))))+
        ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    dsimp [η]
    linarith only [ht,hb]
  have hlin : ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v,
      ∃ b : ℤ, |(p.1:ℝ)*(α-deriv g x₀)+(p.2:ℝ)*(β-g x₀+x₀*deriv g x₀)-b| ≤ η := by
    intro p hp
    obtain ⟨b,hb⟩ := hnear p hp
    exact ⟨b,hpoint p hp b hb⟩
  have hh := TaoTrudgianYang2025.HuxleyLinearForm.fareySector_integer_labels
    hl hv hB hη hR hlarge hlin
  exact fun p hp b hb => hh p hp b (hpoint p hp b hb)


/-- The continuous minor-arc coordinate in Huxley (1993), (3.12). -/
noncomputable def minorArcCoordinate (μ r s x : ℝ) : ℝ := 1/(3*μ*r*(r*x+s))

/-- The exact determinant identity used between (6.10) and (6.11).
The two coordinates are evaluations of the same rational function. -/
theorem affine_ratio_coordinate_difference {μ r s r₁ s₁ z₁ z₂ : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hz₁ : r*z₁+s ≠ 0) (hz₂ : r*z₂+s ≠ 0) :
    (r₁*z₂+s₁)/(r*z₂+s)-(r₁*z₁+s₁)/(r*z₁+s) =
      3*μ*(r*s₁-s*r₁)*(minorArcCoordinate μ r s z₂-minorArcCoordinate μ r s z₁) := by
  dsimp [minorArcCoordinate]
  field_simp [hμ,hr,hz₁,hz₂]
  field_simp [hz₂]
  ring

/-- Two cubic coincidence inequalities control the actual ratio gap,
with the positive lower bound and multiplier kept explicit. -/
theorem cubic_ratio_gap {a u v d ε : ℝ} (hd : 0 ≤ d) (hu : d ≤ u) (hv : d ≤ v)
    (he₁ : |a*u^3-1| ≤ ε) (he₂ : |a*v^3-1| ≤ ε) :
    |a| * (3*d^2*|u-v|) ≤ 2*ε := by
  have hu0 : 0 ≤ u := hd.trans hu
  have hv0 : 0 ≤ v := hd.trans hv
  have hfac : 3*d^2 ≤ u^2+u*v+v^2 := by
    have haa : d*d ≤ u*u := mul_self_le_mul_self hd hu
    have hbb : d*d ≤ v*v := mul_self_le_mul_self hd hv
    have hab : d*d ≤ u*v := mul_le_mul hu hv hd hu0
    nlinarith only [haa,hbb,hab]
  have hid : |u^3-v^3| = |u-v| * (u^2+u*v+v^2) := by
    rw [show u^3-v^3 = (u-v)*(u^2+u*v+v^2) by ring,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ u^2+u*v+v^2)]
  have hdiff : |a*(u^3-v^3)| ≤ 2*ε := by
    calc
      _ = |(a*u^3-1)-(a*v^3-1)| := by congr 1; ring
      _ ≤ |a*u^3-1|+|a*v^3-1| := by
        have ht := abs_add_le (a*u^3-1) (-(a*v^3-1))
        rw [abs_neg] at ht
        simpa only [sub_eq_add_neg] using ht
      _ ≤ _ := by linarith only [he₁,he₂]
  rw [abs_mul,hid] at hdiff
  apply le_trans _ hdiff
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
  nlinarith only [mul_le_mul_of_nonneg_left hfac (abs_nonneg (u-v))]

/-- Two Third-Condition estimates plus genuine separation in G give the
First-Condition determinant saving. The L-dependent estimates feeding
these hypotheses still require the long-block Cauchy argument. -/
theorem determinant_bound_of_cubic_ratios
    {μ r s μ₁ r₁ s₁ z₁ z₂ d ε H : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hd : 0 < d) (hH : 0 < H)
    (hz₁ : r*z₁+s ≠ 0) (hz₂ : r*z₂+s ≠ 0)
    (hq₁ : d ≤ (r₁*z₁+s₁)/(r*z₁+s)) (hq₂ : d ≤ (r₁*z₂+s₁)/(r*z₂+s))
    (he₁ : |μ₁*(r₁*z₁+s₁)^3/(μ*(r*z₁+s)^3)-1| ≤ ε)
    (he₂ : |μ₁*(r₁*z₂+s₁)^3/(μ*(r*z₂+s)^3)-1| ≤ ε)
    (hsep : H ≤ |minorArcCoordinate μ r s z₂-minorArcCoordinate μ r s z₁|) :
    |r*s₁-s*r₁| ≤ 2*ε/(9*|μ₁| * d^2*H) := by
  have ha : |μ₁/μ*((r₁*z₁+s₁)/(r*z₁+s))^3-1| ≤ ε := by
    simpa only [div_pow,div_mul_div_comm,mul_one] using he₁
  have hb : |μ₁/μ*((r₁*z₂+s₁)/(r*z₂+s))^3-1| ≤ ε := by
    simpa only [div_pow,div_mul_div_comm,mul_one] using he₂
  have hg := cubic_ratio_gap hd.le hq₂ hq₁ hb ha
  rw [affine_ratio_coordinate_difference hμ hr hz₁ hz₂] at hg
  norm_num only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 3)] at hg
  have heq : |μ₁| / |μ| * (3*d^2*(3*|μ| * |r*s₁-s*r₁| *
      |minorArcCoordinate μ r s z₂-minorArcCoordinate μ r s z₁|)) =
      9*|μ₁| * d^2*|r*s₁-s*r₁| *
        |minorArcCoordinate μ r s z₂-minorArcCoordinate μ r s z₁| := by
    field_simp
    ring
  rw [heq] at hg
  have hbound : 9*|μ₁| * d^2*|r*s₁-s*r₁| * H ≤ 2*ε :=
    (mul_le_mul_of_nonneg_left hsep (by positivity)).trans hg
  apply (le_div_iff₀ (by positivity : 0 < 9*|μ₁| * d^2*H)).mpr
  nlinarith only [hbound]


/-- A quantitative mean-value step. Only endpoint values and ordinary
derivatives are supplied; no small-derivative conclusion is assumed. -/
theorem exists_small_deriv_of_two_values {f f' : ℝ → ℝ} {a b h E : ℝ}
    (hh : 0 < h) (hgap : h ≤ b-a)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (ha : |f a| ≤ E) (hb : |f b| ≤ E) :
    ∃ y ∈ Set.Ioo a b, |f' y| ≤ 2*E/h := by
  have hab : a < b := by linarith only [hh,hgap]
  have hE : 0 ≤ E := (abs_nonneg _).trans ha
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
  refine ⟨y,hy,?_⟩
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hab)]
  have hsum : |f b-f a| ≤ 2*E := by
    have ht : |f b-f a| ≤ |f b|+|f a| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (f b) 0 (f a)
    linarith only [ht,ha,hb]
  exact (div_le_div_of_nonneg_right hsum (sub_pos.mpr hab).le).trans
    (div_le_div_of_nonneg_left (by positivity) hh hgap)

/-- The twice-applied mean-value argument at four genuinely separated
points. This is the analytic source of the squared long-block saving. -/
theorem four_point_curvature {f : ℝ → ℝ} {a b c d h E : ℝ}
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hf : ∀ x ∈ Set.Icc a d, ContDiffAt ℝ 2 f x)
    (ha : |f a| ≤ E) (hb : |f b| ≤ E) (hc : |f c| ≤ E) (hd : |f d| ≤ E) :
    ∃ z ∈ Set.Ioo a d, |iteratedDeriv 2 f z| ≤ 4*E/h^2 := by
  have hab' : a < b := by linarith only [hh,hab]
  have hbc' : b < c := by linarith only [hh,hbc]
  have hcd' : c < d := by linarith only [hh,hcd]
  have hf' (x : ℝ) (hx : x ∈ Set.Icc a d) : HasDerivAt f (deriv f x) x :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨y₁,hy₁,he₁⟩ := exists_small_deriv_of_two_values hh hab
    (fun x hx => hf' x ⟨hx.1,le_trans hx.2 (hbc'.trans hcd').le⟩) ha hb
  obtain ⟨y₂,hy₂,he₂⟩ := exists_small_deriv_of_two_values hh hcd
    (fun x hx => hf' x ⟨le_trans (hab'.trans hbc').le hx.1,hx.2⟩) hc hd
  have hygap : h ≤ y₂-y₁ := by linarith only [hbc,hy₁.2,hy₂.1]
  have hder (x : ℝ) (hx : x ∈ Set.Icc y₁ y₂) :
      HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
    have hhx := TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite
      (by norm_num : 1 < 2) (hf x ⟨hy₁.1.le.trans hx.1,hx.2.trans hy₂.2.le⟩)
    simpa only [iteratedDeriv_one] using hhx
  obtain ⟨z,hz,hez⟩ := exists_small_deriv_of_two_values hh hygap hder he₁ he₂
  refine ⟨z,⟨hy₁.1.trans hz.1,hz.2.trans hy₂.2⟩,?_⟩
  convert hez using 1
  ring

/-- The converse curvature identity, retaining both the literal cubic
ratio and the affine denominators of the source. -/
theorem rationalPhase_cubic_ratio_abs_eq
    {μ r s μ₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    |μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1| =
      (3*|μ₁| * |r₁*x+s₁|^3/2)*|iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x| := by
  rw [rationalPhase_second hμ hr hμ₁ hr₁ hx hx₁]
  have haux (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
      b/a-1=(3*b/2)*(2/(3*a)-2/(3*b)) := by field_simp
  rw [haux (μ*(r*x+s)^3) (μ₁*(r₁*x+s₁)^3)
    (mul_ne_zero hμ (pow_ne_zero 3 hx)) (mul_ne_zero hμ₁ (pow_ne_zero 3 hx₁))]
  norm_num only [abs_mul,abs_div,abs_pow,abs_of_pos (by norm_num : (0:ℝ) < 3),
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf


/-- A four-point source-phase consumer. It derives a Third-Condition
estimate from affine residual values, rather than assuming curvature or
the cubic-ratio conclusion. Denominator bounds are still geometric inputs. -/
theorem rationalPhase_four_point_cubic_ratio
    {μ r s μ₁ r₁ s₁ a b c d h E D₁ A B : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hden : ∀ x ∈ Set.Icc a d, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc a d, r₁*x+s₁ ≠ 0)
    (hD₁ : ∀ x ∈ Set.Icc a d, |r₁*x+s₁| ≤ D₁)
    (ha : |A*a+B-rationalPhase μ r s μ₁ r₁ s₁ a| ≤ E)
    (hb : |A*b+B-rationalPhase μ r s μ₁ r₁ s₁ b| ≤ E)
    (hc : |A*c+B-rationalPhase μ r s μ₁ r₁ s₁ c| ≤ E)
    (hd : |A*d+B-rationalPhase μ r s μ₁ r₁ s₁ d| ≤ E) :
    ∃ z ∈ Set.Ioo a d,
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 6*|μ₁| * D₁^3*E/h^2 := by
  let g := rationalPhase μ r s μ₁ r₁ s₁
  let f : ℝ → ℝ := fun x => A*x+B-g x
  have hg (x : ℝ) (hx : x ∈ Set.Icc a d) : ContDiffAt ℝ 2 g x := by
    have hdx := hden x hx
    have hdx₁ := hden₁ x hx
    change ContDiffAt ℝ 2 (fun y => 1/(3*μ*r^2*(r*y+s))-1/(3*μ₁*r₁^2*(r₁*y+s₁))) x
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hf (x : ℝ) (hx : x ∈ Set.Icc a d) : ContDiffAt ℝ 2 f x :=
    (show ContDiffAt ℝ 2 (fun y => A*y+B) x by fun_prop).sub (hg x hx)
  obtain ⟨z,hz,hez⟩ := four_point_curvature hh hab hbc hcd hf ha hb hc hd
  have hz' : z ∈ Set.Icc a d := ⟨hz.1.le,hz.2.le⟩
  have he : iteratedDeriv 2 f z = -iteratedDeriv 2 g z := by
    dsimp only [f]
    rw [iteratedDeriv_fun_sub (by fun_prop) (hg z hz')]
    have hdlin : deriv (fun y : ℝ => A*y+B) = fun _ => A := by
      funext y
      simpa only [mul_one,id_eq] using (((hasDerivAt_id y).const_mul A).add_const B).deriv
    rw [iteratedDeriv_succ,iteratedDeriv_one,hdlin]
    simp only [deriv_const,zero_sub]
  rw [he,abs_neg] at hez
  refine ⟨z,hz,?_⟩
  rw [rationalPhase_cubic_ratio_abs_eq hμ hr hμ₁ hr₁ (hden z hz') (hden₁ z hz')]
  change (3*|μ₁| * |r₁*z+s₁|^3/2)*|iteratedDeriv 2 g z| ≤ _
  have hD₁0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ z hz')
  have hE : 0 ≤ E := (abs_nonneg _).trans ha
  calc
    _ ≤ (3*|μ₁| * D₁^3/2)*(4*E/h^2) := by gcongr; exact hD₁ z hz'
    _ = _ := by ring


theorem minorArcCoordinate_difference {μ r s a b : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0) :
    minorArcCoordinate μ r s b-minorArcCoordinate μ r s a =
      -(b-a)/(3*μ*(r*b+s)*(r*a+s)) := by
  dsimp [minorArcCoordinate]
  field_simp [hμ,hr,ha,hb]
  ring

/-- Actual coordinate separation is derived from point spacing and
affine-denominator bounds, not supplied as an independent witness. -/
theorem minorArcCoordinate_gap_lower {μ r s a b h D : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hh : 0 < h) (hD : 0 < D)
    (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0)
    (haD : |r*a+s| ≤ D) (hbD : |r*b+s| ≤ D) (hgap : h ≤ b-a) :
    h/(3*|μ| * D^2) ≤ |minorArcCoordinate μ r s b-minorArcCoordinate μ r s a| := by
  rw [minorArcCoordinate_difference hμ hr ha hb,abs_div,abs_neg,
    abs_of_pos (by linarith only [hh,hgap] : 0 < b-a)]
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hmul : |r*b+s| * |r*a+s| ≤ D^2 := by
    nlinarith only [mul_le_mul hbD haD (abs_nonneg (r*a+s)) hD.le]
  calc
    _ ≤ (b-a)/(3*|μ| * D^2) := div_le_div_of_nonneg_right hgap (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith only [hh,hgap]) (by positivity)
      (by nlinarith only [mul_le_mul_of_nonneg_left hmul (show 0 ≤ 3*|μ| by positivity)])

/-- An eight-point long-block analytic core for the literal source phase.
The inverse-cube spacing saving is derived by two four-point consumers and
the actual G-coordinate identity. Selecting these points from minor arcs
and deriving the uniform geometric bounds remain separate obligations. -/
theorem rationalPhase_eight_point_determinant
    {μ r s μ₁ r₁ s₁ h E D D₁ q A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hD : 0 < D) (hq : 0 < q)
    (hgap : ∀ i : Fin 7, h ≤ x i.succ-x i.castSucc)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound : ∀ y ∈ Set.Icc (x 0) (x 7), |r*y+s| ≤ D)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ D₁)
    (hratio : ∀ y ∈ Set.Icc (x 0) (x 7), q ≤ (r₁*y+s₁)/(r*y+s))
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤ E) :
    |r*s₁-s*r₁| ≤ 4*|μ| * D^2*D₁^3*E/(q^2*h^3) := by
  have hmono : StrictMono x := Fin.strictMono_iff_lt_succ.mpr (fun i => by
    have hi := hgap i
    linarith only [hh,hi])
  have hleft : Set.Icc (x 0) (x 3) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨hy.1,hy.2.trans (hmono.monotone (by decide))⟩
  have hright : Set.Icc (x 4) (x 7) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨(hmono.monotone (by decide)).trans hy.1,hy.2⟩
  obtain ⟨z₁,hz₁,he₁⟩ := rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh
    (hgap 0) (hgap 1) (hgap 2)
    (fun y hy => hden y (hleft hy)) (fun y hy => hden₁ y (hleft hy))
    (fun y hy => hbound₁ y (hleft hy)) (hres 0) (hres 1) (hres 2) (hres 3)
  obtain ⟨z₂,hz₂,he₂⟩ := rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh
    (hgap 4) (hgap 5) (hgap 6)
    (fun y hy => hden y (hright hy)) (fun y hy => hden₁ y (hright hy))
    (fun y hy => hbound₁ y (hright hy)) (hres 4) (hres 5) (hres 6) (hres 7)
  have hz₁' := hleft ⟨hz₁.1.le,hz₁.2.le⟩
  have hz₂' := hright ⟨hz₂.1.le,hz₂.2.le⟩
  change z₁ ∈ Set.Ioo (x 0) (x 3) at hz₁
  change z₂ ∈ Set.Ioo (x 4) (x 7) at hz₂
  have hzgap : h ≤ z₂-z₁ := by
    have hmiddle := hgap 3
    change h ≤ x 4-x 3 at hmiddle
    linarith only [hmiddle,hz₁.2,hz₂.1]
  have hsep := minorArcCoordinate_gap_lower hμ hr hh hD
    (hden z₁ hz₁') (hden z₂ hz₂') (hbound z₁ hz₁') (hbound z₂ hz₂') hzgap
  have he := determinant_bound_of_cubic_ratios hμ hμ₁ hr hq
    (by positivity : 0 < h/(3*|μ| * D^2)) (hden z₁ hz₁') (hden z₂ hz₂')
    (hratio z₁ hz₁') (hratio z₂ hz₂') he₁ he₂ hsep
  convert he using 1
  field_simp
  ring


/-- Separation measured in the actual minor-arc coordinate forces
ordinary point spacing, with the affine denominator scale retained. -/
theorem point_gap_of_minorArcCoordinate_gap {μ r s a b d H : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hab : a ≤ b) (hd : 0 < d) (hH : 0 ≤ H)
    (ha : d ≤ |r*a+s|) (hb : d ≤ |r*b+s|)
    (hgap : H ≤ |minorArcCoordinate μ r s b-minorArcCoordinate μ r s a|) :
    3*|μ| * d^2*H ≤ b-a := by
  have hna : r*a+s ≠ 0 := abs_pos.mp (hd.trans_le ha)
  have hnb : r*b+s ≠ 0 := abs_pos.mp (hd.trans_le hb)
  rw [minorArcCoordinate_difference hμ hr hna hnb,abs_div,abs_neg,
    abs_of_nonneg (sub_nonneg.mpr hab)] at hgap
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)] at hgap
  have hg := (le_div_iff₀ (by positivity : 0 < 3*|μ| * |r*b+s| * |r*a+s|)).mp hgap
  have hp : d^2 ≤ |r*b+s| * |r*a+s| := by
    nlinarith only [mul_le_mul hb ha hd.le (abs_nonneg (r*b+s))]
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3*|μ| * H by positivity)
  nlinarith only [hh,hg]

theorem scaled_minorArcCoordinate_abs {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    |r*minorArcCoordinate μ r s x| = 1/(3*|μ| * |r*x+s|) := by
  dsimp [minorArcCoordinate]
  norm_num only [abs_mul,abs_div,abs_one,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  field_simp

/-- The L^-3 First-Condition saving with linked physical scales.
This consumes the literal (6.1) residual, eight G-separated points, dyadic
denominator bounds and the phase scale. No small determinant, curvature,
or improved coincidence inequality is a hypothesis. The minor-arc
construction still has to supply these geometric inputs uniformly. -/
theorem rationalPhase_long_block_determinant
    {μ r s μ₁ r₁ s₁ d L N R K Kμ A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R)
    (hK : 0 ≤ K) (hscale : 1 ≤ Kμ*|μ| * N*R^2)
    (hmono : StrictMono x)
    (hgap : ∀ i : Fin 7, L*N ≤
      |minorArcCoordinate μ r s (x i.succ)-minorArcCoordinate μ r s (x i.castSucc)|)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), d ≤ |r*y+s| ∧ |r*y+s| ≤ 2*d)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ 4*d)
    (hratio : ∀ y ∈ Set.Icc (x 0) (x 7), (1:ℝ)/2 ≤ (r₁*y+s₁)/(r*y+s))
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      K*R^2/|r*minorArcCoordinate μ r s (x i)|) :
    |r*s₁-s*r₁| ≤ 1024*K*Kμ*R^4/(L^3*N^2) := by
  have hin (i : Fin 8) : x i ∈ Set.Icc (x 0) (x 7) :=
    ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
  have hne (y : ℝ) (hy : y ∈ Set.Icc (x 0) (x 7)) : r*y+s ≠ 0 :=
    abs_pos.mp (hd.trans_le (hden y hy).1)
  have hspacing (i : Fin 7) : 3*|μ| * d^2*(L*N) ≤ x i.succ-x i.castSucc :=
    point_gap_of_minorArcCoordinate_gap hμ hr
      (hmono.monotone (by change i.val ≤ i.val+1; omega)) hd (by positivity)
      (hden _ (hin i.castSucc)).1 (hden _ (hin i.succ)).1 (hgap i)
  have hres' (i : Fin 8) : |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      6*K*|μ| * R^2*d := by
    have he := hres i
    rw [scaled_minorArcCoordinate_abs hμ hr (hne _ (hin i))] at he
    have hid : K*R^2/(1/(3*|μ| * |r*x i+s|)) = 3*K*|μ| * R^2*|r*x i+s| := by
      field_simp
    rw [hid] at he
    apply he.trans
    have hb := mul_le_mul_of_nonneg_left (hden _ (hin i)).2
      (show 0 ≤ 3*K*|μ| * R^2 by positivity)
    nlinarith only [hb]
  have he := rationalPhase_eight_point_determinant x hμ hr hμ₁ hr₁
    (by positivity : 0 < 3*|μ| * d^2*(L*N)) (by positivity : 0 < 2*d)
    (by norm_num : (0:ℝ) < 1/2) hspacing hne hden₁
    (fun y hy => (hden y hy).2) hbound₁ hratio hres'
  have hid : 4*|μ| * (2*d)^2*(4*d)^3*(6*K*|μ| * R^2*d)/
      ((1/2:ℝ)^2*(3*|μ| * d^2*(L*N))^3) =
      (8192/9:ℝ)*K*R^2/(|μ| * L^3*N^3) := by
    field_simp
    ring
  rw [hid] at he
  apply he.trans
  apply (div_le_div_iff₀ (by positivity : 0 < |μ| * L^3*N^3)
    (by positivity : 0 < L^3*N^2)).mpr
  have hs := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 1024*K*R^2*L^3*N^2 by positivity)
  nlinarith only [hs,show 0 ≤ K*R^2*L^3*N^2 by positivity]


/-- A fractional-linear ratio stays between its endpoint values on a
positive-denominator interval. This is the monotonicity step following
Huxley (6.9), proved without a separate monotonicity hypothesis. -/
theorem affine_ratio_mem_endpoint_interval {r s r₁ s₁ a b z : ℝ}
    (hz : z ∈ Set.Icc a b) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hmid : 0 < r*z+s) :
    (r₁*z+s₁)/(r*z+s) ∈ Set.uIcc ((r₁*a+s₁)/(r*a+s)) ((r₁*b+s₁)/(r*b+s)) := by
  rcases le_total 0 (r*s₁-s*r₁) with hC | hC
  · apply Set.mem_uIcc_of_ge
    · apply (div_le_div_iff₀ hb hmid).mpr
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hz.2)]
    · apply (div_le_div_iff₀ hmid ha).mpr
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hz.1)]
  · apply Set.mem_uIcc_of_le
    · apply (div_le_div_iff₀ ha hmid).mpr
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hC (sub_nonneg.mpr hz.1)]
    · apply (div_le_div_iff₀ hmid hb).mpr
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hC (sub_nonneg.mpr hz.2)]

/-- Endpoint Third-Condition estimates extend over the whole interval.
The signed multiplier is arbitrary; the proof derives the appropriate
monotone or antitone cubic map rather than imposing its sign. -/
theorem cubic_ratio_bound_between {μ r s μ₁ r₁ s₁ a b ε : ℝ}
    (hab : a ≤ b) (hden : ∀ z ∈ Set.Icc a b, 0 < r*z+s)
    (ha : |μ₁*(r₁*a+s₁)^3/(μ*(r*a+s)^3)-1| ≤ ε)
    (hb : |μ₁*(r₁*b+s₁)^3/(μ*(r*b+s)^3)-1| ≤ ε) :
    ∀ z ∈ Set.Icc a b, |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ ε := by
  intro z hz
  have hq := affine_ratio_mem_endpoint_interval (r₁ := r₁) (s₁ := s₁) hz
    (hden a ⟨le_rfl,hab⟩) (hden b ⟨hab,le_rfl⟩) (hden z hz)
  let f : ℝ → ℝ := fun u => (μ₁/μ)*u^3-1
  have hmap : ∀ {u v w : ℝ}, w ∈ Set.uIcc u v → f w ∈ Set.uIcc (f u) (f v) := by
    rcases le_total 0 (μ₁/μ) with hsign | hsign
    · have hm : Monotone f := by
        intro u v huv
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left
          ((Odd.strictMono_pow (by decide : Odd (3:ℕ))).monotone huv) hsign) 1
      intro u v w hw
      exact hm.mapsTo_uIcc hw
    · have hm : Antitone f := by
        intro u v huv
        exact sub_le_sub_right (mul_le_mul_of_nonpos_left
          ((Odd.strictMono_pow (by decide : Odd (3:ℕ))).monotone huv) hsign) 1
      intro u v w hw
      exact hm.mapsTo_uIcc hw
  have hha : |f ((r₁*a+s₁)/(r*a+s))| ≤ ε := by
    simpa only [f,div_pow,div_mul_div_comm,mul_one] using ha
  have hhb : |f ((r₁*b+s₁)/(r*b+s))| ≤ ε := by
    simpa only [f,div_pow,div_mul_div_comm,mul_one] using hb
  have hhz : |f ((r₁*z+s₁)/(r*z+s))| ≤ ε := by
    have hi := hmap hq
    rw [Set.mem_uIcc] at hi
    obtain ⟨ha₁,ha₂⟩ := abs_le.mp hha
    obtain ⟨hb₁,hb₂⟩ := abs_le.mp hhb
    apply abs_le.mpr
    rcases hi with hi | hi
    · exact ⟨ha₁.trans hi.1,hi.2.trans hb₂⟩
    · exact ⟨hb₁.trans hi.1,hi.2.trans ha₂⟩
  simpa only [f,div_pow,div_mul_div_comm,mul_one] using hhz


/-- Two four-point curvature witnesses yield the Third Condition on the
entire middle interval, not just at two existential points. -/
theorem rationalPhase_eight_point_third_condition
    {μ r s μ₁ r₁ s₁ h E D₁ A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hgap : ∀ i : Fin 7, h ≤ x i.succ-x i.castSucc)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), 0 < r*y+s)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ D₁)
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤ E) :
    ∀ z ∈ Set.Icc (x 3) (x 4),
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 6*|μ₁| * D₁^3*E/h^2 := by
  have hmono : StrictMono x := Fin.strictMono_iff_lt_succ.mpr (fun i => by
    have hi := hgap i
    linarith only [hh,hi])
  have hleft : Set.Icc (x 0) (x 3) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨hy.1,hy.2.trans (hmono.monotone (by decide))⟩
  have hright : Set.Icc (x 4) (x 7) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨(hmono.monotone (by decide)).trans hy.1,hy.2⟩
  obtain ⟨z₁,hz₁,he₁⟩ := rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh
    (hgap 0) (hgap 1) (hgap 2)
    (fun y hy => (hden y (hleft hy)).ne') (fun y hy => hden₁ y (hleft hy))
    (fun y hy => hbound₁ y (hleft hy)) (hres 0) (hres 1) (hres 2) (hres 3)
  obtain ⟨z₂,hz₂,he₂⟩ := rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh
    (hgap 4) (hgap 5) (hgap 6)
    (fun y hy => (hden y (hright hy)).ne') (fun y hy => hden₁ y (hright hy))
    (fun y hy => hbound₁ y (hright hy)) (hres 4) (hres 5) (hres 6) (hres 7)
  change z₁ ∈ Set.Ioo (x 0) (x 3) at hz₁
  change z₂ ∈ Set.Ioo (x 4) (x 7) at hz₂
  have hmiddle : x 3 ≤ x 4 := hmono.monotone (by decide)
  have hzz : z₁ ≤ z₂ := hz₁.2.le.trans (hmiddle.trans hz₂.1.le)
  have hsegment : Set.Icc z₁ z₂ ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨hz₁.1.le.trans hy.1,hy.2.trans hz₂.2.le⟩
  have hi := cubic_ratio_bound_between hzz (fun y hy => hden y (hsegment hy)) he₁ he₂
  exact fun z hz => hi z ⟨hz₁.2.le.trans hz.1,hz.2.trans hz₂.1.le⟩


/-- The uniform L^-2 Third-Condition analytic core on the middle interval.
The same literal (6.1) residual and G-separated points are used as for the
production determinant saving. Parameter variation in the discrete minor
arcs is not identified with the fixed base parameters here. -/
theorem rationalPhase_long_block_third_condition
    {μ r s μ₁ r₁ s₁ d L N R K J A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R)
    (hK : 0 ≤ K) (hJ : |μ₁| ≤ J*|μ|) (hmono : StrictMono x)
    (hgap : ∀ i : Fin 7, L*N ≤
      |minorArcCoordinate μ r s (x i.succ)-minorArcCoordinate μ r s (x i.castSucc)|)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), d ≤ r*y+s ∧ r*y+s ≤ 2*d)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ 4*d)
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      K*R^2/|r*minorArcCoordinate μ r s (x i)|) :
    ∀ z ∈ Set.Icc (x 3) (x 4),
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 256*J*K*R^2/(L^2*N^2) := by
  have hin (i : Fin 8) : x i ∈ Set.Icc (x 0) (x 7) :=
    ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
  have hpos (y : ℝ) (hy : y ∈ Set.Icc (x 0) (x 7)) : 0 < r*y+s :=
    hd.trans_le (hden y hy).1
  have hspacing (i : Fin 7) : 3*|μ| * d^2*(L*N) ≤ x i.succ-x i.castSucc := by
    apply point_gap_of_minorArcCoordinate_gap hμ hr
      (hmono.monotone (by change i.val ≤ i.val+1; omega)) hd (by positivity)
      _ _ (hgap i)
    · simpa only [abs_of_pos (hpos _ (hin i.castSucc))] using (hden _ (hin i.castSucc)).1
    · simpa only [abs_of_pos (hpos _ (hin i.succ))] using (hden _ (hin i.succ)).1
  have hres' (i : Fin 8) : |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      6*K*|μ| * R^2*d := by
    have he := hres i
    rw [scaled_minorArcCoordinate_abs hμ hr (hpos _ (hin i)).ne',
      abs_of_pos (hpos _ (hin i))] at he
    have hid : K*R^2/(1/(3*|μ| * (r*x i+s))) = 3*K*|μ| * R^2*(r*x i+s) := by
      field_simp
    rw [hid] at he
    apply he.trans
    have hb := mul_le_mul_of_nonneg_left (hden _ (hin i)).2
      (show 0 ≤ 3*K*|μ| * R^2 by positivity)
    nlinarith only [hb]
  have he := rationalPhase_eight_point_third_condition x hμ hr hμ₁ hr₁
    (by positivity : 0 < 3*|μ| * d^2*(L*N)) hspacing hpos hden₁ hbound₁ hres'
  intro z hz
  apply (he z hz).trans
  have hid : 6*|μ₁| * (4*d)^3*(6*K*|μ| * R^2*d)/(3*|μ| * d^2*(L*N))^2 =
      256*|μ₁| * K*R^2/(|μ| * L^2*N^2) := by
    field_simp
    ring
  rw [hid]
  apply (div_le_div_iff₀ (by positivity : 0 < |μ| * L^2*N^2)
    (by positivity : 0 < L^2*N^2)).mpr
  have hs := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ 256*K*R^2*L^2*N^2 by positivity)
  nlinarith only [hs]


/-- Stability under two relative parameter errors. The loss is explicit
and the perturbed denominator is proved positive. -/
theorem ratio_relative_perturbation {a u v ε η : ℝ}
    (ha : |a-1| ≤ ε) (hu : |u-1| ≤ η) (hv : |v-1| ≤ η) (hη : η ≤ 1/2) :
    |a*u/v-1| ≤ 3*ε+4*η := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans ha
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hu
  have hvhalf : (1:ℝ)/2 ≤ v := by linarith [(abs_le.mp hv).1]
  have hvpos : 0 < v := by linarith only [hvhalf]
  have hubound : |u| ≤ (3:ℝ)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hu).1,(abs_le.mp hu).2]
  have hid : a*u/v-1 = (u*(a-1)+(u-1)-(v-1))/v := by field_simp; ring
  have hnum : |u*(a-1)+(u-1)-(v-1)| ≤ (3/2:ℝ)*ε+2*η := by
    have h₁ := abs_add_le (u*(a-1)) (u-1)
    have h₂ := abs_add_le (u*(a-1)+(u-1)) (-(v-1))
    rw [abs_neg] at h₂
    rw [abs_mul] at h₁
    have hp := mul_le_mul hubound ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
    change |u*(a-1)+(u-1)-(v-1)| ≤ _ at h₂
    linarith only [h₁,h₂,hp,hu,hv]
  rw [hid,abs_div,abs_of_pos hvpos]
  calc
    _ ≤ ((3/2:ℝ)*ε+2*η)/v := div_le_div_of_nonneg_right hnum hvpos.le
    _ ≤ ((3/2:ℝ)*ε+2*η)/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hvhalf
    _ = _ := by ring

/-- The fixed cubic coincidence ratio transfers to point-dependent
parameters with quantified relative errors, as required after (6.9).
Deriving those relative errors from the actual minor arcs remains upstream. -/
theorem cubic_ratio_parameter_perturbation
    {μ μ₁ μt μ₁t p q ε η : ℝ} (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hq : q ≠ 0)
    (hbase : |μ₁*p^3/(μ*q^3)-1| ≤ ε)
    (hpert : |μt/μ-1| ≤ η) (hpert₁ : |μ₁t/μ₁-1| ≤ η) (hη : η ≤ 1/2) :
    |μ₁t*p^3/(μt*q^3)-1| ≤ 3*ε+4*η := by
  have hμt : μt ≠ 0 := by
    intro hz
    rw [hz,zero_div] at hpert
    norm_num at hpert
    linarith only [hpert,hη]
  have he := ratio_relative_perturbation hbase hpert₁ hpert hη
  convert he using 1
  congr 1
  field_simp


/-- Relative variation of the literal cubic Taylor coefficient f'''/6,
derived from a fourth-derivative bound on the complete joining segment. -/
theorem cubicTaylorCoefficient_relative_variation
    {f : ℝ → ℝ} {a b U κ : ℝ} (hκ : 0 < κ)
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U)
    (hlower : κ ≤ |iteratedDeriv 3 f a|) :
    |(iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1| ≤ U*|b-a|/κ := by
  have hbase : iteratedDeriv 3 f a ≠ 0 := abs_pos.mp (hκ.trans_le hlower)
  have hd (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f y) y :=
    TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4) (hf y hy)
  have hdiff := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hfourth y hy)
    Set.left_mem_uIcc Set.right_mem_uIcc
  change |iteratedDeriv 3 f b-iteratedDeriv 3 f a| ≤ U*|b-a| at hdiff
  have hid : (iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1 =
      (iteratedDeriv 3 f b-iteratedDeriv 3 f a)/(iteratedDeriv 3 f a) := by field_simp
  rw [hid,abs_div]
  have hU : 0 ≤ U := (abs_nonneg _).trans (hfourth a Set.left_mem_uIcc)
  exact (div_le_div_of_nonneg_right hdiff (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) hκ hlower)


/-- The relative-variation input is discharged for the actual ANTEDB
model phase using existing third-derivative nondegeneracy and jet bounds.
The constant depends on sigma and the fixed model tolerance, not the phase
or its two evaluation points. Physical rescaling remains a later bridge. -/
theorem approximateModelPhase_cubicCoefficient_relative_variation
    {σ δ a b : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (ha : a ∈ Set.Ioo (1:ℝ) 2) (hb : b ∈ Set.Ioo (1:ℝ) 2) :
    |(iteratedDeriv 3 F b/6)/(iteratedDeriv 3 F a/6)-1| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|/
        TaoTrudgianYang2025.modelPhaseThirdLower σ := by
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo (1:ℝ) 2 := by
    rw [Set.mem_uIcc] at hy
    rcases hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 F y :=
    (TaoTrudgianYang2025.approximateModelPhase_contDiffAt hF (hseg y hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hfourth (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 4 F y| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ := by
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF (hseg y hy) 3 le_rfl
    have hr := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ.le (hseg y hy) 3
    have ht := abs_add_le (iteratedDeriv 4 F y-iteratedDeriv 3 (Expdb.modelPhase σ) y)
      (iteratedDeriv 3 (Expdb.modelPhase σ) y)
    rw [sub_add_cancel] at ht
    linarith only [he,hr,ht]
  have hlo := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ
    (TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl) ha).1
  have hlo' : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤ |iteratedDeriv 3 F a| := by
    have hraw : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤ iteratedDeriv 3 F a := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hlo
    exact hraw.trans (le_abs_self _)
  exact cubicTaylorCoefficient_relative_variation
    (TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ) hc hfourth hlo'


/-- Physical rescaling gives the actual n/M variation factor for the
cubic Taylor coefficient. This reuses the completed Heath--Brown
physical-phase entry instead of rebuilding affine derivative machinery. -/
theorem physicalModelPhase_cubicCoefficient_relative_variation
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : T ≠ 0) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    |(iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|/
        (TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  dsimp only
  rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hb,
    TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW ha]
  simp only [one_mul]
  have hcoeff : T/M^3 ≠ 0 := div_ne_zero hT (pow_ne_zero _ hM.ne')
  have hcancel (u v c : ℝ) (hc : c ≠ 0) : (c*u/6)/(c*v/6)=(u/6)/(v/6) := by
    rw [show c*u/6=c*(u/6) by ring,show c*v/6=c*(v/6) by ring,mul_div_mul_left _ _ hc]
  rw [hcancel _ _ _ hcoeff]
  have he := approximateModelPhase_cubicCoefficient_relative_variation hσ hδ hF
    (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha)
    (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hb)
  have hdist : (A+b)/M-(A+a)/M = (b-a)/M := by ring
  rw [hdist,abs_div,abs_of_pos hM] at he
  convert he using 1
  ring


/-- Fixed-base coincidence transfers to actual pointwise cubic Taylor
coefficients of two physical model phases. The relative errors are derived
from the model predicates and the physical displacement, not assumed.
The fixed-base coincidence bound is the explicit upstream input. -/
theorem physicalModelPhase_cubic_ratio_transfer
    {σ δ T M A W a b a₁ b₁ H p q ε : ℝ} {F F₁ : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hF₁ : Expdb.IsApproximateModelPhaseFunction F₁ σ 3 δ)
    (hT : T ≠ 0) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W)
    (ha₁ : a₁ ∈ Set.Ioo 0 W) (hb₁ : b₁ ∈ Set.Ioo 0 W)
    (hH : |b-a| ≤ H) (hH₁ : |b₁-a₁| ≤ H) (hq : q ≠ 0) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let f₁ := TaoTrudgianYang2025.heathBrownPhysicalPhase F₁ T M A 1
    let η := (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*H/
      (TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    η ≤ 1/2 →
    |(iteratedDeriv 3 f₁ a₁/6)*p^3/((iteratedDeriv 3 f a/6)*q^3)-1| ≤ ε →
    |(iteratedDeriv 3 f₁ b₁/6)*p^3/((iteratedDeriv 3 f b/6)*q^3)-1| ≤ 3*ε+4*η := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let f₁ := TaoTrudgianYang2025.heathBrownPhysicalPhase F₁ T M A 1
  let η := (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*H/
    (TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
  change η ≤ 1/2 → _ → _
  intro hη hbase
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha) 3 le_rfl)
  have hcoef := TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3
  have hlower := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hv : |(iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1| ≤ η := by
    apply (physicalModelPhase_cubicCoefficient_relative_variation hσ hδ hF hT hM hA hW ha hb).trans
    dsimp [η]
    gcongr
  have hv₁ : |(iteratedDeriv 3 f₁ b₁/6)/(iteratedDeriv 3 f₁ a₁/6)-1| ≤ η := by
    apply (physicalModelPhase_cubicCoefficient_relative_variation hσ hδ hF₁ hT hM hA hW ha₁ hb₁).trans
    dsimp [η]
    gcongr
  have hμ : iteratedDeriv 3 f a/6 ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hv
    norm_num at hv
    linarith only [hv,hη]
  have hμ₁ : iteratedDeriv 3 f₁ a₁/6 ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hv₁
    norm_num at hv₁
    linarith only [hv₁,hη]
  exact cubic_ratio_parameter_perturbation hμ hμ₁ hq hbase hv hv₁ hη


/-- Taylor's theorem for the actual half-curvature f''/2. This keeps the
cubic coefficient and physical displacement linked, as needed in (3.11). -/
theorem halfCurvature_first_order_remainder
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a)| ≤ U*|b-a|^2/4 := by
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 2 (iteratedDeriv 2 f) y :=
    TaoTrudgianYang2025.contDiffAt_iteratedDeriv_finite (n := 2) (j := 2) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 2 (iteratedDeriv 2 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfourth y hy
  have he := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 1 hg hgg
  have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (iteratedDeriv 2 f) 1 a b =
      iteratedDeriv 2 f a+iteratedDeriv 3 f a*(b-a) := by
    simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
  have hid : iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a) =
      (iteratedDeriv 2 f b-(iteratedDeriv 2 f a+iteratedDeriv 3 f a*(b-a)))/2 := by ring
  rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hh := div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)
  convert hh using 1
  ring


/-- The determinant-one parametrisation (3.5) gives precisely the
continuous coordinate (3.12), with all denominators linked. -/
theorem farey_curvature_coordinate_identity {μ e r v s u t : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) :
    (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) := by
  have hleft : (e*u+v*t)/(r*u+s*t)-e/r = t/(r*(r*u+s*t)) := by
    apply (div_sub_div _ _ hq hr).trans
    rw [mul_comm (r*u+s*t) r]
    congr 1
    linear_combination t*hdet
  rw [hleft]
  dsimp [minorArcCoordinate]
  have hden : r*(u/t)+s = (r*u+s*t)/t := by field_simp
  rw [hden]
  field_simp

/-- Quantitative (3.11) for the actual half-curvature values and their
rational approximation errors. The coordinate/displacement approximation
is derived from Taylor's theorem, not supplied as an entry assumption. -/
theorem minorArcCoordinate_taylor_entry
    {f : ℝ → ℝ} {a b U e r v s u t δ₀ δ₁ : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U)
    (hμ : iteratedDeriv 3 f a/6 ≠ 0)
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1)
    (hbase : iteratedDeriv 2 f a/2 = e/r+δ₀)
    (hpoint : iteratedDeriv 2 f b/2 = (e*u+v*t)/(r*u+s*t)+δ₁) :
    |(b-a)-minorArcCoordinate (iteratedDeriv 3 f a/6) r s (u/t)-
      (δ₁-δ₀)/(3*(iteratedDeriv 3 f a/6))| ≤
      U*|b-a|^2/(12*|iteratedDeriv 3 f a/6|) := by
  let μ := iteratedDeriv 3 f a/6
  have he := halfCurvature_first_order_remainder hf hfourth
  have hg := farey_curvature_coordinate_identity hμ hr ht hq hdet
  change (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) at hg
  rw [hbase,hpoint] at he
  change |(e*u+v*t)/(r*u+s*t)+δ₁-(e/r+δ₀)-3*μ*(b-a)| ≤ U*|b-a|^2/4 at he
  have hnum : (e*u+v*t)/(r*u+s*t)+δ₁-(e/r+δ₀)-3*μ*(b-a) =
      -(3*μ*((b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ))) := by
    have hc : (3*μ)*((δ₁-δ₀)/(3*μ)) = δ₁-δ₀ :=
      mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hμ)
    linear_combination hg-hc
  rw [hnum,abs_neg,abs_mul] at he
  change |(b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ)| ≤ _
  have hpos : 0 < |3*μ| := abs_pos.mpr (mul_ne_zero (by norm_num) hμ)
  have hh : |(b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ)| ≤
      (U*|b-a|^2/4)/|3*μ| :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using he)
  apply hh.trans_eq
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  ring


/-- Equation (3.11) for the actual physical model phase: the fourth-
derivative and cubic-coefficient scales cancel to give n^2/M. Only the
two rational half-curvature approximations remain as source inputs. -/
theorem physicalModelPhase_minorArcCoordinate_taylor_entry
    {σ δ T M A W a b e r v s u t δ₀ δ₁ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W)
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f a/2 = e/r+δ₀ →
    iteratedDeriv 2 f b/2 = (e*u+v*t)/(r*u+s*t)+δ₁ →
    |(b-a)-minorArcCoordinate (iteratedDeriv 3 f a/6) r s (u/t)-
      (δ₁-δ₀)/(3*(iteratedDeriv 3 f a/6))| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let C := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  change _ → _ → _
  intro hbase hpoint
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha) 3 le_rfl)
  have hC : 0 ≤ C := add_nonneg
    (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hf4 (y : ℝ) (hy : y ∈ Set.uIcc a b) : |iteratedDeriv 4 f y| ≤ T/M^4*C := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW (hseg y hy)
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 3 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ.le hyp 3
    have htri := abs_add_le (iteratedDeriv 4 F ((A+y)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 F ((A+y)/M)| ≤ C := by dsimp [C]; linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW (hseg y hy),
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^4)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hlo : κ ≤ iteratedDeriv 3 F ((A+a)/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ
      (TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl)
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hμlo : (T/M^3)*κ/6 ≤ iteratedDeriv 3 f a/6 := by
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW ha,one_mul]
    gcongr
  have hμ : 0 < iteratedDeriv 3 f a/6 := lt_of_lt_of_le (by positivity) hμlo
  have he := minorArcCoordinate_taylor_entry hc hf4 hμ.ne' hr ht hq hdet hbase hpoint
  apply he.trans
  rw [abs_of_pos hμ]
  calc
    (T/M^4*C)*|b-a|^2/(12*(iteratedDeriv 3 f a/6)) ≤
        (T/M^4*C)*|b-a|^2/(12*((T/M^3)*κ/6)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hμlo (by norm_num))
    _ = C*|b-a|^2/(2*κ*M) := by field_simp; ring


/-- Construct the integer centre used in Section 3 by nearest-integer
rounding. Its curvature error is derived, including the factor 1/4. -/
theorem halfCurvature_round_error {f : ℝ → ℝ} {W x U : ℝ}
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hf : ∀ y ∈ Set.Ioo 0 W, ContDiffAt ℝ 3 f y)
    (hthird : ∀ y ∈ Set.Ioo 0 W, |iteratedDeriv 3 f y| ≤ U) :
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/4 := by
  have hd : |(round x:ℝ)-x| ≤ 1/2 := by simpa only [abs_sub_comm] using abs_sub_round x
  have hm : (round x:ℝ) ∈ Set.Ioo 0 W := by
    have hh := abs_le.mp hd
    constructor <;> linarith [hx.1,hx.2,hh.1,hh.2]
  have hx0 : x ∈ Set.Ioo 0 W := by constructor <;> linarith [hx.1,hx.2]
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc x (round x:ℝ)) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hx0.1.trans_le hy.1,hy.2.trans_lt hm.2⟩
    · exact ⟨hm.1.trans_le hy.1,hy.2.trans_lt hx0.2⟩
  have hder (y : ℝ) (hy : y ∈ Set.uIcc x (round x:ℝ)) :
      HasDerivAt (fun z => iteratedDeriv 2 f z/2) (iteratedDeriv 3 f y/2) y :=
    (TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3)
      (hf y (hseg y hy))).div_const 2
  have he := (convex_uIcc x (round x:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hder y hy).hasDerivWithinAt)
    (C := U/2)
    (fun y hy => by
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact div_le_div_of_nonneg_right (hthird y (hseg y hy)) (by norm_num))
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hU : 0 ≤ U := (abs_nonneg _).trans (hthird x hx0)
  refine ⟨hm,?_⟩
  change |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/2*|(round x:ℝ)-x| at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hd hU])


/-- The integer-centre error for an actual ANTEDB physical phase. -/
theorem physicalModelPhase_halfCurvature_round_error
    {σ δ T M A W x : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  have hc (y : ℝ) (hy : y ∈ Set.Ioo 0 W) : ContDiffAt ℝ 3 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self hy)).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hthird (y : ℝ) (hy : y ∈ Set.Ioo 0 W) :
      |iteratedDeriv 3 f y| ≤ T/M^3*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ) := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hy
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 2 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ hyp 2
    have htri := abs_add_le (iteratedDeriv 3 F ((A+y)/M)-iteratedDeriv 2 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 2 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 3 F ((A+y)/M)| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hy,
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^3)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have he := halfCurvature_round_error hx hc hthird
  refine ⟨he.1,he.2.trans_eq ?_⟩
  ring


/-- Rational curvature values in the actual phase range produce integer
minor-arc centres by the intermediate value theorem and rounding. -/
theorem physicalModelPhase_exists_rounded_halfCurvature_center
    {σ δ T M A W l v q : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hl : l ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hv : v ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    q ∈ Set.uIcc (iteratedDeriv 2 f l/2) (iteratedDeriv 2 f v/2) →
    ∃ x ∈ Set.uIcc l v, iteratedDeriv 2 f x/2=q ∧
      (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-q| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  change _ → _
  intro hq
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc l v) : y ∈ Set.Ioo (1/2:ℝ) (W-1/2) := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hl.1.trans_le hy.1,hy.2.trans_lt hv.2⟩
    · exact ⟨hv.1.trans_le hy.1,hy.2.trans_lt hl.2⟩
  have hc : ContinuousOn (fun y => iteratedDeriv 2 f y/2) (Set.uIcc l v) := by
    intro y hy
    have hy0 : y ∈ Set.Ioo 0 W := by
      have hh := hseg y hy
      constructor <;> linarith [hh.1,hh.2]
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    have hf3 : ContDiffAt ℝ 3 f y :=
      ((hcf y (Set.Ioo_subset_Icc_self hy0)).contDiffAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy0) Set.Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact ((TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite
      (by norm_num : 2 < 3) hf3).div_const 2).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hfx⟩ := intermediate_value_uIcc hc hq
  have he := physicalModelPhase_halfCurvature_round_error hσ hF hT hM hA hW (hseg x hx)
  refine ⟨x,hx,hfx,he.1,?_⟩
  rw [← hfx]
  exact he.2


/-- The discrete-to-continuous entry (3.11) for the constructed integer
centres. Both rational approximation errors are discharged by rounding;
the final bound has the source form O(1+n^2/M). -/
theorem physicalModelPhase_rounded_minorArcCoordinate_entry
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    let μ := iteratedDeriv 3 f (round x₀)/6
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n-minorArcCoordinate μ r s (u/t)| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
        TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|n|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let μ := iteratedDeriv 3 f a/6
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  let δ₁ := iteratedDeriv 2 f b/2-(e*u+v*t)/(r*u+s*t)
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₁
  have hδ₀ : |δ₀| ≤ T*C₂/(4*M^3) := by simpa only [hbase] using hround₀.2
  have hδ₁ : |δ₁| ≤ T*C₂/(4*M^3) := by simpa only [hpoint] using hround₁.2
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hround₀.1) 3 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg
    (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hlo : κ ≤ iteratedDeriv 3 F ((A+a)/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ hF₂
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hround₀.1)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hμlo : (T/M^3)*κ/6 ≤ μ := by
    dsimp only [μ,f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hround₀.1,one_mul]
    gcongr
  have hμ : 0 < μ := lt_of_lt_of_le (by positivity) hμlo
  have hde : |δ₁-δ₀| ≤ T*C₂/(2*M^3) := by
    have hh := abs_add_le δ₁ (-δ₀)
    rw [abs_neg,← sub_eq_add_neg] at hh
    calc
      |δ₁-δ₀| ≤ T*C₂/(4*M^3)+T*C₂/(4*M^3) := hh.trans (add_le_add hδ₁ hδ₀)
      _ = T*C₂/(2*M^3) := by ring
  have hpert : |(δ₁-δ₀)/(3*μ)| ≤ C₂/κ := by
    rw [abs_div,abs_of_pos (mul_pos (by norm_num) hμ)]
    calc
      |δ₁-δ₀|/(3*μ) ≤ (T*C₂/(2*M^3))/(3*((T/M^3)*κ/6)) :=
        div_le_div₀ (by positivity) hde (by positivity)
          (mul_le_mul_of_nonneg_left hμlo (by norm_num))
      _ = C₂/κ := by field_simp; ring
  have he := physicalModelPhase_minorArcCoordinate_taylor_entry hσ hδ hF hT hM hA hW
    hround₀.1 hround₁.1 hr ht hq hdet
    (δ₀ := δ₀) (δ₁ := δ₁) (by dsimp [δ₀]; ring) (by dsimp [δ₁]; ring)
  have htri := abs_add_le ((b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ))
    ((δ₁-δ₀)/(3*μ))
  rw [sub_add_cancel] at htri
  apply htri.trans
  linarith only [he,hpert]

/-- Eliminate the cubic coefficient between the first-derivative Taylor
expansion and the half-curvature expansion, as in (3.13). The explicit
5/12 constant suffices for the source's O(n^3 max |f''''|) remainder. -/
theorem firstDerivative_halfCurvature_remainder
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤ 5*U*|b-a|^3/12 := by
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 3 (iteratedDeriv 1 f) y :=
    TaoTrudgianYang2025.contDiffAt_iteratedDeriv_finite (n := 3) (j := 1) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 3 (iteratedDeriv 1 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfourth y hy
  have he₁ := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 2 hg hgg
  have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (iteratedDeriv 1 f) 2 a b =
      iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+iteratedDeriv 3 f a*(b-a)^2/2 := by
    simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he₁
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he₁
  have he₂ := halfCurvature_first_order_remainder hf hfourth
  have hid : iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2) =
      (iteratedDeriv 1 f b-(iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+
        iteratedDeriv 3 f a*(b-a)^2/2))-
      (b-a)*(iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
        3*(iteratedDeriv 3 f a/6)*(b-a)) := by ring
  rw [hid]
  have ht := abs_add_le
    (iteratedDeriv 1 f b-(iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+
      iteratedDeriv 3 f a*(b-a)^2/2))
    (-((b-a)*(iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a))))
  rw [abs_neg,abs_mul,← sub_eq_add_neg] at ht
  exact ht.trans ((add_le_add he₁ (mul_le_mul_of_nonneg_left he₂ (abs_nonneg _))).trans_eq (by ring))


/-- Physical-scale first-derivative residual; the fourth-derivative
bound and smoothness are derived from the actual model predicate. -/
theorem physicalModelPhase_firstDerivative_halfCurvature_remainder
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤
      5*T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|^3/(12*M^4) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hf4 (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 4 f y| ≤ T/M^4*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ) := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW (hseg y hy)
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 3 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ hyp 3
    have htri := abs_add_le (iteratedDeriv 4 F ((A+y)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 F ((A+y)/M)| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW (hseg y hy),
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^4)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  exact (firstDerivative_halfCurvature_remainder hc hf4).trans_eq (by ring)


/-- The actual residual gamma in (3.13)--(3.14), with the curvature
approximation errors discharged for rounded integer centres. -/
theorem physicalModelPhase_rounded_firstDerivative_residual
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let q := r*u+s*t
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))| ≤
      |q| * (T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|n|/(2*M^3)+
        5*T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|n|^3/(12*M^4)) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let q := r*u+s*t
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ hF₂ hT hM hA hW hx₁
  have herr₀ : |iteratedDeriv 2 f a/2-e/r| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
    simpa only [hbase] using hround₀.2
  have herr₁ : |iteratedDeriv 2 f b/2-(e*u+v*t)/q| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
    simpa only [hpoint] using hround₁.2
  have hrat : (e*u+v*t)/q-e/r = t/(r*q) := by
    apply (div_sub_div _ _ hq hr).trans
    rw [mul_comm q r]
    congr 1
    dsimp [q]
    linear_combination t*hdet
  have hcurv : |iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q))| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(2*M^3) := by
    have hid : iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q)) =
        (iteratedDeriv 2 f a/2-e/r)+(iteratedDeriv 2 f b/2-(e*u+v*t)/q) := by
      linear_combination hrat
    rw [hid]
    apply (abs_add_le _ _).trans
    exact (add_le_add herr₀ herr₁).trans_eq (by ring)
  have he := physicalModelPhase_firstDerivative_halfCurvature_remainder hσ hF hT hM hA hW
    hround₀.1 hround₁.1
  have hid : iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*(b-a)/r-(b-a)*t/(r*q) =
      (iteratedDeriv 1 f b-iteratedDeriv 1 f a-
        (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2))+
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q))) := by ring
  change |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*(b-a)/r-(b-a)*t/(r*q))| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact (add_le_add he (mul_le_mul_of_nonneg_left hcurv (abs_nonneg _))).trans_eq (by ring)


/-- The exact arithmetic cancellation in (3.15)--(3.16). The residual
is the actual first-derivative discrepancy, not an independent input. -/
theorem farey_firstDerivative_residual_identity
    {e r v s u t n c θ d₀ d₁ : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1)
    (hd₀ : r*d₀=c+θ) :
    let q := r*u+s*t
    let γ := q*(d₁-d₀-2*e*n/r-n*t/(r*q))
    q*d₁ = c*u+2*n*(e*u+v*t)+(c*s-n)*t/r+θ*q/r+γ := by
  dsimp only
  have hfrac : (r*u+s*t)*(n*t/(r*(r*u+s*t)))=n*t/r := by field_simp
  rw [mul_sub,mul_sub,mul_sub,hfrac]
  field_simp
  linear_combination (r*u+s*t)*hd₀-2*n*t*hdet


/-- The integer label and centred fractional part in (3.15)--(3.16)
come from the actual rounded derivative values. -/
theorem farey_firstDerivative_integer_label
    {e r v s u t n : ℤ} {d₀ d₁ : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let q : ℝ := r*u+s*t
    let c := round ((r:ℝ)*d₀)
    let θ := (r:ℝ)*d₀-c
    let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
    let H := ((c:ℝ)*s-n)*t/r+θ*q/r+γ
    round (q*d₁) = c*u+2*n*(e*u+v*t)+round H ∧
      q*d₁-round (q*d₁) = H-round H := by
  let q : ℝ := r*u+s*t
  let c := round ((r:ℝ)*d₀)
  let θ := (r:ℝ)*d₀-c
  let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
  let H := ((c:ℝ)*s-n)*t/r+θ*q/r+γ
  let j : ℤ := c*u+2*n*(e*u+v*t)
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have hq' : (r:ℝ)*u+s*t ≠ 0 := by exact_mod_cast hq
  have hdet' : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hid : q*d₁=(j:ℝ)+H := by
    have hh := farey_firstDerivative_residual_identity hr' hq' hdet'
      (n := (n:ℝ)) (c := (c:ℝ)) (θ := θ) (d₀ := d₀) (d₁ := d₁)
      (by dsimp [θ]; ring)
    dsimp only at hh
    dsimp [j,H,γ,q]
    push_cast
    linear_combination hh
  have hj : round (q*d₁)=j+round H := by rw [hid,round_intCast_add]
  refine ⟨hj,?_⟩
  change q*d₁-(round (q*d₁):ℝ)=H-(round H:ℝ)
  rw [hj,Int.cast_add,hid]
  ring


/-- The cancellation underlying (5.2)--(5.6), retaining the essential
base-curvature correction 2*delta/(3*mu). The remaining error is quadratic
in n-G, plus the genuine first-derivative Taylor remainder. -/
theorem corrected_nonlinear_residual_identity
    {μ r s u t n δ E : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(E+2*δ*n+3*μ*n^2-n*t/(r*q))
    γ-n*t/r-t/r*(2*δ/(3*μ)-G) = q*(E+(n-G)*(3*μ*(n-G)+2*δ)) := by
  have hG : minorArcCoordinate μ r s (u/t) = t/(3*μ*r*(r*u+s*t)) := by
    dsimp [minorArcCoordinate]
    have hden : r*(u/t)+s=(r*u+s*t)/t := by field_simp
    rw [hden]
    field_simp
  dsimp only
  rw [hG]
  field_simp
  ring


/-- The Section 5 cancellation consumes the actual phase derivatives.
The free remainder variable in the algebraic identity is discharged by
Taylor's theorem; no bound on the combined residual is assumed. -/
theorem firstDerivative_corrected_nonlinear_residual_bound
    {f : ℝ → ℝ} {a b U e r s u t : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U)
    (hμ : iteratedDeriv 3 f a/6 ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    |γ-n*t/r-t/r*(2*δ/(3*μ)-G)| ≤
      |q| * (U*|n|^3/6+|n-G| * (3*|μ| * |n-G|+2*|δ|)) := by
  let n := b-a
  let μ := iteratedDeriv 3 f a/6
  let δ := iteratedDeriv 2 f a/2-e/r
  let q := r*u+s*t
  let G := minorArcCoordinate μ r s (u/t)
  let E := iteratedDeriv 1 f b-(iteratedDeriv 1 f a+iteratedDeriv 2 f a*n+3*μ*n^2)
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 3 (iteratedDeriv 1 f) y :=
    TaoTrudgianYang2025.contDiffAt_iteratedDeriv_finite (n := 3) (j := 1) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 3 (iteratedDeriv 1 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfourth y hy
  have hE : |E| ≤ U*|n|^3/6 := by
    have he := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 2 hg hgg
    have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (iteratedDeriv 1 f) 2 a b =
        iteratedDeriv 1 f a+iteratedDeriv 2 f a*n+3*μ*n^2 := by
      dsimp [n,μ]
      simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
      ring
    rw [hpoly] at he
    norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
    exact he
  have hid : q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q)) =
      q*(E+2*δ*n+3*μ*n^2-n*t/(r*q)) := by dsimp [E,δ]; ring
  have hc := corrected_nonlinear_residual_identity hμ hr ht hq (n := n) (δ := δ) (E := E)
  change |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))-
    n*t/r-t/r*(2*δ/(3*μ)-G)| ≤ _
  rw [hid,hc,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply add_le_add hE
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (n-G))
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact le_rfl


/-- Physical Section 5 cancellation for actual rounded centres. All
Taylor, cubic-coefficient, curvature-rounding and coordinate-error inputs
are derived from the model phase; the correction in beta is retained. -/
theorem physicalModelPhase_corrected_nonlinear_residual_bound
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let D := C₂/κ+C₃*|n|^2/(2*κ*M)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)| ≤
      |q| * (T/M^3) * (C₃*|n|^3/(6*M)+C₂/2*D*(D+1)) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let n := b-a
  let μ := iteratedDeriv 3 f a/6
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  let q := r*u+s*t
  let G := minorArcCoordinate μ r s (u/t)
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  let D := C₂/κ+C₃*|n|^2/(2*κ*M)
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₁
  have hcoord : |n-G| ≤ D := physicalModelPhase_rounded_minorArcCoordinate_entry
    hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint
  have hD : 0 ≤ D := (abs_nonneg _).trans hcoord
  have hδ₀ : |δ₀| ≤ T*C₂/(4*M^3) := by simpa only [hbase] using hround₀.2
  have hμ : μ ≠ 0 := by
    have hv := physicalModelPhase_cubicCoefficient_relative_variation hσ hδ hF hT.ne' hM hA hW
      hround₀.1 hround₀.1
    change |μ/μ-1| ≤ _ at hv
    intro hz
    rw [hz,div_zero] at hv
    norm_num at hv
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hround₀.1.1.trans_le hy.1,hy.2.trans_lt hround₁.1.2⟩
    · exact ⟨hround₁.1.1.trans_le hy.1,hy.2.trans_lt hround₀.1.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hjet (p : ℕ) (hp : p ≤ 3) (y : ℝ) (hy : y ∈ Set.Ioo 0 W) :
      |iteratedDeriv (p+1) f y| ≤ T/M^(p+1)*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ p+δ) := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hy
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp p hp
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ.le hyp p
    have htri := abs_add_le (iteratedDeriv (p+1) F ((A+y)/M)-iteratedDeriv p (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv p (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv (p+1) F ((A+y)/M)| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ p+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hy,
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^(p+1))]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hμhi : |μ| ≤ T/M^3*C₂/6 := by
    dsimp only [μ]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 6)]
    exact div_le_div_of_nonneg_right (hjet 2 (by norm_num) a hround₀.1) (by norm_num)
  have he := firstDerivative_corrected_nonlinear_residual_bound hc
    (fun y hy => hjet 3 le_rfl y (hseg y hy)) hμ hr ht hq (e := e)
  apply he.trans
  have hC₂ : 0 ≤ C₂ := by
    have hh := (abs_nonneg _).trans (hjet 2 (by norm_num) a hround₀.1)
    exact nonneg_of_mul_nonneg_right hh (by positivity : 0 < T/M^3)
  calc
    |q| * ((T/M^4*C₃)*|n|^3/6+|n-G| * (3*|μ| * |n-G|+2*|δ₀|)) ≤
        |q| * ((T/M^4*C₃)*|n|^3/6+D*(3*(T/M^3*C₂/6)*D+2*(T*C₂/(4*M^3)))) := by
      gcongr
    _ = |q| * (T/M^3) * (C₃*|n|^3/(6*M)+C₂/2*D*(D+1)) := by ring


/-- The squared coordinate-error budget costs only 1+n^3/M on a
physical interval of length at most M. This is the absorption needed in
(5.3), not an assumed smallness of the nonlinear residual. -/
theorem coordinate_error_quadratic_budget {A B n M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) :
    (A+B*n^2/M)*(A+B*n^2/M+1) ≤
      (A*(A+1)+(2*A+1)*B+B^2)*(1+n^3/M) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hlinear : n^2/M ≤ 1+n^3/M := by
    apply (div_le_iff₀ hM0).mpr
    rw [show (1+n^3/M)*M=M+n^3 by field_simp]
    by_cases hn1 : n ≤ 1
    · have hh := mul_le_mul_of_nonneg_left hn1 hn
      nlinarith only [hh,hn1,hM,pow_nonneg hn 3]
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hn1) (sq_nonneg n)
      nlinarith only [hh,hM]
  have hquadratic : (n^2/M)^2 ≤ n^3/M := by
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : 0 < M^2) hM0).mpr
    have hh := mul_le_mul_of_nonneg_left hnM (show 0 ≤ n^3*M by positivity)
    nlinarith only [hh]
  have hb1 := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ (2*A+1)*B by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hquadratic (sq_nonneg B)
  have ha0 : 0 ≤ A*(A+1)*(n^3/M) := by positivity
  have hid : (A+B*n^2/M)*(A+B*n^2/M+1) =
      A*(A+1)+(2*A+1)*B*(n^2/M)+B^2*(n^2/M)^2 := by ring
  rw [hid]
  nlinarith only [hb1,hb2,ha0,sq_nonneg B]


/-- The linked physical scale and (5.3) absorb the complete cancellation
budget into the Fourth-Condition scale 1/N, with an explicit constant. -/
theorem corrected_residual_source_scale_budget {A B C₂ C₃ n M N R T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hn : 0 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) (hN : 0 < N)
    (hR : 1 ≤ R) (hT : 0 < T) (hscale : T*N*R^2=M^3) (hcube : n^3 ≤ M*R^2) :
    let K := A*(A+1)+(2*A+1)*B+B^2
    (T/M^3)*(C₃*n^3/(6*M)+C₂/2*(A+B*n^2/M)*(A+B*n^2/M+1)) ≤
      (C₃/3+C₂*K)/N := by
  let K := A*(A+1)+(2*A+1)*B+B^2
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hquad := coordinate_error_quadratic_budget hA hB hn hM hnM
  have hw : n^3/M ≤ R^2 := (div_le_iff₀ hM0).mpr (by simpa only [mul_comm] using hcube)
  have hR2 : 1 ≤ R^2 := by nlinarith only [hR,sq_nonneg (R-1)]
  have hsum : 1+n^3/M ≤ 2*R^2 := by linarith only [hw,hR2]
  have hterm : C₃*n^3/(6*M)+C₂/2*(A+B*n^2/M)*(A+B*n^2/M+1) ≤
      (C₃/6+C₂*K/2)*(1+n^3/M) := by
    have hh := mul_le_mul_of_nonneg_left hquad (show 0 ≤ C₂/2 by positivity)
    have hc : 0 ≤ C₃/6 := by positivity
    calc
      _ ≤ C₃*n^3/(6*M)+C₂/2*(K*(1+n^3/M)) := by nlinarith only [hh]
      _ ≤ _ := by
        rw [show (C₃/6+C₂*K/2)*(1+n^3/M) =
          C₃*n^3/(6*M)+C₂/2*(K*(1+n^3/M))+C₃/6 by ring]
        linarith only [hc]
  calc
    (T/M^3)*(C₃*n^3/(6*M)+C₂/2*(A+B*n^2/M)*(A+B*n^2/M+1)) ≤
        (T/M^3)*((C₃/6+C₂*K/2)*(2*R^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hterm.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = (C₃/3+C₂*K)/N := by
      apply (eq_div_iff hN.ne').mpr
      rw [show (T/M^3)*((C₃/6+C₂*K/2)*(2*R^2))*N =
        (C₃/3+C₂*K)*(T*N*R^2)/M^3 by ring,hscale]
      field_simp


/-- Uniform constant for the Section 5 error, depending only on the
model exponent and tolerance. -/
noncomputable def nonlinearResidualConstant (σ δ : ℝ) : ℝ :=
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  let A₀ := C₂/κ
  let B₀ := C₃/(2*κ)
  C₃/3+C₂*(A₀*(A₀+1)+(2*A₀+1)*B₀+B₀^2)

/-- The actual physical Section 5 error has the Fourth-Condition scale
q/N. The relation T*N*R^2=M^3 and source displacement restriction (5.3)
are explicit; the needed displacement bound n<=M follows from the window. -/
theorem physicalModelPhase_corrected_residual_le_fourth_scale
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |n|^3 ≤ M*R^2 →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)| ≤ nonlinearResidualConstant σ δ*|q|/N := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let n := b-a
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  change _ → _ → _ → _
  intro hbase hpoint hcube
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM0 hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM0 hA hW hx₁
  have hnM : |n| ≤ M := by
    have hWM : W ≤ M := by linarith only [hA,hW]
    apply abs_le.mpr
    dsimp [n,a,b]
    constructor <;> linarith only [hround₀.1.1,hround₀.1.2,hround₁.1.1,hround₁.1.2,hWM]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM0 hA hW hround₀.1) 3 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hb := corrected_residual_source_scale_budget (A := C₂/κ) (B := C₃/(2*κ))
    (by positivity) (by positivity) hC₂ hC₃ (abs_nonneg n) hM hnM hN hR hT hscale hcube
  have he := physicalModelPhase_corrected_nonlinear_residual_bound
    hσ hδ hF hT hM0 hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (r*u+s*t))
  convert hh using 1 <;> dsimp [nonlinearResidualConstant,C₂,C₃,κ,n,a,b] <;> ring


/-- The literal one-arc expression in (5.2), including the base-curvature
correction in its coefficient of t. -/
noncomputable def roundedMinorArcLinearForm (f : ℝ → ℝ) (x₀ e r s u t : ℝ) : ℝ :=
  let a : ℝ := round x₀
  let d₀ := iteratedDeriv 1 f a
  let μ := iteratedDeriv 3 f a/6
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  (r*d₀-round (r*d₀))*u+(d₀*s+2*δ₀/(3*μ*r))*t-t*rationalBranch μ r s (u/t)

/-- Exact linearization identity, prior to any analytic estimate. -/
theorem firstDerivative_linearization_identity
    {f : ℝ → ℝ} {x₀ x₁ e r v s u t : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    q*iteratedDeriv 1 f b-
      (round (r*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t))-
      roundedMinorArcLinearForm f x₀ e r s u t =
      γ-n*t/r-t/r*(2*δ₀/(3*μ)-minorArcCoordinate μ r s (u/t)) := by
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let μ := iteratedDeriv 3 f a/6
  have hb : rationalBranch μ r s (u/t)=minorArcCoordinate μ r s (u/t)/r := by
    dsimp [rationalBranch,minorArcCoordinate]
    rw [div_div]
    congr 1
    ring
  have hh := farey_firstDerivative_residual_identity hr hq hdet
    (n := b-a) (c := round (r*iteratedDeriv 1 f a))
    (θ := r*iteratedDeriv 1 f a-round (r*iteratedDeriv 1 f a))
    (d₀ := iteratedDeriv 1 f a) (d₁ := iteratedDeriv 1 f b) (by ring)
  dsimp only at hh ⊢
  rw [hh]
  dsimp only [roundedMinorArcLinearForm]
  rw [hb]
  dsimp only [a,b,μ]
  field_simp [hr]
  ring


/-- Actual rounded physical phases produce the nonlinear expression
and its integer label at the required q/N scale. No linearization-error
bound, Taylor remainder or rounding error is assumed. -/
theorem physicalModelPhase_rounded_linearization
    {σ δ T M N R A W x₀ x₁ : ℝ} {e r v s u t : ℤ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a := round x₀
    let b := round x₁
    let n := b-a
    let q : ℝ := r*u+s*t
    let j := round ((r:ℝ)*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t)
    iteratedDeriv 2 f x₀/2=(e:ℝ)/r →
    iteratedDeriv 2 f x₁/2=((e:ℝ)*u+v*t)/q →
    |(n:ℝ)|^3 ≤ M*R^2 →
    |q*iteratedDeriv 1 f b-j-roundedMinorArcLinearForm f x₀ e r s u t| ≤
      nonlinearResidualConstant σ δ*|q|/N := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hq' : (r:ℝ)*u+s*t ≠ 0 := by exact_mod_cast hq
  have hdet' : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  change _ → _ → _ → _
  intro hbase hpoint hcube
  have hcube' : |(round x₁:ℝ)-(round x₀:ℝ)|^3 ≤ M*R^2 := by
    simpa only [Int.cast_sub] using hcube
  have he := physicalModelPhase_corrected_residual_le_fourth_scale
    hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr' ht' hq' hdet' hbase hpoint hcube'
  have hid := firstDerivative_linearization_identity (f := f) (x₀ := x₀) (x₁ := x₁) hr' hq' hdet'
  dsimp only at he hid ⊢
  push_cast
  rw [hid]
  exact he


/-- Comparing two actual centred derivatives transports their Fourth
Condition to the corresponding nonlinear expressions and integer labels. -/
theorem rounded_linearization_pair_bound {z z₁ L L₁ E E₁ Δ : ℝ} {j j₁ : ℤ}
    (hL : |z-j-L| ≤ E) (hL₁ : |z₁-j₁-L₁| ≤ E₁)
    (hfourth : |(z-round z)-(z₁-round z₁)| ≤ Δ) :
    |(L-L₁)-((round z-j)-(round z₁-j₁):ℤ)| ≤ Δ+E+E₁ := by
  have hid : (L-L₁)-((round z-j)-(round z₁-j₁):ℤ) =
      ((z-round z)-(z₁-round z₁))-(z-j-L)+(z₁-j₁-L₁) := by
    push_cast
    ring
  rw [hid]
  have ht := abs_add_le ((z-round z)-(z₁-round z₁)) (-(z-j-L))
  rw [abs_neg,← sub_eq_add_neg] at ht
  exact (abs_add_le _ _).trans
    (add_le_add (ht.trans (add_le_add hfourth hL)) hL₁)


/-- Source (5.4)--(5.6) from a pair of actual physical model phases.
The Fourth Condition is on their centred derivatives; all nonlinear
linearization errors and both integer labels are derived. -/
theorem physicalModelPhase_fourth_condition_nonlinear
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun i => round (x₁ i)
    let n := fun i => b i-a i
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let z := fun i => q i*iteratedDeriv 1 (f i) (b i)
    let j := fun i => round ((r i:ℝ)*d₀ i)*u+2*n i*(e i*u+v i*t)
    let h := (round (z 0)-j 0)-(round (z 1)-j 1)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^3 ≤ M*R^2) →
    |(z 0-round (z 0))-(z 1-round (z 1))| ≤ Δ →
    |(θ 0-θ 1)*u+(β₀ 0-β₀ 1)*t-
      (t:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) ((u:ℝ)/t)-h| ≤
      Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N := by
  let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
  let q := fun i => (r i:ℝ)*u+s i*t
  let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*u+
    2*(round (x₁ i)-round (x₀ i))*(e i*u+v i*t)
  let z := fun i => q i*iteratedDeriv 1 (f i) (round (x₁ i))
  let L := fun i => roundedMinorArcLinearForm (f i) (x₀ i) (e i) (r i) (s i) u t
  change _ → _ → _ → _ → _
  intro hbase hpoint hcube hfourth
  have hL (i : Fin 2) : |z i-j i-L i| ≤ nonlinearResidualConstant σ δ*|q i|/N :=
    physicalModelPhase_rounded_linearization hσ hδ (hF i) hT hM hN hR hscale
      (hA i) (hW i) (hx₀ i) (hx₁ i) (hr i) ht (hq i) (hdet i) (hbase i) (hpoint i) (hcube i)
  have he := rounded_linearization_pair_bound (hL 0) (hL 1) hfourth
  have hid : L 0-L 1 =
      (((r 0:ℝ)*iteratedDeriv 1 (f 0) (round (x₀ 0))-round ((r 0:ℝ)*iteratedDeriv 1 (f 0) (round (x₀ 0))))-
        ((r 1:ℝ)*iteratedDeriv 1 (f 1) (round (x₀ 1))-round ((r 1:ℝ)*iteratedDeriv 1 (f 1) (round (x₀ 1)))))*u+
      (iteratedDeriv 1 (f 0) (round (x₀ 0))*s 0+
        2*(iteratedDeriv 2 (f 0) (round (x₀ 0))/2-(e 0:ℝ)/r 0)/(3*(iteratedDeriv 3 (f 0) (round (x₀ 0))/6)*r 0)-
        (iteratedDeriv 1 (f 1) (round (x₀ 1))*s 1+
        2*(iteratedDeriv 2 (f 1) (round (x₀ 1))/2-(e 1:ℝ)/r 1)/(3*(iteratedDeriv 3 (f 1) (round (x₀ 1))/6)*r 1)))*t-
      (t:ℝ)*rationalPhase (iteratedDeriv 3 (f 0) (round (x₀ 0))/6) (r 0) (s 0)
        (iteratedDeriv 3 (f 1) (round (x₀ 1))/6) (r 1) (s 1) ((u:ℝ)/t) := by
    dsimp [L,roundedMinorArcLinearForm,rationalPhase]
    ring
  rw [hid] at he
  exact he.trans_eq (by ring)


/-- Positivity of the explicit source-error constant. -/
theorem nonlinearResidualConstant_nonneg {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ nonlinearResidualConstant σ δ := by
  have h₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 2
  have h₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3
  have hκ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  dsimp [nonlinearResidualConstant]
  positivity


/-- The physical cubic coefficient at an actual rounded centre is
strictly positive, derived from the model's third-derivative lower bound. -/
theorem physicalModelPhase_rounded_cubicCoefficient_pos
    {σ δ T M A W x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    0 < iteratedDeriv 3 (TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1) (round x)/6 := by
  have hr := (physicalModelPhase_halfCurvature_round_error hσ.le hF hT hM hA hW hx).1
  have hlo : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤
      iteratedDeriv 3 F ((A+(round x:ℝ))/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hr)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hp := lt_of_lt_of_le (TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ) hlo
  rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hr,one_mul]
  positivity


/-- The actual paired Fourth Condition feeds the existing complete-sector
rigidity theorem. Geometry, cardinality and the Third Condition remain
explicit upstream inputs; the nonlinear residual and labels do not. -/
theorem physicalModelPhase_sector_integer_labels
    {K : ℕ} {σ δ T M N R Δ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+2*n p i*(e i*p.1+v i*p.2)
    let h := fun p => (round (z p 0)-j p 0)-(round (z p 1)-j p 1)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, r i*p.1+s i*p.2 ≠ 0) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-round (z p 0))-(z p 1-round (z p 1))| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, h p=p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) := by
  let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
  let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
  let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
  let θ := fun i => (r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i))-
    round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))
  let β₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))*s i+
    2*(iteratedDeriv 2 (f i) (round (x₀ i))/2-(e i:ℝ)/r i)/(3*μ i*r i)
  let α := θ 0-θ 1
  let β := β₀ 0-β₀ 1
  let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
  let z := fun p i => q p i*iteratedDeriv 1 (f i) (round (x₁ p i))
  let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*p.1+
    2*(round (x₁ p i)-round (x₀ i))*(e i*p.1+v i*p.2)
  let h := fun p => (round (z p 0)-j p 0)-(round (z p 1)-j p 1)
  let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hbase hx₁ hq hpoint hcube hfourth hqbound hden hden₁ hratio hcard hlarge
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hF₂ (i : Fin 2) := TaoTrudgianYang2025.approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hμ (i : Fin 2) : 0 < μ i := physicalModelPhase_rounded_cubicCoefficient_pos
    hσ hδ (hF₂ i) hT hM0 (hA i) (hW i) (hx₀ i)
  have hr' (i : Fin 2) : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error (hF 0)
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM0 (hA 0) (hW 0)
        (physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0) hT hM0 (hA 0) (hW 0) (hx₀ 0)).1)
      3 le_rfl)
  have hC := nonlinearResidualConstant_nonneg hσ hδ0
  have hη₀ : 0 ≤ η₀ := by dsimp [η₀]; positivity
  have hnear (p : ℤ × ℤ) (hp : p ∈ S) :
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
        ((p.1:ℝ)/(p.2:ℝ))-h p| ≤ η₀ := by
    have ht : p.2 ≠ 0 := by
      have hh := ((TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl
        (le_trans (by norm_num : (0:ℝ) ≤ 1) hw)).mp hp).1
      omega
    have he := physicalModelPhase_fourth_condition_nonlinear hσ hδ hF hT hM hN hR hscale
      hA hW hx₀ (hx₁ p hp) hr ht (hq p hp) hdet hbase (hpoint p hp) (hcube p hp) (hfourth p hp)
    have he' : |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
        ((p.1:ℝ)/(p.2:ℝ))-h p| ≤ Δ+nonlinearResidualConstant σ δ*(|q p 0|+|q p 1|)/N := by
      change |α*(p.1:ℝ)+β*(p.2:ℝ)-(p.2:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
        ((p.1:ℝ)/(p.2:ℝ))-h p| ≤ Δ+nonlinearResidualConstant σ δ*(|q p 0|+|q p 1|)/N at he
      simpa only [mul_comm α,mul_comm β] using he
    exact he'.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hqbound p hp) hC) hN.le))
  intro p hp
  exact sector_nonlinear_integer_labels hl hw hlw hB hy₀ (hμ 0).ne' (hr' 0) (hμ 1) (hr' 1) hd hη₀
    hden hden₁ hratio hcard (fun p hp => ⟨h p,hnear p hp⟩) hlarge
    p hp (h p) (hnear p hp)

theorem sum_nonunit_inverse_square_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2) ≤ 3/4 := by
  by_cases hN : 2 ≤ N
  · have hI : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext d
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [hI,Finset.sum_insert (by simp)]
    let f : ℕ → ℝ := fun d => if 2 < d then 1/(d:ℝ)^2 else 0
    have hs : Summable f := by
      have h := (Real.summable_one_div_nat_pow.mpr
        (by norm_num : 1 < (2:ℕ))).indicator {d | 2 < d}
      apply h.congr
      intro d
      by_cases hd : 2 < d <;> simp [f,hd]
    have hsum : (∑ d ∈ Finset.Icc 3 N, 1/(d:ℝ)^2) ≤ ∑' d, f d := by
      calc
        _ = ∑ d ∈ Finset.Icc 3 N, f d := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd2 : 2 < d := by have h := (Finset.mem_Icc.mp hd).1; omega
          simp only [f,if_pos hd2]
        _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => by dsimp [f]; split <;> positivity)
    have ht := tsum_nat_inverse_square_tail_le (R := 2) (by norm_num)
    change (∑' d, f d) ≤ 1/(2:ℝ) at ht
    calc
      _ ≤ 1/(2:ℝ)^2+1/2 := add_le_add le_rfl (hsum.trans ht)
      _ = 3/4 := by norm_num
  · have hI : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
    simp only [hI,Finset.sum_empty]
    norm_num

/-- Positive endpoint denominators suffice on the entire real segment. -/
theorem affine_positive_between {r s l w y : ℝ}
    (hy : y ∈ Set.Icc l w) (hl : 0 < r*l+s) (hw : 0 < r*w+s) : 0 < r*y+s := by
  rcases le_total 0 r with hr | hr
  · have hh := mul_nonneg hr (sub_nonneg.mpr hy.1)
    nlinarith only [hh,hl]
  · have hh := mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hy.2)
    nlinarith only [hh,hw]


/-- Every member of the complete sector maps to the endpoint interval
of half-curvature targets, with positive physical denominator. -/
theorem fareySector_curvature_targets {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    0 < (r:ℝ)*p.1+s*p.2 ∧
      ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈
        Set.uIcc (((e:ℝ)*l+v)/((r:ℝ)*l+s)) (((e:ℝ)*w+v)/((r:ℝ)*w+s)) := by
  have hm := (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
  have ht : (0:ℝ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) hm.1)
  have hx : (p.1:ℝ)/(p.2:ℝ) ∈ Set.Icc l w :=
    ⟨(le_div_iff₀ ht).mpr hm.2.2.2.1,(div_le_iff₀ ht).mpr hm.2.2.2.2⟩
  have hden := affine_positive_between hx hdenl hdenw
  have hq : 0 < (r:ℝ)*p.1+s*p.2 := by
    have hh := mul_pos hden ht
    have hid : ((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s)*(p.2:ℝ)=(r:ℝ)*p.1+s*p.2 := by
      field_simp
    rwa [hid] at hh
  refine ⟨hq,?_⟩
  have hh := affine_ratio_mem_endpoint_interval (r₁ := (e:ℝ)) (s₁ := (v:ℝ)) hx hdenl hdenw hden
  have hid : ((e:ℝ)*((p.1:ℝ)/(p.2:ℝ))+v)/((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s) =
      ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) := by
    field_simp
  rwa [hid] at hh


/-- Rounding two centres costs at most one in their displacement. -/
theorem rounded_displacement_bound (x y : ℝ) :
    |(round x:ℝ)-(round y:ℝ)| ≤ |x-y|+1 := by
  have hx := abs_sub_round x
  have hy := abs_sub_round y
  have ht := abs_add_le ((round x:ℝ)-x) ((x-y)+(y-(round y:ℝ)))
  have hs := abs_add_le (x-y) (y-(round y:ℝ))
  rw [abs_sub_comm (round x:ℝ) x] at ht
  have hid : (round x:ℝ)-x+((x-y)+(y-(round y:ℝ)))=(round x:ℝ)-(round y:ℝ) := by ring
  rw [hid] at ht
  linarith only [ht,hs,hx,hy]


/-- Endpoint curvature coverage constructs every physical centre in the
complete sector. The source cubic displacement restriction follows from
the actual interval length and rounding, not from separately supplied n. -/
theorem physicalModelPhase_sector_centres {K : ℕ}
    {σ δ T M A W l w L U x₀ H R : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    (hLdist : |L-x₀| ≤ H) (hUdist : |U-x₀| ≤ H) (hcube : (H+1)^3 ≤ M*R^2) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let I := Set.uIcc (iteratedDeriv 2 f L/2) (iteratedDeriv 2 f U/2)
    ((e:ℝ)*l+v)/((r:ℝ)*l+s) ∈ I →
    ((e:ℝ)*w+v)/((r:ℝ)*w+s) ∈ I →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w,
      0 < (r:ℝ)*p.1+s*p.2 ∧ ∃ x ∈ Set.uIcc L U,
        x ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
        iteratedDeriv 2 f x/2=((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∧
        (round x:ℝ) ∈ Set.Ioo 0 W ∧
        |(round x:ℝ)-(round x₀:ℝ)|^3 ≤ M*R^2 := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  change _ → _ → _
  intro hleft hright p hp
  have ht := fareySector_curvature_targets (e := e) (v := v) hl hlw hdenl hdenw hp
  have hm := Set.uIcc_subset_uIcc hleft hright ht.2
  obtain ⟨x,hx,he,hrnd,_herr⟩ := physicalModelPhase_exists_rounded_halfCurvature_center
    hσ hF hT hM hA hW hL hU hm
  have hxi : x ∈ Set.Ioo (1/2:ℝ) (W-1/2) := by
    rcases Set.mem_uIcc.mp hx with hx | hx
    · exact ⟨hL.1.trans_le hx.1,hx.2.trans_lt hU.2⟩
    · exact ⟨hU.1.trans_le hx.1,hx.2.trans_lt hL.2⟩
  have hdist : |x-x₀| ≤ H := by
    have hld := abs_le.mp hLdist
    have hud := abs_le.mp hUdist
    apply abs_le.mpr
    rcases Set.mem_uIcc.mp hx with hx | hx
    · constructor <;> linarith only [hx.1,hx.2,hld.1,hld.2,hud.1,hud.2]
    · constructor <;> linarith only [hx.1,hx.2,hld.1,hld.2,hud.1,hud.2]
  refine ⟨ht.1,x,hx,hxi,he,hrnd,?_⟩
  have hn : |(round x:ℝ)-(round x₀:ℝ)| ≤ H+1 :=
    (rounded_displacement_bound x x₀).trans (add_le_add hdist le_rfl)
  exact (pow_le_pow_left₀ (abs_nonneg _) hn 3).trans hcube


/-- The physical denominator budget is derived from the sector endpoints
and its actual denominator cutoff, not supplied for each rational point. -/
theorem fareySector_denominator_bound {K : ℕ} {l w : ℝ} {r s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    |(r:ℝ)*p.1+s*p.2| ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) := by
  have hm := (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
  have ht : (0:ℝ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) hm.1)
  have htK : (p.2:ℝ) ≤ K := by exact_mod_cast hm.2.1
  have hx : (p.1:ℝ)/(p.2:ℝ) ∈ Set.Icc l w :=
    ⟨(le_div_iff₀ ht).mpr hm.2.2.2.1,(div_le_iff₀ ht).mpr hm.2.2.2.2⟩
  have hpos := (fareySector_curvature_targets (e := 0) (v := 0) hl hlw hdenl hdenw hp).1
  have hmax : (r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s ≤ max ((r:ℝ)*l+s) ((r:ℝ)*w+s) := by
    rcases le_total 0 (r:ℝ) with hr | hr
    · exact (add_le_add (mul_le_mul_of_nonneg_left hx.2 hr) le_rfl).trans (le_max_right _ _)
    · exact (add_le_add (mul_le_mul_of_nonpos_left hx.1 hr) le_rfl).trans (le_max_left _ _)
  rw [abs_of_pos hpos]
  calc
    (r:ℝ)*p.1+s*p.2 = (p.2:ℝ)*((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s) := by field_simp
    _ ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) :=
      mul_le_mul htK hmax (le_of_lt (affine_positive_between hx hdenl hdenw))
        (by exact_mod_cast Nat.zero_le K)


/-- Endpoint coverage supplies the centres used by the nonlinear
Fourth-Condition consumer. The denominator and displacement budgets are
derived on the complete sector; no pointwise centre family is assumed. -/
theorem physicalModelPhase_constructed_sector_nonlinear
    {K : ℕ} {σ δ T M N R Δ l w H : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ L U : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hL : ∀ i, L i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hU : ∀ i, U i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : ∀ i, 0 < (r i:ℝ)*l+s i) (hdenw : ∀ i, 0 < (r i:ℝ)*w+s i)
    (hLdist : ∀ i, |L i-x₀ i| ≤ H) (hUdist : ∀ i, |U i-x₀ i| ≤ H)
    (hcube : (H+1)^3 ≤ M*R^2) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let D := fun i => max ((r i:ℝ)*l+s i) ((r i:ℝ)*w+s i)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, ((e i:ℝ)*l+v i)/((r i:ℝ)*l+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (L i)/2) (iteratedDeriv 2 (f i) (U i)/2)) →
    (∀ i, ((e i:ℝ)*w+v i)/((r i:ℝ)*w+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (L i)/2) (iteratedDeriv 2 (f i) (U i)/2)) →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w,
      ∃ x : Fin 2 → ℝ,
        (∀ i, x i ∈ Set.uIcc (L i) (U i)) ∧
        (∀ i, iteratedDeriv 2 (f i) (x i)/2=((e i:ℝ)*p.1+v i*p.2)/((r i:ℝ)*p.1+s i*p.2)) ∧
        let q := fun i => (r i:ℝ)*p.1+s i*p.2
        let z := fun i => q i*iteratedDeriv 1 (f i) (round (x i))
        let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*p.1+
          2*(round (x i)-round (x₀ i))*(e i*p.1+v i*p.2)
        |(z 0-round (z 0))-(z 1-round (z 1))| ≤ Δ →
        |roundedMinorArcLinearForm (f 0) (x₀ 0) (e 0) (r 0) (s 0) p.1 p.2-
          roundedMinorArcLinearForm (f 1) (x₀ 1) (e 1) (r 1) (s 1) p.1 p.2-
          ((round (z 0)-j 0)-(round (z 1)-j 1):ℤ)| ≤
          Δ+nonlinearResidualConstant σ δ*(K:ℝ)*(D 0+D 1)/N := by
  classical
  let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
  let D := fun i => max ((r i:ℝ)*l+s i) ((r i:ℝ)*w+s i)
  change _ → _ → _ → _
  intro hbase hleft hright p hp
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hF₂ (i : Fin 2) := TaoTrudgianYang2025.approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hex (i : Fin 2) := (physicalModelPhase_sector_centres hσ.le (hF₂ i) hT hM0
    (hA i) (hW i) (hL i) (hU i) hl hlw (hdenl i) (hdenw i)
    (hLdist i) (hUdist i) hcube (hleft i) (hright i) p hp).2
  choose x hx hxi he _hrnd hn using hex
  refine ⟨x,hx,he,?_⟩
  let q := fun i => (r i:ℝ)*p.1+s i*p.2
  let z := fun i => q i*iteratedDeriv 1 (f i) (round (x i))
  let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*p.1+
    2*(round (x i)-round (x₀ i))*(e i*p.1+v i*p.2)
  let V := fun i => roundedMinorArcLinearForm (f i) (x₀ i) (e i) (r i) (s i) p.1 p.2
  change |(z 0-round (z 0))-(z 1-round (z 1))| ≤ Δ → _
  intro hfourth
  have ht : p.2 ≠ 0 := by
    have hh := ((TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp).1
    omega
  have hq (i : Fin 2) : r i*p.1+s i*p.2 ≠ 0 := by
    have hh := (fareySector_curvature_targets (e := e i) (v := v i) hl hlw (hdenl i) (hdenw i) hp).1.ne'
    exact_mod_cast hh
  have hV (i : Fin 2) : |z i-j i-V i| ≤ nonlinearResidualConstant σ δ*|q i|/N := by
    apply physicalModelPhase_rounded_linearization hσ hδ (hF i) hT hM hN hR hscale
      (hA i) (hW i) (hx₀ i) (hxi i) (hr i) ht (hq i) (hdet i) (hbase i) (he i)
    simpa only [Int.cast_sub] using hn i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error (hF 0)
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM0 (hA 0) (hW 0)
        (physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0) hT hM0 (hA 0) (hW 0) (hx₀ 0)).1)
      3 le_rfl)
  have hC := nonlinearResidualConstant_nonneg hσ hδ0
  have hqsum : |q 0|+|q 1| ≤ (K:ℝ)*(D 0+D 1) := by
    have h₀ := fareySector_denominator_bound hl hlw (hdenl 0) (hdenw 0) hp
    have h₁ := fareySector_denominator_bound hl hlw (hdenl 1) (hdenw 1) hp
    exact (add_le_add h₀ h₁).trans_eq (by ring)
  have hb := rounded_linearization_pair_bound (hV 0) (hV 1) hfourth
  apply hb.trans
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqsum hC) hN.le
  calc
    Δ+nonlinearResidualConstant σ δ*|q 0|/N+nonlinearResidualConstant σ δ*|q 1|/N =
        Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N := by ring
    _ ≤ Δ+nonlinearResidualConstant σ δ*((K:ℝ)*(D 0+D 1))/N := add_le_add le_rfl hh
    _ = _ := by dsimp [D]; ring

/-- A uniform primitive-point count for a genuine rectangular box.
Unlike the interval Mobius estimate, this input has no logarithmic error. -/
theorem coprime_rectangle_card_lower (M N : ℕ) :
    (M:ℝ)*N/4 ≤
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) := by
  classical
  let A := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let F := A.filter (fun p => ¬Nat.Coprime p.1 p.2)
  let U : ℕ → Finset (ℕ × ℕ) := fun d =>
    ((Finset.Icc 1 (M/d)) ×ˢ (Finset.Icc 1 (N/d))).image
      (fun p => (d*p.1,d*p.2))
  have hcover : F ⊆ (Finset.Icc 2 M).biUnion U := by
    intro p hp
    obtain ⟨hpA,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    obtain ⟨hp₁pos,hp₁M⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂pos,hp₂N⟩ := Finset.mem_Icc.mp hp₂
    let d := Nat.gcd p.1 p.2
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left p.2 hp₁pos
    have hdne : d ≠ 1 := hbad
    have hdM : d ≤ M := (Nat.gcd_le_left p.2 hp₁pos).trans hp₁M
    have hd₁ : d ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd₂ : d ∣ p.2 := Nat.gcd_dvd_right _ _
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_Icc.mpr ⟨by omega,hdM⟩,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1/d,p.2/d),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₁pos hd₁) hdpos,
        Nat.div_le_div_right hp₁M⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₂pos hd₂) hdpos,
        Nat.div_le_div_right hp₂N⟩
    · exact Prod.ext (Nat.mul_div_cancel' hd₁) (Nat.mul_div_cancel' hd₂)
  have hU (d : ℕ) : (U d).card ≤ (M/d)*(N/d) := by
    have hh := Finset.card_image_le (s := (Finset.Icc 1 (M/d)) ×ˢ (Finset.Icc 1 (N/d)))
      (f := fun p : ℕ × ℕ => (d*p.1,d*p.2))
    simpa only [U,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hh
  have hF : F.card ≤ ∑ d ∈ Finset.Icc 2 M, (M/d)*(N/d) := by
    calc
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun d _ => hU d)
  have hFR : (F.card:ℝ) ≤ (3/4:ℝ)*(M:ℝ)*N := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 M, (((M/d)*(N/d):ℕ):ℝ) := by exact_mod_cast hF
      _ ≤ ∑ d ∈ Finset.Icc 2 M, ((M:ℝ)/(d:ℝ))*((N:ℝ)/(d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [Nat.cast_mul]
        exact mul_le_mul Nat.cast_div_le Nat.cast_div_le (Nat.cast_nonneg _) (by positivity)
      _ = (M:ℝ)*N * ∑ d ∈ Finset.Icc 2 M, 1/(d:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _ ≤ (M:ℝ)*N*(3/4) := mul_le_mul_of_nonneg_left
        (sum_nonunit_inverse_square_le M) (by positivity)
      _ = _ := by ring
  have htotal : G.card+F.card=M*N := by
    have hh := Finset.card_filter_add_card_filter_not (s := A) (fun p => Nat.Coprime p.1 p.2)
    simpa only [A,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hh
  have htotalR : (G.card:ℝ)+(F.card:ℝ)=(M:ℝ)*N := by exact_mod_cast htotal
  change (M:ℝ)*N/4 ≤ (G.card:ℝ)
  linarith


/-- A determinant-one integer change of coordinates preserves the
primitive condition needed to inject the rectangle into rational points. -/
theorem isCoprime_unimodular_image {a b c d m n : ℤ}
    (hdet : a*d-b*c=1) (hmn : IsCoprime m n) : IsCoprime (a*m+b*n) (c*m+d*n) := by
  obtain ⟨x,y,hxy⟩ := hmn
  refine ⟨x*d-y*c,y*a-x*b,?_⟩
  linear_combination hxy+(x*m+y*n)*hdet


/-- No multiplicity is lost in the determinant-one rectangle map. -/
theorem unimodular_image_injective {a b c d : ℤ} (hdet : a*d-b*c=1) :
    Function.Injective (fun p : ℤ × ℤ => (a*p.1+b*p.2,c*p.1+d*p.2)) := by
  intro p q hpq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  apply Prod.ext
  · dsimp only at h₁ h₂
    linear_combination d*h₁-b*h₂-(p.1-q.1)*hdet
  · dsimp only at h₁ h₂
    linear_combination a*h₂-c*h₁-(p.2-q.2)*hdet


/-- A genuine determinant-one rectangle inside the sector gives a
uniform density lower bound, without a Mobius boundary-error term. The
two generating fractions and their linked denominator budget are explicit. -/
theorem unimodular_rectangle_fareySector_interior_card_lower
    {M N K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcap : c*(M:ℤ)+d*(N:ℤ) ≤ K) (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (M:ℝ)*N/4 ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
  classical
  let S := ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter (fun p => Nat.Coprime p.1 p.2)
  let f : ℕ × ℕ → ℤ × ℤ := fun p => (a*p.1+b*p.2,c*p.1+d*p.2)
  have hfi : Function.Injective f := by
    intro p q hpq
    have hh : ((p.1:ℤ),(p.2:ℤ))=((q.1:ℤ),(q.2:ℤ)) := unimodular_image_injective hdet hpq
    apply Prod.ext
    · have h₁ : (p.1:ℤ)=q.1 := congrArg Prod.fst hh
      exact_mod_cast h₁
    · have h₂ : (p.2:ℤ)=q.2 := congrArg Prod.snd hh
      exact_mod_cast h₂
  have hsub : S.image f ⊆ (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2) := by
    intro y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpbox,hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hpbox
    obtain ⟨hmpos,hmM⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hnpos,hnN⟩ := Finset.mem_Icc.mp hn
    have hmI : (0:ℤ) < p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hmpos)
    have hnI : (0:ℤ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hnpos)
    have hden : 0 < c*(p.1:ℤ)+d*(p.2:ℤ) := add_pos (mul_pos hc hmI) (mul_pos hd hnI)
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    swap
    · dsimp [f]
      constructor
      · nlinarith only [mul_pos hmI (show 0 < a*d-b*c by omega)]
      · nlinarith only [mul_pos hnI (show 0 < a*d-b*c by omega)]
    apply (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mpr
    refine ⟨by dsimp [f]; omega,?_,isCoprime_unimodular_image hdet hcop.isCoprime,?_,?_⟩
    · exact (add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hmM) hc.le)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hd.le)).trans hcap
    · have h₁ := mul_le_mul_of_nonneg_right ha.1 (Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1)
      have h₂ := mul_le_mul_of_nonneg_right hb.1 (Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2)
      dsimp [f]
      push_cast
      nlinarith only [h₁,h₂]
    · have h₁ := mul_le_mul_of_nonneg_right ha.2 (Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1)
      have h₂ := mul_le_mul_of_nonneg_right hb.2 (Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2)
      dsimp [f]
      push_cast
      nlinarith only [h₁,h₂]
  have hcard : S.card ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
    rw [← Finset.card_image_of_injective S hfi]
    exact Finset.card_le_card hsub
  exact (coprime_rectangle_card_lower M N).trans (by exact_mod_cast hcard)


theorem unimodular_rectangle_fareySector_card_lower
    {M N K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcap : c*(M:ℤ)+d*(N:ℤ) ≤ K) (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (M:ℝ)*N/4 ≤ (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  classical
  exact (unimodular_rectangle_fareySector_interior_card_lower hdet hc hd hcap hl hlw ha hb).trans
    (by exact_mod_cast (Finset.card_filter_le
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)))


/-- Scale-linked density inside a determinant-one rational cone. The
primitive rectangle dimensions are constructed by flooring the two actual
denominator budgets; no rectangle cardinality or size is assumed. -/
theorem unimodular_cone_fareySector_interior_card_lower
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (K:ℝ)^2/(64*(c:ℝ)*d) ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
  classical
  let M := ⌊(K:ℝ)/(2*(c:ℝ))⌋₊
  let N := ⌊(K:ℝ)/(2*(d:ℝ))⌋₊
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hcx : (2:ℝ) ≤ (K:ℝ)/(2*(c:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : 4*(c:ℝ) ≤ K := by exact_mod_cast hcK
    linarith only [hh]
  have hdx : (2:ℝ) ≤ (K:ℝ)/(2*(d:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : 4*(d:ℝ) ≤ K := by exact_mod_cast hdK
    linarith only [hh]
  have hMhi : (M:ℝ) ≤ (K:ℝ)/(2*(c:ℝ)) := Nat.floor_le (by positivity)
  have hNhi : (N:ℝ) ≤ (K:ℝ)/(2*(d:ℝ)) := Nat.floor_le (by positivity)
  have hMlo : (K:ℝ)/(4*(c:ℝ)) ≤ M := by
    have hh := Nat.lt_floor_add_one ((K:ℝ)/(2*(c:ℝ)))
    change (K:ℝ)/(2*(c:ℝ)) < (M:ℝ)+1 at hh
    rw [show (K:ℝ)/(4*(c:ℝ))=((K:ℝ)/(2*(c:ℝ)))/2 by ring]
    linarith only [hh,hcx]
  have hNlo : (K:ℝ)/(4*(d:ℝ)) ≤ N := by
    have hh := Nat.lt_floor_add_one ((K:ℝ)/(2*(d:ℝ)))
    change (K:ℝ)/(2*(d:ℝ)) < (N:ℝ)+1 at hh
    rw [show (K:ℝ)/(4*(d:ℝ))=((K:ℝ)/(2*(d:ℝ)))/2 by ring]
    linarith only [hh,hdx]
  have hcapR : (c:ℝ)*M+(d:ℝ)*N ≤ K := by
    calc
      _ ≤ (c:ℝ)*((K:ℝ)/(2*(c:ℝ)))+(d:ℝ)*((K:ℝ)/(2*(d:ℝ))) := by gcongr
      _ = _ := by field_simp; ring
  have hcap : c*(M:ℤ)+d*(N:ℤ) ≤ (K:ℤ) := by exact_mod_cast hcapR
  have he := unimodular_rectangle_fareySector_interior_card_lower hdet hc hd hcap hl hlw ha hb
  apply le_trans _ he
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul hMlo hNlo (by positivity) (Nat.cast_nonneg M)) (by norm_num : (0:ℝ) ≤ 4)
  convert hh using 1
  ring


theorem unimodular_cone_fareySector_card_lower
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (K:ℝ)^2/(64*(c:ℝ)*d) ≤ (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  classical
  exact (unimodular_cone_fareySector_interior_card_lower hdet hc hd hcK hdK hl hlw ha hb).trans
    (by exact_mod_cast (Finset.card_filter_le
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)))


/-- Every non-unit rational interval splits at a primitive point of no
larger denominator, with both positive determinants strictly decreasing.
This uses the already proved Bezout neighbor, not a Farey adjacency axiom. -/
theorem rational_interval_determinant_split {a b c d : ℤ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 1 < a*d-b*c) :
    ∃ m n : ℤ, 0 < n ∧ n ≤ max c d ∧ IsCoprime m n ∧
      0 < a*n-m*c ∧ a*n-m*c < a*d-b*c ∧
      0 < m*d-b*n ∧ m*d-b*n < a*d-b*c := by
  rcases le_total d c with hdc | hcd
  · obtain ⟨m,n,hn,hnc,hcop,hunit,hclose⟩ :=
      TaoTrudgianYang2025.HuxleyLinearForm.exists_left_neighbor hc ha
    have hweak : b*n ≤ m*d := hclose b d (by omega) hdc (by nlinarith only [hdet])
    have hid : n*(a*d-b*c)-d=c*(m*d-b*n) := by
      linear_combination d*hunit
    have hstrict : 0 < m*d-b*n := by
      by_contra hbad
      have he : m*d=b*n := by omega
      have hdvd : d ∣ n := hb.symm.dvd_of_dvd_mul_left
        (show d ∣ b*n from he ▸ dvd_mul_left d m)
      have hdn : d ≤ n := Int.le_of_dvd (by omega) hdvd
      have hh := mul_le_mul_of_nonneg_left hdn (show 0 ≤ a*d-b*c by omega)
      rw [he,sub_self,mul_zero] at hid
      have hh' := mul_lt_mul_of_pos_right hdet hd
      nlinarith only [hid,hh,hh']
    have hless : m*d-b*n < a*d-b*c := by
      have hh := mul_le_mul_of_nonneg_right hnc (show 0 ≤ a*d-b*c by omega)
      nlinarith only [hid,hh,hd,hc]
    exact ⟨m,n,by omega,hnc.trans (le_max_left _ _),hcop,
      by nlinarith only [hunit],by nlinarith only [hunit,hdet],hstrict,hless⟩
  · obtain ⟨m,n,hn,hnd,hcop,hunit,hclose⟩ :=
      TaoTrudgianYang2025.HuxleyLinearForm.exists_right_neighbor hd hb
    have hweak : m*c ≤ a*n := hclose a c (by omega) hcd (by nlinarith only [hdet])
    have hid : n*(a*d-b*c)-c=d*(a*n-m*c) := by
      linear_combination -c*hunit
    have hstrict : 0 < a*n-m*c := by
      by_contra hbad
      have he : a*n=m*c := by omega
      have hcvd : c ∣ n := ha.symm.dvd_of_dvd_mul_left
        (show c ∣ a*n from he ▸ dvd_mul_left c m)
      have hcn : c ≤ n := Int.le_of_dvd (by omega) hcvd
      have hh := mul_le_mul_of_nonneg_left hcn (show 0 ≤ a*d-b*c by omega)
      rw [he,sub_self,mul_zero] at hid
      have hh' := mul_lt_mul_of_pos_right hdet hc
      nlinarith only [hid,hh,hh']
    have hless : a*n-m*c < a*d-b*c := by
      have hh := mul_le_mul_of_nonneg_right hnd (show 0 ≤ a*d-b*c by omega)
      nlinarith only [hid,hh,hd,hc]
    exact ⟨m,n,by omega,hnd.trans (le_max_right _ _),hcop,hstrict,hless,
      by nlinarith only [hunit],by nlinarith only [hunit,hdet]⟩


/-- Strict subintervals do not double-count their common rational endpoint. -/
theorem interval_filter_split_card {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (S.filter (fun p => x < f p ∧ f p < y)).card +
      (S.filter (fun p => y < f p ∧ f p < z)).card ≤
      (S.filter (fun p => x < f p ∧ f p < z)).card := by
  classical
  let A := S.filter (fun p => x < f p ∧ f p < y)
  let B := S.filter (fun p => y < f p ∧ f p < z)
  have hd : Disjoint A B := Finset.disjoint_left.mpr (by
    intro p hp hq
    exact (Finset.mem_filter.mp hp).2.2.not_gt (Finset.mem_filter.mp hq).2.1)
  have hs : A ∪ B ⊆ S.filter (fun p => x < f p ∧ f p < z) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp,hlo,hhi.trans_le hyz⟩
    · obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp,hxy.trans_lt hlo,hhi⟩
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card hs


theorem rational_interior_filter_eq {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hl : 0 < l) (hlw : l ≤ w) :
    (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2) =
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c) := by
  classical
  apply Finset.filter_congr
  intro p hp
  have htI : 0 < p.2 := by
    have hh := ((TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp).1
    omega
  have ht : (0:ℝ) < p.2 := by exact_mod_cast htI
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hdR ht,div_lt_div_iff₀ ht hcR]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor <;> exact_mod_cast (by nlinarith only [h₁,h₂] : _)
  · rintro ⟨h₁,h₂⟩
    have h₁I : b*p.2 < p.1*d := by exact_mod_cast h₁
    have h₂I : p.1*c < a*p.2 := by exact_mod_cast h₂
    constructor <;> nlinarith only [h₁I,h₂I]


/-- A logarithm-free density bound between any two reduced rational
endpoints at denominator at most one quarter of the counting cutoff.
The interval is decomposed by strict determinant descent; no partition,
adjacency, density certificate, or cardinality bound is assumed. -/
theorem rational_interval_fareySector_interior_card_lower
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 0 < a*d-b*c) (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (hsa : l ≤ (a:ℝ)/c ∧ (a:ℝ)/c ≤ w)
    (hsb : l ≤ (b:ℝ)/d ∧ (b:ℝ)/d ≤ w) :
    ((a:ℝ)/c-(b:ℝ)/d)*(K:ℝ)^2/64 ≤
      ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card := by
  classical
  generalize hD : (a*d-b*c).toNat = D
  induction D using Nat.strong_induction_on generalizing a b c d with
  | h D ih =>
    have hcR : (0:ℝ) < c := by exact_mod_cast hc
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    by_cases hu : a*d-b*c=1
    · have hgap : (a:ℝ)/c-(b:ℝ)/d=1/((c:ℝ)*d) := by
        field_simp
        exact_mod_cast (show a*d-c*b=1 by nlinarith only [hu])
      have he := unimodular_cone_fareySector_interior_card_lower hu hc hd hcK hdK hl hlw
        ⟨(le_div_iff₀ hcR).mp hsa.1,(div_le_iff₀ hcR).mp hsa.2⟩
        ⟨(le_div_iff₀ hdR).mp hsb.1,(div_le_iff₀ hdR).mp hsb.2⟩
      rw [rational_interior_filter_eq hc hd hl hlw] at he
      calc
        _ = (K:ℝ)^2/(64*(c:ℝ)*d) := by rw [hgap]; ring
        _ ≤ _ := he
    · obtain ⟨m,n,hn,hnmax,hm,hup,hupD,hlo,hloD⟩ :=
        rational_interval_determinant_split hc hd ha hb (by omega)
      have hnK : 4*n ≤ (K:ℤ) := by
        rcases le_max_iff.mp hnmax with hh | hh <;> omega
      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hx : (b:ℝ)/d < (m:ℝ)/n := (div_lt_div_iff₀ hdR hnR).mpr
        (by exact_mod_cast (show b*n < m*d by omega))
      have hy : (m:ℝ)/n < (a:ℝ)/c := (div_lt_div_iff₀ hnR hcR).mpr
        (by exact_mod_cast (show m*c < a*n by omega))
      have hsm : l ≤ (m:ℝ)/n ∧ (m:ℝ)/n ≤ w :=
        ⟨hsb.1.trans hx.le,hy.le.trans hsa.2⟩
      have hupper := ih (a*n-m*c).toNat (by omega)
        hc hn ha hm hup hcK hnK hsa hsm rfl
      have hlower := ih (m*d-b*n).toNat (by omega)
        hn hd hm hb hlo hnK hdK hsm hsb rfl
      have hcount := interval_filter_split_card
        (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
        (fun p => (p.1:ℝ)/p.2) hx.le hy.le
      have hcountR :
          (((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (m:ℝ)/n)).card:ℝ) +
          (((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (m:ℝ)/n < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card:ℝ) ≤
          ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card := by
        have hh := (Nat.cast_le (α := ℝ)).mpr hcount
        simpa only [Nat.cast_add] using hh
      calc
        _ = ((m:ℝ)/n-(b:ℝ)/d)*(K:ℝ)^2/64 +
            ((a:ℝ)/c-(m:ℝ)/n)*(K:ℝ)^2/64 := by ring
        _ ≤ _ := (add_le_add hlower hupper).trans hcountR


/-- Distinct reduced rationals have their literal integer-determinant
separation; this will control Dirichlet approximants near a known anchor. -/
theorem rational_separation_scaled {q r : ℚ} (hne : q ≠ r) :
    1 ≤ |(q:ℝ)-(r:ℝ)| * (q.den:ℝ)*r.den := by
  have hq : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hr : (r.den:ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hqid : (q:ℝ)=(q.num:ℝ)/q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  have hrid : (r:ℝ)=(r.num:ℝ)/r.den := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hid : ((q.num*(r.den:ℤ)-r.num*(q.den:ℤ):ℤ):ℝ)=
      ((q:ℝ)-(r:ℝ))*(q.den:ℝ)*r.den := by
    rw [hqid,hrid]
    push_cast
    field_simp
  have hneI : q.num*(r.den:ℤ)-r.num*(q.den:ℤ) ≠ 0 := by
    intro he
    have hh : (q:ℝ)=(r:ℝ) := by
      have hz : ((q:ℝ)-(r:ℝ))*(q.den:ℝ)*r.den=0 := by rw [← hid,he]; simp
      rcases mul_eq_zero.mp hz with hz | hz
      · rcases mul_eq_zero.mp hz with hz | hz
        · exact sub_eq_zero.mp hz
        · exact (hq hz).elim
      · exact (hr hz).elim
    exact hne (Rat.cast_injective hh)
  have hsep : (1:ℝ) ≤ |((q.num*(r.den:ℤ)-r.num*(q.den:ℤ):ℤ):ℝ)| := by
    exact_mod_cast (show (1:ℤ) ≤ |q.num*(r.den:ℤ)-r.num*(q.den:ℤ)| by
      have hh := abs_pos.mpr hneI
      omega)
  rw [hid,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg q.den : (0:ℝ) ≤ q.den),
    abs_of_nonneg (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)] at hsep
  exact hsep


/-- A known rational in a short interval makes Dirichlet approximation
uniform at that interval's scale. Both cutoff restrictions are explicit
and depend on the anchor's actual reduced denominator. -/
theorem exists_rational_near_anchor {H : ℕ} {x Δ : ℝ} {r : ℚ}
    (hΔ : 0 < Δ) (hH : 16*r.den ≤ H)
    (hscale : 8 ≤ Δ*(H:ℝ)*r.den) (hx : |x-(r:ℝ)| ≤ Δ) :
    ∃ q : ℚ, q.den ≤ H ∧ |x-(q:ℝ)| ≤ Δ/8 := by
  have hH0 : 0 < H := by have hh := r.pos; omega
  have hHR : (0:ℝ) < H := by exact_mod_cast hH0
  obtain ⟨q,hq,hqH⟩ := Real.exists_rat_abs_sub_le_and_den_le x hH0
  refine ⟨q,hqH,?_⟩
  have hd : (0:ℝ) < q.den := by exact_mod_cast q.pos
  have hr : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hHRbound : 16*(r.den:ℝ) ≤ H := by exact_mod_cast hH
  have herr : |x-(q:ℝ)| * (q.den:ℝ)*(H:ℝ) ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by positivity : (0:ℝ) < H+1) hd)).mp hq
    have hm := mul_le_mul_of_nonneg_left (show (H:ℝ) ≤ H+1 by linarith)
      (mul_nonneg (abs_nonneg (x-(q:ℝ))) hd.le)
    nlinarith only [hh,hm]
  by_cases heq : q=r
  · subst q
    have hm := mul_le_mul_of_nonneg_left hscale (abs_nonneg (x-(r:ℝ)))
    have hh := mul_le_mul_of_nonneg_right herr hΔ.le
    nlinarith only [hm,hh]
  · have hsep := rational_separation_scaled heq
    have htri : |(q:ℝ)-(r:ℝ)| ≤ |x-(q:ℝ)|+Δ := by
      have hh := abs_sub_le (q:ℝ) x (r:ℝ)
      rw [abs_sub_comm (q:ℝ) x] at hh
      exact hh.trans (add_le_add le_rfl hx)
    have hsep' := hsep.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htri hd.le) hr.le)
    have he : |x-(q:ℝ)| * (q.den:ℝ)*r.den ≤ 1/16 := by
      have hh := mul_le_mul_of_nonneg_left hHRbound
        (mul_nonneg (abs_nonneg (x-(q:ℝ))) hd.le)
      nlinarith only [hh,herr]
    have hlo : 1/2 ≤ Δ*(q.den:ℝ)*r.den := by nlinarith only [hsep',he]
    have hh := mul_le_mul_of_nonneg_left hlo (abs_nonneg (x-(q:ℝ)))
    have hh' := mul_le_mul_of_nonneg_right he hΔ.le
    nlinarith only [hh,hh']


/-- Construct two reduced rational endpoints inside the real interval,
retaining at least half its width at the prescribed denominator cutoff. -/
theorem exists_rational_inner_endpoints {H : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    ∃ a b : ℚ, a.den ≤ H ∧ b.den ≤ H ∧
      w-(w-l)/4 ≤ (a:ℝ) ∧ (a:ℝ) ≤ w ∧
      l ≤ (b:ℝ) ∧ (b:ℝ) ≤ l+(w-l)/4 := by
  have hΔ : 0 < w-l := sub_pos.mpr hlw
  obtain ⟨b,hbH,hb⟩ := exists_rational_near_anchor hΔ hH hscale
    (show |l+(w-l)/8-(r:ℝ)| ≤ w-l from abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩)
  obtain ⟨a,haH,ha⟩ := exists_rational_near_anchor hΔ hH hscale
    (show |w-(w-l)/8-(r:ℝ)| ≤ w-l from abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩)
  obtain ⟨halo,hahi⟩ := abs_le.mp ha
  obtain ⟨hblo,hbhi⟩ := abs_le.mp hb
  exact ⟨a,b,haH,hbH,by linarith,by linarith,by linarith,by linarith⟩


/-- The complete positive real sector has the required quadratic density
under the two anchor-denominator scale restrictions. The rational inner
endpoints and every determinant-one piece are constructed in the proof. -/
theorem fareySector_card_lower_of_rational_anchor
    {H K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hHK : 4*H ≤ K)
    (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  classical
  obtain ⟨a,b,haH,hbH,halo,hahi,hblo,hbhi⟩ :=
    exists_rational_inner_endpoints hlw hr hH hscale
  have hab : (b:ℝ) < (a:ℝ) := by linarith
  have haR : (0:ℝ) < a.den := by exact_mod_cast a.pos
  have hbR : (0:ℝ) < b.den := by exact_mod_cast b.pos
  have hadiv : (a.num:ℝ)/(a.den:ℝ)=(a:ℝ) := by exact_mod_cast Rat.num_div_den a
  have hbdiv : (b.num:ℝ)/(b.den:ℝ)=(b:ℝ) := by exact_mod_cast Rat.num_div_den b
  have hdet : 0 < a.num*(b.den:ℤ)-b.num*(a.den:ℤ) := by
    have hh := (div_lt_div_iff₀ hbR haR).mp (show (b.num:ℝ)/b.den < (a.num:ℝ)/a.den by
      rwa [hadiv,hbdiv])
    exact_mod_cast (sub_pos.mpr hh)
  have haK : 4*(a.den:ℤ) ≤ (K:ℤ) := by exact_mod_cast (show 4*a.den ≤ K by omega)
  have hbK : 4*(b.den:ℤ) ≤ (K:ℤ) := by exact_mod_cast (show 4*b.den ≤ K by omega)
  have hsa : l ≤ (a.num:ℝ)/(a.den:ℤ) ∧ (a.num:ℝ)/(a.den:ℤ) ≤ w := by
    simp only [Int.cast_natCast,hadiv]
    exact ⟨by linarith,hahi⟩
  have hsb : l ≤ (b.num:ℝ)/(b.den:ℤ) ∧ (b.num:ℝ)/(b.den:ℤ) ≤ w := by
    simp only [Int.cast_natCast,hbdiv]
    exact ⟨hblo,by linarith⟩
  have he := rational_interval_fareySector_interior_card_lower
    (by exact_mod_cast a.pos) (by exact_mod_cast b.pos)
    a.isCoprime_num_den b.isCoprime_num_den hdet haK hbK hl hlw.le hsa hsb
  have hfilter := Finset.card_filter_le
    (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
    (fun p => (b.num:ℝ)/(b.den:ℤ) < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a.num:ℝ)/(a.den:ℤ))
  have hcount := he.trans ((Nat.cast_le (α := ℝ)).mpr hfilter)
  simp only [Int.cast_natCast,hadiv,hbdiv] at hcount
  have hwidth : (w-l)/2 ≤ (a:ℝ)-(b:ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right hwidth (sq_nonneg (K:ℝ))
  linarith only [hh,hcount]


/-- Source-scale local density, with the auxiliary cutoff eliminated.
The hypotheses have precisely the two scales K ≫ q₀ and
K ≫ 1 / ((w-l) q₀); the anchor need not even have minimal denominator. -/
theorem fareySector_card_lower_source_scale
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  let H := K/4
  have hH : 16*r.den ≤ H := by dsimp [H]; omega
  have hHK : 4*H ≤ K := by dsimp [H]; omega
  have hK8 : K ≤ 8*H := by have hh := r.pos; dsimp [H]; omega
  have hscaleH : 8 ≤ (w-l)*(H:ℝ)*r.den := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show (K:ℝ) ≤ 8*(H:ℝ) by exact_mod_cast hK8)
        (sub_nonneg.mpr hlw.le)) (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)
    nlinarith only [hh,hscale]
  exact fareySector_card_lower_of_rational_anchor hl hlw hr hH hHK hscaleH


/-- The source cutoff conditions also force the nontrivial-cardinality
clause required by the existing sector rigidity theorem. -/
theorem fareySector_source_density_gate
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    max ((w-l)*(K:ℝ)^2/128:ℝ) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  have he := fareySector_card_lower_source_scale hl hlw hr hden hscale
  have hh := mul_le_mul_of_nonneg_left
    (show 64*(r.den:ℝ) ≤ K by exact_mod_cast hden)
    (mul_nonneg (sub_nonneg.mpr hlw.le) (Nat.cast_nonneg K))
  apply max_le he
  have hbig : 4096 ≤ (w-l)*(K:ℝ)^2 := by nlinarith only [hh,hscale]
  linarith only [hbig,he]


/-- The nonlinear rigidity consumer now derives its density and size
branch from linked source scales and a scalar error budget. Neither
cardinality hypothesis remains an assumed input. -/
theorem sector_nonlinear_integer_labels_source_density
    {N : ℕ} {l v ν r s ν₁ r₁ s₁ x₀ d ε α β δ : ℝ} {a₀ : ℚ}
    (hl : 0 < l) (hv : 1 ≤ v) (hlv : l < v) (hx₀ : x₀ ∈ Set.Icc l v)
    (ha₀ : (a₀:ℝ) ∈ Set.Icc l v) (hcut : 64*a₀.den ≤ N)
    (hscale : 64 ≤ (v-l)*(N:ℝ)*a₀.den)
    (hν : ν ≠ 0) (hr : r ≠ 0) (hν₁ : 0 < ν₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d) (hδ : 0 ≤ δ)
    (hden : ∀ y ∈ Set.Icc l v, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l v, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.Icc l v, |ν₁*(r₁*y+s₁)^3/(ν*(r*y+s)^3)-1| ≤ ε)
    (hnear : ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-
        (p.2:ℝ)*rationalPhase ν r s ν₁ r₁ s₁ ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ)
    (hbudget : 196608*(δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3))*v < (v-l)/128) :
    let g := rationalPhase ν r s ν₁ r₁ s₁
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ →
      b=p.1*round (α-deriv g x₀)+p.2*round (β-g x₀+x₀*deriv g x₀) := by
  have hcard := fareySector_source_density_gate hl hlv ha₀ hcut hscale
  have hN : 0 < N := by have hh := a₀.pos; omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have he := fareySector_card_lower_source_scale hl hlv ha₀ hcut hscale
  have hlarge : 1536*128*(δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3))*(v*(N:ℝ))*(N:ℝ) <
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v).card := by
    have hh := mul_lt_mul_of_pos_right hbudget (sq_pos_of_pos hNR)
    nlinarith only [hh,he]
  exact sector_nonlinear_integer_labels hl hv hlv.le (by norm_num) hx₀
    hν hr hν₁ hr₁ hd hδ hden hden₁ hratio hcard hnear hlarge

/-- All reduced fractions of positive denominator at most K in an
arbitrary real interval, represented by a canonical integer translation
of the already defined positive sector. -/
noncomputable def rationalInterval (K : ℕ) (l w : ℝ) : Finset (ℤ × ℤ) :=
  let j := ⌈1-l⌉
  (HuxleyLinearForm.fareySector K (l+j) (w+j)).image (fun p => (p.1-j*p.2,p.2))

theorem mem_rationalInterval_iff {K : ℕ} {l w : ℝ} {p : ℤ × ℤ}
    (hlw : l ≤ w) :
    p ∈ rationalInterval K l w ↔ 1 ≤ p.2 ∧ p.2 ≤ K ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ w*p.2 := by
  classical
  let j : ℤ := ⌈1-l⌉
  have hj : 1-l ≤ (j:ℝ) := Int.le_ceil _
  have hl : 0 < l+(j:ℝ) := by linarith
  have hw : 0 ≤ w+(j:ℝ) := by linarith
  change p ∈ (HuxleyLinearForm.fareySector K (l+j) (w+j)).image
    (fun p => (p.1-j*p.2,p.2)) ↔ _
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqpos,hqK,hcop,hlo,hhi⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hw).mp hq
    refine ⟨hqpos,hqK,?_,?_,?_⟩
    · have hh := isCoprime_unimodular_image (a := 1) (b := -j) (c := 0) (d := 1)
        (by ring) hcop
      simpa only [one_mul,zero_mul,zero_add,neg_mul,← sub_eq_add_neg] using hh
    · push_cast
      nlinarith only [hlo]
    · push_cast
      nlinarith only [hhi]
  · rintro ⟨hp,hpK,hcop,hlo,hhi⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1+j*p.2,p.2),(HuxleyLinearForm.mem_fareySector_iff hl hw).mpr
      ⟨hp,hpK,?_,?_,?_⟩,?_⟩
    · have hh := isCoprime_unimodular_image (a := 1) (b := j) (c := 0) (d := 1)
        (by ring) hcop
      simpa only [one_mul,zero_mul,zero_add] using hh
    · push_cast
      nlinarith only [hlo]
    · push_cast
      nlinarith only [hhi]
    · simp


theorem rationalInterval_card_eq (K : ℕ) (l w : ℝ) :
    (rationalInterval K l w).card =
      (HuxleyLinearForm.fareySector K (l+(⌈1-l⌉:ℤ)) (w+(⌈1-l⌉:ℤ))).card := by
  classical
  apply Finset.card_image_of_injective
  intro p q hpq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  dsimp only at h₁ h₂
  apply Prod.ext
  · rw [h₂] at h₁
    linarith only [h₁]
  · exact h₂


/-- The source-scale density bound is invariant under the canonical
integer translation. Negative curvature values are included, with no
positivity assumption on the interval or its numerators. -/
theorem rationalInterval_card_lower_source_scale
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤ (rationalInterval K l w).card := by
  let j : ℤ := ⌈1-l⌉
  have hj : 1-l ≤ (j:ℝ) := Int.le_ceil _
  have hl : 0 < l+(j:ℝ) := by linarith
  have hs : ((r+(j:ℚ):ℚ):ℝ) ∈ Set.Icc (l+(j:ℝ)) (w+(j:ℝ)) := by
    push_cast
    exact ⟨add_le_add hr.1 le_rfl,add_le_add hr.2 le_rfl⟩
  have hd : 64*(r+(j:ℚ)).den ≤ K := by simpa only [Rat.add_intCast_den] using hden
  have hsc : 64 ≤ ((w+(j:ℝ))-(l+(j:ℝ)))*(K:ℝ)*(r+(j:ℚ)).den := by
    simpa only [Rat.add_intCast_den,add_sub_add_right_eq_sub] using hscale
  have hh := fareySector_card_lower_source_scale hl (by linarith) hs hd hsc
  rw [rationalInterval_card_eq]
  simpa only [add_sub_add_right_eq_sub] using hh


/-- The actual model's third-derivative lower bound controls the full
physical half-curvature interval, without an assumed width estimate. -/
theorem physicalModelPhase_halfCurvature_growth
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ*T/(2*M^3)*(y-x) ≤
      iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 := by
  let f := heathBrownPhysicalPhase F T M A 1
  let g := fun z => iteratedDeriv 2 f z/2
  have hd (z : ℝ) (hz : z ∈ Set.Ioo 0 W) :
      HasDerivAt g (iteratedDeriv 3 f z/2) z := by
    have hcf := heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    have hf3 : ContDiffAt ℝ 3 f z :=
      ((hcf z (Set.Ioo_subset_Icc_self hz)).contDiffAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Set.Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hf3).div_const 2
  have hb (z : ℝ) (hz : z ∈ Set.Ioo 0 W) :
      modelPhaseThirdLower σ*T/(2*M^3) ≤ deriv g z := by
    rw [(hd z hz).deriv,heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hz,one_mul]
    have hlo : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F ((A+z)/M) := by
      have hh := (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (heathBrownPhysicalPoint_mem_interior hM hA hW hz)).1
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ T/M^3)) (by norm_num : (0:ℝ) ≤ 2)
    convert hh using 1
    ring
  exact (convex_Ioo (0:ℝ) W).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (by simpa only [interior_Ioo] using hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hb z (by simpa only [interior_Ioo] using hz)) x hx y hy hxy


/-- The physical phase scale determines the curvature width at R^-2. -/
theorem physicalModelPhase_halfCurvature_width
    {σ δ T M A W L U R : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo 0 W) (hU : U ∈ Set.Ioo 0 W) (hLU : L ≤ U)
    (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ/(2*R^2) ≤
      iteratedDeriv 2 f U/2-iteratedDeriv 2 f L/2 := by
  have hh := physicalModelPhase_halfCurvature_growth hσ hδ hF hT hM hA hW hL hU hLU
  have hid : modelPhaseThirdLower σ*T/(2*M^3)*(U-L)=modelPhaseThirdLower σ/(2*R^2) := by
    field_simp
    linear_combination modelPhaseThirdLower σ*hscale
  rwa [hid] at hh


/-- Huxley's rational-curvature counting input for the actual physical
model phase: signed curvature, R^-2 width, cardinality, continuous roots,
integer rounding, and its error are all linked and derived together. -/
theorem physicalModelPhase_rational_curvature_count
    {K : ℕ} {σ δ T M A W L U R : ℝ} {F : ℝ → ℝ} {r : ℚ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 64*r.den ≤ K) (hmajor : 128*R^2 ≤ modelPhaseThirdLower σ*(K:ℝ)*r.den) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := rationalInterval K l w
    (r:ℝ) ∈ Set.Icc l w →
    modelPhaseThirdLower σ*(K:ℝ)^2/(256*R^2) ≤ S.card ∧
      ∀ p ∈ S, ∃ x ∈ Set.Icc L U, iteratedDeriv 2 f x/2=(p.1:ℝ)/p.2 ∧
        (round x:ℝ) ∈ Set.Ioo 0 W ∧
        |iteratedDeriv 2 f (round x)/2-(p.1:ℝ)/p.2| ≤
          T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := heathBrownPhysicalPhase F T M A 1
  let l := iteratedDeriv 2 f L/2
  let w := iteratedDeriv 2 f U/2
  let S := rationalInterval K l w
  change _ → _
  intro hr
  have hL0 : L ∈ Set.Ioo 0 W := ⟨by linarith [hL.1],by linarith [hL.2]⟩
  have hU0 : U ∈ Set.Ioo 0 W := ⟨by linarith [hU.1],by linarith [hU.2]⟩
  have hwidth : modelPhaseThirdLower σ/(2*R^2) ≤ w-l :=
    physicalModelPhase_halfCurvature_width hσ hδ hF hT hM hA hW hL0 hU0 hLU.le hR hscale
  have hκ := modelPhaseThirdLower_pos hσ
  have hlw : l < w := by
    have hh : 0 < modelPhaseThirdLower σ/(2*R^2) := by positivity
    linarith only [hh,hwidth]
  have hscaled : 64 ≤ (w-l)*(K:ℝ)*r.den := by
    have hh : 64 ≤ modelPhaseThirdLower σ*(K:ℝ)*r.den/(2*R^2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hmajor])
    have hg := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg K : (0:ℝ) ≤ K))
      (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)
    calc
      64 ≤ modelPhaseThirdLower σ*(K:ℝ)*r.den/(2*R^2) := hh
      _ = modelPhaseThirdLower σ/(2*R^2)*(K:ℝ)*r.den := by ring
      _ ≤ _ := hg
  have hcount := rationalInterval_card_lower_source_scale hlw hr hcut hscaled
  refine ⟨?_,?_⟩
  · have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hwidth (sq_nonneg (K:ℝ))) (by norm_num : (0:ℝ) ≤ 128)
    apply le_trans _ hcount
    convert hh using 1
    ring
  · intro p hp
    have hm := (mem_rationalInterval_iff hlw.le).mp hp
    have hq : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hpI : (p.1:ℝ)/p.2 ∈ Set.uIcc l w := Set.mem_uIcc.mpr (Or.inl
      ⟨(le_div_iff₀ hq).mpr hm.2.2.2.1,(div_le_iff₀ hq).mpr hm.2.2.2.2⟩)
    have hh := physicalModelPhase_exists_rounded_halfCurvature_center hσ.le hF hT hM hA hW hL hU hpI
    simpa only [Set.uIcc_of_le hLU.le] using hh


/-- The source uses a real cutoff Q and counts denominators below 2Q.
The floor bridge loses only an absolute factor four in the lower bound;
no logarithmic loss or assumed counting estimate is introduced. -/
theorem physicalModelPhase_rational_curvature_count_real
    {σ δ T M A W L U R Q : ℝ} {F : ℝ → ℝ} {r : ℚ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 128*(r.den:ℝ) ≤ Q) (hmajor : 256*R^2 ≤ modelPhaseThirdLower σ*Q*r.den) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := rationalInterval ⌊Q⌋₊ l w
    (r:ℝ) ∈ Set.Icc l w →
    modelPhaseThirdLower σ*Q^2/(1024*R^2) ≤ S.card ∧
      ∀ p ∈ S, 1 ≤ p.2 ∧ (p.2:ℝ) < 2*Q ∧ IsCoprime p.1 p.2 ∧
        ∃ x ∈ Set.Icc L U, iteratedDeriv 2 f x/2=(p.1:ℝ)/p.2 ∧
          (round x:ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round x)/2-(p.1:ℝ)/p.2| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := heathBrownPhysicalPhase F T M A 1
  let l := iteratedDeriv 2 f L/2
  let w := iteratedDeriv 2 f U/2
  have hq0 : (1:ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hQ : 2 ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hfloor : Q/2 ≤ (⌊Q⌋₊:ℝ) := by
    have hh := Nat.lt_floor_add_one Q
    linarith
  have hc : 64*r.den ≤ ⌊Q⌋₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith
  have hκ := modelPhaseThirdLower_pos hσ
  have hm : 128*R^2 ≤ modelPhaseThirdLower σ*(⌊Q⌋₊:ℝ)*r.den := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfloor hκ.le) (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)
    nlinarith only [hh,hmajor]
  change _ → _
  intro hr
  obtain ⟨hcount,hroots⟩ := physicalModelPhase_rational_curvature_count
    hσ hδ hF hT hM hA hW hL hU hLU hR hscale hc hm hr
  have hlw : l ≤ w := le_trans hr.1 hr.2
  refine ⟨?_,?_⟩
  · apply le_trans _ hcount
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs : Q^2 ≤ 4*(⌊Q⌋₊:ℝ)^2 := by
      nlinarith only [sq_nonneg ((⌊Q⌋₊:ℝ)-Q/2),hfloor,hQ0]
    nlinarith only [mul_nonneg hκ.le (mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hs))]
  · intro p hp
    have hh := (mem_rationalInterval_iff hlw).mp hp
    have hpQ : (p.2:ℝ) ≤ Q :=
      le_trans (by exact_mod_cast hh.2.1) (Nat.floor_le hQ0)
    exact ⟨hh.1,by linarith,hh.2.2.1,hroots p hp⟩


/-- Actual inverse Farey coordinates of every reduced curvature fraction
in the interval, with the original denominator cutoff retained. -/
noncomputable def fareyCurvatureCoordinates (K : ℕ) (l w : ℝ) (e r v s : ℤ) :
    Finset (ℤ × ℤ) :=
  (rationalInterval K l w).image (fun p => (v*p.2-s*p.1,r*p.1-e*p.2))

theorem fareyCurvatureCoordinates_card {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    (hdet : v*r-e*s=1) :
    (fareyCurvatureCoordinates K l w e r v s).card=(rationalInterval K l w).card := by
  classical
  apply Finset.card_image_of_injective
  intro p q hpq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  dsimp only at h₁ h₂
  have ha : e*(v*p.2-s*p.1)+v*(r*p.1-e*p.2)=p.1 := by
    linear_combination p.1*hdet
  have hb : e*(v*q.2-s*q.1)+v*(r*q.1-e*q.2)=q.1 := by
    linear_combination q.1*hdet
  have hc : r*(v*p.2-s*p.1)+s*(r*p.1-e*p.2)=p.2 := by
    linear_combination p.2*hdet
  have hd : r*(v*q.2-s*q.1)+s*(r*q.1-e*q.2)=q.2 := by
    linear_combination q.2*hdet
  rw [h₁,h₂] at ha hc
  exact Prod.ext (ha.symm.trans hb) (hc.symm.trans hd)


/-- The transformed set is exactly the full rational sector cut out by
the original denominator, not an independently supplied witness family. -/
theorem mem_fareyCurvatureCoordinates_iff {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hdet : v*r-e*s=1) :
    p ∈ fareyCurvatureCoordinates K l w e r v s ↔
      1 ≤ r*p.1+s*p.2 ∧ r*p.1+s*p.2 ≤ K ∧ IsCoprime p.1 p.2 ∧
        l*((r*p.1+s*p.2:ℤ):ℝ) ≤ (e*p.1+v*p.2:ℤ) ∧
        ((e*p.1+v*p.2:ℤ):ℝ) ≤ w*((r*p.1+s*p.2:ℤ):ℝ) := by
  classical
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hh := (mem_rationalInterval_iff hlw).mp hq
    have ha : e*(v*q.2-s*q.1)+v*(r*q.1-e*q.2)=q.1 := by
      linear_combination q.1*hdet
    have hb : r*(v*q.2-s*q.1)+s*(r*q.1-e*q.2)=q.2 := by
      linear_combination q.2*hdet
    have hc := isCoprime_unimodular_image (a := r) (b := -e) (c := -s) (d := v)
      (by nlinarith only [hdet]) hh.2.2.1
    dsimp only
    rw [ha,hb]
    exact ⟨hh.1,hh.2.1,by simpa only [neg_mul,← sub_eq_add_neg,add_comm] using hc.symm,
      hh.2.2.2.1,hh.2.2.2.2⟩
  · rintro ⟨hq,hqK,hcop,hlo,hhi⟩
    apply Finset.mem_image.mpr
    refine ⟨(e*p.1+v*p.2,r*p.1+s*p.2),?_,?_⟩
    · apply (mem_rationalInterval_iff hlw).mpr
      have hc := isCoprime_unimodular_image (a := r) (b := s) (c := e) (d := v)
        (by nlinarith only [hdet]) hcop
      exact ⟨hq,hqK,hc.symm,hlo,hhi⟩
    · apply Prod.ext
      · dsimp only
        linear_combination p.1*hdet
      · dsimp only
        linear_combination p.2*hdet


theorem fareyCurvatureCoordinates_positive {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hr : 0 < r) (hs : 0 < s)
    (hl : (e:ℝ)/r < l) (hw : w < (v:ℝ)/s)
    (hp : p ∈ fareyCurvatureCoordinates K l w e r v s) : 0 < p.1 ∧ 0 < p.2 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hh := (mem_rationalInterval_iff hlw).mp hq
  have hqpos : (0:ℝ) < q.2 := by exact_mod_cast (show 0 < q.2 by omega)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have he := (div_lt_iff₀ hrR).mp hl
  have hv := (lt_div_iff₀ hsR).mp hw
  have ht := mul_lt_mul_of_pos_right he hqpos
  have hu := mul_lt_mul_of_pos_right hv hqpos
  constructor
  · have ht' := mul_le_mul_of_nonneg_left hh.2.2.2.2 hsR.le
    have hpR : (0:ℝ) < (v:ℝ)*q.2-s*q.1 := by nlinarith only [hu,ht']
    exact_mod_cast hpR
  · have ht' := mul_le_mul_of_nonneg_left hh.2.2.2.1 hrR.le
    have hpR : (0:ℝ) < (r:ℝ)*q.1-e*q.2 := by nlinarith only [ht,ht']
    exact_mod_cast hpR


/-- The real physical count is transported to the actual positive Farey
coordinates. All roots and rounding errors refer to the same counted set;
the only Farey geometry assumed is that the physical curvature interval
lies strictly between the two given determinant-one endpoints. -/
theorem physicalModelPhase_farey_curvature_count
    {σ δ T M A W L U R Q : ℝ} {F : ℝ → ℝ} {a₀ : ℚ} {e r v s : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 128*(a₀.den:ℝ) ≤ Q) (hmajor : 256*R^2 ≤ modelPhaseThirdLower σ*Q*a₀.den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := fareyCurvatureCoordinates ⌊Q⌋₊ l w e r v s
    (a₀:ℝ) ∈ Set.Icc l w → (e:ℝ)/r < l → w < (v:ℝ)/s →
    modelPhaseThirdLower σ*Q^2/(1024*R^2) ≤ S.card ∧
      ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ IsCoprime p.1 p.2 ∧
        1 ≤ r*p.1+s*p.2 ∧ ((r*p.1+s*p.2:ℤ):ℝ) < 2*Q ∧
        ∃ x ∈ Set.Icc L U,
          iteratedDeriv 2 f x/2=((e*p.1+v*p.2:ℤ):ℝ)/((r*p.1+s*p.2:ℤ):ℝ) ∧
          (round x:ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round x)/2-
            ((e*p.1+v*p.2:ℤ):ℝ)/((r*p.1+s*p.2:ℤ):ℝ)| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := heathBrownPhysicalPhase F T M A 1
  let l := iteratedDeriv 2 f L/2
  let w := iteratedDeriv 2 f U/2
  change _ → _ → _ → _
  intro ha₀ he hv
  obtain ⟨hcount,hroots⟩ := physicalModelPhase_rational_curvature_count_real
    hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor ha₀
  have hlw : l ≤ w := le_trans ha₀.1 ha₀.2
  refine ⟨?_,?_⟩
  · rwa [fareyCurvatureCoordinates_card hdet]
  · intro p hp
    have hpos := fareyCurvatureCoordinates_positive hlw hr hs he hv hp
    have hc := ((mem_fareyCurvatureCoordinates_iff hlw hdet).mp hp).2.2.1
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have ha : e*(v*q.2-s*q.1)+v*(r*q.1-e*q.2)=q.1 := by
      linear_combination q.1*hdet
    have hb : r*(v*q.2-s*q.1)+s*(r*q.1-e*q.2)=q.2 := by
      linear_combination q.2*hdet
    obtain ⟨hqpos,hqcut,_,hx⟩ := hroots q hq
    refine ⟨hpos.1,hpos.2,hc,?_,?_,?_⟩
    · dsimp only
      rwa [hb]
    · dsimp only
      rwa [hb]
    · dsimp only
      rwa [ha,hb]

end TaoTrudgianYang2025.HuxleyRationalPhase
