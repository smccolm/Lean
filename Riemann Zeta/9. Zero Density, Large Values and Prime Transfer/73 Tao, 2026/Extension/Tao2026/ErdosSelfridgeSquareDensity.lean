import Tao2026.ErdosSelfridgeDeletion

/-!
# Squarefree density in blocks of 36

This file formalizes the elementary density observation used immediately
after equation (21) in Erdős--Selfridge (1975): at most 24 integers in any
block of 36 consecutive positive integers are squarefree.
-/

namespace Tao2026

/-- A divisor of the block length occurs with exactly its expected frequency
in every interval of that length. -/
theorem card_filter_dvd_Ioc_add_of_dvd (N L d : ℕ) (hd : d ∣ L) :
    ((Finset.Ioc N (N + L)).filter (fun n => d ∣ n)).card = L / d := by
  have hsplit : Finset.Ioc 0 N ∪ Finset.Ioc N (N + L) =
      Finset.Ioc 0 (N + L) :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le N) (Nat.le_add_right N L)
  have hdisjoint : Disjoint (Finset.Ioc 0 N) (Finset.Ioc N (N + L)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hfilterDisjoint :
      Disjoint ((Finset.Ioc 0 N).filter (fun n => d ∣ n))
        ((Finset.Ioc N (N + L)).filter (fun n => d ∣ n)) :=
    hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have htotal := Nat.Ioc_filter_dvd_card_eq_div (N + L) d
  have hinitial := Nat.Ioc_filter_dvd_card_eq_div N d
  rw [← hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint hfilterDisjoint] at htotal
  rw [hinitial, Nat.add_div_of_dvd_left hd] at htotal
  omega

/-- The elements of `(N, N + 36]` divisible by either `2²` or `3²`. -/
def erdosSelfridgeSmallSquareMultiples (N : ℕ) : Finset ℕ :=
  (Finset.Ioc N (N + 36)).filter (fun n => 4 ∣ n ∨ 9 ∣ n)

/-- Exactly twelve members of every block of 36 consecutive integers are
divisible by `4` or by `9`. -/
theorem card_erdosSelfridgeSmallSquareMultiples (N : ℕ) :
    (erdosSelfridgeSmallSquareMultiples N).card = 12 := by
  let I := Finset.Ioc N (N + 36)
  let A := I.filter (fun n => 4 ∣ n)
  let B := I.filter (fun n => 9 ∣ n)
  have hbad : erdosSelfridgeSmallSquareMultiples N = A ∪ B := by
    ext n
    simp only [erdosSelfridgeSmallSquareMultiples, I, A, B,
      Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union]
    tauto
  have hcop : Nat.Coprime 4 9 := by norm_num
  have hinter : A ∩ B = I.filter (fun n => 36 ∣ n) := by
    ext n
    simp only [A, B, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hnI, h4⟩, _hnI, h9⟩
      exact ⟨hnI, hcop.mul_dvd_of_dvd_of_dvd h4 h9⟩
    · rintro ⟨hnI, h36⟩
      have h4 : 4 ∣ n := (by norm_num : 4 ∣ 36) |>.trans h36
      have h9 : 9 ∣ n := (by norm_num : 9 ∣ 36) |>.trans h36
      exact ⟨⟨hnI, h4⟩, hnI, h9⟩
  have hA : A.card = 9 := by
    simpa [I, A] using
      card_filter_dvd_Ioc_add_of_dvd N 36 4 (by norm_num)
  have hB : B.card = 4 := by
    simpa [I, B] using
      card_filter_dvd_Ioc_add_of_dvd N 36 9 (by norm_num)
  have hAB : (A ∩ B).card = 1 := by
    rw [hinter]
    simpa [I] using
      card_filter_dvd_Ioc_add_of_dvd N 36 36 (by norm_num)
  rw [hbad]
  have hinc := Finset.card_union_add_card_inter A B
  omega

/-- The squarefree members of a block of 36 consecutive positive integers. -/
def erdosSelfridgeSquarefreeBlock (N : ℕ) : Finset ℕ :=
  (Finset.Ioc N (N + 36)).filter Squarefree

/-- The elementary density estimate quoted in the square case of
Erdős--Selfridge: no block of 36 consecutive integers contains more than
24 squarefree integers. -/
theorem card_erdosSelfridgeSquarefreeBlock_le (N : ℕ) :
    (erdosSelfridgeSquarefreeBlock N).card ≤ 24 := by
  let I := Finset.Ioc N (N + 36)
  let S := erdosSelfridgeSquarefreeBlock N
  let B := erdosSelfridgeSmallSquareMultiples N
  have hBsubset : B ⊆ I := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hSsubset : S ⊆ I \ B := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnI : n ∈ I := hnData.1
    have hsq : Squarefree n := hnData.2
    rw [Finset.mem_sdiff]
    refine ⟨hnI, ?_⟩
    intro hnB
    rcases (Finset.mem_filter.mp hnB).2 with h4 | h9
    · exact ((Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two) h4
    · exact ((Nat.squarefree_iff_prime_squarefree.mp hsq) 3 Nat.prime_three) h9
  have hScard : S.card ≤ (I \ B).card := Finset.card_le_card hSsubset
  have hdiff := Finset.card_sdiff_of_subset hBsubset
  have hIcard : I.card = 36 := by simp [I]
  have hBcard : B.card = 12 := card_erdosSelfridgeSmallSquareMultiples N
  change S.card ≤ 24
  omega

/-- Offset form of the 36-block estimate, matching the indexing convention
used for the interval values `N + (i + 1)` in the Erdős--Selfridge files. -/
theorem card_filter_squarefree_interval_offsets_le (N : ℕ) :
    ((Finset.range 36).filter
      (fun i => Squarefree (N + (i + 1)))).card ≤ 24 := by
  let R := (Finset.range 36).filter
    (fun i => Squarefree (N + (i + 1)))
  let S := erdosSelfridgeSquarefreeBlock N
  let f : ℕ → ℕ := fun i => N + (i + 1)
  have hmaps : Set.MapsTo f (R : Set ℕ) (S : Set ℕ) := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    change f i ∈ S
    dsimp only [S, erdosSelfridgeSquarefreeBlock]
    rw [Finset.mem_filter]
    refine ⟨?_, hiData.2⟩
    dsimp only [f]
    rw [Finset.mem_Ioc]
    have hi36 := Finset.mem_range.mp hiData.1
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    omega
  have hcard : R.card ≤ S.card :=
    Finset.card_le_card_of_injOn f hmaps hinj.injOn
  have hS : S.card ≤ 24 := card_erdosSelfridgeSquarefreeBlock_le N
  change R.card ≤ 24
  exact hcard.trans hS

/-- Squarefree positive integers at most `M`. -/
def erdosSelfridgeSquarefreeUpTo (M : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 M).filter Squarefree

/-- Adding a complete block of 36 introduces at most 24 new squarefree
integers. -/
theorem card_erdosSelfridgeSquarefreeUpTo_add_thirtySix_le (M : ℕ) :
    (erdosSelfridgeSquarefreeUpTo (M + 36)).card ≤
      (erdosSelfridgeSquarefreeUpTo M).card + 24 := by
  have hsplit : Finset.Ioc 0 M ∪ Finset.Ioc M (M + 36) =
      Finset.Ioc 0 (M + 36) :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le M) (Nat.le_add_right M 36)
  have hdisjoint : Disjoint (Finset.Ioc 0 M) (Finset.Ioc M (M + 36)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hfilterDisjoint :
      Disjoint ((Finset.Ioc 0 M).filter Squarefree)
        ((Finset.Ioc M (M + 36)).filter Squarefree) :=
    hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcardSplit :
      (erdosSelfridgeSquarefreeUpTo (M + 36)).card =
        (erdosSelfridgeSquarefreeUpTo M).card +
          (erdosSelfridgeSquarefreeBlock M).card := by
    rw [erdosSelfridgeSquarefreeUpTo, erdosSelfridgeSquarefreeUpTo,
      erdosSelfridgeSquarefreeBlock, ← hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint hfilterDisjoint]
  rw [hcardSplit]
  exact Nat.add_le_add_left (card_erdosSelfridgeSquarefreeBlock_le M) _

/-- From 44 onward, at most two thirds of the positive integers up to `M`
are squarefree. The finite initial window is followed by induction in blocks
of 36. -/
theorem three_mul_card_erdosSelfridgeSquarefreeUpTo_le_two_mul
    (M : ℕ) (hM : 44 ≤ M) :
    3 * (erdosSelfridgeSquarefreeUpTo M).card ≤ 2 * M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
      by_cases hsmall : M < 80
      · let C := (Finset.Ioc 0 M).filter
          (fun n => ¬ 4 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 25 ∣ n)
        have hsubset : erdosSelfridgeSquarefreeUpTo M ⊆ C := by
          intro n hn
          have hnData := Finset.mem_filter.mp hn
          rw [Finset.mem_filter]
          refine ⟨hnData.1, ?_⟩
          have hsq := Nat.squarefree_iff_prime_squarefree.mp hnData.2
          exact ⟨hsq 2 Nat.prime_two, hsq 3 Nat.prime_three,
            hsq 5 Nat.prime_five⟩
        have hcard := Finset.card_le_card hsubset
        have hC : 3 * C.card ≤ 2 * M := by
          dsimp only [C]
          interval_cases M <;> decide
        omega
      · have hm44 : 44 ≤ M - 36 := by omega
        have hmLt : M - 36 < M := by omega
        have hrepr : M - 36 + 36 = M := by omega
        have hprev := ih (M - 36) hmLt hm44
        have hstep :=
          card_erdosSelfridgeSquarefreeUpTo_add_thirtySix_le (M - 36)
        rw [hrepr] at hstep
        omega

/-- The first 64 squarefree positive integers, described by excluding the
only prime squares at most 103. -/
def erdosSelfridgeInitialSquarefree : Finset ℕ :=
  (Finset.Ioc 0 103).filter
    (fun n => ¬ 4 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 25 ∣ n ∧ ¬ 49 ∣ n)

theorem card_erdosSelfridgeInitialSquarefree :
    erdosSelfridgeInitialSquarefree.card = 64 := by
  decide

theorem squarefree_of_mem_erdosSelfridgeInitialSquarefree
    {n : ℕ} (hn : n ∈ erdosSelfridgeInitialSquarefree) : Squarefree n := by
  have hnData := Finset.mem_filter.mp hn
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpSq
  have hnPos : 0 < n := (Finset.mem_Ioc.mp hnData.1).1
  have hpSqLe : p * p ≤ n := Nat.le_of_dvd hnPos hpSq
  have hnLe : n ≤ 103 := (Finset.mem_Ioc.mp hnData.1).2
  have hpLe : p ≤ 10 := by nlinarith
  have hpGe : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at hp
  all_goals aesop

theorem erdosSelfridgeInitialSquarefree_eq_upTo :
    erdosSelfridgeInitialSquarefree = erdosSelfridgeSquarefreeUpTo 103 := by
  ext n
  simp only [erdosSelfridgeInitialSquarefree,
    erdosSelfridgeSquarefreeUpTo, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hnIoc, hn4, hn9, hn25, hn49⟩
    exact ⟨hnIoc, squarefree_of_mem_erdosSelfridgeInitialSquarefree
      (by simp [erdosSelfridgeInitialSquarefree, hnIoc, hn4, hn9, hn25,
        hn49])⟩
  · rintro ⟨hnIoc, hsq⟩
    have hprimeSq := Nat.squarefree_iff_prime_squarefree.mp hsq
    exact ⟨hnIoc, hprimeSq 2 Nat.prime_two, hprimeSq 3 Nat.prime_three,
      hprimeSq 5 Nat.prime_five, hprimeSq 7 Nat.prime_seven⟩

/-- The finite numerical base of source equation (22), with rational
denominators cleared. -/
theorem initialSquarefree_equation22_base :
    3 ^ 64 * (64 : ℕ).factorial <
      2 ^ 64 * erdosSelfridgeInitialSquarefree.prod id := by
  decide

/-- Exactly `i` elements of a finite natural set precede its `i`th increasing
enumeration value. -/
theorem card_filter_lt_orderEmbOfFin_nat
    {s : Finset ℕ} {k : ℕ} (hs : s.card = k) (i : Fin k) :
    (s.filter (fun n => n < s.orderEmbOfFin hs i)).card = i := by
  let f := s.orderEmbOfFin hs
  have himage : (Finset.Iio i).image f =
      s.filter (fun n => n < f i) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hji, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hs j, f.strictMono hji⟩
    · rintro ⟨hns, hnlt⟩
      let j : Fin k := (s.orderIsoOfFin hs).symm ⟨n, hns⟩
      have hjn : f j = n := by
        change ((s.orderIsoOfFin hs) j : s).1 = n
        rw [show j = (s.orderIsoOfFin hs).symm ⟨n, hns⟩ by rfl,
          (s.orderIsoOfFin hs).apply_symm_apply]
      refine ⟨j, ?_, hjn⟩
      exact f.lt_iff_lt.mp (hjn ▸ hnlt)
  rw [← himage, Finset.card_image_of_injective _ f.injective]
  simp

/-- Exactly `i+1` elements of a finite natural set are at most its `i`th
increasing enumeration value. -/
theorem card_filter_le_orderEmbOfFin_nat
    {s : Finset ℕ} {k : ℕ} (hs : s.card = k) (i : Fin k) :
    (s.filter (fun n => n ≤ s.orderEmbOfFin hs i)).card = i + 1 := by
  let f := s.orderEmbOfFin hs
  have himage : (Finset.Iic i).image f =
      s.filter (fun n => n ≤ f i) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Iic, Finset.mem_filter]
    constructor
    · rintro ⟨j, hji, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hs j, f.monotone hji⟩
    · rintro ⟨hns, hnle⟩
      let j : Fin k := (s.orderIsoOfFin hs).symm ⟨n, hns⟩
      have hjn : f j = n := by
        change ((s.orderIsoOfFin hs) j : s).1 = n
        rw [show j = (s.orderIsoOfFin hs).symm ⟨n, hns⟩ by rfl,
          (s.orderIsoOfFin hs).apply_symm_apply]
      refine ⟨j, ?_, hjn⟩
      exact f.le_iff_le.mp (hjn ▸ hnle)
  rw [← himage, Finset.card_image_of_injective _ f.injective]
  simp

/-- The increasing enumeration of the first 64 squarefree integers is
pointwise no larger than that of any other 64-element squarefree set. -/
theorem initialSquarefree_orderEmb_le
    {A : Finset ℕ} (hAcard : A.card = 64)
    (hAsq : ∀ n ∈ A, Squarefree n) (hApos : ∀ n ∈ A, 0 < n)
    (i : Fin 64) :
    erdosSelfridgeInitialSquarefree.orderEmbOfFin
        card_erdosSelfridgeInitialSquarefree i ≤
      A.orderEmbOfFin hAcard i := by
  let s := erdosSelfridgeInitialSquarefree.orderEmbOfFin
    card_erdosSelfridgeInitialSquarefree i
  let a := A.orderEmbOfFin hAcard i
  by_contra hnot
  have has : a < s := by omega
  have hsMem : s ∈ erdosSelfridgeInitialSquarefree :=
    Finset.orderEmbOfFin_mem _ card_erdosSelfridgeInitialSquarefree i
  have hsLe : s ≤ 103 :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hsMem).1).2
  have hprefixSubset : A.filter (fun n => n ≤ a) ⊆
      erdosSelfridgeInitialSquarefree.filter (fun n => n < s) := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnLe : n ≤ 103 := by omega
    have hnInitial : n ∈ erdosSelfridgeInitialSquarefree := by
      rw [erdosSelfridgeInitialSquarefree_eq_upTo]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hApos n hnData.1, hnLe⟩,
          hAsq n hnData.1⟩
    exact Finset.mem_filter.mpr ⟨hnInitial, by omega⟩
  have hcardLe := Finset.card_le_card hprefixSubset
  have hAcardPrefix := card_filter_le_orderEmbOfFin_nat hAcard i
  have hScardPrefix := card_filter_lt_orderEmbOfFin_nat
    card_erdosSelfridgeInitialSquarefree i
  change (A.filter (fun n => n ≤ a)).card = i + 1 at hAcardPrefix
  change (erdosSelfridgeInitialSquarefree.filter
    (fun n => n < s)).card = i at hScardPrefix
  omega

/-- Consequently, the first-64 product is minimal among products of 64
distinct positive squarefree naturals. -/
theorem initialSquarefree_prod_le
    {A : Finset ℕ} (hAcard : A.card = 64)
    (hAsq : ∀ n ∈ A, Squarefree n) (hApos : ∀ n ∈ A, 0 < n) :
    erdosSelfridgeInitialSquarefree.prod id ≤ A.prod id := by
  let s := erdosSelfridgeInitialSquarefree.orderEmbOfFin
    card_erdosSelfridgeInitialSquarefree
  let a := A.orderEmbOfFin hAcard
  have hsProd : erdosSelfridgeInitialSquarefree.prod id =
      ∏ i : Fin 64, s i := by
    rw [← Finset.image_orderEmbOfFin_univ
      erdosSelfridgeInitialSquarefree
      card_erdosSelfridgeInitialSquarefree]
    rw [Finset.prod_image]
    rfl
    exact s.injective.injOn
  have haProd : A.prod id = ∏ i : Fin 64, a i := by
    rw [← Finset.image_orderEmbOfFin_univ A hAcard]
    rw [Finset.prod_image]
    rfl
    exact a.injective.injOn
  rw [hsProd, haProd]
  exact Finset.prod_le_prod (fun _i _hi => Nat.zero_le _) fun i _hi =>
    initialSquarefree_orderEmb_le hAcard hAsq hApos i

/-- Equation (22) at its finite base length 64, for an arbitrary distinct
family of positive squarefree coefficients. -/
theorem equation22_base_of_card_eq_sixtyFour
    {A : Finset ℕ} (hAcard : A.card = 64)
    (hAsq : ∀ n ∈ A, Squarefree n) (hApos : ∀ n ∈ A, 0 < n) :
    3 ^ 64 * (64 : ℕ).factorial < 2 ^ 64 * A.prod id := by
  exact initialSquarefree_equation22_base.trans_le
    (Nat.mul_le_mul_left _ (initialSquarefree_prod_le hAcard hAsq hApos))

/-- Cleared-denominator form of source equation (22): every set of at least
64 distinct positive squarefree integers has product strictly larger than
`H! * (3/2)^H`. -/
theorem erdosSelfridge_equation22
    {A : Finset ℕ} {H : ℕ} (hAcard : A.card = H)
    (hAsq : ∀ n ∈ A, Squarefree n) (hApos : ∀ n ∈ A, 0 < n)
    (hH : 64 ≤ H) :
    3 ^ H * H.factorial < 2 ^ H * A.prod id := by
  induction H, hH using Nat.le_induction generalizing A with
  | base =>
      exact equation22_base_of_card_eq_sixtyFour hAcard hAsq hApos
  | succ H hH ih =>
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      let m := A.max' hAne
      let B := A.erase m
      have hmA : m ∈ A := Finset.max'_mem A hAne
      have hBcard : B.card = H := by
        dsimp only [B]
        rw [Finset.card_erase_of_mem hmA, hAcard]
        omega
      have hBsq : ∀ n ∈ B, Squarefree n := by
        intro n hn
        exact hAsq n (Finset.mem_of_mem_erase hn)
      have hBpos : ∀ n ∈ B, 0 < n := by
        intro n hn
        exact hApos n (Finset.mem_of_mem_erase hn)
      have hIH : 3 ^ H * H.factorial < 2 ^ H * B.prod id :=
        ih hBcard hBsq hBpos
      have hAinterval : A ⊆ Finset.Ioc 0 m := by
        intro n hn
        exact Finset.mem_Ioc.mpr
          ⟨hApos n hn, Finset.le_max' A n hn⟩
      have hcardM := Finset.card_le_card hAinterval
      have hm44 : 44 ≤ m := by
        have hIocCard : (Finset.Ioc 0 m).card = m := by simp
        omega
      have hAsubsetSquarefree : A ⊆ erdosSelfridgeSquarefreeUpTo m := by
        intro n hn
        exact Finset.mem_filter.mpr ⟨hAinterval hn, hAsq n hn⟩
      have hcardSquarefree := Finset.card_le_card hAsubsetSquarefree
      have hcount :=
        three_mul_card_erdosSelfridgeSquarefreeUpTo_le_two_mul m hm44
      have hcoefficient : 3 * (H + 1) ≤ 2 * m := by omega
      have hscaledStrict :
          (3 * (H + 1)) * (3 ^ H * H.factorial) <
            (3 * (H + 1)) * (2 ^ H * B.prod id) :=
        Nat.mul_lt_mul_of_pos_left hIH (by positivity)
      have hscaledWeak :
          (3 * (H + 1)) * (2 ^ H * B.prod id) ≤
            (2 * m) * (2 ^ H * B.prod id) :=
        Nat.mul_le_mul_right _ hcoefficient
      have hprodA : B.prod id * m = A.prod id := by
        dsimp only [B]
        exact Finset.prod_erase_mul A id hmA
      calc
        3 ^ (H + 1) * (H + 1).factorial =
            (3 * (H + 1)) * (3 ^ H * H.factorial) := by
              rw [pow_succ, Nat.factorial_succ]
              ring
        _ < (3 * (H + 1)) * (2 ^ H * B.prod id) := hscaledStrict
        _ ≤ (2 * m) * (2 ^ H * B.prod id) := hscaledWeak
        _ = 2 ^ (H + 1) * A.prod id := by
              rw [pow_succ, ← hprodA]
              ring

/-- Lemma 1 makes the squarefree coefficients at distinct interval positions
distinct. -/
theorem powerFreePart_two_injOn_range_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 3 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    Set.InjOn (fun i => powerFreePart 2 (N + (i + 1))) (Finset.range H) := by
  intro i hi j hj hij
  have hiInterval : N + (i + 1) ∈ consecutiveInterval N H := by
    rw [consecutiveInterval, Finset.mem_Ioc]
    have hiH := Finset.mem_range.mp hi
    omega
  have hjInterval : N + (j + 1) ∈ consecutiveInterval N H := by
    rw [consecutiveInterval, Finset.mem_Ioc]
    have hjH := Finset.mem_range.mp hj
    omega
  have hscale : H ^ 2 < N :=
    erdosSelfridge_pow_lt_start_of_failure hSS hH (by omega) hHN hfail
  have hsingletons : ({N + (i + 1)} : Finset ℕ) = {N + (j + 1)} := by
    exact powerFreePart_subproduct_injective
      (N := N) (H := H) (l := 2) (r := 1)
      (S := {N + (i + 1)}) (T := {N + (j + 1)})
      hH (by omega) (by omega) (by omega) hscale
      (by simpa using hiInterval) (by simpa using hjInterval)
      (by simp) (by simp) (by simpa using hij)
  have hvalues : N + (i + 1) = N + (j + 1) :=
    Finset.singleton_inj.mp hsingletons
  omega

/-- Source-facing equation (22) for the canonical squarefree coefficients of
a counterexample. The rational factor `(3/2)^H` is represented by clearing
the denominator. -/
theorem powerFreePart_two_equation22_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    3 ^ H * H.factorial <
      2 ^ H * (∏ i ∈ Finset.range H,
        powerFreePart 2 (N + (i + 1))) := by
  let f : ℕ → ℕ := fun i => powerFreePart 2 (N + (i + 1))
  let A := (Finset.range H).image f
  have hinj : Set.InjOn f (Finset.range H) :=
    powerFreePart_two_injOn_range_of_failure hSS (by omega) hHN hfail
  have hAcard : A.card = H := by
    dsimp only [A]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hAsq : ∀ n ∈ A, Squarefree n := by
    intro n hn
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
    apply Nat.squarefree_of_factorization_le_one (powerFreePart_ne_zero _ _)
    intro p
    have hp := factorization_powerFreePart_lt
      (l := 2) (n := N + (i + 1)) (p := p) (by omega)
    omega
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
    exact Nat.pos_iff_ne_zero.mpr (powerFreePart_ne_zero _ _)
  have h22 := erdosSelfridge_equation22 hAcard hAsq hApos hH
  have hprod : A.prod id = ∏ i ∈ Finset.range H, f i := by
    dsimp only [A]
    rw [Finset.prod_image]
    rfl
    exact hinj
  rw [hprod] at h22
  exact h22

end Tao2026
