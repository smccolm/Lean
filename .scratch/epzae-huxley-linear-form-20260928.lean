import TaoTrudgianYang2025
import TaoTrudgianYang2025.HuxleyLinearForms
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand

#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_denominator_integer_identity
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.card_mul_le_of_dvd
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_denominator_branch
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_reduced_approximation
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fixed_residual_separated
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fixed_residual_card_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_denominator_branch
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.linear_form_dichotomy
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.linear_form_dichotomy_round
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.maximal_denominator_determinant_injective
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.determinant_alpha_near
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.determinant_beta_near
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_right_neighbor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_left_neighbor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_exists_unit_determinant
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.card_le_two_mul_nonzero_abs_card_add_one
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_error_integer_of_unit_determinant
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_determinant_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_small_error_bounds
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_one_one_two
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.printed_exact_integrality_counterexample

namespace HuxleyLinearFormRegression

open TaoTrudgianYang2025.HuxleyLinearForm

example
    (S : Finset ℕ) {N : ℕ} {α δ : ℝ}
    (hne : S.Nonempty) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hnear : ∀ n ∈ S, |(n:ℝ)*α-(round ((n:ℝ)*α):ℤ)| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N ∨
      ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ (N:ℝ)/S.card ∧
        |(q:ℝ)*α-(round ((q:ℝ)*α):ℤ)| ≤ δ/S.card ∧
        ∀ n ∈ S, q ∣ n :=
  linear_form_dichotomy_round S hne hN hδ hS hnear

example {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = -1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → m₀*n < n₀*m → a*n ≤ m*b :=
  exists_right_neighbor hn₀ hcop

example {N : ℕ} {l μ : ℝ} {p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ) :
    p ∈ fareySector N l μ ↔ 1 ≤ p.2 ∧ p.2 ≤ N ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2 :=
  mem_fareySector_iff hl hμ

example
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(fareySector N l μ).card :=
  fareySector_small_error_bounds hl hμ hB hδ hR hsmall hnear

example : fareySector 1 1 2 = {(1,1),(2,1)} :=
  fareySector_one_one_two

example :
    max (((2:ℝ)-1)*1^2/1) 2 ≤ ((fareySector 1 1 2).card:ℝ) ∧
    (2:ℝ)*1*(1/1000) ≤ 1/(96*1) ∧
    (∀ p ∈ fareySector 1 1 2,
      ∃ b : ℤ, |(p.1:ℝ)*(1/2000)+(p.2:ℝ)*0-b| ≤ 1/1000) ∧
    ¬∃ k : ℤ, (1/2000:ℝ)=k :=
  printed_exact_integrality_counterexample

end HuxleyLinearFormRegression

#print axioms TaoTrudgianYang2025.HuxleyLinearForm.denominator_fiber_card
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_card_le
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_width
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.prime_coprime_consecutive
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_consecutive_numerators
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_consecutive_numerators
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_alpha_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_denominator_card_lower
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_denominator_common_divisor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_card_le_twice_rectangle
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_beta_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_bounded_density_dichotomy
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_integer_labels

namespace HuxleyFareyDensity

open TaoTrudgianYang2025

theorem sum_nonunit_inverse_square_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2) ≤ 3/4 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.sum_nonunit_inverse_square_le N

#print axioms sum_nonunit_inverse_square_le

/-- A uniform positive proportion of the actual integer square is primitive.
This supplies the mean totient input for the alternate density route. -/
theorem coprime_square_card_lower (N : ℕ) :
    (N:ℝ)^2/4 ≤
      ((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) := by
  classical
  let A := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let F := A.filter (fun p => ¬Nat.Coprime p.1 p.2)
  let U : ℕ → Finset (ℕ × ℕ) := fun d =>
    ((Finset.Icc 1 (N/d)) ×ˢ (Finset.Icc 1 (N/d))).image
      (fun p => (d*p.1,d*p.2))
  have hcover : F ⊆ (Finset.Icc 2 N).biUnion U := by
    intro p hp
    obtain ⟨hpA,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    obtain ⟨hp₁pos,hp₁N⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂pos,hp₂N⟩ := Finset.mem_Icc.mp hp₂
    let d := Nat.gcd p.1 p.2
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left p.2 hp₁pos
    have hdne : d ≠ 1 := hbad
    have hdN : d ≤ N := (Nat.gcd_le_left p.2 hp₁pos).trans hp₁N
    have hd₁ : d ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd₂ : d ∣ p.2 := Nat.gcd_dvd_right _ _
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_Icc.mpr ⟨by omega,hdN⟩,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1/d,p.2/d),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₁pos hd₁) hdpos,
        Nat.div_le_div_right hp₁N⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₂pos hd₂) hdpos,
        Nat.div_le_div_right hp₂N⟩
    · exact Prod.ext (Nat.mul_div_cancel' hd₁) (Nat.mul_div_cancel' hd₂)
  have hU (d : ℕ) : (U d).card ≤ (N/d)^2 := by
    have h := Finset.card_image_le (s := (Finset.Icc 1 (N/d)) ×ˢ (Finset.Icc 1 (N/d)))
      (f := fun p : ℕ × ℕ => (d*p.1,d*p.2))
    simpa only [U,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,pow_two] using h
  have hF : F.card ≤ ∑ d ∈ Finset.Icc 2 N, (N/d)^2 := by
    calc
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun d _ => hU d)
  have hFR : (F.card:ℝ) ≤ (3/4:ℝ)*(N:ℝ)^2 := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 N, (((N/d)^2:ℕ):ℝ) := by exact_mod_cast hF
      _ ≤ ∑ d ∈ Finset.Icc 2 N, ((N:ℝ)/(d:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) Nat.cast_div_le _
      _ = (N:ℝ)^2 * ∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _hd
        rw [div_pow]
        ring
      _ ≤ (N:ℝ)^2*(3/4) := mul_le_mul_of_nonneg_left (sum_nonunit_inverse_square_le N) (sq_nonneg _)
      _ = _ := by ring
  have htotal : G.card+F.card=N^2 := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (fun p => Nat.Coprime p.1 p.2)
    simpa only [A,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,pow_two] using h
  have htotalR : (G.card:ℝ)+(F.card:ℝ)=(N:ℝ)^2 := by exact_mod_cast htotal
  change (N:ℝ)^2/4 ≤ (G.card:ℝ)
  linarith

#print axioms coprime_square_card_lower

theorem sum_totient_lower (N : ℕ) :
    (N:ℝ)^2/8 ≤ ∑ n ∈ Finset.Icc 1 N, (n.totient:ℝ) := by
  classical
  let A := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let C : ℕ → Finset ℕ := fun n => (Finset.Icc 1 n).filter (Nat.Coprime n)
  let U : ℕ → Finset (ℕ × ℕ) := fun n =>
    ((C n).image (fun m => (m,n))) ∪ ((C n).image (fun m => (n,m)))
  have hC (n : ℕ) : (C n).card=n.totient := by
    have h := Nat.filter_coprime_Ico_eq_totient n 1
    have hI : Finset.Ico 1 (1+n) = Finset.Icc 1 n := by
      ext m
      simp only [Finset.mem_Ico,Finset.mem_Icc]
      omega
    rwa [hI] at h
  have hU (n : ℕ) : (U n).card ≤ 2*n.totient := by
    calc
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ (C n).card+(C n).card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = _ := by rw [hC]; omega
  have hcover : G ⊆ (Finset.Icc 1 N).biUnion U := by
    intro p hp
    obtain ⟨hpA,hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    by_cases hle : p.1 ≤ p.2
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.2,hp₂,Finset.mem_union_left _ ?_⟩
      exact Finset.mem_image.mpr ⟨p.1,Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp₁).1,hle⟩,hcop.symm⟩,rfl⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.1,hp₁,Finset.mem_union_right _ ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp₂).1,by omega⟩,hcop⟩,rfl⟩
  have hupper : G.card ≤ ∑ n ∈ Finset.Icc 1 N, 2*n.totient :=
    (Finset.card_le_card hcover).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun n _ => hU n)))
  have hupperR : (G.card:ℝ) ≤ 2*∑ n ∈ Finset.Icc 1 N, (n.totient:ℝ) := by
    have h : (G.card:ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (2:ℝ)*(n.totient:ℝ) := by
      exact_mod_cast hupper
    rwa [← Finset.mul_sum] at h
  have hlower := coprime_square_card_lower N
  change (N:ℝ)^2/4 ≤ (G.card:ℝ) at hlower
  linarith

#print axioms sum_totient_lower

theorem moebius_coprime_indicator {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (∑ d ∈ n.divisors, if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0) =
      if Nat.Coprime n m then 1 else 0 := by
  classical
  have hg : n.gcd m ≠ 0 := (Nat.gcd_pos_of_pos_left m hn).ne'
  have hset : n.divisors.filter (fun d => d ∣ m) = (n.gcd m).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdn,_⟩,hdm⟩
      exact ⟨⟨hdn,hdm⟩,hg⟩
    · rintro ⟨⟨hdn,hdm⟩,_⟩
      exact ⟨⟨hdn,hn.ne'⟩,hdm⟩
  rw [← Finset.sum_filter,hset]
  have hμ : (∑ d ∈ (n.gcd m).divisors, ArithmeticFunction.moebius d) =
      if n.gcd m=1 then (1:ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have hcast := congrArg (fun z : ℤ => (z:ℝ)) hμ
  simpa only [Int.cast_sum,Int.cast_ite,Int.cast_one,Int.cast_zero,Nat.Coprime] using hcast

theorem moebius_totient_weight {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*(n/d:ℕ)) = (n.totient:ℝ) := by
  have hsum : ∀ k : ℕ, 0 < k → (∑ d ∈ k.divisors, (d.totient:ℝ))=(k:ℝ) := by
    intro k _hk
    exact_mod_cast Nat.sum_totient k
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum n hn
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (ArithmeticFunction.moebius d:ℝ)*(e:ℝ))] at h
  exact h

#print axioms moebius_coprime_indicator
#print axioms moebius_totient_weight

theorem coprime_prefix_moebius {n : ℕ} (hn : 0 < n) (X : ℕ) :
    (((Finset.Ioc 0 X).filter (Nat.Coprime n)).card:ℝ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ) := by
  classical
  calc
    _ = ∑ m ∈ Finset.Ioc 0 X, if Nat.Coprime n m then (1:ℝ) else 0 := by
      simp only [Finset.card_filter,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      split_ifs <;> norm_num
    _ = ∑ m ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors,
        if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact (moebius_coprime_indicator hn m).symm
    _ = ∑ d ∈ n.divisors, ∑ m ∈ Finset.Ioc 0 X,
        if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
        Nat.Ioc_filter_dvd_card_eq_div,mul_comm]

theorem moebius_totient_normalized {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
      (n.totient:ℝ)/(n:ℝ) := by
  have h := moebius_totient_weight hn
  have h' : (n:ℝ)*(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
      (n.totient:ℝ) := by
    rw [Finset.mul_sum]
    convert h using 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
    ring
  apply (eq_div_iff (by positivity : (n:ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h'

#print axioms coprime_prefix_moebius
#print axioms moebius_totient_normalized

theorem coprime_prefix_error {n : ℕ} (hn : 0 < n) (X : ℕ) :
    |(((Finset.Ioc 0 X).filter (Nat.Coprime n)).card:ℝ)-
      (X:ℝ)*((n.totient:ℝ)/(n:ℝ))| ≤ n.divisors.card := by
  classical
  rw [coprime_prefix_moebius hn X,← moebius_totient_normalized hn,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        |(ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ)-
          (X:ℝ)*((ArithmeticFunction.moebius d:ℝ)/(d:ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d _hd
      have he : (ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ)-
          (X:ℝ)*((ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
          (ArithmeticFunction.moebius d:ℝ)*(((X/d:ℕ):ℝ)-(X:ℝ)/(d:ℝ)) := by ring
      rw [he,abs_mul]
      have hμ : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hfloor : |((X/d:ℕ):ℝ)-(X:ℝ)/(d:ℝ)| ≤ 1 := by
        have hlo := Nat.floor_le (show (0:ℝ) ≤ (X:ℝ)/(d:ℝ) by positivity)
        have hhi := Nat.lt_floor_add_one ((X:ℝ)/(d:ℝ))
        rw [Nat.floor_div_eq_div] at hlo hhi
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      simpa only [one_mul] using mul_le_mul hμ hfloor (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    _ = _ := by simp

#print axioms coprime_prefix_error

/-- An actual half-open real interval, with explicit arithmetic discrepancy.
This statement retains the divisor error instead of postulating density. -/
theorem coprime_interval_lower {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*((n.totient:ℝ)/(n:ℝ)) ≤
      (((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (Nat.Coprime n)).card:ℝ)+3*n.divisors.card := by
  classical
  let L := ⌊a⌋₊
  let U := ⌊b⌋₊
  let C : ℕ → Finset ℕ := fun X => (Finset.Ioc 0 X).filter (Nat.Coprime n)
  let T := (Finset.Ioc L U).filter (Nat.Coprime n)
  have hLU : L ≤ U := Nat.floor_mono hab
  have hpart : C U=C L ∪ T := by
    ext m
    simp only [C,T,Finset.mem_filter,Finset.mem_Ioc,Finset.mem_union]
    omega
  have hdis : Disjoint (C L) T := by
    apply Finset.disjoint_left.mpr
    intro m hm ht
    have h₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
    have h₂ := Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1
    omega
  have hcounts : ((C U).card:ℝ)=((C L).card:ℝ)+(T.card:ℝ) := by
    rw [hpart,Finset.card_union_of_disjoint hdis,Nat.cast_add]
  let γ : ℝ := (n.totient:ℝ)/(n:ℝ)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ1 : γ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < n)).mpr
    (by exact_mod_cast Nat.totient_le n)
  have hfloor : b-a ≤ (U:ℝ)-(L:ℝ)+1 := by
    have hL := Nat.floor_le ha
    have hU := Nat.lt_floor_add_one b
    change (L:ℝ) ≤ a at hL
    change b < (U:ℝ)+1 at hU
    linarith
  have hscale := mul_le_mul_of_nonneg_right hfloor hγ0
  have hlo := (abs_le.mp (coprime_prefix_error hn L)).2
  have hup := (abs_le.mp (coprime_prefix_error hn U)).1
  change (C L).card-(L:ℝ)*γ ≤ (n.divisors.card:ℝ) at hlo
  change -(n.divisors.card:ℝ) ≤ (C U).card-(U:ℝ)*γ at hup
  have hdiv : (1:ℝ) ≤ n.divisors.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn.ne'⟩)
  change (b-a)*γ ≤ (T.card:ℝ)+3*n.divisors.card
  nlinarith only [hcounts,hγ1,hscale,hlo,hup,hdiv]

#print axioms coprime_interval_lower

/-- Möbius inversion gives a density bound for the complete geometric sector,
with an explicit logarithmic discrepancy. It is not the sharper printed
constant-error estimate used in Huxley's Lemma 2.3. -/
theorem fareySector_card_lower_log (N : ℕ) {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) :
    (μ-l)*(N:ℝ)^2/8 ≤
      ((HuxleyLinearForm.fareySector N l μ).card:ℝ)+3*(N:ℝ)*(1+Real.log N) := by
  classical
  let C : ℕ → Finset ℕ := fun n =>
    (Finset.Ioc ⌊l*(n:ℝ)⌋₊ ⌊μ*(n:ℝ)⌋₊).filter (Nat.Coprime n)
  let U : ℕ → Finset (ℤ × ℤ) := fun n => (C n).image (fun m : ℕ => ((m:ℤ),(n:ℤ)))
  have hcard (n : ℕ) : (U n).card=(C n).card := by
    apply Finset.card_image_of_injective
    intro m k h
    exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  have hdis : (↑(Finset.Icc 1 N):Set ℕ).PairwiseDisjoint U := by
    intro n _hn k _hk hnk
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,_ha,ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b,_hb,hb⟩ := Finset.mem_image.mp hq
    exact hnk (Int.ofNat_inj.mp (congrArg Prod.snd (ha.trans hb.symm)))
  have hsub : (Finset.Icc 1 N).biUnion U ⊆ HuxleyLinearForm.fareySector N l μ := by
    intro p hp
    obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmI,hcop⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmL,hmU⟩ := Finset.mem_Ioc.mp hmI
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hn
    apply (HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlμ)).mpr
    refine ⟨by dsimp; exact_mod_cast hn1,by dsimp; exact_mod_cast hnN,hcop.symm.isCoprime,?_,?_⟩
    · simpa only [Int.cast_natCast] using (Nat.lt_of_floor_lt hmL).le
    · have hu := Nat.floor_le (mul_nonneg (hl.le.trans hlμ) (Nat.cast_nonneg n))
      have hmU' : (m:ℝ) ≤ ⌊μ*(n:ℝ)⌋₊ := by exact_mod_cast hmU
      simpa only [Int.cast_natCast] using hmU'.trans hu
  have hsumCard : (∑ n ∈ Finset.Icc 1 N, ((C n).card:ℝ)) ≤
      (HuxleyLinearForm.fareySector N l μ).card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdis] at hc
    simp only [hcard] at hc
    exact_mod_cast hc
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (μ-l)*(n.totient:ℝ) ≤ ((C n).card:ℝ)+3*n.divisors.card := by
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have he := coprime_interval_lower hn0
      (show (0:ℝ) ≤ l*(n:ℝ) by positivity)
      (mul_le_mul_of_nonneg_right hlμ (Nat.cast_nonneg n))
    have hid : (μ*(n:ℝ)-l*(n:ℝ))*((n.totient:ℝ)/(n:ℝ)) =
        (μ-l)*(n.totient:ℝ) := by
      field_simp [ne_of_gt (show (0:ℝ) < n by exact_mod_cast hn0)]
    rw [hid] at he
    exact he
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have htot := mul_le_mul_of_nonneg_left (sum_totient_lower N) (sub_nonneg.mpr hlμ)
  have hdiv := AtkinsonPrintedSource.sum_divisorCard_le_log N
  have hI : Finset.Ioc 0 N=Finset.Icc 1 N := by ext n; simp; omega
  rw [hI] at hdiv
  nlinarith only [hsum,htot,hdiv,hsumCard]

#print axioms fareySector_card_lower_log

end HuxleyFareyDensity

namespace HuxleySectorRegression

open TaoTrudgianYang2025.HuxleyLinearForm

example (N : ℕ) {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) :
    ((fareySector N l μ).card:ℝ) ≤ (μ-l)*(N:ℝ)*((N:ℝ)+1)/2+(N:ℝ) :=
  fareySector_card_le N hl hlμ

example {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ :=
  sector_consecutive_numerators hl hlμ hN hR

example {N : ℕ} {l μ B : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) :
    (N:ℝ) ≤ (B+1)*((fareySector N l μ).image Prod.snd).card :=
  sector_denominator_card_lower hl hlμ hN hR hdensity

example {N q : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hR : 2 ≤ (fareySector N l μ).card)
    (hdvd : ∀ p ∈ fareySector N l μ, q ∣ p.2.natAbs) : q=1 :=
  sector_denominator_common_divisor hl hμ hR hdvd

example {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card) :=
  fareySector_bounded_density_dichotomy hl hμ hB hδ hR hnear

example {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hlarge : 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) < (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p ∈ fareySector N l μ, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) :=
  fareySector_integer_labels hl hμ hB hδ hR hlarge hnear

end HuxleySectorRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_hasDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_linear_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_linear_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_homogeneous_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_of_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_taylor_of_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_homogeneous_taylor_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_ratio_coordinate_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_gap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.determinant_bound_of_cubic_ratios
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_small_deriv_of_two_values
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.four_point_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_cubic_ratio_abs_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_four_point_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_gap_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_eight_point_determinant
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.point_gap_of_minorArcCoordinate_gap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_minorArcCoordinate_abs
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_determinant

namespace HuxleyRationalPhaseRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (rationalBranch μ r s) x = 2/(3*μ*(r*x+s)^3) :=
  rationalBranch_second hμ hr hx

example
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
      b=p.1*(round (α-deriv g x₀))+p.2*(round (β-g x₀+x₀*deriv g x₀)) :=
  sector_nonlinear_integer_labels hl hv hlv hB hx₀ hν hr hν₁ hr₁ hd hδ hden hden₁ hratio hR hnear

example
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
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 6*|μ₁| * D₁^3*E/h^2 :=
  rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh hab hbc hcd hden hden₁ hD₁ ha hb hc hd

example
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
    |r*s₁-s*r₁| ≤ 4*|μ| * D^2*D₁^3*E/(q^2*h^3) :=
  rationalPhase_eight_point_determinant x hμ hr hμ₁ hr₁ hh hD hq hgap hden hden₁ hbound hbound₁ hratio hres

example {μ r s a b : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0) :
    minorArcCoordinate μ r s b-minorArcCoordinate μ r s a =
      -(b-a)/(3*μ*(r*b+s)*(r*a+s)) :=
  minorArcCoordinate_difference hμ hr ha hb

example
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
    |r*s₁-s*r₁| ≤ 1024*K*Kμ*R^4/(L^3*N^2) :=
  rationalPhase_long_block_determinant x hμ hr hμ₁ hr₁ hd hL hN hR hK hscale hmono hgap hden hden₁ hbound₁ hratio hres

end HuxleyRationalPhaseRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_ratio_mem_endpoint_interval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_bound_between
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_eight_point_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.ratio_relative_perturbation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_parameter_perturbation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubicTaylorCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_cubicCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubic_ratio_transfer
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_first_order_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_curvature_coordinate_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_taylor_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_taylor_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_round_error
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_round_error
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_rounded_halfCurvature_center
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_minorArcCoordinate_entry

namespace HuxleyPhysicalEntryRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {μ r s μ₁ r₁ s₁ d L N R K J A B : ℝ} (x : Fin 8 → ℝ)
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
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 256*J*K*R^2/(L^2*N^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_third_condition μ r s μ₁ r₁ s₁ d L N R K J A B x hμ hr hμ₁ hr₁ hd hL hN hR hK hJ hmono hgap hden hden₁ hbound₁ hres

example {σ δ T M A W a b a₁ b₁ H p q ε : ℝ} {F F₁ : ℝ → ℝ} (hσ : 0 < σ)
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
    |(iteratedDeriv 3 f₁ b₁/6)*p^3/((iteratedDeriv 3 f b/6)*q^3)-1| ≤ 3*ε+4*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubic_ratio_transfer σ δ T M A W a b a₁ b₁ H p q ε F F₁ hσ hδ hF hF₁ hT hM hA hW ha hb ha₁ hb₁ hH hH₁ hq

example {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a)| ≤ U*|b-a|^2/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_first_order_remainder f a b U hf hfourth

example {μ e r v s u t : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) :
    (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_curvature_coordinate_identity μ e r v s u t hμ hr ht hq hdet

example {σ δ T M A W a b e r v s u t δ₀ δ₁ : ℝ} {F : ℝ → ℝ}
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
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_taylor_entry σ δ T M A W a b e r v s u t δ₀ δ₁ F hσ hδ hF hT hM hA hW ha hb hr ht hq hdet

example {f : ℝ → ℝ} {W x U : ℝ}
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hf : ∀ y ∈ Set.Ioo 0 W, ContDiffAt ℝ 3 f y)
    (hthird : ∀ y ∈ Set.Ioo 0 W, |iteratedDeriv 3 f y| ≤ U) :
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_round_error f W x U hx hf hthird

example {σ δ T M A W l v q : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hl : l ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hv : v ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    q ∈ Set.uIcc (iteratedDeriv 2 f l/2) (iteratedDeriv 2 f v/2) →
    ∃ x ∈ Set.uIcc l v, iteratedDeriv 2 f x/2=q ∧
      (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-q| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_rounded_halfCurvature_center σ δ T M A W l v q F hσ hF hT hM hA hW hl hv

example {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
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
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_minorArcCoordinate_entry σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

end HuxleyPhysicalEntryRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_firstDerivative_halfCurvature_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_firstDerivative_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_integer_label
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.corrected_nonlinear_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_corrected_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_error_quadratic_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.corrected_residual_source_scale_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_residual_le_fourth_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_linearization_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_linearization_pair_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.nonlinearResidualConstant_nonneg
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_cubicCoefficient_pos
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels

namespace HuxleyResidualRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤ 5*U*|b-a|^3/12 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_remainder f a b U hf hfourth

example
    {e r v s u t n : ℤ} {d₀ d₁ : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let q : ℝ := r*u+s*t
    let c := round ((r:ℝ)*d₀)
    let θ := (r:ℝ)*d₀-c
    let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
    let H := ((c:ℝ)*s-n)*t/r+θ*q/r+γ
    round (q*d₁) = c*u+2*n*(e*u+v*t)+round H ∧
      q*d₁-round (q*d₁) = H-round H :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_integer_label e r v s u t n d₀ d₁ hr hq hdet

example
    {μ r s u t n δ E : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(E+2*δ*n+3*μ*n^2-n*t/(r*q))
    γ-n*t/r-t/r*(2*δ/(3*μ)-G) = q*(E+(n-G)*(3*μ*(n-G)+2*δ)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.corrected_nonlinear_residual_identity μ r s u t n δ E hμ hr ht hq

example {A B C₂ C₃ n M N R T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hn : 0 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) (hN : 0 < N)
    (hR : 1 ≤ R) (hT : 0 < T) (hscale : T*N*R^2=M^3) (hcube : n^3 ≤ M*R^2) :
    let K := A*(A+1)+(2*A+1)*B+B^2
    (T/M^3)*(C₃*n^3/(6*M)+C₂/2*(A+B*n^2/M)*(A+B*n^2/M+1)) ≤
      (C₃/3+C₂*K)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.corrected_residual_source_scale_budget A B C₂ C₃ n M N R T hA hB hC₂ hC₃ hn hM hnM hN hR hT hscale hcube

example
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
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)| ≤ nonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_residual_le_fourth_scale σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
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
      nonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_linearization σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
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
      Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear σ δ T M N R Δ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
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
    ∀ p ∈ S, h p=p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels K σ δ T M N R Δ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ

end HuxleyResidualRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sum_nonunit_inverse_square_le
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_positive_between
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_curvature_targets
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_displacement_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_centres
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_denominator_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_sector_nonlinear
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coprime_rectangle_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.isCoprime_unimodular_image
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_image_injective
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_rectangle_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_rectangle_fareySector_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_determinant_split
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.interval_filter_split_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interior_filter_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_separation_scaled
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_near_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_inner_endpoints
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_of_rational_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_source_density_gate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels_source_density

namespace HuxleyDensityRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {K : ℕ}
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
        |(round x:ℝ)-(round x₀:ℝ)|^3 ≤ M*R^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_centres K σ δ T M A W l w L U x₀ H R F e r v s hσ hF hT hM hA hW hL hU hl hlw hdenl hdenw hLdist hUdist hcube

example {K : ℕ} {l w : ℝ} {r s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    |(r:ℝ)*p.1+s*p.2| ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_denominator_bound K l w r s hl hlw hdenl hdenw p hp

example
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
          Δ+nonlinearResidualConstant σ δ*(K:ℝ)*(D 0+D 1)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_sector_nonlinear K σ δ T M N R Δ l w H F A W x₀ L U e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hL hU hr hdet hl hlw hdenl hdenw hLdist hUdist hcube

example (M N : ℕ) :
    (M:ℝ)*N/4 ≤
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.coprime_rectangle_card_lower M N

example
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (K:ℝ)^2/(64*(c:ℝ)*d) ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_interior_card_lower K a b c d l w hdet hc hd hcK hdK hl hlw ha hb

example {a b c d : ℤ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 1 < a*d-b*c) :
    ∃ m n : ℤ, 0 < n ∧ n ≤ max c d ∧ IsCoprime m n ∧
      0 < a*n-m*c ∧ a*n-m*c < a*d-b*c ∧
      0 < m*d-b*n ∧ m*d-b*n < a*d-b*c :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_determinant_split a b c d hc hd ha hb hdet

example
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 0 < a*d-b*c) (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (hsa : l ≤ (a:ℝ)/c ∧ (a:ℝ)/c ≤ w)
    (hsb : l ≤ (b:ℝ)/d ∧ (b:ℝ)/d ≤ w) :
    ((a:ℝ)/c-(b:ℝ)/d)*(K:ℝ)^2/64 ≤
      ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_fareySector_interior_card_lower K a b c d l w hc hd ha hb hdet hcK hdK hl hlw hsa hsb

example {H : ℕ} {x Δ : ℝ} {r : ℚ}
    (hΔ : 0 < Δ) (hH : 16*r.den ≤ H)
    (hscale : 8 ≤ Δ*(H:ℝ)*r.den) (hx : |x-(r:ℝ)| ≤ Δ) :
    ∃ q : ℚ, q.den ≤ H ∧ |x-(q:ℝ)| ≤ Δ/8 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_near_anchor H x Δ r hΔ hH hscale hx

example {H : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    ∃ a b : ℚ, a.den ≤ H ∧ b.den ≤ H ∧
      w-(w-l)/4 ≤ (a:ℝ) ∧ (a:ℝ) ≤ w ∧
      l ≤ (b:ℝ) ∧ (b:ℝ) ≤ l+(w-l)/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_inner_endpoints H l w r hlw hr hH hscale

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_source_scale K l w r hl hlw hr hden hscale

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    max ((w-l)*(K:ℝ)^2/128:ℝ) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_source_density_gate K l w r hl hlw hr hden hscale

example
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
      b=p.1*round (α-deriv g x₀)+p.2*round (β-g x₀+x₀*deriv g x₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels_source_density N l v ν r s ν₁ r₁ s₁ x₀ d ε α β δ a₀ hl hv hlv hx₀ ha₀ hcut hscale hν hr hν₁ hr₁ hd hδ hden hden₁ hratio hnear hbudget

end HuxleyDensityRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_rationalInterval_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_lower_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_growth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_width
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count_real
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_fareyCurvatureCoordinates_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_positive
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_curvature_count

namespace HuxleySignedCurvatureRegression

open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example {K : ℕ} {l w : ℝ} {p : ℤ × ℤ}
    (hlw : l ≤ w) :
    p ∈ rationalInterval K l w ↔ 1 ≤ p.2 ∧ p.2 ≤ K ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ w*p.2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_rationalInterval_iff K l w p hlw

example (K : ℕ) (l w : ℝ) :
    (rationalInterval K l w).card =
      (HuxleyLinearForm.fareySector K (l+(⌈1-l⌉:ℤ)) (w+(⌈1-l⌉:ℤ))).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_eq K l w

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤ (rationalInterval K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_lower_source_scale K l w r hlw hr hden hscale

example
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ*T/(2*M^3)*(y-x) ≤
      iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_growth σ δ T M A W x y F hσ hδ hF hT hM hA hW hx hy hxy

example
    {σ δ T M A W L U R : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo 0 W) (hU : U ∈ Set.Ioo 0 W) (hLU : L ≤ U)
    (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ/(2*R^2) ≤
      iteratedDeriv 2 f U/2-iteratedDeriv 2 f L/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_width σ δ T M A W L U R F hσ hδ hF hT hM hA hW hL hU hLU hR hscale

example
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
          T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count K σ δ T M A W L U R F r hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor

example
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
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count_real σ δ T M A W L U R Q F r hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    (hdet : v*r-e*s=1) :
    (fareyCurvatureCoordinates K l w e r v s).card=(rationalInterval K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_card K l w e r v s hdet

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hdet : v*r-e*s=1) :
    p ∈ fareyCurvatureCoordinates K l w e r v s ↔
      1 ≤ r*p.1+s*p.2 ∧ r*p.1+s*p.2 ≤ K ∧ IsCoprime p.1 p.2 ∧
        l*((r*p.1+s*p.2:ℤ):ℝ) ≤ (e*p.1+v*p.2:ℤ) ∧
        ((e*p.1+v*p.2:ℤ):ℝ) ≤ w*((r*p.1+s*p.2:ℤ):ℝ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_fareyCurvatureCoordinates_iff K l w e r v s p hlw hdet

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hr : 0 < r) (hs : 0 < s)
    (hl : (e:ℝ)/r < l) (hw : w < (v:ℝ)/s)
    (hp : p ∈ fareyCurvatureCoordinates K l w e r v s) : 0 < p.1 ∧ 0 < p.2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_positive K l w e r v s p hlw hr hs hl hw hp

example
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
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_curvature_count σ δ T M A W L U R Q F a₀ e r v s hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor hdet hr hs

end HuxleySignedCurvatureRegression
