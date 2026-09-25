import TaoTrudgianYang2025.SargosDoubleLargeSieve
import TaoTrudgianYang2025.RobertSargosNonzeroPartialSummation
import TaoTrudgianYang2025.TruncatedDyadicPartition
import TaoTrudgianYang2025.RobertSargosTaylorCount
import GafniTao.HeathBrownSpacingRealBound
import GafniTao.HeathBrownHarmonicBound

/-! Actual signed polynomial boxes for the Robert--Sargos sieve. The support,
frequency bounds, and dyadic labels are derived from the source prefixes. -/

noncomputable section
open GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

def robertSargosPrefixBox (H Q : ℕ) (r : ℤ) (positive : Bool) (X Y N : ℕ) :
    Finset (ℤ × ℤ × ℤ) :=
  let A : ℤ := if positive then 1 else 1-Q
  let B := max (H:ℤ) (H-r)
  Finset.Icc A (A+X-1) ×ˢ (Finset.Icc B (B+Y-1) ×ˢ Finset.Icc (1:ℤ) N)

theorem robertSargos_signed_prefix_eq_box (f : ℝ → ℝ) (H Q : ℕ) (r m : ℤ)
    (positive : Bool) (X Y N : ℕ) :
    robertSargosSignedPolynomialPrefix f H Q r m positive X Y N =
      ∑ p ∈ robertSargosPrefixBox H Q r positive X Y N,
        robertSargosPolynomialCharacter f m r p.1 p.2.1 p.2.2 := by
  unfold robertSargosPrefixBox robertSargosSignedPolynomialPrefix
  simp only [Finset.sum_product]
  simp_rw [sargos_sum_Icc_eq_range]
  have hX (a : ℤ) : (a+X-1+1-a).toNat = X := by omega
  have hY (b : ℤ) : (b+Y-1+1-b).toNat = Y := by omega
  have hN : ((N:ℤ)+1-1).toNat = N := by omega
  simp only [hX,hY,hN]
  cases positive <;> simp

theorem robertSargos_prefix_box_support (H Q : ℕ) (r : ℤ)
    (positive : Bool) (X Y N : ℕ)
    (hX : X ≤ Q-1) (hY : Y ≤ (robertSargosHOverlap H r).card)
    (p : ℤ × ℤ × ℤ) (hp : p ∈ robertSargosPrefixBox H Q r positive X Y N) :
    p.1 ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0 ∧
      p.2.1 ∈ robertSargosHOverlap H r ∧ p.2.2 ∈ Finset.Icc 1 (N:ℤ) ∧
      (if positive then 0 < p.1 else p.1 < 0) := by
  simp only [robertSargosPrefixBox,Finset.mem_product,Finset.mem_Icc] at hp
  have hq : -(Q:ℤ) < p.1 ∧ p.1 < Q ∧ p.1 ≠ 0 ∧
      (if positive then 0 < p.1 else p.1 < 0) := by
    cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hp ⊢ <;> omega
  refine ⟨Finset.mem_erase.mpr ⟨hq.2.2.1,Finset.mem_Ioo.mpr ⟨hq.1,hq.2.1⟩⟩,
    ?_,Finset.mem_Icc.mpr hp.2.2,hq.2.2.2⟩
  simp only [robertSargosHOverlap,Int.card_Icc] at hY
  simp only [robertSargosHOverlap,Finset.mem_Icc]
  omega

theorem robertSargos_box_frequency_bounds {A : ℝ} {r q h n : ℝ} {Q : ℕ}
    (hA : 0 ≤ A) (hAQ : A ≤ Q) (hr : |r| ≤ A) (hq : |q| ≤ Q)
    (hh : |h| ≤ 2*A) (hn : |n| ≤ Q) :
    |h*q-r*n| ≤ 3*A*Q ∧
      |robertSargosTaylorQuadratic r q h n| ≤ 13*A*(Q:ℝ)^2 := by
  have hQ : (0:ℝ) ≤ Q := Nat.cast_nonneg _
  have hlin : |h*q-r*n| ≤ |h| *|q| +|r| *|n| := by
    simpa only [abs_mul] using abs_sub (h*q) (r*n)
  have hq2 : |q|^2 ≤ (Q:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) hq 2
  have hn2 : |n|^2 ≤ (Q:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) hn 2
  have hr2 : |r|^2 ≤ A^2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hh2 : |h|^2 ≤ (2*A)^2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hAQ2 : A^2 ≤ (Q:ℝ)^2 := pow_le_pow_left₀ hA hAQ 2
  have h₁ : |h| *|q| ≤ 2*A*Q :=
    mul_le_mul hh hq (abs_nonneg _) (by positivity)
  have h₂ : |r| *|n| ≤ A*Q := mul_le_mul hr hn (abs_nonneg _) hA
  constructor
  · linarith
  have t₁ : |h| *|q|^2 ≤ 2*A*(Q:ℝ)^2 :=
    mul_le_mul hh hq2 (sq_nonneg _) (by positivity)
  have t₂ : 2*|h| *|q| *|n| ≤ 4*A*(Q:ℝ)^2 := by
    have h := mul_le_mul h₁ hn (abs_nonneg _) (by positivity)
    nlinarith
  have t₃ : |r| *|n|^2 ≤ A*(Q:ℝ)^2 :=
    mul_le_mul hr hn2 (sq_nonneg _) hA
  have t₄ : |r| *|h|^2 ≤ 4*A*(Q:ℝ)^2 := by
    have h := mul_le_mul hr hh2 (sq_nonneg _) hA
    have h' := mul_le_mul_of_nonneg_left hAQ2 hA
    nlinarith
  have t₅ : |r|^2*|h| ≤ 2*A*(Q:ℝ)^2 := by
    have h := mul_le_mul hr2 hh (abs_nonneg _) (sq_nonneg A)
    have h' := mul_le_mul_of_nonneg_left hAQ2 hA
    nlinarith
  have htri :
      |robertSargosTaylorQuadratic r q h n| ≤
        |h| *|q|^2+2*|h| *|q| *|n| +|r| *|n|^2+|r| *|h|^2+|r|^2*|h| := by
    unfold robertSargosTaylorQuadratic
    calc
      _ ≤ |h*q^2+2*h*q*n-r*n^2-r*h^2| +|r^2*h| := abs_sub _ _
      _ ≤ (|h*q^2+2*h*q*n-r*n^2| +|r*h^2|)+|r^2*h| := by
        gcongr
        exact abs_sub _ _
      _ ≤ ((|h*q^2+2*h*q*n| +|r*n^2|)+|r*h^2|)+|r^2*h| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (((|h*q^2| +|2*h*q*n|)+|r*n^2|)+|r*h^2|)+|r^2*h| := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by simp only [abs_mul,abs_pow,abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  linarith


theorem robertSargos_third_derivative_source_range (f : ℝ → ℝ) (M : ℕ)
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam)
    (x : ℝ) (hx : x ∈ Icc (1:ℝ) M) :
    iteratedDeriv 3 f x ∈
      Icc (iteratedDeriv 3 f 1) (iteratedDeriv 3 f 1+C*lam*M) := by
  have hin y (hy : y ∈ Icc 1 x) : y ∈ Icc (1:ℝ) M := ⟨hy.1,hy.2.trans hx.2⟩
  have h := derivative_increment_bounds (iteratedDeriv 3 f) (iteratedDeriv 4 f)
    hx.1 (fun y hy => hasDerivAt_iteratedDeriv_finite
      (by norm_num : 3 < 4) (hf y (hin y hy)))
    (fun y hy => hlo y (hin y hy)) (fun y hy => hhi y (hin y hy))
  constructor
  · have ht : 0 ≤ lam*(x-1) := mul_nonneg hlam (sub_nonneg.mpr hx.1)
    linarith [h.1]
  · have ht := mul_le_mul_of_nonneg_left (show x-1 ≤ (M:ℝ) by linarith [hx.2])
      (mul_nonneg hC hlam)
    linarith [h.2]

def robertSargosDyadicPrefixBox (H Q : ℕ) (r : ℤ) (positive : Bool) (X Y N j : ℕ) :
    Finset (ℤ × ℤ × ℤ) :=
  (robertSargosPrefixBox H Q r positive X Y N).filter
    (fun p => Nat.log 2 p.1.natAbs = j)

theorem robertSargos_prefix_box_log_lt (H Q : ℕ) (r : ℤ)
    (positive : Bool) (X Y N : ℕ)
    (hX : X ≤ Q-1) (hY : Y ≤ (robertSargosHOverlap H r).card)
    (p : ℤ × ℤ × ℤ) (hp : p ∈ robertSargosPrefixBox H Q r positive X Y N) :
    Nat.log 2 p.1.natAbs < Nat.clog 2 Q := by
  have hs := (robertSargos_prefix_box_support H Q r positive X Y N hX hY p hp).1
  have hq := Finset.mem_erase.mp hs
  have hqi := Finset.mem_Ioo.mp hq.2
  have hi : |p.1| < (Q:ℤ) := abs_lt.mpr ⟨hqi.1,hqi.2⟩
  have hn : p.1.natAbs < Q := by
    have hc : (p.1.natAbs:ℤ) < Q := by simpa only [Int.natCast_natAbs] using hi
    exact_mod_cast hc
  exact Nat.log_lt_of_lt_pow ((Int.natAbs_pos.mpr hq.1).ne')
    (hn.trans_le (Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) Q))

theorem robertSargos_dyadic_prefix_q_range (H Q : ℕ) (r : ℤ)
    (positive : Bool) (X Y N j : ℕ)
    (hX : X ≤ Q-1) (hY : Y ≤ (robertSargosHOverlap H r).card)
    (p : ℤ × ℤ × ℤ) (hp : p ∈ robertSargosDyadicPrefixBox H Q r positive X Y N j) :
    |(p.1:ℝ)| ∈ Icc ((2:ℝ)^j) (2*(2:ℝ)^j) := by
  have hp' := Finset.mem_filter.mp hp
  have hs := (robertSargos_prefix_box_support H Q r positive X Y N hX hY p hp'.1).1
  have hne := (Finset.mem_erase.mp hs).1
  have hlo := Nat.pow_log_le_self 2 ((Int.natAbs_pos.mpr hne).ne')
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) p.1.natAbs
  rw [hp'.2] at hlo hhi
  rw [pow_succ] at hhi
  have he : (p.1.natAbs:ℝ) = |(p.1:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun n : ℤ => (n:ℝ)) (Int.natCast_natAbs p.1)
  constructor
  · have h : (2:ℝ)^j ≤ p.1.natAbs := by exact_mod_cast hlo
    rwa [he] at h
  · have h : (p.1.natAbs:ℝ) ≤ (2:ℝ)^j*2 := by exact_mod_cast hhi.le
    rw [he] at h
    linarith


theorem robertSargos_prefix_box_frequency_bounds {A : ℝ}
    (H Q : ℕ) (r : ℤ) (positive : Bool) (X Y N : ℕ)
    (hA : 0 ≤ A) (hAQ : A ≤ Q) (hH : (H:ℝ) ≤ A) (hr : |(r:ℝ)| ≤ A)
    (hX : X ≤ Q-1) (hY : Y ≤ (robertSargosHOverlap H r).card) (hN : N ≤ Q)
    (p : ℤ × ℤ × ℤ) (hp : p ∈ robertSargosPrefixBox H Q r positive X Y N) :
    |((p.2.1*p.1-r*p.2.2:ℤ):ℝ)| ≤ 3*A*Q ∧
      |robertSargosTaylorQuadratic r p.1 p.2.1 p.2.2| ≤ 13*A*(Q:ℝ)^2 := by
  obtain ⟨hq,hh,hn,_⟩ := robertSargos_prefix_box_support H Q r positive X Y N hX hY p hp
  have hqi := Finset.mem_Ioo.mp (Finset.mem_erase.mp hq).2
  have hq' : |(p.1:ℝ)| ≤ Q := by
    have hi : |p.1| ≤ (Q:ℤ) := (abs_lt.mpr ⟨hqi.1,hqi.2⟩).le
    exact_mod_cast hi
  have hhi := Finset.mem_Ico.mp ((mem_robertSargosHOverlap H p.2.1 r).mp hh).1
  have hh' : |(p.2.1:ℝ)| ≤ 2*A := by
    have hlo' : (H:ℝ) ≤ (p.2.1:ℝ) := by exact_mod_cast hhi.1
    have hhi' : (p.2.1:ℝ) < 2*(H:ℝ) := by exact_mod_cast hhi.2
    rw [abs_of_nonneg ((Nat.cast_nonneg H).trans hlo')]
    linarith
  have hni := Finset.mem_Icc.mp hn
  have hn' : |(p.2.2:ℝ)| ≤ Q := by
    have hlo' : (1:ℝ) ≤ (p.2.2:ℝ) := by exact_mod_cast hni.1
    have hhi' : (p.2.2:ℝ) ≤ N := by exact_mod_cast hni.2
    have hN' : (N:ℝ) ≤ Q := by exact_mod_cast hN
    rw [abs_of_nonneg (by linarith)]
    exact hhi'.trans hN'
  simpa only [Int.cast_sub,Int.cast_mul] using
    robertSargos_box_frequency_bounds hA hAQ hr hq' hh' hn'

def robertSargosSievePoint
    (p : Σ _ : ℤ, (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) : RobertSargosSevenPoint :=
  ⟨p.1,p.2.1.1,p.2.2.1,p.2.1.2.1,p.2.2.2.1,p.2.1.2.2,p.2.2.2.2⟩

theorem robertSargos_sieve_point_injective : Function.Injective robertSargosSievePoint := by
  rintro ⟨r,⟨⟨q₁,h₁,n₁⟩,⟨q₂,h₂,n₂⟩⟩⟩ ⟨s,⟨⟨q₃,h₃,n₃⟩,⟨q₄,h₄,n₄⟩⟩⟩ h
  simp only [robertSargosSievePoint,RobertSargosSevenPoint.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

def robertSargosSieveCollisions (R H Q : ℕ) (positive : ℤ → Bool)
    (X Y N : ℤ → ℕ) (j : ℕ) (E : ℝ) : Finset RobertSargosSevenPoint :=
  (((Finset.Ioo (-(R:ℤ)) R).erase 0).sigma (fun r =>
    sargosIntegerNearPairs (robertSargosDyadicPrefixBox H Q r (positive r) (X r) (Y r) (N r) j)
      (fun p => p.2.1*p.1-r*p.2.2)
      (fun p => robertSargosTaylorQuadratic r p.1 p.2.1 p.2.2) E)).image
        robertSargosSievePoint

theorem robertSargos_sieve_collisions_card (R H Q : ℕ) (positive : ℤ → Bool)
    (X Y N : ℤ → ℕ) (j : ℕ) (E : ℝ) :
    (robertSargosSieveCollisions R H Q positive X Y N j E).card =
      ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        (sargosIntegerNearPairs
          (robertSargosDyadicPrefixBox H Q r (positive r) (X r) (Y r) (N r) j)
          (fun p => p.2.1*p.1-r*p.2.2)
          (fun p => robertSargosTaylorQuadratic r p.1 p.2.1 p.2.2) E).card := by
  classical
  rw [robertSargosSieveCollisions,Finset.card_image_of_injective _ robertSargos_sieve_point_injective,
    Finset.card_sigma]

theorem robertSargos_sieve_collisions_system (R H Q : ℕ) (positive : ℤ → Bool)
    (X Y N : ℤ → ℕ) (j : ℕ) (E : ℝ)
    (hX : ∀ r, X r ≤ Q-1) (hY : ∀ r, Y r ≤ (robertSargosHOverlap H r).card)
    (hN : ∀ r, N r ≤ Q)
    (p : RobertSargosSevenPoint)
    (hp : p ∈ robertSargosSieveCollisions R H Q positive X Y N j E) :
    RobertSargosTaylorSystem R H ((2:ℝ)^j) Q E p := by
  classical
  obtain ⟨⟨r,⟨a,b⟩⟩,hmem,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hr,hab⟩ := Finset.mem_sigma.mp hmem
  obtain ⟨hr0,hri⟩ := Finset.mem_erase.mp hr
  have hri' := Finset.mem_Ioo.mp hri
  obtain ⟨hab,hlinear,hnear⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  obtain ⟨_,hha,hna,hsa⟩ := robertSargos_prefix_box_support H Q r (positive r)
    (X r) (Y r) (N r) (hX r) (hY r) a (Finset.mem_filter.mp ha).1
  obtain ⟨_,hhb,hnb,hsb⟩ := robertSargos_prefix_box_support H Q r (positive r)
    (X r) (Y r) (N r) (hX r) (hY r) b (Finset.mem_filter.mp hb).1
  have hhs (c : ℤ × ℤ × ℤ) (hc : c.2.1 ∈ robertSargosHOverlap H r) :
      (c.2.1:ℝ) ∈ Icc (H:ℝ) (2*H) := by
    have hi := Finset.mem_Ico.mp ((mem_robertSargosHOverlap H c.2.1 r).mp hc).1
    constructor
    · exact_mod_cast hi.1
    · have h : (c.2.1:ℝ) < 2*(H:ℝ) := by exact_mod_cast hi.2
      exact h.le
  have hns (c : ℤ × ℤ × ℤ) (hc : c.2.2 ∈ Finset.Icc (1:ℤ) (N r)) :
      (c.2.2:ℝ) ∈ Icc (1:ℝ) Q := by
    have hi := Finset.mem_Icc.mp hc
    constructor
    · exact_mod_cast hi.1
    · have h : c.2.2 ≤ (Q:ℤ) := hi.2.trans (by exact_mod_cast hN r)
      exact_mod_cast h
  refine ⟨hr0,?_,
    robertSargos_dyadic_prefix_q_range H Q r (positive r) (X r) (Y r) (N r) j (hX r) (hY r) a ha,
    robertSargos_dyadic_prefix_q_range H Q r (positive r) (X r) (Y r) (N r) j (hX r) (hY r) b hb,
    hhs a hha,hhs b hhb,hns a hna,hns b hnb,?_,hlinear,hnear⟩
  · change |(r:ℝ)| ≤ R
    have h : |r| ≤ (R:ℤ) := (abs_lt.mpr ⟨hri'.1,hri'.2⟩).le
    exact_mod_cast h
  · change 0 < a.1*b.1
    cases hsign : positive r <;> simp only [hsign,Bool.false_eq_true,ite_false,ite_true] at hsa hsb
    · exact mul_pos_of_neg_of_neg hsa hsb
    · exact mul_pos hsa hsb

theorem robertSargos_taylor_count_scale_mono {a b s t ε : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hs : 0 < s) (hst : s ≤ t) (hε : 0 ≤ ε) :
    (a*s)^(1+ε)*(1+b/s) ≤ (a*t)^(1+ε)*(1+b/t) := by
  have ht : 0 < t := hs.trans_le hst
  have expand (x : ℝ) (hx : 0 < x) :
      (a*x)^(1+ε)*(1+b/x) = (a*x)^ε*a*(x+b) := by
    rw [add_comm 1 ε,Real.rpow_add_one (mul_pos ha hx).ne']
    field_simp
  rw [expand s hs,expand t ht]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hst ha.le) hε) ha.le
  · linarith
  · positivity
  · positivity

theorem exists_robertSargos_sieve_collisions_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R H Q : ℕ) (positive : ℤ → Bool) (X Y N : ℤ → ℕ)
      (j : ℕ) (E : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ E → (R:ℝ) ≤ H/2 →
      (∀ r, X r ≤ Q-1) → (∀ r, Y r ≤ (robertSargosHOverlap H r).card) →
      (∀ r, N r ≤ Q) →
      ((robertSargosSieveCollisions R H Q positive X Y N j E).card:ℝ) ≤
        C*((R:ℝ)*Q*H*((2:ℝ)^j))^(1+ε)*
          (1+(E+12*R*(H:ℝ)^2)/((H:ℝ)*((2:ℝ)^j))) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_taylor_count ε hε
  refine ⟨C,hC,?_⟩
  intro R H Q positive X Y N j E hR hH hQ hE hRH hX hY hN
  apply hcount _ R H ((2:ℝ)^j) Q E
  · exact_mod_cast hR
  · exact_mod_cast hH
  · exact one_le_pow₀ (by norm_num) 
  · exact_mod_cast hQ
  · exact hE
  · exact hRH
  · exact robertSargos_sieve_collisions_system R H Q positive X Y N j E hX hY hN

theorem exists_robertSargos_sieve_collisions_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R H Q : ℕ) (positive : ℤ → Bool) (X Y N : ℤ → ℕ)
      (j : ℕ) (E : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ E → (R:ℝ) ≤ H/2 →
      (∀ r, X r ≤ Q-1) → (∀ r, Y r ≤ (robertSargosHOverlap H r).card) →
      (∀ r, N r ≤ Q) → j < Nat.clog 2 Q →
      ((robertSargosSieveCollisions R H Q positive X Y N j E).card:ℝ) ≤
        C*((R:ℝ)*Q*H*Q)^(1+ε)*(1+(E+12*R*(H:ℝ)^2)/((H:ℝ)*Q)) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_sieve_collisions_count ε hε
  refine ⟨C,hC,?_⟩
  intro R H Q positive X Y N j E hR hH hQ hE hRH hX hY hN hj
  have hRp : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hQp : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hpow : (2:ℝ)^j ≤ Q := by exact_mod_cast (Nat.pow_lt_of_lt_clog hj).le
  have hmono := robertSargos_taylor_count_scale_mono
    (a := (R:ℝ)*Q*H) (b := (E+12*R*(H:ℝ)^2)/H)
    (s := (2:ℝ)^j) (t := (Q:ℝ)) (by positivity) (by positivity)
    (by positivity) hpow hε.le
  have hm := mul_le_mul_of_nonneg_left hmono hC.le
  apply (hcount R H Q positive X Y N j E hR hH hQ hE hRH hX hY hN).trans
  simpa only [div_div,mul_assoc] using hm

theorem robertSargos_polynomial_character_coordinates (f : ℝ → ℝ) (m r : ℤ)
    (p : ℤ × ℤ × ℤ) :
    robertSargosPolynomialCharacter f m r p.1 p.2.1 p.2.2 =
      fordAdditiveCharacter (((p.2.1*p.1-r*p.2.2:ℤ):ℝ)*(2*iteratedDeriv 2 f m)+
        robertSargosTaylorQuadratic r p.1 p.2.1 p.2.2*iteratedDeriv 3 f m) := by
  unfold robertSargosPolynomialCharacter robertSargosLinear
  congr 1
  push_cast
  ring

theorem robertSargos_polynomial_sieve (f : ℝ → ℝ) (M R H Q : ℕ)
    (positive : ℤ → Bool) (X Y N : ℤ → ℕ) {A C lam : ℝ}
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hA : 0 < A) (hC : 0 < C) (hlam : 0 < lam)
    (hAQ : A ≤ Q) (hH : (H:ℝ) ≤ A) (hR : (R:ℝ) ≤ A)
    (hX : ∀ r, X r ≤ Q-1) (hY : ∀ r, Y r ≤ (robertSargosHOverlap H r).card)
    (hN : ∀ r, N r ≤ Q)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, ∑ m ∈ Finset.Icc (1:ℤ) M,
      ‖robertSargosSignedPolynomialPrefix f H Q r m (positive r) (X r) (Y r) (N r)‖)^2 ≤
      16384*(Nat.clog 2 Q:ℝ)*(((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
        (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
        ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
          (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m)
          (1/(3*A*Q)) (1/(13*A*(Q:ℝ)^2))).card:ℝ)*
        ∑ j ∈ Finset.range (Nat.clog 2 Q),
          ((robertSargosSieveCollisions R H Q positive X Y N j (1/(C*lam*M))).card:ℝ) := by
  classical
  have hMp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hQp : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let T := fun r => robertSargosPrefixBox H Q r (positive r) (X r) (Y r) (N r)
  let u := fun r (p : ℤ × ℤ × ℤ) => p.2.1*p.1-r*p.2.2
  let v := fun (r : ℤ) (p : ℤ × ℤ × ℤ) =>
    robertSargosTaylorQuadratic r p.1 p.2.1 p.2.2
  have hfreq (r : ℤ) (hr : r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0)
      (p : ℤ × ℤ × ℤ) (hp : p ∈ T r) :
      |(u r p:ℝ)| ≤ 3*A*Q ∧ |v r p| ≤ 13*A*(Q:ℝ)^2 := by
    have hri := Finset.mem_Ioo.mp (Finset.mem_erase.mp hr).2
    have hr' : |(r:ℝ)| ≤ R := by
      exact_mod_cast (abs_lt.mpr ⟨hri.1,hri.2⟩).le
    exact robertSargos_prefix_box_frequency_bounds H Q r (positive r) (X r) (Y r) (N r)
      hA.le hAQ hH (hr'.trans hR) (hX r) (hY r) (hN r) p hp
  have hb := sargos_double_large_sieve_partition
    ((Finset.Ioo (-(R:ℤ)) R).erase 0) (Finset.Icc (1:ℤ) M) T
    (fun _ _ => (1:ℂ)) (fun _ p => Nat.log 2 p.1.natAbs) (Nat.clog 2 Q)
    (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m) u v
    (X₁ := 3*A*Q) (X₂ := 13*A*(Q:ℝ)^2) (d := iteratedDeriv 3 f 1) (mu := C*lam*M)
    (by positivity) (by positivity) (by positivity) (by intros; norm_num)
    (by
      intro m hm
      have hm' : (m:ℝ) ∈ Icc (1:ℝ) M := by
        change (1:ℝ) ≤ (m:ℝ) ∧ (m:ℝ) ≤ M
        exact_mod_cast Finset.mem_Icc.mp hm
      exact robertSargos_third_derivative_source_range f M hC.le hlam.le hf hlo hhi m hm')
    (fun r hr p hp => (hfreq r hr p hp).1) (fun r hr p hp => (hfreq r hr p hp).2)
    (fun r _ p hp => robertSargos_prefix_box_log_lt H Q r (positive r)
      (X r) (Y r) (N r) (hX r) (hY r) p hp)
  have hcounts (j : ℕ) :
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        ((sargosIntegerNearPairs ((T r).filter (fun p => Nat.log 2 p.1.natAbs = j))
          (u r) (v r) (1/(C*lam*M))).card:ℝ)) =
      ((robertSargosSieveCollisions R H Q positive X Y N j (1/(C*lam*M))).card:ℝ) := by
    rw [robertSargos_sieve_collisions_card]
    simp only [Nat.cast_sum,T,u,v,robertSargosDyadicPrefixBox]
  simp only [one_mul] at hb
  simp_rw [hcounts] at hb
  simpa only [robertSargos_signed_prefix_eq_box,robertSargos_polynomial_character_coordinates,
    T,u,v] using hb

/-- The arithmetic factor in the source sieve is discharged by the proved
seven-variable theorem, uniformly over every signed prefix family. -/
theorem exists_robertSargos_counted_polynomial_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ) (M R H Q : ℕ)
      (positive : ℤ → Bool) (X Y N : ℤ → ℕ) (A C lam : ℝ),
    1 ≤ M → 1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 < A → 0 < C → 0 < lam →
    A ≤ Q → (H:ℝ) ≤ A → (R:ℝ) ≤ A → (R:ℝ) ≤ H/2 →
    (∀ r, X r ≤ Q-1) → (∀ r, Y r ≤ (robertSargosHOverlap H r).card) →
    (∀ r, N r ≤ Q) →
    (∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x) →
    (∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x) →
    (∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) →
    (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, ∑ m ∈ Finset.Icc (1:ℤ) M,
      ‖robertSargosSignedPolynomialPrefix f H Q r m (positive r) (X r) (Y r) (N r)‖)^2 ≤
      K*(Nat.clog 2 Q:ℝ)^2*(((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
        (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
        ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
          (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m)
          (1/(3*A*Q)) (1/(13*A*(Q:ℝ)^2))).card:ℝ)*
        ((R:ℝ)*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q)) := by
  classical
  obtain ⟨K,hK,hcount⟩ := exists_robertSargos_sieve_collisions_uniform ε hε
  refine ⟨16384*K,by positivity,?_⟩
  intro f M R H Q positive X Y N A C lam hM hR hH hQ hA hC hlam hAQ hHA hRA hRH
    hX hY hN hf hlo hhi
  have hMp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hE : 0 ≤ 1/(C*lam*M) := by positivity
  have hc :
      (∑ j ∈ Finset.range (Nat.clog 2 Q),
        ((robertSargosSieveCollisions R H Q positive X Y N j (1/(C*lam*M))).card:ℝ)) ≤
      (Nat.clog 2 Q:ℝ)*
        (K*((R:ℝ)*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (Nat.clog 2 Q),
          K*((R:ℝ)*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q)) :=
        Finset.sum_le_sum (fun j hj => hcount R H Q positive X Y N j _
          hR hH hQ hE hRH hX hY hN (Finset.mem_range.mp hj))
      _ = _ := by simp
  have hb := robertSargos_polynomial_sieve f M R H Q positive X Y N
    hM hQ hA hC hlam hAQ hHA hRA hX hY hN hf hlo hhi
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤
      16384*(Nat.clog 2 Q:ℝ)*(((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
        (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
        ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
          (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m)
          (1/(3*A*Q)) (1/(13*A*(Q:ℝ)^2))).card:ℝ) by positivity)
  apply hb.trans
  convert hm using 1; ring

/-- Heath--Brown spacing on the actual source interval starting at one.
No smoothness outside that interval is required. -/
theorem robertSargos_spacing_source_interval (S : Finset ℤ) (L : ℕ)
    (g gp : ℝ → ℝ) {mu V theta : ℝ} (hL : 1 ≤ L)
    (hmu : 0 < mu) (hV : 0 ≤ V) (htheta : 0 ≤ theta)
    (hg : ∀ x ∈ Icc (1:ℝ) L, HasDerivAt g (gp x) x)
    (hlo : ∀ x ∈ Icc (1:ℝ) L, mu ≤ gp x)
    (hhi : ∀ x ∈ Icc (1:ℝ) L, gp x ≤ V)
    (hS : ∀ n ∈ S, n ∈ Finset.Icc (1:ℤ) L ∧
      ∃ z : ℤ, |g n-z| ≤ theta) :
    (S.card:ℝ) ≤ 1+(2*theta/mu+1)*(V*L+2*theta+3) := by
  classical
  by_cases hLsmall : L ≤ 1
  · have hLeq : L = 1 := by omega
    have hsub : S ⊆ {1} := by
      intro n hn
      have hi := Finset.mem_Icc.mp (hS n hn).1
      simp only [hLeq,Nat.cast_one] at hi
      simp only [Finset.mem_singleton]
      omega
    have hc : (S.card:ℝ) ≤ 1 := by exact_mod_cast (Finset.card_le_card hsub)
    have hp : 0 ≤ (2*theta/mu+1)*(V*L+2*theta+3) := by positivity
    linarith
  have hN : 1 ≤ L-1 := by omega
  have hcast : ((L-1:ℕ):ℝ) = (L:ℝ)-1 := by
    rw [Nat.cast_sub hL,Nat.cast_one]
  have hin (x : ℝ) (hx : x ∈ Icc (0:ℝ) (L-1:ℕ)) :
      x+1 ∈ Icc (1:ℝ) L := by
    rw [hcast] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hder (x : ℝ) (hx : x ∈ Icc (0:ℝ) (L-1:ℕ)) :
      HasDerivAt (fun t => g (t+1)) (gp (x+1)) x := by
    simpa only [mul_one] using (hg (x+1) (hin x hx)).comp x ((hasDerivAt_id x).add_const 1)
  have hbound := heathBrown_spacing_card_cast_le
    (N := L-1) (g := fun t => g (t+1)) hN hmu htheta hV
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hder x ⟨hx.1.le,hx.2.le⟩).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hder x ⟨hx.1.le,hx.2.le⟩).deriv]
      exact hlo (x+1) (hin x ⟨hx.1.le,hx.2.le⟩))
    (fun x hx => by
      rw [(hder x ⟨hx.1.le,hx.2.le⟩).deriv]
      exact hhi (x+1) (hin x ⟨hx.1.le,hx.2.le⟩))
  let T := heathBrownSpacingSet (L-1) (fun t => g (t+1)) theta
  have hsub : S ⊆ insert 1 (T.image (fun n : ℕ => (n:ℤ)+1)) := by
    intro n hn
    rcases eq_or_ne n 1 with rfl | hn1
    · exact Finset.mem_insert_self _ _
    have hi := Finset.mem_Icc.mp (hS n hn).1
    obtain ⟨z,hz⟩ := (hS n hn).2
    have he : ((n-1).toNat:ℤ)+1 = n := by omega
    have he' : ((n-1).toNat:ℝ)+1 = (n:ℝ) := by exact_mod_cast he
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(n-1).toNat,?_,he⟩
    rw [mem_heathBrownSpacingSet]
    refine ⟨by omega,by omega,?_⟩
    rw [he']
    exact (round_le (g n) z).trans hz
  have hc : (S.card:ℝ) ≤ (T.card:ℝ)+1 := by
    have h := (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Finset.card_image_le) 1))
    exact_mod_cast h
  have hext : V*(L-1:ℕ)+2*theta+3 ≤ V*L+2*theta+3 := by
    rw [hcast]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hext (show 0 ≤ 2*theta/mu+1 by positivity)
  dsimp only [T] at hc
  linarith

theorem robertSargos_shifted_second_derivative (f : ℝ → ℝ) (M : ℕ)
    {C lam k x : ℝ} (hk : 0 ≤ k) (hx : 1 ≤ x) (hxk : x+k ≤ M)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) :
    HasDerivAt (fun t => 2*(iteratedDeriv 2 f (t+k)-iteratedDeriv 2 f t))
      (2*(iteratedDeriv 3 f (x+k)-iteratedDeriv 3 f x)) x ∧
    2*k*lam ≤ 2*(iteratedDeriv 3 f (x+k)-iteratedDeriv 3 f x) ∧
    2*(iteratedDeriv 3 f (x+k)-iteratedDeriv 3 f x) ≤ 2*C*k*lam := by
  have hin (t : ℝ) (ht : t ∈ Icc x (x+k)) : t ∈ Icc (1:ℝ) M :=
    ⟨hx.trans ht.1,ht.2.trans hxk⟩
  have hx' : x ∈ Icc (1:ℝ) M := ⟨hx,by linarith⟩
  have hxk' : x+k ∈ Icc (1:ℝ) M := ⟨by linarith,hxk⟩
  have hd₁ := hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 4) (hf x hx')
  have hd₂ := hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 4) (hf (x+k) hxk')
  have hinc := derivative_increment_bounds (iteratedDeriv 3 f) (iteratedDeriv 4 f)
    (show x ≤ x+k by linarith)
    (fun t ht => hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4) (hf t (hin t ht)))
    (fun t ht => hlo t (hin t ht)) (fun t ht => hhi t (hin t ht))
  refine ⟨?_,?_,?_⟩
  · simpa only [mul_one] using
      ((hd₂.comp x ((hasDerivAt_id x).add_const k)).sub hd₁).const_mul 2
  · nlinarith [hinc.1]
  · nlinarith [hinc.2]

def robertSargosSampleShift (f : ℝ → ℝ) (M k : ℕ) (theta : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (1:ℤ) (M-k:ℕ)).filter (fun m =>
    ∃ z : ℤ, |2*(iteratedDeriv 2 f ((m:ℝ)+k)-iteratedDeriv 2 f m)-z| ≤ theta)

theorem robertSargos_sample_shift_spacing (f : ℝ → ℝ) (M k : ℕ)
    {C lam theta : ℝ} (hk : 1 ≤ k) (hkM : k < M)
    (hC : 0 ≤ C) (hlam : 0 < lam) (htheta : 0 ≤ theta)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) :
    ((robertSargosSampleShift f M k theta).card:ℝ) ≤
      1+(theta/((k:ℝ)*lam)+1)*(2*C*k*lam*M+2*theta+3) := by
  classical
  have hkp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hL : 1 ≤ M-k := by omega
  have hcast : ((M-k:ℕ):ℝ) = (M:ℝ)-k := Nat.cast_sub hkM.le
  have hder (x : ℝ) (hx : x ∈ Icc (1:ℝ) (M-k:ℕ)) :=
    robertSargos_shifted_second_derivative f M (Nat.cast_nonneg k) hx.1
      (show x+(k:ℝ) ≤ M by rw [hcast] at hx; linarith [hx.2]) hf hlo hhi
  have hb := robertSargos_spacing_source_interval (robertSargosSampleShift f M k theta) (M-k)
    (fun t => 2*(iteratedDeriv 2 f (t+k)-iteratedDeriv 2 f t))
    (fun t => 2*(iteratedDeriv 3 f (t+k)-iteratedDeriv 3 f t))
    hL (show 0 < 2*(k:ℝ)*lam by positivity) (show 0 ≤ 2*C*k*lam by positivity) htheta
    (fun x hx => (hder x hx).1) (fun x hx => (hder x hx).2.1)
    (fun x hx => (hder x hx).2.2)
    (fun n hn => Finset.mem_filter.mp hn)
  have hfrac : 2*theta/(2*(k:ℝ)*lam) = theta/((k:ℝ)*lam) := by
    field_simp
  rw [hfrac] at hb
  apply hb.trans
  have hlen : ((M-k:ℕ):ℝ) ≤ M := by exact_mod_cast Nat.sub_le M k
  gcongr


private theorem sargos_periodic_pair_swap {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (theta delta : ℝ) {p : ι × ι} (hp : p ∈ sargosPeriodicNearPairs S x y theta delta) :
    p.swap ∈ sargosPeriodicNearPairs S x y theta delta := by
  classical
  obtain ⟨hmem,⟨z,hz⟩,hy⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hmem
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hb,ha⟩,⟨-z,?_⟩,?_⟩
  · change |x p.2-x p.1-((-z:ℤ):ℝ)| ≤ theta
    have he : x p.2-x p.1-((-z:ℤ):ℝ) = -(x p.1-x p.2-z) := by push_cast; ring
    rwa [he,abs_neg]
  · simpa only [Prod.swap,abs_sub_comm] using hy

theorem robertSargos_sample_positive_pair (f : ℝ → ℝ) (M : ℕ)
    {C lam theta delta : ℝ} (hlam : 0 < lam)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam)
    (a b : ℤ) (hab : a < b)
    (hp : (a,b) ∈ sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
      (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m) theta delta) :
    ∃ k ∈ Finset.Icc 1 ⌊delta/lam⌋₊,
      a ∈ robertSargosSampleShift f M k theta ∧ b = a+k := by
  classical
  obtain ⟨hmem,⟨z,hz⟩,hy⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hmem
  have hai := Finset.mem_Icc.mp ha
  have hbi := Finset.mem_Icc.mp hb
  let k := (b-a).toNat
  have hk : 1 ≤ k := by dsimp [k]; omega
  have he : (k:ℤ) = b-a := by dsimp [k]; omega
  have hkM : k < M := by omega
  have he' : (k:ℝ) = (b:ℝ)-(a:ℝ) := by exact_mod_cast he
  have hin (t : ℝ) (ht : t ∈ Icc (a:ℝ) b) : t ∈ Icc (1:ℝ) M :=
    ⟨(show (1:ℝ) ≤ (a:ℝ) by exact_mod_cast hai.1).trans ht.1,
      ht.2.trans (by exact_mod_cast hbi.2)⟩
  have hinc := derivative_increment_bounds (iteratedDeriv 3 f) (iteratedDeriv 4 f)
    (show (a:ℝ) ≤ b by exact_mod_cast hab.le)
    (fun t ht => hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4) (hf t (hin t ht)))
    (fun t ht => hlo t (hin t ht)) (fun t ht => hhi t (hin t ht))
  have hdelta : iteratedDeriv 3 f b-iteratedDeriv 3 f a ≤ delta := by
    apply (le_abs_self _).trans
    simpa only [abs_sub_comm] using hy
  have hkfloor : k ≤ ⌊delta/lam⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlam).mpr
    rw [he']
    nlinarith [hinc.1]
  refine ⟨k,Finset.mem_Icc.mpr ⟨hk,hkfloor⟩,?_,by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hai.1,by omega⟩,⟨-z,?_⟩⟩
  have hab' : (a:ℝ)+(k:ℝ) = (b:ℝ) := by linarith
  rw [hab']
  have heq : 2*(iteratedDeriv 2 f b-iteratedDeriv 2 f a)-((-z:ℤ):ℝ) =
      -(2*iteratedDeriv 2 f a-2*iteratedDeriv 2 f b-z) := by push_cast; ring
  rwa [heq,abs_neg]

theorem robertSargos_sample_pairs_shift_count (f : ℝ → ℝ) (M : ℕ)
    {C lam theta delta : ℝ} (hlam : 0 < lam)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) :
    ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
      (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m) theta delta).card:ℝ) ≤
      (M:ℝ)+2*∑ k ∈ Finset.Icc 1 ⌊delta/lam⌋₊,
        ((robertSargosSampleShift f M k theta).card:ℝ) := by
  classical
  let B := sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
    (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m) theta delta
  let D := (Finset.Icc (1:ℤ) M).image (fun m => (m,m))
  let U := (Finset.Icc 1 ⌊delta/lam⌋₊).sigma (fun k => robertSargosSampleShift f M k theta)
  let P := U.image (fun p => (p.2,p.2+(p.1:ℤ)))
  have hpos (a b : ℤ) (hab : a < b) (hp : (a,b) ∈ B) : (a,b) ∈ P := by
    obtain ⟨k,hk,ha,he⟩ := robertSargos_sample_positive_pair f M hlam hf hlo hhi a b hab hp
    apply Finset.mem_image.mpr
    exact ⟨⟨k,a⟩,Finset.mem_sigma.mpr ⟨hk,ha⟩,by simp only [he]⟩
  have hsub : B ⊆ D ∪ (P ∪ P.image Prod.swap) := by
    rintro ⟨a,b⟩ hp
    rcases lt_trichotomy a b with hab | hab | hab
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hpos a b hab hp))
    · subst b
      have ha := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    · have hs := sargos_periodic_pair_swap _ _ _ theta delta hp
      exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(b,a),hpos b a hab hs,rfl⟩))
  have hD : D.card ≤ M := by
    have hc : (Finset.Icc (1:ℤ) M).card = M := by simp [Int.card_Icc]
    exact Finset.card_image_le.trans_eq hc
  have hP : P.card ≤ ∑ k ∈ Finset.Icc 1 ⌊delta/lam⌋₊,
      (robertSargosSampleShift f M k theta).card := by
    have hc : U.card = ∑ k ∈ Finset.Icc 1 ⌊delta/lam⌋₊,
        (robertSargosSampleShift f M k theta).card := Finset.card_sigma _ _
    exact Finset.card_image_le.trans_eq hc
  have hcard : B.card ≤ M+2*∑ k ∈ Finset.Icc 1 ⌊delta/lam⌋₊,
      (robertSargosSampleShift f M k theta).card := by
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_union_le D (P ∪ P.image Prod.swap)
    have h₃ := Finset.card_union_le P (P.image Prod.swap)
    have h₄ : (P.image Prod.swap).card ≤ P.card := Finset.card_image_le
    omega
  exact_mod_cast hcard

/-- The sample-spacing factor is bounded by a harmonic loss once its explicit
physical-scale inequalities hold. No sample-count bound is an assumption. -/
theorem robertSargos_sample_pairs_spacing_bound (f : ℝ → ℝ) (M : ℕ)
    {C lam theta delta : ℝ} (hM : 1 ≤ M) (hC : 1 ≤ C) (hlam : 0 < lam)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hKM : ⌊delta/lam⌋₊ ≤ M)
    (hthetaK : theta*(⌊delta/lam⌋₊:ℝ) ≤ 1)
    (hlamK : lam*(⌊delta/lam⌋₊:ℝ)^2 ≤ 1)
    (hthetaM : theta ≤ lam*M)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) :
    ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
      (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m) theta delta).card:ℝ) ≤
      32*C*M*(1+Real.log M) := by
  classical
  let K := ⌊delta/lam⌋₊
  have hC0 : 0 ≤ C := by linarith
  have hL : 1 ≤ 1+Real.log (M:ℝ) := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ M by exact_mod_cast hM)
    linarith
  have hper (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      ((robertSargosSampleShift f M k theta).card:ℝ) ≤
        2*C*theta*M+2*C*lam*M*k+(5*theta/lam)*(k:ℝ)⁻¹+6 := by
    have hki := Finset.mem_Icc.mp hk
    have hkp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    by_cases hkM : k < M
    · have hb := robertSargos_sample_shift_spacing f M k hki.1 hkM hC0 hlam htheta hf hlo hhi
      have hm := mul_le_mul_of_nonneg_left
        (show 2*C*k*lam*M+2*theta+3 ≤ 2*C*k*lam*M+5 by linarith)
        (show 0 ≤ theta/((k:ℝ)*lam)+1 by positivity)
      have he : 1+(theta/((k:ℝ)*lam)+1)*(2*C*k*lam*M+5) =
          2*C*theta*M+2*C*lam*M*k+(5*theta/lam)*(k:ℝ)⁻¹+6 := by
        field_simp; ring
      rw [← he]
      linarith
    · have he : M-k = 0 := by omega
      have hempty : robertSargosSampleShift f M k theta = ∅ := by
        simp [robertSargosSampleShift,he]
      rw [hempty,Finset.card_empty,Nat.cast_zero]
      positivity
  have hsumk : (∑ k ∈ Finset.Icc 1 K, (k:ℝ)) ≤ (K:ℝ)^2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 K, (K:ℝ) :=
        Finset.sum_le_sum (fun k hk => by exact_mod_cast (Finset.mem_Icc.mp hk).2)
      _ = _ := by simp [sq]
  have hharm := harmonic_cast_le_one_add_log_of_le hKM hM
  have heq :
      (∑ k ∈ Finset.Icc 1 K,
        (2*C*theta*M+2*C*lam*M*k+(5*theta/lam)*(k:ℝ)⁻¹+6)) =
      (2*C*theta*M+6)*K+2*C*lam*M*(∑ k ∈ Finset.Icc 1 K, (k:ℝ))+
        (5*theta/lam)*(harmonic K:ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
      Nat.card_Icc,Nat.add_sub_cancel,← Finset.mul_sum]
    ring
  have hsum := Finset.sum_le_sum hper
  rw [heq] at hsum
  have hkterm := mul_le_mul_of_nonneg_left hsumk (show 0 ≤ 2*C*lam*M by positivity)
  have hhterm := mul_le_mul_of_nonneg_left hharm (show 0 ≤ 5*theta/lam by positivity)
  have h₁ := mul_le_mul_of_nonneg_left hthetaK (show 0 ≤ 2*C*M by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hlamK (show 0 ≤ 2*C*M by positivity)
  have hdiv : theta/lam ≤ M := (div_le_iff₀ hlam).mpr (by nlinarith only [hthetaM])
  have h₃ := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ 5*(1+Real.log (M:ℝ)) by linarith)
  have h₄ : (K:ℝ) ≤ M := by exact_mod_cast hKM
  have hCM : C*(M:ℝ) ≤ C*M*(1+Real.log M) :=
    le_mul_of_one_le_right (by positivity) hL
  have hML : (M:ℝ)*(1+Real.log M) ≤ C*M*(1+Real.log M) := by
    have h := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ (M:ℝ)*(1+Real.log M) by positivity)
    nlinarith only [h]
  have hMC : (M:ℝ) ≤ C*M*(1+Real.log M) := by
    have h := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (α := ℝ) M)
    nlinarith only [h,hCM]
  have hb := robertSargos_sample_pairs_shift_count f M (theta := theta) (delta := delta) hlam hf hlo hhi
  change _ ≤ (M:ℝ)+2*∑ k ∈ Finset.Icc 1 K,
    ((robertSargosSampleShift f M k theta).card:ℝ) at hb
  dsimp only [K] at hsum hkterm hb h₄
  simp only [div_eq_mul_inv] at hb hsum hkterm hhterm h₁ h₂ h₃ h₄
  have hMp : (0:ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith only [hb,hsum,hkterm,hhterm,h₁,h₂,h₃,h₄,hCM,hML,hMC,hMp]


private theorem robertSargos_spacing_scale_budgets (M Q : ℕ) {T lam : ℝ}
    (hT : 2 ≤ T) (hlam : 0 < lam) (hnorm : T^13*lam = 1)
    (hQ : T^3/2 ≤ (Q:ℝ)) (hM : T^8 ≤ M) :
    let theta := 1/(3*T^2*Q)
    let delta := 1/(13*T^2*(Q:ℝ)^2)
    0 ≤ theta ∧ theta ≤ 1 ∧ ⌊delta/lam⌋₊ ≤ M ∧
      theta*(⌊delta/lam⌋₊:ℝ) ≤ 1 ∧
      lam*(⌊delta/lam⌋₊:ℝ)^2 ≤ 1 ∧ theta ≤ lam*M := by
  dsimp only
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hQp : (0:ℝ) < Q := (by positivity : 0 < T^3/2).trans_le hQ
  have hT5 : 0 < T^5 := by positivity
  have hT5one : 1 ≤ T^5 := one_le_pow₀ hT1
  have hT58 : T^5 ≤ T^8 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT1013 : T^10 ≤ T^13 := pow_le_pow_right₀ hT1 (by norm_num)
  have hq2 : T^6 ≤ 4*(Q:ℝ)^2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ T^3/2 by positivity) hQ 2
    nlinarith only [h]
  have htheta : 1/(3*T^2*Q) ≤ 1/T^5 := by
    apply one_div_le_one_div_of_le hT5
    have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 3*T^2 by positivity)
    nlinarith only [h,show 0 ≤ T^5 by positivity]
  have hcut : (1/(13*T^2*(Q:ℝ)^2))/lam ≤ T^5 := by
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < 13*T^2*(Q:ℝ)^2*lam)).mpr
    have h := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ T^7*lam by positivity)
    have hn : T^13*lam = 1 := hnorm
    nlinarith only [h,hn]
  have hfloor : (⌊(1/(13*T^2*(Q:ℝ)^2))/lam⌋₊:ℝ) ≤ T^5 :=
    (Nat.floor_le (by positivity)).trans hcut
  have hfloor2 := pow_le_pow_left₀
    (Nat.cast_nonneg ⌊(1/(13*T^2*(Q:ℝ)^2))/lam⌋₊) hfloor 2
  have hprod := mul_le_mul htheta hfloor
    (Nat.cast_nonneg _) (le_of_lt (by positivity : 0 < 1/T^5))
  have hnorm5 : (1/T^5)*T^5 = 1 := by field_simp
  have hthetaLam : 1/T^5 = lam*T^8 := by
    apply (div_eq_iff hT5.ne').mpr
    nlinarith only [hnorm]
  refine ⟨by positivity,?_,?_,?_,?_,?_⟩
  · exact htheta.trans ((div_le_one hT5).mpr hT5one)
  · have h := hfloor.trans (hT58.trans hM)
    exact_mod_cast h
  · rwa [hnorm5] at hprod
  · have h := mul_le_mul_of_nonneg_left hfloor2 hlam.le
    have h' := mul_le_mul_of_nonneg_left hT1013 hlam.le
    nlinarith only [h,h',hnorm]
  · rw [hthetaLam] at htheta
    exact htheta.trans (mul_le_mul_of_nonneg_left hM hlam.le)


/-- Sample spacing at the literal floor scale from the C4 source hypotheses. -/
theorem robertSargos_physical_sample_spacing (f : ℝ → ℝ) (M : ℕ)
    {C lam : ℝ} (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hf : ∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t)
    (hlo : ∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t)
    (hhi : ∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) :
    let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
    let A := lam^(-(2:ℝ)/13)
    ((sargosPeriodicNearPairs (Finset.Icc (1:ℤ) M)
      (fun m => 2*iteratedDeriv 2 f m) (fun m => iteratedDeriv 3 f m)
      (1/(3*A*Q)) (1/(13*A*(Q:ℝ)^2))).card:ℝ) ≤ 32*C*M*(1+Real.log M) := by
  dsimp only
  let T := lam^(-(1:ℝ)/13)
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hn : T^13*lam = 1 := (thirteenth_root_physical_scale hlam hsmall).2
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have hT1 : 1 ≤ T := by linarith
  have hfloor := (positive_floor_half_bounds
    (show 1 ≤ lam^(-(3:ℝ)/13) by rw [← h3]; exact one_le_pow₀ hT1)).2.1
  rw [← h3] at hfloor
  have hM' : T^8 ≤ M := by rwa [h8]
  have hM1 : 1 ≤ M := by
    have h := (one_le_pow₀ hT1 : 1 ≤ T^8).trans hM'
    exact_mod_cast h
  obtain ⟨htheta,htheta1,hKM,hthetaK,hlamK,hthetaM⟩ :=
    robertSargos_spacing_scale_budgets M ⌊lam^(-(3:ℝ)/13)⌋₊ hT hlam hn (by simpa only [h3] using hfloor) hM'
  rw [← h2]
  exact robertSargos_sample_pairs_spacing_bound f M hM1 hC hlam
    htheta htheta1 hKM hthetaK hlamK hthetaM hf hlo hhi

end TaoTrudgianYang2025
