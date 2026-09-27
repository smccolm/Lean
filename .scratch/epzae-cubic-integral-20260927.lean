import TaoTrudgianYang2025.SquareProductCount
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Literal cubic eighth-moment integral from the proved signed resonance count.
Reuse the existing two-frequency rectangular-window estimate, not a new kernel. -/

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025.CubicIntegralPrototype
open SquareProductCount SquareProductCount.CubicEight

theorem integral_integer_character (n : ℤ) :
    (∫ x : ℝ in Icc (0:ℝ) 1, fordAdditiveCharacter ((n:ℝ)*x))=
      if n=0 then (1:ℂ) else 0 := by
  by_cases hn : n=0
  · simp [hn,fordAdditiveCharacter]
  rw [if_neg hn,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  let c : ℂ := (n:ℂ)*(2*Real.pi*Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hn)
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (x : ℝ) : fordAdditiveCharacter ((n:ℝ)*x)=Complex.exp (c*x) := by
    unfold fordAdditiveCharacter c
    push_cast
    congr 1
    ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero]
  have hexp : Complex.exp c=1 := Complex.exp_int_mul_two_pi_mul_I n
  rw [hexp,sub_self,zero_div]

theorem integral_integer_planar_character (n m : ℤ) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      fordAdditiveCharacter ((n:ℝ)*α+(m:ℝ)*β))=
        if n=0 ∧ m=0 then (1:ℂ) else 0 := by
  simp_rw [fordAdditiveCharacter_add,integral_const_mul,integral_integer_character,
    integral_mul_const,integral_integer_character]
  by_cases hn : n=0 <;> by_cases hm : m=0 <;> simp [hn,hm]

theorem integer_planar_inner (n m : ℤ) (c : ℂ) (α : ℝ) :
    (∫ β : ℝ in Icc (0:ℝ) 1,
      c*fordAdditiveCharacter ((n:ℝ)*α+(m:ℝ)*β))=
      (c*fordAdditiveCharacter ((n:ℝ)*α))*(if m=0 then 1 else 0) := by
  simp_rw [fordAdditiveCharacter_add,←mul_assoc,integral_const_mul,integral_integer_character]

theorem integer_planar_norm_sq_integral {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℤ) :
    ((∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (u i:ℝ)) (fun i => (v i:ℝ)) α β‖^2 : ℝ):ℂ)=
      ∑p∈S ×ˢ S, if u p.1=u p.2 ∧ v p.1=v p.2 then z p.1*conj (z p.2) else 0 := by
  classical
  let A := fun (p : ι × ι) (α β : ℝ) => (z p.1*conj (z p.2))*
    fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α+((v p.1-v p.2:ℤ):ℝ)*β)
  have hi (p : ι × ι) (α : ℝ) : IntegrableOn (A p α) (Icc (0:ℝ) 1) := by
    have hc : Continuous (A p α) := by unfold A fordAdditiveCharacter; fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have he (p : ι × ι) (α : ℝ) : (∫ β : ℝ in Icc (0:ℝ) 1, A p α β)=
      (z p.1*conj (z p.2))*fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α)*
        (if v p.1-v p.2=0 then 1 else 0) :=
    integer_planar_inner _ _ _ α
  have ho (p : ι × ι) : IntegrableOn (fun α => ∫ β : ℝ in Icc (0:ℝ) 1, A p α β) (Icc (0:ℝ) 1) := by
    simp_rw [he]
    have hc : Continuous (fun α =>
        (z p.1*conj (z p.2))*fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α)*
          (if v p.1-v p.2=0 then 1 else 0)) := by unfold fordAdditiveCharacter; fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  rw [←integral_complex_ofReal]
  simp_rw [←integral_complex_ofReal,sargosPlanarSum_norm_sq]
  have hA : (fun (α β : ℝ) => ∑p∈S ×ˢ S,
      z p.1*conj (z p.2)*fordAdditiveCharacter
        (((u p.1:ℝ)-(u p.2:ℝ))*α+((v p.1:ℝ)-(v p.2:ℝ))*β))=
      fun α β => ∑p∈S ×ˢ S, A p α β := by simp only [A,Int.cast_sub]
  change (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
    (fun α β => ∑p∈S ×ˢ S, z p.1*conj (z p.2)*fordAdditiveCharacter
      (((u p.1:ℝ)-(u p.2:ℝ))*α+((v p.1:ℝ)-(v p.2:ℝ))*β)) α β)=_
  rw [hA]
  simp_rw [integral_finsetSum _ (fun p _ => hi p _)]
  rw [integral_finsetSum _ (fun p _ => ho p)]
  apply Finset.sum_congr rfl
  intro p _hp
  simp_rw [he,integral_mul_const,integral_const_mul,integral_integer_character]
  by_cases hu : u p.1=u p.2 <;> by_cases hv : v p.1=v p.2 <;> simp [sub_eq_zero,hu,hv]

theorem integer_planar_collision_compression {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v w : ι → ℤ)
    (hw : ∀i∈S, ∀j∈S, w i=w j ↔ u i=u j ∧ v i=v j) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (u i:ℝ)) (fun i => (v i:ℝ)) α β‖^2)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0‖^2 := by
  have hzero (x y : ℝ) :
      sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x y=
        sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0 := by
    simp only [sargosPlanarSum,zero_mul,add_zero]
  have he : (∫ x : ℝ in Icc (0:ℝ) 1, ∫ y : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x y‖^2)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0‖^2 := by
    simp_rw [hzero]
    simp only [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),
      sub_zero,one_mul]
  rw [←he]
  apply Complex.ofReal_injective
  have hwgram := integer_planar_norm_sq_integral S z w (fun _ => 0)
  simp only [Int.cast_zero] at hwgram
  rw [integer_planar_norm_sq_integral,hwgram]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  simp only [and_true,hw p.1 hi p.2 hj]

theorem integer_carry_separation {a b c d B : ℤ} (hB : 0 < B)
    (hab : |a-b| < B) : a+B*c=b+B*d ↔ a=b ∧ c=d := by
  constructor
  · intro h
    have he : a-b=-(B*(c-d)) := by linarith only [h]
    have ha := congrArg abs he
    rw [abs_neg,abs_mul,abs_of_pos hB] at ha
    have hcd : c=d := by
      by_contra hn
      have hg : 1 ≤ |c-d| := by
        have hp := abs_pos.mpr (sub_ne_zero.mpr hn)
        omega
      have hm := mul_le_mul_of_nonneg_left hg hB.le
      omega
    exact ⟨by rw [hcd] at h; omega,hcd⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def cubicTupleSet (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (1:ℤ) N)

def cubicFirst (n : Fin 4 → ℤ) : ℤ := ∑r, n r
def cubicSecond (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^2
def cubicThird (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^3
def cubicCombined (N : ℕ) (n : Fin 4 → ℤ) : ℤ := cubicFirst n+(8*(N:ℤ)+1)*cubicSecond n

theorem cubicTuple_abs {N : ℕ} {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) (r : Fin 4) :
    |n r| ≤ (N:ℤ) := by
  have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn r)
  rw [abs_of_nonneg (by omega)]
  exact hh.2

theorem cubicFirst_abs {N : ℕ} {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) :
    |cubicFirst n| ≤ 4*(N:ℤ) := by
  have hh := (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=n)).trans
    (Finset.sum_le_sum (fun r (_hr : r∈Finset.univ) => cubicTuple_abs hn r))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

theorem cubicCombined_collision {N : ℕ} {n m : Fin 4 → ℤ}
    (hn : n∈cubicTupleSet N) (hm : m∈cubicTupleSet N) :
    cubicCombined N n=cubicCombined N m ↔ cubicFirst n=cubicFirst m ∧ cubicSecond n=cubicSecond m := by
  have ha := (abs_sub_le (cubicFirst n) 0 (cubicFirst m)).trans
    (add_le_add (by simpa using cubicFirst_abs hn) (by simpa using cubicFirst_abs hm))
  have hb : 0 < 8*(N:ℤ)+1 := by positivity
  exact integer_carry_separation hb (by linarith only [ha])

def cubicSourceSum (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) : ℂ :=
  ∑ n∈Finset.Icc (1:ℤ) N,
    z n*fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ)

def cubicTupleCoefficient (z : ℤ → ℂ) (n : Fin 4 → ℤ) : ℂ := ∏r, z (n r)

theorem cubicSourceSum_fourth (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    (cubicSourceSum N z α β γ)^4=
      sargosPlanarSum (cubicTupleSet N)
        (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
        (fun n => (cubicFirst n:ℝ)) (fun n => (cubicSecond n:ℝ)) α β := by
  classical
  have hp : (cubicSourceSum N z α β γ)^4=∏ _r : Fin 4, cubicSourceSum N z α β γ := by simp
  rw [hp]
  unfold cubicSourceSum
  rw [Finset.prod_univ_sum]
  unfold sargosPlanarSum cubicTupleSet
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.prod_mul_distrib,sargos_character_finset_prod]
  unfold cubicTupleCoefficient
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  unfold cubicFirst cubicSecond cubicThird
  push_cast
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul]
  ring

theorem cubicSourceSum_eighth (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    ‖cubicSourceSum N z α β γ‖^8=
      ‖sargosPlanarSum (cubicTupleSet N)
        (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
        (fun n => (cubicFirst n:ℝ)) (fun n => (cubicSecond n:ℝ)) α β‖^2 := by
  rw [←cubicSourceSum_fourth,norm_pow,←pow_mul]

theorem cubic_modulation_sum (N : ℕ) (z : ℤ → ℂ) (x γ : ℝ) :
    sargosPlanarSum (cubicTupleSet N)
      (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
      (fun n => (cubicCombined N n:ℝ)) (fun _ => 0) x 0=
      sargosPlanarSum (cubicTupleSet N) (cubicTupleCoefficient z)
        (fun n => (cubicCombined N n:ℝ)) (fun n => (cubicThird n:ℝ)) x γ := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [mul_assoc,←fordAdditiveCharacter_add]
  simp only [zero_mul,add_zero]
  congr 2
  ring

theorem cubic_eighth_torus_eq_combined (N : ℕ) (z : ℤ → ℂ) (γ : ℝ) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖cubicSourceSum N z α β γ‖^8)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum (cubicTupleSet N) (cubicTupleCoefficient z)
          (fun n => (cubicCombined N n:ℝ)) (fun n => (cubicThird n:ℝ)) x γ‖^2 := by
  simp_rw [cubicSourceSum_eighth]
  rw [integer_planar_collision_compression (cubicTupleSet N) _ cubicFirst cubicSecond (cubicCombined N)
    (fun _ hn _ hm => cubicCombined_collision hn hm)]
  simp_rw [cubic_modulation_sum]

theorem cubicTupleCoefficient_norm {N : ℕ} {z : ℤ → ℂ}
    (hz : ∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) :
    ‖cubicTupleCoefficient z n‖ ≤ 1 := by
  unfold cubicTupleCoefficient
  rw [norm_prod]
  have hh := Finset.prod_le_prod (s:=Finset.univ) (f:=fun r => ‖z (n r)‖) (g:=fun _ => (1:ℝ))
    (fun r _ => norm_nonneg _) (fun r _ => hz _ (Fintype.mem_piFinset.mp hn r))
  simpa only [Finset.prod_const_one] using hh

theorem int_eq_of_real_half_gap {a b : ℤ} (h : |(a:ℝ)-(b:ℝ)| ≤ 1/2) : a=b := by
  have hh : |(a:ℝ)-(b:ℝ)| < 1 := lt_of_le_of_lt h (by norm_num)
  have hi : |a-b| < 1 := by exact_mod_cast hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg _)))

theorem exists_cubic_combined_near_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ((sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_eight_count hε
  refine ⟨2*C,by positivity,?_⟩
  intro N hN P hP
  let S := sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
    (fun n => (cubicThird n:ℝ)) (1/2) P
  have hbox (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      (∀r, |p.1 r| ≤ (N:ℤ)) ∧ ∀r, |p.2 r| ≤ (N:ℤ) := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨cubicTuple_abs hh.1,cubicTuple_abs hh.2⟩
  have hcollision (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      cubicFirst p.1=cubicFirst p.2 ∧ cubicSecond p.1=cubicSecond p.2 := by
    obtain ⟨hp,hfirst,_hthird⟩ := Finset.mem_filter.mp hp
    have hh := Finset.mem_product.mp hp
    exact (cubicCombined_collision hh.1 hh.2).mp (int_eq_of_real_half_gap hfirst)
  have hthird (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      |(∑r, (p.1 r)^3)-∑r, (p.2 r)^3| ≤ (⌈P⌉₊:ℤ) := by
    have hh := (Finset.mem_filter.mp hp).2.2
    have hb : |(cubicThird p.1:ℝ)-(cubicThird p.2:ℝ)| ≤ (⌈P⌉₊:ℝ) :=
      hh.trans (Nat.le_ceil P)
    exact_mod_cast hb
  have hh := h N hN ⌈P⌉₊ S hbox (fun p hp => (hcollision p hp).1)
    (fun p hp => (hcollision p hp).2) hthird
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hceil : (⌈P⌉₊:ℝ) ≤ P+1 := (Nat.ceil_lt_add_one hP).le
  have hscale : (N:ℝ)^2+⌈P⌉₊ ≤ 2*((N:ℝ)^2+P) := by nlinarith
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) ((2:ℝ)+ε))
  exact hs.trans_eq (by ring)

def cubicEighthMoment (N : ℕ) (z : ℤ → ℂ) (P : ℝ) : ℝ :=
  ∫ γ : ℝ in Icc (0:ℝ) (1/P), ∫ α : ℝ in Icc (0:ℝ) 1,
    ∫ β : ℝ in Icc (0:ℝ) 1, ‖cubicSourceSum N z α β γ‖^8

theorem cubicEighthMoment_le_count (N : ℕ) (z : ℤ → ℂ)
    (hz : ∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) {P : ℝ} (hP : 0 < P) :
    P*cubicEighthMoment N z P ≤
      32*((sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) := by
  let S := cubicTupleSet N
  let Z := cubicTupleCoefficient z
  let u := fun n => (cubicCombined N n:ℝ)
  let v := fun n => (cubicThird n:ℝ)
  let F := fun p : ℝ × ℝ => ‖sargosPlanarSum S Z u v p.1 p.2‖^2
  have hwindow : 0 < 1/P := by positivity
  have hi := integrable_sargosPlanarNormSq_rectangle S Z u v 0 1 0 (1/P)
  simp only [zero_add] at hi
  have he : cubicEighthMoment N z P=
      ∫ x : ℝ in Icc (0:ℝ) 1, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ) := by
    unfold cubicEighthMoment
    simp_rw [cubic_eighth_torus_eq_combined]
    exact (integral_prod_symm F hi).symm.trans (integral_prod F hi)
  have houter := integrable_sargosPlanarNormSq_window_outer S Z u v 0 2 0 (1/P)
  simp only [zero_add] at houter
  have hsubset : Icc (0:ℝ) 1 ⊆ Icc (0:ℝ) 2 := Icc_subset_Icc_right (by norm_num)
  have hmono : (∫ x : ℝ in Icc (0:ℝ) 1, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ)) ≤
      ∫ x : ℝ in Icc (0:ℝ) 2, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ) := by
    apply setIntegral_mono_set houter
      (Filter.Eventually.of_forall (fun x => integral_nonneg (fun γ => sq_nonneg _)))
    exact Filter.Eventually.of_forall (fun x hx => hsubset hx)
  have hz' (n : Fin 4 → ℤ) (hn : n∈S) : ‖Z n‖ ≤ 1 := cubicTupleCoefficient_norm hz hn
  have hw := sargosPlanar_window_le_nearPairs S Z u v hz' (δ:=2) (lambda:=1/P)
    (by norm_num) hwindow 0 0
  norm_num only [zero_add,show (16:ℝ)*2=32 by norm_num,one_div_one_div] at hw
  have hh := hmono.trans hw
  rw [he]
  have hp := mul_le_mul_of_nonneg_left hh hP.le
  apply hp.trans_eq
  field_simp
  rfl

/-- The literal weighted cubic eighth moment, in the original physical
window and normalized additive-character convention. -/
theorem exists_cubic_eighth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 < P →
      ∀ (z : ℤ → ℂ), (∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      P*cubicEighthMoment N z P ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_combined_near_count hε
  refine ⟨32*C,by positivity,?_⟩
  intro N hN P hP z hz
  have hh := (cubicEighthMoment_le_count N z hz hP).trans
    (mul_le_mul_of_nonneg_left (h N hN P hP.le) (by norm_num : (0:ℝ) ≤ 32))
  exact hh.trans_eq (by ring)

/-- Explicit unweighted original finite sum; the constant is independent
of both the length and the reciprocal cubic window. -/
theorem exists_cubic_eighth_moment_unweighted {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 < P →
      P*(∫ γ : ℝ in Icc (0:ℝ) (1/P), ∫ α : ℝ in Icc (0:ℝ) 1,
        ∫ β : ℝ in Icc (0:ℝ) 1,
          ‖∑ n∈Finset.Icc (1:ℤ) N,
            fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ)‖^8) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_eighth_moment hε
  refine ⟨C,hC,?_⟩
  intro N hN P hP
  simpa only [cubicEighthMoment,cubicSourceSum,one_mul] using
    h N hN P hP (fun _ => 1) (fun _ _ => by norm_num)

#print axioms exists_cubic_eighth_moment_unweighted
#print axioms cubicEighthMoment_le_count
#print axioms exists_cubic_eighth_moment
#print axioms cubicSourceSum_fourth
#print axioms cubicSourceSum_eighth
#print axioms cubic_modulation_sum
#print axioms cubic_eighth_torus_eq_combined
#print axioms cubicTupleCoefficient_norm
#print axioms int_eq_of_real_half_gap
#print axioms exists_cubic_combined_near_count
#print axioms integer_planar_collision_compression
#print axioms integer_carry_separation
#print axioms cubicTuple_abs
#print axioms cubicFirst_abs
#print axioms cubicCombined_collision
#print axioms integer_planar_inner
#print axioms integer_planar_norm_sq_integral
#print axioms integral_integer_character
#print axioms integral_integer_planar_character

-- Regression: the compressed frequency retains both moments, without
-- identifying distinct tuples or erasing a nonzero cubic difference.
example : cubicCombined 8 ![1,4,6,7]=cubicCombined 8 ![2,3,5,8] ∧
    cubicThird ![1,4,6,7]-cubicThird ![2,3,5,8]=(-48:ℤ) := by
  norm_num [cubicCombined,cubicFirst,cubicSecond,cubicThird,Fin.sum_univ_succ]

example : (![1,4,6,7] : Fin 4 → ℤ)∈cubicTupleSet 8 ∧
    (![2,3,5,8] : Fin 4 → ℤ)∈cubicTupleSet 8 := by
  constructor <;> simp only [cubicTupleSet,Fintype.mem_piFinset,Finset.mem_Icc] <;>
    intro r <;> fin_cases r <;> norm_num

example : (∫ x : ℝ in Icc (0:ℝ) 1, fordAdditiveCharacter ((1:ℤ)*x))=0 := by
  simpa using integral_integer_character 1

example : (∫ x : ℝ in Icc (0:ℝ) 1, fordAdditiveCharacter ((0:ℤ)*x))=1 := by
  simpa using integral_integer_character 0

example {a b : ℤ} (h : |(a:ℝ)-(b:ℝ)| ≤ 1/2) : a=b :=
  int_eq_of_real_half_gap h

example {c d : ℤ} : (16+33*c=(-16:ℤ)+33*d) ↔ ((16:ℤ)= -16 ∧ c=d) :=
  integer_carry_separation (by norm_num) (by norm_num)

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 < P →
      ∀ (z : ℤ → ℂ), (∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      P*cubicEighthMoment N z P ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) :=
  exists_cubic_eighth_moment hε

example {P : ℝ} (hP : 0 < P) (z : ℤ → ℂ) (hz : ‖z 1‖ ≤ 1) :
    P*cubicEighthMoment 1 z P ≤
      32*((sargosNearPairs (cubicTupleSet 1) (fun n => (cubicCombined 1 n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) := by
  apply cubicEighthMoment_le_count 1 z _ hP
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have he : n=1 := by omega
  simpa [he] using hz

end TaoTrudgianYang2025.CubicIntegralPrototype
