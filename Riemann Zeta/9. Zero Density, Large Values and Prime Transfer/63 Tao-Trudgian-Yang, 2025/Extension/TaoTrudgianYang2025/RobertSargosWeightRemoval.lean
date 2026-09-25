import TaoTrudgianYang2025.RobertSargosMixedJets
import TaoTrudgianYang2025.RobertSargosRectangularAbel
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Source-derived mixed exponential derivatives and uniform rectangular Abel variation. -/

noncomputable section
open GafniTao Set
open scoped ContDiff
namespace TaoTrudgianYang2025

private theorem hasDerivAt_robertSargos_character {g : ℝ → ℝ} {g' x : ℝ}
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => fordAdditiveCharacter (g y))
      (fordAdditiveCharacter (g x)*((2*Real.pi*Complex.I)*(g':ℂ))) x := by
  exact (hg.ofReal_comp.const_mul (2*Real.pi*Complex.I)).cexp

def robertSargosCharacterJet (f : ℝ → ℝ) (m r : ℝ) (a b c : Bool)
    (q h n : ℝ) : ℂ :=
  let J := fun i j k => (robertSargosMixedJet f m r i j k q h n : ℂ)
  let t : ℂ := 2*Real.pi*Complex.I
  let E := fordAdditiveCharacter (robertSargosMixedRemainder f m r q h n)
  match a,b,c with
  | false,false,false => E
  | true,false,false => t*J 1 0 0*E
  | false,true,false => t*J 0 1 0*E
  | false,false,true => t*J 0 0 1*E
  | true,true,false => (t*J 1 1 0+t^2*J 1 0 0*J 0 1 0)*E
  | true,false,true => (t*J 1 0 1+t^2*J 1 0 0*J 0 0 1)*E
  | false,true,true => (t*J 0 1 1+t^2*J 0 1 0*J 0 0 1)*E
  | true,true,true =>
      (t*J 1 1 1+t^2*(J 1 1 0*J 0 0 1+J 1 0 1*J 0 1 0+
        J 0 1 1*J 1 0 0)+t^3*J 1 0 0*J 0 1 0*J 0 0 1)*E

theorem hasDerivAt_robertSargos_character_jet_q
    {f : ℝ → ℝ} {m r q h n : ℝ} (b c : Bool)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h))) :
    HasDerivAt (fun x => robertSargosCharacterJet f m r false b c x h n)
      (robertSargosCharacterJet f m r true b c q h n) q := by
  let t : ℂ := 2*Real.pi*Complex.I
  have hd (j k : ℕ) (hj : j+k < 4) :
      HasDerivAt (fun x => (robertSargosMixedJet f m r 0 j k x h n : ℂ))
        (robertSargosMixedJet f m r 1 j k q h n : ℂ) q :=
    (hasDerivAt_robertSargos_mixed_jet_q (by simpa using hj) hp hm).ofReal_comp
  have hzero : HasDerivAt (fun x => robertSargosMixedRemainder f m r x h n)
      (robertSargosMixedJet f m r 1 0 0 q h n) q := by
    simpa only [robertSargos_mixed_jet_zero] using
      hasDerivAt_robertSargos_mixed_jet_q (i := 0) (j := 0) (k := 0)
        (by norm_num) hp hm
  have he := hasDerivAt_robertSargos_character hzero
  cases b <;> cases c
  · convert he using 1
    dsimp [robertSargosCharacterJet]
    ring
  · convert ((hd 0 1 (by norm_num)).const_mul t).mul he using 1
    dsimp [robertSargosCharacterJet,t]
    ring
  · convert ((hd 1 0 (by norm_num)).const_mul t).mul he using 1
    dsimp [robertSargosCharacterJet,t]
    ring
  · convert (((hd 1 1 (by norm_num)).const_mul t).add
      (((hd 1 0 (by norm_num)).const_mul (t^2)).mul (hd 0 1 (by norm_num)))).mul he using 1
    dsimp [robertSargosCharacterJet,t]
    ring

theorem hasDerivAt_robertSargos_character_jet_h
    {f : ℝ → ℝ} {m r q h n : ℝ} (c : Bool)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosCharacterJet f m r false false c q x n)
      (robertSargosCharacterJet f m r false true c q h n) h := by
  let t : ℂ := 2*Real.pi*Complex.I
  have hd (k : ℕ) (hk : k < 4) :
      HasDerivAt (fun x => (robertSargosMixedJet f m r 0 0 k q x n : ℂ))
        (robertSargosMixedJet f m r 0 1 k q h n : ℂ) h :=
    (hasDerivAt_robertSargos_mixed_jet_h (by simpa using hk) hp hm hrp hrm).ofReal_comp
  have hzero : HasDerivAt (fun x => robertSargosMixedRemainder f m r q x n)
      (robertSargosMixedJet f m r 0 1 0 q h n) h := by
    simpa only [robertSargos_mixed_jet_zero] using
      hasDerivAt_robertSargos_mixed_jet_h (i := 0) (j := 0) (k := 0)
        (by norm_num) hp hm hrp hrm
  have he := hasDerivAt_robertSargos_character hzero
  cases c
  · convert he using 1
    dsimp [robertSargosCharacterJet]
    ring
  · convert ((hd 1 (by norm_num)).const_mul t).mul he using 1
    dsimp [robertSargosCharacterJet,t]
    ring

theorem hasDerivAt_robertSargos_character_jet_n
    {f : ℝ → ℝ} {m r q h n : ℝ}
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosCharacterJet f m r false false false q h x)
      (robertSargosCharacterJet f m r false false true q h n) n := by
  have hzero : HasDerivAt (fun x => robertSargosMixedRemainder f m r q h x)
      (robertSargosMixedJet f m r 0 0 1 q h n) n := by
    simpa only [robertSargos_mixed_jet_zero] using
      hasDerivAt_robertSargos_mixed_jet_n (i := 0) (j := 0) (k := 0)
        (by norm_num) hp hm hrp hrm
  convert hasDerivAt_robertSargos_character hzero using 1
  dsimp [robertSargosCharacterJet]
  ring

private theorem norm_character_linear_le {t u : ℂ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (ht : ‖t‖ ≤ T) (hu : ‖u‖ ≤ K) :
    ‖t*u‖ ≤ (1+T*K)^3 := by
  rw [norm_mul]
  have hb := mul_le_mul ht hu (norm_nonneg _) hT
  have hp : 0 ≤ T*K := mul_nonneg hT hK
  nlinarith [sq_nonneg (T*K),pow_nonneg hp 3]

private theorem norm_character_quadratic_le {t u v w : ℂ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (ht : ‖t‖ ≤ T)
    (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) (hw : ‖w‖ ≤ K) :
    ‖t*u+t^2*v*w‖ ≤ (1+T*K)^3 := by
  have h1 : ‖t*u‖ ≤ T*K := by
    rw [norm_mul]
    exact mul_le_mul ht hu (norm_nonneg _) hT
  have h2 : ‖t^2*v*w‖ ≤ T^2*K^2 := by
    rw [norm_mul,norm_mul,norm_pow]
    have ht2 := pow_le_pow_left₀ (norm_nonneg t) ht 2
    calc
      _ ≤ T^2*K*K := mul_le_mul
        (mul_le_mul ht2 hv (norm_nonneg _) (sq_nonneg T)) hw
        (norm_nonneg _) (mul_nonneg (sq_nonneg T) hK)
      _ = _ := by ring
  have hsum := (norm_add_le (t*u) (t^2*v*w)).trans (add_le_add h1 h2)
  have hp : 0 ≤ T*K := mul_nonneg hT hK
  nlinarith [sq_nonneg (T*K),pow_nonneg hp 3]

private theorem norm_character_cubic_le {t a b c d e f g : ℂ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (ht : ‖t‖ ≤ T)
    (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (hc : ‖c‖ ≤ K)
    (hd : ‖d‖ ≤ K) (he : ‖e‖ ≤ K) (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K) :
    ‖t*a+t^2*(b*c+d*e+f*g)+t^3*g*e*c‖ ≤ (1+T*K)^3 := by
  have h1 : ‖t*a‖ ≤ T*K := by
    rw [norm_mul]
    exact mul_le_mul ht ha (norm_nonneg _) hT
  have hm (u v : ℂ) (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) : ‖u*v‖ ≤ K^2 := by
    rw [norm_mul]
    nlinarith [mul_le_mul hu hv (norm_nonneg _) hK]
  have h2 : ‖t^2*(b*c+d*e+f*g)‖ ≤ T^2*(3*K^2) := by
    rw [norm_mul,norm_pow]
    apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg t) ht 2) _ (norm_nonneg _) (sq_nonneg T)
    have hsum := norm_add_le (b*c+d*e) (f*g)
    have hsum' := norm_add_le (b*c) (d*e)
    linarith [hm b c hb hc,hm d e hd he,hm f g hf hg]
  have h3 : ‖t^3*g*e*c‖ ≤ T^3*K^3 := by
    simp only [norm_mul,norm_pow]
    have ht3 := pow_le_pow_left₀ (norm_nonneg t) ht 3
    calc
      _ ≤ T^3*K*K*K := mul_le_mul
        (mul_le_mul (mul_le_mul ht3 hg (norm_nonneg _) (pow_nonneg hT _))
          he (norm_nonneg _) (mul_nonneg (pow_nonneg hT _) hK))
        hc (norm_nonneg _) (mul_nonneg (mul_nonneg (pow_nonneg hT _) hK) hK)
      _ = _ := by ring
  have hsum := norm_add_le (t*a+t^2*(b*c+d*e+f*g)) (t^3*g*e*c)
  have hsum' := norm_add_le (t*a) (t^2*(b*c+d*e+f*g))
  have hp : 0 ≤ T*K := mul_nonneg hT hK
  nlinarith

theorem robertSargos_character_jet_bound
    (f : ℝ → ℝ) (m r q h n : ℝ) {Q K : ℝ}
    (hQ : 0 < Q) (hK : 0 ≤ K)
    (hJ : ∀ i ≤ 1, ∀ j ≤ 1, ∀ k ≤ 1,
      Q^(i+j+k)*|robertSargosMixedJet f m r i j k q h n| ≤ K)
    (a b c : Bool) :
    Q^(a.toNat+b.toNat+c.toNat)*
      ‖robertSargosCharacterJet f m r a b c q h n‖ ≤ (1+2*Real.pi*K)^3 := by
  let J := fun i j k => (robertSargosMixedJet f m r i j k q h n : ℂ)
  let U := fun i j k => (Q:ℂ)^(i+j+k)*J i j k
  let t : ℂ := 2*Real.pi*Complex.I
  let E := fordAdditiveCharacter (robertSargosMixedRemainder f m r q h n)
  have ht : ‖t‖ ≤ 2*Real.pi := by
    norm_num [t,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hE : ‖E‖ = 1 := sargos_character_norm _
  have hU (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
      ‖U i j k‖ ≤ K := by
    dsimp [U,J]
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le,
      Complex.norm_real,Real.norm_eq_abs]
    exact hJ i hi j hj k hk
  cases a <;> cases b <;> cases c
  · change 1*‖E‖ ≤ _
    rw [hE,mul_one]
    exact one_le_pow₀ (by nlinarith [Real.pi_pos] : 1 ≤ 1+2*Real.pi*K)
  · change Q^1*‖robertSargosCharacterJet f m r false false true q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^1*robertSargosCharacterJet f m r false false true q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 0 0 1)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 0 0 1‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_linear_le (by positivity) hK ht (hU 0 0 1 (by norm_num) (by norm_num) (by norm_num))
  · change Q^1*‖robertSargosCharacterJet f m r false true false q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^1*robertSargosCharacterJet f m r false true false q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 0 1 0)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 0 1 0‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_linear_le (by positivity) hK ht (hU 0 1 0 (by norm_num) (by norm_num) (by norm_num))
  · change Q^2*‖robertSargosCharacterJet f m r false true true q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^2*robertSargosCharacterJet f m r false true true q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 0 1 1+t^2*U 0 1 0*U 0 0 1)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 0 1 1+t^2*U 0 1 0*U 0 0 1‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_quadratic_le (by positivity) hK ht (hU 0 1 1 (by norm_num) (by norm_num) (by norm_num)) (hU 0 1 0 (by norm_num) (by norm_num) (by norm_num)) (hU 0 0 1 (by norm_num) (by norm_num) (by norm_num))
  · change Q^1*‖robertSargosCharacterJet f m r true false false q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^1*robertSargosCharacterJet f m r true false false q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 1 0 0)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 1 0 0‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_linear_le (by positivity) hK ht (hU 1 0 0 (by norm_num) (by norm_num) (by norm_num))
  · change Q^2*‖robertSargosCharacterJet f m r true false true q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^2*robertSargosCharacterJet f m r true false true q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 1 0 1+t^2*U 1 0 0*U 0 0 1)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 1 0 1+t^2*U 1 0 0*U 0 0 1‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_quadratic_le (by positivity) hK ht (hU 1 0 1 (by norm_num) (by norm_num) (by norm_num)) (hU 1 0 0 (by norm_num) (by norm_num) (by norm_num)) (hU 0 0 1 (by norm_num) (by norm_num) (by norm_num))
  · change Q^2*‖robertSargosCharacterJet f m r true true false q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^2*robertSargosCharacterJet f m r true true false q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 1 1 0+t^2*U 1 0 0*U 0 1 0)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 1 1 0+t^2*U 1 0 0*U 0 1 0‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_quadratic_le (by positivity) hK ht (hU 1 1 0 (by norm_num) (by norm_num) (by norm_num)) (hU 1 0 0 (by norm_num) (by norm_num) (by norm_num)) (hU 0 1 0 (by norm_num) (by norm_num) (by norm_num))
  · change Q^3*‖robertSargosCharacterJet f m r true true true q h n‖ ≤ _
    calc
      _ = ‖(Q:ℂ)^3*robertSargosCharacterJet f m r true true true q h n‖ := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ.le]
      _ = ‖(t*U 1 1 1+t^2*(U 1 1 0*U 0 0 1+U 1 0 1*U 0 1 0+U 0 1 1*U 1 0 0)+t^3*U 1 0 0*U 0 1 0*U 0 0 1)*E‖ := by
        congr 1
        dsimp [robertSargosCharacterJet,U,J,t,E]
        ring
      _ = ‖t*U 1 1 1+t^2*(U 1 1 0*U 0 0 1+U 1 0 1*U 0 1 0+U 0 1 1*U 1 0 0)+t^3*U 1 0 0*U 0 1 0*U 0 0 1‖ := by rw [norm_mul,hE,mul_one]
      _ ≤ _ := norm_character_cubic_le (by positivity) hK ht (hU 1 1 1 (by norm_num) (by norm_num) (by norm_num)) (hU 1 1 0 (by norm_num) (by norm_num) (by norm_num)) (hU 0 0 1 (by norm_num) (by norm_num) (by norm_num)) (hU 1 0 1 (by norm_num) (by norm_num) (by norm_num)) (hU 0 1 0 (by norm_num) (by norm_num) (by norm_num)) (hU 0 1 1 (by norm_num) (by norm_num) (by norm_num)) (hU 1 0 0 (by norm_num) (by norm_num) (by norm_num))

theorem robertSargos_physical_character_jet_bound
    (f : ℝ → ℝ) (M H : ℕ) (m : ℤ) {C lam r q h n : ℝ} (a b c : Bool)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hm : m ∈ robertSargosCommonMInterval M H
      ⌊lam^(-(3:ℝ)/13)⌋₊ ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hq : |q| ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hh : h ∈ Set.Icc (H:ℝ) (2*H)) (hhr : h+r ∈ Set.Icc (H:ℝ) (2*H))
    (hn : n ∈ Set.Icc 1 (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hf : ∀ x ∈ Set.Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Set.Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Set.Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)^(a.toNat+b.toNat+c.toNat)*
      ‖robertSargosCharacterJet f m r a b c q h n‖ ≤ (1+648*Real.pi*C)^3 := by
  have hQ : 0 < (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) :=
    zero_lt_one.trans_le (robertSargos_floor_fourth_scale hlam hsmall).1
  have hK : 0 ≤ 324*C := by have := zero_le_one.trans hC; positivity
  have hJ (i : ℕ) (hi : i ≤ 1) (j : ℕ) (hj : j ≤ 1) (k : ℕ) (hk : k ≤ 1) :
      (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)^(i+j+k)*
        |robertSargosMixedJet f m r i j k q h n| ≤ 324*C :=
    robertSargos_physical_mixed_jet_bound f M H m (by omega) hC hlam hsmall hH hm
      hq hh hhr hn hf hlo hhi
  have ht := robertSargos_character_jet_bound f m r q h n hQ hK hJ a b c
  simpa only [show 2*Real.pi*(324*C) = 648*Real.pi*C by ring] using ht

def robertSargosAmplitudeJet (f : ℝ → ℝ) (m r Q s : ℝ) (a b c : Bool)
    (q h n : ℝ) : ℂ :=
  ((1-s*q/Q : ℝ):ℂ)*robertSargosCharacterJet f m r a b c q h n+
    if a then ((-s/Q : ℝ):ℂ)*robertSargosCharacterJet f m r false b c q h n else 0

theorem hasDerivAt_robertSargos_amplitude_jet_q
    {f : ℝ → ℝ} {m r Q s q h n : ℝ} (b c : Bool)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h))) :
    HasDerivAt (fun x => robertSargosAmplitudeJet f m r Q s false b c x h n)
      (robertSargosAmplitudeJet f m r Q s true b c q h n) q := by
  have hw : HasDerivAt (fun x : ℝ => ((1-s*x/Q : ℝ):ℂ)) ((-s/Q : ℝ):ℂ) q := by
    convert ((((hasDerivAt_id q).const_mul s).div_const Q).const_sub 1).ofReal_comp using 1
    push_cast
    ring
  have he := hasDerivAt_robertSargos_character_jet_q (r := r) b c hp hm
  convert hw.mul he using 1
  · funext x
    simp [robertSargosAmplitudeJet]
  · dsimp only [robertSargosAmplitudeJet]
    simp only [ite_true]
    ring

theorem hasDerivAt_robertSargos_amplitude_jet_h
    {f : ℝ → ℝ} {m r Q s q h n : ℝ} (c : Bool)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosAmplitudeJet f m r Q s false false c q x n)
      (robertSargosAmplitudeJet f m r Q s false true c q h n) h := by
  simpa [robertSargosAmplitudeJet] using
    (hasDerivAt_robertSargos_character_jet_h c hp hm hrp hrm).const_mul
      ((1-s*q/Q : ℝ):ℂ)

theorem hasDerivAt_robertSargos_amplitude_jet_n
    {f : ℝ → ℝ} {m r Q s q h n : ℝ}
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosAmplitudeJet f m r Q s false false false q h x)
      (robertSargosAmplitudeJet f m r Q s false false true q h n) n := by
  simpa [robertSargosAmplitudeJet] using
    (hasDerivAt_robertSargos_character_jet_n hp hm hrp hrm).const_mul
      ((1-s*q/Q : ℝ):ℂ)

theorem robertSargos_amplitude_jet_zero (f : ℝ → ℝ) (m r Q s q h n : ℝ)
    (hq : |q| = s*q) :
    robertSargosAmplitudeJet f m r Q s false false false q h n =
      robertSargosMixedAmplitude f m r Q q h n := by
  simp [robertSargosAmplitudeJet,robertSargosCharacterJet,robertSargosMixedAmplitude,hq]

theorem robertSargos_amplitude_jet_bound (f : ℝ → ℝ) (m r s q h n : ℝ)
    {Q D : ℝ} (hQ : 0 < Q) (hD : 0 ≤ D) (hs : |s| = 1)
    (hq : s*q ∈ Set.Icc 0 Q)
    (hb : ∀ a b c : Bool, Q^(a.toNat+b.toNat+c.toNat)*
      ‖robertSargosCharacterJet f m r a b c q h n‖ ≤ D)
    (a b c : Bool) :
    Q^(a.toNat+b.toNat+c.toNat)*
      ‖robertSargosAmplitudeJet f m r Q s a b c q h n‖ ≤ 2*D := by
  have hfrac : 0 ≤ s*q/Q ∧ s*q/Q ≤ 1 :=
    ⟨div_nonneg hq.1 hQ.le,(div_le_one hQ).mpr hq.2⟩
  have hw : ‖((1-s*q/Q : ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1-s*q/Q)]
    linarith
  have hd : ‖((-s/Q : ℝ):ℂ)‖ = Q⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_neg,hs,abs_of_pos hQ,one_div]
  have hmain (a b c : Bool) :
      Q^(a.toNat+b.toNat+c.toNat)*
        ‖((1-s*q/Q : ℝ):ℂ)*robertSargosCharacterJet f m r a b c q h n‖ ≤ D := by
    rw [norm_mul]
    calc
      _ = ‖((1-s*q/Q : ℝ):ℂ)‖*
          (Q^(a.toNat+b.toNat+c.toNat)*‖robertSargosCharacterJet f m r a b c q h n‖) := by ring
      _ ≤ 1*D := mul_le_mul hw (hb a b c) (by positivity) (by norm_num)
      _ = _ := one_mul D
  cases a
  · have ht := hmain false b c
    simpa [robertSargosAmplitudeJet] using ht.trans (show D ≤ 2*D by linarith)
  · have he (e : ℕ) : Q^(1+e)*Q⁻¹ = Q^e := by
      rw [pow_add,pow_one]
      calc
        _ = Q*Q⁻¹*Q^e := by ring
        _ = _ := by rw [mul_inv_cancel₀ hQ.ne',one_mul]
    have hrem :
        Q^(1+b.toNat+c.toNat)*
          ‖((-s/Q : ℝ):ℂ)*robertSargosCharacterJet f m r false b c q h n‖ ≤ D := by
      rw [norm_mul,hd,← mul_assoc,Nat.add_assoc,he]
      simpa only [Bool.toNat_false,Nat.zero_add] using hb false b c
    have hnorm := norm_add_le
      (((1-s*q/Q : ℝ):ℂ)*robertSargosCharacterJet f m r true b c q h n)
      (((-s/Q : ℝ):ℂ)*robertSargosCharacterJet f m r false b c q h n)
    have hmul := mul_le_mul_of_nonneg_left hnorm
      (pow_nonneg hQ.le (1+b.toNat+c.toNat))
    change Q^(1+b.toNat+c.toNat)*
      ‖((1-s*q/Q : ℝ):ℂ)*robertSargosCharacterJet f m r true b c q h n+
        ((-s/Q : ℝ):ℂ)*robertSargosCharacterJet f m r false b c q h n‖ ≤ 2*D
    have hmain' := hmain true b c
    simp only [Bool.toNat_true] at hmain'
    nlinarith


def robertSargosAbelFactor (Q : ℝ) (N i : ℕ) : ℝ :=
  if i+1 < N then Q⁻¹ else 1

private theorem abel_point_mem {N i : ℕ} (hi : i < N) (A : ℝ) :
    A+i ∈ Icc A (A+N-1) := by
  have hi' : (i:ℝ)+1 ≤ N := by exact_mod_cast (show i+1 ≤ N by omega)
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]

private theorem norm_abel_difference_le
    (F G : ℝ → ℂ) {N i : ℕ} (hi : i < N) {A Q D : ℝ}
    (hd : ∀ x ∈ Icc A (A+N-1), HasDerivAt F (G x) x)
    (hb : ∀ x ∈ Icc A (A+N-1), ‖F x‖ ≤ D)
    (hg : ∀ x ∈ Icc A (A+N-1), ‖G x‖ ≤ D/Q) :
    ‖robertSargosAbelDifference N (fun j => F (A+j)) i‖ ≤
      D*robertSargosAbelFactor Q N i := by
  have hx := abel_point_mem hi A
  by_cases hlast : i+1 < N
  · have hy := abel_point_mem hlast A
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hd x hx).hasDerivWithinAt) hg (convex_Icc A (A+N-1)) hx hy
    simp only [Nat.cast_add,Nat.cast_one,
      show A+((i:ℝ)+1)-(A+i) = 1 by ring,norm_one,mul_one] at hmv
    simpa only [robertSargosAbelDifference,robertSargosAbelFactor,if_pos hlast,
      norm_sub_rev,Nat.cast_add,Nat.cast_one,div_eq_mul_inv] using hmv
  · simpa only [robertSargosAbelDifference,robertSargosAbelFactor,if_neg hlast,mul_one]
      using hb (A+i) hx

private theorem hasDerivAt_abel_difference
    (F G : ℕ → ℝ → ℂ) {N i : ℕ} (hi : i < N) {x : ℝ}
    (hd : ∀ j < N, HasDerivAt (F j) (G j x) x) :
    HasDerivAt (fun y => robertSargosAbelDifference N (fun j => F j y) i)
      (robertSargosAbelDifference N (fun j => G j x) i) x := by
  by_cases hlast : i+1 < N
  · simpa only [robertSargosAbelDifference,if_pos hlast] using
      (hd i hi).sub (hd (i+1) hlast)
  · simpa only [robertSargosAbelDifference,if_neg hlast] using hd i hi

theorem robertSargos_abel_coefficient_reverse (w : ℕ → ℕ → ℕ → ℂ)
    (X Y Z i j k : ℕ) :
    robertSargosAbelCoefficient X Y Z w i j k =
      robertSargosAbelDifference Z
        (fun z => robertSargosAbelDifference Y
          (fun y => robertSargosAbelDifference X (fun x => w x y z) i) j) k := by
  unfold robertSargosAbelCoefficient robertSargosAbelDifference
  split_ifs <;> ring

theorem robertSargos_abel_coefficient_bound
    (F : Bool → Bool → Bool → ℝ → ℝ → ℝ → ℂ)
    {X Y Z i j k : ℕ} (hi : i < X) (hj : j < Y) (hk : k < Z)
    {A B C Q D : ℝ}
    (hfx : ∀ b c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F false b c u y z) (F true b c x y z) x)
    (hfy : ∀ c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F false false c x u z) (F false true c x y z) y)
    (hfz : ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F false false false x y u) (F false false true x y z) z)
    (hb : ∀ a b c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      ‖F a b c x y z‖ ≤ D/Q^(a.toNat+b.toNat+c.toNat)) :
    ‖robertSargosAbelCoefficient X Y Z
      (fun x y z => F false false false (A+x) (B+y) (C+z)) i j k‖ ≤
      D*robertSargosAbelFactor Q X i*robertSargosAbelFactor Q Y j*
        robertSargosAbelFactor Q Z k := by
  let cx := robertSargosAbelFactor Q X i
  let cy := robertSargosAbelFactor Q Y j
  let W := fun b c y z =>
    robertSargosAbelDifference X (fun x => F false b c (A+x) y z) i
  have hW (b c : Bool) (y : ℝ) (hy : y ∈ Icc B (B+Y-1))
      (z : ℝ) (hz : z ∈ Icc C (C+Z-1)) :
      ‖W b c y z‖ ≤ D*cx/Q^(b.toNat+c.toNat) := by
    calc
      _ ≤ (D/Q^(b.toNat+c.toNat))*cx := by
        apply norm_abel_difference_le (F false b c · y z) (F true b c · y z) hi
        · intro x hx
          exact hfx b c x hx y hy z hz
        · intro x hx
          simpa only [Bool.toNat_false,Nat.zero_add] using hb false b c x hx y hy z hz
        · intro x hx
          simpa only [Bool.toNat_true,Nat.add_assoc,pow_add,pow_one,div_div,mul_comm]
            using hb true b c x hx y hy z hz
      _ = _ := by ring
  have hWy (c : Bool) (y : ℝ) (hy : y ∈ Icc B (B+Y-1))
      (z : ℝ) (hz : z ∈ Icc C (C+Z-1)) :
      HasDerivAt (fun u => W false c u z) (W true c y z) y := by
    apply hasDerivAt_abel_difference
      (fun x u => F false false c (A+x) u z)
      (fun x u => F false true c (A+x) u z) hi
    intro x hx
    exact hfy c (A+x) (abel_point_mem hx A) y hy z hz
  have hWz (y : ℝ) (hy : y ∈ Icc B (B+Y-1))
      (z : ℝ) (hz : z ∈ Icc C (C+Z-1)) :
      HasDerivAt (fun u => W false false y u) (W false true y z) z := by
    apply hasDerivAt_abel_difference
      (fun x u => F false false false (A+x) y u)
      (fun x u => F false false true (A+x) y u) hi
    intro x hx
    exact hfz (A+x) (abel_point_mem hx A) y hy z hz
  let V := fun c z => robertSargosAbelDifference Y (fun y => W false c (B+y) z) j
  have hV (c : Bool) (z : ℝ) (hz : z ∈ Icc C (C+Z-1)) :
      ‖V c z‖ ≤ D*cx*cy/Q^c.toNat := by
    calc
      _ ≤ (D*cx/Q^c.toNat)*cy := by
        apply norm_abel_difference_le (W false c · z) (W true c · z) hj
        · intro y hy
          exact hWy c y hy z hz
        · intro y hy
          simpa only [Bool.toNat_false,Nat.zero_add] using hW false c y hy z hz
        · intro y hy
          simpa only [Bool.toNat_true,pow_add,pow_one,div_div,mul_comm]
            using hW true c y hy z hz
      _ = _ := by ring
  have hVz (z : ℝ) (hz : z ∈ Icc C (C+Z-1)) :
      HasDerivAt (V false) (V true z) z := by
    apply hasDerivAt_abel_difference
      (fun y u => W false false (B+y) u)
      (fun y u => W false true (B+y) u) hj
    intro y hy
    exact hWz (B+y) (abel_point_mem hy B) z hz
  rw [robertSargos_abel_coefficient_reverse]
  exact norm_abel_difference_le (V false) (V true) hk hVz
    (fun z hz => by simpa only [Bool.toNat_false,pow_zero,div_one] using hV false z hz)
    (fun z hz => by simpa only [Bool.toNat_true,pow_one] using hV true z hz)

theorem sum_robertSargosAbelFactor_le {Q : ℝ} (hQ : 0 < Q) {N : ℕ}
    (hN : (N:ℝ) ≤ Q) :
    (∑ i ∈ Finset.range N, robertSargosAbelFactor Q N i) ≤ 2 := by
  cases N with
  | zero => simp
  | succ N =>
    have hs : (∑ i ∈ Finset.range N, robertSargosAbelFactor Q (N+1) i) =
        (N:ℝ)/Q := by
      calc
        _ = ∑ _i ∈ Finset.range N, Q⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [robertSargosAbelFactor,if_pos (show i+1 < N+1 by
            have := Finset.mem_range.mp hi
            omega)]
        _ = _ := by simp [div_eq_mul_inv]
    rw [Finset.sum_range_succ,hs]
    simp only [robertSargosAbelFactor,lt_self_iff_false,if_false]
    have hN' : (N:ℝ) ≤ Q := by
      simp only [Nat.cast_succ] at hN
      linarith
    have hdiv := (div_le_one hQ).mpr hN'
    linarith

theorem robertSargos_abel_variation_of_mixed_derivatives {ι : Type*}
    (S : Finset ι) (F : ι → Bool → Bool → Bool → ℝ → ℝ → ℝ → ℂ)
    {X Y Z : ℕ} {A B C Q D : ℝ}
    (hQ : 0 < Q) (hD : 0 ≤ D) (hX : (X:ℝ) ≤ Q)
    (hY : (Y:ℝ) ≤ Q) (hZ : (Z:ℝ) ≤ Q)
    (hfx : ∀ m ∈ S, ∀ b c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F m false b c u y z) (F m true b c x y z) x)
    (hfy : ∀ m ∈ S, ∀ c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F m false false c x u z) (F m false true c x y z) y)
    (hfz : ∀ m ∈ S, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      HasDerivAt (fun u => F m false false false x y u) (F m false false true x y z) z)
    (hb : ∀ m ∈ S, ∀ a b c, ∀ x ∈ Icc A (A+X-1), ∀ y ∈ Icc B (B+Y-1),
      ∀ z ∈ Icc C (C+Z-1),
      ‖F m a b c x y z‖ ≤ D/Q^(a.toNat+b.toNat+c.toNat)) :
    robertSargosAbelVariation S X Y Z
      (fun m x y z => F m false false false (A+x) (B+y) (C+z)) ≤ 8*D := by
  classical
  have hfnonneg (N i : ℕ) : 0 ≤ robertSargosAbelFactor Q N i := by
    unfold robertSargosAbelFactor
    split <;> positivity
  have hp (i : ℕ) (hi : i ∈ Finset.range X) (j : ℕ) (hj : j ∈ Finset.range Y)
      (k : ℕ) (hk : k ∈ Finset.range Z) :
      ((S.sup (fun m => ‖robertSargosAbelCoefficient X Y Z
        (fun x y z => F m false false false (A+x) (B+y) (C+z)) i j k‖₊) : NNReal) : ℝ) ≤
      D*robertSargosAbelFactor Q X i*robertSargosAbelFactor Q Y j*
        robertSargosAbelFactor Q Z k := by
    let V := D*robertSargosAbelFactor Q X i*robertSargosAbelFactor Q Y j*
      robertSargosAbelFactor Q Z k
    have hV : 0 ≤ V := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hD (hfnonneg X i)) (hfnonneg Y j)) (hfnonneg Z k)
    have hs : S.sup (fun m => ‖robertSargosAbelCoefficient X Y Z
        (fun x y z => F m false false false (A+x) (B+y) (C+z)) i j k‖₊) ≤
        (⟨V,hV⟩ : NNReal) := by
      apply Finset.sup_le
      intro m hm
      have h := robertSargos_abel_coefficient_bound (F m)
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
        (hfx m hm) (hfy m hm) (hfz m hm) (hb m hm)
      exact_mod_cast h
    exact_mod_cast hs
  have hx0 : 0 ≤ ∑ i ∈ Finset.range X, robertSargosAbelFactor Q X i :=
    Finset.sum_nonneg (fun i _ => hfnonneg X i)
  have hy0 : 0 ≤ ∑ j ∈ Finset.range Y, robertSargosAbelFactor Q Y j :=
    Finset.sum_nonneg (fun j _ => hfnonneg Y j)
  have hz0 : 0 ≤ ∑ k ∈ Finset.range Z, robertSargosAbelFactor Q Z k :=
    Finset.sum_nonneg (fun k _ => hfnonneg Z k)
  unfold robertSargosAbelVariation
  calc
    _ ≤ ∑ k ∈ Finset.range Z, ∑ j ∈ Finset.range Y, ∑ i ∈ Finset.range X,
        D*robertSargosAbelFactor Q X i*robertSargosAbelFactor Q Y j*
          robertSargosAbelFactor Q Z k := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact hp i hi j hj k hk
    _ = D*(∑ i ∈ Finset.range X, robertSargosAbelFactor Q X i)*
        (∑ j ∈ Finset.range Y, robertSargosAbelFactor Q Y j)*
        (∑ k ∈ Finset.range Z, robertSargosAbelFactor Q Z k) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ D*2*2*2 := by
      apply mul_le_mul (mul_le_mul
        (mul_le_mul_of_nonneg_left (sum_robertSargosAbelFactor_le hQ hX) hD)
        (sum_robertSargosAbelFactor_le hQ hY) hy0 (by positivity))
        (sum_robertSargosAbelFactor_le hQ hZ) hz0 (by positivity)
    _ = _ := by ring


open Set

private theorem robertSargos_physical_mixed_points
    (f : ℝ → ℝ) (M H : ℕ) (m : ℤ) {lam r q h n : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hm : m ∈ robertSargosCommonMInterval M H
      ⌊lam^(-(3:ℝ)/13)⌋₊ ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hq : |q| ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hh : h ∈ Icc (H:ℝ) (2*H)) (hhr : h+r ∈ Icc (H:ℝ) (2*H))
    (hn : n ∈ Icc 1 (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x) :
    ∀ u ∈ ({n+q+h,n+q-h,n+h+r,n-h-r} : Finset ℝ),
      ContDiffAt ℝ 4 f ((m:ℝ)+u) := by
  have hQ := (robertSargos_floor_fourth_scale hlam hsmall).1
  have hHQ := robertSargos_floor_half_height hlam hsmall hH
  simp only [robertSargosCommonMInterval,Finset.mem_Icc] at hm
  have hml : 2*(H:ℝ)+(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
  have hmu : (m:ℝ) ≤ (M:ℝ)-2*H-(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)-
      (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by exact_mod_cast hm.2
  have hg := robertSargos_mixed_shift_geometry (M := (M:ℝ)) hQ (Nat.cast_nonneg H) hHQ
    ⟨hml,by linarith⟩ hq hh hhr hn
  intro u hu
  exact hf _ (hg.2 u hu).1

theorem robertSargos_physical_rectangle_variation
    (f : ℝ → ℝ) (M H Q X Y N : ℕ) (r A B s : ℝ) {C lam : ℝ}
    (hQeq : Q = ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hX : X ≤ Q) (hY : Y ≤ Q) (hN : N ≤ Q) (hs : |s| = 1)
    (hq : ∀ x ∈ Icc A (A+X-1), s*x ∈ Icc 0 (Q:ℝ))
    (hBlo : (H:ℝ) ≤ B) (hBhi : B+Y-1 ≤ 2*H)
    (hBrlo : (H:ℝ) ≤ B+r) (hBrhi : B+Y-1+r ≤ 2*H)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    robertSargosAbelVariation (robertSargosCommonMInterval M H Q Q) X Y N
      (fun m x y z => robertSargosAmplitudeJet f m r Q s false false false
        (A+x) (B+y) (1+z)) ≤ 16*(1+648*Real.pi*C)^3 := by
  subst Q
  let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
  let D := (1+648*Real.pi*C)^3
  have hCp : 0 ≤ C := zero_le_one.trans hC
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 < (Q:ℝ) :=
    zero_lt_one.trans_le (robertSargos_floor_fourth_scale hlam hsmall).1
  have hgeometry (x : ℝ) (hx : x ∈ Icc A (A+X-1))
      (y : ℝ) (hy : y ∈ Icc B (B+Y-1))
      (z : ℝ) (hz : z ∈ Icc (1:ℝ) (1+(N:ℝ)-1)) :
      |x| ≤ (Q:ℝ) ∧ y ∈ Icc (H:ℝ) (2*H) ∧
        y+r ∈ Icc (H:ℝ) (2*H) ∧ z ∈ Icc 1 (Q:ℝ) := by
    have hqx := hq x hx
    have habs : |x| = s*x := by
      calc
        _ = |s*x| := by rw [abs_mul,hs,one_mul]
        _ = _ := abs_of_nonneg hqx.1
    refine ⟨by rw [habs]; exact hqx.2,⟨hBlo.trans hy.1,hy.2.trans hBhi⟩,
      ⟨by linarith [hy.1],by linarith [hy.2]⟩,hz.1,?_⟩
    have hN' : (N:ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast hN
    linarith [hz.2]
  have hpoints (m : ℤ) (hm : m ∈ robertSargosCommonMInterval M H Q Q)
      (x : ℝ) (hx : x ∈ Icc A (A+X-1))
      (y : ℝ) (hy : y ∈ Icc B (B+Y-1))
      (z : ℝ) (hz : z ∈ Icc (1:ℝ) (1+(N:ℝ)-1)) :
      ∀ u ∈ ({z+x+y,z+x-y,z+y+r,z-y-r} : Finset ℝ),
        ContDiffAt ℝ 4 f ((m:ℝ)+u) := by
    obtain ⟨hx',hy',hyr',hz'⟩ := hgeometry x hx y hy z hz
    exact robertSargos_physical_mixed_points f M H m hlam hsmall hH hm
      hx' hy' hyr' hz' hf
  have hvar := robertSargos_abel_variation_of_mixed_derivatives
    (robertSargosCommonMInterval M H Q Q)
    (fun m a b c x y z => robertSargosAmplitudeJet f m r Q s a b c x y z)
    (A := A) (B := B) (C := 1) (X := X) (Y := Y) (Z := N)
    hQ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hD)
    (by dsimp [Q]; exact_mod_cast hX)
    (by dsimp [Q]; exact_mod_cast hY)
    (by dsimp [Q]; exact_mod_cast hN) ?_ ?_ ?_ ?_
  · dsimp only [Q,D] at hvar
    nlinarith
  · intro m hm b c x hx y hy z hz
    have hp := hpoints m hm x hx y hy z hz
    exact hasDerivAt_robertSargos_amplitude_jet_q b c
      (hp _ (by simp)) (hp _ (by simp))
  · intro m hm c x hx y hy z hz
    have hp := hpoints m hm x hx y hy z hz
    exact hasDerivAt_robertSargos_amplitude_jet_h c
      (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp))
  · intro m hm x hx y hy z hz
    have hp := hpoints m hm x hx y hy z hz
    exact hasDerivAt_robertSargos_amplitude_jet_n
      (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp))
  · intro m hm a b c x hx y hy z hz
    obtain ⟨hx',hy',hyr',hz'⟩ := hgeometry x hx y hy z hz
    have hchar (a b c : Bool) :
        (Q:ℝ)^(a.toNat+b.toNat+c.toNat)*
          ‖robertSargosCharacterJet f m r a b c x y z‖ ≤ D :=
      robertSargos_physical_character_jet_bound f M H m a b c hC hlam hsmall hH hm
        hx' hy' hyr' hz' hf hlo hhi
    have hamp := robertSargos_amplitude_jet_bound f m r s x y z hQ hD hs
      (hq x hx) hchar a b c
    apply (le_div_iff₀ (pow_pos hQ _)).mpr
    simpa only [mul_comm] using hamp


theorem robertSargos_physical_rectangle_common_prefix
    (f : ℝ → ℝ) (M H Q X Y N : ℕ) (r A B s : ℝ) {C lam : ℝ}
    (hQeq : Q = ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hXp : 0 < X) (hYp : 0 < Y) (hNp : 0 < N)
    (hX : X ≤ Q) (hY : Y ≤ Q) (hN : N ≤ Q) (hs : |s| = 1)
    (hq : ∀ x ∈ Icc A (A+X-1), s*x ∈ Icc 0 (Q:ℝ))
    (hBlo : (H:ℝ) ≤ B) (hBhi : B+Y-1 ≤ 2*H)
    (hBrlo : (H:ℝ) ≤ B+r) (hBrhi : B+Y-1+r ≤ 2*H)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ∃ i < X, ∃ j < Y, ∃ k < N,
      (∑ m ∈ robertSargosCommonMInterval M H Q Q,
        ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range N,
          ((1-|A+x|/Q : ℝ):ℂ)*fordAdditiveCharacter
            (robertSargosSymmetricDifference f ((m:ℝ)+(1+z)+(A+x)) (B+y)-
              robertSargosSymmetricDifference f ((m:ℝ)+(1+z)) (B+y+r))‖) ≤
      16*(1+648*Real.pi*C)^3*
        ∑ m ∈ robertSargosCommonMInterval M H Q Q,
          ‖∑ x ∈ Finset.range (i+1), ∑ y ∈ Finset.range (j+1),
            ∑ z ∈ Finset.range (k+1),
              robertSargosPolynomialCharacter f m r (A+x) (B+y) (1+z)‖ := by
  let S := robertSargosCommonMInterval M H Q Q
  let w := fun (m : ℤ) (x y z : ℕ) => robertSargosAmplitudeJet f m r Q s false false false
    (A+x) (B+y) (1+z)
  let a := fun (m : ℤ) (x y z : ℕ) => robertSargosPolynomialCharacter f m r (A+x) (B+y) (1+z)
  obtain ⟨i,hi,j,hj,k,hk,hbound⟩ :=
    robertSargos_rectangular_common_prefix S w a hXp hYp hNp
  refine ⟨i,hi,j,hj,k,hk,?_⟩
  have hvar := robertSargos_physical_rectangle_variation f M H Q X Y N r A B s
    hQeq hC hlam hsmall hH hX hY hN hs hq hBlo hBhi hBrlo hBrhi hf hlo hhi
  have he (m : ℤ) :
      ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range N,
        ((1-|A+x|/Q : ℝ):ℂ)*fordAdditiveCharacter
          (robertSargosSymmetricDifference f ((m:ℝ)+(1+z)+(A+x)) (B+y)-
            robertSargosSymmetricDifference f ((m:ℝ)+(1+z)) (B+y+r))‖ =
      ‖∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.range N,
        w m x y z*a m x y z‖ := by
    rw [robertSargos_mixed_rectangular_norm f m r Q
      (fun x => A+x) (fun y => B+y) (fun z => 1+z) X Y N]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := hq (A+x) (abel_point_mem (Finset.mem_range.mp hx) A)
    have habs : |A+x| = s*(A+x) := by
      calc
        _ = |s*(A+x)| := by rw [abs_mul,hs,one_mul]
        _ = _ := abs_of_nonneg hx'.1
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    dsimp [w,a]
    rw [robertSargos_amplitude_jet_zero f m r Q s (A+x) (B+y) (1+z) habs]
  simp only [he]
  exact hbound.trans (mul_le_mul_of_nonneg_right hvar (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))


end TaoTrudgianYang2025
