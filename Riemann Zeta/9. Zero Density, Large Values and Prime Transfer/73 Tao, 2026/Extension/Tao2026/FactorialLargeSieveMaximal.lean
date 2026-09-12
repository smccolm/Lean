import Tao2026.FactorialLargeSieveCor29
import Tao2026.FactorialAsymptotics

open Filter Asymptotics

namespace Tao2026

noncomputable section

def factorialSieveDegree (x a : ℕ) : ℕ :=
  ⌊Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a)⌋₊

theorem factorialSieveDegree_cast_le
    {x a : ℕ} (ha : 2 ≤ a) :
    (factorialSieveDegree x a : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a) := by
  apply Nat.floor_le
  exact div_nonneg (Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ x + 1 by omega))) (by
    have : 0 < Real.log (a : ℝ) :=
      Real.log_pos (by exact_mod_cast ha)
    positivity)

theorem factorialSieveDegree_product_le
    {x a : ℕ} (ha : 2 ≤ a) :
    (a ^ factorialSieveDegree x a) *
        (a ^ factorialSieveDegree x a) ≤ x + 1 := by
  let k := factorialSieveDegree x a
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hxpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hk := factorialSieveDegree_cast_le (x := x) ha
  have hlog : (2 * (k : ℝ)) * Real.log a ≤
      Real.log ((x + 1 : ℕ) : ℝ) := by
    calc
      (2 * (k : ℝ)) * Real.log a ≤
          (2 * (Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a))) *
            Real.log a := by gcongr
      _ = Real.log ((x + 1 : ℕ) : ℝ) := by field_simp
  have hpowReal : ((a ^ (2 * k) : ℕ) : ℝ) ≤ (x + 1 : ℕ) := by
    calc
      ((a ^ (2 * k) : ℕ) : ℝ) =
          Real.exp (Real.log (((a ^ (2 * k) : ℕ) : ℝ))) := by
        rw [Real.exp_log]
        positivity
      _ = Real.exp ((2 * (k : ℝ)) * Real.log a) := by
        congr 1
        rw [Nat.cast_pow, Real.log_pow]
        norm_num [Nat.cast_mul]
      _ ≤ Real.exp (Real.log ((x + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr hlog
      _ = (x + 1 : ℕ) := Real.exp_log hxpos
  have hpowNat : a ^ (2 * k) ≤ x + 1 := by exact_mod_cast hpowReal
  calc
    a ^ k * a ^ k = a ^ (2 * k) := by rw [← pow_add]; congr 1; omega
    _ ≤ x + 1 := hpowNat

/-- Maximality of the floor-defined degree: the next squared power is
strictly larger than the ambient interval length. -/
theorem factorialSieveDegree_next_power_gt
    {x a : ℕ} (ha : 2 ≤ a) :
    x + 1 < a ^ (2 * (factorialSieveDegree x a + 1)) := by
  let k := factorialSieveDegree x a
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hxpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hfloor :
      Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a) < (k : ℝ) + 1 := by
    simpa only [k, factorialSieveDegree] using
      (Nat.lt_floor_add_one
        (Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a)))
  have hlog : Real.log ((x + 1 : ℕ) : ℝ) <
      (2 * ((k : ℝ) + 1)) * Real.log a := by
    have h :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log a)).mp hfloor
    nlinarith
  have hpowReal : ((x + 1 : ℕ) : ℝ) <
      ((a ^ (2 * (k + 1)) : ℕ) : ℝ) := by
    calc
      ((x + 1 : ℕ) : ℝ) = Real.exp (Real.log ((x + 1 : ℕ) : ℝ)) := by
        rw [Real.exp_log hxpos]
      _ < Real.exp ((2 * ((k : ℝ) + 1)) * Real.log a) :=
        Real.exp_lt_exp.mpr hlog
      _ = Real.exp (Real.log (((a ^ (2 * (k + 1)) : ℕ) : ℝ))) := by
        congr 1
        rw [Nat.cast_pow, Real.log_pow]
        norm_num [Nat.cast_mul, Nat.cast_add]
      _ = ((a ^ (2 * (k + 1)) : ℕ) : ℝ) := by
        rw [Real.exp_log]
        positivity
  exact_mod_cast hpowReal

/-- Any squared power already fitting in the ambient interval gives a lower
bound on the floor-defined sieve degree. -/
theorem le_factorialSieveDegree_of_power_le
    {x a n : ℕ} (ha : 2 ≤ a) (hpow : a ^ (2 * n) ≤ x + 1) :
    n ≤ factorialSieveDegree x a := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hpowPos : (0 : ℝ) < (a : ℝ) ^ (2 * n) := by positivity
  have hxpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hpowReal : (a : ℝ) ^ (2 * n) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog : (2 * (n : ℝ)) * Real.log (a : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) := by
    calc
      (2 * (n : ℝ)) * Real.log (a : ℝ) =
          Real.log ((a : ℝ) ^ (2 * n)) := by
        rw [Real.log_pow]
        norm_num [Nat.cast_mul]
      _ ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hpowPos hxpos hpowReal
  have hratio : (n : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log (a : ℝ)) := by
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log a)).2 (by
      convert hlog using 1
      ring)
  rw [factorialSieveDegree]
  exact Nat.le_floor hratio

theorem factorialSieveDegree_pos
    {x a : ℕ} (ha : 2 ≤ a) (hsq : a ^ 2 ≤ x + 1) :
    1 ≤ factorialSieveDegree x a := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hsqReal : ((a : ℝ) ^ 2) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsq
  have hlog : 2 * Real.log (a : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) := by
    calc
      2 * Real.log (a : ℝ) = Real.log ((a : ℝ) ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (show 0 < (a : ℝ) ^ 2 by positivity)
          (show 0 < ((x + 1 : ℕ) : ℝ) by positivity) hsqReal
  apply (Nat.floor_pos).2
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log a)).2 (by
    simpa only [one_mul] using hlog)

theorem two_mul_factorialSieveDegree_le_card
    {x a : ℕ} (ha : 2 ≤ a)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hlarge : 4 * Real.log ((x + 1 : ℕ) : ℝ) ≤ a) :
    2 * factorialSieveDegree x a ≤
      (factorialUpperHalfPrimes a).card := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hk := factorialSieveDegree_cast_le (x := x) ha
  have hfirst : ((2 * factorialSieveDegree x a : ℕ) : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) / Real.log a := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (factorialSieveDegree x a : ℝ) ≤
          2 * (Real.log ((x + 1 : ℕ) : ℝ) /
            (2 * Real.log a)) := by gcongr
      _ = Real.log ((x + 1 : ℕ) : ℝ) / Real.log a := by
        field_simp
  have hsecond : Real.log ((x + 1 : ℕ) : ℝ) / Real.log a ≤
      (a : ℝ) / (4 * Real.log a) := by
    exact (div_le_div_iff₀ hloga (by positivity : (0 : ℝ) < 4 * Real.log a)).2
      (by nlinarith)
  have hreal : ((2 * factorialSieveDegree x a : ℕ) : ℝ) ≤
      ((factorialUpperHalfPrimes a).card : ℝ) :=
    hfirst.trans (hsecond.trans hcard)
  exact_mod_cast hreal

theorem factorial_source_scale_base_ge
    {x a : ℕ} (ha : 2 ≤ a)
    (hk : 1 ≤ factorialSieveDegree x a) :
    (a : ℝ) / 1600 ≤
      ((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) /
        factorialSieveDegree x a := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hkpos : (0 : ℝ) < factorialSieveDegree x a := by exact_mod_cast hk
  have hdegree := factorialSieveDegree_cast_le (x := x) ha
  have hlogmono : Real.log ((x + 1 : ℕ) : ℝ) ≤
      Real.log ((x + 2 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show 0 < ((x + 1 : ℕ) : ℝ) by positivity)
      (show 0 < ((x + 2 : ℕ) : ℝ) by positivity)
      (by exact_mod_cast (show x + 1 ≤ x + 2 by omega))
  have hstep : 2 * (factorialSieveDegree x a : ℝ) * Real.log a ≤
      Real.log ((x + 2 : ℕ) : ℝ) := by
    calc
      2 * (factorialSieveDegree x a : ℝ) * Real.log a ≤
          2 * (Real.log ((x + 1 : ℕ) : ℝ) / (2 * Real.log a)) *
            Real.log a := by gcongr
      _ = Real.log ((x + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ _ := hlogmono
  have hratio : 1 ≤ Real.log ((x + 2 : ℕ) : ℝ) /
      (2 * (factorialSieveDegree x a : ℝ) * Real.log a) := by
    apply (le_div_iff₀ (mul_pos (by positivity) hloga)).2
    simpa only [one_mul] using hstep
  calc
    (a : ℝ) / 1600 = (a : ℝ) / 1600 * 1 := by ring
    _ ≤ (a : ℝ) / 1600 *
        (Real.log ((x + 2 : ℕ) : ℝ) /
          (2 * (factorialSieveDegree x a : ℝ) * Real.log a)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = ((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) /
        factorialSieveDegree x a := by
      norm_num [Nat.cast_add]
      field_simp
      ring

theorem rpow_half_sub_le_factorialSieveDegree_pow
    {x a : ℕ} {δ : ℝ}
    (ha : 2 ≤ a) (haC : 1600 ≤ a)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsq : a ^ 2 ≤ x + 1)
    (hconstant : Real.log 1600 ≤ δ / 4 * Real.log a)
    (hupper : Real.log a ≤
      δ / 4 * Real.log ((x + 1 : ℕ) : ℝ)) :
    (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ)) ≤
      ((a : ℝ) / 1600) ^ factorialSieveDegree x a := by
  let X : ℝ := ((x + 1 : ℕ) : ℝ)
  let A : ℝ := (a : ℝ)
  let k : ℕ := factorialSieveDegree x a
  let r : ℝ := Real.log X / (2 * Real.log A)
  have hX : 0 < X := by positivity
  have hA : 0 < A := by positivity
  have hlogA : 0 < Real.log A :=
    Real.log_pos (by dsimp only [A]; exact_mod_cast ha)
  have hlogX : 0 ≤ Real.log X :=
    Real.log_nonneg (by dsimp only [X]; exact_mod_cast (show 1 ≤ x + 1 by omega))
  have hkpos : 1 ≤ k := factorialSieveDegree_pos ha hsq
  have hkcast : (k : ℝ) ≤ r := by
    simpa only [k, r, X, A] using factorialSieveDegree_cast_le (x := x) ha
  have hrone : 1 ≤ r := (show (1 : ℝ) ≤ k by exact_mod_cast hkpos).trans hkcast
  have hrfloor : r - 1 ≤ (k : ℝ) := by
    have hlt : r < (k : ℝ) + 1 := by
      simpa only [r, k, factorialSieveDegree] using
        (Nat.lt_floor_add_one r)
    linarith
  have hrlog : r * Real.log A = Real.log X / 2 := by
    dsimp only [r]
    field_simp
  have hlogdiv : Real.log (A / 1600) =
      Real.log A - Real.log 1600 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have hbaseNonneg : 0 ≤ Real.log (A / 1600) := by
    apply Real.log_nonneg
    dsimp only [A]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 1600)).2 (by
      exact_mod_cast haC)
  have hbaseLower : (1 - δ / 4) * Real.log A ≤
      Real.log (A / 1600) := by
    rw [hlogdiv]
    dsimp only [A] at hconstant ⊢
    linarith
  have hrminus : 0 ≤ r - 1 := by linarith
  have honeMinus : 0 ≤ 1 - δ / 4 := by linarith
  have hδlogX : 0 ≤ δ * Real.log X := mul_nonneg hδ.le hlogX
  have hδlogA : 0 ≤ δ * Real.log A := mul_nonneg hδ.le hlogA.le
  have hdrlog : δ * (r * Real.log A) = δ * (Real.log X / 2) :=
    congrArg (fun z : ℝ => δ * z) hrlog
  have htarget : ((1 / 2 : ℝ) - δ) * Real.log X ≤
      (r - 1) * ((1 - δ / 4) * Real.log A) := by
    dsimp only [X, A] at hupper ⊢
    nlinarith
  have hlogPower : ((1 / 2 : ℝ) - δ) * Real.log X ≤
      (k : ℝ) * Real.log (A / 1600) := by
    calc
      ((1 / 2 : ℝ) - δ) * Real.log X ≤
          (r - 1) * ((1 - δ / 4) * Real.log A) := htarget
      _ ≤ (r - 1) * Real.log (A / 1600) :=
        mul_le_mul_of_nonneg_left hbaseLower hrminus
      _ ≤ (k : ℝ) * Real.log (A / 1600) :=
        mul_le_mul_of_nonneg_right hrfloor hbaseNonneg
  calc
    X ^ ((1 / 2 : ℝ) - δ) =
        Real.exp (((1 / 2 : ℝ) - δ) * Real.log X) := by
      rw [Real.rpow_def_of_pos hX]
      ring_nf
    _ ≤ Real.exp ((k : ℝ) * Real.log (A / 1600)) :=
      Real.exp_le_exp.mpr hlogPower
    _ = (A / 1600) ^ k := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      ring_nf

theorem factorialLargeSieveSurvivor_card_le_rpow
    {x a H : ℕ} {δ : ℝ}
    (ha : 2 ≤ a) (haC : 1600 ≤ a)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hcard : (a : ℝ) / (4 * Real.log a) ≤
      ((factorialUpperHalfPrimes a).card : ℝ))
    (hH : 1 ≤ H)
    (hlog : (400 : ℝ) ≤ Real.log (x + 2))
    (hhard : (H : ℝ) * Real.log (x + 2) / 100 < a)
    (hsq : a ^ 2 ≤ x + 1)
    (hlarge : 4 * Real.log ((x + 1 : ℕ) : ℝ) ≤ a)
    (hconstant : Real.log 1600 ≤ δ / 4 * Real.log a)
    (hupper : Real.log a ≤
      δ / 4 * Real.log ((x + 1 : ℕ) : ℝ)) :
    ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
      8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) := by
  let k := factorialSieveDegree x a
  have hk : 1 ≤ k := factorialSieveDegree_pos ha hsq
  have hkcard : 2 * k ≤ (factorialUpperHalfPrimes a).card :=
    two_mul_factorialSieveDegree_le_card ha hcard hlarge
  have hproduct : (a ^ k) * (a ^ k) ≤ x + 1 :=
    factorialSieveDegree_product_le ha
  have hsource := factorialLargeSieveSurvivor_card_source_bound
    ha hcard hH hlog hhard hk hkcard hproduct
  have hbase := factorial_source_scale_base_ge (x := x) ha hk
  have hdenom : ((a : ℝ) / 1600) ^ k ≤
      (((a : ℝ) * Real.log (x + 2) / (3200 * Real.log a)) / k) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  have hpower := rpow_half_sub_le_factorialSieveDegree_pow
    ha haC hδ hδone hsq hconstant hupper
  have hmul : (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ)) *
      ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
        8 * (x + 1) := by
    calc
      (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ)) *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) ≤
        ((a : ℝ) / 1600) ^ k *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) :=
        mul_le_mul_of_nonneg_right hpower (by positivity)
      _ ≤ (((a : ℝ) * Real.log (x + 2) /
            (3200 * Real.log a)) / k) ^ k *
          ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) :=
        mul_le_mul_of_nonneg_right hdenom (by positivity)
      _ ≤ 8 * (x + 1) := hsource
  have hX : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hP : (0 : ℝ) <
      ((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ) :=
    Real.rpow_pos_of_pos hX _
  apply le_of_mul_le_mul_right _ hP
  calc
    ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) *
        (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ)) ≤
      8 * (x + 1) := by simpa only [mul_comm] using hmul
    _ = (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) *
        (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - δ)) := by
      rw [mul_assoc, ← Real.rpow_add hX]
      norm_num [Nat.cast_add]

theorem eventually_log_nat_le_mul_log_of_powerUpperBound_zero
    (g : ℕ → ℕ)
    (hg : PowerUpperBound (fun x => (g x : ℝ)) 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (g x : ℝ) ≤
        δ * Real.log ((x + 1 : ℕ) : ℝ) := by
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨C, hC⟩ := (hg (δ / 2) hhalf).bound
  have hpowTop : Tendsto (fun x : ℕ => (x : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  have habsorb : ∀ᶠ x : ℕ in atTop, C ≤ (x : ℝ) ^ (δ / 2) :=
    hpowTop.eventually (eventually_ge_atTop C)
  filter_upwards [hC, habsorb, eventually_ge_atTop (1 : ℕ)] with x hx hCx hxone
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxone
  have hXpos : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hgNonneg : (0 : ℝ) ≤ g x := by positivity
  have hxpowNonneg : 0 ≤ (x : ℝ) ^ (δ / 2) :=
    Real.rpow_nonneg hxpos.le _
  have hg_le_xpow : (g x : ℝ) ≤ (x : ℝ) ^ δ := by
    calc
      (g x : ℝ) = ‖(g x : ℝ)‖ := by
        rw [Real.norm_of_nonneg hgNonneg]
      _ ≤ C * ‖(x : ℝ) ^ ((0 : ℝ) + δ / 2)‖ := hx
      _ = C * (x : ℝ) ^ (δ / 2) := by
        rw [zero_add, Real.norm_of_nonneg hxpowNonneg]
      _ ≤ (x : ℝ) ^ (δ / 2) * (x : ℝ) ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hCx hxpowNonneg
      _ = (x : ℝ) ^ δ := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  have hxX : (x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show x ≤ x + 1 by omega)
  have hg_le_Xpow : (g x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) ^ δ :=
    hg_le_xpow.trans (Real.rpow_le_rpow hxpos.le hxX hδ.le)
  by_cases hgzero : g x = 0
  · have hlogXnonneg : 0 ≤ Real.log (((x + 1 : ℕ) : ℝ)) :=
      Real.log_nonneg (show (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) by
        exact_mod_cast (show 1 ≤ x + 1 by omega))
    rw [hgzero, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg hδ.le hlogXnonneg
  · calc
      Real.log (g x : ℝ) ≤
          Real.log (((x + 1 : ℕ) : ℝ) ^ δ) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < (g x : ℝ) by
            exact_mod_cast (Nat.pos_of_ne_zero hgzero))
          (Real.rpow_pos_of_pos hXpos δ) hg_le_Xpow
      _ = δ * Real.log ((x + 1 : ℕ) : ℝ) := Real.log_rpow hXpos δ

theorem nat_sq_le_succ_of_log_le
    {x a : ℕ} {δ : ℝ} (ha : 2 ≤ a) (hδone : δ ≤ 1)
    (hupper : Real.log a ≤
      δ / 4 * Real.log ((x + 1 : ℕ) : ℝ)) :
    a ^ 2 ≤ x + 1 := by
  have hA : (0 : ℝ) < a := by positivity
  have hX : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hlogX : 0 ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x + 1 by omega))
  have hlog : 2 * Real.log (a : ℝ) ≤
      Real.log ((x + 1 : ℕ) : ℝ) := by
    calc
      2 * Real.log (a : ℝ) ≤
          2 * (δ / 4 * Real.log ((x + 1 : ℕ) : ℝ)) := by gcongr
      _ ≤ Real.log ((x + 1 : ℕ) : ℝ) := by nlinarith
  have hreal : (((a ^ 2 : ℕ) : ℝ)) ≤ ((x + 1 : ℕ) : ℝ) := by
    calc
      (((a ^ 2 : ℕ) : ℝ)) = Real.exp (2 * Real.log (a : ℝ)) := by
        rw [Nat.cast_pow]
        conv_lhs => rw [← Real.exp_log (pow_pos hA 2)]
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.exp (Real.log ((x + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr hlog
      _ = ((x + 1 : ℕ) : ℝ) := Real.exp_log hX
  exact_mod_cast hreal

theorem card_factorialLargeSieveBudgetedEndpointsUpTo_le_sum_intervals
    (x B A G : ℕ) :
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤
      ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        (factorialLargeSieveIntervalsAt x B a H).card := by
  calc
    (factorialLargeSieveBudgetedEndpointsUpTo x B A G).card ≤
        (factorialLargeSieveBudgetedIntervalsUpTo x B A G).card :=
      Finset.card_image_le
    _ = ((Finset.Icc 1 A).biUnion fun a =>
        (Finset.Icc 2 G).biUnion fun H =>
          factorialLargeSieveIntervalsAt x B a H).card := by
      rw [factorialLargeSieveBudgetedIntervalsUpTo_eq_biUnion]
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((Finset.Icc 2 G).biUnion fun H =>
          factorialLargeSieveIntervalsAt x B a H).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        (factorialLargeSieveIntervalsAt x B a H).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.card_biUnion_le

theorem factorialLargeSieveIntervalsAt_eq_empty_of_not_parameters
    {x B a H : ℕ}
    (hnot : ¬ (B < H ∧
      (H : ℝ) * Real.log (x + 2) / 100 < a)) :
    factorialLargeSieveIntervalsAt x B a H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  apply hnot
  have htAt := mem_factorialLargeSieveIntervalsAt.mp ht
  have htLarge := mem_factorialLargeSieveIntervalsUpTo.mp htAt.1
  exact ⟨by simpa only [htAt.2.2] using htLarge.1,
    by simpa only [htAt.2.1, htAt.2.2] using htLarge.2⟩

theorem eventually_factorialLargeSieveIntervalsAt_card_le_rpow
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∀ᶠ x : ℕ in atTop,
      ∀ a ∈ Finset.Icc 1 (factorialLemma41IndexBudget x),
        ∀ H ∈ Finset.Icc 2 (factorialLemma42GapBudget x),
          ((factorialLargeSieveIntervalsAt x 400 a H).card : ℝ) ≤
            8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog400 : ∀ᶠ x : ℕ in atTop, (400 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 400)
  obtain ⟨a₀, ha₀⟩ :=
    (eventually_atTop.1 eventually_card_factorialUpperHalfPrimes_lower)
  have hlogPNT : ∀ᶠ x : ℕ in atTop,
      (100 : ℝ) * a₀ ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop ((100 : ℝ) * a₀))
  let M : ℝ := (4 / δ) * Real.log 1600
  have hlogConstant : ∀ᶠ x : ℕ in atTop,
      Real.exp M / 4 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (Real.exp M / 4))
  have hbudgetLog :=
    eventually_log_nat_le_mul_log_of_powerUpperBound_zero
      factorialLemma41IndexBudget
      factorialLemma41IndexBudget_powerUpperBound (δ := δ / 4) (by positivity)
  filter_upwards [hlog400, hlogPNT, hlogConstant, hbudgetLog,
      eventually_ge_atTop (1 : ℕ)] with x hx400 hxPNT hxConstant hxBudget hxpos
  intro a haRange H hHRange
  by_cases hparams : 400 < H ∧
      (H : ℝ) * Real.log (x + 2) / 100 < a
  · have hlogMonoX : Real.log (x : ℝ) ≤
        Real.log ((x + 1 : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (x : ℝ)
        exact_mod_cast hxpos
      · show (0 : ℝ) < ((x + 1 : ℕ) : ℝ)
        positivity
      · exact_mod_cast (show x ≤ x + 1 by omega)
    have hlogMonoX2 : Real.log (x : ℝ) ≤
        Real.log ((x : ℝ) + 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (x : ℝ)
        exact_mod_cast hxpos
      · show (0 : ℝ) < (x : ℝ) + 2
        positivity
      · norm_num
    have hlog : (400 : ℝ) ≤ Real.log ((x : ℝ) + 2) :=
      hx400.trans hlogMonoX2
    have hH : 1 ≤ H := by omega
    have haCReal : (1600 : ℝ) < a := by
      have hHReal : (400 : ℝ) < H := by exact_mod_cast hparams.1
      nlinarith
    have haC : 1600 ≤ a := by exact_mod_cast haCReal.le
    have ha : 2 ≤ a := haC.trans' (by decide)
    have hlarge : 4 * Real.log ((x + 1 : ℕ) : ℝ) ≤ a := by
      have hHReal : (400 : ℝ) < H := by exact_mod_cast hparams.1
      have hlogXnonneg : 0 ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ x + 1 by omega))
      have hlogOrder : Real.log ((x + 1 : ℕ) : ℝ) ≤
          Real.log ((x : ℝ) + 2) := by
        apply Real.strictMonoOn_log.monotoneOn
        · show (0 : ℝ) < ((x + 1 : ℕ) : ℝ)
          positivity
        · show (0 : ℝ) < (x : ℝ) + 2
          positivity
        · norm_num
      nlinarith
    have ha₀aReal : (a₀ : ℝ) < a := by
      have hHReal : (1 : ℝ) ≤ H := by exact_mod_cast hH
      nlinarith
    have ha₀a : a₀ ≤ a := by exact_mod_cast ha₀aReal.le
    have hcard := ha₀ a ha₀a
    have haBudget : a ≤ factorialLemma41IndexBudget x :=
      (Finset.mem_Icc.mp haRange).2
    have hbudgetPos : 0 < factorialLemma41IndexBudget x :=
      lt_of_lt_of_le (by omega : 0 < a) haBudget
    have hlogBudgetMono : Real.log (a : ℝ) ≤
        Real.log (factorialLemma41IndexBudget x : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (a : ℝ)
        positivity
      · show (0 : ℝ) < (factorialLemma41IndexBudget x : ℝ)
        exact_mod_cast hbudgetPos
      · exact_mod_cast haBudget
    have hupper : Real.log (a : ℝ) ≤
        δ / 4 * Real.log ((x + 1 : ℕ) : ℝ) :=
      hlogBudgetMono.trans hxBudget
    have hsq : a ^ 2 ≤ x + 1 :=
      nat_sq_le_succ_of_log_le ha hδone hupper
    have hexpLe : Real.exp M ≤
        4 * Real.log ((x + 1 : ℕ) : ℝ) := by
      nlinarith
    have hexpLeA : Real.exp M ≤ (a : ℝ) := hexpLe.trans hlarge
    have hMle : M ≤ Real.log (a : ℝ) := by
      rw [← Real.log_exp M]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos M)
        (show (0 : ℝ) < (a : ℝ) by positivity) hexpLeA
    have hconstant : Real.log 1600 ≤ δ / 4 * Real.log (a : ℝ) := by
      calc
        Real.log 1600 = δ / 4 * M := by
          dsimp only [M]
          field_simp
        _ ≤ δ / 4 * Real.log (a : ℝ) :=
          mul_le_mul_of_nonneg_left hMle (by positivity)
    exact (show ((factorialLargeSieveIntervalsAt x 400 a H).card : ℝ) ≤
        ((factorialLargeSieveSurvivorStarts x a H).card : ℝ) by
          exact_mod_cast card_factorialLargeSieveIntervalsAt_le_survivors x 400 a H).trans
      (factorialLargeSieveSurvivor_card_le_rpow ha haC hδ hδone hcard
        hH hlog hparams.2 hsq hlarge hconstant hupper)
  · rw [factorialLargeSieveIntervalsAt_eq_empty_of_not_parameters hparams]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem card_factorialLargeSieveBudgetedEndpointsUpTo_le_rpow
    {x B A G : ℕ} {δ : ℝ}
    (hfiber : ∀ a ∈ Finset.Icc 1 A, ∀ H ∈ Finset.Icc 2 G,
      ((factorialLargeSieveIntervalsAt x B a H).card : ℝ) ≤
        8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) :
    ((factorialLargeSieveBudgetedEndpointsUpTo x B A G).card : ℝ) ≤
      (A : ℝ) * G *
        (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) := by
  let S : ℝ := 8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))
  calc
    ((factorialLargeSieveBudgetedEndpointsUpTo x B A G).card : ℝ) ≤
        ((∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
          (factorialLargeSieveIntervalsAt x B a H).card : ℕ) : ℝ) := by
      exact_mod_cast
        card_factorialLargeSieveBudgetedEndpointsUpTo_le_sum_intervals x B A G
    _ = ∑ a ∈ Finset.Icc 1 A, ∑ H ∈ Finset.Icc 2 G,
        ((factorialLargeSieveIntervalsAt x B a H).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ _a ∈ Finset.Icc 1 A, ∑ _H ∈ Finset.Icc 2 G, S := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum fun H hH => hfiber a ha H hH
    _ = ((Finset.Icc 1 A).card : ℝ) *
        (((Finset.Icc 2 G).card : ℝ) * S) := by simp
    _ ≤ (A : ℝ) * ((G : ℝ) * S) := by
      gcongr <;> simp
    _ = (A : ℝ) * G *
        (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) := by
      simp only [S]
      ring

theorem factorialLargeSieveEndpointsUpTo_subset_budgeted
    {x B A G : ℕ}
    (hsub : factorialLargeSieveIntervalsUpTo x B ⊆
      factorialLargeSieveBudgetedIntervalsUpTo x B A G) :
    factorialLargeSieveEndpointsUpTo x B ⊆
      factorialLargeSieveBudgetedEndpointsUpTo x B A G := by
  intro n hn
  rw [factorialLargeSieveEndpointsUpTo, Finset.mem_image] at hn
  rcases hn with ⟨t, ht, rfl⟩
  rw [factorialLargeSieveBudgetedEndpointsUpTo, Finset.mem_image]
  exact ⟨t, hsub ht, rfl⟩

theorem eventually_factorialLargeSieveEndpoint_card_le_budgeted_rpow
    (h42 : TaoLemma42Conclusion) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∀ᶠ x : ℕ in atTop,
      ((factorialLargeSieveEndpointsUpTo x 400).card : ℝ) ≤
        (factorialLemma41IndexBudget x : ℝ) *
          factorialLemma42GapBudget x *
            (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) := by
  filter_upwards
      [eventually_factorialLargeSieveIntervalsUpTo_subset_budgeted 400 h42,
        eventually_factorialLargeSieveIntervalsAt_card_le_rpow hδ hδone]
      with x hsub hfiber
  have hcard : (factorialLargeSieveEndpointsUpTo x 400).card ≤
      (factorialLargeSieveBudgetedEndpointsUpTo x 400
        (factorialLemma41IndexBudget x)
        (factorialLemma42GapBudget x)).card :=
    Finset.card_le_card (factorialLargeSieveEndpointsUpTo_subset_budgeted hsub)
  exact (show ((factorialLargeSieveEndpointsUpTo x 400).card : ℝ) ≤
      ((factorialLargeSieveBudgetedEndpointsUpTo x 400
        (factorialLemma41IndexBudget x)
        (factorialLemma42GapBudget x)).card : ℝ) by
      exact_mod_cast hcard).trans
    (card_factorialLargeSieveBudgetedEndpointsUpTo_le_rpow hfiber)

theorem factorialLargeSieveEndpointCount_powerUpperBound
    (h42 : TaoLemma42Conclusion) :
    PowerUpperBound
      (fun x => ((factorialLargeSieveEndpointsUpTo x 400).card : ℝ))
      (1 / 2 : ℝ) := by
  have hbudgets : PowerUpperBound
      (fun x => (factorialLemma41IndexBudget x : ℝ) *
        (factorialLemma42GapBudget x : ℝ)) 0 := by
    simpa only [zero_add] using
      factorialLemma41IndexBudget_powerUpperBound.mul
        factorialLemma42GapBudget_powerUpperBound
  intro ε hε
  let δ : ℝ := min (ε / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδeps : δ ≤ ε / 4 := min_le_left _ _
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨C, hC⟩ := (hbudgets (ε / 4) hquarter).bound
  have hendpoint :=
    eventually_factorialLargeSieveEndpoint_card_le_budgeted_rpow
      h42 hδ hδone
  refine IsBigO.of_bound (8 * C * (2 : ℝ) ^ ((1 / 2 : ℝ) + δ)) ?_
  filter_upwards [hC, hendpoint, eventually_ge_atTop (1 : ℕ)]
      with x hxBudget hxEndpoint hxone
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxone
  have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast hxone
  have hbudgetNonneg : 0 ≤
      (factorialLemma41IndexBudget x : ℝ) *
        (factorialLemma42GapBudget x : ℝ) := by positivity
  have hxQuarterNonneg : 0 ≤ (x : ℝ) ^ (ε / 4) :=
    Real.rpow_nonneg hxpos.le _
  have hbudget :
      (factorialLemma41IndexBudget x : ℝ) *
          (factorialLemma42GapBudget x : ℝ) ≤
        C * (x : ℝ) ^ (ε / 4) := by
    simpa only [zero_add, Real.norm_of_nonneg hbudgetNonneg,
      Real.norm_of_nonneg hxQuarterNonneg] using hxBudget
  have hpNonneg : 0 ≤ (1 / 2 : ℝ) + δ := by positivity
  have hshiftBase : (((x + 1 : ℕ) : ℝ)) ≤ 2 * (x : ℝ) := by
    norm_num
    exact_mod_cast (by omega : x + 1 ≤ 2 * x)
  have hshift : (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) ≤
      (2 : ℝ) ^ ((1 / 2 : ℝ) + δ) *
        (x : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
    calc
      (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) ≤
          (2 * (x : ℝ)) ^ ((1 / 2 : ℝ) + δ) :=
        Real.rpow_le_rpow (by positivity) hshiftBase hpNonneg
      _ = (2 : ℝ) ^ ((1 / 2 : ℝ) + δ) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
        rw [Real.mul_rpow (by norm_num) hxpos.le]
  have hpower : (x : ℝ) ^ (ε / 4) *
        (x : ℝ) ^ ((1 / 2 : ℝ) + δ) ≤
      (x : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    rw [← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  calc
    ((factorialLargeSieveEndpointsUpTo x 400).card : ℝ) ≤
        (factorialLemma41IndexBudget x : ℝ) *
          factorialLemma42GapBudget x *
            (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) :=
      hxEndpoint
    _ ≤ (C * (x : ℝ) ^ (ε / 4)) *
        (8 * (((x + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ))) := by
      gcongr
    _ ≤ (C * (x : ℝ) ^ (ε / 4)) *
        (8 * ((2 : ℝ) ^ ((1 / 2 : ℝ) + δ) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + δ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hshift (by norm_num)
      · exact hbudgetNonneg.trans hbudget
    _ = (8 * C * (2 : ℝ) ^ ((1 / 2 : ℝ) + δ)) *
        ((x : ℝ) ^ (ε / 4) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + δ)) := by ring
    _ ≤ (8 * C * (2 : ℝ) ^ ((1 / 2 : ℝ) + δ)) *
        (x : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
      apply mul_le_mul_of_nonneg_left hpower
      have hCnonneg : 0 ≤ C :=
        nonneg_of_mul_nonneg_left (hbudgetNonneg.trans hbudget)
          (Real.rpow_pos_of_pos hxpos _)
      positivity

/-- The maximal-degree Corollary 2.9 estimate closes the nontrivial half of
Theorem 1.9 once Lemma 4.2 is supplied. -/
theorem nontrivialFactorialThreeCount_powerUpperBound_of_lemma42
    (h42 : TaoLemma42Conclusion) :
    PowerUpperBound
      (fun x => (nontrivialFactorialThreeCount x : ℝ)) (1 / 2 : ℝ) :=
  nontrivialFactorialThreeCount_powerUpperBound_of_largeSieve 400 h42
    (factorialLargeSieveEndpointCount_powerUpperBound h42)

end

end Tao2026
