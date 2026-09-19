import Tao2026.FinitePermutationWeightedOrbits
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# All-degree Newton integrality from weighted finite orbits

Each cycle of length `l` with integral weight `b` contributes the formal
Euler factor `(1 - b X^l)⁻¹`. Its coefficients are integral, and its
logarithmic derivative has the required divisor-sum coefficients. Comparing
the resulting differential equation with the literal Newton recursion
proves integrality in every degree. No analytic convergence, trace spectrum,
or division in the ring of algebraic integers is assumed.
-/

namespace Tao2026
open Finset PowerSeries
open scoped BigOperators PowerSeries
noncomputable section

def complexEulerFactor (l : ℕ) (hl : l ≠ 0) (b : ℂ) : PowerSeries ℂ :=
  PowerSeries.expand l hl (PowerSeries.rescale b (PowerSeries.mk 1))

theorem complexEulerFactor_coeff (l : ℕ) (hl : l ≠ 0) (b : ℂ) (n : ℕ) :
    PowerSeries.coeff n (complexEulerFactor l hl b) =
      if l ∣ n then b ^ (n / l) else 0 := by
  simp [complexEulerFactor, PowerSeries.coeff_expand, PowerSeries.coeff_rescale]

theorem complexEulerFactor_constantCoeff (l : ℕ) (hl : l ≠ 0) (b : ℂ) :
    PowerSeries.constantCoeff (complexEulerFactor l hl b) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, complexEulerFactor_coeff]
  simp

theorem complexEulerFactor_mul_one_sub (l : ℕ) (hl : l ≠ 0) (b : ℂ) :
    complexEulerFactor l hl b * (1 - PowerSeries.C b * PowerSeries.X ^ l) = 1 := by
  have h := congrArg (fun f : PowerSeries ℂ =>
    PowerSeries.expand l hl (PowerSeries.rescale b f))
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa [map_mul, map_sub, PowerSeries.rescale_X, PowerSeries.expand_C,
    complexEulerFactor] using h

theorem complexEulerFactor_integral (l : ℕ) (hl : l ≠ 0) (b : ℂ)
    (hb : IsIntegral ℤ b) (n : ℕ) :
    IsIntegral ℤ (PowerSeries.coeff n (complexEulerFactor l hl b)) := by
  rw [complexEulerFactor_coeff]
  split_ifs
  · exact hb.pow _
  · exact isIntegral_zero

theorem complexEulerFactor_derivative (l : ℕ) (hl : l ≠ 0) (b : ℂ) :
    PowerSeries.X * PowerSeries.derivative ℂ (complexEulerFactor l hl b) =
      complexEulerFactor l hl b *
        (PowerSeries.C (l : ℂ) * (complexEulerFactor l hl b - 1)) := by
  let G := complexEulerFactor l hl b
  let a : PowerSeries ℂ := PowerSeries.C b * PowerSeries.X ^ l
  have hG : G * (1 - a) = 1 := complexEulerFactor_mul_one_sub l hl b
  have hc : PowerSeries.constantCoeff (1 - a) ≠ 0 := by
    simp [a, hl]
  have hInv : G = (1 - a)⁻¹ := (PowerSeries.eq_inv_iff_mul_eq_one hc).2 hG
  have hDG : PowerSeries.derivative ℂ G = G ^ 2 * PowerSeries.derivative ℂ a := by
    conv_lhs => rw [hInv, PowerSeries.derivative_inv']
    rw [← hInv, map_sub]
    simp
  have hX : (PowerSeries.X : PowerSeries ℂ) * PowerSeries.X ^ (l - 1) =
      PowerSeries.X ^ l := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hl)]
  have ha : PowerSeries.X * PowerSeries.derivative ℂ a =
      PowerSeries.C (l : ℂ) * a := by
    simp only [a, Derivation.leibniz, PowerSeries.derivative_C,
      PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one,
      smul_eq_mul]
    rw [show (l : PowerSeries ℂ) = PowerSeries.C (l : ℂ) by simp]
    calc
      _ = PowerSeries.C (l : ℂ) * PowerSeries.C b *
          (PowerSeries.X * PowerSeries.X ^ (l - 1)) := by ring
      _ = _ := by rw [hX]; ring
  have hGa : G * a = G - 1 := by linear_combination -hG
  change PowerSeries.X * PowerSeries.derivative ℂ G =
    G * (PowerSeries.C (l : ℂ) * (G - 1))
  rw [hDG]
  calc
    _ = G ^ 2 * (PowerSeries.X * PowerSeries.derivative ℂ a) := by ring
    _ = G * (PowerSeries.C (l : ℂ) * (G * a)) := by rw [ha]; ring
    _ = _ := by rw [hGa]

theorem complexPowerSeries_integral_mul (F G : PowerSeries ℂ)
    (hF : ∀ n, IsIntegral ℤ (PowerSeries.coeff n F))
    (hG : ∀ n, IsIntegral ℤ (PowerSeries.coeff n G)) (n : ℕ) :
    IsIntegral ℤ (PowerSeries.coeff n (F * G)) := by
  rw [PowerSeries.coeff_mul]
  exact IsIntegral.sum _ (fun a _ => (hF a.1).mul (hG a.2))

theorem complexPowerSeries_integral_prod {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries ℂ)
    (hF : ∀ i ∈ s, ∀ n, IsIntegral ℤ (PowerSeries.coeff n (F i))) (n : ℕ) :
    IsIntegral ℤ (PowerSeries.coeff n (∏ i ∈ s, F i)) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      simp only [prod_empty, PowerSeries.coeff_one]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  | @insert a s ha ih =>
      rw [prod_insert ha]
      exact complexPowerSeries_integral_mul _ _ (hF a (mem_insert_self _ _))
        (fun k => ih (fun i hi => hF i (mem_insert_of_mem hi)) k) n

theorem complexPowerSeries_prod_derivative {ι : Type*} (s : Finset ι)
    (F T : ι → PowerSeries ℂ)
    (hF : ∀ i ∈ s, PowerSeries.X * PowerSeries.derivative ℂ (F i) = F i * T i) :
    PowerSeries.X * PowerSeries.derivative ℂ (∏ i ∈ s, F i) =
      (∏ i ∈ s, F i) * ∑ i ∈ s, T i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, Derivation.leibniz]
      have hs := ih (fun i hi => hF i (mem_insert_of_mem hi))
      have ha' := hF a (mem_insert_self _ _)
      simp only [smul_eq_mul]
      calc
        _ = (PowerSeries.X * PowerSeries.derivative ℂ (F a)) * (∏ i ∈ s, F i) +
            F a * (PowerSeries.X * PowerSeries.derivative ℂ (∏ i ∈ s, F i)) := by ring
        _ = _ := by rw [ha', hs]; ring

theorem complexNewtonElementary_eq_signed_coeff
    (s : ℕ → ℂ) (F T : PowerSeries ℂ)
    (hF : PowerSeries.constantCoeff F = 1)
    (hT : PowerSeries.constantCoeff T = 0)
    (hD : PowerSeries.X * PowerSeries.derivative ℂ F = F * T)
    (m : ℕ)
    (hs : ∀ d, 0 < d → d ≤ m → s d = -PowerSeries.coeff d T) :
    complexNewtonElementary s m = (-1 : ℂ) ^ m * PowerSeries.coeff m F := by
  revert hs
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hs
      cases m with
      | zero => simp [complexNewtonElementary, hF]
      | succ k =>
          rw [complexNewtonElementary_succ]
          have hcoeff := congrArg (PowerSeries.coeff (k + 1)) hD
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            PowerSeries.coeff_mul] at hcoeff
          have hsum :
              (∑ a ∈ antidiagonal (k + 1) with a.1 < k + 1,
                (-1 : ℂ) ^ a.1 * complexNewtonElementary s a.1 * s a.2) =
                -(PowerSeries.coeff (k + 1) F * (k + 1)) := by
            rw [hcoeff, ← Finset.sum_neg_distrib]
            calc
              _ = ∑ a ∈ antidiagonal (k + 1) with a.1 < k + 1,
                  -(PowerSeries.coeff a.1 F * PowerSeries.coeff a.2 T) := by
                apply sum_congr rfl
                intro a ha
                have ha' := mem_filter.mp ha
                have hab := mem_antidiagonal.mp ha'.1
                rw [ih a.1 ha'.2 (fun d hd hda => hs d hd (hda.trans ha'.2.le)),
                  hs a.2 (by omega) (by omega)]
                rcases neg_one_pow_eq_or ℂ a.1 with hsign | hsign <;>
                  rw [hsign] <;> ring
              _ = _ := by
                rw [sum_filter]
                apply sum_congr rfl
                intro a ha
                split_ifs with hlt
                · rfl
                · have hab := mem_antidiagonal.mp ha
                  have ha2 : a.2 = 0 := by omega
                  simp [ha2, hT]
          rw [hsum]
          have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          field_simp

theorem complexEulerDivisorSumNewton_integral {ι : Type*} [Fintype ι]
    (l : ι → ℕ) (hl : ∀ i, l i ≠ 0) (b : ι → ℂ)
    (hb : ∀ i, IsIntegral ℤ (b i)) (s : ℕ → ℂ) (m : ℕ)
    (hs : ∀ d, 0 < d → d ≤ m → s d =
      -(∑ i, if l i ∣ d then (l i : ℂ) * b i ^ (d / l i) else 0)) :
    IsIntegral ℤ (complexNewtonElementary s m) := by
  let G (i : ι) := complexEulerFactor (l i) (hl i) (b i)
  let F : PowerSeries ℂ := ∏ i, G i
  let T : PowerSeries ℂ := ∑ i, PowerSeries.C (l i : ℂ) * (G i - 1)
  have hF : PowerSeries.constantCoeff F = 1 := by
    simp [F, G, complexEulerFactor_constantCoeff]
  have hT : PowerSeries.constantCoeff T = 0 := by
    simp [T, G, complexEulerFactor_constantCoeff]
  have hD : PowerSeries.X * PowerSeries.derivative ℂ F = F * T :=
    complexPowerSeries_prod_derivative univ G
      (fun i => PowerSeries.C (l i : ℂ) * (G i - 1))
      (fun i _ => complexEulerFactor_derivative (l i) (hl i) (b i))
  have hcoeff : ∀ d, 0 < d → d ≤ m → s d = -PowerSeries.coeff d T := by
    intro d hd hdm
    rw [hs d hd hdm]
    congr 1
    simp only [T, map_sum, PowerSeries.coeff_C_mul, map_sub,
      G, complexEulerFactor_coeff, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hd),
      sub_zero, mul_ite, mul_zero]
  rw [complexNewtonElementary_eq_signed_coeff s F T hF hT hD m hcoeff]
  exact ((show IsIntegral ℤ (-1 : ℂ) from isIntegral_one.neg).pow m).mul
    (complexPowerSeries_integral_prod univ G
      (fun i _ n => complexEulerFactor_integral (l i) (hl i) (b i) (hb i) n) m)

theorem finitePermutationWeight_newton_integral {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (w : ℕ → α → ℂ)
    (hint : ∀ d x, IsIntegral ℤ (w d x))
    (hinv : ∀ d x, (σ ^ d) x = x → w d (σ x) = w d x)
    (hmul : ∀ d k x, (σ ^ d) x = x → w (d * k) x = w d x ^ k)
    (s : ℕ → ℂ) (m : ℕ)
    (hs : letI : DecidableEq α := Classical.decEq _
      ∀ d, 0 < d → d ≤ m → s d =
        -(∑ x ∈ univ.filter (fun x => (σ ^ d) x = x), w d x)) :
    IsIntegral ℤ (complexNewtonElementary s m) := by
  classical
  letI : Fintype (finitePermutationOrbits σ) := Fintype.ofFinite _
  apply complexEulerDivisorSumNewton_integral
    (finitePermutationOrbitLength σ)
    (fun o => (finitePermutationOrbitLength_pos σ o).ne')
    (fun o => w (finitePermutationOrbitLength σ o) o.out)
    (fun o => hint _ o.out) s m
  intro d hd hdm
  rw [hs d hd hdm, finitePermutationWeight_fixed_sum σ w hinv hmul d]

end
end Tao2026
