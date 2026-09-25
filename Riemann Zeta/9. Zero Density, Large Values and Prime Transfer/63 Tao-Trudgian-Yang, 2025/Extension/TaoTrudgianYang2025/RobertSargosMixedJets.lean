import TaoTrudgianYang2025.RobertSargosCubicJets
import TaoTrudgianYang2025.FiniteSmoothThirdDerivative
import TaoTrudgianYang2025.ThirteenthRootScales
import TaoTrudgianYang2025.RobertSargosShiftSupport
noncomputable section
open scoped ContDiff
namespace TaoTrudgianYang2025

private theorem cubic_remainder_contDiffAt {f : ℝ → ℝ} {m y : ℝ}
    (hf : ContDiffAt ℝ 4 f (m+y)) :
    ContDiffAt ℝ 4 (robertSargosCubicRemainder f m) y := by
  have hp : ContDiffAt ℝ 4 (finiteTaylorPolynomial f 3 m) (m+y) :=
    (finiteTaylorPolynomial_contDiff f 3 m).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  exact (hf.sub hp).comp y (contDiffAt_const.add contDiffAt_id)

def robertSargosMixedJet (f : ℝ → ℝ) (m r : ℝ) (i j k : ℕ)
    (q h n : ℝ) : ℝ :=
  iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n+q+h)-
    (-1:ℝ)^j*iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n+q-h)+
      if i = 0 then
        -iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n+h+r)+
          (-1:ℝ)^j*iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n-h-r)
      else 0

theorem robertSargos_mixed_jet_zero (f : ℝ → ℝ) (m r q h n : ℝ) :
    robertSargosMixedJet f m r 0 0 0 q h n =
      robertSargosMixedRemainder f m r q h n := by
  simp only [robertSargosMixedJet,robertSargosMixedRemainder,Nat.add_zero,
    iteratedDeriv_zero,pow_zero,one_mul,ite_true]
  ring

theorem hasDerivAt_robertSargos_mixed_jet_q
    {f : ℝ → ℝ} {m r q h n : ℝ} {i j k : ℕ} (horder : i+j+k < 4)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h))) :
    HasDerivAt (fun x => robertSargosMixedJet f m r i j k x h n)
      (robertSargosMixedJet f m r (i+1) j k q h n) q := by
  have hd (y : ℝ) (hy : ContDiffAt ℝ 4 f (m+y)) :=
    hasDerivAt_iteratedDeriv_finite horder (cubic_remainder_contDiffAt hy)
  have hdp := (hd _ hp).comp q (((hasDerivAt_id q).const_add n).add_const h)
  have hdm := (hd _ hm).comp q (((hasDerivAt_id q).const_add n).sub_const h)
  have hh := (hdp.sub (hdm.const_mul ((-1:ℝ)^j))).add_const
    (if i = 0 then
      -iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n+h+r)+
        (-1:ℝ)^j*iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) (n-h-r)
     else 0)
  simpa only [robertSargosMixedJet,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,add_zero,mul_one] using hh

theorem hasDerivAt_robertSargos_mixed_jet_n
    {f : ℝ → ℝ} {m r q h n : ℝ} {i j k : ℕ} (horder : i+j+k < 4)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosMixedJet f m r i j k q h x)
      (robertSargosMixedJet f m r i j (k+1) q h n) n := by
  have hd (y : ℝ) (hy : ContDiffAt ℝ 4 f (m+y)) :=
    hasDerivAt_iteratedDeriv_finite horder (cubic_remainder_contDiffAt hy)
  have hdp := (hd _ hp).comp n (((hasDerivAt_id n).add_const q).add_const h)
  have hdm := (hd _ hm).comp n (((hasDerivAt_id n).add_const q).sub_const h)
  have hdrp := (hd _ hrp).comp n (((hasDerivAt_id n).add_const h).add_const r)
  have hdrm := (hd _ hrm).comp n (((hasDerivAt_id n).sub_const h).sub_const r)
  by_cases hi : i = 0
  · simpa only [robertSargosMixedJet,if_pos hi,Nat.add_assoc,mul_one] using
      (hdp.sub (hdm.const_mul ((-1:ℝ)^j))).add
        (hdrp.neg.add (hdrm.const_mul ((-1:ℝ)^j)))
  · simpa only [robertSargosMixedJet,if_neg hi,Nat.add_assoc,mul_one,add_zero] using
      hdp.sub (hdm.const_mul ((-1:ℝ)^j))

theorem hasDerivAt_robertSargos_mixed_jet_h
    {f : ℝ → ℝ} {m r q h n : ℝ} {i j k : ℕ} (horder : i+j+k < 4)
    (hp : ContDiffAt ℝ 4 f (m+(n+q+h)))
    (hm : ContDiffAt ℝ 4 f (m+(n+q-h)))
    (hrp : ContDiffAt ℝ 4 f (m+(n+h+r)))
    (hrm : ContDiffAt ℝ 4 f (m+(n-h-r))) :
    HasDerivAt (fun x => robertSargosMixedJet f m r i j k q x n)
      (robertSargosMixedJet f m r i (j+1) k q h n) h := by
  have hd (y : ℝ) (hy : ContDiffAt ℝ 4 f (m+y)) :=
    hasDerivAt_iteratedDeriv_finite horder (cubic_remainder_contDiffAt hy)
  have hdp := (hd _ hp).comp h ((hasDerivAt_id h).const_add (n+q))
  have hdm := (hd _ hm).comp h ((hasDerivAt_id h).const_sub (n+q))
  have hdrp := (hd _ hrp).comp h (((hasDerivAt_id h).const_add n).add_const r)
  have hdrm := (hd _ hrm).comp h (((hasDerivAt_id h).const_sub n).sub_const r)
  by_cases hi : i = 0
  · convert (hdp.sub (hdm.const_mul ((-1:ℝ)^j))).add
      (hdrp.neg.add (hdrm.const_mul ((-1:ℝ)^j))) using 1
    · funext x
      simp only [robertSargosMixedJet,if_pos hi,Function.comp_apply,Pi.sub_apply,
        Pi.add_apply,Pi.neg_apply,id_eq]
    · simp only [robertSargosMixedJet,if_pos hi,pow_succ]
      rw [show i+(j+1)+k = i+j+k+1 by omega]
      ring
  · convert hdp.sub (hdm.const_mul ((-1:ℝ)^j)) using 1
    · funext x
      simp only [robertSargosMixedJet,if_neg hi,add_zero,Function.comp_apply,
        Pi.sub_apply]
    · simp only [robertSargosMixedJet,if_neg hi,add_zero,pow_succ]
      rw [show i+(j+1)+k = i+j+k+1 by omega]
      ring

theorem abs_robertSargos_mixed_jet_le
    {f : ℝ → ℝ} {a b m r q h n B L : ℝ} {i j k : ℕ}
    (horder : i+j+k ≤ 4) (hB : 0 ≤ B) (hm : m ∈ Set.Icc a b)
    (hp : ∀ y ∈ ({n+q+h,n+q-h,n+h+r,n-h-r} : Finset ℝ),
      m+y ∈ Set.Icc a b ∧ |y| ≤ L)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 4 f x)
    (hb : ∀ x ∈ Set.Icc a b, |iteratedDeriv 4 f x| ≤ B) :
    |robertSargosMixedJet f m r i j k q h n| ≤ 4*B*L^(4-(i+j+k)) := by
  have hj (y : ℝ) (hy : y ∈ ({n+q+h,n+q-h,n+h+r,n-h-r} : Finset ℝ)) :
      |iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m) y| ≤
        B*L^(4-(i+j+k)) := by
    have hy' := hp y hy
    have hin (x : ℝ) (hx : x ∈ Set.uIcc m (m+y)) : x ∈ Set.Icc a b :=
      ⟨(le_min hm.1 hy'.1.1).trans hx.1, hx.2.trans (max_le hm.2 hy'.1.2)⟩
    exact robertSargos_cubic_remainder_radius_jets horder hy'.2
      (fun x hx => hf x (hin x hx)) (fun x hx => hb x (hin x hx))
  have h₁ := hj (n+q+h) (by simp)
  have h₂ := hj (n+q-h) (by simp)
  have h₃ := hj (n+h+r) (by simp)
  have h₄ := hj (n-h-r) (by simp)
  have hL : 0 ≤ L := (abs_nonneg (n+q+h)).trans (hp _ (by simp)).2
  have hD : 0 ≤ B*L^(4-(i+j+k)) := mul_nonneg hB (pow_nonneg hL _)
  let g := iteratedDeriv (i+j+k) (robertSargosCubicRemainder f m)
  have ht := abs_sub_le (g (n+q+h)) 0 ((-1:ℝ)^j*g (n+q-h))
  have hu := abs_add_le (-g (n+h+r)) ((-1:ℝ)^j*g (n-h-r))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_pow,abs_one,one_pow,one_mul] at ht hu
  by_cases hi : i = 0
  · have hv := abs_add_le (g (n+q+h)-(-1:ℝ)^j*g (n+q-h))
      (-g (n+h+r)+(-1:ℝ)^j*g (n-h-r))
    simp only [robertSargosMixedJet,if_pos hi]
    dsimp [g] at ht hu hv
    linarith
  · simp only [robertSargosMixedJet,if_neg hi,add_zero]
    dsimp [g] at ht
    linarith

theorem robertSargos_mixed_shift_geometry
    {M H Q m r q h n : ℝ} (hQ : 1 ≤ Q) (hH : 0 ≤ H) (hHQ : 2*H ≤ Q)
    (hm : m ∈ Set.Icc (2*H+Q) (M-2*H-2*Q))
    (hq : |q| ≤ Q) (hh : h ∈ Set.Icc H (2*H))
    (hhr : h+r ∈ Set.Icc H (2*H)) (hn : n ∈ Set.Icc 1 Q) :
    m ∈ Set.Icc 1 M ∧
      ∀ y ∈ ({n+q+h,n+q-h,n+h+r,n-h-r} : Finset ℝ),
        m+y ∈ Set.Icc 1 M ∧ |y| ≤ 3*Q := by
  have hqa := abs_le.mp hq
  refine ⟨⟨by linarith [hm.1],by linarith [hm.2]⟩,?_⟩
  intro y hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · constructor <;> linarith [hm.1,hm.2,hqa.1,hqa.2,hh.1,hh.2,hhr.1,hhr.2,hn.1,hn.2]
    · rw [abs_le]
      constructor <;> linarith [hqa.1,hqa.2,hh.1,hh.2,hhr.1,hhr.2,hn.1,hn.2]

theorem robertSargos_normalized_mixed_jet_bound
    {f : ℝ → ℝ} {M H Q m r q h n C lam : ℝ} {i j k : ℕ}
    (horder : i+j+k ≤ 4) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hQ : 1 ≤ Q) (hH : 0 ≤ H) (hHQ : 2*H ≤ Q) (hscale : lam*Q^4 ≤ 1)
    (hm : m ∈ Set.Icc (2*H+Q) (M-2*H-2*Q))
    (hq : |q| ≤ Q) (hh : h ∈ Set.Icc H (2*H))
    (hhr : h+r ∈ Set.Icc H (2*H)) (hn : n ∈ Set.Icc 1 Q)
    (hf : ∀ x ∈ Set.Icc 1 M, ContDiffAt ℝ 4 f x)
    (hb : ∀ x ∈ Set.Icc 1 M, |iteratedDeriv 4 f x| ≤ C*lam) :
    Q^(i+j+k)*|robertSargosMixedJet f m r i j k q h n| ≤ 324*C := by
  obtain ⟨hm',hp⟩ := robertSargos_mixed_shift_geometry hQ hH hHQ hm hq hh hhr hn
  have ht := abs_robertSargos_mixed_jet_le horder (mul_nonneg hC hlam) hm' hp hf hb
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have he : Q^(i+j+k)*(4*(C*lam)*(3*Q)^(4-(i+j+k))) =
      4*C*(3:ℝ)^(4-(i+j+k))*(lam*Q^4) := by
    rw [mul_pow]
    have hpw : Q^(i+j+k)*Q^(4-(i+j+k)) = Q^4 := by
      rw [← pow_add,Nat.add_sub_of_le horder]
    calc
      _ = 4*C*(3:ℝ)^(4-(i+j+k))*lam*(Q^(i+j+k)*Q^(4-(i+j+k))) := by ring
      _ = _ := by rw [hpw]; ring
  have hp3 : (3:ℝ)^(4-(i+j+k)) ≤ 81 := by
    calc
      _ ≤ (3:ℝ)^4 := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ = 81 := by norm_num
  calc
    _ ≤ Q^(i+j+k)*(4*(C*lam)*(3*Q)^(4-(i+j+k))) :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg hQ0 _)
    _ = _ := he
    _ ≤ 4*C*(3:ℝ)^(4-(i+j+k))*1 :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ 324*C := by nlinarith [mul_le_mul_of_nonneg_left hp3 hC]

theorem robertSargos_floor_fourth_scale {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192) :
    1 ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ∧
      lam*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)^4 ≤ 1 := by
  let T := lam^(-(1:ℝ)/13)
  have hT := thirteenth_root_physical_scale hlam hsmall
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [hT.1]
  have he : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have hTp : 1 ≤ T^3 := one_le_pow₀ hT1
  have hfloor := positive_floor_half_bounds (he ▸ hTp)
  have hQ1 : 1 ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by exact_mod_cast hfloor.1
  refine ⟨hQ1,?_⟩
  have hQ : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ T^3 := by
    rw [he]
    exact hfloor.2.2
  have h4 := pow_le_pow_left₀ (Nat.cast_nonneg ⌊lam^(-(3:ℝ)/13)⌋₊) hQ 4
  have h12 : T^12 ≤ T^13 := pow_le_pow_right₀ hT1 (by norm_num)
  have hp : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)^4 ≤ T^13 := by
    calc
      _ ≤ (T^3)^4 := h4
      _ = T^12 := by ring
      _ ≤ _ := h12
  have hmul := mul_le_mul_of_nonneg_left hp hlam.le
  have ht13 : T^13*lam = 1 := hT.2
  nlinarith

theorem robertSargos_floor_half_height {lam : ℝ} {H : ℕ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    2*(H:ℝ) ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by
  let T := lam^(-(1:ℝ)/13)
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hT1 : 1 ≤ T := by linarith
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have hfloor := (positive_floor_half_bounds
    (show 1 ≤ lam^(-(3:ℝ)/13) by rw [← h3]; exact one_le_pow₀ hT1)).2.1
  rw [← h2] at hH
  rw [← h3] at hfloor ⊢
  nlinarith [mul_le_mul_of_nonneg_right hT (sq_nonneg T)]

theorem robertSargos_physical_mixed_jet_bound
    (f : ℝ → ℝ) (M H : ℕ) (m : ℤ) {C lam r q h n : ℝ} {i j k : ℕ}
    (horder : i+j+k ≤ 4) (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hm : m ∈ robertSargosCommonMInterval M H
      ⌊lam^(-(3:ℝ)/13)⌋₊ ⌊lam^(-(3:ℝ)/13)⌋₊)
    (hq : |q| ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hh : h ∈ Set.Icc (H:ℝ) (2*H)) (hhr : h+r ∈ Set.Icc (H:ℝ) (2*H))
    (hn : n ∈ Set.Icc 1 (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))
    (hf : ∀ x ∈ Set.Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Set.Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Set.Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)^(i+j+k)*
      |robertSargosMixedJet f m r i j k q h n| ≤ 324*C := by
  obtain ⟨hQ,hscale⟩ := robertSargos_floor_fourth_scale hlam hsmall
  have hHQ := robertSargos_floor_half_height hlam hsmall hH
  simp only [robertSargosCommonMInterval,Finset.mem_Icc] at hm
  have hml : 2*(H:ℝ)+(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
  have hmu : (m:ℝ) ≤ (M:ℝ)-2*H-(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)-
      (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by exact_mod_cast hm.2
  apply robertSargos_normalized_mixed_jet_bound horder (zero_le_one.trans hC)
    hlam.le hQ (Nat.cast_nonneg H) hHQ hscale ⟨hml,by linarith⟩ hq hh hhr hn hf
  intro x hx
  rw [abs_of_nonneg (hlam.le.trans (hlo x hx))]
  exact hhi x hx

end TaoTrudgianYang2025
