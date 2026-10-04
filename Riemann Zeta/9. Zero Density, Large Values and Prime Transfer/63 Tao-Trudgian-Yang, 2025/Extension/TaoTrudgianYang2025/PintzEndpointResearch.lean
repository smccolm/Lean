import TaoTrudgianYang2025.LiteratureDensity
import TaoTrudgianYang2025.HeathBrownSharpNearRow
import TaoTrudgianYang2025.HeathBrownSharpAsymptotics
import GuthMaynard.LargeValuesMatrix
import TaoTrudgianYang2025.DirichletBlockPhase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TaoTrudgianYang2025.ZetaLogReflectionTerms
import TaoTrudgianYang2025.AtkinsonFirstDerivative
import TaoTrudgianYang2025.ContinuousSecondDerivativeRange
import TaoTrudgianYang2025.AtkinsonMainPartialSummation
import TaoTrudgianYang2025.IntegerIntervalCount
import TaoTrudgianYang2025.ExponentPairGramLogLoss
import TaoTrudgianYang2025.RobertSargosExponentPair
import TaoTrudgianYang2025.HeathBrownExponentPairs
import GuthMaynard.HughesYoungDFIProfile
import Mathlib.Order.Preorder.Finite

/-!
# Research proof of the frozen second Pintz endpoint

This is an owner-authorized research strengthening, not a reproduction of
Pintz Theorem 1 at its strict cell boundary. No frozen statement is changed.

For the actual logarithmic coefficient cells at H = ceil(N^(9/40)), the
mixed-height overlap count is at most N^(19/20), and the self count at most
3*N. Heights are aggregated BEFORE Holder. The critical degree-six VMVT,
proved by the pinned native dependency, supplies the 42nd moment. Both
Abel transfers and the actual translation-boundary error are included.
The resulting separated count is at most N^(7/200); analytic local
occupancy recovers the original count at most N^(9/100). The exact
scale neighbourhood then gives LV_zeta(41/42,tau) <= 3*tau/170 on
37/7 <= tau < 340/63, and the existing density transfer gives 63/85.

The retained research scratch preserves the other explored routes.
The first and integer-tail disputed endpoints are not proved here.
-/

noncomputable section
open Complex Finset RiemannZeta.GuthMaynard MeasureTheory
open scoped ComplexConjugate Matrix ComplexOrder ENNReal
namespace TaoTrudgianYang2025.PintzEndpointResearch
open TaoTrudgianYang2025

def gramKernel (P : LargeValuePattern) (t u : ℝ) : ℂ :=
  ∑ n ∈ P.indices, dirichletPhase n (u-t)

def farMatrix (P : LargeValuePattern) (L : ℝ) :
    Matrix P.ordinates P.ordinates ℂ := fun t u =>
  if L < |(u:ℝ)-t| then gramKernel P t u else 0

def nearMatrix (P : LargeValuePattern) (L : ℝ) :
    Matrix P.ordinates P.ordinates ℂ := fun t u =>
  if |(u:ℝ)-t| ≤ L then gramKernel P t u else 0

def fullMatrix (P : LargeValuePattern) : Matrix P.ordinates P.ordinates ℂ :=
  fun t u => gramKernel P t u

theorem gramKernel_conj (P : LargeValuePattern) (t u : ℝ) :
    conj (gramKernel P u t) = gramKernel P t u := by
  unfold gramKernel
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← dirichletPhase_mul_star (P.index_pos hn) t u,
    ← dirichletPhase_mul_star (P.index_pos hn) u t]
  simp only [Complex.star_def, map_mul, starRingEnd_self_apply]
  ring

#print axioms gramKernel_conj

theorem nearMatrix_hermitian (P : LargeValuePattern) (L : ℝ) :
    (nearMatrix P L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro t u
  change conj (if |(t:ℝ)-u| ≤ L then gramKernel P u t else 0) = _
  rw [abs_sub_comm (t:ℝ) (u:ℝ)]
  by_cases h : |(u:ℝ)-t| ≤ L
  · simp only [nearMatrix, h, ite_true, gramKernel_conj]
  · simp only [nearMatrix, h, ite_false, map_zero]

#print axioms nearMatrix_hermitian

theorem near_add_far (P : LargeValuePattern) (L : ℝ) :
    nearMatrix P L+farMatrix P L = fullMatrix P := by
  ext t u
  simp only [Matrix.add_apply, nearMatrix, farMatrix, fullMatrix]
  by_cases h : |(u:ℝ)-t| ≤ L
  · simp only [h, not_lt_of_ge h, ite_true, ite_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_false, ite_true, zero_add]

#print axioms near_add_far

private theorem hermitian_quadratic_norm_le_row {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {B : ℝ}
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ B) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ B*(∑ i, ‖x i‖^2) := by
  let S := ∑ i, ∑ j, ‖A i j‖*‖x i‖*‖x j‖
  have hnorm : ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ S := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [norm_mul, norm_star]
    exact le_of_eq (by ring)
  have hsymm (i j : ι) : ‖A j i‖ = ‖A i j‖ := by
    rw [← hA.apply i j, norm_star]
  have hsplit : (∑ i, ∑ j, ‖A i j‖*(‖x i‖^2+‖x j‖^2)) =
      2*(∑ i, (∑ j, ‖A i j‖)*‖x i‖^2) := by
    simp only [mul_add, Finset.sum_add_distrib]
    have hs : (∑ i, ∑ j, ‖A i j‖*‖x j‖^2) =
        ∑ i, (∑ j, ‖A i j‖)*‖x i‖^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [hsymm, ← Finset.sum_mul]
    rw [hs]
    simp only [← Finset.sum_mul]
    ring
  have hs : 2*S ≤ ∑ i, ∑ j, ‖A i j‖*(‖x i‖^2+‖x j‖^2) := by
    dsimp only [S]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_nonneg (norm_nonneg (A i j)) (sq_nonneg (‖x i‖-‖x j‖))
    nlinarith only [hh]
  have hr : (∑ i, (∑ j, ‖A i j‖)*‖x i‖^2) ≤ B*(∑ i, ‖x i‖^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  rw [hsplit] at hs
  linarith only [hnorm,hs,hr]

#print axioms hermitian_quadratic_norm_le_row

def zetaAnchor (P : ZetaLargeValuePattern) (t : ℝ) : ℂ :=
  ∑ n ∈ P.active, dirichletPhase n t

theorem zetaAnchor_eq_pattern (P : ZetaLargeValuePattern) (t : ℝ) :
    zetaAnchor P t = ∑ n ∈ P.indices, P.coeff n*dirichletPhase n t := by
  classical
  rw [zetaAnchor]
  calc
    _ = ∑ n ∈ P.active, P.coeff n*dirichletPhase n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [P.coeff_eq_indicator n (P.active_subset hn),if_pos hn,one_mul]
    _ = _ := Finset.sum_subset P.active_subset (fun n hn hna => by
      rw [P.coeff_eq_indicator n hn,if_neg hna,zero_mul])

#print axioms zetaAnchor_eq_pattern

def anchorMass (P : ZetaLargeValuePattern) : ℝ :=
  ∑ t : P.ordinates, ‖zetaAnchor P t‖^2

def anchorFar (P : ZetaLargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t : P.ordinates, ∑ u : P.ordinates,
    zetaAnchor P t*conj (zetaAnchor P u)*farMatrix P.toLargeValuePattern L t u

theorem anchorMass_lower (P : ZetaLargeValuePattern) :
    (P.ordinates.card:ℝ)*P.V^2 ≤ anchorMass P := by
  have hlow (t : P.ordinates) : P.V ≤ ‖zetaAnchor P t‖ := by
    rw [zetaAnchor_eq_pattern]
    exact P.large t t.property
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun t (_ : t ∈ (Finset.univ:Finset P.ordinates)) =>
    pow_le_pow_left₀ P.V_pos.le (hlow t) 2)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using hs

#print axioms anchorMass_lower

private theorem weighted_gram_energy (P : LargeValuePattern) (x : P.ordinates → ℂ) :
    ((∑ n ∈ P.indices, ‖∑ t : P.ordinates, x t*dirichletPhase n t‖^2:ℝ):ℂ) =
      star x ⬝ᵥ (fullMatrix P *ᵥ x) := by
  have hp (n : ℕ) :
      ((‖∑ t : P.ordinates,x t*dirichletPhase n t‖^2:ℝ):ℂ) =
      conj (∑ t : P.ordinates,x t*dirichletPhase n t)*
        (∑ t : P.ordinates,x t*dirichletPhase n t) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  have hcast : ((∑ n ∈ P.indices, ‖∑ t : P.ordinates,x t*dirichletPhase n t‖^2:ℝ):ℂ) =
      ∑ n ∈ P.indices,((‖∑ t : P.ordinates,x t*dirichletPhase n t‖^2:ℝ):ℂ) := by
    push_cast
    rfl
  rw [hcast]
  simp_rw [hp]
  simp only [map_sum,map_mul]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,fullMatrix,gramKernel,
    Pi.star_apply,Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← dirichletPhase_mul_star (P.index_pos hn) u t,Complex.star_def]
  ring

#print axioms weighted_gram_energy

theorem anchorSquare_le_fullGram (P : ZetaLargeValuePattern) :
    anchorMass P^2 ≤ 2*P.N*
      (star (fun t : P.ordinates => conj (zetaAnchor P t)) ⬝ᵥ
        (fullMatrix P.toLargeValuePattern *ᵥ (fun t => conj (zetaAnchor P t)))).re := by
  classical
  let x := fun t : P.ordinates => conj (zetaAnchor P t)
  let y := fun n => ∑ t : P.ordinates,x t*dirichletPhase n t
  have hm : (∑ n ∈ P.active,y n) = ((anchorMass P:ℝ):ℂ) := by
    dsimp only [y]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    change (∑ t : P.ordinates,conj (zetaAnchor P t)*zetaAnchor P t) = _
    simp only [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,anchorMass]
    push_cast
    rfl
  have hc := norm_sum_mul_sq_le P.active (fun _ => (1:ℂ)) y
  simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  rw [hm,Complex.norm_real,Real.norm_eq_abs,sq_abs] at hc
  have hs : (∑ n ∈ P.active,‖y n‖^2) ≤ ∑ n ∈ P.indices,‖y n‖^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg P.active_subset (fun _ _ _ => sq_nonneg _)
  have hcard : (P.active.card:ℝ) ≤ 2*P.N :=
    (show (P.active.card:ℝ) ≤ P.indices.card by exact_mod_cast Finset.card_le_card P.active_subset).trans
      P.indices_card_cast_le_two_mul_N
  have he := congrArg Complex.re (weighted_gram_energy P.toLargeValuePattern x)
  simp only [Complex.ofReal_re] at he
  calc
    _ ≤ (P.active.card:ℝ)*(∑ n ∈ P.active,‖y n‖^2) := hc
    _ ≤ 2*P.N*(∑ n ∈ P.indices,‖y n‖^2) :=
      mul_le_mul hcard hs (by positivity) (by have := P.one_lt_N; linarith)
    _ = _ := by rw [show (∑ n ∈ P.indices,‖y n‖^2) = _ from he]

#print axioms anchorSquare_le_fullGram

def restrictOrdinates (P : ZetaLargeValuePattern) (S : Finset ℝ)
    (hS : S ⊆ P.ordinates) : ZetaLargeValuePattern :=
  { P with
    ordinates := S
    ordinates_in_interval := fun t ht => P.ordinates_in_interval t (hS ht)
    ordinates_oneSeparated := fun t ht u hu htu =>
      P.ordinates_oneSeparated t (hS ht) u (hS hu) htu
    large := fun t ht => P.large t (hS ht) }

theorem anchorFar_eq_zero_of_diameter (P : ZetaLargeValuePattern) (L : ℝ)
    (hdiam : ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates, |u-t| ≤ L) :
    anchorFar P L = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro u _
  simp only [farMatrix,if_neg (not_lt_of_ge (hdiam t t.property u u.property)),mul_zero]

#print axioms anchorFar_eq_zero_of_diameter

theorem exponentPair_nearMatrix_local_row {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
      ∀ t : P.ordinates,
      (∑ u : P.ordinates, ‖nearMatrix P L t u‖) ≤
        2*P.N+C*((P.ordinates.filter (fun u => |u-(t:ℝ)| ≤ L)).card : ℝ)*
          ((2*L)/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*L)) : ℝ) := by
  classical
  obtain ⟨C,hC,hrow⟩ := hpair.sharp_gram_row_bound hε
  refine ⟨C,hC,?_⟩
  intro P L hL t
  let S := P.ordinates.filter (fun u => |u-(t:ℝ)| ≤ L)
  let Q : LargeValuePattern := { P with
    T := 2*L
    T_pos := by positivity
    intervalLeft := (t:ℝ)-L
    intervalRight := (t:ℝ)+L
    ordinates := S
    interval_length := by ring
    ordinates_in_interval := by
      intro u hu
      have hd := abs_le.mp (Finset.mem_filter.mp hu).2
      constructor <;> linarith
    ordinates_oneSeparated := fun u hu v hv huv =>
      P.ordinates_oneSeparated u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv
    large := fun u hu => P.large u (Finset.mem_filter.mp hu).1 }
  have htQ : (t:ℝ) ∈ Q.ordinates := by
    change (t:ℝ) ∈ S
    simp only [S,Finset.mem_filter,t.property,sub_self,abs_zero,true_and]
    exact hL.le
  have hh := hrow Q t htQ
  have he : (∑ u : P.ordinates, ‖nearMatrix P L t u‖) =
      ∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ := by
    simp only [nearMatrix,gramKernel,apply_ite norm,norm_zero,S,Finset.sum_filter]
    exact Finset.sum_attach P.ordinates (fun u : ℝ =>
      if |u-(t:ℝ)| ≤ L then ‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖ else 0)
  rw [he]
  exact hh

#print axioms exponentPair_nearMatrix_local_row

theorem exponentPair_nearMatrix_row {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
      ∀ t : P.ordinates,
      (∑ u : P.ordinates, ‖nearMatrix P L t u‖) ≤
        2*P.N+C*(P.ordinates.card : ℝ)*((2*L)/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*L)) : ℝ) := by
  obtain ⟨C,hC,hrow⟩ := exponentPair_nearMatrix_local_row hpair hε
  refine ⟨C,hC,?_⟩
  intro P L hL t
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  apply (hrow P L hL t).trans
  have hc : ((P.ordinates.filter (fun u => |u-(t:ℝ)| ≤ L)).card : ℝ) ≤
      P.ordinates.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  gcongr

#print axioms exponentPair_nearMatrix_row

theorem anchor_retained_pair {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ZetaLargeValuePattern) (L : ℝ), 0 < L →
      anchorMass P^2 ≤ 2*P.N*
        ((2*P.N+C*(P.ordinates.card : ℝ)*((2*L)/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*L)) : ℝ))*anchorMass P+
          (anchorFar P L).re) := by
  obtain ⟨C,hC,hrow⟩ := exponentPair_nearMatrix_row hpair hε
  refine ⟨C,hC,?_⟩
  intro P L hL
  let x := fun t : P.ordinates => conj (zetaAnchor P t)
  have hn := hermitian_quadratic_norm_le_row
    (nearMatrix_hermitian P.toLargeValuePattern L)
    (hrow P.toLargeValuePattern L hL) x
  have he : (∑ t : P.ordinates,‖x t‖^2) = anchorMass P := by
    simp only [x,Complex.norm_conj,anchorMass]
  rw [he] at hn
  have hf : star x ⬝ᵥ (farMatrix P.toLargeValuePattern L *ᵥ x) = anchorFar P L := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,Complex.star_def,
      x,starRingEnd_self_apply,anchorFar]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hg := anchorSquare_le_fullGram P
  change anchorMass P^2 ≤ 2*P.N*(star x ⬝ᵥ (fullMatrix P.toLargeValuePattern *ᵥ x)).re at hg
  rw [← near_add_far P.toLargeValuePattern L,Matrix.add_mulVec,dotProduct_add,
    Complex.add_re,hf] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left
    (add_le_add ((Complex.re_le_norm _).trans hn) le_rfl)
    (by have := P.one_lt_N; linarith))

#print axioms anchor_retained_pair

private theorem eventually_pairNear_scales {C η : ℝ} (hC : 1 ≤ C) (hη : 0 < η) :
    ∀ᶠ N : ℝ in Filter.atTop,
      4*N*(C*((2*N^(10/3 : ℝ))/N)^(3/40+1/10000 : ℝ)*N^(31/40+1/10000 : ℝ)) ≤
        N^(1951/1000 : ℝ) ∧
      8*N*(2*N+4*Real.pi*C*N*(harmonic (Nat.ceil (2*N^(10/3 : ℝ))) : ℝ)) ≤
        N^(2+η) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  filter_upwards [eventually_const_log_pow_le_rpow (8*C) (by positivity) 0
      (η := 1/3000) (by norm_num),
    eventually_const_log_pow_le_rpow (16+32*Real.pi*C*(19/3)) (by positivity) 1 hη,
    Filter.eventually_ge_atTop (2 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hconst hsmall hN hlog
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  constructor
  · have hscale : (2*N^(10/3 : ℝ))/N = 2*N^(7/3 : ℝ) := by
      rw [mul_div_assoc]
      nth_rw 2 [← Real.rpow_one N]
      rw [← Real.rpow_sub hNp]
      norm_num
    have htwo : (2 : ℝ)^(3/40+1/10000 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3/40+1/10000 : ℝ) ≤ 1)
    have hpow : ((2*N^(10/3 : ℝ))/N)^(3/40+1/10000 : ℝ)*N^(31/40+1/10000 : ℝ) ≤
        2*N^(2851/3000 : ℝ) := by
      rw [hscale,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNp.le _),
        ← Real.rpow_mul hNp.le,mul_assoc,← Real.rpow_add hNp]
      norm_num
      exact mul_le_mul_of_nonneg_right (by norm_num at htwo; exact htwo)
        (Real.rpow_nonneg hNp.le _)
    have hc : 8*C ≤ N^(1/3000 : ℝ) := by simpa only [pow_zero,mul_one] using hconst
    calc
      _ = 4*N*C*(((2*N^(10/3 : ℝ))/N)^(3/40+1/10000 : ℝ)*N^(31/40+1/10000 : ℝ)) := by ring
      _ ≤ 4*N*C*(2*N^(2851/3000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (8*C)*(N*N^(2851/3000 : ℝ)) := by ring
      _ ≤ N^(1/3000 : ℝ)*(N*N^(2851/3000 : ℝ)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = N^(1463/750 : ℝ) := by
        nth_rw 2 [← Real.rpow_one N]
        rw [← Real.rpow_add hNp,← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  · have hupper : 2*N^(10/3 : ℝ) ≤ N^(13/3 : ℝ) := by
      calc
        _ ≤ N*N^(10/3 : ℝ) := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNp.le _)
        _ = _ := by
          nth_rw 1 [← Real.rpow_one N]
          rw [← Real.rpow_add hNp]
          norm_num
    have hh : (harmonic (Nat.ceil (2*N^(10/3 : ℝ))) : ℝ) ≤ (19/3)*Real.log N := by
      simpa only [show (13/3 : ℝ)+2=19/3 by norm_num] using
        harmonic_ceil_le_log_of_power_window hN hlog (by norm_num : (0 : ℝ) ≤ 13/3)
          (by positivity) hupper
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 32*Real.pi*C*N^2)
    have hn := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 16*N^2)
    calc
      _ ≤ N^2*((16+32*Real.pi*C*(19/3))*Real.log N) := by nlinarith only [hm,hn]
      _ ≤ N^2*N^η := mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hsmall)
        (sq_nonneg N)
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_add hNp]; norm_num

#print axioms eventually_pairNear_scales

theorem anchorFar_pairGap_dichotomy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      (P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
      (P.ordinates.card : ℝ)^2*P.V^4 ≤ 8*P.N*(anchorFar P (P.N^(10/3 : ℝ))).re := by
  obtain ⟨C₀,hC₀,hsource⟩ := anchor_retained_pair exponentPair_three_fortieths
    (ε := 1/10000) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (eventually_pairNear_scales hC₀ hε)
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨hvalue,hdiag⟩ := hN₀ P.N ((le_max_right _ _).trans hPN)
  have hv2 : P.N^(1951/1000 : ℝ) ≤ P.V^2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at h
    norm_num at h
    exact h
  let F := C₀*((2*P.N^(10/3 : ℝ))/P.N)^(3/40+1/10000 : ℝ)*P.N^(31/40+1/10000 : ℝ)
  let D := 2*P.N+4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*P.N^(10/3 : ℝ))) : ℝ)
  have hmass : 0 ≤ anchorMass P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl := anchorMass_lower P
  have hsmall : 4*P.N*((P.ordinates.card : ℝ)*F) ≤ anchorMass P := by
    have h := mul_le_mul_of_nonneg_left (hvalue.trans hv2) (Nat.cast_nonneg P.ordinates.card)
    dsimp [F]
    nlinarith only [h,hl]
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hmass
  have hg := hsource P (P.N^(10/3 : ℝ)) (Real.rpow_pos_of_pos hNp _)
  have hbudget : 2*P.N+C₀*(P.ordinates.card : ℝ)*
      ((2*P.N^(10/3 : ℝ))/P.N)^(3/40+1/10000 : ℝ)*P.N^(31/40+1/10000 : ℝ)+
      4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*P.N^(10/3 : ℝ))) : ℝ) =
      D+(P.ordinates.card : ℝ)*F := by dsimp [D,F]; ring
  rw [hbudget] at hg
  have hmain : anchorMass P^2 ≤ 4*P.N*D*anchorMass P+
      4*P.N*(anchorFar P (P.N^(10/3 : ℝ))).re := by
    nlinarith only [hg,hsmall']
  by_cases hs : anchorMass P ≤ 8*P.N*D
  · left
    exact hl.trans (hs.trans (by simpa only [D,mul_assoc] using hdiag))
  · right
    have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hs) hmass
    have hsq := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity) hl 2
    nlinarith only [hmain,hm,hsq]

#print axioms anchorFar_pairGap_dichotomy

theorem ordinate_local_mass_pair {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V → ∀ x : ℝ,
      ((P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(10/3 : ℝ))).card : ℝ)*P.V^2 ≤
        P.N^(2+ε) := by
  classical
  obtain ⟨C,hC,hsource⟩ := anchorFar_pairGap_dichotomy hε
  refine ⟨C,hC,?_⟩
  intro P hPN hV x
  let S := P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(10/3 : ℝ))
  let Q := restrictOrdinates P S (Finset.filter_subset _ _)
  have hzero : anchorFar Q (Q.N^(10/3 : ℝ)) = 0 := by
    apply anchorFar_eq_zero_of_diameter
    intro t ht u hu
    have ht' := (Finset.mem_filter.mp ht).2
    have hu' := (Finset.mem_filter.mp hu).2
    exact abs_le.2 ⟨by dsimp [Q,restrictOrdinates]; linarith,
      by dsimp [Q,restrictOrdinates]; linarith⟩
  rcases hsource Q hPN hV with h | h
  · exact h
  · rw [hzero,Complex.zero_re,mul_zero] at h
    have hv := P.V_pos
    have hr : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hcard : (S.card : ℝ) = 0 := by
      change (S.card : ℝ)^2*P.V^4 ≤ 0 at h
      by_contra he
      have hp : 0 < (S.card : ℝ) := lt_of_le_of_ne hr (Ne.symm he)
      exact (not_lt_of_ge h) (mul_pos (sq_pos_of_pos hp) (pow_pos hv 4))
    change (S.card : ℝ)*P.V^2 ≤ _
    rw [hcard,zero_mul]
    exact Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _

#print axioms ordinate_local_mass_pair

private theorem ordinate_local_count_pair :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V → ∀ x : ℝ,
      ((P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(10/3 : ℝ))).card : ℝ) ≤
        P.N^(1/20 : ℝ) := by
  obtain ⟨C,hC,hsource⟩ := ordinate_local_mass_pair (ε := 1/1000) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro P hPN hV x
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hcount := hsource P hPN hV x
  have hv2 : P.N^(1951/1000 : ℝ) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hv2
    (Nat.cast_nonneg (P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(10/3 : ℝ))).card)
  have he : P.N^(1/20 : ℝ)*P.N^(1951/1000 : ℝ) = P.N^(2+1/1000 : ℝ) := by
    rw [← Real.rpow_add hNp]
    norm_num
  rw [← he] at hcount
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hNp _)).mp (hh.trans hcount)

#print axioms ordinate_local_count_pair

def logarithmicTaylorPhase (t : ℝ) (x : ℝ) : ℝ := -(t/(2*Real.pi))*Real.log x

theorem logarithmicTaylorPhase_character {n : ℕ} (hn : 0 < n) (t : ℝ) :
    GafniTao.heathBrownPhase (logarithmicTaylorPhase t n) = dirichletPhase n t := by
  rw [GafniTao.heathBrownPhase,dirichletPhase_eq_exp hn]
  have he : 2*Real.pi*logarithmicTaylorPhase t n = -t*Real.log (n : ℝ) := by
    unfold logarithmicTaylorPhase
    field_simp
  rw [he]
  congr 1
  ring

#print axioms logarithmicTaylorPhase_character

theorem logarithmicTaylorPhase_coordinate (p : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (p+1) (logarithmicTaylorPhase t) x / ((p+1).factorial : ℝ) =
      (-1 : ℝ)^(p+1)*t/(2*Real.pi*((p+1 : ℕ) : ℝ)*x^(p+1)) := by
  unfold logarithmicTaylorPhase
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_real_log_succ p hx]
  have hfac : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hp : ((p+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  simp only [zpow_neg,pow_succ]
  field_simp
  rw [show ((p : ℤ)+1) = ((p+1 : ℕ) : ℤ) by omega,zpow_natCast,pow_succ]
  ring

#print axioms logarithmicTaylorPhase_coordinate

def logarithmicTaylorCell (H : ℕ) (t n : ℝ) : Set (GafniTao.HeathBrownCoefficientTorus 7) :=
  GafniTao.heathBrownCoefficientCell 7 H (logarithmicTaylorPhase t) n

theorem logarithmicTaylorCell_overlap_coordinates {H : ℕ} {t u n : ℝ}
    (hn : 0 < n)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u n).Nonempty) :
    GafniTao.heathBrownDistanceToInteger ((t-u)/(8*Real.pi*n^4)) ≤ 2/((H : ℝ)^4) ∧
    GafniTao.heathBrownDistanceToInteger ((t-u)/(10*Real.pi*n^5)) ≤ 2/((H : ℝ)^5) ∧
    GafniTao.heathBrownDistanceToInteger ((t-u)/(12*Real.pi*n^6)) ≤ 2/((H : ℝ)^6) := by
  obtain ⟨α,ht,hu⟩ := hover
  have hcoord (j : Fin 6) :
      GafniTao.heathBrownDistanceToInteger
        ((-1 : ℝ)^((j : ℕ)+1)*(t-u)/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*n^((j : ℕ)+1))) ≤
        2/((H : ℝ)^((j : ℕ)+1)) := by
    have htj := ht j (Set.mem_univ j)
    have huj := hu j (Set.mem_univ j)
    have hdist := dist_triangle
      (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n j) (α j)
      (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase u) n j)
    have he : dist (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n j)
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase u) n j) =
        GafniTao.heathBrownDistanceToInteger
          ((-1 : ℝ)^((j : ℕ)+1)*(t-u)/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*n^((j : ℕ)+1))) := by
      unfold GafniTao.heathBrownCoefficientCenter
      rw [logarithmicTaylorPhase_coordinate _ t hn,logarithmicTaylorPhase_coordinate _ u hn,
        GafniTao.unitAddCircle_dist_real_coe]
      congr 1
      ring
    rw [he] at hdist
    change dist (α j) _ ≤ _ at htj huj
    rw [dist_comm (α j)] at htj
    change dist _ _ ≤ ((H : ℝ)^((j : ℕ)+1))⁻¹ at htj huj
    simpa only [div_eq_mul_inv] using
      hdist.trans (show _ ≤ 2*((H : ℝ)^((j : ℕ)+1))⁻¹ by linarith only [htj,huj])
  have h4 := hcoord ⟨3,by decide⟩
  have h5 := hcoord ⟨4,by decide⟩
  have h6 := hcoord ⟨5,by decide⟩
  norm_num at h4 h5 h6
  have he4 : 2*Real.pi*4*n^4 = 8*Real.pi*n^4 := by ring
  have he5 : 2*Real.pi*5*n^5 = 10*Real.pi*n^5 := by ring
  have he6 : 2*Real.pi*6*n^6 = 12*Real.pi*n^6 := by ring
  rw [he4] at h4
  rw [he5,← neg_sub t u,neg_div,GafniTao.heathBrownDistanceToInteger_neg] at h5
  rw [he6] at h6
  exact ⟨h4,h5,h6⟩

#print axioms logarithmicTaylorCell_overlap_coordinates

theorem logarithmicTaylorCell_commonCentre_spacing {H : ℕ} {t u n : ℝ}
    (hn : 0 < n) (hH : 1 ≤ H) (hscale : 8*n ≤ (H : ℝ)^5)
    (hheight : |t-u| ≤ Real.pi*n^6)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u n).Nonempty) :
    |t-u| ≤ 16*Real.pi*n^4/(H : ℝ)^4 := by
  obtain ⟨h4,h5,h6⟩ := logarithmicTaylorCell_overlap_coordinates hn hover
  have hHp : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH56 : (H : ℝ)^5 ≤ (H : ℝ)^6 := by
    calc
      _ = (H : ℝ)^5*1 := by ring
      _ ≤ (H : ℝ)^5*H := mul_le_mul_of_nonneg_left hH1 (by positivity)
      _ = _ := by ring
  have h6small : |(t-u)/(12*Real.pi*n^6)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi*n^6)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hheight,show 0 < Real.pi*n^6 by positivity]
  have h6abs := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h6 h6small
  rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi*n^6)] at h6abs
  have h6mul := (div_le_iff₀ (by positivity : 0 < 12*Real.pi*n^6)).mp h6abs
  rw [div_mul_eq_mul_div] at h6mul
  have h5small : |(t-u)/(10*Real.pi*n^5)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 10*Real.pi*n^5)]
    apply (div_le_iff₀ (by positivity)).mpr
    apply h6mul.trans
    apply (div_le_iff₀ (by positivity : 0 < (H : ℝ)^6)).mpr
    have hh := mul_le_mul_of_nonneg_left (hscale.trans hH56)
      (show 0 ≤ 5*Real.pi*n^5 by positivity)
    nlinarith only [hh,show 0 ≤ Real.pi*n^6 by positivity]
  have h5abs := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h5 h5small
  rw [abs_div,abs_of_pos (by positivity : 0 < 10*Real.pi*n^5)] at h5abs
  have h5mul := (div_le_iff₀ (by positivity : 0 < 10*Real.pi*n^5)).mp h5abs
  rw [div_mul_eq_mul_div] at h5mul
  have h4small : |(t-u)/(8*Real.pi*n^4)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 8*Real.pi*n^4)]
    apply (div_le_iff₀ (by positivity)).mpr
    apply h5mul.trans
    apply (div_le_iff₀ (by positivity : 0 < (H : ℝ)^5)).mpr
    have hh := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 4*Real.pi*n^4 by positivity)
    nlinarith only [hh,show 0 ≤ Real.pi*n^5 by positivity]
  have h4abs := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h4 h4small
  rw [abs_div,abs_of_pos (by positivity : 0 < 8*Real.pi*n^4)] at h4abs
  have hh := (div_le_iff₀ (by positivity : 0 < 8*Real.pi*n^4)).mp h4abs
  convert hh using 1
  ring

#print axioms logarithmicTaylorCell_commonCentre_spacing

theorem logarithmicTaylorCell_actual_far_disjoint :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.T ≤ P.N^(27/5 : ℝ) → ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      P.N^(10/3 : ℝ) < |t-u| → ∀ n ∈ P.indices,
      Disjoint (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n)
        (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u n) := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 16 (by norm_num) 0 (η := 1/8) (by norm_num))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (256*Real.pi) (by positivity) 0
      (η := 7/30) (by norm_num))
  refine ⟨max 1 (max N₀ N₁),le_max_left _ _,?_⟩
  intro P hPN hT t ht u hu hfar n hn
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnb := (P.mem_indices_iff n).mp hn
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hHlow : P.N^(9/40 : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
  have hHone : 1 ≤ H := by
    exact_mod_cast (Real.one_le_rpow P.one_lt_N.le (by norm_num : (0 : ℝ) ≤ 9/40)).trans hHlow
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hc₀ : 16 ≤ P.N^(1/8 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N
      ((le_max_left N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hc₁ : 256*Real.pi ≤ P.N^(7/30 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N
      ((le_max_right N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hHfive : P.N^(9/8 : ℝ) ≤ (H : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 5
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hHfour : P.N^(9/10 : ℝ) ≤ (H : ℝ)^4 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 4
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hscale : 8*(n : ℝ) ≤ (H : ℝ)^5 := by
    calc
      _ ≤ 16*P.N := by linarith only [hnb.2]
      _ ≤ P.N^(1/8 : ℝ)*P.N := mul_le_mul_of_nonneg_right hc₀ hNp.le
      _ = P.N^(9/8 : ℝ) := by
        nth_rw 2 [← Real.rpow_one P.N]
        rw [← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := hHfive
  have hheight : |t-u| ≤ Real.pi*(n : ℝ)^6 := by
    have ht' := P.ordinates_in_interval t ht
    have hu' := P.ordinates_in_interval u hu
    have hgap : |t-u| ≤ P.T := abs_le.2 ⟨by linarith [P.interval_length],
      by linarith [P.interval_length]⟩
    have hN6 : P.N^(27/5 : ℝ) ≤ P.N^6 := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
        P.one_lt_N.le (by norm_num : (27/5 : ℝ) ≤ (6 : ℕ))
    have hn6 := pow_le_pow_left₀ hNp.le hnb.1 6
    have hpi : (n : ℝ)^6 ≤ Real.pi*(n : ℝ)^6 := by
      have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
        (show 0 ≤ (n : ℝ)^6 by positivity)
      simpa only [one_mul] using hh
    exact hgap.trans (hT.trans (hN6.trans (hn6.trans hpi)))
  apply Set.disjoint_left.mpr
  intro α hαt hαu
  have hspace := logarithmicTaylorCell_commonCentre_spacing hnp hHone hscale hheight
    (show (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u n).Nonempty from ⟨α,hαt,hαu⟩)
  have hbound : 16*Real.pi*(n : ℝ)^4/(H : ℝ)^4 ≤ P.N^(10/3 : ℝ) := by
    calc
      _ ≤ 16*Real.pi*(2*P.N)^4/(H : ℝ)^4 := by gcongr; exact hnb.2
      _ ≤ 16*Real.pi*(2*P.N)^4/P.N^(9/10 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNp _) hHfour
      _ = (256*Real.pi)*(P.N^4/P.N^(9/10 : ℝ)) := by ring
      _ = (256*Real.pi)*P.N^(31/10 : ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_sub hNp]
        norm_num
      _ ≤ P.N^(7/30 : ℝ)*P.N^(31/10 : ℝ) :=
        mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  exact (not_le_of_gt hfar) (hspace.trans hbound)

#print axioms logarithmicTaylorCell_actual_far_disjoint

theorem logarithmicTaylorCell_mixed_coordinate {H : ℕ} {t u n m : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty)
    (j : Fin 6) :
    GafniTao.heathBrownDistanceToInteger
      ((-1 : ℝ)^((j : ℕ)+1)*t/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*n^((j : ℕ)+1)) -
       (-1 : ℝ)^((j : ℕ)+1)*u/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*m^((j : ℕ)+1))) ≤
      2/((H : ℝ)^((j : ℕ)+1)) := by
  obtain ⟨α,ht,hu⟩ := hover
  have htj := ht j (Set.mem_univ j)
  have huj := hu j (Set.mem_univ j)
  have hdist := dist_triangle
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n j) (α j)
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase u) m j)
  unfold GafniTao.heathBrownCoefficientCenter at hdist
  rw [logarithmicTaylorPhase_coordinate _ t hn,logarithmicTaylorPhase_coordinate _ u hm,
    GafniTao.unitAddCircle_dist_real_coe] at hdist
  change dist (α j) _ ≤ _ at htj huj
  rw [dist_comm (α j)] at htj
  change dist _ _ ≤ ((H : ℝ)^((j : ℕ)+1))⁻¹ at htj huj
  unfold GafniTao.heathBrownCoefficientCenter at htj huj
  rw [logarithmicTaylorPhase_coordinate _ t hn] at htj
  rw [logarithmicTaylorPhase_coordinate _ u hm] at huj
  simpa only [div_eq_mul_inv] using
    hdist.trans (show _ ≤ 2*((H : ℝ)^((j : ℕ)+1))⁻¹ by linarith only [htj,huj])

#print axioms logarithmicTaylorCell_mixed_coordinate

private theorem reciprocal_fifth_sixth {x y B : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxB : x ≤ B) (hyB : y ≤ B) :
    |1/x^5-1/y^5| ≤ B*|1/x^6-1/y^6| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx hyB hxB (le_of_not_ge hxy)
  have h5 : x^5 ≤ y^5 := pow_le_pow_left₀ hx.le hxy 5
  have h6 : x^6 ≤ y^6 := pow_le_pow_left₀ hx.le hxy 6
  rw [abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h5)),
    abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h6))]
  have hB : 0 < B := hx.trans_le hxB
  have ha : x*(y^5-x^5) ≤ y^6-x^6 := by
    nlinarith only [mul_nonneg (show 0 ≤ y^5 by positivity) (sub_nonneg.mpr hxy)]
  have hb := mul_le_mul_of_nonneg_left hyB (show 0 ≤ x*(y^5-x^5) by positivity)
  have hc := mul_le_mul_of_nonneg_left ha hB.le
  apply (le_of_mul_le_mul_left _ (show 0 < x^6*y^6 by positivity))
  field_simp
  nlinarith only [hb,hc]

#print axioms reciprocal_fifth_sixth

private theorem reciprocal_fifth_integer_gap {N : ℝ} (hN : 0 < N) {n m : ℕ}
    (hn : N ≤ (n : ℝ)) (hm : N ≤ (m : ℝ))
    (hn' : (n : ℝ) ≤ 2*N) (hm' : (m : ℝ) ≤ 2*N) (hne : n ≠ m) :
    1/(1024*N^6) ≤ |1/(n : ℝ)^5-1/(m : ℝ)^5| := by
  wlog hnm : n < m generalizing n m
  · simpa only [abs_sub_comm] using this hm hn hm' hn' hne.symm (by omega)
  have hnp : 0 < (n : ℝ) := hN.trans_le hn
  have hmp : 0 < (m : ℝ) := hN.trans_le hm
  have hstep : (n : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast hnm
  have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ)+1 by positivity) hstep 5
  have hnum : N^4 ≤ (m : ℝ)^5-(n : ℝ)^5 := by
    have hn4 := pow_le_pow_left₀ hN.le hn 4
    have hp3 : 0 ≤ (n : ℝ)^3 := by positivity
    have hp2 : 0 ≤ (n : ℝ)^2 := by positivity
    nlinarith only [hpow,hn4,hp3,hp2,hnp]
  have hden : (n : ℝ)^5*(m : ℝ)^5 ≤ 1024*N^10 := by
    calc
      _ ≤ (2*N)^5*(2*N)^5 := mul_le_mul
        (pow_le_pow_left₀ hnp.le hn' 5) (pow_le_pow_left₀ hmp.le hm' 5)
        (by positivity) (by positivity)
      _ = _ := by ring
  have horder : (n : ℝ)^5 ≤ (m : ℝ)^5 := by nlinarith only [hnum,pow_nonneg hN.le 4]
  rw [abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) horder))]
  apply (le_of_mul_le_mul_left _
    (show 0 < 1024*N^6*(n : ℝ)^5*(m : ℝ)^5 by positivity))
  field_simp
  have hh := mul_le_mul_of_nonneg_left hnum (show 0 ≤ 1024*N^6 by positivity)
  nlinarith only [hden,hh]

#print axioms reciprocal_fifth_integer_gap

theorem logarithmicTaylorCell_mixed_centres_eq
    {H n m : ℕ} {N T t u : ℝ} (hN : 1 ≤ N) (hT : 0 < T)
    (hn : N ≤ (n : ℝ)) (hm : N ≤ (m : ℝ))
    (hn' : (n : ℝ) ≤ 2*N) (hm' : (m : ℝ) ≤ 2*N)
    (ht : T ≤ t) (hu : T ≤ u) (ht' : t ≤ 2*T) (hu' : u ≤ 2*T)
    (hH : 0 < H) (hheight : 4*T/N^6 ≤ 6*Real.pi)
    (hwrap : 48*Real.pi*N/(H : ℝ)^6+3*T/(8192*N^6) ≤ 5*Real.pi)
    (hprecision : 20*Real.pi/(H : ℝ)^5 ≤ T/(8192*N^6))
    (hgap : |t-u| ≤ T/(8192*N))
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty) :
    n = m := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hnp : 0 < (n : ℝ) := hNp.trans_le hn
  have hmp : 0 < (m : ℝ) := hNp.trans_le hm
  have htp : 0 < t := hT.trans_le ht
  have hup : 0 < u := hT.trans_le hu
  have hHp : 0 < (H : ℝ) := by exact_mod_cast hH
  have h6 := logarithmicTaylorCell_mixed_coordinate hnp hmp hover ⟨5,by decide⟩
  have h5 := logarithmicTaylorCell_mixed_coordinate hnp hmp hover ⟨4,by decide⟩
  norm_num at h6 h5
  have he6 : t/(2*Real.pi*6*(n : ℝ)^6)-u/(2*Real.pi*6*(m : ℝ)^6) =
      (t/(n : ℝ)^6-u/(m : ℝ)^6)/(12*Real.pi) := by ring
  have he5 : -t/(2*Real.pi*5*(n : ℝ)^5)- -u/(2*Real.pi*5*(m : ℝ)^5) =
      -((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)) := by ring
  rw [he6] at h6
  rw [he5,GafniTao.heathBrownDistanceToInteger_neg] at h5
  have h6size : |t/(n : ℝ)^6-u/(m : ℝ)^6| ≤ 4*T/N^6 := by
    calc
      _ ≤ |t/(n : ℝ)^6|+|u/(m : ℝ)^6| := abs_sub _ _
      _ = t/(n : ℝ)^6+u/(m : ℝ)^6 := by rw [abs_of_pos (by positivity),abs_of_pos (by positivity)]
      _ ≤ 2*T/N^6+2*T/N^6 := add_le_add
        (div_le_div₀ (by positivity) ht' (by positivity) (pow_le_pow_left₀ hNp.le hn 6))
        (div_le_div₀ (by positivity) hu' (by positivity) (pow_le_pow_left₀ hNp.le hm 6))
      _ = _ := by ring
  have h6half : |(t/(n : ℝ)^6-u/(m : ℝ)^6)/(12*Real.pi)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [h6size,hheight]
  have h6abs := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h6 h6half
  rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi)] at h6abs
  have h6raw : |t/(n : ℝ)^6-u/(m : ℝ)^6| ≤ 24*Real.pi/(H : ℝ)^6 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 12*Real.pi)).mp h6abs
    convert hh using 1
    ring
  have hfixed6 : t*|1/(n : ℝ)^6-1/(m : ℝ)^6| ≤
      24*Real.pi/(H : ℝ)^6+|t-u|/(m : ℝ)^6 := by
    calc
      _ = |t/(n : ℝ)^6-t/(m : ℝ)^6| := by
        rw [show t/(n : ℝ)^6-t/(m : ℝ)^6 = t*(1/(n : ℝ)^6-1/(m : ℝ)^6) by ring,
          abs_mul,abs_of_pos htp]
      _ ≤ |t/(n : ℝ)^6-u/(m : ℝ)^6|+|(u-t)/(m : ℝ)^6| := by
        rw [show t/(n : ℝ)^6-t/(m : ℝ)^6 =
          (t/(n : ℝ)^6-u/(m : ℝ)^6)+(u-t)/(m : ℝ)^6 by ring]
        exact abs_add_le _ _
      _ ≤ _ := by rw [abs_div,abs_of_pos (by positivity : 0 < (m : ℝ)^6),abs_sub_comm u t]; gcongr
  have h5size : |t/(n : ℝ)^5-u/(m : ℝ)^5| ≤
      48*Real.pi*N/(H : ℝ)^6+3*T/(8192*N^6) := by
    have hrec := reciprocal_fifth_sixth hnp hmp hn' hm'
    have hf : t*|1/(n : ℝ)^5-1/(m : ℝ)^5| ≤
        2*N*(24*Real.pi/(H : ℝ)^6+|t-u|/(m : ℝ)^6) := by
      calc
        _ ≤ t*(2*N*|1/(n : ℝ)^6-1/(m : ℝ)^6|) := mul_le_mul_of_nonneg_left hrec htp.le
        _ = 2*N*(t*|1/(n : ℝ)^6-1/(m : ℝ)^6|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfixed6 (by positivity)
    calc
      _ ≤ t*|1/(n : ℝ)^5-1/(m : ℝ)^5|+|t-u|/(m : ℝ)^5 := by
        have hh := abs_add_le (t*(1/(n : ℝ)^5-1/(m : ℝ)^5)) ((t-u)/(m : ℝ)^5)
        rw [abs_mul,abs_of_pos htp,abs_div,abs_of_pos (by positivity : 0 < (m : ℝ)^5)] at hh
        rw [show t*(1/(n : ℝ)^5-1/(m : ℝ)^5)+(t-u)/(m : ℝ)^5 =
          t/(n : ℝ)^5-u/(m : ℝ)^5 by ring] at hh
        exact hh
      _ ≤ 2*N*(24*Real.pi/(H : ℝ)^6+(T/(8192*N))/N^6)+(T/(8192*N))/N^5 := by
        apply add_le_add (hf.trans _) _
        · gcongr
        · exact div_le_div₀ (by positivity) hgap (by positivity) (pow_le_pow_left₀ hNp.le hm 5)
      _ = _ := by field_simp; ring
  have h5half : |(t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 10*Real.pi)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [h5size,hwrap]
  have h5abs := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h5 h5half
  rw [abs_div,abs_of_pos (by positivity : 0 < 10*Real.pi)] at h5abs
  have h5raw : |t/(n : ℝ)^5-u/(m : ℝ)^5| ≤ 20*Real.pi/(H : ℝ)^5 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 10*Real.pi)).mp h5abs
    convert hh using 1
    ring
  by_contra hne
  have hsep := mul_le_mul_of_nonneg_left
    (reciprocal_fifth_integer_gap hNp hn hm hn' hm' hne) htp.le
  have hfixed5 : t*|1/(n : ℝ)^5-1/(m : ℝ)^5| ≤
      20*Real.pi/(H : ℝ)^5+|t-u|/(m : ℝ)^5 := by
    calc
      _ = |t/(n : ℝ)^5-t/(m : ℝ)^5| := by
        rw [show t/(n : ℝ)^5-t/(m : ℝ)^5 = t*(1/(n : ℝ)^5-1/(m : ℝ)^5) by ring,
          abs_mul,abs_of_pos htp]
      _ ≤ |t/(n : ℝ)^5-u/(m : ℝ)^5|+|(u-t)/(m : ℝ)^5| := by
        rw [show t/(n : ℝ)^5-t/(m : ℝ)^5 =
          (t/(n : ℝ)^5-u/(m : ℝ)^5)+(u-t)/(m : ℝ)^5 by ring]
        exact abs_add_le _ _
      _ ≤ _ := by rw [abs_div,abs_of_pos (by positivity : 0 < (m : ℝ)^5),abs_sub_comm u t]; gcongr
  have hsmall : |t-u|/(m : ℝ)^5 ≤ T/(8192*N^6) := by
    calc
      _ ≤ (T/(8192*N))/N^5 := div_le_div₀ (by positivity) hgap (by positivity)
        (pow_le_pow_left₀ hNp.le hm 5)
      _ = _ := by field_simp
  have hlow' : T/(1024*N^6) ≤ t*|1/(n : ℝ)^5-1/(m : ℝ)^5| := by
    calc
      _ = T*(1/(1024*N^6)) := by ring
      _ ≤ t*(1/(1024*N^6)) := mul_le_mul_of_nonneg_right ht (by positivity)
      _ ≤ _ := hsep
  have hpos : 0 < T/N^6 := by positivity
  have ha : T/(1024*N^6) = (T/N^6)/1024 := by ring
  have hb : T/(8192*N^6) = (T/N^6)/8192 := by ring
  rw [ha] at hlow'
  rw [hb] at hprecision hsmall
  linarith only [hlow',hfixed5,hprecision,hsmall,hpos]

#print axioms logarithmicTaylorCell_mixed_centres_eq

theorem logarithmicTaylorCell_medium_far_disjoint :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      P.N^(10/3 : ℝ) < |t-u| → |t-u| ≤ P.T/(8192*P.N) →
      ∀ n ∈ P.indices, ∀ m ∈ P.indices,
      Disjoint (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n)
        (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m) := by
  obtain ⟨C₀,hC₀,hsame⟩ := logarithmicTaylorCell_actual_far_disjoint
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (48*Real.pi) (by positivity) 0
      (η := 7/20) (by norm_num))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (163840*Real.pi) (by positivity) 0
      (η := 1/8) (by norm_num))
  refine ⟨max C₀ (max N₀ N₁),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT t ht u hu hfar hgap n hn m hm
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hHlow : P.N^(9/40 : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
  have hHone : 1 ≤ H := by
    exact_mod_cast (Real.one_le_rpow P.one_lt_N.le (by norm_num : (0 : ℝ) ≤ 9/40)).trans hHlow
  have hHp : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hHfive : P.N^(9/8 : ℝ) ≤ (H : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 5
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hHsix : P.N^(27/20 : ℝ) ≤ (H : ℝ)^6 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 6
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hc₀ : 48*Real.pi ≤ P.N^(7/20 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N
      ((le_max_left N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hc₁ : 163840*Real.pi ≤ P.N^(1/8 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N
      ((le_max_right N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hT6 : P.T ≤ P.N^6 := by
    apply hT.trans
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (27/5 : ℝ) ≤ (6 : ℕ))
  have hheight : 4*P.T/P.N^6 ≤ 6*Real.pi := by
    have hh : 4*P.T/P.N^6 ≤ 4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hT6])
    linarith [Real.pi_gt_three]
  have hwrap : 48*Real.pi*P.N/(H : ℝ)^6+3*P.T/(8192*P.N^6) ≤ 5*Real.pi := by
    have ha : 48*Real.pi*P.N/(H : ℝ)^6 ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      calc
        _ ≤ P.N^(7/20 : ℝ)*P.N := mul_le_mul_of_nonneg_right hc₀ hNp.le
        _ = P.N^(27/20 : ℝ) := by
          nth_rw 2 [← Real.rpow_one P.N]
          rw [← Real.rpow_add hNp]
          norm_num
        _ ≤ _ := hHsix
    have hb : 3*P.T/(8192*P.N^6) ≤ 3/8192 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [hT6]
    linarith [Real.pi_gt_three]
  have hprecision : 20*Real.pi/(H : ℝ)^5 ≤ P.T/(8192*P.N^6) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ = (163840*Real.pi)*P.N^6 := by ring
      _ ≤ P.N^(1/8 : ℝ)*P.N^6 := mul_le_mul_of_nonneg_right hc₁ (by positivity)
      _ = P.N^5*P.N^(9/8 : ℝ) := by
        rw [← Real.rpow_natCast P.N 6,← Real.rpow_natCast P.N 5,
          ← Real.rpow_add hNp,← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := mul_le_mul hTlow hHfive (Real.rpow_nonneg hNp.le _) P.T_pos.le
  apply Set.disjoint_left.mpr
  intro α hαt hαu
  have heq := logarithmicTaylorCell_mixed_centres_eq P.one_lt_N.le P.T_pos
    hnb.1 hmb.1 hnb.2 hmb.2 ht'.1 hu'.1 ht'.2 hu'.2
    (show 0 < H by omega) hheight hwrap hprecision hgap
    (show (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty from ⟨α,hαt,hαu⟩)
  subst m
  exact (Set.disjoint_left.mp
    (hsame P ((le_max_left _ _).trans hPN) hT t ht u hu hfar n hn)) hαt hαu

#print axioms logarithmicTaylorCell_medium_far_disjoint

def logarithmicTaylorSixthRatio (t u : ℝ) : ℝ := (u/t)^(1/6 : ℝ)

def logarithmicTaylorFifthLabel (t u n m : ℝ) : ℤ :=
  round ((t/n^5-u/m^5)/(10*Real.pi))

theorem logarithmicTaylorSixthRatio_bounds {T t u : ℝ} (hT : 0 < T)
    (ht : T ≤ t) (hu : T ≤ u) (ht' : t ≤ 2*T) (hu' : u ≤ 2*T) :
    0 < logarithmicTaylorSixthRatio t u ∧
    1/2 ≤ logarithmicTaylorSixthRatio t u ∧ logarithmicTaylorSixthRatio t u ≤ 2 ∧
    t*(logarithmicTaylorSixthRatio t u)^6 = u := by
  have htp : 0 < t := hT.trans_le ht
  have hup : 0 < u := hT.trans_le hu
  have hratio : 0 < u/t := by positivity
  have hlo : 1/2 ≤ u/t := (le_div_iff₀ htp).mpr (by linarith only [hu,ht'])
  have hhi : u/t ≤ 2 := (div_le_iff₀ htp).mpr (by linarith only [ht,hu'])
  have hr : 0 < logarithmicTaylorSixthRatio t u := Real.rpow_pos_of_pos hratio _
  have hpow : (logarithmicTaylorSixthRatio t u)^6 = u/t := by
    unfold logarithmicTaylorSixthRatio
    rw [← Real.rpow_mul_natCast hratio.le]
    norm_num
  refine ⟨hr,?_,?_,?_⟩
  · by_contra! hh
    have hh' := pow_lt_pow_left₀ hh hr.le (by decide : 6 ≠ 0)
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hlo,hh']
  · by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by norm_num : (0 : ℝ) ≤ 2) (by decide : 6 ≠ 0)
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hhi,hh']
  · rw [hpow]
    field_simp

#print axioms logarithmicTaylorSixthRatio_bounds

theorem logarithmicTaylorCell_sixth_raw (P : ZetaLargeValuePattern)
    (hT : P.T ≤ P.N^6) {H n m : ℕ} {t u : ℝ}
    (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
    (hn : n ∈ P.indices) (hm : m ∈ P.indices)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty) :
    |t/(n : ℝ)^6-u/(m : ℝ)^6| ≤ 24*Real.pi/(H : ℝ)^6 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have htp := P.T_pos.trans_le ht'.1
  have hup := P.T_pos.trans_le hu'.1
  have h6 := logarithmicTaylorCell_mixed_coordinate hnp hmp hover ⟨5,by decide⟩
  norm_num at h6
  have he6 : t/(2*Real.pi*6*(n : ℝ)^6)-u/(2*Real.pi*6*(m : ℝ)^6) =
      (t/(n : ℝ)^6-u/(m : ℝ)^6)/(12*Real.pi) := by ring
  rw [he6] at h6
  have hsize : |t/(n : ℝ)^6-u/(m : ℝ)^6| ≤ 4 := by
    calc
      _ ≤ |t/(n : ℝ)^6|+|u/(m : ℝ)^6| := abs_sub _ _
      _ = t/(n : ℝ)^6+u/(m : ℝ)^6 := by
        rw [abs_of_pos (by positivity),abs_of_pos (by positivity)]
      _ ≤ 2*P.T/P.N^6+2*P.T/P.N^6 := add_le_add
        (div_le_div₀ (by linarith [P.T_pos]) ht'.2 (by positivity) (pow_le_pow_left₀ hNp.le hnb.1 6))
        (div_le_div₀ (by linarith [P.T_pos]) hu'.2 (by positivity) (pow_le_pow_left₀ hNp.le hmb.1 6))
      _ = 4*P.T/P.N^6 := by ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith only [hT])
  have hhalf : |(t/(n : ℝ)^6-u/(m : ℝ)^6)/(12*Real.pi)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hh := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h6 hhalf
  rw [abs_div,abs_of_pos (by positivity : 0 < 12*Real.pi)] at hh
  have hh' := (div_le_iff₀ (by positivity : 0 < 12*Real.pi)).mp hh
  convert hh' using 1
  ring

#print axioms logarithmicTaylorCell_sixth_raw

theorem logarithmicTaylorCell_fifth_projection (P : ZetaLargeValuePattern)
    (hT : P.T ≤ P.N^6) {H n m : ℕ} {t u : ℝ}
    (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
    (hn : n ∈ P.indices) (hm : m ∈ P.indices)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty) :
    |t*(1-logarithmicTaylorSixthRatio t u)/(n : ℝ)^5 -
      10*Real.pi*(logarithmicTaylorFifthLabel t u n m : ℝ)| ≤
      96*Real.pi*P.N/(H : ℝ)^6+20*Real.pi/(H : ℝ)^5 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have htp := P.T_pos.trans_le ht'.1
  have hup := P.T_pos.trans_le hu'.1
  obtain ⟨hrp,hrlo,hrhi,hrpow⟩ :=
    logarithmicTaylorSixthRatio_bounds P.T_pos ht'.1 hu'.1 ht'.2 hu'.2
  let r := logarithmicTaylorSixthRatio t u
  have hrnp : 0 < r*(n : ℝ) := by dsimp only [r]; positivity
  have hrnhi : r*(n : ℝ) ≤ 4*P.N := by
    have hh := mul_le_mul hrhi hnb.2 hnp.le (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [r]
    linarith only [hh]
  have h6 := logarithmicTaylorCell_sixth_raw P hT ht hu hn hm hover
  have he6 : u/(r*(n : ℝ))^6 = t/(n : ℝ)^6 := by
    rw [← hrpow]
    dsimp only [r]
    field_simp
  have he5 : t*(1-r)/(n : ℝ)^5 = t/(n : ℝ)^5-u/(r*(n : ℝ))^5 := by
    rw [← hrpow]
    dsimp only [r]
    field_simp
  have hprojection : |t*(1-r)/(n : ℝ)^5-(t/(n : ℝ)^5-u/(m : ℝ)^5)| ≤
      96*Real.pi*P.N/(H : ℝ)^6 := by
    have hrec := reciprocal_fifth_sixth hmp hrnp
      (hmb.2.trans (by linarith only [hNp] : 2*P.N ≤ 4*P.N)) hrnhi
    calc
      _ = |u*(1/(m : ℝ)^5-1/(r*(n : ℝ))^5)| := by rw [he5]; congr 1; ring
      _ = u*|1/(m : ℝ)^5-1/(r*(n : ℝ))^5| := by rw [abs_mul,abs_of_pos hup]
      _ ≤ u*(4*P.N*|1/(m : ℝ)^6-1/(r*(n : ℝ))^6|) :=
        mul_le_mul_of_nonneg_left hrec hup.le
      _ = 4*P.N*|u/(m : ℝ)^6-u/(r*(n : ℝ))^6| := by
        rw [show u/(m : ℝ)^6-u/(r*(n : ℝ))^6 = u*(1/(m : ℝ)^6-1/(r*(n : ℝ))^6) by ring,
          abs_mul,abs_of_pos hup]
        ring
      _ = 4*P.N*|t/(n : ℝ)^6-u/(m : ℝ)^6| := by rw [he6,abs_sub_comm]
      _ ≤ 4*P.N*(24*Real.pi/(H : ℝ)^6) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = _ := by ring
  have h5 := logarithmicTaylorCell_mixed_coordinate hnp hmp hover ⟨4,by decide⟩
  norm_num at h5
  have he : -t/(2*Real.pi*5*(n : ℝ)^5)- -u/(2*Real.pi*5*(m : ℝ)^5) =
      -((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)) := by ring
  rw [he,GafniTao.heathBrownDistanceToInteger_neg] at h5
  unfold GafniTao.heathBrownDistanceToInteger at h5
  have hlabel : |(t/(n : ℝ)^5-u/(m : ℝ)^5)-10*Real.pi*(logarithmicTaylorFifthLabel t u n m : ℝ)| ≤
      20*Real.pi/(H : ℝ)^5 := by
    have hh := mul_le_mul_of_nonneg_left h5 (show 0 ≤ 10*Real.pi by positivity)
    unfold logarithmicTaylorFifthLabel
    calc
      _ = 10*Real.pi*|(t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)-
          (round ((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)) : ℝ)| := by
        rw [show (t/(n : ℝ)^5-u/(m : ℝ)^5)-
            10*Real.pi*(round ((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)) : ℝ) =
            10*Real.pi*((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)-
              (round ((t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)) : ℝ)) by field_simp,
          abs_mul,abs_of_pos (show 0 < 10*Real.pi by positivity)]
      _ ≤ _ := by convert hh using 1; ring
  exact (abs_sub_le _ (t/(n : ℝ)^5-u/(m : ℝ)^5) _).trans (add_le_add hprojection hlabel)

#print axioms logarithmicTaylorCell_fifth_projection

private theorem reciprocal_fifth_real_gap {N x y : ℝ} (hN : 0 < N)
    (hx : N ≤ x) (hy : N ≤ y) (hx' : x ≤ 2*N) (hy' : y ≤ 2*N) :
    |x-y|/(1024*N^6) ≤ |1/x^5-1/y^5| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx hy' hx' (le_of_not_ge hxy)
  have hxp : 0 < x := hN.trans_le hx
  have hyp : 0 < y := hN.trans_le hy
  have h4 := pow_le_pow_left₀ hxp.le hxy 4
  have hN4 := pow_le_pow_left₀ hN.le hx 4
  have hnum : N^4*(y-x) ≤ y^5-x^5 := by
    have ha := mul_nonneg hyp.le (sub_nonneg.mpr h4)
    have hb := mul_le_mul_of_nonneg_right hN4 (sub_nonneg.mpr hxy)
    nlinarith only [ha,hb]
  have hden : x^5*y^5 ≤ 1024*N^10 := by
    calc
      _ ≤ (2*N)^5*(2*N)^5 := mul_le_mul
        (pow_le_pow_left₀ hxp.le hx' 5) (pow_le_pow_left₀ hyp.le hy' 5)
        (by positivity) (by positivity)
      _ = _ := by ring
  have h5 := pow_le_pow_left₀ hxp.le hxy 5
  rw [abs_sub_comm x y,abs_of_nonneg (sub_nonneg.mpr hxy),
    abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h5))]
  apply (le_of_mul_le_mul_left _ (show 0 < 1024*N^6*x^5*y^5 by positivity))
  field_simp
  have ha := mul_le_mul_of_nonneg_right hden (sub_nonneg.mpr hxy)
  have hb := mul_le_mul_of_nonneg_left hnum (show 0 ≤ 1024*N^6 by positivity)
  nlinarith only [ha,hb]

#print axioms reciprocal_fifth_real_gap

private theorem fifth_curve_label_diameter {N D E q x y : ℝ}
    (hN : 0 < N) (hq : 0 < |q|) (hsmall : E ≤ Real.pi*|q|)
    (hx : N ≤ x) (hy : N ≤ y) (hx' : x ≤ 2*N) (hy' : y ≤ 2*N)
    (hlabelx : |D/x^5-10*Real.pi*q| ≤ E)
    (hlabely : |D/y^5-10*Real.pi*q| ≤ E) :
    |x-y| ≤ 2048*N*E/|q| := by
  have hxp : 0 < x := hN.trans_le hx
  have hnorm : 10*Real.pi*|q| ≤ E+|D|/x^5 := by
    have hh := abs_sub_le (10*Real.pi*q) (D/x^5) 0
    simp only [sub_zero] at hh
    rw [abs_mul,abs_of_pos (by positivity : 0 < 10*Real.pi),
      abs_sub_comm (10*Real.pi*q),abs_div,abs_of_pos (by positivity : 0 < x^5)] at hh
    linarith only [hh,hlabelx]
  have hratio : |q| ≤ |D|/x^5 := by
    have hpi := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 9*Real.pi by linarith [Real.pi_gt_three]) hq.le
    nlinarith only [hnorm,hsmall,hpi]
  have hlower : |q| * N^5 ≤ |D| := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hx 5) hq.le).trans
      ((le_div_iff₀ (by positivity)).mp hratio)
  have hdiff : |D| * |1/x^5-1/y^5| ≤ 2*E := by
    calc
      _ = |D/x^5-D/y^5| := by
        rw [show D/x^5-D/y^5 = D*(1/x^5-1/y^5) by ring,abs_mul]
      _ ≤ |D/x^5-10*Real.pi*q|+|10*Real.pi*q-D/y^5| := abs_sub_le _ _ _
      _ ≤ _ := by rw [abs_sub_comm (10*Real.pi*q)]; linarith only [hlabelx,hlabely]
  have hgap := mul_le_mul_of_nonneg_left
    (reciprocal_fifth_real_gap hN hx hy hx' hy') (abs_nonneg D)
  have hraw : |D| * |x-y| ≤ 2048*N^6*E := by
    have hh := hgap.trans hdiff
    rw [← mul_div_assoc] at hh
    have hh' := (div_le_iff₀ (by positivity : 0 < 1024*N^6)).mp hh
    nlinarith only [hh']
  have hlift := mul_le_mul_of_nonneg_right hlower (abs_nonneg (x-y))
  have hh : N^5*(|q| * |x-y|) ≤ N^5*(2048*N*E) := by
    nlinarith only [hlift,hraw]
  have hcancel := (mul_le_mul_iff_right₀ (show 0 < N^5 by positivity)).mp hh
  apply (le_div_iff₀ hq).mpr
  nlinarith only [hcancel]

#print axioms fifth_curve_label_diameter

theorem logarithmicTaylorCell_nonzero_label_diameter :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates, ∀ q : ℤ, q ≠ 0 →
      ∀ n ∈ P.indices, ∀ m ∈ P.indices, ∀ n' ∈ P.indices, ∀ m' ∈ P.indices,
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m).Nonempty →
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n' ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m').Nonempty →
      logarithmicTaylorFifthLabel t u n m = q → logarithmicTaylorFifthLabel t u n' m' = q →
      |(n : ℝ)-(n' : ℝ)| ≤ P.N^(7/10 : ℝ)/|(q : ℝ)| := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (393216*Real.pi) (by positivity) 0
      (η := 1/20) (by norm_num))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (81920*Real.pi) (by positivity) 0
      (η := 33/40) (by norm_num))
  refine ⟨max 1 (max N₀ N₁),le_max_left _ _,?_⟩
  intro P hPN hT t ht u hu q hq n hn m hm n' hn' m' hm' hover hover' hlabel hlabel'
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let E := 96*Real.pi*P.N/(H : ℝ)^6+20*Real.pi/(H : ℝ)^5
  have hHlow : P.N^(9/40 : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
  have hHp : 0 < (H : ℝ) := (Real.rpow_pos_of_pos hNp _).trans_le hHlow
  have hHfive : P.N^(9/8 : ℝ) ≤ (H : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 5
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hHsix : P.N^(27/20 : ℝ) ≤ (H : ℝ)^6 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 6
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hc₀ : 393216*Real.pi ≤ P.N^(1/20 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N
      ((le_max_left N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hc₁ : 81920*Real.pi ≤ P.N^(33/40 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N
      ((le_max_right N₀ N₁).trans ((le_max_right _ _).trans hPN))
  have hfirst : 196608*Real.pi*P.N^2/(H : ℝ)^6 ≤ P.N^(7/10 : ℝ)/2 := by
    calc
      _ ≤ 196608*Real.pi*P.N^2/P.N^(27/20 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNp _) hHsix
      _ = (393216*Real.pi)*P.N^(13/20 : ℝ)/2 := by
        rw [show 196608*Real.pi*P.N^2/P.N^(27/20 : ℝ) =
          (393216*Real.pi)/2*(P.N^2/P.N^(27/20 : ℝ)) by ring,
          ← Real.rpow_natCast P.N 2,← Real.rpow_sub hNp]
        norm_num
        ring
      _ ≤ P.N^(1/20 : ℝ)*P.N^(13/20 : ℝ)/2 := by gcongr
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hsecond : 40960*Real.pi*P.N/(H : ℝ)^5 ≤ P.N^(7/10 : ℝ)/2 := by
    calc
      _ ≤ 40960*Real.pi*P.N/P.N^(9/8 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNp _) hHfive
      _ = (81920*Real.pi)*P.N^(-1/8 : ℝ)/2 := by
        rw [show 40960*Real.pi*P.N/P.N^(9/8 : ℝ) =
          (81920*Real.pi)/2*(P.N/P.N^(9/8 : ℝ)) by ring]
        nth_rw 1 [← Real.rpow_one P.N]
        rw [← Real.rpow_sub hNp]
        norm_num
        ring
      _ ≤ P.N^(33/40 : ℝ)*P.N^(-1/8 : ℝ)/2 := by gcongr
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hscale : 2048*P.N*E ≤ P.N^(7/10 : ℝ) := by
    calc
      _ = 196608*Real.pi*P.N^2/(H : ℝ)^6+40960*Real.pi*P.N/(H : ℝ)^5 := by
        dsimp only [E]
        ring
      _ ≤ P.N^(7/10 : ℝ)/2+P.N^(7/10 : ℝ)/2 := add_le_add hfirst hsecond
      _ = _ := by ring
  have hE : E ≤ 1 := by
    have hp : P.N^(7/10 : ℝ) ≤ P.N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        P.one_lt_N.le (by norm_num : (7/10 : ℝ) ≤ 1)
    have hh : P.N*(2048*E) ≤ P.N*1 := by nlinarith only [hscale,hp]
    have hh' := (mul_le_mul_iff_right₀ hNp).mp hh
    linarith only [hh']
  have hqone : (1 : ℝ) ≤ |(q : ℝ)| := by
    have hh : (1 : ℤ) ≤ |q| := by have hp := abs_pos.mpr hq; omega
    exact_mod_cast hh
  have hsmall : E ≤ Real.pi*|(q : ℝ)| := by
    have hh := mul_le_mul_of_nonneg_left hqone Real.pi_pos.le
    linarith [Real.pi_gt_three]
  have hx := logarithmicTaylorCell_fifth_projection P hT ht hu hn hm hover
  have hy := logarithmicTaylorCell_fifth_projection P hT ht hu hn' hm' hover'
  rw [hlabel] at hx
  rw [hlabel'] at hy
  have hnb := (P.mem_indices_iff n).mp hn
  have hnb' := (P.mem_indices_iff n').mp hn'
  have hh := fifth_curve_label_diameter hNp (zero_lt_one.trans_le hqone) hsmall
    hnb.1 hnb'.1 hnb.2 hnb'.2 hx hy
  exact hh.trans (div_le_div_of_nonneg_right hscale (abs_nonneg _))

#print axioms logarithmicTaylorCell_nonzero_label_diameter

theorem logarithmicTaylorCell_fifth_label_error {H : ℕ} {t u n m : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty) :
    |t/n^5-u/m^5-10*Real.pi*(logarithmicTaylorFifthLabel t u n m : ℝ)| ≤
      20*Real.pi/(H : ℝ)^5 := by
  have hh := logarithmicTaylorCell_mixed_coordinate hn hm hover ⟨4,by decide⟩
  norm_num at hh
  have he : -t/(2*Real.pi*5*n^5)- -u/(2*Real.pi*5*m^5) =
      -((t/n^5-u/m^5)/(10*Real.pi)) := by ring
  rw [he,GafniTao.heathBrownDistanceToInteger_neg] at hh
  unfold GafniTao.heathBrownDistanceToInteger at hh
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 10*Real.pi by positivity)
  unfold logarithmicTaylorFifthLabel
  calc
    _ = 10*Real.pi*|(t/n^5-u/m^5)/(10*Real.pi)-
        (round ((t/n^5-u/m^5)/(10*Real.pi)) : ℝ)| := by
      rw [show t/n^5-u/m^5-10*Real.pi*(round ((t/n^5-u/m^5)/(10*Real.pi)) : ℝ) =
        10*Real.pi*((t/n^5-u/m^5)/(10*Real.pi)-
          (round ((t/n^5-u/m^5)/(10*Real.pi)) : ℝ)) by field_simp,
        abs_mul,abs_of_pos (show 0 < 10*Real.pi by positivity)]
    _ ≤ _ := by convert hmul using 1; ring

#print axioms logarithmicTaylorCell_fifth_label_error

theorem logarithmicTaylorCell_same_label_unique_second :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.N^5 ≤ P.T →
      ∀ t : ℝ, ∀ u ∈ P.ordinates, ∀ n ∈ P.indices, ∀ m ∈ P.indices, ∀ m' ∈ P.indices,
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m).Nonempty →
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m').Nonempty →
      logarithmicTaylorFifthLabel t u n m = logarithmicTaylorFifthLabel t u n m' → m = m' := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (81920*Real.pi) (by positivity) 0
      (η := 1/8) (by norm_num))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hPN hT t u hu n hn m hm m' hm' hover hover' hlabel
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hmb' := (P.mem_indices_iff m').mp hm'
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have hmp' : 0 < (m' : ℝ) := hNp.trans_le hmb'.1
  have hu' : P.T ≤ u := by
    simpa only [P.intervalLeft_eq] using (P.ordinates_in_interval u hu).1
  have hup := P.T_pos.trans_le hu'
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hHlow : P.N^(9/40 : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
  have hHp : 0 < (H : ℝ) := (Real.rpow_pos_of_pos hNp _).trans_le hHlow
  have hHfive : P.N^(9/8 : ℝ) ≤ (H : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 5
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hc : 81920*Real.pi ≤ P.N^(1/8 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_right _ _).trans hPN)
  have hprecision : 40*Real.pi/(H : ℝ)^5 ≤ P.T/(2048*P.N^6) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ = (81920*Real.pi)*P.N^6 := by ring
      _ ≤ P.N^(1/8 : ℝ)*P.N^6 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = P.N^5*P.N^(9/8 : ℝ) := by
        rw [← Real.rpow_natCast P.N 6,← Real.rpow_natCast P.N 5,
          ← Real.rpow_add hNp,← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := mul_le_mul hT hHfive (Real.rpow_nonneg hNp.le _) P.T_pos.le
  have ha := logarithmicTaylorCell_fifth_label_error hnp hmp hover
  have hb := logarithmicTaylorCell_fifth_label_error hnp hmp' hover'
  change _ ≤ 20*Real.pi/(H : ℝ)^5 at ha hb
  rw [hlabel] at ha
  have hdiff : u*|1/(m : ℝ)^5-1/(m' : ℝ)^5| ≤ 40*Real.pi/(H : ℝ)^5 := by
    calc
      _ = |(t/(n : ℝ)^5-u/(m' : ℝ)^5)-(t/(n : ℝ)^5-u/(m : ℝ)^5)| := by
        rw [show (t/(n : ℝ)^5-u/(m' : ℝ)^5)-(t/(n : ℝ)^5-u/(m : ℝ)^5) =
          u*(1/(m : ℝ)^5-1/(m' : ℝ)^5) by ring,abs_mul,abs_of_pos hup]
      _ ≤ |t/(n : ℝ)^5-u/(m' : ℝ)^5-10*Real.pi*(logarithmicTaylorFifthLabel t u n m' : ℝ)|+
          |10*Real.pi*(logarithmicTaylorFifthLabel t u n m' : ℝ)-(t/(n : ℝ)^5-u/(m : ℝ)^5)| :=
        abs_sub_le _ _ _
      _ ≤ _ := by
        rw [abs_sub_comm (10*Real.pi*_)]
        calc
          _ ≤ 20*Real.pi/(H : ℝ)^5+20*Real.pi/(H : ℝ)^5 := add_le_add hb ha
          _ = _ := by ring
  by_contra hne
  have hsep := mul_le_mul_of_nonneg_left
    (reciprocal_fifth_integer_gap hNp hmb.1 hmb'.1 hmb.2 hmb'.2 hne) hup.le
  have hlow : P.T/(1024*P.N^6) ≤ u*|1/(m : ℝ)^5-1/(m' : ℝ)^5| := by
    calc
      _ = P.T*(1/(1024*P.N^6)) := by ring
      _ ≤ u*(1/(1024*P.N^6)) := mul_le_mul_of_nonneg_right hu' (by positivity)
      _ ≤ _ := hsep
  have hh := hlow.trans (hdiff.trans hprecision)
  have hpos : 0 < P.T/P.N^6 := div_pos P.T_pos (pow_pos hNp _)
  have he1 : P.T/(1024*P.N^6) = (P.T/P.N^6)/1024 := by ring
  have he2 : P.T/(2048*P.N^6) = (P.T/P.N^6)/2048 := by ring
  rw [he1,he2] at hh
  linarith only [hh,hpos]

#print axioms logarithmicTaylorCell_same_label_unique_second

def logarithmicTaylorLabelPairs (P : ZetaLargeValuePattern) (t u : ℝ) (q : ℤ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (P.indices.product P.indices).filter (fun p =>
    (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
      logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 = q)

theorem logarithmicTaylorLabelPairs_card_nonzero :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^6 → ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      ∀ q : ℤ, q ≠ 0 →
      ((logarithmicTaylorLabelPairs P t u q).card : ℝ) ≤
        1+2*P.N^(7/10 : ℝ)/|(q : ℝ)| := by
  classical
  obtain ⟨Cd,hCd,hdia⟩ := logarithmicTaylorCell_nonzero_label_diameter
  obtain ⟨Cu,hCu,hunique⟩ := logarithmicTaylorCell_same_label_unique_second
  refine ⟨max Cd Cu,hCd.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT t ht u hu q hq
  have hNd : Cd ≤ P.N := (le_max_left _ _).trans hPN
  have hNu : Cu ≤ P.N := (le_max_right _ _).trans hPN
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let A := logarithmicTaylorLabelPairs P t u q
  have hspec {p : ℕ × ℕ} (hp : p ∈ A) :
      (p.1 ∈ P.indices ∧ p.2 ∈ P.indices) ∧
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 = q := by
    obtain ⟨hp',hover,hlabel⟩ := Finset.mem_filter.mp hp
    exact ⟨Finset.mem_product.mp hp',hover,hlabel⟩
  by_cases hempty : A = ∅
  · change (A.card : ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨p₀,hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let S : Finset ℤ := A.image (fun p => (p.1 : ℤ))
    have hcard : S.card = A.card := by
      apply Finset.card_image_iff.mpr
      rintro ⟨n,m⟩ ha ⟨n',m'⟩ hb hab
      change (n : ℤ) = (n' : ℤ) at hab
      have hnn : n = n' := by exact_mod_cast hab
      subst n'
      have hsa := hspec ha
      have hsb := hspec hb
      have hmm := hunique P hNu hTlow t u hu n hsa.1.1 m hsa.1.2 m' hsb.1.2
        hsa.2.1 hsb.2.1 (hsa.2.2.trans hsb.2.2.symm)
      exact congrArg (fun j : ℕ => (n,j)) hmm
    have hbound := integer_card_le_of_abs_sub_le S
      (a := (p₀.1 : ℝ)) (B := P.N^(7/10 : ℝ)/|(q : ℝ)|) (by positivity) (by
        intro z hz
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
        have hs := hspec hp
        have hs₀ := hspec hp₀
        have hh := hdia P hNd hT t ht u hu q hq
          p.1 hs.1.1 p.2 hs.1.2 p₀.1 hs₀.1.1 p₀.2 hs₀.1.2
          hs.2.1 hs₀.2.1 hs.2.2 hs₀.2.2
        simpa only [Int.cast_natCast] using hh)
    rw [hcard] at hbound
    calc
      _ ≤ 2*(P.N^(7/10 : ℝ)/|(q : ℝ)|)+1 := hbound
      _ = _ := by ring

#print axioms logarithmicTaylorLabelPairs_card_nonzero

theorem logarithmicTaylorFifthLabel_range (P : ZetaLargeValuePattern)
    (hT : P.N^5 ≤ P.T) {t u : ℝ} (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
    {n m : ℕ} (hn : n ∈ P.indices) (hm : m ∈ P.indices) :
    |(logarithmicTaylorFifthLabel t u n m : ℝ)| ≤ 2*P.T/P.N^5 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have htp := hTp.trans_le ht'.1
  have hup := hTp.trans_le hu'.1
  have hdelta : |t/(n : ℝ)^5-u/(m : ℝ)^5| ≤ 4*P.T/P.N^5 := by
    calc
      _ ≤ |t/(n : ℝ)^5|+|u/(m : ℝ)^5| := abs_sub _ _
      _ = t/(n : ℝ)^5+u/(m : ℝ)^5 := by
        rw [abs_of_pos (by positivity),abs_of_pos (by positivity)]
      _ ≤ 2*P.T/P.N^5+2*P.T/P.N^5 := add_le_add
        (div_le_div₀ (by positivity) ht'.2 (by positivity) (pow_le_pow_left₀ hNp.le hnb.1 5))
        (div_le_div₀ (by positivity) hu'.2 (by positivity) (pow_le_pow_left₀ hNp.le hmb.1 5))
      _ = _ := by ring
  let x := (t/(n : ℝ)^5-u/(m : ℝ)^5)/(10*Real.pi)
  have hx : |x| ≤ P.T/P.N^5 := by
    dsimp only [x]
    rw [abs_div,abs_of_pos (by positivity : 0 < 10*Real.pi)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left
      (show (4 : ℝ) ≤ 10*Real.pi by linarith [Real.pi_gt_three])
      (show 0 ≤ P.T/P.N^5 by positivity)
    calc
      _ ≤ 4*P.T/P.N^5 := hdelta
      _ = (P.T/P.N^5)*4 := by ring
      _ ≤ _ := hh
  have hround : |(round x : ℝ)| ≤ 1/2+|x| := by
    have hh := abs_sub_le (round x : ℝ) x 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (round x : ℝ)] at hh
    exact hh.trans (add_le_add (abs_sub_round x) le_rfl)
  have hunit : 1 ≤ P.T/P.N^5 := (le_div_iff₀ (by positivity)).mpr (by simpa using hT)
  change |(round x : ℝ)| ≤ _
  rw [show 2*P.T/P.N^5 = 2*(P.T/P.N^5) by ring]
  nlinarith only [hround,hx,hunit]

#print axioms logarithmicTaylorFifthLabel_range

def logarithmicTaylorNonzeroPairs (P : ZetaLargeValuePattern) (t u : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (P.indices.product P.indices).filter (fun p =>
    (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
      logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 ≠ 0)

theorem logarithmicTaylorNonzeroPairs_card_harmonic :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^6 → ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      let M := Nat.ceil (2*P.T/P.N^5)
      ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) ≤
        2*(M : ℝ)+4*P.N^(7/10 : ℝ)*(harmonic M : ℝ) := by
  classical
  obtain ⟨C,hC,hfibre⟩ := logarithmicTaylorLabelPairs_card_nonzero
  refine ⟨C,hC,?_⟩
  intro P hPN hTlow hT t ht u hu
  let M := Nat.ceil (2*P.T/P.N^5)
  change ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) ≤
    2*(M : ℝ)+4*P.N^(7/10 : ℝ)*(harmonic M : ℝ)
  let B (j : ℕ) := logarithmicTaylorLabelPairs P t u (j : ℤ) ∪
    logarithmicTaylorLabelPairs P t u (-(j : ℤ))
  have hcover : logarithmicTaylorNonzeroPairs P t u ⊆ (Finset.Icc 1 M).biUnion B := by
    intro p hp
    obtain ⟨hp',hover,hq⟩ := Finset.mem_filter.mp hp
    have hpm := Finset.mem_product.mp hp'
    let q := logarithmicTaylorFifthLabel t u p.1 p.2
    have hqbound := logarithmicTaylorFifthLabel_range P hTlow ht hu hpm.1 hpm.2
    have hcast : (q.natAbs : ℝ) = |(q : ℝ)| := by
      have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs q)
      simpa only [Int.cast_natCast,Int.cast_abs] using hh
    have hjhi : q.natAbs ≤ M := by
      have hh : (q.natAbs : ℝ) ≤ (M : ℝ) := by
        rw [hcast]
        exact hqbound.trans (Nat.le_ceil _)
      exact_mod_cast hh
    have hjlo : 1 ≤ q.natAbs := by
      have hh := Int.natAbs_pos.mpr hq
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨q.natAbs,Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩,?_⟩
    have hsign : q = (q.natAbs : ℤ) ∨ q = -(q.natAbs : ℤ) := by
      cases q with
      | ofNat j => exact Or.inl rfl
      | negSucc j => right; omega
    rcases hsign with hsign | hsign
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨hp',hover,hsign⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hp',hover,hsign⟩
  have hcard : (logarithmicTaylorNonzeroPairs P t u).card ≤
      ∑ j ∈ Finset.Icc 1 M, (B j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hB (j : ℕ) (hj : j ∈ Finset.Icc 1 M) :
      ((B j).card : ℝ) ≤ 2+4*P.N^(7/10 : ℝ)/(j : ℝ) := by
    have hjp : 0 < j := by have hh := (Finset.mem_Icc.mp hj).1; omega
    have hjr : 0 < (j : ℝ) := by exact_mod_cast hjp
    have hplus := hfibre P hPN hTlow hT t ht u hu (j : ℤ) (by exact_mod_cast hjp.ne')
    have hminus := hfibre P hPN hTlow hT t ht u hu (-(j : ℤ)) (by exact_mod_cast (neg_ne_zero.mpr hjr.ne'))
    have hsum : ((B j).card : ℝ) ≤
        ((logarithmicTaylorLabelPairs P t u (j : ℤ)).card : ℝ)+
          ((logarithmicTaylorLabelPairs P t u (-(j : ℤ))).card : ℝ) := by
      exact_mod_cast (Finset.card_union_le
        (logarithmicTaylorLabelPairs P t u (j : ℤ)) (logarithmicTaylorLabelPairs P t u (-(j : ℤ))))
    simp only [Int.cast_natCast,Int.cast_neg,abs_neg,abs_of_pos hjr] at hplus hminus
    calc
      _ ≤ (1+2*P.N^(7/10 : ℝ)/(j : ℝ))+(1+2*P.N^(7/10 : ℝ)/(j : ℝ)) :=
        hsum.trans (add_le_add hplus hminus)
      _ = _ := by ring
  have hcardR : ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 M, ((B j).card : ℝ) := by exact_mod_cast hcard
  apply hcardR.trans
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 M, (2+4*P.N^(7/10 : ℝ)/(j : ℝ)) := Finset.sum_le_sum hB
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum,div_eq_mul_inv]
      ring

#print axioms logarithmicTaylorNonzeroPairs_card_harmonic

theorem logarithmicTaylorNonzeroPairs_card_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) ≤ P.N^(3/4 : ℝ) := by
  obtain ⟨C₀,hC₀,hcount⟩ := logarithmicTaylorNonzeroPairs_card_harmonic
  have hev : ∀ᶠ N : ℝ in Filter.atTop,
      18 ≤ N^(7/20 : ℝ) ∧ 12 ≤ N^(1/20 : ℝ) ∧
        12*Real.log N ≤ N^(1/20 : ℝ) := by
    filter_upwards [eventually_const_log_pow_le_rpow 18 (by norm_num) 0
        (η := 7/20) (by norm_num),
      eventually_const_log_pow_le_rpow 12 (by norm_num) 0
        (η := 1/20) (by norm_num),
      eventually_const_log_pow_le_rpow 12 (by norm_num) 1
        (η := 1/20) (by norm_num)] with N ha hb hc
    simpa only [pow_zero,mul_one,pow_one] using And.intro ha (And.intro hb hc)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max C₀ N₀,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT t ht u hu
  obtain ⟨ha,hb,hc⟩ := hN₀ P.N ((le_max_right _ _).trans hPN)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hT6 : P.T ≤ P.N^6 := hT.trans (by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (27/5 : ℝ) ≤ (6 : ℕ)))
  let M := Nat.ceil (2*P.T/P.N^5)
  have hraw := hcount P ((le_max_left _ _).trans hPN) hTlow hT6 t ht u hu
  change ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) ≤
    2*(M : ℝ)+4*P.N^(7/10 : ℝ)*(harmonic M : ℝ) at hraw
  have hunit : 1 ≤ P.T/P.N^5 := (le_div_iff₀ (by positivity)).mpr (by simpa using hTlow)
  have hM : (M : ℝ) ≤ 3*P.N^(2/5 : ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2*P.T/P.N^5 by positivity)
    change (M : ℝ) < 2*P.T/P.N^5+1 at hh
    rw [show 2*P.T/P.N^5 = 2*(P.T/P.N^5) by ring] at hh
    calc
      _ ≤ 3*(P.T/P.N^5) := by linarith only [hh,hunit]
      _ ≤ 3*(P.N^(27/5 : ℝ)/P.N^5) := by gcongr
      _ = _ := by rw [← Real.rpow_natCast P.N 5,← Real.rpow_sub hNp]; norm_num
  have hMN : (M : ℝ) ≤ P.N := by
    have hthree : 3 ≤ P.N^(3/5 : ℝ) := (by linarith only [ha] : (3 : ℝ) ≤ P.N^(7/20 : ℝ)).trans
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num))
    calc
      _ ≤ 3*P.N^(2/5 : ℝ) := hM
      _ ≤ P.N^(3/5 : ℝ)*P.N^(2/5 : ℝ) := mul_le_mul_of_nonneg_right hthree (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hMp : 0 < (M : ℝ) := (show 0 < 2*P.T/P.N^5 by positivity).trans_le (Nat.le_ceil _)
  have hharm : (harmonic M : ℝ) ≤ 1+Real.log P.N :=
    (harmonic_le_one_add_log M).trans (by linarith only [Real.log_le_log hMp hMN])
  have ha' : 18*P.N^(2/5 : ℝ) ≤ P.N^(3/4 : ℝ) := by
    calc
      _ ≤ P.N^(7/20 : ℝ)*P.N^(2/5 : ℝ) := mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hb' : 12*P.N^(7/10 : ℝ) ≤ P.N^(3/4 : ℝ) := by
    calc
      _ ≤ P.N^(1/20 : ℝ)*P.N^(7/10 : ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hc' : 12*Real.log P.N*P.N^(7/10 : ℝ) ≤ P.N^(3/4 : ℝ) := by
    calc
      _ ≤ P.N^(1/20 : ℝ)*P.N^(7/10 : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hs := mul_le_mul_of_nonneg_left hharm (show 0 ≤ 4*P.N^(7/10 : ℝ) by positivity)
  nlinarith only [hraw,hM,hs,ha',hb',hc']

#print axioms logarithmicTaylorNonzeroPairs_card_uniform

private theorem reciprocal_fifth_gap_upper {x y B : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxB : x ≤ B) (hyB : y ≤ B) :
    |x-y|/B^6 ≤ |1/x^5-1/y^5| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx hyB hxB (le_of_not_ge hxy)
  have hB : 0 < B := hx.trans_le hxB
  have h4 := pow_le_pow_left₀ hx.le hxy 4
  have h5 := pow_le_pow_left₀ hx.le hxy 5
  have hnum : x^4*(y-x) ≤ y^5-x^5 := by
    nlinarith only [mul_nonneg hy.le (sub_nonneg.mpr h4)]
  have hden : x*y^5 ≤ B^6 := by
    calc
      _ ≤ B*B^5 := mul_le_mul hxB (pow_le_pow_left₀ hy.le hyB 5) (by positivity) hB.le
      _ = _ := by ring
  rw [abs_sub_comm x y,abs_of_nonneg (sub_nonneg.mpr hxy),
    abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h5))]
  apply (le_of_mul_le_mul_left _ (show 0 < B^6*x^5*y^5 by positivity))
  field_simp
  have ha := mul_le_mul_of_nonneg_right hden (show 0 ≤ x^4*(y-x) by positivity)
  have hb := mul_le_mul_of_nonneg_left hnum (show 0 ≤ B^6 by positivity)
  nlinarith only [ha,hb]

#print axioms reciprocal_fifth_gap_upper

private theorem reciprocal_sixth_fifth {x y a : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hay : a ≤ y) :
    |1/x^6-1/y^6| ≤ (2/a)*|1/x^5-1/y^5| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hay hax (le_of_not_ge hxy)
  have hx : 0 < x := ha.trans_le hax
  have hy : 0 < y := ha.trans_le hay
  have h4 := pow_le_pow_left₀ hx.le hxy 4
  have h5 := pow_le_pow_left₀ hx.le hxy 5
  have h6 := pow_le_pow_left₀ hx.le hxy 6
  have hnum : x^4*(y-x) ≤ y^5-x^5 := by
    nlinarith only [mul_nonneg hy.le (sub_nonneg.mpr h4)]
  have hnum' : y^6-x^6 ≤ 2*y*(y^5-x^5) := by
    have hh := mul_le_mul_of_nonneg_left hnum hx.le
    have hh' := mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr h5)
    nlinarith only [hh,hh']
  rw [abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h6)),
    abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) h5))]
  apply (le_of_mul_le_mul_left _ (show 0 < a*x^6*y^6 by positivity))
  field_simp
  have hh := mul_le_mul_of_nonneg_left hnum' ha.le
  have hh' := mul_le_mul_of_nonneg_right hax (show 0 ≤ 2*y*(y^5-x^5) by positivity)
  nlinarith only [hh,hh']

#print axioms reciprocal_sixth_fifth

def logarithmicTaylorFifthRatio (t u : ℝ) : ℝ := (u/t)^(1/5 : ℝ)

theorem logarithmicTaylorFifthRatio_bounds {T t u : ℝ} (hT : 0 < T)
    (ht : T ≤ t) (hu : T ≤ u) (ht' : t ≤ 2*T) (hu' : u ≤ 2*T) :
    0 < logarithmicTaylorFifthRatio t u ∧
    1/2 ≤ logarithmicTaylorFifthRatio t u ∧ logarithmicTaylorFifthRatio t u ≤ 2 ∧
    t*(logarithmicTaylorFifthRatio t u)^5 = u := by
  have htp : 0 < t := hT.trans_le ht
  have hup : 0 < u := hT.trans_le hu
  have hratio : 0 < u/t := by positivity
  have hlo : 1/2 ≤ u/t := (le_div_iff₀ htp).mpr (by linarith only [hu,ht'])
  have hhi : u/t ≤ 2 := (div_le_iff₀ htp).mpr (by linarith only [ht,hu'])
  have hr : 0 < logarithmicTaylorFifthRatio t u := Real.rpow_pos_of_pos hratio _
  have hpow : (logarithmicTaylorFifthRatio t u)^5 = u/t := by
    unfold logarithmicTaylorFifthRatio
    rw [← Real.rpow_mul_natCast hratio.le]
    norm_num
  refine ⟨hr,?_,?_,?_⟩
  · by_contra! hh
    have hh' := pow_lt_pow_left₀ hh hr.le (by decide : 5 ≠ 0)
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hlo,hh']
  · by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by norm_num : (0 : ℝ) ≤ 2) (by decide : 5 ≠ 0)
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hhi,hh']
  · rw [hpow]
    field_simp

#print axioms logarithmicTaylorFifthRatio_bounds

theorem logarithmicTaylorCell_zero_label_strip (P : ZetaLargeValuePattern)
    {H n m : ℕ} {t u : ℝ} (hH : 0 < H)
    (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
    (hn : n ∈ P.indices) (hm : m ∈ P.indices)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty)
    (hq : logarithmicTaylorFifthLabel t u n m = 0) :
    |(m : ℝ)-logarithmicTaylorFifthRatio t u*(n : ℝ)| ≤
      81920*Real.pi*P.N^6/(P.T*(H : ℝ)^5) := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hHp : 0 < (H : ℝ) := by exact_mod_cast hH
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have hup := hTp.trans_le hu'.1
  obtain ⟨hrp,_,hrhi,hrpow⟩ :=
    logarithmicTaylorFifthRatio_bounds hTp ht'.1 hu'.1 ht'.2 hu'.2
  let r := logarithmicTaylorFifthRatio t u
  have hrnp : 0 < r*(n : ℝ) := by dsimp only [r]; positivity
  have hrnhi : r*(n : ℝ) ≤ 4*P.N := by
    have hh := mul_le_mul hrhi hnb.2 hnp.le (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [r]
    linarith only [hh]
  have he5 : u/(r*(n : ℝ))^5 = t/(n : ℝ)^5 := by
    rw [← hrpow]
    dsimp only [r]
    field_simp
  have h5 := logarithmicTaylorCell_fifth_label_error hnp hmp hover
  rw [hq,Int.cast_zero,mul_zero,sub_zero] at h5
  have hrec := reciprocal_fifth_gap_upper hmp hrnp
    (hmb.2.trans (by linarith only [hNp] : 2*P.N ≤ 4*P.N)) hrnhi
  have hscaled : u*(|(m : ℝ)-r*(n : ℝ)|/(4*P.N)^6) ≤ 20*Real.pi/(H : ℝ)^5 := by
    calc
      _ ≤ u*|1/(m : ℝ)^5-1/(r*(n : ℝ))^5| := mul_le_mul_of_nonneg_left hrec hup.le
      _ = |u/(m : ℝ)^5-u/(r*(n : ℝ))^5| := by
        rw [show u/(m : ℝ)^5-u/(r*(n : ℝ))^5 =
          u*(1/(m : ℝ)^5-1/(r*(n : ℝ))^5) by ring,abs_mul,abs_of_pos hup]
      _ = |t/(n : ℝ)^5-u/(m : ℝ)^5| := by rw [he5,abs_sub_comm]
      _ ≤ _ := h5
  have hscaled' : P.T*|(m : ℝ)-r*(n : ℝ)| ≤
      (20*Real.pi/(H : ℝ)^5)*(4*P.N)^6 := by
    have hh := mul_le_mul_of_nonneg_right hu'.1
      (show 0 ≤ |(m : ℝ)-r*(n : ℝ)|/(4*P.N)^6 by positivity)
    have hh' : P.T*|(m : ℝ)-r*(n : ℝ)|/(4*P.N)^6 ≤ 20*Real.pi/(H : ℝ)^5 := by
      rw [mul_div_assoc]
      exact hh.trans hscaled
    exact (div_le_iff₀ (by positivity)).mp hh'
  change |(m : ℝ)-r*(n : ℝ)| ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right hscaled' (show 0 ≤ (H : ℝ)^5 by positivity)
  field_simp at hh
  nlinarith only [hh]

#print axioms logarithmicTaylorCell_zero_label_strip

theorem logarithmicTaylorFifthRatio_gap {T t u : ℝ} (hT : 0 < T)
    (ht : T ≤ t) (hu : T ≤ u) (ht' : t ≤ 2*T) (hu' : u ≤ 2*T) :
    |t-u| ≤ 160*T*|logarithmicTaylorFifthRatio t u-1| := by
  obtain ⟨hrp,_,hrhi,hrpow⟩ := logarithmicTaylorFifthRatio_bounds hT ht hu ht' hu'
  let r := logarithmicTaylorFifthRatio t u
  have htp := hT.trans_le ht
  have hpoly : r^4+r^3+r^2+r+1 ≤ 80 := by
    have h2 := pow_le_pow_left₀ hrp.le hrhi 2
    have h3 := pow_le_pow_left₀ hrp.le hrhi 3
    have h4 := pow_le_pow_left₀ hrp.le hrhi 4
    dsimp only [r]
    norm_num at h2 h3 h4
    linarith only [h2,h3,h4,hrhi]
  calc
    _ = t*|r^5-1| := by
      rw [← hrpow,show t-t*logarithmicTaylorFifthRatio t u^5 =
        -(t*(logarithmicTaylorFifthRatio t u^5-1)) by ring,
        abs_neg,abs_mul,abs_of_pos htp]
    _ = t*(|r-1| * (r^4+r^3+r^2+r+1)) := by
      rw [show r^5-1 = (r-1)*(r^4+r^3+r^2+r+1) by ring,
        abs_mul,abs_of_nonneg (show 0 ≤ r^4+r^3+r^2+r+1 by dsimp only [r]; positivity)]
    _ ≤ t*(|r-1| * 80) := by gcongr
    _ ≤ (2*T)*(|r-1| * 80) := mul_le_mul_of_nonneg_right ht' (by positivity)
    _ = _ := by ring

#print axioms logarithmicTaylorFifthRatio_gap

theorem logarithmicTaylorCell_zero_label_slope (P : ZetaLargeValuePattern)
    (hT : P.T ≤ P.N^6) {H n m : ℕ} {t u : ℝ} (hH : 0 < H) (hHN : (H : ℝ) ≤ P.N)
    (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
    (hn : n ∈ P.indices) (hm : m ∈ P.indices)
    (hover : (logarithmicTaylorCell H t n ∩ logarithmicTaylorCell H u m).Nonempty)
    (hq : logarithmicTaylorFifthLabel t u n m = 0) :
    |logarithmicTaylorFifthRatio t u-1| ≤ 13312*Real.pi*P.N^6/(P.T*(H : ℝ)^6) := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hHp : 0 < (H : ℝ) := by exact_mod_cast hH
  have hnb := (P.mem_indices_iff n).mp hn
  have hmb := (P.mem_indices_iff m).mp hm
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have hmp : 0 < (m : ℝ) := hNp.trans_le hmb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have htp := hTp.trans_le ht'.1
  have hup := hTp.trans_le hu'.1
  obtain ⟨hrp,hrlo,hrhi,hrpow⟩ :=
    logarithmicTaylorFifthRatio_bounds hTp ht'.1 hu'.1 ht'.2 hu'.2
  let r := logarithmicTaylorFifthRatio t u
  have hrnp : 0 < r*(n : ℝ) := by dsimp only [r]; positivity
  have hrnlo : P.N/2 ≤ r*(n : ℝ) := by
    have hh := mul_le_mul hrlo hnb.1 hNp.le hrp.le
    dsimp only [r]
    linarith only [hh]
  have he5 : u/(r*(n : ℝ))^5 = t/(n : ℝ)^5 := by
    rw [← hrpow]
    dsimp only [r]
    field_simp
  have he6 : t/(n : ℝ)^6-u/(r*(n : ℝ))^6 =
      (t/(r*(n : ℝ)^6))*(r-1) := by
    rw [← hrpow]
    dsimp only [r]
    field_simp
  have h5 := logarithmicTaylorCell_fifth_label_error hnp hmp hover
  rw [hq,Int.cast_zero,mul_zero,sub_zero] at h5
  have hrec := reciprocal_sixth_fifth (show 0 < P.N/2 by positivity)
    (show P.N/2 ≤ (m : ℝ) by linarith only [hmb.1,hNp]) hrnlo
  have hprojection : |u/(m : ℝ)^6-u/(r*(n : ℝ))^6| ≤ 80*Real.pi/(P.N*(H : ℝ)^5) := by
    calc
      _ = u*|1/(m : ℝ)^6-1/(r*(n : ℝ))^6| := by
        rw [show u/(m : ℝ)^6-u/(r*(n : ℝ))^6 =
          u*(1/(m : ℝ)^6-1/(r*(n : ℝ))^6) by ring,abs_mul,abs_of_pos hup]
      _ ≤ u*((2/(P.N/2))*|1/(m : ℝ)^5-1/(r*(n : ℝ))^5|) :=
        mul_le_mul_of_nonneg_left hrec hup.le
      _ = (4/P.N)*|t/(n : ℝ)^5-u/(m : ℝ)^5| := by
        rw [abs_sub_comm (t/(n : ℝ)^5),← he5,
          show u/(m : ℝ)^5-u/(r*(n : ℝ))^5 =
            u*(1/(m : ℝ)^5-1/(r*(n : ℝ))^5) by ring,abs_mul,abs_of_pos hup]
        ring
      _ ≤ (4/P.N)*(20*Real.pi/(H : ℝ)^5) := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  have hprojection' : 80*Real.pi/(P.N*(H : ℝ)^5) ≤ 80*Real.pi/(H : ℝ)^6 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc
      _ = (H : ℝ)*(H : ℝ)^5 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHN (by positivity)
  have h6 := logarithmicTaylorCell_sixth_raw P hT ht hu hn hm hover
  have hs : (t/(r*(n : ℝ)^6))*|r-1| ≤ 104*Real.pi/(H : ℝ)^6 := by
    calc
      _ = |t/(n : ℝ)^6-u/(r*(n : ℝ))^6| := by
        rw [he6,abs_mul,abs_of_pos (show 0 < t/(r*(n : ℝ)^6) by dsimp only [r]; positivity)]
      _ ≤ |t/(n : ℝ)^6-u/(m : ℝ)^6|+|u/(m : ℝ)^6-u/(r*(n : ℝ))^6| := abs_sub_le _ _ _
      _ ≤ 24*Real.pi/(H : ℝ)^6+80*Real.pi/(H : ℝ)^6 := add_le_add h6 (hprojection.trans hprojection')
      _ = _ := by ring
  have hden : r*(n : ℝ)^6 ≤ 128*P.N^6 := by
    calc
      _ ≤ 2*(2*P.N)^6 := mul_le_mul hrhi (pow_le_pow_left₀ hnp.le hnb.2 6) (by positivity) (by norm_num)
      _ = _ := by ring
  have hs' : t*|r-1| ≤ (104*Real.pi/(H : ℝ)^6)*(r*(n : ℝ)^6) := by
    apply (div_le_iff₀ (by dsimp only [r]; positivity)).mp
    simpa only [div_mul_eq_mul_div] using hs
  have hs'' : P.T*|r-1| ≤ (104*Real.pi/(H : ℝ)^6)*(128*P.N^6) :=
    (mul_le_mul_of_nonneg_right ht'.1 (abs_nonneg _)).trans
      (hs'.trans (mul_le_mul_of_nonneg_left hden (by positivity)))
  change |r-1| ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right hs'' (show 0 ≤ (H : ℝ)^6 by positivity)
  field_simp at hh
  nlinarith only [hh]

#print axioms logarithmicTaylorCell_zero_label_slope

private theorem integer_pair_strip_card (A : Finset (ℕ × ℕ))
    {N r η : ℝ} (hN : 0 ≤ N) (hη : 0 ≤ η) (hr : r ≠ 1)
    (hfirst : ∀ p ∈ A, (p.1 : ℝ) ≤ 2*N)
    (hstrip : ∀ p ∈ A, |(p.2 : ℝ)-r*(p.1 : ℝ)| ≤ η) :
    (A.card : ℝ) ≤ (4*N*|r-1|+2*η+1)*(2*η/|r-1|+1) := by
  classical
  let d (p : ℕ × ℕ) : ℤ := (p.2 : ℤ)-(p.1 : ℤ)
  let D := A.image d
  have hθ : 0 < |r-1| := abs_pos.mpr (sub_ne_zero.mpr hr)
  have hD : (D.card : ℝ) ≤ 4*N*|r-1|+2*η+1 := by
    have hh := integer_card_le_of_abs_sub_le D
      (a := 0) (B := 2*N*|r-1|+η) (by positivity) (by
        intro z hz
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
        simp only [d,Int.cast_sub,Int.cast_natCast,sub_zero]
        calc
          _ = |((p.2 : ℝ)-r*(p.1 : ℝ))+(r-1)*(p.1 : ℝ)| := by congr 1; ring
          _ ≤ |(p.2 : ℝ)-r*(p.1 : ℝ)|+|(r-1)*(p.1 : ℝ)| := abs_add_le _ _
          _ ≤ η+|r-1| * (2*N) := by
            rw [abs_mul,abs_of_nonneg (show 0 ≤ (p.1 : ℝ) from Nat.cast_nonneg _)]
            exact add_le_add (hstrip p hp) (mul_le_mul_of_nonneg_left (hfirst p hp) (abs_nonneg _))
          _ = _ := by ring)
    linarith only [hh]
  let F (z : ℤ) := A.filter (fun p => d p = z)
  have hF (z : ℤ) : ((F z).card : ℝ) ≤ 2*η/|r-1|+1 := by
    let S : Finset ℤ := (F z).image (fun p => (p.1 : ℤ))
    have hcard : S.card = (F z).card := by
      apply Finset.card_image_iff.mpr
      rintro ⟨n,m⟩ ha ⟨n',m'⟩ hb hab
      change (n : ℤ) = (n' : ℤ) at hab
      have hnn : n = n' := by exact_mod_cast hab
      have hda := (Finset.mem_filter.mp ha).2
      have hdb := (Finset.mem_filter.mp hb).2
      change (m : ℤ)-(n : ℤ) = z at hda
      change (m' : ℤ)-(n' : ℤ) = z at hdb
      have hmm : m = m' := by omega
      exact Prod.ext hnn hmm
    have hh := integer_card_le_of_abs_sub_le S
      (a := (z : ℝ)/(r-1)) (B := η/|r-1|) (by positivity) (by
        intro j hj
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨hpa,hpd⟩ := Finset.mem_filter.mp hp
        have hd : (z : ℝ) = (p.2 : ℝ)-(p.1 : ℝ) := by
          have hh := congrArg (fun w : ℤ => (w : ℝ)) hpd
          simpa only [d,Int.cast_sub,Int.cast_natCast] using hh.symm
        rw [Int.cast_natCast,hd]
        calc
          _ = |((p.1 : ℝ)*r-(p.2 : ℝ))/(r-1)| := by
            congr 1
            field_simp
            ring
          _ = |(p.2 : ℝ)-r*(p.1 : ℝ)|/|r-1| := by rw [abs_div,abs_sub_comm]; congr 2; ring
          _ ≤ _ := div_le_div_of_nonneg_right (hstrip p hpa) hθ.le)
    rw [hcard] at hh
    rw [← mul_div_assoc] at hh
    exact hh
  have hcard : (A.card : ℝ) = ∑ z ∈ D, ((F z).card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image d A)
  calc
    _ = ∑ z ∈ D, ((F z).card : ℝ) := hcard
    _ ≤ ∑ _z ∈ D, (2*η/|r-1|+1) := Finset.sum_le_sum (fun z _ => hF z)
    _ = (D.card : ℝ)*(2*η/|r-1|+1) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)

#print axioms integer_pair_strip_card

theorem logarithmicTaylorZeroPairs_card_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      P.T/(8192*P.N) < |t-u| →
      ((logarithmicTaylorLabelPairs P t u 0).card : ℝ) ≤ P.N^(9/10 : ℝ) := by
  classical
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (1000000000000*Real.pi) (by positivity) 0
      (η := 1/40) (by norm_num))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hPN hTlow hT t ht u hu hgap
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hbig : 1000000000000*Real.pi ≤ P.N^(1/40 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_right _ _).trans hPN)
  have hc : 81920*Real.pi ≤ P.N^(1/8 : ℝ) :=
    (show 81920*Real.pi ≤ 1000000000000*Real.pi by nlinarith [Real.pi_pos]).trans
      (hbig.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)))
  have htwo : 2 ≤ P.N^(31/40 : ℝ) :=
    (show (2 : ℝ) ≤ 1000000000000*Real.pi by linarith [Real.pi_gt_three]).trans
      (hbig.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)))
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hHlow : P.N^(9/40 : ℝ) ≤ (H : ℝ) := Nat.le_ceil _
  have hHp : 0 < (H : ℝ) := (Real.rpow_pos_of_pos hNp _).trans_le hHlow
  have hH : 0 < H := by exact_mod_cast hHp
  have hHN : (H : ℝ) ≤ P.N := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (9/40))
    have hone := Real.one_le_rpow P.one_lt_N.le (by norm_num : (0 : ℝ) ≤ 9/40)
    calc
      _ ≤ 2*P.N^(9/40 : ℝ) := by dsimp only [H]; linarith only [hh,hone]
      _ ≤ P.N^(31/40 : ℝ)*P.N^(9/40 : ℝ) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hHfive : P.N^(9/8 : ℝ) ≤ (H : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 5
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hHsix : P.N^(27/20 : ℝ) ≤ (H : ℝ)^6 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hHlow 6
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hT6 : P.T ≤ P.N^6 := hT.trans (by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (27/5 : ℝ) ≤ (6 : ℕ)))
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hu' : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  let r := logarithmicTaylorFifthRatio t u
  let θ := |r-1|
  let η := 81920*Real.pi*P.N^6/(P.T*(H : ℝ)^5)
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hθlow : 1/(1310720*P.N) ≤ θ := by
    have hh := hgap.trans_le (logarithmicTaylorFifthRatio_gap hTp ht'.1 hu'.1 ht'.2 hu'.2)
    change P.T/(8192*P.N) < 160*P.T*θ at hh
    rw [show P.T/(8192*P.N) = (160*P.T)*(1/(1310720*P.N)) by ring] at hh
    exact ((mul_lt_mul_iff_right₀ (show 0 < 160*P.T by positivity)).mp hh).le
  have hθ : 0 < θ := (show 0 < 1/(1310720*P.N) by positivity).trans_le hθlow
  have hr : r ≠ 1 := sub_ne_zero.mp (abs_pos.mp hθ)
  have hNη : P.N*η ≤ 81920*Real.pi*P.N^(7/8 : ℝ) := by
    calc
      _ = (81920*Real.pi)*(P.N^7/(P.T*(H : ℝ)^5)) := by dsimp only [η]; ring
      _ ≤ (81920*Real.pi)*(P.N^7/(P.N^5*P.N^(9/8 : ℝ))) := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast P.N 7,← Real.rpow_natCast P.N 5,
          ← Real.rpow_add hNp,← Real.rpow_sub hNp]
        norm_num
  have hηone : η ≤ 1 := by
    have hh : P.N*η ≤ P.N*1 := by
      calc
        _ ≤ (81920*Real.pi)*P.N^(7/8 : ℝ) := hNη
        _ ≤ P.N^(1/8 : ℝ)*P.N^(7/8 : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by rw [← Real.rpow_add hNp]; norm_num
    exact (mul_le_mul_iff_right₀ hNp).mp hh
  have hηratio : η/θ ≤ 1310720*(P.N*η) := by
    calc
      _ ≤ η/(1/(1310720*P.N)) := div_le_div_of_nonneg_left hη (by positivity) hθlow
      _ = _ := by rw [one_div,div_inv_eq_mul]; ring
  let A := logarithmicTaylorLabelPairs P t u 0
  have hspec {p : ℕ × ℕ} (hp : p ∈ A) :
      (p.1 ∈ P.indices ∧ p.2 ∈ P.indices) ∧
      (logarithmicTaylorCell H t p.1 ∩ logarithmicTaylorCell H u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 = 0 := by
    obtain ⟨hp',hover,hq⟩ := Finset.mem_filter.mp hp
    exact ⟨Finset.mem_product.mp hp',hover,hq⟩
  by_cases he : A = ∅
  · change (A.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨p₀,hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hs₀ := hspec hp₀
    have hslope := logarithmicTaylorCell_zero_label_slope P hT6 hH hHN ht hu
      hs₀.1.1 hs₀.1.2 hs₀.2.1 hs₀.2.2
    change θ ≤ 13312*Real.pi*P.N^6/(P.T*(H : ℝ)^6) at hslope
    have hNθ : P.N*θ ≤ 13312*Real.pi*P.N^(7/8 : ℝ) := by
      calc
        _ ≤ P.N*(13312*Real.pi*P.N^6/(P.T*(H : ℝ)^6)) := mul_le_mul_of_nonneg_left hslope hNp.le
        _ = (13312*Real.pi)*(P.N^7/(P.T*(H : ℝ)^6)) := by ring
        _ ≤ (13312*Real.pi)*(P.N^7/(P.N^5*P.N^(27/20 : ℝ))) := by gcongr
        _ = (13312*Real.pi)*P.N^(13/20 : ℝ) := by
          rw [← Real.rpow_natCast P.N 7,← Real.rpow_natCast P.N 5,
            ← Real.rpow_add hNp,← Real.rpow_sub hNp]
          norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)) (by positivity)
    have hraw := integer_pair_strip_card A hNp.le hη hr
      (fun p hp => ((P.mem_indices_iff p.1).mp (hspec hp).1.1).2)
      (fun p hp => logarithmicTaylorCell_zero_label_strip P hH ht hu
        (hspec hp).1.1 (hspec hp).1.2 (hspec hp).2.1 (hspec hp).2.2)
    change (A.card : ℝ) ≤ (4*P.N*θ+2*η+1)*(2*η/θ+1) at hraw
    have hexpand : (4*P.N*θ+2*η+1)*(2*η/θ+1) =
        8*(P.N*η)+4*(P.N*θ)+4*η*(η/θ)+2*η+2*(η/θ)+1 := by
      field_simp
      ring
    rw [hexpand] at hraw
    have hηsquare := mul_le_mul_of_nonneg_right hηone (show 0 ≤ η/θ by positivity)
    have hcoarse : (A.card : ℝ) ≤ 7864328*(P.N*η)+4*(P.N*θ)+5 := by
      nlinarith only [hraw,hηsquare,hηratio,hηone]
    have hone : 1 ≤ P.N^(7/8 : ℝ) := Real.one_le_rpow P.one_lt_N.le (by norm_num)
    have hsmall : (A.card : ℝ) ≤ (1000000000000*Real.pi)*P.N^(7/8 : ℝ) := by
      have hcst : 7864328*(81920*Real.pi)+4*(13312*Real.pi)+5 ≤ 1000000000000*Real.pi := by
        linarith [Real.pi_gt_three]
      calc
        _ ≤ 7864328*((81920*Real.pi)*P.N^(7/8 : ℝ))+
            4*((13312*Real.pi)*P.N^(7/8 : ℝ))+5*P.N^(7/8 : ℝ) := by
          nlinarith only [hcoarse,hNη,hNθ,hone]
        _ = (7864328*(81920*Real.pi)+4*(13312*Real.pi)+5)*P.N^(7/8 : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcst (by positivity)
    calc
      _ ≤ (1000000000000*Real.pi)*P.N^(7/8 : ℝ) := hsmall
      _ ≤ P.N^(1/40 : ℝ)*P.N^(7/8 : ℝ) := mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num

#print axioms logarithmicTaylorZeroPairs_card_uniform

def logarithmicTaylorMixedPairs (P : ZetaLargeValuePattern) (t u : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (P.indices.product P.indices).filter (fun p =>
    (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
      logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty)

theorem logarithmicTaylorMixedPairs_split (P : ZetaLargeValuePattern) (t u : ℝ) :
    logarithmicTaylorMixedPairs P t u =
      logarithmicTaylorLabelPairs P t u 0 ∪ logarithmicTaylorNonzeroPairs P t u := by
  classical
  ext p
  simp only [logarithmicTaylorMixedPairs,logarithmicTaylorLabelPairs,
    logarithmicTaylorNonzeroPairs,Finset.mem_filter,Finset.mem_union]
  tauto

#print axioms logarithmicTaylorMixedPairs_split

theorem logarithmicTaylorMixedPairs_card_far :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates,
      P.N^(10/3 : ℝ) < |t-u| →
      ((logarithmicTaylorMixedPairs P t u).card : ℝ) ≤ P.N^(19/20 : ℝ) := by
  classical
  obtain ⟨C₀,hC₀,hzero⟩ := logarithmicTaylorZeroPairs_card_uniform
  obtain ⟨C₁,_,hnonzero⟩ := logarithmicTaylorNonzeroPairs_card_uniform
  obtain ⟨C₂,_,hmedium⟩ := logarithmicTaylorCell_medium_far_disjoint
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 2 (by norm_num) 0 (η := 1/20) (by norm_num))
  refine ⟨max C₀ (max C₁ (max C₂ N₀)),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT t ht u hu hfar
  have hN₀' : C₀ ≤ P.N := (le_max_left _ _).trans hPN
  have hN₁' : C₁ ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hPN)
  have hN₂' : C₂ ≤ P.N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  by_cases hgap : |t-u| ≤ P.T/(8192*P.N)
  · have hempty : logarithmicTaylorMixedPairs P t u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp',α,hαt,hαu⟩ := Finset.mem_filter.mp hp
      have hpm := Finset.mem_product.mp hp'
      exact (Set.disjoint_left.mp (hmedium P hN₂' hTlow hT t ht u hu hfar hgap
        p.1 hpm.1 p.2 hpm.2)) hαt hαu
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · have hza := hzero P hN₀' hTlow hT t ht u hu (lt_of_not_ge hgap)
    have hnza := hnonzero P hN₁' hTlow hT t ht u hu
    have hsum : ((logarithmicTaylorMixedPairs P t u).card : ℝ) ≤
        ((logarithmicTaylorLabelPairs P t u 0).card : ℝ)+
        ((logarithmicTaylorNonzeroPairs P t u).card : ℝ) := by
      rw [logarithmicTaylorMixedPairs_split]
      exact_mod_cast Finset.card_union_le (logarithmicTaylorLabelPairs P t u 0)
        (logarithmicTaylorNonzeroPairs P t u)
    have htwo : 2 ≤ P.N^(1/20 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hPN)))
    calc
      _ ≤ P.N^(9/10 : ℝ)+P.N^(3/4 : ℝ) := hsum.trans (add_le_add hza hnza)
      _ ≤ 2*P.N^(9/10 : ℝ) := by
        have hh := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num : (3/4 : ℝ) ≤ 9/10)
        linarith only [hh]
      _ ≤ P.N^(1/20 : ℝ)*P.N^(9/10 : ℝ) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num

#print axioms logarithmicTaylorMixedPairs_card_far

theorem logarithmicTaylorMixedPairs_card_self :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ t ∈ P.ordinates, ((logarithmicTaylorMixedPairs P t t).card : ℝ) ≤ 3*P.N := by
  classical
  obtain ⟨C₀,hC₀,hunique⟩ := logarithmicTaylorCell_same_label_unique_second
  obtain ⟨C₁,_,hnonzero⟩ := logarithmicTaylorNonzeroPairs_card_uniform
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT t ht
  let A := logarithmicTaylorLabelPairs P t t 0
  have hdiag {p : ℕ × ℕ} (hp : p ∈ A) : p.2 = p.1 := by
    obtain ⟨hp',hover,hq⟩ := Finset.mem_filter.mp hp
    have hpm := Finset.mem_product.mp hp'
    let H := Nat.ceil (P.N^(9/40 : ℝ))
    have hcenter : GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) p.1 ∈
        logarithmicTaylorCell H t p.1 := by
      intro j hj
      change dist _ _ ≤ GafniTao.heathBrownCellRadius H j
      rw [dist_self]
      unfold GafniTao.heathBrownCellRadius
      positivity
    have hself : (logarithmicTaylorCell H t p.1 ∩ logarithmicTaylorCell H t p.1).Nonempty :=
      ⟨_,hcenter,hcenter⟩
    apply hunique P ((le_max_left _ _).trans hPN) hTlow t t ht p.1 hpm.1 p.2 hpm.2 p.1 hpm.1 hover hself
    rw [hq]
    simp only [logarithmicTaylorFifthLabel,sub_self,zero_div,round_zero]
  have hzero : (A.card : ℝ) ≤ 2*P.N := by
    have himage : A.image Prod.fst ⊆ P.indices := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hcard : (A.image Prod.fst).card = A.card := by
      apply Finset.card_image_iff.mpr
      intro p hp q hq heq
      apply Prod.ext heq
      exact (hdiag hp).trans (heq.trans (hdiag hq).symm)
    have hh : (A.card : ℝ) ≤ (P.indices.card : ℝ) := by
      have hh' := Finset.card_le_card himage
      rw [hcard] at hh'
      exact_mod_cast hh'
    exact hh.trans P.indices_card_cast_le_two_mul_N
  have hnz := hnonzero P ((le_max_right _ _).trans hPN) hTlow hT t ht t ht
  have hsum : ((logarithmicTaylorMixedPairs P t t).card : ℝ) ≤
      (A.card : ℝ)+((logarithmicTaylorNonzeroPairs P t t).card : ℝ) := by
    rw [logarithmicTaylorMixedPairs_split]
    exact_mod_cast Finset.card_union_le A (logarithmicTaylorNonzeroPairs P t t)
  have hpow : P.N^(3/4 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (3/4 : ℝ) ≤ 1)
  linarith only [hsum,hzero,hnz,hpow]

#print axioms logarithmicTaylorMixedPairs_card_self

def logarithmicTaylorNuAt (P : ZetaLargeValuePattern) (t : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) : ℝ :=
  ∑ n ∈ P.indices, GafniTao.heathBrownCellIndicator 7
    (Nat.ceil (P.N^(9/40 : ℝ))) (logarithmicTaylorPhase t) n α

def logarithmicTaylorNu (P : ZetaLargeValuePattern) (W : Finset ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) : ℝ :=
  ∑ t ∈ W, logarithmicTaylorNuAt P t α

def logarithmicTaylorOverlapIndicator (P : ZetaLargeValuePattern) (t u : ℝ)
    (p : ℕ × ℕ) : GafniTao.HeathBrownCoefficientTorus 7 → ℝ :=
  (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
    logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).indicator (fun _ => 1)

theorem integrable_logarithmicTaylorOverlapIndicator (P : ZetaLargeValuePattern)
    (t u : ℝ) (p : ℕ × ℕ) :
    Integrable (logarithmicTaylorOverlapIndicator P t u p)
      (GafniTao.heathBrownCoefficientMeasure 7) := by
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure 7) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  exact (integrable_const (1 : ℝ)).indicator
    ((GafniTao.measurableSet_heathBrownCoefficientCell 7 _ _ _).inter
      (GafniTao.measurableSet_heathBrownCoefficientCell 7 _ _ _))

#print axioms integrable_logarithmicTaylorOverlapIndicator

theorem logarithmicTaylorNuAt_mul (P : ZetaLargeValuePattern) (t u : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) :
    logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α =
      ∑ p ∈ P.indices.product P.indices, logarithmicTaylorOverlapIndicator P t u p α := by
  classical
  unfold logarithmicTaylorNuAt
  rw [Finset.sum_mul_sum]
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ha : α ∈ logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n
  <;> by_cases hb : α ∈ logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u m
  <;> simp only [logarithmicTaylorCell] at ha hb
  <;> simp [GafniTao.heathBrownCellIndicator,logarithmicTaylorOverlapIndicator,
    logarithmicTaylorCell,ha,hb]

#print axioms logarithmicTaylorNuAt_mul

theorem integrable_logarithmicTaylorNuAt_mul (P : ZetaLargeValuePattern) (t u : ℝ) :
    Integrable (fun α => logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α)
      (GafniTao.heathBrownCoefficientMeasure 7) := by
  have hh := integrable_finsetSum (P.indices.product P.indices)
    (fun p _ => integrable_logarithmicTaylorOverlapIndicator P t u p)
  apply hh.congr
  filter_upwards [] with α
  exact (logarithmicTaylorNuAt_mul P t u α).symm

#print axioms integrable_logarithmicTaylorNuAt_mul

theorem logarithmicTaylorCell_measureReal (P : ZetaLargeValuePattern)
    (hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ))) (t : ℝ) (n : ℕ) :
    (GafniTao.heathBrownCoefficientMeasure 7).real
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n) =
      64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21 := by
  unfold GafniTao.heathBrownCoefficientMeasure logarithmicTaylorCell
  rw [GafniTao.measureReal_heathBrownCoefficientCell_exact hH]
  norm_num [GafniTao.heathBrownCriticalMoment,div_eq_mul_inv]

#print axioms logarithmicTaylorCell_measureReal

theorem integral_logarithmicTaylorNuAt_mul_le (P : ZetaLargeValuePattern)
    (hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ))) (t u : ℝ) :
    (∫ α, logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α
      ∂(GafniTao.heathBrownCoefficientMeasure 7)) ≤
      ((logarithmicTaylorMixedPairs P t u).card : ℝ)*
        (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21) := by
  classical
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure 7) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  let S := P.indices.product P.indices
  let A := logarithmicTaylorMixedPairs P t u
  let μ := GafniTao.heathBrownCoefficientMeasure 7
  let v : ℝ := 64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21
  have hint (p : ℕ × ℕ) : (∫ α, logarithmicTaylorOverlapIndicator P t u p α ∂μ) =
      μ.real (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2) :=
    integral_indicator_one
      ((GafniTao.measurableSet_heathBrownCoefficientCell 7 _ _ _).inter
        (GafniTao.measurableSet_heathBrownCoefficientCell 7 _ _ _))
  have hterm (p : ℕ × ℕ) (hp : p ∈ S) :
      (∫ α, logarithmicTaylorOverlapIndicator P t u p α ∂μ) ≤ if p ∈ A then v else 0 := by
    rw [hint]
    by_cases hover : (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
        logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty
    · have hpA : p ∈ A := Finset.mem_filter.mpr ⟨hp,hover⟩
      rw [if_pos hpA]
      exact (measureReal_mono Set.inter_subset_left).trans_eq
        (logarithmicTaylorCell_measureReal P hH t p.1)
    · have hpA : p ∉ A := fun hh => hover (Finset.mem_filter.mp hh).2
      rw [if_neg hpA,Set.not_nonempty_iff_eq_empty.mp hover]
      simp
  have hAS : A ⊆ S := fun p hp => (Finset.mem_filter.mp hp).1
  simp_rw [logarithmicTaylorNuAt_mul]
  rw [integral_finsetSum _ (fun p _ => integrable_logarithmicTaylorOverlapIndicator P t u p)]
  calc
    _ ≤ ∑ p ∈ S, (if p ∈ A then v else 0) := Finset.sum_le_sum hterm
    _ = (A.card : ℝ)*v := by
      rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hAS,
        Finset.sum_const,nsmul_eq_mul]

#print axioms integral_logarithmicTaylorNuAt_mul_le

theorem logarithmicTaylorNu_sq (P : ZetaLargeValuePattern) (W : Finset ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) :
    (logarithmicTaylorNu P W α)^2 =
      ∑ t ∈ W, ∑ u ∈ W, logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α := by
  unfold logarithmicTaylorNu
  rw [pow_two,Finset.sum_mul_sum]

#print axioms logarithmicTaylorNu_sq

theorem integrable_logarithmicTaylorNu_sq (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    Integrable (fun α => (logarithmicTaylorNu P W α)^2)
      (GafniTao.heathBrownCoefficientMeasure 7) := by
  have hh := integrable_finsetSum W (fun t _ => integrable_finsetSum W
    (fun u _ => integrable_logarithmicTaylorNuAt_mul P t u))
  apply hh.congr
  filter_upwards [] with α
  exact (logarithmicTaylorNu_sq P W α).symm

#print axioms integrable_logarithmicTaylorNu_sq

theorem integral_logarithmicTaylorNu_sq_le (P : ZetaLargeValuePattern)
    (hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ))) (W : Finset ℝ) :
    (∫ α, (logarithmicTaylorNu P W α)^2 ∂(GafniTao.heathBrownCoefficientMeasure 7)) ≤
      (∑ t ∈ W, ∑ u ∈ W, ((logarithmicTaylorMixedPairs P t u).card : ℝ))*
        (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21) := by
  simp_rw [logarithmicTaylorNu_sq]
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum W
    (fun u _ => integrable_logarithmicTaylorNuAt_mul P t u))]
  simp_rw [integral_finsetSum _ (fun u _ => integrable_logarithmicTaylorNuAt_mul P _ u)]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun t _ => Finset.sum_le_sum
    (fun u _ => integral_logarithmicTaylorNuAt_mul_le P hH t u))

#print axioms integral_logarithmicTaylorNu_sq_le

theorem logarithmicTaylorNu_nonneg (P : ZetaLargeValuePattern) (W : Finset ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) : 0 ≤ logarithmicTaylorNu P W α := by
  exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg
    (fun n _ => GafniTao.heathBrownCellIndicator_nonneg 7 _ n (logarithmicTaylorPhase t) α))

#print axioms logarithmicTaylorNu_nonneg

theorem integrable_logarithmicTaylorNuAt (P : ZetaLargeValuePattern) (t : ℝ) :
    Integrable (logarithmicTaylorNuAt P t) (GafniTao.heathBrownCoefficientMeasure 7) :=
  integrable_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator 7 _ n _)

#print axioms integrable_logarithmicTaylorNuAt

theorem integrable_logarithmicTaylorNu (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    Integrable (logarithmicTaylorNu P W) (GafniTao.heathBrownCoefficientMeasure 7) :=
  integrable_finsetSum _ (fun t _ => integrable_logarithmicTaylorNuAt P t)

#print axioms integrable_logarithmicTaylorNu

theorem integral_logarithmicTaylorNu (P : ZetaLargeValuePattern)
    (hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ))) (W : Finset ℝ) :
    (∫ α, logarithmicTaylorNu P W α ∂(GafniTao.heathBrownCoefficientMeasure 7)) =
      (W.card : ℝ)*(P.indices.card : ℝ)*(64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21) := by
  unfold logarithmicTaylorNu
  rw [integral_finsetSum _ (fun t _ => integrable_logarithmicTaylorNuAt P t)]
  have hint (t : ℝ) : (∫ α, logarithmicTaylorNuAt P t α
      ∂(GafniTao.heathBrownCoefficientMeasure 7)) =
      (P.indices.card : ℝ)*(64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21) := by
    unfold logarithmicTaylorNuAt
    rw [integral_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator 7 _ n _)]
    simp_rw [GafniTao.integral_heathBrownCellIndicator]
    change (∑ n ∈ P.indices, (GafniTao.heathBrownCoefficientMeasure 7).real
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n)) = _
    simp_rw [logarithmicTaylorCell_measureReal P hH t]
    rw [Finset.sum_const,nsmul_eq_mul]
  simp_rw [hint]
  rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]

#print axioms integral_logarithmicTaylorNu

theorem integral_logarithmicTaylorNu_sq_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      (∫ α, (logarithmicTaylorNu P W α)^2 ∂(GafniTao.heathBrownCoefficientMeasure 7)) ≤
        (3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
          (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21) := by
  classical
  obtain ⟨C₀,hC₀,hfar⟩ := logarithmicTaylorMixedPairs_card_far
  obtain ⟨C₁,_,hself⟩ := logarithmicTaylorMixedPairs_card_self
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT W hW hsep
  have hceil : (1 : ℝ) < (Nat.ceil (P.N^(9/40 : ℝ)) : ℝ) :=
    (Real.one_lt_rpow P.one_lt_N (by norm_num : (0 : ℝ) < 9/40)).trans_le (Nat.le_ceil _)
  have hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ)) := by
    have hh : 1 < Nat.ceil (P.N^(9/40 : ℝ)) := by exact_mod_cast hceil
    omega
  have hrow (t : ℝ) (ht : t ∈ W) :
      (∑ u ∈ W, ((logarithmicTaylorMixedPairs P t u).card : ℝ)) ≤
        3*P.N+(W.card : ℝ)*P.N^(19/20 : ℝ) := by
    calc
      _ ≤ ∑ u ∈ W, ((if u = t then 3*P.N else 0)+P.N^(19/20 : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases heq : u = t
        · subst u
          rw [if_pos rfl]
          exact (hself P ((le_max_right _ _).trans hPN) hTlow hT t (hW ht)).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _))
        · rw [if_neg heq,zero_add]
          exact hfar P ((le_max_left _ _).trans hPN) hTlow hT t (hW ht) u (hW hu)
            (hsep ht hu (Ne.symm heq))
      _ = _ := by simp [Finset.sum_add_distrib,ht,nsmul_eq_mul]
  have hsum : (∑ t ∈ W, ∑ u ∈ W, ((logarithmicTaylorMixedPairs P t u).card : ℝ)) ≤
      3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ) := by
    calc
      _ ≤ ∑ _t ∈ W, (3*P.N+(W.card : ℝ)*P.N^(19/20 : ℝ)) := Finset.sum_le_sum hrow
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring
  exact (integral_logarithmicTaylorNu_sq_le P hH W).trans
    (mul_le_mul_of_nonneg_right hsum (by positivity))

#print axioms integral_logarithmicTaylorNu_sq_uniform

theorem logarithmicTaylor_joint_weyl_mean :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      ∀ Q : ℕ, Q ≤ Nat.ceil (P.N^(9/40 : ℝ)) →
      (∫⁻ α : GafniTao.HeathBrownCoefficientTorus 7,
        ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 Q α‖*
          ENNReal.ofReal (logarithmicTaylorNu P W α)
          ∂(GafniTao.heathBrownCoefficientMeasure 7)) ≤
        (GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ))) : ENNReal)^(1/42 : ℝ)*
        ENNReal.ofReal ((3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
          (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(1/42 : ℝ)*
        ENNReal.ofReal ((W.card : ℝ)*(P.indices.card : ℝ)*
          (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(20/21 : ℝ) := by
  obtain ⟨C,hC,hsecond⟩ := integral_logarithmicTaylorNu_sq_uniform
  refine ⟨C,hC,?_⟩
  intro P hPN hTlow hT W hW hsep Q hQ
  let μ := GafniTao.heathBrownCoefficientMeasure 7
  let A : GafniTao.HeathBrownCoefficientTorus 7 → ENNReal :=
    fun α => ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 Q α‖
  let B : GafniTao.HeathBrownCoefficientTorus 7 → ENNReal :=
    fun α => ENNReal.ofReal (logarithmicTaylorNu P W α)
  have hA : AEMeasurable A μ :=
    (ENNReal.continuous_ofReal.comp
      (GafniTao.continuous_fordVinogradovWeylSum 6 Q).norm).aemeasurable
  have hB : AEMeasurable B μ :=
    (integrable_logarithmicTaylorNu P W).aemeasurable.ennreal_ofReal
  have hholder := GafniTao.heathBrown_lintegral_mul_le_three_moments hA hB
    (by norm_num : 1 ≤ (21 : ℕ))
  have hAI : (∫⁻ α, A α^42 ∂μ) = (GafniTao.fordVinogradovMomentNat 21 6 Q : ENNReal) :=
    GafniTao.ford_vinogradov_lintegral_mean_eq 21 6 Q
  have hceil : (1 : ℝ) < (Nat.ceil (P.N^(9/40 : ℝ)) : ℝ) :=
    (Real.one_lt_rpow P.one_lt_N (by norm_num : (0 : ℝ) < 9/40)).trans_le (Nat.le_ceil _)
  have hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ)) := by
    have hh : 1 < Nat.ceil (P.N^(9/40 : ℝ)) := by exact_mod_cast hceil
    omega
  have hBI : (∫⁻ α, B α ∂μ) = ENNReal.ofReal ((W.card : ℝ)*(P.indices.card : ℝ)*
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)) := by
    rw [← integral_logarithmicTaylorNu P hH W]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_logarithmicTaylorNu P W)
      (Filter.Eventually.of_forall (logarithmicTaylorNu_nonneg P W))).symm
  have hBII : (∫⁻ α, B α^2 ∂μ) ≤ ENNReal.ofReal
      ((3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
        (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)) := by
    calc
      _ = ∫⁻ α, ENNReal.ofReal ((logarithmicTaylorNu P W α)^2) ∂μ := by
        apply lintegral_congr
        intro α
        exact (ENNReal.ofReal_pow (logarithmicTaylorNu_nonneg P W α) 2).symm
      _ = ENNReal.ofReal (∫ α, (logarithmicTaylorNu P W α)^2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_logarithmicTaylorNu_sq P W)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsecond P hPN hTlow hT W hW hsep)
  have hmono : (GafniTao.fordVinogradovMomentNat 21 6 Q : ENNReal) ≤
      (GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ))) : ENNReal) := by
    exact_mod_cast GafniTao.fordVinogradovMomentNat_mono 21 6 hQ
  norm_num at hholder
  rw [hAI,hBI] at hholder
  exact hholder.trans (by gcongr)

#print axioms logarithmicTaylor_joint_weyl_mean

theorem logarithmicTaylor_separated_subset :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      ∃ W : Finset ℝ, W ⊆ P.ordinates ∧
        (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) ∧
        (P.ordinates.card : ℝ) ≤ 2*(W.card : ℝ)*P.N^(1/20 : ℝ) := by
  classical
  obtain ⟨C,hC,hlocal⟩ := ordinate_local_count_pair
  refine ⟨C,hC,?_⟩
  intro P hPN hV
  let L := P.N^(10/3 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos (zero_lt_one.trans P.one_lt_N) _
  let F := P.ordinates.powerset.filter (fun W : Finset ℝ =>
    (W : Set ℝ).Pairwise (fun t u => L < |t-u|))
  obtain ⟨W,hmax⟩ := F.exists_maximal
    ⟨∅,Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _,by simp⟩⟩
  have hW : W ⊆ P.ordinates := Finset.mem_powerset.mp (Finset.mem_filter.mp hmax.1).1
  have hsep : (W : Set ℝ).Pairwise (fun t u => L < |t-u|) := (Finset.mem_filter.mp hmax.1).2
  have hcover (t : ℝ) (ht : t ∈ P.ordinates) : ∃ u ∈ W, |t-u| ≤ L := by
    by_contra! hh
    have htW : t ∉ W := by
      intro htW
      have ha := hh t htW
      rw [sub_self,abs_zero] at ha
      linarith only [ha,hL]
    have hi : insert t W ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨ht,hW⟩),?_⟩
      rw [Finset.coe_insert]
      apply hsep.insert
      intro u hu htu
      exact ⟨hh u hu,by simpa only [abs_sub_comm] using hh u hu⟩
    exact htW ((hmax.2 hi (Finset.subset_insert t W)) (Finset.mem_insert_self t W))
  let B (u : ℝ) := P.ordinates.filter (fun t => |t-u| ≤ L)
  have hB (u : ℝ) : ((B u).card : ℝ) ≤ 2*P.N^(1/20 : ℝ) := by
    let A₀ := P.ordinates.filter (fun t => u-L ≤ t ∧ t ≤ (u-L)+L)
    let A₁ := P.ordinates.filter (fun t => u ≤ t ∧ t ≤ u+L)
    have hsub : B u ⊆ A₀ ∪ A₁ := by
      intro t ht
      obtain ⟨htS,habs⟩ := Finset.mem_filter.mp ht
      have hab := abs_le.mp habs
      by_cases htu : t ≤ u
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htS,by constructor <;> linarith only [hab.1,htu]⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htS,by constructor <;> linarith only [hab.2,htu]⟩)
    have hc : ((B u).card : ℝ) ≤ (A₀.card : ℝ)+(A₁.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le A₀ A₁)
    have h₀ := hlocal P hPN hV (u-L)
    have h₁ := hlocal P hPN hV u
    change (A₀.card : ℝ) ≤ P.N^(1/20 : ℝ) at h₀
    change (A₁.card : ℝ) ≤ P.N^(1/20 : ℝ) at h₁
    linarith only [hc,h₀,h₁]
  have hsub : P.ordinates ⊆ W.biUnion B := by
    intro t ht
    obtain ⟨u,hu,hgap⟩ := hcover t ht
    exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨ht,hgap⟩⟩
  have hc : (P.ordinates.card : ℝ) ≤ ∑ u ∈ W, ((B u).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  refine ⟨W,hW,hsep,?_⟩
  calc
    _ ≤ ∑ u ∈ W, ((B u).card : ℝ) := hc
    _ ≤ ∑ _u ∈ W, 2*P.N^(1/20 : ℝ) := Finset.sum_le_sum (fun u _ => hB u)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring

#print axioms logarithmicTaylor_separated_subset

theorem norm_interval_phase_average_sub_le (f : ℝ → ℝ)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (H : ℕ) :
    ‖(∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Icc a b,
        GafniTao.heathBrownPhase (f ((n+h : ℕ) : ℝ))) -
      (H : ℂ)*(∑ n ∈ Finset.Icc a b, GafniTao.heathBrownPhase (f n))‖ ≤
      (H : ℝ)*((H : ℝ)+1) := by
  classical
  let J := b+1-a
  let c := a-1
  let g : ℝ → ℝ := fun x => f (x+(c : ℝ))
  have hJ : 1 ≤ J := by dsimp only [J]; omega
  have hleft : 1+c = a := by dsimp only [c]; omega
  have hright : J+c = b := by dsimp only [J,c]; omega
  have himage : (Finset.Icc 1 J).image (fun n => n+c) = Finset.Icc a b := by
    rw [Finset.image_add_right_Icc,hleft,hright]
  have hshift (h : ℕ) : GafniTao.heathBrownShiftedExponentialSum J g h =
      ∑ n ∈ Finset.Icc a b, GafniTao.heathBrownPhase (f ((n+h : ℕ) : ℝ)) := by
    unfold GafniTao.heathBrownShiftedExponentialSum
    rw [← himage,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      dsimp only [g]
      congr 2
      push_cast
      ring
    · intro n hn m hm heq
      exact Nat.add_right_cancel heq
  have hbase : GafniTao.heathBrownExponentialSum J g =
      ∑ n ∈ Finset.Icc a b, GafniTao.heathBrownPhase (f n) := by
    have hh := hshift 0
    simpa only [GafniTao.heathBrownShiftedExponentialSum_zero,Nat.add_zero] using hh
  have hh := GafniTao.norm_heathBrown_translation_average_sub_le hJ H g
  simpa only [hshift,hbase] using hh

#print axioms norm_interval_phase_average_sub_le

theorem logarithmicTaylorPhase_seventh_norm {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ‖iteratedDeriv 7 (logarithmicTaylorPhase t) x‖ = 360*t/(Real.pi*x^7) := by
  have hh := logarithmicTaylorPhase_coordinate 6 t hx
  norm_num at hh
  have he : iteratedDeriv 7 (logarithmicTaylorPhase t) x = -(360*t/(Real.pi*x^7)) := by
    have he := (div_eq_iff (by norm_num : (5040 : ℝ) ≠ 0)).mp hh
    calc
      _ = _ := he
      _ = _ := by ring
  rw [he,norm_neg,Real.norm_eq_abs,abs_of_pos (by positivity)]

#print axioms logarithmicTaylorPhase_seventh_norm

theorem logarithmicTaylor_shifted_Abel (P : ZetaLargeValuePattern)
    {t : ℝ} (ht : t ∈ P.ordinates) {n H : ℕ} (hn : n ∈ P.indices) (hH : 1 ≤ H) :
    ‖∑ h ∈ Finset.Icc 1 H,
      GafniTao.heathBrownPhase (logarithmicTaylorPhase t ((n+h : ℕ) : ℝ))‖ ≤
      ‖GafniTao.heathBrownWeylSum 7 H
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖+
      (1440*P.T/P.N^7*(H : ℝ)^6)*
        ∑ j ∈ Finset.Ico 1 H, ‖GafniTao.heathBrownWeylSum 7 j
          (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖ := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hnb := (P.mem_indices_iff n).mp hn
  have hnp : 0 < (n : ℝ) := hNp.trans_le hnb.1
  have ht' : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have htp := P.T_pos.trans_le ht'.1
  have hsmooth : ContDiffOn ℝ (7 : ℕ) (logarithmicTaylorPhase t) (Set.Ioi 0) := by
    intro x hx
    have hl : ContDiffAt ℝ (7 : ℕ) Real.log x := Real.contDiffAt_log.mpr (ne_of_gt hx)
    exact (contDiffAt_const.mul hl).contDiffWithinAt
  have hsmoothD : ContDiffOn ℝ (6 : ℕ) (deriv (logarithmicTaylorPhase t)) (Set.Ioi 0) :=
    hsmooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfat : ContDiffAt ℝ (5 : ℕ) (deriv (logarithmicTaylorPhase t)) n :=
    (hsmoothD.contDiffAt (Ioi_mem_nhds hnp)).of_le (by norm_num)
  have hfd (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) H) :
      HasDerivAt (logarithmicTaylorPhase t)
        (deriv (logarithmicTaylorPhase t) ((n : ℝ)+x)) ((n : ℝ)+x) := by
    have hnx : 0 < (n : ℝ)+x := by linarith only [hnp,hx.1]
    exact ((hsmooth.contDiffAt (Ioi_mem_nhds hnx)).differentiableAt (by norm_num)).hasDerivAt
  have hfon (x : ℝ) (_hx : x ∈ Set.Icc (1 : ℝ) H) :
      ContDiffOn ℝ (6 : ℕ) (deriv (logarithmicTaylorPhase t)) (Set.Icc (n : ℝ) ((n : ℝ)+x)) :=
    hsmoothD.mono (fun ξ hξ => hnp.trans_le hξ.1)
  have hderiv (x : ℝ) (_hx : x ∈ Set.Icc (1 : ℝ) H) (ξ : ℝ)
      (hξ : ξ ∈ Set.Ioo (n : ℝ) ((n : ℝ)+x)) :
      ‖iteratedDeriv 7 (logarithmicTaylorPhase t) ξ‖ ≤ 720*(P.T/(Real.pi*P.N^7)) := by
    have hξp : 0 < ξ := hnp.trans hξ.1
    rw [logarithmicTaylorPhase_seventh_norm htp hξp]
    calc
      _ ≤ 360*(2*P.T)/(Real.pi*P.N^7) := by
        apply div_le_div₀ (by positivity) (by linarith only [ht'.2]) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNp.le (hnb.1.trans hξ.1.le) 7) Real.pi_pos.le
      _ = _ := by ring
  have hh := GafniTao.heathBrown_shifted_source_sum_norm_le_partial
    (k := 7) (H := H) (A := 720) (lambda := P.T/(Real.pi*P.N^7))
    (by norm_num) hH hfat hfd hfon hderiv
  simp only [show (7 : ℕ)-1 = 6 by norm_num,Nat.cast_add] at hh ⊢
  simp_rw [GafniTao.norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum (by norm_num : 1 ≤ (7 : ℕ))]
  have hc : 2*Real.pi*(720*(P.T/(Real.pi*P.N^7))*(H : ℝ)^6) =
      1440*P.T/P.N^7*(H : ℝ)^6 := by field_simp; norm_num
  rw [hc] at hh
  exact hh

#print axioms logarithmicTaylor_shifted_Abel

theorem logarithmicTaylor_actual_Abel (P : ZetaLargeValuePattern)
    {t : ℝ} (ht : t ∈ P.ordinates) {H : ℕ} (hH : 1 ≤ H) :
    (H : ℝ)*P.V ≤
      (∑ n ∈ P.indices, ‖GafniTao.heathBrownWeylSum 7 H
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖)+
      (1440*P.T/P.N^7*(H : ℝ)^6)*
        (∑ j ∈ Finset.Ico 1 H, ∑ n ∈ P.indices, ‖GafniTao.heathBrownWeylSum 7 j
          (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖)+
      (H : ℝ)*((H : ℝ)+1) := by
  classical
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hlarge : P.V ≤ ‖zetaAnchor P t‖ := by rw [zetaAnchor_eq_pattern]; exact P.large t ht
  have hnonempty : P.active.Nonempty := by
    by_contra hh
    have he : P.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    simp only [zetaAnchor,he,Finset.sum_empty,norm_zero] at hlarge
    linarith [P.V_pos]
  obtain ⟨a,b,habactive⟩ := P.active_isInterval
  have hab : a ≤ b := by
    obtain ⟨n,hn⟩ := hnonempty
    rw [habactive] at hn
    exact (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
  have ha : 1 ≤ a := P.index_pos (P.active_subset (by rw [habactive]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩))
  have hsource : (∑ n ∈ Finset.Icc a b,
      GafniTao.heathBrownPhase (logarithmicTaylorPhase t n)) = zetaAnchor P t := by
    rw [zetaAnchor,habactive]
    apply Finset.sum_congr rfl
    intro n hn
    exact logarithmicTaylorPhase_character (P.index_pos (P.active_subset (by simpa only [habactive] using hn))) t
  let U : ℂ := ∑ n ∈ P.active, ∑ h ∈ Finset.Icc 1 H,
    GafniTao.heathBrownPhase (logarithmicTaylorPhase t ((n+h : ℕ) : ℝ))
  have hboundary : ‖U-(H : ℂ)*zetaAnchor P t‖ ≤ (H : ℝ)*((H : ℝ)+1) := by
    have hh := norm_interval_phase_average_sub_le (logarithmicTaylorPhase t) ha hab H
    rw [hsource,Finset.sum_comm] at hh
    simpa only [U,habactive] using hh
  have hentry : (H : ℝ)*P.V ≤ ‖U‖+(H : ℝ)*((H : ℝ)+1) := by
    calc
      _ ≤ (H : ℝ)*‖zetaAnchor P t‖ := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg _)
      _ = ‖(H : ℂ)*zetaAnchor P t‖ := by rw [norm_mul,Complex.norm_natCast]
      _ = ‖U-(U-(H : ℂ)*zetaAnchor P t)‖ := by congr 1; ring
      _ ≤ ‖U‖+‖U-(H : ℂ)*zetaAnchor P t‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hboundary
  let c : ℝ := 1440*P.T/P.N^7*(H : ℝ)^6
  let F (j n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 7 j
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hsum : ‖U‖ ≤ (∑ n ∈ P.indices, F H n)+c*(∑ j ∈ Finset.Ico 1 H, ∑ n ∈ P.indices, F j n) := by
    calc
      _ ≤ ∑ n ∈ P.active, ‖∑ h ∈ Finset.Icc 1 H,
          GafniTao.heathBrownPhase (logarithmicTaylorPhase t ((n+h : ℕ) : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ P.active, (F H n+c*∑ j ∈ Finset.Ico 1 H, F j n) :=
        Finset.sum_le_sum (fun n hn => logarithmicTaylor_shifted_Abel P ht (P.active_subset hn) hH)
      _ ≤ ∑ n ∈ P.indices, (F H n+c*∑ j ∈ Finset.Ico 1 H, F j n) :=
        Finset.sum_le_sum_of_subset_of_nonneg P.active_subset (fun n _ _ => by dsimp only [F]; positivity)
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
  exact hentry.trans (add_le_add hsum le_rfl)

#print axioms logarithmicTaylor_actual_Abel

theorem logarithmicTaylor_joint_cellwise_le (P : ZetaLargeValuePattern)
    (W : Finset ℝ) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ Nat.ceil (P.N^(9/40 : ℝ)))
    (α : GafniTao.HeathBrownCoefficientTorus 7) :
    (∑ t ∈ W, ∑ n ∈ P.indices,
      GafniTao.heathBrownCellIndicator 7 (Nat.ceil (P.N^(9/40 : ℝ)))
        (logarithmicTaylorPhase t) n α *
      ‖GafniTao.heathBrownWeylSum 7 Q
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖) ≤
      ‖GafniTao.heathBrownWeylSum 7 Q α‖*logarithmicTaylorNu P W α+
      (98*Real.pi/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ))*
        ∑ j ∈ Finset.Ico 1 Q,
          ‖GafniTao.heathBrownWeylSum 7 j α‖*logarithmicTaylorNu P W α := by
  classical
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hceil : (1 : ℝ) < (H : ℝ) :=
    (Real.one_lt_rpow P.one_lt_N (by norm_num : (0 : ℝ) < 9/40)).trans_le (Nat.le_ceil _)
  have hH : 2 ≤ H := by
    have hh : 1 < H := by exact_mod_cast hceil
    omega
  let c : ℝ := 98*Real.pi/(H : ℝ)
  let F (j : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 7 j α‖
  let I (t : ℝ) (n : ℕ) : ℝ :=
    GafniTao.heathBrownCellIndicator 7 H (logarithmicTaylorPhase t) n α
  have hpoint (t : ℝ) (n : ℕ) :
      I t n*‖GafniTao.heathBrownWeylSum 7 Q
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖ ≤
        I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
    by_cases hα : α ∈ GafniTao.heathBrownCoefficientCell 7 H (logarithmicTaylorPhase t) n
    · have hi : I t n = 1 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      rw [hi,one_mul,one_mul]
      have hh := GafniTao.norm_heathBrown_centerWeyl_le hH hQ hQH hα
      norm_num only [Nat.cast_ofNat] at hh
      have he : 2*Real.pi*(49/(H : ℝ)) = c := by dsimp only [c]; ring
      simpa only [he,F] using hh
    · have hi : I t n = 0 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      simp only [hi,zero_mul,le_refl]
  calc
    _ ≤ ∑ t ∈ W, ∑ n ∈ P.indices, I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun n _ => hpoint t n))
    _ = (logarithmicTaylorNu P W α)*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
      simp_rw [← Finset.sum_mul]
      rfl
    _ = _ := by
      rw [mul_add]
      simp_rw [← Finset.sum_mul]
      dsimp only [c,F,H]
      ring

#print axioms logarithmicTaylor_joint_cellwise_le

def logarithmicTaylorIntegratedWeyl (P : ZetaLargeValuePattern)
    (W : Finset ℝ) (Q : ℕ) : ENNReal :=
  ∫⁻ α : GafniTao.HeathBrownCoefficientTorus 7,
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 Q α‖*
      ENNReal.ofReal (logarithmicTaylorNu P W α)
      ∂(GafniTao.heathBrownCoefficientMeasure 7)

theorem measurable_logarithmicTaylorNu (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    Measurable (logarithmicTaylorNu P W) := by
  unfold logarithmicTaylorNu logarithmicTaylorNuAt
  exact Finset.measurable_sum W (fun t _ => Finset.measurable_sum P.indices
    (fun n _ => GafniTao.measurable_heathBrownCellIndicator 7 _ n (logarithmicTaylorPhase t)))

#print axioms measurable_logarithmicTaylorNu

theorem logarithmicTaylor_joint_center_integral (P : ZetaLargeValuePattern)
    (W : Finset ℝ) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ Nat.ceil (P.N^(9/40 : ℝ))) :
    ENNReal.ofReal (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)*
      (∑ t ∈ W, ∑ n ∈ P.indices,
        ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 Q
          (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖) ≤
      logarithmicTaylorIntegratedWeyl P W Q+
        ENNReal.ofReal (98*Real.pi/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ))*
          ∑ j ∈ Finset.Ico 1 Q, logarithmicTaylorIntegratedWeyl P W j := by
  classical
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let μ := GafniTao.heathBrownCoefficientMeasure 7
  let c : ℝ := 98*Real.pi/(H : ℝ)
  let v : ℝ := 64/(H : ℝ)^21
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let F (j : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 7) : ENNReal :=
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 j α‖*
      ENNReal.ofReal (logarithmicTaylorNu P W α)
  let I (t : ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 7) : ℝ :=
    GafniTao.heathBrownCellIndicator 7 H (logarithmicTaylorPhase t) n α
  let K (t : ℝ) (n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 7 Q
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖
  have hI (t : ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 7) : 0 ≤ I t n α :=
    GafniTao.heathBrownCellIndicator_nonneg 7 H n (logarithmicTaylorPhase t) α
  have hK (t : ℝ) (n : ℕ) : 0 ≤ K t n := norm_nonneg _
  have hpoint (α : GafniTao.HeathBrownCoefficientTorus 7) :
      (∑ t ∈ W, ∑ n ∈ P.indices, ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) ≤
        F Q α+ENNReal.ofReal c*∑ j ∈ Finset.Ico 1 Q, F j α := by
    have hh := ENNReal.ofReal_le_ofReal (logarithmicTaylor_joint_cellwise_le P W hQ hQH α)
    change ENNReal.ofReal (∑ t ∈ W, ∑ n ∈ P.indices, I t n α*K t n) ≤ _ at hh
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => Finset.sum_nonneg
      (fun n _ => mul_nonneg (hI t n α) (hK t n)))] at hh
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hI _ n α) (hK _ n)),
      ENNReal.ofReal_mul (hI _ _ α)] at hh
    have hprod (j : ℕ) : 0 ≤ ‖GafniTao.heathBrownWeylSum 7 j α‖*logarithmicTaylorNu P W α :=
      mul_nonneg (norm_nonneg _) (logarithmicTaylorNu_nonneg P W α)
    rw [ENNReal.ofReal_add (hprod Q) (mul_nonneg hc (Finset.sum_nonneg (fun j _ => hprod j))),
      ENNReal.ofReal_mul (norm_nonneg _),ENNReal.ofReal_mul hc,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hprod j)] at hh
    simp_rw [ENNReal.ofReal_mul (norm_nonneg _)] at hh
    exact hh
  have hceil : (1 : ℝ) < (H : ℝ) :=
    (Real.one_lt_rpow P.one_lt_N (by norm_num : (0 : ℝ) < 9/40)).trans_le (Nat.le_ceil _)
  have hH : 2 ≤ H := by
    have hh : 1 < H := by exact_mod_cast hceil
    omega
  have hcell (t : ℝ) (n : ℕ) : μ (GafniTao.heathBrownCoefficientCell 7 H (logarithmicTaylorPhase t) n) =
      ENNReal.ofReal v := by
    have hh := GafniTao.measure_heathBrownCoefficientCell_exact (k := 7) hH (logarithmicTaylorPhase t) (n : ℝ)
    simpa only [μ,v,GafniTao.heathBrownCoefficientMeasure,GafniTao.heathBrownCriticalMoment,
      show 7-1 = (6 : ℕ) by norm_num,show 7*6/2 = (21 : ℕ) by norm_num,
      show (2 : ℝ)^6 = 64 by norm_num,div_eq_mul_inv] using hh
  have hmeas (t : ℝ) (n : ℕ) : Measurable (fun α => ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) :=
    (GafniTao.measurable_heathBrownCellIndicator 7 H n (logarithmicTaylorPhase t)).ennreal_ofReal.mul measurable_const
  have hleft : (∫⁻ α, ∑ t ∈ W, ∑ n ∈ P.indices,
      ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n) ∂μ) =
      ENNReal.ofReal v*(∑ t ∈ W, ∑ n ∈ P.indices, ENNReal.ofReal (K t n)) := by
    rw [lintegral_finsetSum W (fun t _ => Finset.measurable_sum P.indices (fun n _ => hmeas t n))]
    simp_rw [lintegral_finsetSum P.indices (fun n _ => hmeas _ n)]
    simp_rw [I,μ,GafniTao.lintegral_heathBrownCellIndicator_mul_const]
    change (∑ t ∈ W, ∑ n ∈ P.indices, μ (GafniTao.heathBrownCoefficientCell 7 H
      (logarithmicTaylorPhase t) n)*ENNReal.ofReal (K t n)) = _
    simp_rw [hcell,← Finset.mul_sum]
  have hF (j : ℕ) : Measurable (F j) :=
    (ENNReal.continuous_ofReal.comp (GafniTao.continuous_fordVinogradovWeylSum 6 j).norm).measurable.mul
      (measurable_logarithmicTaylorNu P W).ennreal_ofReal
  have hh := lintegral_mono (μ := μ) hpoint
  rw [hleft,lintegral_add_left (hF Q),lintegral_const_mul _
    (Finset.measurable_sum (Finset.Ico 1 Q) (fun j _ => hF j)),
    lintegral_finsetSum (Finset.Ico 1 Q) (fun j _ => hF j)] at hh
  exact hh

#print axioms logarithmicTaylor_joint_center_integral

def logarithmicTaylorJointMajorant (P : ZetaLargeValuePattern) (W : Finset ℝ) : ℝ :=
  (GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ))) : ℝ)^(1/42 : ℝ)*
    ((3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(1/42 : ℝ)*
    ((W.card : ℝ)*(P.indices.card : ℝ)*
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(20/21 : ℝ)

theorem logarithmicTaylor_joint_center_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      ∀ Q : ℕ, 1 ≤ Q → Q ≤ Nat.ceil (P.N^(9/40 : ℝ)) →
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)*
        (∑ t ∈ W, ∑ n ∈ P.indices, ‖GafniTao.heathBrownWeylSum 7 Q
          (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖) ≤
        (1+98*Real.pi)*logarithmicTaylorJointMajorant P W := by
  classical
  obtain ⟨C,hC,hmean⟩ := logarithmicTaylor_joint_weyl_mean
  refine ⟨C,hC,?_⟩
  intro P hPN hTlow hT W hW hsep Q hQ hQH
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let v : ℝ := 64/(H : ℝ)^21
  let c : ℝ := 98*Real.pi/(H : ℝ)
  let E : ℝ := (3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*v
  let B : ℝ := (W.card : ℝ)*(P.indices.card : ℝ)*v
  let J := GafniTao.fordVinogradovMomentNat 21 6 H
  let M : ENNReal := (J : ENNReal)^(1/42 : ℝ)*ENNReal.ofReal E^(1/42 : ℝ)*
    ENNReal.ofReal B^(20/21 : ℝ)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : M ≠ ∞ := by dsimp only [M]; finiteness
  have hI (j : ℕ) (hj : j ≤ H) : logarithmicTaylorIntegratedWeyl P W j ≤ M :=
    hmean P hPN hTlow hT W hW hsep j hj
  have htail : (∑ j ∈ Finset.Ico 1 Q, logarithmicTaylorIntegratedWeyl P W j) ≤ (H : ENNReal)*M := by
    calc
      _ ≤ ∑ _j ∈ Finset.Ico 1 Q, M := Finset.sum_le_sum (fun j hj =>
        hI j ((Finset.mem_Ico.mp hj).2.le.trans hQH))
      _ = ((Finset.Ico 1 Q).card : ENNReal)*M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_left
        exact_mod_cast (show (Finset.Ico 1 Q).card ≤ H by simp only [Nat.card_Ico]; omega)
  have hh := (logarithmicTaylor_joint_center_integral P W hQ hQH).trans
    (add_le_add (hI Q hQH) (mul_le_mul_right htail (ENNReal.ofReal c)))
  let S : ℝ := ∑ t ∈ W, ∑ n ∈ P.indices, ‖GafniTao.heathBrownWeylSum 7 Q
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have heleft : ENNReal.ofReal (v*S) = ENNReal.ofReal v*
      (∑ t ∈ W, ∑ n ∈ P.indices, ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 7 Q
        (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖) := by
    rw [ENNReal.ofReal_mul hv]
    congr 1
    dsimp only [S]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  change ENNReal.ofReal v*_ ≤ M+ENNReal.ofReal c*((H : ENNReal)*M) at hh
  rw [← heleft,show M+ENNReal.ofReal c*((H : ENNReal)*M) =
    (1+ENNReal.ofReal c*(H : ENNReal))*M by ring] at hh
  have hr := ENNReal.toReal_mono (show (1+ENNReal.ofReal c*(H : ENNReal))*M ≠ ∞ by finiteness) hh
  rw [ENNReal.toReal_ofReal (mul_nonneg hv hS),ENNReal.toReal_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,ENNReal.toReal_natCast] at hr
  have hmreal : M.toReal = logarithmicTaylorJointMajorant P W := by
    dsimp only [M]
    simp only [ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hE,ENNReal.toReal_ofReal hB]
    rfl
  have hHr : (0 : ℝ) < H := by
    have hHpos : 0 < H := by omega
    exact_mod_cast hHpos
  have hcoef : 1+c*(H : ℝ) = 1+98*Real.pi := by dsimp only [c]; field_simp
  rw [hmreal,hcoef] at hr
  exact hr

#print axioms logarithmicTaylor_joint_center_uniform

theorem logarithmicTaylor_joint_source :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      let H := Nat.ceil (P.N^(9/40 : ℝ))
      let v : ℝ := 64/(H : ℝ)^21
      v*(H : ℝ)*(W.card : ℝ)*P.V ≤
        (1+1440*P.T/P.N^7*(H : ℝ)^7)*(1+98*Real.pi)*logarithmicTaylorJointMajorant P W+
        v*(W.card : ℝ)*(H : ℝ)*((H : ℝ)+1) := by
  classical
  obtain ⟨C,hC,hcenter⟩ := logarithmicTaylor_joint_center_uniform
  refine ⟨C,hC,?_⟩
  intro P hPN hTlow hT W hW hsep
  dsimp only
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let v : ℝ := 64/(H : ℝ)^21
  let c : ℝ := 1440*P.T/P.N^7*(H : ℝ)^6
  let M := (1+98*Real.pi)*logarithmicTaylorJointMajorant P W
  let A (t : ℝ) (j : ℕ) : ℝ := ∑ n ∈ P.indices, ‖GafniTao.heathBrownWeylSum 7 j
    (GafniTao.heathBrownCoefficientCenter 7 (logarithmicTaylorPhase t) n)‖
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hH : 1 ≤ H := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hNp _)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hM : 0 ≤ M := by dsimp only [M,logarithmicTaylorJointMajorant]; positivity
  have hpartial (j : ℕ) (hj : 1 ≤ j) (hjH : j ≤ H) : v*(∑ t ∈ W, A t j) ≤ M :=
    hcenter P hPN hTlow hT W hW hsep j hj hjH
  have htail : (∑ j ∈ Finset.Ico 1 H, v*(∑ t ∈ W, A t j)) ≤ (H : ℝ)*M := by
    calc
      _ ≤ ∑ _j ∈ Finset.Ico 1 H, M := Finset.sum_le_sum (fun j hj =>
        hpartial j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2.le)
      _ = ((Finset.Ico 1 H).card : ℝ)*M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast
        (show (Finset.Ico 1 H).card ≤ H by simp only [Nat.card_Ico]; omega)) hM
  have hsum : (W.card : ℝ)*(H : ℝ)*P.V ≤
      (∑ t ∈ W, A t H)+c*(∑ j ∈ Finset.Ico 1 H, ∑ t ∈ W, A t j)+
      (W.card : ℝ)*((H : ℝ)*((H : ℝ)+1)) := by
    have hh := Finset.sum_le_sum (fun t ht => logarithmicTaylor_actual_Abel P (hW ht) hH)
    change (∑ _t ∈ W, (H : ℝ)*P.V) ≤
      ∑ t ∈ W, (A t H+c*(∑ j ∈ Finset.Ico 1 H, A t j)+(H : ℝ)*((H : ℝ)+1)) at hh
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hh
    rw [Finset.sum_comm (s := W) (t := Finset.Ico 1 H) (f := A)] at hh
    simpa only [mul_assoc] using hh
  calc
    _ = v*((W.card : ℝ)*(H : ℝ)*P.V) := by ring
    _ ≤ v*((∑ t ∈ W, A t H)+c*(∑ j ∈ Finset.Ico 1 H, ∑ t ∈ W, A t j)+
        (W.card : ℝ)*((H : ℝ)*((H : ℝ)+1))) := mul_le_mul_of_nonneg_left hsum hv
    _ = v*(∑ t ∈ W, A t H)+c*(∑ j ∈ Finset.Ico 1 H, v*(∑ t ∈ W, A t j))+
        v*(W.card : ℝ)*(H : ℝ)*((H : ℝ)+1) := by rw [← Finset.mul_sum]; ring
    _ ≤ M+c*((H : ℝ)*M)+v*(W.card : ℝ)*(H : ℝ)*((H : ℝ)+1) :=
      add_le_add (add_le_add (hpartial H hH le_rfl) (mul_le_mul_of_nonneg_left htail hc)) le_rfl
    _ = _ := by dsimp only [M,c]; ring

#print axioms logarithmicTaylor_joint_source

private theorem logarithmicTaylor_source_scales :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.T ≤ P.N^(27/5 : ℝ) → P.N^(1951/2000 : ℝ) ≤ P.V →
      let H := Nat.ceil (P.N^(9/40 : ℝ))
      (H : ℝ) ≤ P.N ∧ 1440*P.T/P.N^7*(H : ℝ)^7 ≤ 1 ∧
        (H : ℝ)+1 ≤ P.V/2 := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 184320 (by norm_num) 0 (η := 1/40) (by norm_num))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 6 (by norm_num) 0 (η := 1501/2000) (by norm_num))
  refine ⟨max 1 (max N₀ N₁),le_max_left _ _,?_⟩
  intro P hPN hT hV
  dsimp only
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have ha : 184320 ≤ P.N^(1/40 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_left _ _).trans ((le_max_right _ _).trans hPN))
  have hb : 6 ≤ P.N^(1501/2000 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  have hone : 1 ≤ P.N^(9/40 : ℝ) := Real.one_le_rpow P.one_lt_N.le (by norm_num)
  have hH : (H : ℝ) ≤ 2*P.N^(9/40 : ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (9/40))
    change (H : ℝ) < P.N^(9/40 : ℝ)+1 at hh
    linarith only [hh,hone]
  have hHN : (H : ℝ) ≤ P.N := by
    have htwo : 2 ≤ P.N^(31/40 : ℝ) := (by linarith only [ha] : (2 : ℝ) ≤ P.N^(1/40 : ℝ)).trans
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num))
    calc
      _ ≤ 2*P.N^(9/40 : ℝ) := hH
      _ ≤ P.N^(31/40 : ℝ)*P.N^(9/40 : ℝ) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hHseven : (H : ℝ)^7 ≤ 128*P.N^(63/40 : ℝ) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg H) hH 7
    rw [mul_pow,← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  refine ⟨hHN,?_,?_⟩
  · calc
      _ ≤ 1440*P.N^(27/5 : ℝ)/P.N^7*(128*P.N^(63/40 : ℝ)) := by gcongr
      _ = 184320/P.N^(1/40 : ℝ) := by
        rw [← Real.rpow_natCast P.N 7]
        norm_num only [Nat.cast_ofNat]
        rw [show 1440*P.N^(27/5 : ℝ)/P.N^(7 : ℝ)*(128*P.N^(63/40 : ℝ)) =
          184320*(P.N^(27/5 : ℝ)*P.N^(63/40 : ℝ)/P.N^(7 : ℝ)) by ring]
        rw [← Real.rpow_add hNp,← Real.rpow_sub hNp]
        norm_num
        rw [Real.rpow_neg hNp.le]
        rfl
      _ ≤ 1 := (div_le_one (by positivity)).mpr ha
  · have hh : 6*P.N^(9/40 : ℝ) ≤ P.N^(1951/2000 : ℝ) := by
      calc
        _ ≤ P.N^(1501/2000 : ℝ)*P.N^(9/40 : ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
        _ = _ := by rw [← Real.rpow_add hNp]; norm_num
    change (H : ℝ)+1 ≤ _
    linarith only [hH,hone,hh,hV]

#print axioms logarithmicTaylor_source_scales

theorem logarithmicTaylor_joint_source_reduced :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)*
        (Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)*(W.card : ℝ)*P.V ≤
        (4*(1+98*Real.pi))*logarithmicTaylorJointMajorant P W := by
  obtain ⟨C₀,hC₀,hsource⟩ := logarithmicTaylor_joint_source
  obtain ⟨C₁,_,hscales⟩ := logarithmicTaylor_source_scales
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT hV W hW hsep
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let v : ℝ := 64/(H : ℝ)^21
  let L : ℝ := v*(H : ℝ)*(W.card : ℝ)*P.V
  let M := (1+98*Real.pi)*logarithmicTaylorJointMajorant P W
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hM : 0 ≤ M := by dsimp only [M,logarithmicTaylorJointMajorant]; positivity
  obtain ⟨_,hscale,hboundary⟩ := hscales P ((le_max_right _ _).trans hPN) hT hV
  have hh := hsource P ((le_max_left _ _).trans hPN) hTlow hT W hW hsep
  dsimp only at hh hscale hboundary
  rw [mul_assoc (1+1440*P.T/P.N^7*(H : ℝ)^7) (1+98*Real.pi)
    (logarithmicTaylorJointMajorant P W)] at hh
  change L ≤ (1+1440*P.T/P.N^7*(H : ℝ)^7)*M+
    v*(W.card : ℝ)*(H : ℝ)*((H : ℝ)+1) at hh
  have hfirst : (1+1440*P.T/P.N^7*(H : ℝ)^7)*M ≤ 2*M :=
    mul_le_mul_of_nonneg_right (by linarith only [hscale]) hM
  have hlast : v*(W.card : ℝ)*(H : ℝ)*((H : ℝ)+1) ≤ L/2 := by
    calc
      _ ≤ v*(W.card : ℝ)*(H : ℝ)*(P.V/2) := mul_le_mul_of_nonneg_left hboundary (by dsimp only [v]; positivity)
      _ = _ := by dsimp only [L]; ring
  change L ≤ (4*(1+98*Real.pi))*logarithmicTaylorJointMajorant P W
  have hL : L ≤ 4*M := by linarith only [hh,hfirst,hlast]
  simpa only [M,mul_assoc] using hL

#print axioms logarithmicTaylor_joint_source_reduced

theorem logarithmicTaylorJointMajorant_pow (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    (logarithmicTaylorJointMajorant P W)^42 =
      (GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ))) : ℝ)*
        ((3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
          (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))*
        ((W.card : ℝ)*(P.indices.card : ℝ)*
          (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^40 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let J := GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ)))
  let E : ℝ := (3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
    (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)
  let B : ℝ := (W.card : ℝ)*(P.indices.card : ℝ)*
    (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hJpow : ((J : ℝ)^(1/42 : ℝ))^42 = J := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg J)]
    norm_num
  have hEpow : (E^(1/42 : ℝ))^42 = E := by
    rw [← Real.rpow_mul_natCast hE]
    norm_num
  have hBpow : (B^(20/21 : ℝ))^42 = B^40 := by
    rw [← Real.rpow_mul_natCast hB]
    norm_num
  change ((J : ℝ)^(1/42 : ℝ)*E^(1/42 : ℝ)*B^(20/21 : ℝ))^42 = (J : ℝ)*E*B^40
  rw [mul_pow,mul_pow,hJpow,hEpow,hBpow]

#print axioms logarithmicTaylorJointMajorant_pow

theorem logarithmicTaylor_joint_critical :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      (W.card : ℝ)*P.V^42 ≤
        K*(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^(1/1000 : ℝ)*P.N^40*
          (3*P.N+(W.card : ℝ)*P.N^(19/20 : ℝ)) := by
  obtain ⟨C,hC,hsource⟩ := logarithmicTaylor_joint_source_reduced
  obtain ⟨J₀,hJ₀,hvmvt⟩ := GafniTao.heathBrownVMVTMainConjecture_native.critical
    (by norm_num : 2 ≤ (7 : ℕ)) (by norm_num : (0 : ℝ) < 1/1000)
  let D : ℝ := 4*(1+98*Real.pi)
  let K : ℝ := D^42*J₀/64*2^40
  have hD : 0 < D := by dsimp only [D]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨C,hC,K,hK,?_⟩
  intro P hPN hTlow hT hV W hW hsep
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let v : ℝ := 64/(H : ℝ)^21
  let R : ℝ := W.card
  let I : ℝ := P.indices.card
  let E : ℝ := 3*R*P.N+R^2*P.N^(19/20 : ℝ)
  let J := GafniTao.fordVinogradovMomentNat 21 6 H
  have hH : 1 ≤ H := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hNp _)
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hv : 0 < v := by dsimp only [v]; positivity
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hI : 0 ≤ I := Nat.cast_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  by_cases hRzero : R = 0
  · change R*P.V^42 ≤ _
    rw [hRzero,zero_mul]
    positivity
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
  have hsource' := hsource P hPN hTlow hT hV W hW hsep
  change v*(H : ℝ)*R*P.V ≤ D*logarithmicTaylorJointMajorant P W at hsource'
  have hVp := P.V_pos
  have hpow := pow_le_pow_left₀ (show 0 ≤ v*(H : ℝ)*R*P.V by positivity) hsource' 42
  rw [mul_pow D (logarithmicTaylorJointMajorant P W) 42,logarithmicTaylorJointMajorant_pow] at hpow
  change (v*(H : ℝ)*R*P.V)^42 ≤ D^42*((J : ℝ)*(E*v)*(R*I*v)^40) at hpow
  have hcancel : R^42*P.V^42 ≤ (D^42*(J : ℝ)/(v*(H : ℝ)^42))*(R^40*I^40*E) := by
    apply (mul_le_mul_iff_right₀ (show 0 < v^42*(H : ℝ)^42 by positivity)).mp
    calc
      _ = (v*(H : ℝ)*R*P.V)^42 := by ring
      _ ≤ D^42*((J : ℝ)*(E*v)*(R*I*v)^40) := hpow
      _ = _ := by field_simp
  have hJbound : (J : ℝ) ≤ J₀*(H : ℝ)^(21+1/1000 : ℝ) := by
    have hh := GafniTao.heathBrownCriticalMoment_bound (by norm_num : 2 ≤ (7 : ℕ)) hH hvmvt
    norm_num only [GafniTao.heathBrownCriticalMoment] at hh
    simpa only [show (21+1/1000 : ℝ) = 21001/1000 by norm_num] using hh
  have hcoef : D^42*(J : ℝ)/(v*(H : ℝ)^42) ≤ (D^42*J₀/64)*(H : ℝ)^(1/1000 : ℝ) := by
    calc
      _ ≤ D^42*(J₀*(H : ℝ)^(21+1/1000 : ℝ))/(v*(H : ℝ)^42) := by gcongr
      _ = _ := by
        rw [Real.rpow_add hHr,Real.rpow_ofNat]
        dsimp only [v]
        field_simp
  have hbound : R^42*P.V^42 ≤ R^41*(K*(H : ℝ)^(1/1000 : ℝ)*P.N^40*
      (3*P.N+R*P.N^(19/20 : ℝ))) := by
    calc
      _ ≤ (D^42*(J : ℝ)/(v*(H : ℝ)^42))*(R^40*I^40*E) := hcancel
      _ ≤ ((D^42*J₀/64)*(H : ℝ)^(1/1000 : ℝ))*(R^40*(2*P.N)^40*E) := by
        apply mul_le_mul hcoef
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hI P.indices_card_cast_le_two_mul_N 40) (by positivity)) hE
        · positivity
        · positivity
      _ = _ := by dsimp only [E,K]; ring
  change R*P.V^42 ≤ _
  apply (mul_le_mul_iff_right₀ (pow_pos hRp 41)).mp
  convert hbound using 1; ring

#print axioms logarithmicTaylor_joint_critical

theorem logarithmicTaylor_separated_card :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      ∀ W : Finset ℝ, W ⊆ P.ordinates →
      (W : Set ℝ).Pairwise (fun t u => P.N^(10/3 : ℝ) < |t-u|) →
      (W.card : ℝ) ≤ P.N^(7/200 : ℝ) := by
  obtain ⟨C₀,hC₀,K,hK,hcritical⟩ := logarithmicTaylor_joint_critical
  obtain ⟨C₁,_,hscales⟩ := logarithmicTaylor_source_scales
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_const_log_pow_le_rpow K hK.le 0 (η := 1/1000) (by norm_num)).and
      ((eventually_const_log_pow_le_rpow 2 (by norm_num) 0 (η := 19/1000) (by norm_num)).and
        (eventually_const_log_pow_le_rpow 6 (by norm_num) 0 (η := 1/250) (by norm_num))))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT hV W hW hsep
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hVp := P.V_pos
  have hN₀' := hN₀ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  simp only [pow_zero,mul_one] at hN₀'
  let H := Nat.ceil (P.N^(9/40 : ℝ))
  let R : ℝ := W.card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hHN : (H : ℝ) ≤ P.N := (hscales P ((le_max_left _ _).trans
    ((le_max_right _ _).trans hPN)) hT hV).1
  have hfactor : K*(H : ℝ)^(1/1000 : ℝ) ≤ P.N^(1/500 : ℝ) := by
    calc
      _ ≤ P.N^(1/1000 : ℝ)*P.N^(1/1000 : ℝ) :=
        mul_le_mul hN₀'.1 (Real.rpow_le_rpow (Nat.cast_nonneg H) hHN (by norm_num)) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hvpower : P.N^(40971/1000 : ℝ) ≤ P.V^42 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hV 42
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  have hraw := hcritical P ((le_max_left _ _).trans hPN) hTlow hT hV W hW hsep
  change R*P.V^42 ≤ K*(H : ℝ)^(1/1000 : ℝ)*P.N^40*(3*P.N+R*P.N^(19/20 : ℝ)) at hraw
  have hbound : R*P.N^(40971/1000 : ℝ) ≤
      3*P.N^(20501/500 : ℝ)+R*P.N^(5119/125 : ℝ) := by
    calc
      _ ≤ R*P.V^42 := mul_le_mul_of_nonneg_left hvpower hR
      _ ≤ K*(H : ℝ)^(1/1000 : ℝ)*P.N^40*(3*P.N+R*P.N^(19/20 : ℝ)) := hraw
      _ ≤ P.N^(1/500 : ℝ)*P.N^40*(3*P.N+R*P.N^(19/20 : ℝ)) := by gcongr
      _ = _ := by
        rw [mul_add]
        have h₀ : P.N^(1/500 : ℝ)*P.N^40*P.N = P.N^(20501/500 : ℝ) := by
          calc
            _ = P.N^(1/500 : ℝ)*P.N^(40 : ℝ)*P.N^(1 : ℝ) := by norm_num
            _ = P.N^((1/500 : ℝ)+40+1) := by rw [← Real.rpow_add hNp,← Real.rpow_add hNp]
            _ = _ := by norm_num
        have h₁ : P.N^(1/500 : ℝ)*P.N^40*P.N^(19/20 : ℝ) = P.N^(5119/125 : ℝ) := by
          rw [← Real.rpow_natCast P.N 40,← Real.rpow_add hNp,← Real.rpow_add hNp]
          norm_num
        linear_combination 3*h₀+R*h₁
  have hsmall : 2*P.N^(5119/125 : ℝ) ≤ P.N^(40971/1000 : ℝ) := by
    calc
      _ ≤ P.N^(19/1000 : ℝ)*P.N^(5119/125 : ℝ) := mul_le_mul_of_nonneg_right hN₀'.2.1 (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hsmallR := mul_le_mul_of_nonneg_left hsmall hR
  have hleading : R*P.N^(40971/1000 : ℝ) ≤ 6*P.N^(20501/500 : ℝ) := by
    nlinarith only [hbound,hsmallR]
  have hRbound : R ≤ 6*P.N^(31/1000 : ℝ) := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hNp (40971/1000))).mpr hleading
    calc
      _ ≤ 6*P.N^(20501/500 : ℝ)/P.N^(40971/1000 : ℝ) := hh
      _ = _ := by rw [mul_div_assoc,← Real.rpow_sub hNp]; norm_num
  calc
    _ ≤ 6*P.N^(31/1000 : ℝ) := hRbound
    _ ≤ P.N^(1/250 : ℝ)*P.N^(31/1000 : ℝ) := mul_le_mul_of_nonneg_right hN₀'.2.2 (by positivity)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

#print axioms logarithmicTaylor_separated_card

theorem logarithmicTaylor_actual_card :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^5 ≤ P.T → P.T ≤ P.N^(27/5 : ℝ) →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      (P.ordinates.card : ℝ) ≤ P.N^(9/100 : ℝ) := by
  obtain ⟨C₀,hC₀,hselect⟩ := logarithmicTaylor_separated_subset
  obtain ⟨C₁,_,hcount⟩ := logarithmicTaylor_separated_card
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 2 (by norm_num) 0 (η := 1/200) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hTlow hT hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨W,hW,hsep,hcover⟩ := hselect P ((le_max_left _ _).trans hPN) hV
  have hc := hcount P ((le_max_left _ _).trans ((le_max_right _ _).trans hPN)) hTlow hT hV W hW hsep
  have htwo : 2 ≤ P.N^(1/200 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  calc
    _ ≤ 2*(W.card : ℝ)*P.N^(1/20 : ℝ) := hcover
    _ ≤ P.N^(1/200 : ℝ)*P.N^(7/200 : ℝ)*P.N^(1/20 : ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNp,← Real.rpow_add hNp]; norm_num

#print axioms logarithmicTaylor_actual_card

theorem pintz_second_endpoint_research_largeValueBound {τ : ℝ}
    (hτlo : 37/7 ≤ τ) (hτhi : τ < 340/63) :
    IsZetaLargeValueBound (41/42) τ (3*τ/170) := by
  intro ε hε
  obtain ⟨C,hC,hcard⟩ := logarithmicTaylor_actual_card
  let δ : ℝ := min (1/2000) (min ((τ-5)/2) ((27/5-τ)/2))
  have hτfive : 5 < τ := by linarith only [hτlo]
  have hτupper : τ < 27/5 := by linarith only [hτhi]
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith only [hτfive]) (by linarith only [hτupper]))
  have hδsmall : δ ≤ 1/2000 := min_le_left _ _
  have hδlow : δ ≤ (τ-5)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδup : δ ≤ (27/5-τ)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hPN hTlow hTup hVlow _hVup
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT₀ : P.N^5 ≤ P.T := by
    calc
      _ = P.N^(5 : ℝ) := (Real.rpow_ofNat P.N 5).symm
      _ ≤ P.N^(τ-δ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδlow,hτfive])
      _ ≤ P.T := hTlow
  have hT₁ : P.T ≤ P.N^(27/5 : ℝ) := hTup.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδup,hτupper]))
  have hV : P.N^(1951/2000 : ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδsmall] :
      (1951/2000 : ℝ) ≤ 41/42-δ)).trans hVlow
  calc
    _ ≤ P.N^(9/100 : ℝ) := hcard P hPN hT₀ hT₁ hV
    _ ≤ P.N^(3*τ/170+ε) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith only [hτlo,hε])
    _ ≤ C*P.N^(3*τ/170+ε) := le_mul_of_one_le_left (by positivity) hC

#print axioms pintz_second_endpoint_research_largeValueBound

theorem pintz_second_endpoint_research_exponent {τ : ℝ}
    (hτlo : 37/7 ≤ τ) (hτhi : τ < 340/63) :
    zetaLargeValueExponent (41/42) τ ≤ ((3*τ/170 : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound (pintz_second_endpoint_research_largeValueBound hτlo hτhi)

#print axioms pintz_second_endpoint_research_exponent

theorem pintz_second_endpoint_research_density :
    zeroDensityExponent (41/42) ≤ ((63/85 : ℝ) : EReal) := by
  have hh := zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    (41/42) (3/170) (85/21) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  apply hh
  · intro τ hτlo hτhi
    by_cases hlo : τ < 37/7
    · rw [zetaLargeValueExponent_eq_bot_pintz_second_endpoint_lower hτlo hlo]
      exact bot_le
    · have hb := pintz_second_endpoint_research_exponent (le_of_not_gt hlo) hτhi
      rw [← EReal.coe_mul,show (3/170 : ℝ)*τ = 3*τ/170 by ring]
      exact hb
  · intro τ hτlo hτhi
    have hb := largeValueExponent_le_pintz_second_endpoint_general hτlo hτhi
    rw [← EReal.coe_mul,show (3/170 : ℝ)*τ = 3*τ/170 by ring]
    exact hb

#print axioms pintz_second_endpoint_research_density

example : ∀ τ : ℝ, 37/7 ≤ τ → τ < 340/63 →
    IsZetaLargeValueBound (41/42) τ (3*τ/170) :=
  fun _ hlo hhi => pintz_second_endpoint_research_largeValueBound hlo hhi

example : ∀ τ : ℝ, 37/7 ≤ τ → τ < 340/63 →
    zetaLargeValueExponent (41/42) τ ≤ ((3*τ/170 : ℝ) : EReal) :=
  fun _ hlo hhi => pintz_second_endpoint_research_exponent hlo hhi

example : zeroDensityExponent (41/42) ≤ ((63/85 : ℝ) : EReal) :=
  pintz_second_endpoint_research_density

end TaoTrudgianYang2025.PintzEndpointResearch

