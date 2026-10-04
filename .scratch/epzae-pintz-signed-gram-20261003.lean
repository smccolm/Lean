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

/-! Retained phase-weighted Gram entry for the actual pattern.
No far-correlation estimate or endpoint bound is assumed. -/
noncomputable section
open Complex Finset RiemannZeta.GuthMaynard
open scoped ComplexConjugate
namespace PintzSignedGramScratch
open TaoTrudgianYang2025

def alignedOffDiagonal (P : LargeValuePattern) : ℂ :=
  let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
  ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
    if t = u then 0 else
      conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))

theorem retained_gram (P : LargeValuePattern) :
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      4*P.N^2*(P.ordinates.card:ℝ)+2*P.N*(alignedOffDiagonal P).re := by
  classical
  let D := fun t => ∑ n ∈ P.indices,P.coeff n*dirichletPhase n t
  let c := fun t => phaseAlign (D t)
  let b := fun n => ∑ t ∈ P.ordinates,c t*dirichletPhase n t
  have halign : ‖∑ t ∈ P.ordinates,c t*D t‖ = ∑ t ∈ P.ordinates,‖D t‖ := by
    have he : (∑ t ∈ P.ordinates,c t*D t) =
        ((∑ t ∈ P.ordinates,‖D t‖:ℝ):ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun t _ => phaseAlign_mul (D t))
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    positivity
  have hlow : (P.ordinates.card:ℝ)*P.V ≤ ∑ t ∈ P.ordinates,‖D t‖ := by
    calc
      _ = ∑ _t ∈ P.ordinates,P.V := by simp
      _ ≤ _ := Finset.sum_le_sum P.large
  have hexpand : (∑ t ∈ P.ordinates,c t*D t) =
      ∑ n ∈ P.indices,P.coeff n*b n := by
    simp only [D,b,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcs := norm_sum_mul_sq_le P.indices P.coeff b
  rw [← hexpand] at hcs
  have hcoeff : (∑ n ∈ P.indices,‖P.coeff n‖^2) ≤ 2*P.N := by
    calc
      _ ≤ ∑ _n ∈ P.indices,(1:ℝ) := Finset.sum_le_sum fun n hn => by
        simpa only [one_pow] using
          pow_le_pow_left₀ (norm_nonneg _) (P.coeff_one_bounded n hn) 2
      _ = (P.indices.card:ℝ) := by simp
      _ ≤ _ := P.indices_card_cast_le_two_mul_N
  have hsampling : ((P.ordinates.card:ℝ)*P.V)^2 ≤
      2*P.N*(∑ n ∈ P.indices,‖b n‖^2) := by
    have hlo : ((P.ordinates.card:ℝ)*P.V)^2 ≤ ‖∑ t ∈ P.ordinates,c t*D t‖^2 := by
      rw [halign]
      exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) P.V_pos.le) hlow 2
    exact hlo.trans (hcs.trans (mul_le_mul_of_nonneg_right hcoeff
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  let G := fun t u => conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
  have henergy : ((∑ n ∈ P.indices,‖b n‖^2:ℝ):ℂ) =
      ∑ t ∈ P.ordinates,∑ u ∈ P.ordinates,G t u := by
    have hpoint (n : ℕ) :
        ((‖b n‖^2:ℝ):ℂ) = conj (b n)*b n := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    have hcast : ((∑ n ∈ P.indices,‖b n‖^2:ℝ):ℂ) =
        ∑ n ∈ P.indices,((‖b n‖^2:ℝ):ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp_rw [hpoint]
    simp only [b,map_sum,map_mul]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    dsimp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hp := dirichletPhase_mul_star (P.index_pos hn) u t
    rw [Complex.star_def] at hp
    rw [← hp]
    ring
  have hdiag (t : ℝ) : (G t t).re ≤ 2*P.N := by
    have hc := norm_phaseAlign_le_one (D t)
    have hc2 : ‖c t‖^2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hc 2
    have he : G t t = ((‖c t‖^2:ℝ):ℂ)*(P.indices.card:ℂ) := by
      simp only [G,sub_self,dirichletPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
      rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    rw [he]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero]
    exact (mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg _)).trans
      (by simpa only [one_mul] using P.indices_card_cast_le_two_mul_N)
  have hsplit : (∑ t ∈ P.ordinates,∑ u ∈ P.ordinates,G t u) =
      (∑ t ∈ P.ordinates,G t t)+alignedOffDiagonal P := by
    have hrow (t : ℝ) (ht : t ∈ P.ordinates) :
        (∑ u ∈ P.ordinates,G t u) =
          G t t+∑ u ∈ P.ordinates,if t = u then 0 else G t u := by
      have hh : ∀ u : ℝ, G t u =
          (if t = u then G t t else 0)+(if t = u then 0 else G t u) := by
        intro u
        split_ifs with h
        · subst u
          simp only [add_zero]
        · simp only [zero_add]
      have hs := Finset.sum_congr rfl (fun u (_ : u ∈ P.ordinates) => hh u)
      simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq,if_pos ht] using hs
    calc
      _ = ∑ t ∈ P.ordinates,(G t t+
          ∑ u ∈ P.ordinates,if t = u then 0 else G t u) :=
        Finset.sum_congr rfl hrow
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  have hre := congrArg Complex.re henergy
  rw [hsplit] at hre
  simp only [Complex.ofReal_re,Complex.add_re,Complex.re_sum] at hre
  have hsum := Finset.sum_le_sum (s:=P.ordinates) (fun t _ => hdiag t)
  have hbound : (∑ n ∈ P.indices,‖b n‖^2) ≤
      (P.ordinates.card:ℝ)*(2*P.N)+(alignedOffDiagonal P).re := by
    rw [hre]
    exact add_le_add
      (by simpa only [Finset.sum_const,nsmul_eq_mul] using hsum) le_rfl
  have hh := hsampling.trans
    (mul_le_mul_of_nonneg_left hbound
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (zero_lt_one.trans P.one_lt_N).le))
  nlinarith only [hh]

example (P : LargeValuePattern) :
    alignedOffDiagonal P =
      let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      ∑ t ∈ P.ordinates,∑ u ∈ P.ordinates,
        if t = u then 0 else conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t)) := rfl

example (P : LargeValuePattern) :
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      4*P.N^2*(P.ordinates.card:ℝ)+2*P.N*(alignedOffDiagonal P).re :=
  retained_gram P

#print axioms alignedOffDiagonal
#print axioms retained_gram

/-- The existing near-row theorem controls every small frequency of the
actual signed Gram sum. Only the explicit far sum remains. -/
theorem retained_gram_near_control (P : LargeValuePattern) {L : ℝ}
    (hL : 0 ≤ L) (hLN : L ≤ P.N^2) :
    let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
    let Qfar := ∑ t ∈ P.ordinates,
      ∑ u ∈ P.ordinates.filter (fun u => L < |u-t|),
        if t = u then 0 else
          conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      8*P.N^2*(P.ordinates.card:ℝ)+
        2*P.N*(P.ordinates.card:ℝ)^2*(2+200*Real.sqrt L)+
        48*Real.pi*P.N^2*(P.ordinates.card:ℝ)*(harmonic (Nat.ceil L):ℝ)+
        2*P.N*Qfar.re := by
  classical
  let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
  let F := fun t u => if t = u then (0:ℂ) else
    conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
  let Qnear := ∑ t ∈ P.ordinates,
    ∑ u ∈ P.ordinates.filter (fun u => |u-t| ≤ L),F t u
  let Qfar := ∑ t ∈ P.ordinates,
    ∑ u ∈ P.ordinates.filter (fun u => L < |u-t|),F t u
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤
    8*P.N^2*(P.ordinates.card:ℝ)+
      2*P.N*(P.ordinates.card:ℝ)^2*(2+200*Real.sqrt L)+
      48*Real.pi*P.N^2*(P.ordinates.card:ℝ)*(harmonic (Nat.ceil L):ℝ)+
      2*P.N*Qfar.re
  have hsplit : Qnear+Qfar = alignedOffDiagonal P := by
    dsimp only [Qnear,Qfar,alignedOffDiagonal]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
      P.ordinates (fun u => |u-t| ≤ L) (F t)
  have hterm (t u : ℝ) : (F t u).re ≤
      ‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖ := by
    dsimp only [F]
    split_ifs
    · exact norm_nonneg _
    · apply (Complex.re_le_norm _).trans
      rw [norm_mul,norm_mul,Complex.norm_conj]
      have ht := norm_phaseAlign_le_one
        (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      have hu := norm_phaseAlign_le_one
        (∑ n ∈ P.indices,P.coeff n*dirichletPhase n u)
      have hprod : ‖c t‖*‖c u‖ ≤ 1 := by
        simpa only [one_mul] using mul_le_mul ht hu (norm_nonneg _) (by norm_num)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  have hnear : Qnear.re ≤ (P.ordinates.card:ℝ)*
      (2*P.N+(P.ordinates.card:ℝ)*(2+200*Real.sqrt L)+
        24*Real.pi*P.N*(harmonic (Nat.ceil L):ℝ)) := by
    dsimp only [Qnear]
    simp only [Complex.re_sum]
    calc
      _ ≤ ∑ t ∈ P.ordinates,
          (2*P.N+(P.ordinates.card:ℝ)*(2+200*Real.sqrt L)+
            24*Real.pi*P.N*(harmonic (Nat.ceil L):ℝ)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact (Finset.sum_le_sum (fun u _ => hterm t u)).trans
          (P.sharp_gram_near_row ht hL hLN)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hgram := TaoTrudgianYang2025.PintzEndpointGram.retained_gram P
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤
    4*P.N^2*(P.ordinates.card:ℝ)+2*P.N*(alignedOffDiagonal P).re at hgram
  rw [← hsplit,Complex.add_re] at hgram
  have hN : 0 ≤ 2*P.N := by have := P.one_lt_N; linarith
  have hnear' := mul_le_mul_of_nonneg_left hnear hN
  nlinarith only [hgram,hnear']

example (P : LargeValuePattern) {L : ℝ} (hL : 0 ≤ L) (hLN : L ≤ P.N^2) :
    let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
    let Qfar := ∑ t ∈ P.ordinates,
      ∑ u ∈ P.ordinates.filter (fun u => L < |u-t|),
        if t = u then 0 else
          conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      8*P.N^2*(P.ordinates.card:ℝ)+
        2*P.N*(P.ordinates.card:ℝ)^2*(2+200*Real.sqrt L)+
        48*Real.pi*P.N^2*(P.ordinates.card:ℝ)*(harmonic (Nat.ceil L):ℝ)+
        2*P.N*Qfar.re :=
  retained_gram_near_control P hL hLN

#print axioms retained_gram_near_control

example (P : LargeValuePattern) : alignedOffDiagonal P =
    TaoTrudgianYang2025.PintzEndpointGram.alignedOffDiagonal P := rfl

/-- Uniform near-frequency absorption at an amplitude weaker than every
endpoint pattern's threshold after choosing a sufficiently small loss.
The actual far sum is retained, not estimated by an assumption. -/
theorem retained_gram_far_reduction {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : LargeValuePattern, N₀ ≤ P.N →
      P.N^(193/200:ℝ) ≤ P.V →
      let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      let Qfar := ∑ t ∈ P.ordinates,
        ∑ u ∈ P.ordinates.filter (fun u => P.N^(7/5:ℝ) < |u-t|),
          if t = u then 0 else
            conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
      ((P.ordinates.card:ℝ)*P.V)^2 ≤
        (P.ordinates.card:ℝ)*P.N^(2+ε)+4*P.N*Qfar.re := by
  classical
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_heathBrown_near_value_factor.and
      (eventually_heathBrown_diagonal_factor hε))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hPN hV
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hgood := hN₀ P.N ((le_max_right 1 N₀).trans hPN)
  let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
  let Qfar := ∑ t ∈ P.ordinates,
    ∑ u ∈ P.ordinates.filter (fun u => P.N^(7/5:ℝ) < |u-t|),
      if t = u then 0 else
        conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤
    (P.ordinates.card:ℝ)*P.N^(2+ε)+4*P.N*Qfar.re
  have hL : 0 ≤ P.N^(7/5:ℝ) := Real.rpow_nonneg hNpos.le _
  have hLN : P.N^(7/5:ℝ) ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (7/5:ℝ) ≤ 2)
  have hfinite := retained_gram_near_control P hL hLN
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤
    8*P.N^2*(P.ordinates.card:ℝ)+
      2*P.N*(P.ordinates.card:ℝ)^2*(2+200*Real.sqrt (P.N^(7/5:ℝ)))+
      48*Real.pi*P.N^2*(P.ordinates.card:ℝ)*
        (harmonic (Nat.ceil (P.N^(7/5:ℝ))):ℝ)+2*P.N*Qfar.re at hfinite
  have hvalue : 4*P.N*(2+200*Real.sqrt (P.N^(7/5:ℝ))) ≤ P.V^2 := calc
    _ ≤ P.N^(171/100:ℝ) := hgood.1
    _ ≤ P.N^(193/100:ℝ) := Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num)
    _ = (P.N^(193/200:ℝ))^2 := by
      rw [← Real.rpow_mul_natCast hNpos.le]
      norm_num
    _ ≤ P.V^2 := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hV 2
  have hvalueR := mul_le_mul_of_nonneg_left hvalue
    (sq_nonneg (P.ordinates.card:ℝ))
  have hharm : (0:ℝ) ≤ harmonic (Nat.ceil (P.N^(7/5:ℝ))) := by
    exact_mod_cast (Finset.sum_nonneg (fun i _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i+1))) :
        (0:ℚ) ≤ harmonic (Nat.ceil (P.N^(7/5:ℝ))))
  have hdiag : 16*P.N^2+96*Real.pi*P.N^2*
      (harmonic (Nat.ceil (P.N^(7/5:ℝ))):ℝ) ≤ P.N^(2+ε) := by
    have hpos : 0 ≤ 96*Real.pi*P.N^2*
        (harmonic (Nat.ceil (P.N^(7/5:ℝ))):ℝ) := by positivity
    have hd := hgood.2
    nlinarith only [hpos,hd]
  have hdiagR := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg P.ordinates.card)
  nlinarith only [hfinite,hvalueR,hdiagR]

example {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : LargeValuePattern, N₀ ≤ P.N →
      P.N^(193/200:ℝ) ≤ P.V →
      let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      let Qfar := ∑ t ∈ P.ordinates,
        ∑ u ∈ P.ordinates.filter (fun u => P.N^(7/5:ℝ) < |u-t|),
          if t = u then 0 else
            conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
      ((P.ordinates.card:ℝ)*P.V)^2 ≤
        (P.ordinates.card:ℝ)*P.N^(2+ε)+4*P.N*Qfar.re :=
  retained_gram_far_reduction hε

#print axioms retained_gram_far_reduction

example (P : LargeValuePattern) {σ δ : ℝ}
    (hσ : 39/40 ≤ σ) (hδ : δ ≤ 1/100)
    (hV : P.N^(σ-δ) ≤ P.V) : P.N^(193/200:ℝ) ≤ P.V :=
  (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
    (by linarith only [hσ,hδ])).trans hV

example {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      P.N^(193/200:ℝ) ≤ P.V →
      let c := fun t => phaseAlign (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      let Qfar := ∑ t ∈ P.ordinates,
        ∑ u ∈ P.ordinates.filter (fun u => P.N^(7/5:ℝ) < |u-t|),
          if t = u then 0 else
            conj (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t))
      ((P.ordinates.card:ℝ)*P.V)^2 ≤
        (P.ordinates.card:ℝ)*P.N^(2+ε)+4*P.N*Qfar.re := by
  obtain ⟨N₀,hN₀,hbound⟩ := retained_gram_far_reduction hε
  exact ⟨N₀,hN₀,fun P hPN hV => hbound P.toLargeValuePattern hPN hV⟩

/- Arithmetic check for a plain Cauchy--Schwarz/convolution application:
its N*R^(3/2) term has too large an N exponent in the entire open strip. -/
example {τ : ℝ} (hτ : τ < 340/63) :
    2*(41/42)-1+(3*τ/170)/2 < (1:ℝ) := by
  linarith only [hτ]

example : (37/7:ℝ) ≤ 16/3 ∧ (16/3:ℝ) < 340/63 ∧
    2*(41/42)-1+2*(3*(16/3)/170) <
      (1/2:ℝ)+(16/3)/4+(13/8)*(3*(16/3)/170) := by
  norm_num

/-! Original endpoint research: the actual far matrix has a controlled
negative spectrum, leaving a signed cubic trace instead of an absolute
termwise correlation bound. No endpoint estimate is assumed. -/

open scoped Matrix ComplexOrder

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

def nearRowBudget (P : LargeValuePattern) (L : ℝ) : ℝ :=
  2*P.N+(P.ordinates.card:ℝ)*(2+200*Real.sqrt L)+
    24*Real.pi*P.N*(harmonic (Nat.ceil L):ℝ)

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

theorem farMatrix_hermitian (P : LargeValuePattern) (L : ℝ) :
    (farMatrix P L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro t u
  change conj (if L < |(t:ℝ)-u| then gramKernel P u t else 0) = _
  rw [abs_sub_comm (t:ℝ) (u:ℝ)]
  by_cases h : L < |(u:ℝ)-t|
  · simp only [farMatrix, h, ite_true, gramKernel_conj]
  · simp only [farMatrix, h, ite_false, map_zero]

theorem nearMatrix_hermitian (P : LargeValuePattern) (L : ℝ) :
    (nearMatrix P L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro t u
  change conj (if |(t:ℝ)-u| ≤ L then gramKernel P u t else 0) = _
  rw [abs_sub_comm (t:ℝ) (u:ℝ)]
  by_cases h : |(u:ℝ)-t| ≤ L
  · simp only [nearMatrix, h, ite_true, gramKernel_conj]
  · simp only [nearMatrix, h, ite_false, map_zero]

theorem near_add_far (P : LargeValuePattern) (L : ℝ) :
    nearMatrix P L+farMatrix P L = fullMatrix P := by
  ext t u
  simp only [Matrix.add_apply, nearMatrix, farMatrix, fullMatrix]
  by_cases h : |(u:ℝ)-t| ≤ L
  · simp only [h, not_lt_of_ge h, ite_true, ite_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_false, ite_true, zero_add]

theorem fullMatrix_posSemidef (P : LargeValuePattern) :
    (fullMatrix P).PosSemidef := by
  let M : Matrix P.ordinates P.indices ℂ := fun t n => conj (dirichletPhase n t)
  have he : fullMatrix P = M*M.conjTranspose := by
    ext t u
    simp only [fullMatrix, gramKernel, Matrix.mul_apply, Matrix.conjTranspose_apply, M,
      Complex.star_def, starRingEnd_self_apply]
    rw [← Finset.sum_attach P.indices]
    apply Finset.sum_congr rfl
    intro n _
    rw [← dirichletPhase_mul_star (P.index_pos n.property) u t, Complex.star_def]
    ring
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose M

theorem nearMatrix_row_bound (P : LargeValuePattern) {L : ℝ}
    (hL : 0 ≤ L) (hLN : L ≤ P.N^2) (t : P.ordinates) :
    (∑ u : P.ordinates, ‖nearMatrix P L t u‖) ≤ nearRowBudget P L := by
  have he : (∑ u : P.ordinates, ‖nearMatrix P L t u‖) =
      ∑ u ∈ P.ordinates.filter (fun u => |u-(t:ℝ)| ≤ L),
        ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ := by
    simp only [nearMatrix, gramKernel, apply_ite norm, norm_zero,
      Finset.sum_filter]
    exact Finset.sum_attach P.ordinates (fun u : ℝ =>
      if |u-(t:ℝ)| ≤ L then ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ else 0)
  rw [he]
  exact P.sharp_gram_near_row t.property hL hLN

/-- A row-sum bound controls the actual Hermitian quadratic form. -/
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

/-- Every negative eigenvalue of the far matrix is controlled by the
PROVED near row, using positivity of the original, actual Gram matrix. -/
theorem farMatrix_eigenvalue_lower (P : LargeValuePattern) {L : ℝ}
    (hL : 0 ≤ L) (hLN : L ≤ P.N^2) (i : P.ordinates) :
    -nearRowBudget P L ≤ (farMatrix_hermitian P L).eigenvalues i := by
  let H := farMatrix_hermitian P L
  let x : P.ordinates → ℂ := H.eigenvectorBasis i
  have hx : (∑ j, ‖x j‖^2) = 1 := by
    have hn := H.eigenvectorBasis.orthonormal.1 i
    have hs := congrArg (fun r : ℝ => r^2) hn
    dsimp only at hs
    rw [EuclideanSpace.norm_sq_eq] at hs
    simpa only [one_pow] using hs
  have hnear := hermitian_quadratic_norm_le_row (nearMatrix_hermitian P L)
    (nearMatrix_row_bound P hL hLN) x
  rw [hx,mul_one] at hnear
  have hpos := (fullMatrix_posSemidef P).re_dotProduct_nonneg x
  rw [← near_add_far P L, Matrix.add_mulVec, dotProduct_add, map_add] at hpos
  have he := H.eigenvalues_eq i
  change H.eigenvalues i = (star x ⬝ᵥ (farMatrix P L *ᵥ x)).re at he
  have hn := (Complex.re_le_norm (star x ⬝ᵥ (nearMatrix P L *ᵥ x))).trans hnear
  change 0 ≤ (star x ⬝ᵥ (nearMatrix P L *ᵥ x)).re+
    (star x ⬝ᵥ (farMatrix P L *ᵥ x)).re at hpos
  change -nearRowBudget P L ≤ H.eigenvalues i
  linarith only [hn,hpos,he]

#print axioms farMatrix_eigenvalue_lower

private theorem star_dot_self_eq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖^2 : ℝ):ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum,
    Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_pow _ _

private theorem hermitian_quadratic_le_max {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {M : ℝ}
    (hM : ∀ i, hA.eigenvalues i ≤ M) (x : ι → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ M*(∑ i, ‖x i‖^2) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i:ℂ))
  have hspec : A = U*(D*star U) := by
    simpa only [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def, mul_assoc]
      using hA.spectral_theorem
  have hunit : U*star U = 1 := by simp [U]
  have hd : (((M:ℂ) • (1:Matrix ι ι ℂ))-D).PosSemidef := by
    have he : ((M:ℂ) • (1:Matrix ι ι ℂ))-D =
        Matrix.diagonal (fun i => ((M-hA.eigenvalues i:ℝ):ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · simp [D, hij]
    rw [he, Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast sub_nonneg.mpr (hM i)
  have hp : (((M:ℂ) • (1:Matrix ι ι ℂ))-A).PosSemidef := by
    have hh := hd.mul_mul_conjTranspose_same U
    have he : U*(((M:ℂ) • (1:Matrix ι ι ℂ))-D)*U.conjTranspose =
        ((M:ℂ) • (1:Matrix ι ι ℂ))-A := by
      change U*(((M:ℂ) • (1:Matrix ι ι ℂ))-D)*star U = _
      rw [mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hunit, hspec]
      rw [mul_assoc]
    rw [he] at hh
    exact hh
  have hh := hp.re_dotProduct_nonneg x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_dot_self_eq, smul_eq_mul,
    map_sub] at hh
  change 0 ≤ ((M:ℂ)*((∑ i, ‖x i‖^2:ℝ):ℂ)).re-
    (star x ⬝ᵥ (A *ᵥ x)).re at hh
  rw [← Complex.ofReal_mul, Complex.ofReal_re] at hh
  linarith only [hh]

/-- The cubic trace controls positive Rayleigh quotients when all negative
eigenvalues have a proved lower bound. The signed trace is not absolutized. -/
private theorem hermitian_quadratic_cube_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {B R : ℝ} (hB : 0 ≤ B) (hlow : ∀ i, -B ≤ hA.eigenvalues i)
    (x : ι → ℂ) (hx : (∑ i, ‖x i‖^2) ≤ R) :
    (star x ⬝ᵥ (A *ᵥ x)).re^3 ≤
      R^3*((Matrix.trace (A^3)).re+(Fintype.card ι:ℝ)*B^3) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ:Finset ι).Nonempty) hA.eigenvalues
  have hjmax (i : ι) : hA.eigenvalues i ≤ hA.eigenvalues j := by
    rw [← hj]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  let M := max 0 (hA.eigenvalues j)
  have hM : 0 ≤ M := le_max_left _ _
  have hR : 0 ≤ R := (Finset.sum_nonneg (fun i _ => sq_nonneg (‖x i‖))).trans hx
  have hQ : (star x ⬝ᵥ (A *ᵥ x)).re ≤ R*M :=
    (hermitian_quadratic_le_max hA
      (fun i => (hjmax i).trans (le_max_right _ _)) x).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx hM)
  have hcube (i : ι) : 0 ≤ hA.eigenvalues i^3+B^3 := by
    have hc := (show Odd (3:ℕ) by decide).strictMono_pow.monotone (hlow i)
    norm_num at hc
    linarith only [hc]
  have htrace : (Matrix.trace (A^3)).re = ∑ i, hA.eigenvalues i^3 := by
    rw [hA.trace_cube_eq_sum_eigenvalues_cube]
    simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]
  have he : (∑ i, (hA.eigenvalues i^3+B^3)) =
      (Matrix.trace (A^3)).re+(Fintype.card ι:ℝ)*B^3 := by
    rw [htrace, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hM3 : M^3 ≤ (Matrix.trace (A^3)).re+(Fintype.card ι:ℝ)*B^3 := by
    rcases le_total (hA.eigenvalues j) 0 with hj0 | hj0
    · rw [show M = 0 from max_eq_left hj0, zero_pow (by decide : (3:ℕ) ≠ 0), ← he]
      exact Finset.sum_nonneg (fun i _ => hcube i)
    · rw [show M = hA.eigenvalues j from max_eq_right hj0, ← he]
      exact (le_add_of_nonneg_right (pow_nonneg hB 3)).trans
        (Finset.single_le_sum (fun i _ => hcube i) (Finset.mem_univ j))
  have hQ3 := (show Odd (3:ℕ) by decide).strictMono_pow.monotone hQ
  rw [mul_pow] at hQ3
  exact hQ3.trans (mul_le_mul_of_nonneg_left hM3 (pow_nonneg hR 3))

def signedFarSum (P : LargeValuePattern) (L : ℝ) : ℂ :=
  let c := fun t => phaseAlign (∑ n ∈ P.indices, P.coeff n*dirichletPhase n t)
  ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates.filter (fun u => L < |u-t|),
    if t = u then 0 else conj (c t)*c u*gramKernel P t u

def farTriangle (P : LargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t : P.ordinates, ∑ u : P.ordinates, ∑ v : P.ordinates,
    farMatrix P L t u*farMatrix P L u v*farMatrix P L v t

theorem signedFarSum_quadratic (P : LargeValuePattern) {L : ℝ} (hL : 0 ≤ L) :
    signedFarSum P L =
      let c : P.ordinates → ℂ := fun t =>
        phaseAlign (∑ n ∈ P.indices, P.coeff n*dirichletPhase n t)
      star c ⬝ᵥ (farMatrix P L *ᵥ c) := by
  classical
  simp only [signedFarSum, dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def,
    Finset.mul_sum]
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_filter, ← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : L < |(u:ℝ)-t|
  · have htu : (t:ℝ) ≠ u := by intro he; rw [he, sub_self, abs_zero] at hu; linarith
    simp only [farMatrix, hu, htu, ite_true, ite_false]
    ring
  · simp only [farMatrix, hu, ite_false, zero_mul, mul_zero]

theorem farTriangle_trace (P : LargeValuePattern) (L : ℝ) :
    farTriangle P L = Matrix.trace (farMatrix P L^3) :=
  (matrix_trace_cube_expand _).symm

/-- An unconditional bound for the ACTUAL phase-aligned far sum. All
negative-spectrum losses are explicit near-row quantities; only the
signed, all-far cubic correlation remains to be estimated analytically. -/
theorem signedFarSum_cube_le_triangle (P : LargeValuePattern) {L : ℝ}
    (hL : 0 ≤ L) (hLN : L ≤ P.N^2) :
    (signedFarSum P L).re^3 ≤ (P.ordinates.card:ℝ)^3*
      ((farTriangle P L).re+(P.ordinates.card:ℝ)*nearRowBudget P L^3) := by
  classical
  by_cases hW : P.ordinates.Nonempty
  · haveI : Nonempty P.ordinates := hW.to_subtype
    let c : P.ordinates → ℂ := fun t =>
      phaseAlign (∑ n ∈ P.indices, P.coeff n*dirichletPhase n t)
    have hc : (∑ t, ‖c t‖^2) ≤ (P.ordinates.card:ℝ) := by
      calc
        _ ≤ ∑ _t : P.ordinates, (1:ℝ) := Finset.sum_le_sum (fun t _ => by
          simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
            (norm_phaseAlign_le_one (∑ n ∈ P.indices, P.coeff n*dirichletPhase n t)) 2)
        _ = _ := by simp
    have hB : 0 ≤ nearRowBudget P L := by
      obtain ⟨t,ht⟩ := hW
      exact (Finset.sum_nonneg (fun u _ => norm_nonneg (nearMatrix P L ⟨t,ht⟩ u))).trans
        (nearMatrix_row_bound P hL hLN ⟨t,ht⟩)
    have hh := hermitian_quadratic_cube_le (farMatrix_hermitian P L) hB
      (farMatrix_eigenvalue_lower P hL hLN) c hc
    rw [signedFarSum_quadratic P hL, farTriangle_trace]
    simpa only [Fintype.card_coe] using hh
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    simp only [signedFarSum, he, Finset.sum_empty, Complex.zero_re, Finset.card_empty,
      Nat.cast_zero, zero_pow (by decide : (3:ℕ) ≠ 0), zero_mul, le_refl]

#print axioms signedFarSum_quadratic
#print axioms farTriangle_trace
#print axioms signedFarSum_cube_le_triangle

/-- The cubic spectral bound is consumed by the previously established
Gram/near absorption for the SAME pattern and the SAME physical far cutoff. -/
theorem retained_gram_cubic_far_reduction {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : LargeValuePattern, N₀ ≤ P.N →
      P.N^(193/200:ℝ) ≤ P.V →
      ((P.ordinates.card:ℝ)*P.V^2-P.N^(2+ε))^3 ≤
        64*P.N^3*((farTriangle P (P.N^(7/5:ℝ))).re+
          (P.ordinates.card:ℝ)*nearRowBudget P (P.N^(7/5:ℝ))^3) := by
  obtain ⟨N₀,hN₀,hbound⟩ := retained_gram_far_reduction hε
  refine ⟨N₀,hN₀,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hL : 0 ≤ P.N^(7/5:ℝ) := Real.rpow_nonneg hNp.le _
  have hLN : P.N^(7/5:ℝ) ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (7/5:ℝ) ≤ 2)
  have hg := hbound P hPN hV
  change ((P.ordinates.card:ℝ)*P.V)^2 ≤
    (P.ordinates.card:ℝ)*P.N^(2+ε)+4*P.N*(signedFarSum P (P.N^(7/5:ℝ))).re at hg
  have ht := signedFarSum_cube_le_triangle P hL hLN
  by_cases hR : P.ordinates.card = 0
  · have he := Finset.card_eq_zero.mp hR
    have hf : farTriangle P (P.N^(7/5:ℝ)) = 0 := by
      simp only [farTriangle]
      haveI : IsEmpty P.ordinates := by simpa only [he] using
        (inferInstance : IsEmpty (↥(∅:Finset ℝ)))
      exact Finset.sum_eq_zero (fun t _ => isEmptyElim t)
    rw [hR, Nat.cast_zero, zero_mul, zero_sub, hf, Complex.zero_re, zero_mul, add_zero,
      mul_zero]
    simpa only [zero_pow (by decide : (3:ℕ) ≠ 0)] using
      (show Odd (3:ℕ) by decide).strictMono_pow.monotone
        (neg_nonpos.mpr (Real.rpow_nonneg hNp.le (2+ε)))
  · have hRp : 0 < (P.ordinates.card:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hR)
    have hb : (P.ordinates.card:ℝ)*
        ((P.ordinates.card:ℝ)*P.V^2-P.N^(2+ε)) ≤
          4*P.N*(signedFarSum P (P.N^(7/5:ℝ))).re := by nlinarith only [hg]
    have hc := (show Odd (3:ℕ) by decide).strictMono_pow.monotone hb
    rw [mul_pow, mul_pow, mul_pow] at hc
    have hd := mul_le_mul_of_nonneg_left ht (show 0 ≤ (4:ℝ)^3*P.N^3 by positivity)
    have hall : (P.ordinates.card:ℝ)^3*
        ((P.ordinates.card:ℝ)*P.V^2-P.N^(2+ε))^3 ≤
        (P.ordinates.card:ℝ)^3*(64*P.N^3*
          ((farTriangle P (P.N^(7/5:ℝ))).re+
            (P.ordinates.card:ℝ)*nearRowBudget P (P.N^(7/5:ℝ))^3)) := by
      calc
        _ ≤ (4:ℝ)^3*P.N^3*(signedFarSum P (P.N^(7/5:ℝ))).re^3 := hc
        _ ≤ _ := by convert hd using 1; ring
    exact (mul_le_mul_iff_right₀ (pow_pos hRp 3)).mp hall

#print axioms retained_gram_cubic_far_reduction

/-- The near-spectrum loss is at most N^(1+epsilon) for the actual endpoint
patterns. The sixth powering is used positively to control the row budget,
not asserted to prove the desired endpoint itself. -/
theorem endpoint_nearRowBudget_uniform {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : LargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        nearRowBudget P (P.N^(7/5:ℝ)) ≤ P.N^(1+ε) := by
  have hb : IsLargeValueBound (41/42) τ (2/7) := by
    have hm := meanSquare_largeValueBound (σ:=41/42) (τ:=τ/6) (by norm_num)
    rw [max_eq_left (by linarith only [hτu] : 1+τ/6-2*(41/42) ≤ 2-2*(41/42))] at hm
    have hp := IsLargeValueBound.of_powered (by norm_num : (1/2:ℝ) ≤ 41/42)
      (by norm_num : (41/42:ℝ) ≤ 1) (by linarith only [hτ] : 0 ≤ τ)
      6 (by omega) hm
    norm_num at hp
    exact hp
  obtain ⟨C₀,hC₀,δ,hδ,hcard⟩ := hb (1/280) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    ((eventually_const_log_pow_le_rpow (404*C₀) (by linarith only [hC₀])
      0 (η:=3/280) (by norm_num)).and (eventually_heathBrown_diagonal_factor hε))
  refine ⟨max C₀ N₀,hC₀.trans (le_max_left _ _),δ,hδ,?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR := hcard P ((le_max_left _ _).trans hPN) hTl hTu hVl hVu
  have hgood := hN₀ P.N ((le_max_right _ _).trans hPN)
  have hs : 404*C₀ ≤ P.N^(3/280:ℝ) := by
    simpa only [pow_zero, mul_one] using hgood.1
  have hroot : Real.sqrt (P.N^(7/5:ℝ)) = P.N^(7/10:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
    norm_num
  have hfactor : 2+200*Real.sqrt (P.N^(7/5:ℝ)) ≤ 202*P.N^(7/10:ℝ) := by
    rw [hroot]
    have hh := Real.one_le_rpow P.one_lt_N.le (by norm_num : (0:ℝ) ≤ 7/10)
    linarith only [hh]
  have hsmall : 2*((P.ordinates.card:ℝ)*(2+200*Real.sqrt (P.N^(7/5:ℝ)))) ≤ P.N := by
    calc
      _ ≤ 2*(C₀*P.N^(2/7+1/280:ℝ)*(202*P.N^(7/10:ℝ))) := by
        gcongr
      _ = (404*C₀)*(P.N^(277/280:ℝ)) := by
        have he : P.N^(2/7+1/280:ℝ)*P.N^(7/10:ℝ) = P.N^(277/280:ℝ) := by
          rw [← Real.rpow_add hNp]
          norm_num
        calc
          _ = (404*C₀)*(P.N^(2/7+1/280:ℝ)*P.N^(7/10:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ P.N^(3/280:ℝ)*P.N^(277/280:ℝ) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hNp.le _)
      _ = P.N := by rw [← Real.rpow_add hNp]; norm_num
  have hdiag : 8*(2*P.N+24*Real.pi*P.N*
      (harmonic (Nat.ceil (P.N^(7/5:ℝ))):ℝ)) ≤ P.N^(1+ε) := by
    apply (mul_le_mul_iff_right₀ hNp).mp
    have he : P.N*P.N^(1+ε) = P.N^(2+ε) := by
      conv_lhs => lhs; rw [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    rw [he]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hgood.2
  have hNpow : P.N ≤ P.N^(1+ε) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (show (1:ℝ) ≤ 1+ε by linarith only [hε])
  unfold nearRowBudget
  linarith only [hsmall,hdiag,hNpow,Real.rpow_nonneg hNp.le (1+ε)]

/-- Uniform endpoint-pattern reduction with ALL near/negative spectral
losses discharged. The only unevaluated analytic quantity is the explicit
signed all-far triangle of the original Dirichlet kernel. -/
theorem endpoint_signed_triangle_reduction {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ((P.ordinates.card:ℝ)*P.V^2-P.N^(2+ε))^3 ≤
          64*P.N^3*((farTriangle P.toLargeValuePattern (P.N^(7/5:ℝ))).re+
            (P.ordinates.card:ℝ)*P.N^(3+ε)) := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hnear⟩ := endpoint_nearRowBudget_uniform hτ hτu
    (show 0 < ε/3 by linarith only [hε])
  obtain ⟨N₀,hN₀,hgram⟩ := retained_gram_cubic_far_reduction hε
  refine ⟨max C₀ N₀,hC₀.trans (le_max_left _ _),min δ₀ (1/100),
    lt_min hδ₀ (by norm_num),?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hd : min δ₀ (1/100:ℝ) ≤ δ₀ := min_le_left _ _
  have hd1 : min δ₀ (1/100:ℝ) ≤ 1/100 := min_le_right _ _
  have hb := hnear P.toLargeValuePattern ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
  have hv : P.N^(193/200:ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd1])).trans hVl
  have hg := hgram P.toLargeValuePattern ((le_max_right _ _).trans hPN) hv
  have hb3 : nearRowBudget P.toLargeValuePattern (P.N^(7/5:ℝ))^3 ≤ P.N^(3+ε) := by
    have hh := (show Odd (3:ℕ) by decide).strictMono_pow.monotone hb
    have he : (P.N^(1+ε/3))^3 = P.N^(3+ε) := by
      rw [← Real.rpow_mul_natCast hNp.le]
      congr 1
      push_cast
      ring
    rwa [he] at hh
  exact hg.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb3 (Nat.cast_nonneg P.ordinates.card)))
    (by positivity))

#print axioms endpoint_nearRowBudget_uniform
#print axioms endpoint_signed_triangle_reduction

def cyclePhase (a b c : ℕ) (t u v : ℝ) : ℂ :=
  dirichletPhase a (u-t)*dirichletPhase b (v-u)*dirichletPhase c (t-v)

def distinctCycle (P : LargeValuePattern) (t u v : ℝ) : ℂ :=
  ∑ a ∈ P.indices, ∑ b ∈ P.indices, ∑ c ∈ P.indices,
    if a ≠ b ∧ b ≠ c ∧ c ≠ a then cyclePhase a b c t u v else 0

def collisionCycle (P : LargeValuePattern) (t u v : ℝ) : ℂ :=
  ∑ a ∈ P.indices, ∑ b ∈ P.indices, ∑ c ∈ P.indices,
    if a ≠ b ∧ b ≠ c ∧ c ≠ a then 0 else cyclePhase a b c t u v

theorem cycle_distinct_add_collision (P : LargeValuePattern) (t u v : ℝ) :
    distinctCycle P t u v+collisionCycle P t u v =
      gramKernel P t u*gramKernel P u v*gramKernel P v t := by
  simp only [distinctCycle, collisionCycle,
    ← Finset.sum_add_distrib]
  have hi (a b c : ℕ) :
      (if a ≠ b ∧ b ≠ c ∧ c ≠ a then cyclePhase a b c t u v else 0)+
      (if a ≠ b ∧ b ≠ c ∧ c ≠ a then 0 else cyclePhase a b c t u v) =
        cyclePhase a b c t u v := by split_ifs <;> simp only [add_zero, zero_add]
  simp only [hi]
  simp only [cyclePhase, gramKernel, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Coincident Fourier frequencies in one actual kernel triangle cost only
three square-cardinality contributions, with no loss on its signed distinct part. -/
theorem collisionCycle_norm_le (P : LargeValuePattern) (t u v : ℝ) :
    ‖collisionCycle P t u v‖ ≤ 3*(P.indices.card:ℝ)^2 := by
  classical
  have hterm (a : ℕ) (ha : a ∈ P.indices) (b : ℕ) (hb : b ∈ P.indices)
      (c : ℕ) (hc : c ∈ P.indices) :
      ‖if a ≠ b ∧ b ≠ c ∧ c ≠ a then (0:ℂ) else cyclePhase a b c t u v‖ ≤
        (if a = b then (1:ℝ) else 0)+(if b = c then 1 else 0)+
          (if c = a then 1 else 0) := by
    have hn : ‖cyclePhase a b c t u v‖ = 1 := by
      simp only [cyclePhase, norm_mul, P.norm_dirichletPhase ha,
        P.norm_dirichletPhase hb, P.norm_dirichletPhase hc, one_mul]
    by_cases hd : a ≠ b ∧ b ≠ c ∧ c ≠ a
    · rw [if_pos hd]
      simp only [norm_zero, if_neg hd.1, if_neg hd.2.1, if_neg hd.2.2,
        add_zero, le_refl]
    · rw [if_neg hd, hn]
      by_cases hab : a = b
      · rw [if_pos hab]
        split_ifs <;> norm_num
      · by_cases hbc : b = c
        · rw [if_neg hab, if_pos hbc]
          split_ifs <;> norm_num
        · have hca : c = a := by tauto
          rw [if_neg hab, if_neg hbc, if_pos hca]
          norm_num
  calc
    _ ≤ ∑ a ∈ P.indices, ∑ b ∈ P.indices, ∑ c ∈ P.indices,
        ((if a = b then (1:ℝ) else 0)+(if b = c then 1 else 0)+
          (if c = a then 1 else 0)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun c hc => hterm a ha b hb c hc)
    _ = _ := by
      simp [Finset.sum_add_distrib]
      ring

def distinctFarTriangle (P : LargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t : P.ordinates, ∑ u : P.ordinates, ∑ v : P.ordinates,
    if L < |(u:ℝ)-t| ∧ L < |(v:ℝ)-u| ∧ L < |(t:ℝ)-v|
    then distinctCycle P t u v else 0

/-- An actual signed far-triangle estimate with all coincident integer
frequencies removed and their complete contribution bounded explicitly. -/
theorem farTriangle_le_distinct (P : LargeValuePattern) (L : ℝ) :
    (farTriangle P L).re ≤ (distinctFarTriangle P L).re+
      12*P.N^2*(P.ordinates.card:ℝ)^3 := by
  classical
  have hpoint (t u v : P.ordinates) :
      (farMatrix P L t u*farMatrix P L u v*farMatrix P L v t).re ≤
        (if L < |(u:ℝ)-t| ∧ L < |(v:ℝ)-u| ∧ L < |(t:ℝ)-v|
        then distinctCycle P t u v else 0).re+3*(P.indices.card:ℝ)^2 := by
    by_cases htu : L < |(u:ℝ)-t|
    · by_cases huv : L < |(v:ℝ)-u|
      · by_cases hvt : L < |(t:ℝ)-v|
        · simp only [farMatrix, htu, huv, hvt, and_self, ite_true]
          rw [← cycle_distinct_add_collision, Complex.add_re]
          exact add_le_add le_rfl
            ((Complex.re_le_norm _).trans (collisionCycle_norm_le P t u v))
        · simp only [farMatrix, htu, huv, hvt, and_false, ite_false, ite_true,
            mul_zero, Complex.zero_re, zero_add]
          positivity
      · simp only [farMatrix, htu, huv, true_and, false_and, ite_true, ite_false,
          mul_zero, zero_mul, Complex.zero_re, zero_add]
        positivity
    · simp only [farMatrix, htu, false_and, ite_false, zero_mul, Complex.zero_re, zero_add]
      positivity
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ:Finset P.ordinates)) =>
    Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ:Finset P.ordinates)) =>
      Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ:Finset P.ordinates)) => hpoint t u v)))
  have hsum : (farTriangle P L).re ≤ (distinctFarTriangle P L).re+
      3*(P.indices.card:ℝ)^2*(P.ordinates.card:ℝ)^3 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul] at hs
    simp only [farTriangle, distinctFarTriangle, Complex.re_sum]
    convert hs using 1
    ring
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg P.indices.card)
    P.indices_card_cast_le_two_mul_N 2
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 3*(P.ordinates.card:ℝ)^3 by positivity)
  exact hsum.trans (add_le_add le_rfl (by nlinarith only [hm]))

#print axioms cycle_distinct_add_collision
#print axioms collisionCycle_norm_le
#print axioms farTriangle_le_distinct

theorem endpoint_card_square_uniform {τ : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : LargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        12*(P.ordinates.card:ℝ)^2 ≤ P.N := by
  have hb : IsLargeValueBound (41/42) τ (2/7) := by
    have hm := meanSquare_largeValueBound (σ:=41/42) (τ:=τ/6) (by norm_num)
    rw [max_eq_left (by linarith only [hτu] : 1+τ/6-2*(41/42) ≤ 2-2*(41/42))] at hm
    have hp := IsLargeValueBound.of_powered (by norm_num : (1/2:ℝ) ≤ 41/42)
      (by norm_num : (41/42:ℝ) ≤ 1) (by linarith only [hτ] : 0 ≤ τ)
      6 (by omega) hm
    norm_num at hp
    exact hp
  obtain ⟨C₀,hC₀,δ,hδ,hcard⟩ := hb (1/42) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (12*C₀^2) (by positivity)
      0 (η:=8/21) (by norm_num))
  refine ⟨max C₀ N₀,hC₀.trans (le_max_left _ _),δ,hδ,?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR := hcard P ((le_max_left _ _).trans hPN) hTl hTu hVl hVu
  have hc : 12*C₀^2 ≤ P.N^(8/21:ℝ) := by
    simpa only [pow_zero,mul_one] using hN₀ P.N ((le_max_right _ _).trans hPN)
  have hs : 12*(P.ordinates.card:ℝ)^2 ≤ P.N := by
    calc
      _ ≤ 12*(C₀*P.N^(2/7+1/42:ℝ))^2 := by gcongr
      _ = (12*C₀^2)*P.N^(13/21:ℝ) := by
        rw [mul_pow,← Real.rpow_mul_natCast hNp.le]
        norm_num
        ring
      _ ≤ P.N^(8/21:ℝ)*P.N^(13/21:ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _)
      _ = P.N := by rw [← Real.rpow_add hNp]; norm_num
  exact hs

theorem endpoint_collision_absorbed {τ : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : LargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        12*P.N^2*(P.ordinates.card:ℝ)^3 ≤ (P.ordinates.card:ℝ)*P.N^3 := by
  obtain ⟨C,hC,δ,hδ,hs⟩ := endpoint_card_square_uniform hτ hτu
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hPN hTl hTu hVl hVu
  have hm := mul_le_mul_of_nonneg_left (hs P hPN hTl hTu hVl hVu)
    (show 0 ≤ (P.ordinates.card:ℝ)*P.N^2 by positivity)
  nlinarith only [hm]

/-- The actual endpoint reduction after the repeated-frequency error is
absorbed. No bound for the signed distinct-frequency sum is assumed. -/
theorem endpoint_distinct_triangle_reduction {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ((P.ordinates.card:ℝ)*P.V^2-P.N^(2+ε))^3 ≤
          64*P.N^3*((distinctFarTriangle P.toLargeValuePattern (P.N^(7/5:ℝ))).re+
            2*(P.ordinates.card:ℝ)*P.N^(3+ε)) := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hgram⟩ := endpoint_signed_triangle_reduction hτ hτu hε
  obtain ⟨C₁,_,δ₁,hδ₁,hcoll⟩ := endpoint_collision_absorbed hτ hτu
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hg := hgram P ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (sub_le_sub_left (min_le_left δ₀ δ₁) τ)).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (add_le_add le_rfl (min_le_left δ₀ δ₁))))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (sub_le_sub_left (min_le_left δ₀ δ₁) (41/42))).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (add_le_add le_rfl (min_le_left δ₀ δ₁))))
  have hc := hcoll P.toLargeValuePattern ((le_max_right _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (sub_le_sub_left (min_le_right δ₀ δ₁) τ)).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (add_le_add le_rfl (min_le_right δ₀ δ₁))))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (sub_le_sub_left (min_le_right δ₀ δ₁) (41/42))).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (add_le_add le_rfl (min_le_right δ₀ δ₁))))
  have hf := farTriangle_le_distinct P.toLargeValuePattern (P.N^(7/5:ℝ))
  have hn : P.N^3 ≤ P.N^(3+ε) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (show (3:ℝ) ≤ 3+ε by linarith only [hε])
  have he := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg P.ordinates.card)
  exact hg.trans (mul_le_mul_of_nonneg_left (by linarith only [hf,hc,he]) (by positivity))

theorem cyclePhase_eq_log_ratios {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (t u v : ℝ) :
    cyclePhase a b c t u v = Complex.exp (Complex.I*
      (((u-t)*Real.log ((c:ℝ)/a)+(v-u)*Real.log ((c:ℝ)/b):ℝ):ℂ)) := by
  have hap : (a:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hbp : (b:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hcp : (c:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  simp only [cyclePhase,dirichletPhase_eq_exp ha,dirichletPhase_eq_exp hb,
    dirichletPhase_eq_exp hc,← Complex.exp_add,Real.log_div hcp hap,
    Real.log_div hcp hbp]
  congr 1
  push_cast
  ring

#print axioms endpoint_collision_absorbed
#print axioms endpoint_distinct_triangle_reduction
#print axioms cyclePhase_eq_log_ratios

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

/-- An anchored far-correlation inequality for the ACTUAL zeta interval
coefficients. It keeps the anchor at ordinate zero; the other two ordinates
remain in [T,2T], rather than replacing the problem by a translated spectrum. -/
theorem anchor_retained_far (P : ZetaLargeValuePattern) {L : ℝ}
    (hL : 0 ≤ L) (hLN : L ≤ P.N^2) :
    anchorMass P^2 ≤ 2*P.N*
      (nearRowBudget P.toLargeValuePattern L*anchorMass P+(anchorFar P L).re) := by
  let x := fun t : P.ordinates => conj (zetaAnchor P t)
  have hn := hermitian_quadratic_norm_le_row
    (nearMatrix_hermitian P.toLargeValuePattern L)
    (nearMatrix_row_bound P.toLargeValuePattern hL hLN) x
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

def anchoredCycle (P : ZetaLargeValuePattern) (t u : ℝ) : ℂ :=
  ∑ a ∈ P.active, ∑ b ∈ P.indices, ∑ c ∈ P.active, cyclePhase a b c 0 t u

theorem anchoredCycle_eq (P : ZetaLargeValuePattern) (t u : ℝ) :
    anchoredCycle P t u = zetaAnchor P t*conj (zetaAnchor P u)*
      gramKernel P.toLargeValuePattern t u := by
  have hs : ∑ c ∈ P.active,dirichletPhase c (-u) = conj (zetaAnchor P u) := by
    simp only [zetaAnchor,map_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hp := dirichletPhase_mul_star (P.index_pos (P.active_subset hc)) 0 u
    simpa only [zero_sub,dirichletPhase_zero,one_mul,Complex.star_def] using hp.symm
  simp only [anchoredCycle,cyclePhase,sub_zero,zero_sub,
    ← Finset.mul_sum,← Finset.sum_mul,hs,gramKernel,zetaAnchor]
  ring

theorem anchorFar_eq_cycles (P : ZetaLargeValuePattern) (L : ℝ) :
    anchorFar P L = ∑ t : P.ordinates, ∑ u : P.ordinates,
      if L < |(u:ℝ)-t| then anchoredCycle P t u else 0 := by
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  simp only [farMatrix]
  split_ifs
  · exact (anchoredCycle_eq P t u).symm
  · exact mul_zero _

#print axioms zetaAnchor_eq_pattern
#print axioms anchorMass_lower
#print axioms anchorSquare_le_fullGram
#print axioms anchor_retained_far
#print axioms anchoredCycle_eq
#print axioms anchorFar_eq_cycles

/-- The continuous zero-frequency contribution of the actual active interval. -/
def anchorBulk (P : ZetaLargeValuePattern) (t : ℝ) : ℂ :=
  if h : P.active.Nonempty then
    ∫ x : ℝ in (P.active.min' h:ℝ)..(P.active.max' h:ℝ),
      (x:ℂ)^(-(Complex.I*(t:ℂ)))
  else 0

theorem dirichlet_integral_decay {A B t : ℝ} (hA : 0 < A) (hB : 0 < B)
    (ht : 0 < t) :
    ‖∫ x : ℝ in A..B, (x:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤ (A+B)/t := by
  rw [integral_cpow (Or.inl (by simp : (-1:ℝ) < (-(Complex.I*(t:ℂ))).re)),norm_div]
  have hn : ‖(B:ℂ)^(-(Complex.I*(t:ℂ))+1)-
      (A:ℂ)^(-(Complex.I*(t:ℂ))+1)‖ ≤ A+B := by
    have hh := norm_sub_le ((B:ℂ)^(-(Complex.I*(t:ℂ))+1))
      ((A:ℂ)^(-(Complex.I*(t:ℂ))+1))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB,Complex.norm_cpow_eq_rpow_re_of_pos hA] at hh
    simpa [add_comm] using hh
  have hd : t ≤ ‖-(Complex.I*(t:ℂ))+1‖ := by
    have hh := Complex.abs_im_le_norm (-(Complex.I*(t:ℂ))+1)
    simpa [abs_of_pos ht] using hh
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) ht hd)

theorem anchorBulk_norm_le (P : ZetaLargeValuePattern) {t : ℝ} (ht : t ∈ P.ordinates) :
    ‖anchorBulk P t‖ ≤ 4*P.N/P.T := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htT : P.T ≤ t := by
    simpa only [P.intervalLeft_eq] using (P.ordinates_in_interval t ht).1
  unfold anchorBulk
  split_ifs with h
  · have ha := P.active_subset (Finset.min'_mem P.active h)
    have hb := P.active_subset (Finset.max'_mem P.active h)
    have haN := (P.mem_indices_iff _).mp ha
    have hbN := (P.mem_indices_iff _).mp hb
    have hsum : (P.active.min' h:ℝ)+(P.active.max' h:ℝ) ≤ 4*P.N := by
      linarith only [haN.2,hbN.2]
    exact (dirichlet_integral_decay (hNp.trans_le haN.1) (hNp.trans_le hbN.1)
      (P.T_pos.trans_le htT)).trans
        ((div_le_div_of_nonneg_right hsum (P.T_pos.le.trans htT)).trans
          (div_le_div_of_nonneg_left (by positivity) P.T_pos htT))
  · rw [norm_zero]
    exact div_nonneg (by positivity) P.T_pos.le

def anchorResidual (P : ZetaLargeValuePattern) (t : ℝ) : ℂ :=
  zetaAnchor P t-anchorBulk P t

def anchorResidualFar (P : ZetaLargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t : P.ordinates, ∑ u : P.ordinates,
    anchorResidual P t*conj (anchorResidual P u)*farMatrix P.toLargeValuePattern L t u

theorem zetaAnchor_norm_le (P : ZetaLargeValuePattern) (t : ℝ) :
    ‖zetaAnchor P t‖ ≤ 2*P.N := by
  calc
    _ ≤ ∑ n ∈ P.active, ‖dirichletPhase n t‖ := norm_sum_le _ _
    _ = ∑ _n ∈ P.active,(1:ℝ) := Finset.sum_congr rfl (fun _ hn =>
      P.norm_dirichletPhase (P.active_subset hn) t)
    _ = (P.active.card:ℝ) := by simp
    _ ≤ P.indices.card := by exact_mod_cast Finset.card_le_card P.active_subset
    _ ≤ _ := P.indices_card_cast_le_two_mul_N

theorem farMatrix_norm_le (P : LargeValuePattern) (L : ℝ) (t u : P.ordinates) :
    ‖farMatrix P L t u‖ ≤ 2*P.N := by
  unfold farMatrix
  split_ifs
  · calc
      _ ≤ ∑ n ∈ P.indices,‖dirichletPhase n ((u:ℝ)-t)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ P.indices,(1:ℝ) := Finset.sum_congr rfl (fun _ hn =>
        P.norm_dirichletPhase hn ((u:ℝ)-t))
      _ = (P.indices.card:ℝ) := by simp
      _ ≤ _ := P.indices_card_cast_le_two_mul_N
  · rw [norm_zero]
    have := P.one_lt_N
    linarith

/-- Actual analytic removal of the continuous zero mode from the signed
anchored far correlation. Both cross terms are included. -/
theorem anchorFar_bulk_error (P : ZetaLargeValuePattern) (hT : 1 ≤ P.T) (L : ℝ) :
    ‖anchorFar P L-anchorResidualFar P L‖ ≤
      64*P.N^3/P.T*(P.ordinates.card:ℝ)^2 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hz (t : P.ordinates) : ‖zetaAnchor P t‖ ≤ 2*P.N := zetaAnchor_norm_le P t
  have hb (t : P.ordinates) : ‖anchorBulk P t‖ ≤ 4*P.N/P.T := anchorBulk_norm_le P t.property
  have hr (t : P.ordinates) : ‖anchorResidual P t‖ ≤ 6*P.N := by
    have hdiv : 4*P.N/P.T ≤ 4*P.N := (div_le_self (by positivity) hT)
    exact (norm_sub_le _ _).trans (by linarith only [hz t,hb t,hdiv])
  have hpoint (t u : P.ordinates) :
      ‖zetaAnchor P t*conj (zetaAnchor P u)*farMatrix P.toLargeValuePattern L t u-
        anchorResidual P t*conj (anchorResidual P u)*farMatrix P.toLargeValuePattern L t u‖ ≤
        64*P.N^3/P.T := by
    have he : zetaAnchor P t*conj (zetaAnchor P u)-
        anchorResidual P t*conj (anchorResidual P u) =
        anchorBulk P t*conj (zetaAnchor P u)+anchorResidual P t*conj (anchorBulk P u) := by
      simp only [anchorResidual,map_sub]
      ring
    rw [← sub_mul,he,norm_mul]
    have hp : ‖anchorBulk P t*conj (zetaAnchor P u)+
        anchorResidual P t*conj (anchorBulk P u)‖ ≤
        (4*P.N/P.T)*(2*P.N)+(6*P.N)*(4*P.N/P.T) := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul,Complex.norm_conj]
      gcongr
      · exact hb t
      · exact hz u
      · exact hr t
      · exact hb u
    calc
      _ ≤ ((4*P.N/P.T)*(2*P.N)+(6*P.N)*(4*P.N/P.T))*(2*P.N) :=
        mul_le_mul hp (farMatrix_norm_le _ _ _ _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold anchorFar anchorResidualFar
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t : P.ordinates, ∑ _u : P.ordinates, 64*P.N^3/P.T := by
      apply Finset.sum_le_sum
      intro t _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => hpoint t u))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

#print axioms dirichlet_integral_decay
#print axioms anchorBulk_norm_le
#print axioms zetaAnchor_norm_le
#print axioms farMatrix_norm_le
#print axioms anchorFar_bulk_error

theorem endpoint_anchor_bulk_absorbed {τ : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ‖anchorFar P (P.N^(7/5:ℝ))-anchorResidualFar P (P.N^(7/5:ℝ))‖ ≤ 1 := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hcard⟩ := endpoint_card_square_uniform hτ hτu
  refine ⟨max C₀ 64,hC₀.trans (le_max_left _ _),min δ₀ (1/7),
    lt_min hδ₀ (by norm_num),?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have h64 : 64 ≤ P.N := (le_max_right _ _).trans hPN
  have hd := min_le_left δ₀ (1/7:ℝ)
  have hd1 := min_le_right δ₀ (1/7:ℝ)
  have hc := hcard P.toLargeValuePattern ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
  have hc' : (P.ordinates.card:ℝ)^2 ≤ P.N := by nlinarith only [hc,sq_nonneg (P.ordinates.card:ℝ)]
  have hNT : P.N^5 ≤ P.T := by
    have hpow := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show (5:ℝ) ≤ τ-min δ₀ (1/7) by linarith only [hτ,hd1])
    have hh : P.N^5 ≤ P.N^(τ-min δ₀ (1/7)) := by
      simpa only [Real.rpow_ofNat] using hpow
    exact hh.trans hTl
  have hT : 1 ≤ P.T := (one_le_pow₀ P.one_lt_N.le).trans hNT
  have he := anchorFar_bulk_error P hT (P.N^(7/5:ℝ))
  have hsize : 64*P.N^4 ≤ P.T := by
    have hm := mul_le_mul_of_nonneg_right h64 (pow_nonneg hNp.le 4)
    nlinarith only [hm,hNT]
  apply he.trans
  calc
    _ ≤ 64*P.N^3/P.T*P.N := mul_le_mul_of_nonneg_left hc' (by positivity)
    _ = (64*P.N^4)/P.T := by ring
    _ ≤ 1 := (div_le_one P.T_pos).mpr hsize

/-- A second, zeta-specific route to the endpoint. The near form and the
continuous zero-mode contribution are discharged, while the exact signed
high-height discrete residual correlation is preserved. -/
theorem endpoint_anchored_residual_dichotomy {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card:ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
        (P.ordinates.card:ℝ)^2*P.V^4 ≤
          4*P.N*((anchorResidualFar P (P.N^(7/5:ℝ))).re+1) := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hnear⟩ := endpoint_nearRowBudget_uniform hτ hτu hε
  obtain ⟨C₁,_,δ₁,hδ₁,hbulk⟩ := endpoint_anchor_bulk_absorbed hτ hτu
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hd₀ := min_le_left δ₀ δ₁
  have hd₁ := min_le_right δ₀ δ₁
  have hn := hnear P.toLargeValuePattern ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])))
  have hb := hbulk P ((le_max_right _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₁])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₁])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₁])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₁])))
  have hL := Real.rpow_nonneg hNp.le (7/5:ℝ)
  have hLN : P.N^(7/5:ℝ) ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (7/5:ℝ) ≤ 2)
  have hg := anchor_retained_far P hL hLN
  have hf : (anchorFar P (P.N^(7/5:ℝ))).re ≤
      (anchorResidualFar P (P.N^(7/5:ℝ))).re+1 := by
    have hh := (Complex.re_le_norm _).trans hb
    rw [Complex.sub_re] at hh
    linarith only [hh]
  have hmass : 0 ≤ anchorMass P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn' := mul_le_mul_of_nonneg_right hn hmass
  have hmain : anchorMass P^2 ≤ 2*P.N*
      (P.N^(1+ε)*anchorMass P+(anchorResidualFar P (P.N^(7/5:ℝ))).re+1) := by
    exact hg.trans (mul_le_mul_of_nonneg_left (by linarith only [hn',hf]) (by positivity))
  have he : P.N*P.N^(1+ε) = P.N^(2+ε) := by
    conv_lhs => lhs; rw [← Real.rpow_one P.N]
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hl := anchorMass_lower P
  by_cases hs : anchorMass P ≤ 4*P.N^(2+ε)
  · exact Or.inl (hl.trans hs)
  · right
    have hs' : 4*P.N^(2+ε) ≤ anchorMass P := (lt_of_not_ge hs).le
    have hm := mul_le_mul_of_nonneg_right hs' hmass
    have hsq := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card:ℝ)*P.V^2 by positivity) hl 2
    have he' : 2*P.N*(P.N^(1+ε)*anchorMass P+
        (anchorResidualFar P (P.N^(7/5:ℝ))).re+1) =
        2*P.N^(2+ε)*anchorMass P+2*P.N*((anchorResidualFar P (P.N^(7/5:ℝ))).re+1) := by
      calc
        _ = 2*(P.N*P.N^(1+ε))*anchorMass P+
          2*P.N*((anchorResidualFar P (P.N^(7/5:ℝ))).re+1) := by ring
        _ = _ := by rw [he]
    rw [he'] at hmain
    nlinarith only [hmain,hm,hsq]

#print axioms endpoint_card_square_uniform
#print axioms endpoint_anchor_bulk_absorbed
#print axioms endpoint_anchored_residual_dichotomy

#print axioms gramKernel_conj
#print axioms farMatrix_hermitian
#print axioms nearMatrix_hermitian
#print axioms near_add_far
#print axioms fullMatrix_posSemidef
#print axioms nearMatrix_row_bound
#print axioms hermitian_quadratic_norm_le_row
#print axioms star_dot_self_eq
#print axioms hermitian_quadratic_le_max
#print axioms hermitian_quadratic_cube_le
#print axioms weighted_gram_energy

example (P : LargeValuePattern) (t : P.ordinates) : farMatrix P 0 t t = 0 := by
  simp only [farMatrix,sub_self,abs_zero,lt_self_iff_false,ite_false]

example {a : ℕ} (ha : 0 < a) (t u v : ℝ) : cyclePhase a a a t u v = 1 := by
  rw [cyclePhase_eq_log_ratios ha ha ha]
  simp [show (a:ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt ha]

example (P : ZetaLargeValuePattern) (h : P.active = ∅) (t : ℝ) :
    anchorBulk P t = 0 := by simp [anchorBulk,h]

example (P : ZetaLargeValuePattern) (hT : 1 ≤ P.T) (L : ℝ) :
    ‖anchorFar P L-anchorResidualFar P L‖ ≤ 64*P.N^3/P.T*(P.ordinates.card:ℝ)^2 :=
  anchorFar_bulk_error P hT L

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card:ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
        (P.ordinates.card:ℝ)^2*P.V^4 ≤
          4*P.N*((anchorResidualFar P (P.N^(7/5:ℝ))).re+1) :=
  endpoint_anchored_residual_dichotomy (by norm_num) (by norm_num) hε

/-- Both signs of the continuous Dirichlet integral, needed for the two
orientations of an actual far pair. -/
theorem dirichlet_integral_abs_decay {A B t : ℝ} (hA : 0 < A) (hB : 0 < B)
    (ht : t ≠ 0) :
    ‖∫ x : ℝ in A..B, (x:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤ (A+B)/|t| := by
  rw [integral_cpow (Or.inl (by simp : (-1:ℝ) < (-(Complex.I*(t:ℂ))).re)),norm_div]
  have hn : ‖(B:ℂ)^(-(Complex.I*(t:ℂ))+1)-
      (A:ℂ)^(-(Complex.I*(t:ℂ))+1)‖ ≤ A+B := by
    have hh := norm_sub_le ((B:ℂ)^(-(Complex.I*(t:ℂ))+1))
      ((A:ℂ)^(-(Complex.I*(t:ℂ))+1))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB,Complex.norm_cpow_eq_rpow_re_of_pos hA] at hh
    simpa [add_comm] using hh
  have hd : |t| ≤ ‖-(Complex.I*(t:ℂ))+1‖ := by
    simpa using Complex.abs_im_le_norm (-(Complex.I*(t:ℂ))+1)
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr ht) hd)

def kernelBulk (P : LargeValuePattern) (s : ℝ) : ℂ :=
  ∫ x : ℝ in P.N..(2*P.N), (x:ℂ)^(-(Complex.I*(s:ℂ)))

def anchorTripleResidualFar (P : ZetaLargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t : P.ordinates, ∑ u : P.ordinates,
    if L < |(u:ℝ)-t| then anchorResidual P t*conj (anchorResidual P u)*
      (gramKernel P.toLargeValuePattern t u-kernelBulk P.toLargeValuePattern (u-t))
    else 0

theorem kernelBulk_far_norm_le (P : LargeValuePattern) {L t u : ℝ}
    (hL : 0 < L) (hfar : L < |u-t|) : ‖kernelBulk P (u-t)‖ ≤ 3*P.N/L := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  calc
    _ ≤ (P.N+2*P.N)/|u-t| := dirichlet_integral_abs_decay hNp (by positivity)
      (abs_pos.mp (hL.trans hfar))
    _ ≤ (P.N+2*P.N)/L := div_le_div_of_nonneg_left (by positivity) hL hfar.le
    _ = _ := by ring

/-- Remove the middle kernel's continuous integral from the ACTUAL signed
far form. The remaining object has discrete residuals in all three factors. -/
theorem anchorResidualFar_middle_error (P : ZetaLargeValuePattern) (hT : 1 ≤ P.T)
    {L : ℝ} (hL : 0 < L) :
    ‖anchorResidualFar P L-anchorTripleResidualFar P L‖ ≤
      108*P.N^3/L*(P.ordinates.card:ℝ)^2 := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hr (t : P.ordinates) : ‖anchorResidual P t‖ ≤ 6*P.N := by
    have hz := zetaAnchor_norm_le P t
    have hb := anchorBulk_norm_le P t.property
    have hdiv : 4*P.N/P.T ≤ 4*P.N := div_le_self (by positivity) hT
    exact (norm_sub_le _ _).trans (by linarith only [hz,hb,hdiv])
  have hpoint (t u : P.ordinates) :
      ‖anchorResidual P t*conj (anchorResidual P u)*farMatrix P.toLargeValuePattern L t u-
        (if L < |(u:ℝ)-t| then anchorResidual P t*conj (anchorResidual P u)*
          (gramKernel P.toLargeValuePattern t u-kernelBulk P.toLargeValuePattern (u-t))
        else 0)‖ ≤ 108*P.N^3/L := by
    by_cases hf : L < |(u:ℝ)-t|
    · simp only [farMatrix,if_pos hf]
      rw [← mul_sub,sub_sub_cancel,norm_mul,norm_mul,Complex.norm_conj]
      calc
        _ ≤ (6*P.N)*(6*P.N)*(3*P.N/L) := by
          gcongr
          · exact hr t
          · exact hr u
          · exact kernelBulk_far_norm_le P.toLargeValuePattern hL hf
        _ = _ := by ring
    · simp only [farMatrix,if_neg hf,mul_zero,sub_self,norm_zero]
      positivity
  unfold anchorResidualFar anchorTripleResidualFar
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t : P.ordinates, ∑ _u : P.ordinates, 108*P.N^3/L := by
      apply Finset.sum_le_sum
      intro t _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => hpoint t u))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

/-- Uniform removal of all three continuous bulk contributions. The exact
signed discrete triple-residual correlation, NOT an assumed majorant,
is the only far-correlation term left in the actual endpoint consumer. -/
theorem endpoint_triple_residual_dichotomy {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card:ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
        (P.ordinates.card:ℝ)^2*P.V^4 ≤
          8*P.N*((anchorTripleResidualFar P (P.N^(7/5:ℝ))).re+1) := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hbase⟩ := endpoint_anchored_residual_dichotomy hτ hτu hε
  refine ⟨max C₀ 864,hC₀.trans (le_max_left _ _),min δ₀ (1/100),
    lt_min hδ₀ (by norm_num),?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hd := min_le_left δ₀ (1/100:ℝ)
  have hd1 := min_le_right δ₀ (1/100:ℝ)
  have hg := hbase P ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd])))
  rcases hg with hg | hg
  · exact Or.inl hg
  · right
    have hT : 1 ≤ P.T := (Real.one_le_rpow P.one_lt_N.le
      (show 0 ≤ τ-min δ₀ (1/100) by linarith only [hτ,hd1])).trans hTl
    have hL : 0 < P.N^(7/5:ℝ) := Real.rpow_pos_of_pos hNp _
    have hv : P.N^(9/10:ℝ) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd1])).trans hVl
    have hv4 : P.N^(18/5:ℝ) ≤ P.V^4 := by
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (9/10:ℝ)) hv 4
      rw [← Real.rpow_mul_natCast hNp.le] at hh
      norm_num at hh
      exact hh
    have hn5 : P.N^5 ≤ P.N^(7/5:ℝ)*P.V^4 := by
      calc
        _ = P.N^(7/5:ℝ)*P.N^(18/5:ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hv4 hL.le
    have hn : 864 ≤ P.N := (le_max_right _ _).trans hPN
    have hscale : 864*P.N^4 ≤ P.N^(7/5:ℝ)*P.V^4 := by
      have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg hNp.le 4)
      nlinarith only [hh,hn5]
    have he := anchorResidualFar_middle_error P hT hL
    have hre := (Complex.re_le_norm _).trans he
    rw [Complex.sub_re] at hre
    have herr : 8*P.N*(108*P.N^3/P.N^(7/5:ℝ)*(P.ordinates.card:ℝ)^2) ≤
        (P.ordinates.card:ℝ)^2*P.V^4 := by
      calc
        _ = (P.ordinates.card:ℝ)^2*(864*P.N^4/P.N^(7/5:ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((div_le_iff₀ hL).mpr (by nlinarith only [hscale])) (sq_nonneg _)
    have hfar := mul_le_mul_of_nonneg_left hre (show 0 ≤ 8*P.N by positivity)
    nlinarith only [hg,herr,hfar]

#print axioms dirichlet_integral_abs_decay
#print axioms kernelBulk_far_norm_le
#print axioms anchorResidualFar_middle_error
#print axioms endpoint_triple_residual_dichotomy

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card:ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
        (P.ordinates.card:ℝ)^2*P.V^4 ≤
          8*P.N*((anchorTripleResidualFar P (P.N^(7/5:ℝ))).re+1) :=
  endpoint_triple_residual_dichotomy (by norm_num) (by norm_num) hε

/-- The actual sharp B-process sum, with the phase and conjugation retained.
Unlike the public norm comparison, this can be multiplied inside a signed
three-factor correlation. The stationary set is the native retained set. -/
def reflectedDirichletSum (N t : ℝ) (a b : ℕ) : ℂ :=
  conj ((Real.fourierChar ((t/(2*Real.pi))*Real.log N) : ℂ) *
    ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
      modelPhaseStationaryMainTerm Real.log (t/(2*Real.pi)) N q)

theorem dirichlet_sharp_complex_reflection {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t : ℝ) (a b : ℕ),
      1 ≤ N → 2*Real.pi ≤ t → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖(∑ n ∈ Finset.Icc a b, dirichletPhase n t)-
        reflectedDirichletSum N t a b‖ ≤
        C*(N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hsource⟩ := modelPhase_source_sharp_comparison
    (by norm_num : (0 : ℝ) < 1) hε
  refine ⟨C,hC,?_⟩
  intro N t a b hN ht ha hb
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hT : 1 ≤ t/(2*Real.pi) :=
    (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by simpa using ht)
  have hsum : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      conj ((Real.fourierChar ((t/(2*Real.pi))*Real.log N) : ℂ)*
        Expdb.exponentialSumAt Real.log (t/(2*Real.pi)) N a b) := by
    rw [Expdb.exponentialSumAt,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact_mod_cast hNp.trans_le (ha.trans hna)
    rw [← cpow_im_logModel_identity hnpos hNp t]
    simpa only [dirichletPhase,mul_comm I (t : ℂ)] using cpow_neg_im_eq_star n t
  rw [hsum,reflectedDirichletSum,← map_sub,← mul_sub,norm_conj,norm_mul]
  simp only [Circle.norm_coe,one_mul]
  exact hsource N (t/(2*Real.pi)) a b hN hT ha hb Real.log 0
    (le_min (modelPhaseCurvatureLower_pos (by norm_num : (0 : ℝ) < 1)).le
      (by norm_num))
    (log_approximateModel bufferedLocalStationaryOrder (le_refl 0))

/-- Phase of one negative-imaginary-power stationary contribution. -/
def reflectedLogPhase (t q : ℝ) : ℝ :=
  t*Real.log q-t*Real.log (t/(2*Real.pi))+t+Real.pi/4

def reflectedLogTerm (t q : ℝ) : ℂ :=
  ((Real.sqrt (t/(2*Real.pi))/q : ℝ) : ℂ)*
    Complex.exp (I*(reflectedLogPhase t q : ℂ))

theorem reflected_stationary_term {N t q : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hv : q*N/(t/(2*Real.pi)) ∈ modelPhaseSlopeRange Real.log) :
    conj ((Real.fourierChar ((t/(2*Real.pi))*Real.log N) : ℂ)*
      modelPhaseStationaryMainTerm Real.log (t/(2*Real.pi)) N q) =
      reflectedLogTerm t q := by
  have hT : 0 < t/(2*Real.pi) := by positivity
  have hq := logarithmicStationaryFrequency_pos hT hN hv
  rw [modelPhaseStationaryMainTerm_log hT hN hv,zetaLogReflectionCarrier,
    Real.fourierChar_apply,Real.fourierChar_apply,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne'),
    ← Complex.ofReal_log hq.le]
  simp only [map_mul,map_inv₀,Complex.conj_ofReal,Complex.conj_I,map_neg,
    ← Complex.exp_conj]
  rw [reflectedLogTerm,reflectedLogPhase,
    Real.log_div hT.ne' hN.ne']
  push_cast
  have hphase :
      conj (↑(2*Real.pi) * I * ↑(t/(2*Real.pi)*Real.log N)) +
        conj (↑(2*Real.pi) * I * ↑(t/(2*Real.pi)*
          (Real.log (t/(2*Real.pi))-Real.log N)-t/(2*Real.pi)-1/8)) +
        ↑(Real.log q) * -(-I * ↑(2*Real.pi*(t/(2*Real.pi)))) =
      I*(↑t*↑(Real.log q)-↑t*↑(Real.log (t/(2*Real.pi)))+↑t+↑Real.pi/4) := by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  calc
    _ = ((↑(Real.sqrt (t/(2*Real.pi))) : ℂ)/↑q)*
        Complex.exp (conj (↑(2*Real.pi) * I * ↑(t/(2*Real.pi)*Real.log N)) +
          conj (↑(2*Real.pi) * I * ↑(t/(2*Real.pi)*
            (Real.log (t/(2*Real.pi))-Real.log N)-t/(2*Real.pi)-1/8)) +
          ↑(Real.log q) * -(-I * ↑(2*Real.pi*(t/(2*Real.pi))))) := by
      simp only [Complex.exp_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring_nf
    _ = _ := by rw [hphase]

#print axioms dirichlet_sharp_complex_reflection
#print axioms reflected_stationary_term

theorem reflectedDirichletSum_eq {N t : ℝ} (hN : 0 < N) (ht : 0 < t)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    reflectedDirichletSum N t a b =
      ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
        reflectedLogTerm t q := by
  rw [reflectedDirichletSum,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact reflected_stationary_term hN ht
    (logarithmicSharpStationarySet_slope (by positivity) hN ha hb hq)

/-- Angular phase of the actual reflected triple. Its joint stationary locus
is the additive relation q+r=s, not three independent logarithmic phases. -/
def reflectedAngularPhase (q r s x : ℝ) : ℝ :=
  x*Real.log q+(1-x)*Real.log r-
    x*Real.log x-(1-x)*Real.log (1-x)-Real.log s

theorem reflected_triple_phase {u x : ℝ} (hu : 0 < u) (hx : 0 < x)
    (hx1 : x < 1) (q r s : ℝ) :
    reflectedLogPhase (u*x) q+reflectedLogPhase (u*(1-x)) r-
      reflectedLogPhase u s = u*reflectedAngularPhase q r s x+Real.pi/4 := by
  have hm : 0 < 1-x := by linarith
  simp only [reflectedLogPhase,reflectedAngularPhase,
    Real.log_div (mul_pos hu hx).ne' (by positivity : (2*Real.pi : ℝ) ≠ 0),
    Real.log_div (mul_pos hu hm).ne' (by positivity : (2*Real.pi : ℝ) ≠ 0),
    Real.log_div hu.ne' (by positivity : (2*Real.pi : ℝ) ≠ 0),
    Real.log_mul hu.ne' hx.ne',Real.log_mul hu.ne' hm.ne']
  ring

theorem reflected_triple_term {u x : ℝ} (hu : 0 < u) (hx : 0 < x)
    (hx1 : x < 1) (q r s : ℝ) :
    reflectedLogTerm (u*x) q*reflectedLogTerm (u*(1-x)) r*
      conj (reflectedLogTerm u s) =
      (((Real.sqrt (u*x/(2*Real.pi))/q)*
        (Real.sqrt (u*(1-x)/(2*Real.pi))/r)*
        (Real.sqrt (u/(2*Real.pi))/s) : ℝ) : ℂ)*
      Complex.exp (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ)) := by
  rw [← reflected_triple_phase hu hx hx1 q r s]
  simp only [reflectedLogTerm,map_mul,Complex.conj_ofReal,← Complex.exp_conj,
    Complex.conj_I]
  push_cast
  simp only [mul_sub,mul_add,Complex.exp_sub,Complex.exp_add,div_eq_mul_inv,
    ← Complex.exp_neg]
  ring_nf

def reflectedAngularSlope (q r x : ℝ) : ℝ :=
  Real.log q-Real.log r+Real.log (1-x)-Real.log x

theorem hasDerivAt_reflectedAngularPhase {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (q r s : ℝ) :
    HasDerivAt (reflectedAngularPhase q r s) (reflectedAngularSlope q r x) x := by
  have hm : 1-x ≠ 0 := by linarith
  have hid := hasDerivAt_id x
  have hsub := (hasDerivAt_const x (1 : ℝ)).sub hid
  have hlog := Real.hasDerivAt_log hx.ne'
  have hlogsub := hsub.log hm
  convert ((((hid.mul_const (Real.log q)).add
    (hsub.mul_const (Real.log r))).sub (hid.mul hlog)).sub
    (hsub.mul hlogsub)).sub_const (Real.log s) using 1
  dsimp [reflectedAngularSlope]
  field_simp
  ring

theorem reflectedAngularSlope_antitone (q r : ℝ) :
    AntitoneOn (reflectedAngularSlope q r) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hlog := Real.log_le_log hx.1 hxy
  have hlogsub := Real.log_le_log (by linarith [hy.2] : 0 < 1-y)
    (by linarith : 1-y ≤ 1-x)
  dsimp [reflectedAngularSlope]
  linarith

theorem reflectedAngularSlope_eq_log_ratio {q r x : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hx : 0 < x) (hx1 : x < 1) :
    reflectedAngularSlope q r x = Real.log (q*(1-x)/(r*x)) := by
  rw [Real.log_div (mul_pos hq (by linarith)).ne' (mul_pos hr hx).ne',
    Real.log_mul hq.ne' (by linarith : 1-x ≠ 0),Real.log_mul hr.ne' hx.ne']
  dsimp [reflectedAngularSlope]
  ring

#print axioms reflectedDirichletSum_eq
#print axioms reflected_triple_phase
#print axioms reflected_triple_term
#print axioms hasDerivAt_reflectedAngularPhase
#print axioms reflectedAngularSlope_antitone
#print axioms reflectedAngularSlope_eq_log_ratio

/-- Actual oscillatory cancellation to the left of the transverse saddle.
No exponential-sum or correlation estimate is assumed. -/
theorem norm_reflectedAngular_integral_left {q r u a b : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hsaddle : b < q/(q+r)) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2/(u*Real.log (q*(1-b)/(r*b))) := by
  have hbpos : 0 < b := ha.trans_le hab
  have hqb : (q+r)*b < q := by
    have hh := (lt_div_iff₀ (by positivity : 0 < q+r)).mp hsaddle
    nlinarith
  have hratio : 1 < q*(1-b)/(r*b) := by
    apply (lt_div_iff₀ (mul_pos hr hbpos)).mpr
    nlinarith
  have hslope : 0 < reflectedAngularSlope q r b := by
    rw [reflectedAngularSlope_eq_log_ratio hq hr hbpos hb]
    exact Real.log_pos hratio
  let φ := fun x => (u*reflectedAngularPhase q r s x+Real.pi/4)/(2*Real.pi)
  have hmem (x : ℝ) (hx : x ∈ Set.Icc a b) : x ∈ Set.Ioo 0 1 :=
    ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :
      deriv φ x = u*reflectedAngularSlope q r x/(2*Real.pi) := by
    exact ((((hasDerivAt_reflectedAngularPhase (hmem x hx).1 (hmem x hx).2 q r s).const_mul
      u).add_const (Real.pi/4)).div_const (2*Real.pi)).deriv
  have h := norm_phaseIntegral_le_of_positive_slope hab
    (by positivity : 0 < u*reflectedAngularSlope q r b/(2*Real.pi))
    (φ := φ)
    (by
      intro x hx
      dsimp [φ,reflectedAngularPhase]
      fun_prop (disch := first | exact (hmem x hx).1.ne' | linarith [(hmem x hx).2]))
    (by
      intro x hx
      rw [hd x hx]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (reflectedAngularSlope_antitone q r (hmem x hx) ⟨hbpos,hb⟩ hx.2)
          hu.le) (by positivity))
    (by
      intro x hx y hy hxy
      rw [hd x hx,hd y hy]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (reflectedAngularSlope_antitone q r (hmem x hx) (hmem y hy) hxy)
          hu.le) (by positivity))
  have heq : (fun x => Complex.exp (2*Real.pi*I*(φ x : ℂ))) =
      (fun x => Complex.exp
        (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))) := by
    funext x
    congr 1
    dsimp [φ]
    push_cast
    field_simp
  rw [heq] at h
  apply h.trans_eq
  rw [reflectedAngularSlope_eq_log_ratio hq hr hbpos hb]
  field_simp

#print axioms norm_reflectedAngular_integral_left

theorem reflectedAngularPhase_swap (q r s x : ℝ) :
    reflectedAngularPhase q r s (1-x) = reflectedAngularPhase r q s x := by
  simp only [reflectedAngularPhase,sub_sub_cancel]
  ring

theorem norm_reflectedAngular_integral_right {q r u a b : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hsaddle : q/(q+r) < a) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2/(u*Real.log (r*a/(q*(1-a)))) := by
  have hgap : 1-a < r/(r+q) := by
    have hh := (div_lt_iff₀ (by positivity : 0 < q+r)).mp hsaddle
    apply (lt_div_iff₀ (by positivity : 0 < r+q)).mpr
    nlinarith
  have h := norm_reflectedAngular_integral_left hr hq hu
    (by linarith : 0 < 1-b) (by linarith : 1-b ≤ 1-a)
    (by linarith : 1-a < 1) hgap s
  have heq : (fun x => Complex.exp
      (I*((u*reflectedAngularPhase r q s x+Real.pi/4 : ℝ) : ℂ))) =
      (fun x => Complex.exp
        (I*((u*reflectedAngularPhase q r s (1-x)+Real.pi/4 : ℝ) : ℂ))) := by
    funext x
    rw [reflectedAngularPhase_swap]
  rw [heq,intervalIntegral.integral_comp_sub_left
    (fun x => Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))) 1] at h
  simpa only [sub_sub_cancel] using h

theorem reflectedAngularPhase_at_saddle {q r s : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    reflectedAngularPhase q r s (q/(q+r)) = Real.log ((q+r)/s) ∧
      reflectedAngularSlope q r (q/(q+r)) = 0 := by
  have hsum : 0 < q+r := add_pos hq hr
  have hcomp : 1-q/(q+r) = r/(q+r) := by field_simp; ring
  simp only [reflectedAngularPhase,reflectedAngularSlope,hcomp,
    Real.log_div hq.ne' hsum.ne',Real.log_div hr.ne' hsum.ne',
    Real.log_div hsum.ne' hs.ne']
  constructor
  · field_simp
    ring
  · ring

#print axioms reflectedAngularPhase_swap
#print axioms norm_reflectedAngular_integral_right
#print axioms reflectedAngularPhase_at_saddle

theorem reflectedAngularPhase_le_saddle {q r s x : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) (hx : 0 < x) (hx1 : x < 1) :
    reflectedAngularPhase q r s x ≤ Real.log ((q+r)/s) := by
  have hsum : 0 < q+r := add_pos hq hr
  have hm : 0 < 1-x := by linarith
  have hqlog := Real.log_le_sub_one_of_pos (div_pos hq (mul_pos hx hsum))
  have hrlog := Real.log_le_sub_one_of_pos (div_pos hr (mul_pos hm hsum))
  rw [Real.log_div hq.ne' (mul_pos hx hsum).ne',
    Real.log_mul hx.ne' hsum.ne'] at hqlog
  rw [Real.log_div hr.ne' (mul_pos hm hsum).ne',
    Real.log_mul hm.ne' hsum.ne'] at hrlog
  have hcancel : x*(q/(x*(q+r))-1)+(1-x)*(r/((1-x)*(q+r))-1) = 0 := by
    field_simp
    ring
  have hleft := mul_le_mul_of_nonneg_left hqlog hx.le
  have hright := mul_le_mul_of_nonneg_left hrlog hm.le
  rw [reflectedAngularPhase,Real.log_div hsum.ne' hs.ne']
  nlinarith

/-- Radial cancellation above the additive-frequency cone, uniformly over
the entire angular interval. This is an estimate for the actual complex
phase of the reflected triple, not an assumed correlation bound. -/
theorem norm_reflectedRadial_integral_above_cone {q r s x A B : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hs : q+r < s)
    (hx : 0 < x) (hx1 : x < 1) (hAB : A ≤ B) :
    ‖∫ u in A..B, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2/Real.log (s/(q+r)) := by
  have hsum : 0 < q+r := add_pos hq hr
  have hspos : 0 < s := hsum.trans hs
  have hgap : 0 < Real.log (s/(q+r)) :=
    Real.log_pos ((one_lt_div hsum).mpr hs)
  have hF : reflectedAngularPhase q r s x ≤ -Real.log (s/(q+r)) := by
    have hh := reflectedAngularPhase_le_saddle hq hr hspos hx hx1
    rw [Real.log_div hsum.ne' hspos.ne'] at hh
    rw [Real.log_div hspos.ne' hsum.ne']
    linarith
  let φ := fun u => (u*reflectedAngularPhase q r s x+Real.pi/4)/(2*Real.pi)
  have hd (u : ℝ) : deriv φ u = reflectedAngularPhase q r s x/(2*Real.pi) := by
    simpa only [one_mul] using ((((hasDerivAt_id u).mul_const
      (reflectedAngularPhase q r s x)).add_const (Real.pi/4)).div_const (2*Real.pi)).deriv
  have h := norm_phaseIntegral_le_of_negative_slope hAB
    (by positivity : 0 < Real.log (s/(q+r))/(2*Real.pi))
    (φ := φ) (by intro u _; dsimp [φ]; fun_prop)
    (by
      intro u _
      rw [hd,← neg_div]
      exact div_le_div_of_nonneg_right hF (by positivity))
    (by intro u _ v _ _; rw [hd,hd])
  have heq : (fun u => Complex.exp (2*Real.pi*I*(φ u : ℂ))) =
      (fun u => Complex.exp
        (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))) := by
    funext u
    congr 1
    dsimp [φ]
    push_cast
    field_simp
  rw [heq] at h
  apply h.trans_eq
  field_simp

#print axioms reflectedAngularPhase_le_saddle
#print axioms norm_reflectedRadial_integral_above_cone

private theorem saddle_distance_le_log_ratio {q r b : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hb : 0 < b) (hb1 : b < 1)
    (hgap : b ≤ q/(q+r)) :
    q/(q+r)-b ≤ Real.log (q*(1-b)/(r*b)) := by
  have hsum : 0 < q+r := add_pos hq hr
  have hden : 0 < q*(1-b) := mul_pos hq (by linarith)
  have hnum : 0 ≤ q-(q+r)*b := by
    have hh := (le_div_iff₀ hsum).mp hgap
    nlinarith
  have hdenle : q*(1-b) ≤ q+r := by nlinarith
  have hdiv := div_le_div_of_nonneg_left hnum hden hdenle
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hden (mul_pos hr hb))
  have hid : q/(q+r)-b = (q-(q+r)*b)/(q+r) := by field_simp
  have hother : 1-(q*(1-b)/(r*b))⁻¹ = (q-(q+r)*b)/(q*(1-b)) := by
    field_simp [(sub_pos.mpr hb1).ne']
    ring
  rw [hid]
  exact hdiv.trans (hother ▸ hlog)

theorem norm_reflectedAngular_integral_left_gap {q r u a b δ : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hδ : 0 < δ)
    (hgap : b+δ ≤ q/(q+r)) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤ 2/(u*δ) := by
  have hg : b < q/(q+r) := by linarith
  have hh := saddle_distance_le_log_ratio hq hr (ha.trans_le hab) hb hg.le
  have hl : δ ≤ Real.log (q*(1-b)/(r*b)) := by linarith
  exact (norm_reflectedAngular_integral_left hq hr hu ha hab hb hg s).trans
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hu hδ)
      (mul_le_mul_of_nonneg_left hl hu.le))

theorem norm_reflectedAngular_integral_right_gap {q r u a b δ : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hδ : 0 < δ)
    (hgap : q/(q+r)+δ ≤ a) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤ 2/(u*δ) := by
  have hsum : 0 < q+r := add_pos hq hr
  have hcompl : r/(r+q) = 1-q/(q+r) := by field_simp; ring
  have hgap' : (1-a)+δ ≤ r/(r+q) := by rw [hcompl]; linarith
  have h := norm_reflectedAngular_integral_left_gap hr hq hu
    (by linarith : 0 < 1-b) (by linarith : 1-b ≤ 1-a)
    (by linarith : 1-a < 1) hδ hgap' s
  have heq : (fun x => Complex.exp
      (I*((u*reflectedAngularPhase r q s x+Real.pi/4 : ℝ) : ℂ))) =
      (fun x => Complex.exp
        (I*((u*reflectedAngularPhase q r s (1-x)+Real.pi/4 : ℝ) : ℂ))) := by
    funext x
    rw [reflectedAngularPhase_swap]
  rw [heq,intervalIntegral.integral_comp_sub_left
    (fun x => Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))) 1] at h
  simpa only [sub_sub_cancel] using h

#print axioms saddle_distance_le_log_ratio
#print axioms norm_reflectedAngular_integral_left_gap
#print axioms norm_reflectedAngular_integral_right_gap

/-- A uniform transverse oscillation estimate for the actual reflected
triple phase. The saddle is inside, outside, or at an endpoint of the
integration interval; the clipped decomposition treats every case. -/
theorem norm_reflectedAngular_integral_split {q r u a b δ : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (hδ : 0 < δ) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2*δ+4/(u*δ) := by
  let x₀ := q/(q+r)
  let c := max a (min b (x₀-δ))
  let d := max a (min b (x₀+δ))
  let f := fun x => Complex.exp
    (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))
  have hac : a ≤ c := le_max_left _ _
  have hcb : c ≤ b := max_le hab (min_le_left _ _)
  have had : a ≤ d := le_max_left _ _
  have hdb : d ≤ b := max_le hab (min_le_left _ _)
  have hcd : c ≤ d := max_le_max le_rfl (min_le_min_left b (by linarith))
  have hwidth : d-c ≤ 2*δ := by
    have hh := abs_max_sub_max_le_max a (min b (x₀+δ)) a (min b (x₀-δ))
    have hm := abs_min_sub_min_le_max b (x₀+δ) b (x₀-δ)
    have he : x₀+δ-(x₀-δ) = 2*δ := by ring
    simp only [sub_self,abs_zero,he] at hm
    rw [abs_of_pos (by positivity : 0 < 2*δ),
      max_eq_right (by positivity : 0 ≤ 2*δ)] at hm
    simp only [sub_self,abs_zero] at hh
    rw [max_eq_right (abs_nonneg (min b (x₀+δ)-min b (x₀-δ)))] at hh
    exact (le_abs_self (d-c)).trans (hh.trans hm)
  have hnorm (x : ℝ) : ‖f x‖ = 1 := by
    simp [f,Complex.norm_exp]
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := ha.trans_le hx.1
    have hx1 : x < 1 := hx.2.trans_lt hb
    dsimp [f,reflectedAngularPhase]
    fun_prop (disch := first | exact hxpos.ne' | linarith)
  have hi {v w : ℝ} (hav : a ≤ v) (hvw : v ≤ w) (hwb : w ≤ b) :
      IntervalIntegrable f MeasureTheory.volume v w :=
    ContinuousOn.intervalIntegrable_of_Icc hvw (hcont.mono
      (by intro x hx; exact ⟨hav.trans hx.1,hx.2.trans hwb⟩))
  have hleft : ‖∫ x in a..c, f x‖ ≤ 2/(u*δ) := by
    by_cases hca : c = a
    · rw [hca,intervalIntegral.integral_same,norm_zero]
      positivity
    have hcgt : a < c := lt_of_le_of_ne hac (Ne.symm hca)
    have hmin : a < min b (x₀-δ) :=
      (lt_max_iff.mp hcgt).resolve_left (lt_irrefl _)
    have hceq : c = min b (x₀-δ) := max_eq_right hmin.le
    have hcgap : c+δ ≤ q/(q+r) := by
      rw [hceq]
      have hh := min_le_right b (x₀-δ)
      dsimp [x₀] at hh
      linarith
    exact norm_reflectedAngular_integral_left_gap hq hr hu ha hac
      (hcb.trans_lt hb) hδ hcgap s
  have hright : ‖∫ x in d..b, f x‖ ≤ 2/(u*δ) := by
    by_cases hdb' : d = b
    · rw [hdb',intervalIntegral.integral_same,norm_zero]
      positivity
    have hdb'' : d < b := lt_of_le_of_ne hdb hdb'
    have hhigh : x₀+δ < b := by
      by_contra hh
      have he : min b (x₀+δ) = b := min_eq_left (not_lt.mp hh)
      have hdge : b ≤ d := by
        change b ≤ max a (min b (x₀+δ))
        rw [he]
        exact le_max_right _ _
      linarith
    have hdgap : q/(q+r)+δ ≤ d := by
      change x₀+δ ≤ max a (min b (x₀+δ))
      rw [min_eq_right hhigh.le]
      exact le_max_right _ _
    exact norm_reflectedAngular_integral_right_gap hq hr hu (ha.trans_le had)
      hdb hb hδ hdgap s
  have hmiddle : ‖∫ x in c..d, f x‖ ≤ 2*δ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := (1 : ℝ)) (fun x _ => (hnorm x).le)
    simpa only [one_mul,abs_of_nonneg (sub_nonneg.mpr hcd)] using hh.trans
      (by simpa only [one_mul,abs_of_nonneg (sub_nonneg.mpr hcd)] using hwidth)
  have hsplit : (∫ x in a..b, f x) =
      ((∫ x in a..c, f x)+(∫ x in c..d, f x))+(∫ x in d..b, f x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hac hcb)
      (hi hac hcd hdb),
      intervalIntegral.integral_add_adjacent_intervals (hi le_rfl had hdb)
        (hi had hdb le_rfl)]
  change ‖∫ x in a..b, f x‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ (‖∫ x in a..c, f x‖+‖∫ x in c..d, f x‖)+‖∫ x in d..b, f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2/(u*δ)+2*δ+2/(u*δ) := add_le_add (add_le_add hleft hmiddle) hright
    _ = _ := by ring

theorem norm_reflectedAngular_integral_sqrt {q r u a b : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) (s : ℝ) :
    ‖∫ x in a..b, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      6/Real.sqrt u := by
  have hroot : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hh := norm_reflectedAngular_integral_split hq hr hu ha hab hb
    (by positivity : 0 < (Real.sqrt u)⁻¹) s
  apply hh.trans_eq
  have hsq := Real.sq_sqrt hu.le
  field_simp
  nlinarith

#print axioms norm_reflectedAngular_integral_split
#print axioms norm_reflectedAngular_integral_sqrt

theorem norm_reciprocal_reflectedRadial_integral {q r s x A B : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hs : q+r < s)
    (hx : 0 < x) (hx1 : x < 1) (hAB : A ≤ B) :
    ‖((s⁻¹ : ℝ) : ℂ)*∫ u in A..B, Complex.exp
      (I*((u*reflectedAngularPhase q r s x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2/(s-(q+r)) := by
  have hsum : 0 < q+r := add_pos hq hr
  have hspos : 0 < s := hsum.trans hs
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hspos hsum)
  have hprod : s-(q+r) ≤ s*Real.log (s/(q+r)) := by
    have hh := mul_le_mul_of_nonneg_left hlog hspos.le
    have he : s*(1-(s/(q+r))⁻¹) = s-(q+r) := by field_simp
    rwa [he] at hh
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hspos)]
  calc
    _ ≤ s⁻¹*(2/Real.log (s/(q+r))) := mul_le_mul_of_nonneg_left
      (norm_reflectedRadial_integral_above_cone hq hr hs hx hx1 hAB) (by positivity)
    _ = 2/(s*Real.log (s/(q+r))) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hs) hprod

/-- Summed oscillatory cancellation for the reciprocal-weighted integer
dual frequencies strictly above the additive cone. The frequency cost is
harmonic, and no cancellation estimate for the finite sum is hypothesized. -/
theorem norm_reflectedRadial_above_cone_sum {q r x A B : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hx : 0 < x) (hx1 : x < 1)
    (hAB : A ≤ B) (K : ℕ) :
    ‖∫ u in A..B, ∑ j ∈ Finset.Icc 1 K,
      (((q+r+(j : ℝ))⁻¹ : ℝ) : ℂ)*Complex.exp
        (I*((u*reflectedAngularPhase q r (q+r+j) x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2*(harmonic K : ℝ) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 K, 2/(j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjpos : 0 < (j : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hj).1
        rw [intervalIntegral.integral_const_mul]
        simpa only [add_sub_cancel_left] using norm_reciprocal_reflectedRadial_integral
          hq hr (by linarith : q+r < q+r+(j : ℝ)) hx hx1 hAB
      _ = 2*(harmonic K : ℝ) := by
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
          Finset.mul_sum,div_eq_mul_inv]
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

#print axioms norm_reciprocal_reflectedRadial_integral
#print axioms norm_reflectedRadial_above_cone_sum

example (u : ℝ) (hu : 0 < u) :
    ‖∫ x in (1/4 : ℝ)..(3/4 : ℝ), Complex.exp
      (I*((u*reflectedAngularPhase 1 1 2 x+Real.pi/4 : ℝ) : ℂ))‖ ≤
      6/Real.sqrt u :=
  norm_reflectedAngular_integral_sqrt (by norm_num) (by norm_num) hu
    (by norm_num) (by norm_num) (by norm_num) 2

example (A B : ℝ) (hAB : A ≤ B) (K : ℕ) :
    ‖∫ u in A..B, ∑ j ∈ Finset.Icc 1 K,
      (((2+(j : ℝ))⁻¹ : ℝ) : ℂ)*Complex.exp
        (I*((u*reflectedAngularPhase 1 1 (2+j) (1/2)+Real.pi/4 : ℝ) : ℂ))‖ ≤
      2*(harmonic K : ℝ) := by
  simpa only [show (1 : ℝ)+1 = 2 by norm_num] using
    norm_reflectedRadial_above_cone_sum (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) hAB K

/-- The literal q-dependent phase on the additive dual slice q+r=s. -/
def resonantLogSlicePhase (t h s q : ℝ) : ℝ :=
  t*Real.log q+h*Real.log (s-q)

theorem hasDerivAt_resonantLogSlicePhase {q s : ℝ}
    (hq : 0 < q) (hqs : q < s) (t h : ℝ) :
    HasDerivAt (resonantLogSlicePhase t h s) (t/q-h/(s-q)) q := by
  have hsub := (hasDerivAt_const q s).sub (hasDerivAt_id q)
  convert ((Real.hasDerivAt_log hq.ne').const_mul t).add
    ((hsub.log (sub_pos.mpr hqs).ne').const_mul h) using 1
  dsimp
  ring

theorem hasDerivAt_resonantLogSliceSlope {q s : ℝ}
    (hq : 0 < q) (hqs : q < s) (t h : ℝ) :
    HasDerivAt (fun y => t/y-h/(s-y)) (-t/q^2-h/(s-q)^2) q := by
  convert ((hasDerivAt_const q t).div (hasDerivAt_id q) hq.ne').sub
    ((hasDerivAt_const q h).div
      ((hasDerivAt_const q s).sub (hasDerivAt_id q)) (sub_pos.mpr hqs).ne') using 1
  dsimp
  ring

/-- An actual finite-frequency cancellation bound on the additive cone.
The curvature bounds are derived from the two linked positive frequency
boxes; no derivative or exponential-sum estimate is assumed. -/
theorem norm_resonantLogSlice_sum {t h s Q R A : ℝ} (L : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hQ : 0 < Q) (hR : 0 < R)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R)
    (hsmall : (t/Q^2+h/R^2)/(8*Real.pi) ≤ 1) :
    ‖∑ n ∈ Finset.range L,
      Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))‖ ≤
      12*(4*L*Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))+
        2/Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))) := by
  let α := (t/Q^2+h/R^2)/(8*Real.pi)
  have hα : 0 < α := by dsimp [α]; positivity
  let F := fun q => resonantLogSlicePhase t h s q/(2*Real.pi)
  let F' := fun q => (t/q-h/(s-q))/(2*Real.pi)
  let F'' := fun q => (-t/q^2-h/(s-q)^2)/(2*Real.pi)
  have hbox (q : ℝ) (hq : q ∈ Set.Icc A (A+L)) :
      Q ≤ q ∧ q ≤ 2*Q ∧ R ≤ s-q ∧ s-q ≤ 2*R := by
    exact ⟨hQA.trans hq.1,hq.2.trans hAQ,by linarith [hq.2],by linarith [hq.1]⟩
  have hderiv (q : ℝ) (hq : q ∈ Set.Icc A (A+L)) : HasDerivAt F (F' q) q :=
    (hasDerivAt_resonantLogSlicePhase (hQ.trans_le (hbox q hq).1)
      (by linarith [(hbox q hq).2.2.1]) t h).div_const (2*Real.pi)
  have hderiv' (q : ℝ) (hq : q ∈ Set.Icc A (A+L)) : HasDerivAt F' (F'' q) q :=
    (hasDerivAt_resonantLogSliceSlope (hQ.trans_le (hbox q hq).1)
      (by linarith [(hbox q hq).2.2.1]) t h).div_const (2*Real.pi)
  have hcurv (q : ℝ) (hq : q ∈ Set.Icc A (A+L)) :
      -(4*α) ≤ F'' q ∧ F'' q ≤ -α := by
    obtain ⟨hql,hqu,hrl,hru⟩ := hbox q hq
    have hqp : 0 < q := hQ.trans_le hql
    have hrp : 0 < s-q := hR.trans_le hrl
    have hqlo := div_le_div_of_nonneg_left ht.le (sq_pos_of_pos hqp)
      (show q^2 ≤ (2*Q)^2 by nlinarith)
    have hrlo := div_le_div_of_nonneg_left hh.le (sq_pos_of_pos hrp)
      (show (s-q)^2 ≤ (2*R)^2 by nlinarith)
    have hqhi := div_le_div_of_nonneg_left ht.le (sq_pos_of_pos hQ)
      (show Q^2 ≤ q^2 by nlinarith)
    have hrhi := div_le_div_of_nonneg_left hh.le (sq_pos_of_pos hR)
      (show R^2 ≤ (s-q)^2 by nlinarith)
    have hlo : (t/Q^2+h/R^2)/4 ≤ t/q^2+h/(s-q)^2 := by
      calc
        _ = t/(2*Q)^2+h/(2*R)^2 := by ring
        _ ≤ _ := add_le_add hqlo hrlo
    have hhi : t/q^2+h/(s-q)^2 ≤ t/Q^2+h/R^2 := add_le_add hqhi hrhi
    have hl := div_le_div_of_nonneg_right hlo (by positivity : 0 ≤ 2*Real.pi)
    have hu := div_le_div_of_nonneg_right hhi (by positivity : 0 ≤ 2*Real.pi)
    have he : F'' q = -(t/q^2+h/(s-q)^2)/(2*Real.pi) := by dsimp [F'']; ring
    rw [he]
    dsimp [α]
    constructor
    · convert neg_le_neg hu using 1 <;> ring
    · convert neg_le_neg hl using 1 <;> ring
  have hb := continuous_second_derivative_negative_range_bound F F' F'' A L
    (by norm_num : (0 : ℝ) ≤ 4) hα hsmall hderiv hderiv'
    (fun q hq => (hcurv q hq).1) (fun q hq => (hcurv q hq).2)
  have hchar (q : ℝ) : GafniTao.fordAdditiveCharacter (F q) =
      Complex.exp (I*(resonantLogSlicePhase t h s q : ℂ)) := by
    unfold GafniTao.fordAdditiveCharacter
    congr 1
    dsimp [F]
    push_cast
    field_simp
  simpa only [hchar] using hb

#print axioms hasDerivAt_resonantLogSlicePhase
#print axioms hasDerivAt_resonantLogSliceSlope
#print axioms norm_resonantLogSlice_sum

/-- The actual reciprocal weights on an additive dual-frequency slice are
retained. Their variation is derived by telescoping the decreasing first
reciprocal and increasing second reciprocal. Every phase-prefix bound is
obtained from the preceding analytic theorem, not supplied as a premise. -/
theorem norm_weighted_resonantLogSlice_sum {t h s Q R A : ℝ} (L : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hQ : 0 < Q) (hR : 0 < R)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R)
    (hsmall : (t/Q^2+h/R^2)/(8*Real.pi) ≤ 1) :
    ‖∑ n ∈ Finset.range L,
      (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
        Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))‖ ≤
      36/(Q*R)*(4*L*Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))+
        2/Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))) := by
  let α := (t/Q^2+h/R^2)/(8*Real.pi)
  let B := 12*(4*L*Real.sqrt α+2/Real.sqrt α)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let v := fun n : ℕ => (A+(n : ℝ))⁻¹
  let w := fun n : ℕ => (s-(A+n))⁻¹
  let z := fun n : ℕ => Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))
  have hp : ∀ j : ℕ, j ≤ L → ‖∑ i ∈ Finset.range j,z i‖ ≤ B := by
    intro j hj
    have hj' : (j : ℝ) ≤ L := by exact_mod_cast hj
    have hb := norm_resonantLogSlice_sum j ht hh hQ hR hQA
      (by linarith : A+j ≤ 2*Q) (by linarith : R ≤ s-(A+j)) hsR hsmall
    apply hb.trans
    dsimp [B,α]
    gcongr
  have hvw (i : ℕ) (hi : i ≤ L) :
      0 ≤ v i ∧ v i ≤ Q⁻¹ ∧ 0 ≤ w i ∧ w i ≤ R⁻¹ := by
    have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
    have hvi : Q ≤ A+i := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hwi : R ≤ s-(A+i) := by linarith
    dsimp [v,w]
    exact ⟨inv_nonneg.mpr (hQ.trans_le hvi).le,inv_anti₀ hQ hvi,
      inv_nonneg.mpr (hR.trans_le hwi).le,inv_anti₀ hR hwi⟩
  have hvanti (i : ℕ) : v (i+1) ≤ v i := by
    have hvi : 0 < A+i := by have := hQ.trans_le hQA; positivity
    apply inv_anti₀ hvi
    dsimp
    push_cast
    linarith
  have hwmono (i : ℕ) (hi : i+1 ≤ L) : w i ≤ w (i+1) := by
    have hi' : ((i+1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hi
    have hwi : 0 < s-(A+(i+1 : ℕ)) := by linarith
    apply inv_anti₀ hwi
    push_cast
    linarith
  have hdiff (i : ℕ) (hi : i+1 ≤ L) :
      ‖((v (i+1)*w (i+1) : ℝ) : ℂ)-((v i*w i : ℝ) : ℂ)‖ ≤
        R⁻¹*(v i-v (i+1))+Q⁻¹*(w (i+1)-w i) := by
    have hv0 := hvw i (by omega)
    have hv1 := hvw (i+1) hi
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have he : v (i+1)*w (i+1)-v i*w i =
        w (i+1)*(v (i+1)-v i)+v i*(w (i+1)-w i) := by ring
    rw [he]
    calc
      _ ≤ |w (i+1)*(v (i+1)-v i)|+|v i*(w (i+1)-w i)| := abs_add_le _ _
      _ = w (i+1)*(v i-v (i+1))+v i*(w (i+1)-w i) := by
        rw [abs_mul,abs_mul,abs_of_nonneg hv1.2.2.1,abs_of_nonneg hv0.1,
          abs_of_nonpos (sub_nonpos.mpr (hvanti i)),
          abs_of_nonneg (sub_nonneg.mpr (hwmono i hi)),neg_sub]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right hv1.2.2.2 (sub_nonneg.mpr (hvanti i)))
        (mul_le_mul_of_nonneg_right hv0.2.1 (sub_nonneg.mpr (hwmono i hi)))
  have hlast : ‖((v (L-1)*w (L-1) : ℝ) : ℂ)‖ ≤ Q⁻¹*R⁻¹ := by
    have hh := hvw (L-1) (by omega)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh.1 hh.2.2.1)]
    exact mul_le_mul hh.2.1 hh.2.2.2 hh.2.2.1 (by positivity)
  have hvariation : (∑ i ∈ Finset.range (L-1),
      ‖((v (i+1)*w (i+1) : ℝ) : ℂ)-((v i*w i : ℝ) : ℂ)‖) ≤ 2*(Q⁻¹*R⁻¹) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (L-1),
          (R⁻¹*(v i-v (i+1))+Q⁻¹*(w (i+1)-w i)) :=
        Finset.sum_le_sum (fun i hi => hdiff i (by have := Finset.mem_range.mp hi; omega))
      _ = R⁻¹*(v 0-v (L-1))+Q⁻¹*(w (L-1)-w 0) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
          Finset.sum_range_sub',Finset.sum_range_sub]
      _ ≤ _ := by
        have hv0 := hvw 0 (Nat.zero_le L)
        have hvl := hvw (L-1) (by omega)
        have hqinv : 0 ≤ Q⁻¹ := by positivity
        have hrinv : 0 ≤ R⁻¹ := by positivity
        nlinarith [mul_nonneg hrinv hvl.1,mul_nonneg hqinv hv0.2.2.1,
          mul_le_mul_of_nonneg_left hv0.2.1 hrinv,
          mul_le_mul_of_nonneg_left hvl.2.2.2 hqinv]
  have hparts := norm_sum_mul_le_discrete_parts
    (fun i => ((v i*w i : ℝ) : ℂ)) z L
  change ‖∑ n ∈ Finset.range L,((v n*w n : ℝ) : ℂ)*z n‖ ≤ _
  apply hparts.trans
  calc
    _ ≤ Q⁻¹*R⁻¹*B+(∑ i ∈ Finset.range (L-1),
        ‖((v (i+1)*w (i+1) : ℝ) : ℂ)-((v i*w i : ℝ) : ℂ)‖)*B := by
      apply add_le_add
      · exact mul_le_mul hlast (hp L le_rfl) (norm_nonneg _) (by positivity)
      · rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hp (i+1) (by have := Finset.mem_range.mp hi; omega))
          (norm_nonneg _)
    _ ≤ Q⁻¹*R⁻¹*B+2*(Q⁻¹*R⁻¹)*B :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hvariation hB)
    _ = _ := by dsimp [B,α]; ring

#print axioms norm_weighted_resonantLogSlice_sum

theorem reflected_resonant_product (t h s q : ℝ) :
    reflectedLogTerm t q*reflectedLogTerm h (s-q)*conj (reflectedLogTerm (t+h) s) =
      Complex.exp (I*((-t*Real.log (t/(2*Real.pi))-h*Real.log (h/(2*Real.pi))+
        (t+h)*Real.log ((t+h)/(2*Real.pi))-(t+h)*Real.log s+Real.pi/4 : ℝ) : ℂ))*
      ((Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
        Real.sqrt ((t+h)/(2*Real.pi))/s : ℝ) : ℂ)*
      ((q⁻¹*(s-q)⁻¹ : ℝ) : ℂ)*
      Complex.exp (I*(resonantLogSlicePhase t h s q : ℂ)) := by
  simp only [reflectedLogTerm,map_mul,Complex.conj_ofReal,← Complex.exp_conj,
    Complex.conj_I]
  have hphase : reflectedLogPhase t q+reflectedLogPhase h (s-q)-
      reflectedLogPhase (t+h) s =
        (-t*Real.log (t/(2*Real.pi))-h*Real.log (h/(2*Real.pi))+
          (t+h)*Real.log ((t+h)/(2*Real.pi))-(t+h)*Real.log s+Real.pi/4)+
        resonantLogSlicePhase t h s q := by
    dsimp [reflectedLogPhase,resonantLogSlicePhase]
    ring
  have hexp := congrArg (fun y : ℝ => Complex.exp (I*(y : ℂ))) hphase
  push_cast at hexp ⊢
  simp only [mul_sub,mul_add,Complex.exp_sub,Complex.exp_add,div_eq_mul_inv,
    ← Complex.exp_neg] at hexp
  calc
    _ = (↑(Real.sqrt (t/(2*Real.pi)))*↑(Real.sqrt (h/(2*Real.pi)))*
        ↑(Real.sqrt ((t+h)/(2*Real.pi)))/↑s)*((↑q)⁻¹*(↑s-↑q)⁻¹)*
        ((Complex.exp (I*↑(reflectedLogPhase t q))*
          Complex.exp (I*↑(reflectedLogPhase h (s-q))))*
          Complex.exp (-(I*↑(reflectedLogPhase (t+h) s)))) := by ring_nf
    _ = _ := by
      rw [hexp]
      simp only [mul_sub,mul_add,Complex.exp_sub,Complex.exp_add,div_eq_mul_inv,
        ← Complex.exp_neg]
      ring_nf

/-- Cancellation for a literal finite slice of the reflected three-factor
correlation, with all reciprocal amplitudes and the common phase kept. -/
theorem norm_resonant_reflectedTerm_sum {t h s Q R A : ℝ} (L : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hQ : 0 < Q) (hR : 0 < R)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R)
    (hsmall : (t/Q^2+h/R^2)/(8*Real.pi) ≤ 1) :
    ‖∑ n ∈ Finset.range L,
      reflectedLogTerm t (A+n)*reflectedLogTerm h (s-(A+n))*
        conj (reflectedLogTerm (t+h) s)‖ ≤
      (Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
        Real.sqrt ((t+h)/(2*Real.pi))/s)*
      (36/(Q*R)*(4*L*Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))+
        2/Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi)))) := by
  let c := Complex.exp (I*((-t*Real.log (t/(2*Real.pi))-h*Real.log (h/(2*Real.pi))+
    (t+h)*Real.log ((t+h)/(2*Real.pi))-(t+h)*Real.log s+Real.pi/4 : ℝ) : ℂ))
  let M := Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
    Real.sqrt ((t+h)/(2*Real.pi))/s
  have hs : 0 < s := by
    have := hQ.trans_le hQA
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hc : ‖c‖ = 1 := by simp [c,Complex.norm_exp]
  have heq : (∑ n ∈ Finset.range L,
      reflectedLogTerm t (A+n)*reflectedLogTerm h (s-(A+n))*
        conj (reflectedLogTerm (t+h) s)) =
      c*(M : ℂ)*∑ n ∈ Finset.range L,
        (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
          Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact (reflected_resonant_product t h s (A+n)).trans (by dsimp [c,M]; ring)
  rw [heq,norm_mul,norm_mul,hc,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_left
    (norm_weighted_resonantLogSlice_sum L ht hh hQ hR hQA hAQ hRs hsR hsmall) hM

#print axioms reflected_resonant_product
#print axioms norm_resonant_reflectedTerm_sum

/-- Closed summation intervals need no unproved extra unit of room beyond
their last retained frequency. The last point is bounded separately. -/
theorem norm_weighted_resonantLogSlice_sum_closed {t h s Q R A : ℝ} (L : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hQ : 0 < Q) (hR : 0 < R)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R)
    (hsmall : (t/Q^2+h/R^2)/(8*Real.pi) ≤ 1) :
    ‖∑ n ∈ Finset.range (L+1),
      (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
        Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))‖ ≤
      48/(Q*R)*(4*L*Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))+
        2/Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))) := by
  let α := (t/Q^2+h/R^2)/(8*Real.pi)
  have hα : 0 < α := by dsimp [α]; positivity
  have hroot : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hroot1 : Real.sqrt α ≤ 1 := (Real.sqrt_le_one).mpr hsmall
  have hx : Q ≤ A+L := by linarith [Nat.cast_nonneg (α := ℝ) L]
  have hlast :
      ‖(((A+(L : ℝ))⁻¹*(s-(A+L))⁻¹ : ℝ) : ℂ)*
        Complex.exp (I*(resonantLogSlicePhase t h s (A+L) : ℂ))‖ ≤ 1/(Q*R) := by
    have hxpos : 0 < A+L := hQ.trans_le hx
    have hypos : 0 < s-(A+L) := hR.trans_le hRs
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hxpos) (inv_pos.mpr hypos))]
    simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,zero_mul,
      Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
    have hb := mul_le_mul (inv_anti₀ hQ hx) (inv_anti₀ hR hRs)
      (by positivity : 0 ≤ (s-(A+L))⁻¹) (by positivity : 0 ≤ Q⁻¹)
    simpa only [one_div,mul_inv_rev,mul_comm] using hb
  have hbase : 1 ≤ 4*L*Real.sqrt α+2/Real.sqrt α := by
    have hquot : 1 ≤ 2/Real.sqrt α := (le_div_iff₀ hroot).mpr (by linarith)
    have hh : 0 ≤ 4*L*Real.sqrt α := by positivity
    linarith
  rw [Finset.sum_range_succ]
  apply (norm_add_le _ _).trans
  have hb := norm_weighted_resonantLogSlice_sum L ht hh hQ hR hQA hAQ hRs hsR hsmall
  apply (add_le_add hb hlast).trans
  have hQR : 0 < Q*R := mul_pos hQ hR
  have hb' := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hQR.le)
  dsimp [α] at hbase hb'
  simp only [div_eq_mul_inv] at hb' ⊢
  nlinarith [inv_nonneg.mpr hQR.le]

#print axioms norm_weighted_resonantLogSlice_sum_closed

theorem norm_resonant_reflectedTerm_sum_eq {t h s : ℝ}
    (hs : 0 < s) (A : ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L,
      reflectedLogTerm t (A+n)*reflectedLogTerm h (s-(A+n))*
        conj (reflectedLogTerm (t+h) s)‖ =
      (Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
        Real.sqrt ((t+h)/(2*Real.pi))/s)*
      ‖∑ n ∈ Finset.range L,
        (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
          Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))‖ := by
  let c := Complex.exp (I*((-t*Real.log (t/(2*Real.pi))-h*Real.log (h/(2*Real.pi))+
    (t+h)*Real.log ((t+h)/(2*Real.pi))-(t+h)*Real.log s+Real.pi/4 : ℝ) : ℂ))
  let M := Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
    Real.sqrt ((t+h)/(2*Real.pi))/s
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hc : ‖c‖ = 1 := by simp [c,Complex.norm_exp]
  have heq : (∑ n ∈ Finset.range L,
      reflectedLogTerm t (A+n)*reflectedLogTerm h (s-(A+n))*
        conj (reflectedLogTerm (t+h) s)) =
      c*(M : ℂ)*∑ n ∈ Finset.range L,
        (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
          Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact (reflected_resonant_product t h s (A+n)).trans (by dsimp [c,M]; ring)
  rw [heq,norm_mul,norm_mul,hc,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM]

theorem norm_resonant_reflectedTerm_sum_closed {t h s Q R A : ℝ} (L : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hQ : 0 < Q) (hR : 0 < R)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R)
    (hsmall : (t/Q^2+h/R^2)/(8*Real.pi) ≤ 1) :
    ‖∑ n ∈ Finset.range (L+1),
      reflectedLogTerm t (A+n)*reflectedLogTerm h (s-(A+n))*
        conj (reflectedLogTerm (t+h) s)‖ ≤
      (Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
        Real.sqrt ((t+h)/(2*Real.pi))/s)*
      (48/(Q*R)*(4*L*Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi))+
        2/Real.sqrt ((t/Q^2+h/R^2)/(8*Real.pi)))) := by
  have hs : 0 < s := by
    have := hQ.trans_le hQA
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  rw [norm_resonant_reflectedTerm_sum_eq hs]
  exact mul_le_mul_of_nonneg_left
    (norm_weighted_resonantLogSlice_sum_closed L ht hh hQ hR hQA hAQ hRs hsR hsmall)
    (by positivity)

private theorem resonant_physical_scale_bound {N Q R s l : ℝ}
    (hN : 1 ≤ N) (hNR : N ≤ R) (hRQ : R ≤ Q) (hs : 0 < s)
    (hl : 0 ≤ l) (hlR : l ≤ R) :
    (Real.sqrt (2*N*Q)*Real.sqrt (2*N*R)*Real.sqrt (2*N*(Q+R))/s)*
      (48/(Q*R)*(4*l*Real.sqrt (N/(2*Q)+N/(2*R))+
        2/Real.sqrt (N/(2*Q)+N/(2*R)))) ≤ 1536*N^2/s := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := hNp.trans_le hNR
  have hQp : 0 < Q := hRp.trans_le hRQ
  let α := N/(2*Q)+N/(2*R)
  let p := Real.sqrt (N*R)
  let a := Real.sqrt α
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < a := Real.sqrt_pos.mpr hα
  have hp : 0 < p := Real.sqrt_pos.mpr (mul_pos hNp hRp)
  have hαlo : N/(2*R) ≤ α := by
    have hh : 0 ≤ N/(2*Q) := by positivity
    dsimp [α]
    linarith
  have hαhi : α ≤ N/R := by
    have hh := div_le_div_of_nonneg_left hNp.le (by positivity : 0 < 2*R)
      (by linarith : 2*R ≤ 2*Q)
    dsimp [α]
    calc
      _ ≤ N/(2*R)+N/(2*R) := add_le_add hh le_rfl
      _ = _ := by ring
  have hpsq : p^2 = N*R := Real.sq_sqrt (mul_pos hNp hRp).le
  have hasq : a^2 = α := Real.sq_sqrt hα.le
  have hpa : p*a ≤ N := by
    have hh := (le_div_iff₀ hRp).mp hαhi
    have hh' := mul_le_mul_of_nonneg_left hh hNp.le
    apply (sq_le_sq₀ (mul_pos hp ha).le hNp.le).mp
    calc
      _ = (N*R)*α := by rw [mul_pow,hpsq,hasq]
      _ ≤ _ := by nlinarith
  have hdiv : p/a ≤ 2*R := by
    apply (div_le_iff₀ ha).mpr
    apply (sq_le_sq₀ hp.le (by positivity : 0 ≤ 2*R*a)).mp
    rw [hpsq,mul_pow,hasq]
    have hh := (div_le_iff₀ (by positivity : 0 < 2*R)).mp hαlo
    have hh' := mul_le_mul_of_nonneg_left hh hRp.le
    nlinarith [mul_pos hNp hRp]
  have hamp : Real.sqrt (2*N*Q)*Real.sqrt (2*N*R)*Real.sqrt (2*N*(Q+R)) ≤
      4*N*Q*p := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*N*Q),
      ← Real.sqrt_mul (by positivity : 0 ≤ (2*N*Q)*(2*N*R))]
    calc
      _ ≤ Real.sqrt ((4*N*Q)^2*(N*R)) := Real.sqrt_le_sqrt (by
        have hh := mul_le_mul_of_nonneg_left (show Q+R ≤ 2*Q by linarith)
          (by positivity : 0 ≤ 8*N^3*Q*R)
        nlinarith)
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0 ≤ 4*N*Q)]
  have hbracket : p*(4*l*a+2/a) ≤ 8*N*R := by
    have hx := mul_le_mul_of_nonneg_left hpa (by positivity : 0 ≤ 4*l)
    have hy := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    have hz := mul_le_mul_of_nonneg_left hlR (by positivity : 0 ≤ 4*N)
    have hw := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 4*R)
    calc
      _ = 4*l*(p*a)+2*(p/a) := by ring
      _ ≤ _ := by nlinarith
  have hprod : (Real.sqrt (2*N*Q)*Real.sqrt (2*N*R)*Real.sqrt (2*N*(Q+R)))*
      (4*l*a+2/a) ≤ 32*N^2*Q*R := by
    calc
      _ ≤ (4*N*Q*p)*(4*l*a+2/a) := mul_le_mul_of_nonneg_right hamp (by positivity)
      _ = (4*N*Q)*(p*(4*l*a+2/a)) := by ring
      _ ≤ (4*N*Q)*(8*N*R) := mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 48/(s*Q*R))
  change _ ≤ _ at hh
  convert hh using 1 <;> dsimp [a,α] <;> field_simp
  norm_num

#print axioms norm_resonant_reflectedTerm_sum_eq
#print axioms norm_resonant_reflectedTerm_sum_closed
#print axioms resonant_physical_scale_bound

/-- With heights linked to their true dyadic dual scales, the resonant
slice has size O(N^2/s). This is a discrete oscillatory bound for the actual
three reflected factors, including a closed endpoint and its weights. -/
theorem norm_resonant_reflectedTerm_physical_closed {N Q R A s : ℝ} (L : ℕ)
    (hN : 1 ≤ N) (hNR : N ≤ R) (hRQ : R ≤ Q)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R) :
    ‖∑ n ∈ Finset.range (L+1),
      reflectedLogTerm (4*Real.pi*N*Q) (A+n)*
        reflectedLogTerm (4*Real.pi*N*R) (s-(A+n))*
          conj (reflectedLogTerm (4*Real.pi*N*Q+4*Real.pi*N*R) s)‖ ≤
      1536*N^2/s := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := hNp.trans_le hNR
  have hQp : 0 < Q := hRp.trans_le hRQ
  have hs : 0 < s := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hα : ((4*Real.pi*N*Q)/Q^2+(4*Real.pi*N*R)/R^2)/(8*Real.pi) =
      N/(2*Q)+N/(2*R) := by field_simp; ring
  have hsmall : ((4*Real.pi*N*Q)/Q^2+(4*Real.pi*N*R)/R^2)/(8*Real.pi) ≤ 1 := by
    rw [hα]
    have hh := div_le_div_of_nonneg_left hNp.le (by positivity : 0 < 2*R)
      (by linarith : 2*R ≤ 2*Q)
    calc
      _ ≤ N/(2*R)+N/(2*R) := add_le_add hh le_rfl
      _ = N/R := by ring
      _ ≤ 1 := (div_le_one hRp).mpr hNR
  have hb := norm_resonant_reflectedTerm_sum_closed L
    (by positivity : 0 < 4*Real.pi*N*Q) (by positivity : 0 < 4*Real.pi*N*R)
    hQp hRp hQA hAQ hRs hsR hsmall
  apply hb.trans
  have hq : 4*Real.pi*N*Q/(2*Real.pi) = 2*N*Q := by field_simp; ring
  have hr : 4*Real.pi*N*R/(2*Real.pi) = 2*N*R := by field_simp; ring
  have hu : (4*Real.pi*N*Q+4*Real.pi*N*R)/(2*Real.pi) = 2*N*(Q+R) := by
    field_simp
    ring
  rw [hq,hr,hu,hα]
  exact resonant_physical_scale_bound hN hNR hRQ hs (Nat.cast_nonneg L)
    (by linarith : (L : ℝ) ≤ R)

#print axioms norm_resonant_reflectedTerm_physical_closed

/-- The complementary short-height regime is bounded with the literal
amplitude and interval length, without a curvature hypothesis. -/
theorem norm_resonant_reflectedTerm_physical_short {N Q R A s : ℝ} (L : ℕ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRN : R ≤ N) (hRQ : R ≤ Q)
    (hQA : Q ≤ A)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R) :
    ‖∑ n ∈ Finset.range (L+1),
      reflectedLogTerm (4*Real.pi*N*Q) (A+n)*
        reflectedLogTerm (4*Real.pi*N*R) (s-(A+n))*
          conj (reflectedLogTerm (4*Real.pi*N*Q+4*Real.pi*N*R) s)‖ ≤
      8*N^2/s := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQp : 0 < Q := hRp.trans_le hRQ
  have hs : 0 < s := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hLR : (L : ℝ)+1 ≤ 2*R := by linarith
  let t := 4*Real.pi*N*Q
  let h := 4*Real.pi*N*R
  have hw : ‖∑ n ∈ Finset.range (L+1),
      (((A+(n : ℝ))⁻¹*(s-(A+n))⁻¹ : ℝ) : ℂ)*
        Complex.exp (I*(resonantLogSlicePhase t h s (A+n) : ℂ))‖ ≤
      ((L : ℝ)+1)/(Q*R) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _n ∈ Finset.range (L+1),1/(Q*R) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnL : (n : ℝ) ≤ L := by
          exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
        have hq : Q ≤ A+n := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hr : R ≤ s-(A+n) := by linarith
        have hqp : 0 < A+n := hQp.trans_le hq
        have hrp : 0 < s-(A+n) := hRp.trans_le hr
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (mul_pos (inv_pos.mpr hqp) (inv_pos.mpr hrp))]
        simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,zero_mul,
          Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
        have hb := mul_le_mul (inv_anti₀ hQp hq) (inv_anti₀ hRp hr)
          (by positivity : 0 ≤ (s-(A+n))⁻¹) (by positivity : 0 ≤ Q⁻¹)
        simpa only [one_div,mul_inv_rev,mul_comm] using hb
      _ = _ := by simp [div_eq_mul_inv]
  have hamp : Real.sqrt (2*N*Q)*Real.sqrt (2*N*R)*Real.sqrt (2*N*(Q+R)) ≤
      4*N^2*Q := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*N*Q),
      ← Real.sqrt_mul (by positivity : 0 ≤ (2*N*Q)*(2*N*R))]
    calc
      _ ≤ Real.sqrt ((4*N*Q)^2*(N*R)) := Real.sqrt_le_sqrt (by
        have hh := mul_le_mul_of_nonneg_left (show Q+R ≤ 2*Q by linarith)
          (by positivity : 0 ≤ 8*N^3*Q*R)
        nlinarith)
      _ = 4*N*Q*Real.sqrt (N*R) := by
        rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0 ≤ 4*N*Q)]
      _ ≤ 4*N*Q*Real.sqrt (N^2) := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by nlinarith : N*R ≤ N^2)) (by positivity)
      _ = _ := by rw [Real.sqrt_sq hNp.le]; ring
  rw [norm_resonant_reflectedTerm_sum_eq hs]
  apply (mul_le_mul_of_nonneg_left hw (by positivity)).trans
  have hq : t/(2*Real.pi) = 2*N*Q := by dsimp [t]; field_simp; ring
  have hr : h/(2*Real.pi) = 2*N*R := by dsimp [h]; field_simp; ring
  have hu : (t+h)/(2*Real.pi) = 2*N*(Q+R) := by dsimp [t,h]; field_simp; ring
  change (Real.sqrt (t/(2*Real.pi))*Real.sqrt (h/(2*Real.pi))*
    Real.sqrt ((t+h)/(2*Real.pi))/s)*(((L : ℝ)+1)/(Q*R)) ≤ _
  rw [hq,hr,hu]
  calc
    _ ≤ (4*N^2*Q/s)*(2*R/(Q*R)) := mul_le_mul
      (div_le_div_of_nonneg_right hamp hs.le)
      (div_le_div_of_nonneg_right hLR (by positivity)) (by positivity) (by positivity)
    _ = _ := by field_simp; ring

/-- Both linked physical regimes, with a uniform constant and no assumed
analytic prefix or curvature bound. -/
theorem norm_resonant_reflectedTerm_physical {N Q R A s : ℝ} (L : ℕ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQA : Q ≤ A) (hAQ : A+L ≤ 2*Q)
    (hRs : R ≤ s-(A+L)) (hsR : s-A ≤ 2*R) :
    ‖∑ n ∈ Finset.range (L+1),
      reflectedLogTerm (4*Real.pi*N*Q) (A+n)*
        reflectedLogTerm (4*Real.pi*N*R) (s-(A+n))*
          conj (reflectedLogTerm (4*Real.pi*N*Q+4*Real.pi*N*R) s)‖ ≤
      1536*N^2/s := by
  by_cases hNR : N ≤ R
  · exact norm_resonant_reflectedTerm_physical_closed L hN hNR hRQ hQA hAQ hRs hsR
  have hs : 0 < s := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  exact (norm_resonant_reflectedTerm_physical_short L hN hR (not_le.mp hNR).le
    hRQ hQA hRs hsR).trans
    (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg N]) hs.le)

#print axioms norm_resonant_reflectedTerm_physical_short
#print axioms norm_resonant_reflectedTerm_physical

theorem norm_resonant_reflectedTerm_Icc {N Q R s : ℝ} (a b : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRQ : R ≤ Q) (hs : 0 < s)
    (hbox : ∀ q ∈ Finset.Icc a b,
      Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*Q ∧ R ≤ s-q ∧ s-q ≤ 2*R) :
    ‖∑ q ∈ Finset.Icc a b,
      reflectedLogTerm (4*Real.pi*N*Q) q*
        reflectedLogTerm (4*Real.pi*N*R) (s-q)*
          conj (reflectedLogTerm (4*Real.pi*N*Q+4*Real.pi*N*R) s)‖ ≤
      1536*N^2/s := by
  by_cases hab : a ≤ b
  · have ha := hbox a (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
    have hb := hbox b (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩)
    have hlen : a+((b-a).toNat : ℤ) = b := by omega
    have hlenr : (a : ℝ)+((b-a).toNat : ℝ) = (b : ℝ) := by exact_mod_cast hlen
    have hcount : (b+1-a).toNat = (b-a).toNat+1 := by omega
    have h := norm_resonant_reflectedTerm_physical (b-a).toNat hN hR hRQ ha.1
      (by rw [hlenr]; exact hb.2.1)
      (by rw [hlenr]; exact hb.2.2.1) ha.2.2.2
    rw [Int.Icc_eq_finset_map,Finset.sum_map,hcount]
    simpa only [Function.Embedding.trans_apply,Nat.castEmbedding_apply,
      addLeftEmbedding_apply,Int.cast_add,Int.cast_natCast] using h
  · rw [Finset.Icc_eq_empty_of_lt (not_le.mp hab),Finset.sum_empty,norm_zero]
    positivity

#print axioms norm_resonant_reflectedTerm_Icc

/-- One row of the EXACT additive resonance in the two native retained
stationary sets. No dyadic replacement or enlarged summation set is used. -/
def reflectedConeRow (N t h : ℝ) (a b c d : ℕ) (s : ℤ) : ℂ :=
  ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
    if s-q ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d then
      reflectedLogTerm t q*reflectedLogTerm h (s-q)*conj (reflectedLogTerm (t+h) s)
    else 0

theorem norm_reflectedConeRow {N t h : ℝ} (a b c d : ℕ) (s : ℤ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N) (hs : 0 < (s : ℝ)) :
    ‖reflectedConeRow N t h a b c d s‖ ≤ 1536*N^2/(s : ℝ) := by
  classical
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have ht : 0 < t := hh.trans_le hht
  let Q := t/(4*Real.pi*N)
  let R := h/(4*Real.pi*N)
  have hR : 1 ≤ R := (le_div_iff₀ (by positivity)).mpr (by simpa using hmin)
  have hRQ : R ≤ Q := div_le_div_of_nonneg_right hht (by positivity)
  have hQt : 4*Real.pi*N*Q = t := by dsimp [Q]; field_simp
  have hRh : 4*Real.pi*N*R = h := by dsimp [R]; field_simp
  have hwindow (v : ℝ) (hv : 0 < v) (i j : ℕ)
      (hi : N ≤ (i : ℝ)) (hj : (j : ℝ) ≤ 2*N) (q : ℤ)
      (hq : q ∈ modelPhaseSharpStationarySet Real.log (v/(2*Real.pi)) N i j) :
      v/(4*Real.pi*N) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*(v/(4*Real.pi*N)) := by
    have hw := logarithmicSharpStationarySet_window (by positivity) hNp hi hj hq
    have hlo : (v/(2*Real.pi))/(2*N) = v/(4*Real.pi*N) := by ring
    have hhi : (v/(2*Real.pi))/N = 2*(v/(4*Real.pi*N)) := by ring
    rw [hlo,hhi] at hw
    exact ⟨hw.1.le,hw.2.le⟩
  by_cases hlongt : (a : ℝ)/N+4*(Real.sqrt (t/(2*Real.pi)))⁻¹ < (b : ℝ)/N
  · by_cases hlongh : (c : ℝ)/N+4*(Real.sqrt (h/(2*Real.pi)))⁻¹ < (d : ℝ)/N
    · let lo₁ := modelPhaseBufferedPlateauLower Real.log ((b : ℝ)/N)
        ((Real.sqrt (t/(2*Real.pi)))⁻¹) (t/(2*Real.pi)) N
      let hi₁ := modelPhaseBufferedPlateauUpper Real.log ((a : ℝ)/N)
        ((Real.sqrt (t/(2*Real.pi)))⁻¹) (t/(2*Real.pi)) N
      let lo₂ := modelPhaseBufferedPlateauLower Real.log ((d : ℝ)/N)
        ((Real.sqrt (h/(2*Real.pi)))⁻¹) (h/(2*Real.pi)) N
      let hi₂ := modelPhaseBufferedPlateauUpper Real.log ((c : ℝ)/N)
        ((Real.sqrt (h/(2*Real.pi)))⁻¹) (h/(2*Real.pi)) N
      have hset₁ : modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b =
          Finset.Ioo lo₁ hi₁ := modelPhaseSharpStationarySet_of_long hlongt
      have hset₂ : modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d =
          Finset.Ioo lo₂ hi₂ := modelPhaseSharpStationarySet_of_long hlongh
      let lower := max (lo₁+1) (s-hi₂+1)
      let upper := min (hi₁-1) (s-lo₂-1)
      have hfilter : (Finset.Ioo lo₁ hi₁).filter
          (fun q => s-q ∈ Finset.Ioo lo₂ hi₂) = Finset.Icc lower upper := by
        ext q
        simp only [Finset.mem_filter,Finset.mem_Ioo,Finset.mem_Icc,
          lower,upper,max_le_iff,le_min_iff]
        omega
      have hbox : ∀ q ∈ Finset.Icc lower upper,
          Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*Q ∧ R ≤ (s : ℝ)-q ∧ (s : ℝ)-q ≤ 2*R := by
        intro q hq
        rw [← hfilter] at hq
        obtain ⟨hqt,hqh⟩ := Finset.mem_filter.mp hq
        have hqt' : q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b := by
          rwa [hset₁]
        have hqh' : s-q ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d := by
          rwa [hset₂]
        have hwq := hwindow t ht a b ha hb q hqt'
        have hwr := hwindow h hh c d hc hd (s-q) hqh'
        simp only [Int.cast_sub] at hwr
        exact ⟨hwq.1,hwq.2,hwr.1,hwr.2⟩
      have hrow := norm_resonant_reflectedTerm_Icc lower upper hN hR hRQ hs hbox
      rw [reflectedConeRow,hset₁,hset₂,← Finset.sum_filter,hfilter]
      simpa only [hQt,hRh,Int.cast_sub] using hrow
    · rw [reflectedConeRow,modelPhaseSharpStationarySet_of_short (not_lt.mp hlongh)]
      simp only [Finset.notMem_empty,if_false,Finset.sum_const_zero,norm_zero]
      positivity
  · rw [reflectedConeRow,modelPhaseSharpStationarySet_of_short (not_lt.mp hlongt),
      Finset.sum_empty,norm_zero]
    positivity

#print axioms norm_reflectedConeRow

def reflectedCone (N t h : ℝ) (a b c d e f : ℕ) : ℂ :=
  ∑ s ∈ modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f,
    reflectedConeRow N t h a b c d s

/-- The exact additive-resonance part of all THREE native retained dual
sums has size O(N^2), uniformly in the two linked heights. -/
theorem norm_reflectedCone {N t h : ℝ} (a b c d e f : ℕ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    ‖reflectedCone N t h a b c d e f‖ ≤ 3072*N^2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have ht : 0 < t := hh.trans_le hht
  let S := modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f
  let X := (t+h)/(4*Real.pi*N)
  have hX : 1 ≤ X := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hmem (s : ℤ) (hs : s ∈ S) : X ≤ (s : ℝ) ∧ (s : ℝ) ≤ 2*X := by
    have hw := logarithmicSharpStationarySet_window (by positivity) hNp he hf hs
    have hlo : ((t+h)/(2*Real.pi))/(2*N) = X := by dsimp [X]; ring
    have hhi : ((t+h)/(2*Real.pi))/N = 2*X := by dsimp [X]; ring
    rw [hlo,hhi] at hw
    exact ⟨hw.1.le,hw.2.le⟩
  have hcard : (S.card : ℝ) ≤ 2*X := by
    have hc := integer_card_le_interval_length_add_one S (by linarith : X ≤ 2*X) hmem
    linarith
  have hrow (s : ℤ) (hs : s ∈ S) :
      ‖reflectedConeRow N t h a b c d s‖ ≤ 1536*N^2/X :=
    (norm_reflectedConeRow a b c d s hN hmin hht ha hb hc hd
      (hXp.trans_le (hmem s hs).1)).trans
      (div_le_div_of_nonneg_left (by positivity) hXp (hmem s hs).1)
  unfold reflectedCone
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s ∈ S,1536*N^2/X := Finset.sum_le_sum hrow
    _ = (S.card : ℝ)*(1536*N^2/X) := by simp
    _ ≤ (2*X)*(1536*N^2/X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp; ring

#print axioms norm_reflectedCone

/-- The remaining signed dual sum, with the exact complement q+r!=s.
This is the actual finite expression, not an assumed bound for it. -/
def reflectedOffCone (N t h : ℝ) (a b c d e f : ℕ) : ℂ :=
  ∑ s ∈ modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f,
    ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
      ∑ r ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d,
        if q+r = s then 0 else
          reflectedLogTerm t q*reflectedLogTerm h r*conj (reflectedLogTerm (t+h) s)

theorem reflected_product_cone_split {N t h : ℝ} (a b c d e f : ℕ)
    (hN : 0 < N) (ht : 0 < t) (hh : 0 < h)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
      conj (reflectedDirichletSum N (t+h) e f) =
        reflectedCone N t h a b c d e f+reflectedOffCone N t h a b c d e f := by
  classical
  let S₁ := modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b
  let S₂ := modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d
  let S₃ := modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f
  let G := fun q r s : ℤ =>
    reflectedLogTerm t q*reflectedLogTerm h r*conj (reflectedLogTerm (t+h) s)
  have hrow (s : ℤ) : (∑ q ∈ S₁,∑ r ∈ S₂,if q+r=s then G q r s else 0) =
      reflectedConeRow N t h a b c d s := by
    unfold reflectedConeRow
    apply Finset.sum_congr rfl
    intro q _
    have hcond (r : ℤ) : q+r=s ↔ r=s-q := by omega
    simp only [hcond,Finset.sum_ite_eq']
    simp only [G,S₂,Int.cast_sub]
  have hfull : reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
      conj (reflectedDirichletSum N (t+h) e f) =
        ∑ s ∈ S₃,∑ q ∈ S₁,∑ r ∈ S₂,G q r s := by
    rw [reflectedDirichletSum_eq hN ht ha hb,
      reflectedDirichletSum_eq hN hh hc hd,
      reflectedDirichletSum_eq hN (add_pos ht hh) he hf]
    simp only [map_sum]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  rw [hfull,reflectedCone,reflectedOffCone]
  change (∑ s ∈ S₃,∑ q ∈ S₁,∑ r ∈ S₂,G q r s) =
    (∑ s ∈ S₃,reflectedConeRow N t h a b c d s)+
      ∑ s ∈ S₃,∑ q ∈ S₁,∑ r ∈ S₂,if q+r=s then 0 else G q r s
  simp_rw [← hrow,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases heq : q+r=s <;> simp only [heq,if_true,if_false,zero_add,add_zero]

/-- The resonant contribution is actually bounded, rather than left as a
new analytic premise. Only the explicit off-cone signed sum remains. -/
theorem reflected_product_offCone_error {N t h : ℝ} (a b c d e f : ℕ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    ‖reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
        conj (reflectedDirichletSum N (t+h) e f)-
      reflectedOffCone N t h a b c d e f‖ ≤ 3072*N^2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  rw [reflected_product_cone_split a b c d e f hNp (hh.trans_le hht) hh ha hb hc hd he hf,
    add_sub_cancel_right]
  exact norm_reflectedCone a b c d e f hN hmin hht ha hb hc hd he hf

#print axioms reflected_product_cone_split
#print axioms reflected_product_offCone_error

example : ‖reflectedCone 100 (40000*Real.pi) (40000*Real.pi)
    100 200 100 200 100 200‖ ≤ 3072*(100 : ℝ)^2 := by
  apply norm_reflectedCone <;> norm_num
  nlinarith [Real.pi_pos]

example : ‖∑ n ∈ Finset.range 2,
    reflectedLogTerm (4*Real.pi*2*4) (5+n)*
      reflectedLogTerm (4*Real.pi*2*3) (9-(5+n))*
        conj (reflectedLogTerm (4*Real.pi*2*4+4*Real.pi*2*3) 9)‖ ≤
    1536*(2 : ℝ)^2/9 := by
  exact norm_resonant_reflectedTerm_physical 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem norm_dirichletInterval_le {N : ℝ} (t : ℝ) (a b : ℕ)
    (hN : 1 ≤ N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖∑ n ∈ Finset.Icc a b,dirichletPhase n t‖ ≤ 2*N := by
  by_cases hab : a ≤ b
  · have hcard : ((Finset.Icc a b).card : ℝ) ≤ 2*N := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    calc
      _ ≤ ∑ n ∈ Finset.Icc a b,‖dirichletPhase n t‖ := norm_sum_le _ _
      _ = ((Finset.Icc a b).card : ℝ) := by
        have hterm (n : ℕ) (hn : n ∈ Finset.Icc a b) : ‖dirichletPhase n t‖ = 1 := by
          have hnpos : 0 < n := by
            have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
            exact_mod_cast (show (0 : ℝ) < n by linarith)
          rw [dirichletPhase_eq_exp hnpos]
          simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,zero_mul,
            Complex.ofReal_im,mul_zero,sub_zero,Real.exp_zero]
        simp_rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := hcard
  · rw [Finset.Icc_eq_empty_of_lt (by omega),Finset.sum_empty,norm_zero]
    linarith

private theorem triple_product_perturbation {x y z X Y Z : ℂ} {B E : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B)
    (hz : ‖z‖ ≤ B) (heX : ‖x-X‖ ≤ E) (heY : ‖y-Y‖ ≤ E)
    (heZ : ‖z-Z‖ ≤ E) :
    ‖x*y*conj z-X*Y*conj Z‖ ≤ 3*E*(B+E)^2 := by
  have hX : ‖X‖ ≤ B+E := by
    calc
      _ = ‖x-(x-X)‖ := by congr 1; ring
      _ ≤ ‖x‖+‖x-X‖ := norm_sub_le _ _
      _ ≤ B+E := add_le_add hx heX
  have hY : ‖Y‖ ≤ B+E := by
    calc
      _ = ‖y-(y-Y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖y-Y‖ := norm_sub_le _ _
      _ ≤ B+E := add_le_add hy heY
  have hM : 0 ≤ B+E := add_nonneg hB hE
  have hB' : B ≤ B+E := le_add_of_nonneg_right hE
  have hdecomp : x*y*conj z-X*Y*conj Z =
      (x-X)*y*conj z+X*(y-Y)*conj z+X*Y*conj (z-Z) := by
    rw [map_sub]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖(x-X)*y*conj z‖+‖X*(y-Y)*conj z‖+‖X*Y*conj (z-Z)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E*(B+E)*(B+E)+(B+E)*E*(B+E)+(B+E)*(B+E)*E := by
      simp only [norm_mul,norm_conj]
      gcongr
      · exact hy.trans hB'
      · exact hz.trans hB'
      · exact hz.trans hB'
    _ = _ := by ring

/-- Uniform complex reflection of the original triple, including all
three B-process errors. -/
theorem dirichlet_product_reflection_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t h : ℝ) (a b c d e f : ℕ),
      1 ≤ N → 4*Real.pi*N ≤ h → h ≤ t →
      N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      N ≤ (c : ℝ) → (d : ℝ) ≤ 2*N →
      N ≤ (e : ℝ) → (f : ℝ) ≤ 2*N →
      let E := C*(N/Real.sqrt (h/(2*Real.pi))+((t+h)/(2*Real.pi))^ε)
      ‖(∑ n ∈ Finset.Icc a b,dirichletPhase n t)*
          (∑ n ∈ Finset.Icc c d,dirichletPhase n h)*
          conj (∑ n ∈ Finset.Icc e f,dirichletPhase n (t+h))-
        reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
          conj (reflectedDirichletSum N (t+h) e f)‖ ≤ 3*E*(2*N+E)^2 := by
  obtain ⟨C,hC,hsource⟩ := dirichlet_sharp_complex_reflection hε
  refine ⟨C,hC,?_⟩
  intro N t h a b c d e f hN hmin hht ha hb hc hd he hf E
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have ht : 0 < t := hh.trans_le hht
  have hπ : 0 < 2*Real.pi := by positivity
  have htwo : 2*Real.pi ≤ h := by nlinarith [Real.pi_pos]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have herr (v : ℝ) (l r : ℕ) (hlo : h ≤ v) (hhi : v ≤ t+h)
      (hl : N ≤ (l : ℝ)) (hr : (r : ℝ) ≤ 2*N) :
      ‖(∑ n ∈ Finset.Icc l r,dirichletPhase n v)-
        reflectedDirichletSum N v l r‖ ≤ E := by
    apply (hsource N v l r hN (htwo.trans hlo) hl hr).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
    apply add_le_add
    · exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (div_pos hh hπ))
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hlo hπ.le))
    · exact Real.rpow_le_rpow (div_nonneg (hh.le.trans hlo) hπ.le)
        (div_le_div_of_nonneg_right hhi hπ.le) hε.le
  exact triple_product_perturbation (show 0 ≤ 2*N by positivity) hE
    (norm_dirichletInterval_le t a b hN ha hb)
    (norm_dirichletInterval_le h c d hN hc hd)
    (norm_dirichletInterval_le (t+h) e f hN he hf)
    (herr t a b hht (by linarith) ha hb)
    (herr h c d le_rfl (by linarith) hc hd)
    (herr (t+h) e f (by linarith) le_rfl he hf)

/-- The original three Dirichlet sums, with every B-process error retained.
The only remaining large-frequency object is the explicit signed off-cone sum;
its norm or cancellation is not assumed. -/
theorem dirichlet_product_offCone_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t h : ℝ) (a b c d e f : ℕ),
      1 ≤ N → 4*Real.pi*N ≤ h → h ≤ t →
      N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      N ≤ (c : ℝ) → (d : ℝ) ≤ 2*N →
      N ≤ (e : ℝ) → (f : ℝ) ≤ 2*N →
      let E := C*(N/Real.sqrt (h/(2*Real.pi))+((t+h)/(2*Real.pi))^ε)
      ‖(∑ n ∈ Finset.Icc a b,dirichletPhase n t)*
          (∑ n ∈ Finset.Icc c d,dirichletPhase n h)*
          conj (∑ n ∈ Finset.Icc e f,dirichletPhase n (t+h))-
        reflectedOffCone N t h a b c d e f‖ ≤ 3072*N^2+3*E*(2*N+E)^2 := by
  obtain ⟨C,hC,hsource⟩ := dirichlet_product_reflection_error hε
  refine ⟨C,hC,?_⟩
  intro N t h a b c d e f hN hmin hht ha hb hc hd he hf E
  have hprod := hsource N t h a b c d e f hN hmin hht ha hb hc hd he hf
  have hcone := reflected_product_offCone_error a b c d e f hN hmin hht ha hb hc hd he hf
  exact (norm_sub_le_norm_sub_add_norm_sub _
      (reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
        conj (reflectedDirichletSum N (t+h) e f)) _).trans
    (by linarith)

#print axioms norm_dirichletInterval_le
#print axioms triple_product_perturbation
#print axioms dirichlet_product_reflection_error
#print axioms dirichlet_product_offCone_error

private theorem norm_reflectedLogTerm {v q : ℝ} (hq : 0 < q) :
    ‖reflectedLogTerm v q‖ = Real.sqrt (v/(2*Real.pi))/q := by
  rw [reflectedLogTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hq.le)]
  simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,zero_mul,
    Complex.ofReal_im,mul_zero,sub_zero,Real.exp_zero,mul_one]

/-- Actual shifted resonance q+r=s+k, retaining the third frequency s. -/
def reflectedShiftedConeRow (N t h : ℝ) (a b c d : ℕ) (s k : ℤ) : ℂ :=
  (∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
    if s+k-q ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d then
      reflectedLogTerm t q*reflectedLogTerm h ((s+k-q : ℤ) : ℝ)
    else 0)*conj (reflectedLogTerm (t+h) s)

/-- Curvature cancellation persists on EVERY additive translate, not merely
the zero-mismatch surface. The varying third-frequency amplitude is retained. -/
theorem norm_reflectedShiftedConeRow {N t h : ℝ} (a b c d : ℕ) (s k : ℤ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N) (hs : 0 < (s : ℝ)) :
    ‖reflectedShiftedConeRow N t h a b c d s k‖ ≤ 1536*N^2/(s : ℝ) := by
  classical
  let A : ℂ := ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
    if s+k-q ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d then
      reflectedLogTerm t q*reflectedLogTerm h ((s+k-q : ℤ) : ℝ) else 0
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have ht : 0 < t := hh.trans_le hht
  change ‖A*conj (reflectedLogTerm (t+h) s)‖ ≤ _
  by_cases hsk : 0 < ((s+k : ℤ) : ℝ)
  · have hfactor : reflectedConeRow N t h a b c d (s+k) =
        A*conj (reflectedLogTerm (t+h) ((s+k : ℤ) : ℝ)) := by
      dsimp [reflectedConeRow,A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp only [Int.cast_sub,Int.cast_add,zero_mul]
    have hold := norm_reflectedConeRow a b c d (s+k) hN hmin hht ha hb hc hd hsk
    rw [hfactor,norm_mul,norm_conj,norm_reflectedLogTerm hsk] at hold
    have hnumer : ‖A‖*Real.sqrt ((t+h)/(2*Real.pi)) ≤ 1536*N^2 := by
      rw [← mul_div_assoc] at hold
      exact (div_le_div_iff_of_pos_right hsk).mp hold
    rw [norm_mul,norm_conj,norm_reflectedLogTerm hs,← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnumer hs.le
  · have hA : A = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqpos : 0 < (q : ℝ) :=
        (by positivity : 0 < (t/(2*Real.pi))/(2*N)).trans
          (logarithmicSharpStationarySet_window (by positivity) hNp ha hb hq).1
      split_ifs with hr
      · have hrpos : 0 < ((s+k-q : ℤ) : ℝ) :=
          (by positivity : 0 < (h/(2*Real.pi))/(2*N)).trans
            (logarithmicSharpStationarySet_window (by positivity) hNp hc hd hr).1
        simp only [Int.cast_sub] at hrpos
        linarith
      · rfl
    rw [hA,zero_mul,norm_zero]
    positivity

def reflectedShiftedCone (N t h : ℝ) (a b c d e f : ℕ) (k : ℤ) : ℂ :=
  ∑ s ∈ modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f,
    reflectedShiftedConeRow N t h a b c d s k

theorem norm_reflectedShiftedCone {N t h : ℝ} (a b c d e f : ℕ) (k : ℤ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    ‖reflectedShiftedCone N t h a b c d e f k‖ ≤ 3072*N^2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have ht : 0 < t := hh.trans_le hht
  let S := modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f
  let X := (t+h)/(4*Real.pi*N)
  have hX : 1 ≤ X := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hmem (s : ℤ) (hs : s ∈ S) : X ≤ (s : ℝ) ∧ (s : ℝ) ≤ 2*X := by
    have hw := logarithmicSharpStationarySet_window (by positivity) hNp he hf hs
    have hlo : ((t+h)/(2*Real.pi))/(2*N) = X := by dsimp [X]; ring
    have hhi : ((t+h)/(2*Real.pi))/N = 2*X := by dsimp [X]; ring
    rw [hlo,hhi] at hw
    exact ⟨hw.1.le,hw.2.le⟩
  have hcard : (S.card : ℝ) ≤ 2*X := by
    have hc' := integer_card_le_interval_length_add_one S (by linarith : X ≤ 2*X) hmem
    linarith
  have hrow (s : ℤ) (hs : s ∈ S) :
      ‖reflectedShiftedConeRow N t h a b c d s k‖ ≤ 1536*N^2/X :=
    (norm_reflectedShiftedConeRow a b c d s k hN hmin hht ha hb hc hd
      (hXp.trans_le (hmem s hs).1)).trans
      (div_le_div_of_nonneg_left (by positivity) hXp (hmem s hs).1)
  unfold reflectedShiftedCone
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s ∈ S,1536*N^2/X := Finset.sum_le_sum hrow
    _ = (S.card : ℝ)*(1536*N^2/X) := by simp
    _ ≤ (2*X)*(1536*N^2/X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp; ring

#print axioms norm_reflectedLogTerm
#print axioms norm_reflectedShiftedConeRow
#print axioms norm_reflectedShiftedCone

/-- A finite mismatch band in the original three native frequency sets. -/
def reflectedBand (N t h : ℝ) (a b c d e f : ℕ) (K : Finset ℤ) : ℂ :=
  ∑ s ∈ modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f,
    ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
      ∑ r ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d,
        if q+r-s ∈ K then
          reflectedLogTerm t q*reflectedLogTerm h r*conj (reflectedLogTerm (t+h) s)
        else 0

theorem reflectedBand_eq_shifted_sum (N t h : ℝ) (a b c d e f : ℕ) (K : Finset ℤ) :
    reflectedBand N t h a b c d e f K =
      ∑ k ∈ K,reflectedShiftedCone N t h a b c d e f k := by
  classical
  let S₁ := modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b
  let S₂ := modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d
  let S₃ := modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f
  let G (q r s : ℤ) :=
    reflectedLogTerm t q*reflectedLogTerm h r*conj (reflectedLogTerm (t+h) s)
  have hrow (s k : ℤ) : reflectedShiftedConeRow N t h a b c d s k =
      ∑ q ∈ S₁,∑ r ∈ S₂,if k=q+r-s then G q r s else 0 := by
    rw [reflectedShiftedConeRow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    have hcond (r : ℤ) : k=q+r-s ↔ r=s+k-q := by omega
    simp only [hcond,Finset.sum_ite_eq']
    split_ifs <;> simp only [G,zero_mul]
  unfold reflectedBand reflectedShiftedCone
  change (∑ s ∈ S₃,∑ q ∈ S₁,∑ r ∈ S₂,if q+r-s ∈ K then G q r s else 0) =
    ∑ k ∈ K,∑ s ∈ S₃,reflectedShiftedConeRow N t h a b c d s k
  simp_rw [hrow]
  rw [Finset.sum_comm (s := K) (t := S₃)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm (s := K) (t := S₁)]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm (s := K) (t := S₂)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.sum_ite_eq']

/-- A proved O(N^2 |K|) cancellation estimate for the actual finite mismatch
band, uniform in the native cutoffs and both linked heights. -/
theorem norm_reflectedBand {N t h : ℝ} (a b c d e f : ℕ) (K : Finset ℤ)
    (hN : 1 ≤ N) (hmin : 4*Real.pi*N ≤ h) (hht : h ≤ t)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    ‖reflectedBand N t h a b c d e f K‖ ≤ 3072*N^2*(K.card : ℝ) := by
  rw [reflectedBand_eq_shifted_sum]
  calc
    _ ≤ ∑ k ∈ K,‖reflectedShiftedCone N t h a b c d e f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ K,3072*N^2 := Finset.sum_le_sum (fun k _ =>
      norm_reflectedShiftedCone a b c d e f k hN hmin hht ha hb hc hd he hf)
    _ = _ := by simp [mul_comm]

#print axioms reflectedBand_eq_shifted_sum
#print axioms norm_reflectedBand

def reflectedOutsideBand (N t h : ℝ) (a b c d e f : ℕ) (K : Finset ℤ) : ℂ :=
  ∑ s ∈ modelPhaseSharpStationarySet Real.log ((t+h)/(2*Real.pi)) N e f,
    ∑ q ∈ modelPhaseSharpStationarySet Real.log (t/(2*Real.pi)) N a b,
      ∑ r ∈ modelPhaseSharpStationarySet Real.log (h/(2*Real.pi)) N c d,
        if q+r-s ∈ K then 0 else
          reflectedLogTerm t q*reflectedLogTerm h r*conj (reflectedLogTerm (t+h) s)

theorem reflected_product_band_split {N t h : ℝ} (a b c d e f : ℕ) (K : Finset ℤ)
    (hN : 0 < N) (ht : 0 < t) (hh : 0 < h)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hc : N ≤ (c : ℝ)) (hd : (d : ℝ) ≤ 2*N)
    (he : N ≤ (e : ℝ)) (hf : (f : ℝ) ≤ 2*N) :
    reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
      conj (reflectedDirichletSum N (t+h) e f) =
        reflectedBand N t h a b c d e f K+reflectedOutsideBand N t h a b c d e f K := by
  classical
  rw [reflectedDirichletSum_eq hN ht ha hb,
    reflectedDirichletSum_eq hN hh hc hd,
    reflectedDirichletSum_eq hN (add_pos ht hh) he hf]
  simp only [map_sum]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  unfold reflectedBand reflectedOutsideBand
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp only [zero_add,add_zero]

/-- Original Dirichlet triples with an arbitrary finite mismatch band
removed by proved discrete curvature cancellation, and every reflection error
still explicit. No estimate for the signed outside-band sum is assumed. -/
theorem dirichlet_product_outsideBand_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t h : ℝ) (a b c d e f : ℕ) (K : Finset ℤ),
      1 ≤ N → 4*Real.pi*N ≤ h → h ≤ t →
      N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      N ≤ (c : ℝ) → (d : ℝ) ≤ 2*N →
      N ≤ (e : ℝ) → (f : ℝ) ≤ 2*N →
      let E := C*(N/Real.sqrt (h/(2*Real.pi))+((t+h)/(2*Real.pi))^ε)
      ‖(∑ n ∈ Finset.Icc a b,dirichletPhase n t)*
          (∑ n ∈ Finset.Icc c d,dirichletPhase n h)*
          conj (∑ n ∈ Finset.Icc e f,dirichletPhase n (t+h))-
        reflectedOutsideBand N t h a b c d e f K‖ ≤
          3072*N^2*(K.card : ℝ)+3*E*(2*N+E)^2 := by
  obtain ⟨C,hC,hsource⟩ := dirichlet_product_reflection_error hε
  refine ⟨C,hC,?_⟩
  intro N t h a b c d e f K hN hmin hht ha hb hc hd he hf E
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 0 < h := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*N) hmin
  have hprod := hsource N t h a b c d e f hN hmin hht ha hb hc hd he hf
  have hband : ‖reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
      conj (reflectedDirichletSum N (t+h) e f)-
      reflectedOutsideBand N t h a b c d e f K‖ ≤ 3072*N^2*(K.card : ℝ) := by
    rw [reflected_product_band_split a b c d e f K hNp (hh.trans_le hht) hh ha hb hc hd he hf,
      add_sub_cancel_right]
    exact norm_reflectedBand a b c d e f K hN hmin hht ha hb hc hd he hf
  exact (norm_sub_le_norm_sub_add_norm_sub _
      (reflectedDirichletSum N t a b*reflectedDirichletSum N h c d*
        conj (reflectedDirichletSum N (t+h) e f)) _).trans
    (by linarith)

#print axioms reflected_product_band_split
#print axioms dirichlet_product_outsideBand_error

/-- The signed dual remainder on the actual ordered ordinate pair. Reverse
orientation is conjugated, not replaced by an absolute value. -/
def anchorOutsideBand (P : ZetaLargeValuePattern) (a b : ℕ) (K : Finset ℤ)
    (t u : ℝ) : ℂ :=
  if t ≤ u then reflectedOutsideBand P.N t (u-t) a b P.scale (2*P.scale) a b K
  else conj (reflectedOutsideBand P.N u (t-u) a b P.scale (2*P.scale) a b K)

def anchorOutsideBandFar (P : ZetaLargeValuePattern) (a b : ℕ) (K : Finset ℤ)
    (L : ℝ) : ℂ :=
  ∑ t : P.ordinates,∑ u : P.ordinates,
    if L < |(u : ℝ)-t| then anchorOutsideBand P a b K t u else 0

/-- Entry from the ACTUAL zeta pattern into the mismatch decomposition.
All endpoints, orientations, moving stationary sets and reflection errors
are derived from that pattern. No correlation upper bound is an input. -/
theorem anchorFar_outsideBand_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ZetaLargeValuePattern) (L : ℝ) (K : Finset ℤ),
      4*Real.pi*P.N ≤ L → ∃ a b : ℕ, P.active = Finset.Icc a b ∧
      let E := C*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^ε)
      ‖anchorFar P L-anchorOutsideBandFar P a b K L‖ ≤
        (P.ordinates.card : ℝ)^2*(3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2) := by
  obtain ⟨C,hC,hsource⟩ := dirichlet_product_outsideBand_error hε
  refine ⟨C,hC,?_⟩
  intro P L K hL
  obtain ⟨a,b,hab⟩ := P.active_isInterval
  refine ⟨a,b,hab,?_⟩
  intro E
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hLp : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4*Real.pi*P.N) hL
  have hπ : 0 < 2*Real.pi := by positivity
  have hTp : 0 < P.T := P.T_pos
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrange (t : P.ordinates) : P.T ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using
      P.ordinates_in_interval t t.property
  have hordered (t u : P.ordinates) (hgap : L < (u : ℝ)-t) :
      ‖zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u-
        reflectedOutsideBand P.N t (u-t) a b P.scale (2*P.scale) a b K‖ ≤
        3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2 := by
    have hbounds := P.active_interval_bounds hab (P.active_nonempty_of_mem_ordinates t.property)
    have ht := hrange t
    have hu := hrange u
    have htp : 0 < (t : ℝ) := hTp.trans_le ht.1
    have hh : 0 < (u : ℝ)-t := hLp.trans hgap
    have hht : (u : ℝ)-t ≤ t := by linarith
    have hsc : P.N ≤ (P.scale : ℝ) := P.N_eq_scale.le
    have hsc' : ((2*P.scale : ℕ) : ℝ) ≤ 2*P.N := by rw [P.N_eq_scale]; norm_num
    let E₀ := C*(P.N/Real.sqrt (((u : ℝ)-t)/(2*Real.pi))+
      (((t : ℝ)+((u : ℝ)-t))/(2*Real.pi))^ε)
    have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
    have hEE : E₀ ≤ E := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
      apply add_le_add
      · exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (div_pos hLp hπ))
          (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hgap.le hπ.le))
      · exact Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_right (by linarith) hπ.le) hε.le
    have hb := hsource P.N t (u-t) a b P.scale (2*P.scale) a b K
      P.one_lt_N.le (hL.trans hgap.le) hht hbounds.2.1 hbounds.2.2 hsc hsc'
      hbounds.2.1 hbounds.2.2
    have hident : zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u =
        (∑ n ∈ Finset.Icc a b,dirichletPhase n t)*
          (∑ n ∈ Finset.Icc P.scale (2*P.scale),dirichletPhase n (u-t))*
          conj (∑ n ∈ Finset.Icc a b,dirichletPhase n ((t : ℝ)+(u-t))) := by
      simp only [zetaAnchor,hab,gramKernel,P.indices_eq_dyadicInterval,add_sub_cancel]
      ring
    rw [hident]
    apply hb.trans
    change 3072*P.N^2*(K.card : ℝ)+3*E₀*(2*P.N+E₀)^2 ≤ _
    gcongr
  have hpoint (t u : P.ordinates) :
      ‖zetaAnchor P t*conj (zetaAnchor P u)*farMatrix P.toLargeValuePattern L t u-
        (if L < |(u : ℝ)-t| then anchorOutsideBand P a b K t u else 0)‖ ≤
        3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2 := by
    by_cases hfar : L < |(u : ℝ)-t|
    · simp only [farMatrix,if_pos hfar,anchorOutsideBand]
      by_cases htu : (t : ℝ) ≤ u
      · rw [if_pos htu]
        exact hordered t u (by simpa only [abs_of_nonneg (sub_nonneg.mpr htu)] using hfar)
      · rw [if_neg htu]
        have hgap : L < (t : ℝ)-u := by
          rw [abs_of_neg (by linarith : (u : ℝ)-t < 0)] at hfar
          linarith
        have h := hordered u t hgap
        have hid : zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u =
            conj (zetaAnchor P u*conj (zetaAnchor P t)*gramKernel P.toLargeValuePattern u t) := by
          rw [map_mul,map_mul,starRingEnd_self_apply,gramKernel_conj]
          ring
        rw [hid,← map_sub,norm_conj]
        exact h
    · simp only [farMatrix,if_neg hfar,mul_zero,sub_self,norm_zero]
      positivity
  unfold anchorFar anchorOutsideBandFar
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t : P.ordinates,∑ _u : P.ordinates,
        (3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2) := by
      apply Finset.sum_le_sum
      intro t _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => hpoint t u))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

#print axioms anchorFar_outsideBand_error

private theorem eventually_reflectionError_sqrt (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ T : ℝ, 0 < T → T ≤ N^6 →
      C*(N/Real.sqrt (N^(7/5 : ℝ)/(2*Real.pi))+
        ((2*T)/(2*Real.pi))^(1/100 : ℝ)) ≤ N^(1/2 : ℝ) := by
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (C*(Real.sqrt (2*Real.pi)+1)) (by positivity)
      0 (η := 1/5) (by norm_num))
  refine ⟨max 1 N₁,le_max_left _ _,?_⟩
  intro N hN T hT hTu
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hconst : C*(Real.sqrt (2*Real.pi)+1) ≤ N^(1/5 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ N ((le_max_right _ _).trans hN)
  have hroot : Real.sqrt (N^(7/5 : ℝ)/(2*Real.pi)) =
      N^(7/10 : ℝ)/Real.sqrt (2*Real.pi) := by
    rw [Real.sqrt_div (Real.rpow_nonneg hNp.le _),Real.sqrt_eq_rpow,
      ← Real.rpow_mul hNp.le]
    norm_num
  have hfirst : N/Real.sqrt (N^(7/5 : ℝ)/(2*Real.pi)) =
      Real.sqrt (2*Real.pi)*N^(3/10 : ℝ) := by
    rw [hroot,div_div_eq_mul_div]
    have he : N/N^(7/10 : ℝ) = N^(3/10 : ℝ) := by
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_sub hNp]
      norm_num
    calc
      N*Real.sqrt (2*Real.pi)/N^(7/10 : ℝ) =
          Real.sqrt (2*Real.pi)*(N/N^(7/10 : ℝ)) := by ring
      _ = _ := by rw [he]
  have hbase : (2*T)/(2*Real.pi) ≤ T := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      _ = T/Real.pi := by ring
      _ ≤ T := div_le_self hT.le hpi
  have hsecond : ((2*T)/(2*Real.pi))^(1/100 : ℝ) ≤ N^(3/10 : ℝ) := by
    calc
      _ ≤ (N^6)^(1/100 : ℝ) := Real.rpow_le_rpow (by positivity)
        (hbase.trans hTu) (by norm_num)
      _ = N^(3/50 : ℝ) := by rw [← Real.rpow_natCast,← Real.rpow_mul hNp.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  calc
    _ ≤ C*(Real.sqrt (2*Real.pi)*N^(3/10 : ℝ)+N^(3/10 : ℝ)) := by
      rw [hfirst]
      gcongr
    _ = (C*(Real.sqrt (2*Real.pi)+1))*N^(3/10 : ℝ) := by ring
    _ ≤ N^(1/5 : ℝ)*N^(3/10 : ℝ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

def nearMismatchBand (N : ℝ) : Finset ℤ := Finset.Icc (-⌊Real.sqrt N⌋) ⌊Real.sqrt N⌋

theorem nearMismatchBand_card {N : ℝ} (hN : 1 ≤ N) :
    ((nearMismatchBand N).card : ℝ) ≤ 3*N^(1/2 : ℝ) := by
  have hs : 1 ≤ Real.sqrt N := (Real.one_le_sqrt).mpr hN
  have hfloor := Int.floor_le (Real.sqrt N)
  have hm (k : ℤ) (hk : k ∈ nearMismatchBand N) :
      -Real.sqrt N ≤ (k : ℝ) ∧ (k : ℝ) ≤ Real.sqrt N := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
    have hl' : -((⌊Real.sqrt N⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl
    have hu' : (k : ℝ) ≤ ((⌊Real.sqrt N⌋ : ℤ) : ℝ) := by exact_mod_cast hu
    constructor <;> linarith
  have hc := integer_card_le_interval_length_add_one (nearMismatchBand N)
    (by linarith : -Real.sqrt N ≤ Real.sqrt N) hm
  rw [← Real.sqrt_eq_rpow]
  linarith

#print axioms eventually_reflectionError_sqrt
#print axioms nearMismatchBand_card

/-- All frequencies within sqrt(N) of additive resonance, together with
all three sharp-reflection errors, cost O(R^2 N^(5/2)) in the ACTUAL
signed far correlation. Only the outside-band sum remains. -/
theorem anchorFar_nearBand_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ‖anchorFar P (P.N^(7/5 : ℝ))-
          anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(7/5 : ℝ))‖ ≤
          9243*(P.ordinates.card : ℝ)^2*P.N^(5/2 : ℝ) := by
  obtain ⟨C₀,hC₀,hsource⟩ := anchorFar_outsideBand_error (ε := 1/100) (by norm_num)
  obtain ⟨N₀,hN₀,hsmall⟩ := eventually_reflectionError_sqrt C₀ (zero_le_one.trans hC₀)
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*Real.pi) (by positivity)
      0 (η := 2/5) (by norm_num))
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconst : 4*Real.pi ≤ P.N^(2/5 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N ((le_max_right _ _).trans hPN)
  have hL : 4*Real.pi*P.N ≤ P.N^(7/5 : ℝ) := by
    calc
      _ ≤ P.N^(2/5 : ℝ)*P.N := mul_le_mul_of_nonneg_right hconst hNp.le
      _ = _ := by nth_rw 2 [← Real.rpow_one P.N]; rw [← Real.rpow_add hNp]; norm_num
  obtain ⟨a,b,hab,herror⟩ := hsource P (P.N^(7/5 : ℝ)) (nearMismatchBand P.N) hL
  refine ⟨a,b,hab,?_⟩
  let E := C₀*(P.N/Real.sqrt (P.N^(7/5 : ℝ)/(2*Real.pi))+
    ((2*P.T)/(2*Real.pi))^(1/100 : ℝ))
  have hE0 : 0 ≤ E := by have := P.T_pos; dsimp [E]; positivity
  have hE : E ≤ P.N^(1/2 : ℝ) :=
    hsmall P.N ((le_max_left _ _).trans hPN) P.T P.T_pos hT
  have hhalf : P.N^(1/2 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num : (1/2 : ℝ) ≤ 1)
  have hpower : P.N^2*P.N^(1/2 : ℝ) = P.N^(5/2 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNp]
    norm_num
  have hband : 3072*P.N^2*((nearMismatchBand P.N).card : ℝ) ≤ 9216*P.N^(5/2 : ℝ) := by
    calc
      _ ≤ 3072*P.N^2*(3*P.N^(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (nearMismatchBand_card P.one_lt_N.le) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hreflect : 3*E*(2*P.N+E)^2 ≤ 27*P.N^(5/2 : ℝ) := by
    calc
      _ ≤ 3*P.N^(1/2 : ℝ)*(2*P.N+P.N)^2 := by gcongr; exact hE.trans hhalf
      _ = _ := by rw [← hpower]; ring
  apply herror.trans
  calc
    _ ≤ (P.ordinates.card : ℝ)^2*(9243*P.N^(5/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hband,hreflect]) (sq_nonneg _)
    _ = _ := by ring

#print axioms anchorFar_nearBand_uniform

/-- Uniform endpoint-pattern reduction after ACTUALLY proving and absorbing
the full sqrt(N)-wide resonance band and every reflection error. The signed
outside-band correlation, not a supplied majorant, is the remaining object. -/
theorem endpoint_outsideBand_dichotomy {τ ε : ℝ}
    (hτ : 37/7 ≤ τ) (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 8*P.N*
            (anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(7/5 : ℝ))).re) := by
  obtain ⟨C₀,hC₀,δ₀,hδ₀,hnear⟩ := endpoint_nearRowBudget_uniform hτ hτu hε
  obtain ⟨C₁,_,hband⟩ := anchorFar_nearBand_uniform
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 73944 (by norm_num) 0 (η := 3/10) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),min δ₀ (1/100),
    lt_min hδ₀ (by norm_num),?_⟩
  intro P hPN hTl hTu hVl hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hd₀ := min_le_left δ₀ (1/100 : ℝ)
  have hd₁ := min_le_right δ₀ (1/100 : ℝ)
  have hn := hnear P.toLargeValuePattern ((le_max_left _ _).trans hPN)
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])).trans hTl)
    (hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₀])))
  have hT6 : P.T ≤ P.N^6 := by
    apply hTu.trans
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show τ+min δ₀ (1/100) ≤ (6 : ℕ) by norm_num; linarith only [hτu,hd₁])
  obtain ⟨a,b,hab,herr⟩ := hband P
    ((le_max_left C₁ N₀).trans ((le_max_right _ _).trans hPN)) hT6
  refine ⟨a,b,hab,?_⟩
  have hL := Real.rpow_nonneg hNp.le (7/5 : ℝ)
  have hLN : P.N^(7/5 : ℝ) ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (7/5 : ℝ) ≤ 2)
  have hg := anchor_retained_far P hL hLN
  have hmass : 0 ≤ anchorMass P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn' := mul_le_mul_of_nonneg_right hn hmass
  have hmain : anchorMass P^2 ≤ 2*P.N*
      (P.N^(1+ε)*anchorMass P+(anchorFar P (P.N^(7/5 : ℝ))).re) :=
    hg.trans (mul_le_mul_of_nonneg_left (add_le_add hn' le_rfl) (by positivity))
  have he : P.N*P.N^(1+ε) = P.N^(2+ε) := by
    conv_lhs => lhs; rw [← Real.rpow_one P.N]
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hl := anchorMass_lower P
  by_cases hs : anchorMass P ≤ 4*P.N^(2+ε)
  · exact Or.inl (hl.trans hs)
  · right
    have hs' : 4*P.N^(2+ε) ≤ anchorMass P := (lt_of_not_ge hs).le
    have hm := mul_le_mul_of_nonneg_right hs' hmass
    have hsq := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity) hl 2
    have he' : 2*P.N*(P.N^(1+ε)*anchorMass P+(anchorFar P (P.N^(7/5 : ℝ))).re) =
        2*P.N^(2+ε)*anchorMass P+2*P.N*(anchorFar P (P.N^(7/5 : ℝ))).re := by
      calc
        _ = 2*(P.N*P.N^(1+ε))*anchorMass P+
          2*P.N*(anchorFar P (P.N^(7/5 : ℝ))).re := by ring
        _ = _ := by rw [he]
    rw [he'] at hmain
    have hraw : (P.ordinates.card : ℝ)^2*P.V^4 ≤
        4*P.N*(anchorFar P (P.N^(7/5 : ℝ))).re := by
      nlinarith only [hmain,hm,hsq]
    have hv : P.N^(19/20 : ℝ) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hd₁])).trans hVl
    have hv4 : P.N^(19/5 : ℝ) ≤ P.V^4 := by
      have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (19/20 : ℝ)) hv 4
      rw [← Real.rpow_mul_natCast hNp.le] at h
      norm_num at h
      exact h
    have hconst : 73944 ≤ P.N^(3/10 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N
        ((le_max_right C₁ N₀).trans ((le_max_right _ _).trans hPN))
    have hp : P.N*P.N^(5/2 : ℝ) = P.N^(7/2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      norm_num
    have hscale : 73944*P.N^(7/2 : ℝ) ≤ P.V^4 := by
      calc
        _ ≤ P.N^(3/10 : ℝ)*P.N^(7/2 : ℝ) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
        _ = P.N^(19/5 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := hv4
    have habs : 8*P.N*(9243*(P.ordinates.card : ℝ)^2*P.N^(5/2 : ℝ)) ≤
        (P.ordinates.card : ℝ)^2*P.V^4 := by
      calc
        _ = (P.ordinates.card : ℝ)^2*(73944*P.N^(7/2 : ℝ)) := by rw [← hp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    have hre := (Complex.re_le_norm _).trans herr
    rw [Complex.sub_re] at hre
    have hfar := mul_le_mul_of_nonneg_left hre (show 0 ≤ 8*P.N by positivity)
    nlinarith only [hraw,habs,hfar]

#print axioms endpoint_outsideBand_dichotomy

example : ‖reflectedBand 100 (40000*Real.pi) (40000*Real.pi)
    100 200 100 200 100 200 (Finset.Icc (-4) 4)‖ ≤ 3072*(100 : ℝ)^2*9 := by
  have h := norm_reflectedBand (N := 100) (t := 40000*Real.pi) (h := 40000*Real.pi)
    100 200 100 200 100 200 (Finset.Icc (-4) 4)
    (by norm_num) (by nlinarith [Real.pi_pos]) le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcard : (Finset.Icc (-4 : ℤ) 4).card = 9 := by decide
  simpa only [hcard,Nat.cast_ofNat] using h

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ 4*P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 8*P.N*
            (anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(7/5 : ℝ))).re) :=
  endpoint_outsideBand_dichotomy (by norm_num) (by norm_num) hε

private theorem eventually_refinedNear_scales {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℝ in Filter.atTop,
      4*N*(2+200*Real.sqrt (N^(9/5 : ℝ))) ≤ N^(48/25 : ℝ) ∧
      8*N*(2*N+24*Real.pi*N*(harmonic (Nat.ceil (N^(9/5 : ℝ))) : ℝ)) ≤
        N^(2+η) := by
  filter_upwards [eventually_const_log_pow_le_rpow 808 (by norm_num) 0
      (η := 1/50) (by norm_num),
    eventually_const_log_pow_le_rpow (16+768*Real.pi) (by positivity) 1 hη,
    Filter.eventually_ge_atTop (2 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hconst hsmall hN hlog
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  constructor
  · have hs : Real.sqrt (N^(9/5 : ℝ)) = N^(9/10 : ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hNp.le]
      norm_num
    have hone : 1 ≤ N^(9/10 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have hc : 808 ≤ N^(1/50 : ℝ) := by simpa only [pow_zero,mul_one] using hconst
    rw [hs]
    calc
      _ ≤ 808*(N*N^(9/10 : ℝ)) := by nlinarith
      _ = 808*N^(19/10 : ℝ) := by
        rw [show (19/10 : ℝ)=1+9/10 by norm_num,Real.rpow_add hNp,Real.rpow_one]
      _ ≤ N^(1/50 : ℝ)*N^(19/10 : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  · have hL : 1 ≤ N^(9/5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have hc : (Nat.ceil (N^(9/5 : ℝ)) : ℝ) ≤ 2*N^(9/5 : ℝ) := by
      have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (9/5))
      linarith
    have hc0 : (0 : ℝ) < Nat.ceil (N^(9/5 : ℝ)) :=
      (Real.rpow_pos_of_pos hNp _).trans_le (Nat.le_ceil _)
    have hl := Real.log_le_log hc0 hc
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
      Real.log_rpow hNp] at hl
    have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
    have hh : (harmonic (Nat.ceil (N^(9/5 : ℝ))) : ℝ) ≤ 4*Real.log N := by
      have hb := harmonic_le_one_add_log (Nat.ceil (N^(9/5 : ℝ)))
      linarith
    have hdiag : 8*N*(2*N+24*Real.pi*N*(harmonic (Nat.ceil (N^(9/5 : ℝ))) : ℝ)) ≤
        N^2*((16+768*Real.pi)*Real.log N) := by
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 192*Real.pi*N^2)
      have hn := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 16*N^2)
      nlinarith only [hm,hn]
    calc
      _ ≤ N^2*((16+768*Real.pi)*Real.log N) := hdiag
      _ ≤ N^2*N^η := mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hsmall)
        (sq_nonneg N)
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_add hNp]; norm_num

/-- A larger part of the ACTUAL far correlation is absorbed using the
anchor mass itself. No preliminary R bound is spent on the off-diagonal
near-row term; all gaps up to N^(9/5) are included. -/
theorem anchorFar_refinedGap_dichotomy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(24/25 : ℝ) ≤ P.V →
      (P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
      (P.ordinates.card : ℝ)^2*P.V^4 ≤ 8*P.N*(anchorFar P (P.N^(9/5 : ℝ))).re := by
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (eventually_refinedNear_scales hε)
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨hvalue,hdiag⟩ := hN₀ P.N ((le_max_right _ _).trans hPN)
  have hv2 : P.N^(48/25 : ℝ) ≤ P.V^2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (24/25 : ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at h
    norm_num at h
    exact h
  let F := 2+200*Real.sqrt (P.N^(9/5 : ℝ))
  let D := 2*P.N+24*Real.pi*P.N*(harmonic (Nat.ceil (P.N^(9/5 : ℝ))) : ℝ)
  have hmass : 0 ≤ anchorMass P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl := anchorMass_lower P
  have hsmall : 4*P.N*((P.ordinates.card : ℝ)*F) ≤ anchorMass P := by
    have h := mul_le_mul_of_nonneg_left (hvalue.trans hv2) (Nat.cast_nonneg P.ordinates.card)
    dsimp [F]
    nlinarith only [h,hl]
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hmass
  have hLN : P.N^(9/5 : ℝ) ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (9/5 : ℝ) ≤ 2)
  have hg := anchor_retained_far P (Real.rpow_nonneg hNp.le _) hLN
  have hbudget : nearRowBudget P.toLargeValuePattern (P.N^(9/5 : ℝ)) =
      D+(P.ordinates.card : ℝ)*F := by unfold nearRowBudget D F; ring
  rw [hbudget] at hg
  have hmain : anchorMass P^2 ≤ 4*P.N*D*anchorMass P+
      4*P.N*(anchorFar P (P.N^(9/5 : ℝ))).re := by
    nlinarith only [hg,hsmall']
  by_cases hs : anchorMass P ≤ 8*P.N*D
  · left
    exact hl.trans (hs.trans (by simpa only [D,mul_assoc] using hdiag))
  · right
    have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hs) hmass
    have hsq := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity) hl 2
    nlinarith only [hmain,hm,hsq]

#print axioms eventually_refinedNear_scales
#print axioms anchorFar_refinedGap_dichotomy

/-- The proved reflection/band error is uniform above the original gap
cutoff. This allows the new medium-gap absorption to be combined with the
same actual frequency decomposition, without a fresh analytic premise. -/
theorem anchorFar_nearBand_above_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      ∀ L : ℝ, P.N^(7/5 : ℝ) ≤ L →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ‖anchorFar P L-anchorOutsideBandFar P a b (nearMismatchBand P.N) L‖ ≤
          9243*(P.ordinates.card : ℝ)^2*P.N^(5/2 : ℝ) := by
  obtain ⟨C₀,hC₀,hsource⟩ := anchorFar_outsideBand_error (ε := 1/100) (by norm_num)
  obtain ⟨N₀,hN₀,hsmall⟩ := eventually_reflectionError_sqrt C₀ (zero_le_one.trans hC₀)
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*Real.pi) (by positivity)
      0 (η := 2/5) (by norm_num))
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT L hNL
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconst : 4*Real.pi ≤ P.N^(2/5 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N ((le_max_right _ _).trans hPN)
  have hL : 4*Real.pi*P.N ≤ L := by
    calc
      _ ≤ P.N^(2/5 : ℝ)*P.N := mul_le_mul_of_nonneg_right hconst hNp.le
      _ = P.N^(7/5 : ℝ) := by
        nth_rw 2 [← Real.rpow_one P.N]
        rw [← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := hNL
  obtain ⟨a,b,hab,herror⟩ := hsource P L (nearMismatchBand P.N) hL
  refine ⟨a,b,hab,?_⟩
  let E := C₀*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^(1/100 : ℝ))
  have hLp : 0 < L := (Real.rpow_pos_of_pos hNp (7/5)).trans_le hNL
  have hE0 : 0 ≤ E := by have := P.T_pos; dsimp [E]; positivity
  have hE : E ≤ P.N^(1/2 : ℝ) := by
    apply le_trans _ (hsmall P.N ((le_max_left _ _).trans hPN) P.T P.T_pos hT)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC₀)
    apply add_le_add _ le_rfl
    exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hNL (by positivity)))
  have hhalf : P.N^(1/2 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num : (1/2 : ℝ) ≤ 1)
  have hpower : P.N^2*P.N^(1/2 : ℝ) = P.N^(5/2 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNp]
    norm_num
  have hband : 3072*P.N^2*((nearMismatchBand P.N).card : ℝ) ≤ 9216*P.N^(5/2 : ℝ) := by
    calc
      _ ≤ 3072*P.N^2*(3*P.N^(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (nearMismatchBand_card P.one_lt_N.le) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hreflect : 3*E*(2*P.N+E)^2 ≤ 27*P.N^(5/2 : ℝ) := by
    calc
      _ ≤ 3*P.N^(1/2 : ℝ)*(2*P.N+P.N)^2 := by gcongr; exact hE.trans hhalf
      _ = _ := by rw [← hpower]; ring
  apply herror.trans
  calc
    _ ≤ (P.ordinates.card : ℝ)^2*(9243*P.N^(5/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hband,hreflect]) (sq_nonneg _)
    _ = _ := by ring

/-- A physical actual-pattern consumer with BOTH the enlarged ordinate
gap cutoff and the frequency mismatch band removed by proved estimates. -/
theorem anchorFar_refinedOutsideBand_dichotomy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.T ≤ P.N^6 → P.N^(24/25 : ℝ) ≤ P.V →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
        (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
          (anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(9/5 : ℝ))).re) := by
  obtain ⟨C₀,hC₀,hnear⟩ := anchorFar_refinedGap_dichotomy hε
  obtain ⟨C₁,_,hband⟩ := anchorFar_nearBand_above_uniform
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 147888 (by norm_num) 0 (η := 3/10) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨a,b,hab,herr⟩ := hband P
    ((le_max_left C₁ N₀).trans ((le_max_right _ _).trans hPN)) hT (P.N^(9/5 : ℝ))
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num))
  refine ⟨a,b,hab,?_⟩
  rcases hnear P ((le_max_left _ _).trans hPN) hV with hn | hn
  · exact Or.inl hn
  · right
    have hv : P.N^(19/20 : ℝ) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hV
    have hv4 : P.N^(19/5 : ℝ) ≤ P.V^4 := by
      have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (19/20 : ℝ)) hv 4
      rw [← Real.rpow_mul_natCast hNp.le] at h
      norm_num at h
      exact h
    have hconst : 147888 ≤ P.N^(3/10 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N
        ((le_max_right C₁ N₀).trans ((le_max_right _ _).trans hPN))
    have hp : P.N*P.N^(5/2 : ℝ) = P.N^(7/2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      norm_num
    have hscale : 147888*P.N^(7/2 : ℝ) ≤ P.V^4 := by
      calc
        _ ≤ P.N^(3/10 : ℝ)*P.N^(7/2 : ℝ) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
        _ = P.N^(19/5 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := hv4
    have habs : 16*P.N*(9243*(P.ordinates.card : ℝ)^2*P.N^(5/2 : ℝ)) ≤
        (P.ordinates.card : ℝ)^2*P.V^4 := by
      calc
        _ = (P.ordinates.card : ℝ)^2*(147888*P.N^(7/2 : ℝ)) := by rw [← hp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    have hre := (Complex.re_le_norm _).trans herr
    rw [Complex.sub_re] at hre
    have hfar := mul_le_mul_of_nonneg_left hre (show 0 ≤ 16*P.N by positivity)
    nlinarith only [hn,habs,hfar]

#print axioms anchorFar_nearBand_above_uniform
#print axioms anchorFar_refinedOutsideBand_dichotomy

/-- The enlarged-gap reduction has the original two-sided endpoint
neighbourhood quantifiers. It in fact needs no lower bound on tau. -/
theorem endpoint_refinedOutsideBand_dichotomy {τ ε : ℝ}
    (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
            (anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(9/5 : ℝ))).re) := by
  obtain ⟨C,hC,hsource⟩ := anchorFar_refinedOutsideBand_dichotomy hε
  refine ⟨C,hC,1/100,by norm_num,?_⟩
  intro P hPN _hTl hTu hVl _hVu
  apply hsource P hPN
  · apply hTu.trans
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show τ+1/100 ≤ (6 : ℕ) by norm_num; linarith only [hτu])
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl

#print axioms endpoint_refinedOutsideBand_dichotomy

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
            (anchorOutsideBandFar P a b (nearMismatchBand P.N) (P.N^(9/5 : ℝ))).re) :=
  endpoint_refinedOutsideBand_dichotomy (by norm_num) hε

/-- Restriction retains the exact active interval, phases and height scale. -/
def restrictOrdinates (P : ZetaLargeValuePattern) (S : Finset ℝ)
    (hS : S ⊆ P.ordinates) : ZetaLargeValuePattern :=
  { P with
    ordinates := S
    ordinates_in_interval := fun t ht => P.ordinates_in_interval t (hS ht)
    ordinates_oneSeparated := fun t ht u hu htu =>
      P.ordinates_oneSeparated t (hS ht) u (hS hu) htu
    large := fun t ht => P.large t (hS ht) }

/-- The actual far matrix vanishes on an ordinate set of diameter at most
the cutoff; the large-value pattern is not replaced by an abstract count. -/
theorem anchorFar_eq_zero_of_diameter (P : ZetaLargeValuePattern) (L : ℝ)
    (hdiam : ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates, |u-t| ≤ L) :
    anchorFar P L = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro u _
  simp only [farMatrix,if_neg (not_lt_of_ge (hdiam t t.property u u.property)),mul_zero]

/-- An unconditional local nonconcentration estimate for the ACTUAL
large-value ordinates. It follows from the enlarged-gap Gram argument,
not from a supplied local-density hypothesis. -/
theorem ordinate_local_mass_refined {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(24/25 : ℝ) ≤ P.V → ∀ x : ℝ,
      ((P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(9/5 : ℝ))).card : ℝ)*P.V^2 ≤
        P.N^(2+ε) := by
  classical
  obtain ⟨C,hC,hsource⟩ := anchorFar_refinedGap_dichotomy hε
  refine ⟨C,hC,?_⟩
  intro P hPN hV x
  let S := P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(9/5 : ℝ))
  let Q := restrictOrdinates P S (Finset.filter_subset _ _)
  have hzero : anchorFar Q (Q.N^(9/5 : ℝ)) = 0 := by
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

#print axioms anchorFar_eq_zero_of_diameter
#print axioms ordinate_local_mass_refined

def wideMismatchBand (N : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊N^(9/10 : ℝ)⌋) ⌊N^(9/10 : ℝ)⌋

theorem wideMismatchBand_card {N : ℝ} (hN : 1 ≤ N) :
    ((wideMismatchBand N).card : ℝ) ≤ 3*N^(9/10 : ℝ) := by
  have hs : 1 ≤ N^(9/10 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hfloor := Int.floor_le (N^(9/10 : ℝ))
  have hm (k : ℤ) (hk : k ∈ wideMismatchBand N) :
      -N^(9/10 : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ N^(9/10 : ℝ) := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
    have hl' : -((⌊N^(9/10 : ℝ)⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl
    have hu' : (k : ℝ) ≤ ((⌊N^(9/10 : ℝ)⌋ : ℤ) : ℝ) := by exact_mod_cast hu
    constructor <;> linarith
  have hc := integer_card_le_interval_length_add_one (wideMismatchBand N)
    (by linarith : -N^(9/10 : ℝ) ≤ N^(9/10 : ℝ)) hm
  linarith

/-- Removal of a substantially wider portion of the actual far sum.
The estimate includes every sharp-reflection error and moving cutoff. -/
theorem anchorFar_wideBand_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      ∀ L : ℝ, P.N^(7/5 : ℝ) ≤ L →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ‖anchorFar P L-anchorOutsideBandFar P a b (wideMismatchBand P.N) L‖ ≤
          9243*(P.ordinates.card : ℝ)^2*P.N^(29/10 : ℝ) := by
  obtain ⟨C₀,hC₀,hsource⟩ := anchorFar_outsideBand_error (ε := 1/100) (by norm_num)
  obtain ⟨N₀,hN₀,hsmall⟩ := eventually_reflectionError_sqrt C₀ (zero_le_one.trans hC₀)
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*Real.pi) (by positivity)
      0 (η := 2/5) (by norm_num))
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT L hNL
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconst : 4*Real.pi ≤ P.N^(2/5 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N ((le_max_right _ _).trans hPN)
  have hL : 4*Real.pi*P.N ≤ L := by
    calc
      _ ≤ P.N^(2/5 : ℝ)*P.N := mul_le_mul_of_nonneg_right hconst hNp.le
      _ = P.N^(7/5 : ℝ) := by
        nth_rw 2 [← Real.rpow_one P.N]
        rw [← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := hNL
  obtain ⟨a,b,hab,herror⟩ := hsource P L (wideMismatchBand P.N) hL
  refine ⟨a,b,hab,?_⟩
  let E := C₀*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^(1/100 : ℝ))
  have hLp : 0 < L := (Real.rpow_pos_of_pos hNp (7/5)).trans_le hNL
  have hE0 : 0 ≤ E := by have := P.T_pos; dsimp [E]; positivity
  have hE : E ≤ P.N^(1/2 : ℝ) := by
    apply le_trans _ (hsmall P.N ((le_max_left _ _).trans hPN) P.T P.T_pos hT)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC₀)
    apply add_le_add _ le_rfl
    exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hNL (by positivity)))
  have hhalf : P.N^(1/2 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num : (1/2 : ℝ) ≤ 1)
  have hpower : P.N^2*P.N^(9/10 : ℝ) = P.N^(29/10 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNp]
    norm_num
  have hband : 3072*P.N^2*((wideMismatchBand P.N).card : ℝ) ≤ 9216*P.N^(29/10 : ℝ) := by
    calc
      _ ≤ 3072*P.N^2*(3*P.N^(9/10 : ℝ)) :=
        mul_le_mul_of_nonneg_left (wideMismatchBand_card P.one_lt_N.le) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hreflect : 3*E*(2*P.N+E)^2 ≤ 27*P.N^(29/10 : ℝ) := by
    calc
      _ ≤ 3*P.N^(1/2 : ℝ)*(2*P.N+P.N)^2 := by gcongr; exact hE.trans hhalf
      _ = 27*P.N^2*P.N^(1/2 : ℝ) := by ring
      _ ≤ 27*P.N^2*P.N^(9/10 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)) (by positivity)
      _ = _ := by rw [← hpower]; ring
  apply herror.trans
  calc
    _ ≤ (P.ordinates.card : ℝ)^2*(9243*P.N^(29/10 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hband,hreflect]) (sq_nonneg _)
    _ = _ := by ring

/-- The wider N^(9/10) frequency band is absorbed at the FROZEN endpoint,
with the full two-sided parameter neighbourhoods and the enlarged actual
ordinate-gap cutoff. The signed complement is retained, never assumed small. -/
theorem endpoint_wideOutsideBand_dichotomy {τ ε : ℝ}
    (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
            (anchorOutsideBandFar P a b (wideMismatchBand P.N) (P.N^(9/5 : ℝ))).re) := by
  obtain ⟨C₀,hC₀,hnear⟩ := anchorFar_refinedGap_dichotomy hε
  obtain ⟨C₁,_,hband⟩ := anchorFar_wideBand_uniform
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 147888 (by norm_num) 0 (η := 1/420) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),1/2000,by norm_num,?_⟩
  intro P hPN _hTl hTu hVl _hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT : P.T ≤ P.N^6 := hTu.trans (by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show τ+1/2000 ≤ (6 : ℕ) by norm_num; linarith only [hτu]))
  have hV : P.N^(24/25 : ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl
  obtain ⟨a,b,hab,herr⟩ := hband P
    ((le_max_left C₁ N₀).trans ((le_max_right _ _).trans hPN)) hT (P.N^(9/5 : ℝ))
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num))
  refine ⟨a,b,hab,?_⟩
  rcases hnear P ((le_max_left _ _).trans hPN) hV with hn | hn
  · exact Or.inl hn
  · right
    have hv : P.N^(1639/1680 : ℝ) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl
    have hv4 : P.N^(1639/420 : ℝ) ≤ P.V^4 := by
      have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1639/1680 : ℝ)) hv 4
      rw [← Real.rpow_mul_natCast hNp.le] at h
      norm_num at h
      exact h
    have hconst : 147888 ≤ P.N^(1/420 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N
        ((le_max_right C₁ N₀).trans ((le_max_right _ _).trans hPN))
    have hp : P.N*P.N^(29/10 : ℝ) = P.N^(39/10 : ℝ) := by
      nth_rw 1 [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      norm_num
    have hscale : 147888*P.N^(39/10 : ℝ) ≤ P.V^4 := by
      calc
        _ ≤ P.N^(1/420 : ℝ)*P.N^(39/10 : ℝ) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
        _ = P.N^(1639/420 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := hv4
    have habs : 16*P.N*(9243*(P.ordinates.card : ℝ)^2*P.N^(29/10 : ℝ)) ≤
        (P.ordinates.card : ℝ)^2*P.V^4 := by
      calc
        _ = (P.ordinates.card : ℝ)^2*(147888*P.N^(39/10 : ℝ)) := by rw [← hp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    have hre := (Complex.re_le_norm _).trans herr
    rw [Complex.sub_re] at hre
    have hfar := mul_le_mul_of_nonneg_left hre (show 0 ≤ 16*P.N by positivity)
    nlinarith only [hn,habs,hfar]

#print axioms wideMismatchBand_card
#print axioms anchorFar_wideBand_uniform
#print axioms endpoint_wideOutsideBand_dichotomy

/-- The analytic pair bounds an ACTUAL truncated Gram row at every
positive cutoff. Recentring is performed on the real pattern itself. -/
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

/-- Pair-driven truncation of the anchored Gram form. The pair theorem,
the real near matrix and its row estimate are all consumed in this proof. -/
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

#print axioms exponentPair_nearMatrix_local_row
#print axioms exponentPair_nearMatrix_row
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

/-- The installed analytic (3/40,31/40) pair removes ALL gaps through
N^(10/3) from the actual anchored correlation. No row or endpoint
estimate is left as a theorem hypothesis. -/
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

#print axioms eventually_pairNear_scales
#print axioms anchorFar_pairGap_dichotomy

/-- Local nonconcentration at the enlarged, pair-driven length. -/
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

/-- Combined actual removal of gaps up to N^(10/3), the entire
N^(9/10)-wide additive mismatch band, and all reflection errors. -/
theorem endpoint_pairWideOutsideBand_dichotomy {τ ε : ℝ}
    (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
            (anchorOutsideBandFar P a b (wideMismatchBand P.N) (P.N^(10/3 : ℝ))).re) := by
  obtain ⟨C₀,hC₀,hnear⟩ := anchorFar_pairGap_dichotomy hε
  obtain ⟨C₁,_,hband⟩ := anchorFar_wideBand_uniform
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 147888 (by norm_num) 0 (η := 1/420) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),1/2000,by norm_num,?_⟩
  intro P hPN _hTl hTu hVl _hVu
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT : P.T ≤ P.N^6 := hTu.trans (by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show τ+1/2000 ≤ (6 : ℕ) by norm_num; linarith only [hτu]))
  have hV : P.N^(1951/2000 : ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl
  obtain ⟨a,b,hab,herr⟩ := hband P
    ((le_max_left C₁ N₀).trans ((le_max_right _ _).trans hPN)) hT (P.N^(10/3 : ℝ))
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num))
  refine ⟨a,b,hab,?_⟩
  rcases hnear P ((le_max_left _ _).trans hPN) hV with hn | hn
  · exact Or.inl hn
  · right
    have hv : P.N^(1639/1680 : ℝ) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl
    have hv4 : P.N^(1639/420 : ℝ) ≤ P.V^4 := by
      have h := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1639/1680 : ℝ)) hv 4
      rw [← Real.rpow_mul_natCast hNp.le] at h
      norm_num at h
      exact h
    have hconst : 147888 ≤ P.N^(1/420 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N
        ((le_max_right C₁ N₀).trans ((le_max_right _ _).trans hPN))
    have hp : P.N*P.N^(29/10 : ℝ) = P.N^(39/10 : ℝ) := by
      nth_rw 1 [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      norm_num
    have hscale : 147888*P.N^(39/10 : ℝ) ≤ P.V^4 := by
      calc
        _ ≤ P.N^(1/420 : ℝ)*P.N^(39/10 : ℝ) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
        _ = P.N^(1639/420 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := hv4
    have habs : 16*P.N*(9243*(P.ordinates.card : ℝ)^2*P.N^(29/10 : ℝ)) ≤
        (P.ordinates.card : ℝ)^2*P.V^4 := by
      calc
        _ = (P.ordinates.card : ℝ)^2*(147888*P.N^(39/10 : ℝ)) := by rw [← hp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    have hre := (Complex.re_le_norm _).trans herr
    rw [Complex.sub_re] at hre
    have hfar := mul_le_mul_of_nonneg_left hre (show 0 ≤ 16*P.N by positivity)
    nlinarith only [hn,habs,hfar]

#print axioms ordinate_local_mass_pair
#print axioms endpoint_pairWideOutsideBand_dichotomy

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∃ a b : ℕ, P.active = Finset.Icc a b ∧
          ((P.ordinates.card : ℝ)*P.V^2 ≤ P.N^(2+ε) ∨
          (P.ordinates.card : ℝ)^2*P.V^4 ≤ 16*P.N*
            (anchorOutsideBandFar P a b (wideMismatchBand P.N) (P.N^(10/3 : ℝ))).re) :=
  endpoint_pairWideOutsideBand_dichotomy (by norm_num) hε

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V → ∀ x : ℝ,
      ((P.ordinates.filter (fun t => x ≤ t ∧ t ≤ x+P.N^(10/3 : ℝ))).card : ℝ)*P.V^2 ≤
        P.N^(2+ε) := ordinate_local_mass_pair hε

/-- A uniform bound for the actual coefficient-one interval throughout the
physical height range needed by all three factors in a far correlation. -/
theorem dirichletInterval_sixthRange_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t : ℝ), C ≤ N → N ≤ t → t ≤ N^6 →
      ∀ a b : ℕ, N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖∑ n ∈ Finset.Icc a b, dirichletPhase n t‖ ≤ N^(981/1000 : ℝ) := by
  have hpair : ExponentPair (1/162) (359/378) := by
    convert exponentPair_heathBrown (by norm_num : 3 ≤ (7 : ℕ)) using 1 <;> norm_num
  obtain ⟨C₀,hC₀,hsource⟩ := hpair.logarithmic_sum_bound (ε := 1/100000) (by norm_num)
  let β : ℝ := 359/378+5/162+6/100000
  have hβ : 0 ≤ β := by norm_num [β]
  have hmargin : 0 < 981/1000-β := by norm_num [β]
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (C₀*(1+2*Real.pi)) (by positivity)
      0 hmargin)
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N t hNC hNt ht a b ha hb
  have hN : 1 ≤ N := (le_max_left _ _).trans hNC
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have htp : 0 < t := hNp.trans_le hNt
  have hbound := hsource t N a b htp hN ha hb
  have hratio : t/N ≤ N^5 := by
    apply (div_le_iff₀ hNp).mpr
    convert ht using 1
  have hpower : (t/N)^(1/162+1/100000 : ℝ)*N^(359/378+1/100000 : ℝ) ≤ N^β := by
    calc
      _ ≤ (N^5)^(1/162+1/100000 : ℝ)*N^(359/378+1/100000 : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hratio (by norm_num))
          (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        congr 1
        dsimp [β]
        ring
  have hlow : 2*Real.pi*N/t ≤ 2*Real.pi := by
    apply (div_le_iff₀ htp).mpr
    exact mul_le_mul_of_nonneg_left hNt (by positivity)
  have hone : 1 ≤ N^β := Real.one_le_rpow hN hβ
  have hconst : C₀*(1+2*Real.pi) ≤ N^(981/1000-β) := by
    simpa only [pow_zero,mul_one] using hN₀ N ((le_max_right _ _).trans hNC)
  have he : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      ∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I)) := by
    simp only [dirichletPhase,mul_comm Complex.I]
    rfl
  rw [he]
  calc
    _ ≤ C₀*((t/N)^(1/162+1/100000 : ℝ)*N^(359/378+1/100000 : ℝ)+2*Real.pi*N/t) := hbound
    _ ≤ C₀*(N^β+2*Real.pi*N^β) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC₀)
      exact add_le_add hpower (hlow.trans (by nlinarith [Real.pi_pos]))
    _ = (C₀*(1+2*Real.pi))*N^β := by ring
    _ ≤ N^(981/1000-β)*N^β := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

/-- A literal slice of the actual anchored far correlation, with its signs
unchanged. The strict cutoff ensures this is a part of anchorFar, not a
new surrogate correlation. -/
def anchorDifferenceSlab (P : ZetaLargeValuePattern) (H : ℝ) : ℂ :=
  ∑ t ∈ P.ordinates,
    ∑ u ∈ P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
      P.N^(10/3 : ℝ) < u-t),
      zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u

/-- An actual upper bound on each surviving difference interval, not a
conditional endpoint wrapper. The local count and every pointwise factor
bound are proved from the real pattern and installed analytic pairs. -/
theorem anchorDifferenceSlab_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ≤ P.T → 2*P.T ≤ P.N^6 → P.N^(1951/2000 : ℝ) ≤ P.V →
      ∀ H : ℝ,
      ‖anchorDifferenceSlab P H‖ ≤ (P.ordinates.card : ℝ)*P.N^(2993/1000 : ℝ) := by
  classical
  obtain ⟨C₀,hC₀,hsource⟩ := dirichletInterval_sixthRange_bound
  obtain ⟨C₁,_,hlocal⟩ := ordinate_local_mass_pair (ε := 1/1000) (by norm_num)
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hNT hT hV H
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hscale : P.N ≤ P.N^(10/3 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (1 : ℝ) ≤ 10/3)
  have hpoint := hsource P.N
  have hrange (t : ℝ) (ht : t ∈ P.ordinates) : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hanchor (t : ℝ) (ht : t ∈ P.ordinates) : ‖zetaAnchor P t‖ ≤ P.N^(981/1000 : ℝ) := by
    obtain ⟨a,b,hab⟩ := P.active_isInterval
    have habounds := P.active_interval_bounds hab (P.active_nonempty_of_mem_ordinates ht)
    rw [zetaAnchor,hab]
    exact hpoint t ((le_max_left _ _).trans hPN) (hNT.trans (hrange t ht).1)
      ((hrange t ht).2.trans hT) a b habounds.2.1 habounds.2.2
  have hkernel (t u : ℝ) (ht : t ∈ P.ordinates) (hu : u ∈ P.ordinates)
      (hgap : P.N^(10/3 : ℝ) < u-t) :
      ‖gramKernel P.toLargeValuePattern t u‖ ≤ P.N^(981/1000 : ℝ) := by
    have huT := hrange u hu
    have htT := hrange t ht
    have hgT : u-t ≤ P.N^6 := by linarith [P.T_pos]
    unfold gramKernel
    rw [P.indices_eq_dyadicInterval]
    exact hpoint (u-t) ((le_max_left _ _).trans hPN) (hscale.trans hgap.le) hgT
      P.scale (2*P.scale) P.N_eq_scale.le (by rw [P.N_eq_scale]; norm_num)
  have hrow (t : ℝ) (ht : t ∈ P.ordinates) :
      ‖∑ u ∈ P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
        P.N^(10/3 : ℝ) < u-t),
        zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u‖ ≤
        P.N^(2993/1000 : ℝ) := by
    let S := P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
      P.N^(10/3 : ℝ) < u-t)
    let B := P.ordinates.filter (fun u => t+H ≤ u ∧ u ≤ (t+H)+P.N^(10/3 : ℝ))
    have hSB : S ⊆ B := by
      intro u hu
      obtain ⟨hu,hlo,hhi,_⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu,by constructor <;> linarith⟩
    have hcount := hlocal P ((le_max_right _ _).trans hPN) hV (t+H)
    have hv2 : P.N^(1951/1000 : ℝ) ≤ P.V^2 := by
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 2
      rw [← Real.rpow_mul_natCast hNp.le] at hh
      norm_num at hh
      exact hh
    have hB : (B.card : ℝ) ≤ P.N^(1/20 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hv2 (Nat.cast_nonneg B.card)
      have he : P.N^(1/20 : ℝ)*P.N^(1951/1000 : ℝ) = P.N^(2+1/1000 : ℝ) := by
        rw [← Real.rpow_add hNp]
        norm_num
      have hp := Real.rpow_pos_of_pos hNp (1951/1000 : ℝ)
      change (B.card : ℝ)*P.V^2 ≤ _ at hcount
      rw [← he] at hcount
      exact (mul_le_mul_iff_left₀ hp).mp (hh.trans hcount)
    have hS : (S.card : ℝ) ≤ P.N^(1/20 : ℝ) :=
      (show (S.card : ℝ) ≤ B.card by exact_mod_cast Finset.card_le_card hSB).trans hB
    have hterm (u : ℝ) (hu : u ∈ S) :
        ‖zetaAnchor P t*conj (zetaAnchor P u)*gramKernel P.toLargeValuePattern t u‖ ≤
          P.N^(2943/1000 : ℝ) := by
      have hui := (Finset.mem_filter.mp hu).1
      have hgap := (Finset.mem_filter.mp hu).2.2.2
      rw [norm_mul,norm_mul,norm_conj]
      calc
        _ ≤ P.N^(981/1000 : ℝ)*P.N^(981/1000 : ℝ)*P.N^(981/1000 : ℝ) :=
          mul_le_mul (mul_le_mul (hanchor t ht) (hanchor u hui) (norm_nonneg _)
            (Real.rpow_nonneg hNp.le _)) (hkernel t u ht hui hgap) (norm_nonneg _)
              (by positivity)
        _ = _ := by rw [← Real.rpow_add hNp,← Real.rpow_add hNp]; norm_num
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _u ∈ S, P.N^(2943/1000 : ℝ) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ)*P.N^(2943/1000 : ℝ) := by simp
      _ ≤ P.N^(1/20 : ℝ)*P.N^(2943/1000 : ℝ) :=
        mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  unfold anchorDifferenceSlab
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ P.ordinates, P.N^(2993/1000 : ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp

#print axioms dirichletInterval_sixthRange_bound
#print axioms anchorDifferenceSlab_bound

/-- Exact source-entry identity: the slab is the corresponding restriction
of the original signed far sum, including its literal strict cutoff. -/
theorem anchorDifferenceSlab_eq_far_restriction (P : ZetaLargeValuePattern)
    {H : ℝ} (hH : 0 ≤ H) :
    anchorDifferenceSlab P H =
      ∑ t : P.ordinates, ∑ u : P.ordinates,
        if H ≤ (u : ℝ)-t ∧ (u : ℝ)-t ≤ H+P.N^(10/3 : ℝ) then
          zetaAnchor P t*conj (zetaAnchor P u)*farMatrix P.toLargeValuePattern
            (P.N^(10/3 : ℝ)) t u else 0 := by
  classical
  unfold anchorDifferenceSlab
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro u _
  simp only [farMatrix]
  by_cases h₁ : H ≤ (u : ℝ)-t
  · by_cases h₂ : (u : ℝ)-t ≤ H+P.N^(10/3 : ℝ)
    · rw [abs_of_nonneg (hH.trans h₁)]
      simp only [h₁,h₂,true_and,and_self,ite_true]
      split_ifs <;> simp only [mul_zero]
    · simp only [h₂,and_false,false_and,ite_false]
  · simp only [h₁,false_and,ite_false]

#print axioms anchorDifferenceSlab_eq_far_restriction

/-- The new actual slab estimate enters the original endpoint strip with
all physical-height and value hypotheses derived, not left as inputs. -/
theorem endpoint_differenceSlab_uniform {τ : ℝ}
    (hτl : 37/7 ≤ τ) (hτu : τ < 340/63) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        ∀ H : ℝ, ‖anchorDifferenceSlab P H‖ ≤
          (P.ordinates.card : ℝ)*P.N^(2993/1000 : ℝ) := by
  obtain ⟨C,_,hsource⟩ := anchorDifferenceSlab_bound
  refine ⟨max 4 C,(by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _),1/2000,by norm_num,?_⟩
  intro P hPN hTl hTu hVl _hVu
  apply hsource P ((le_max_right _ _).trans hPN)
  · apply le_trans _ hTl
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show (1 : ℝ) ≤ τ-1/2000 by linarith only [hτl])
  · have hN4 : 4 ≤ P.N := (le_max_left _ _).trans hPN
    have h2 : (2 : ℝ) ≤ P.N^(1/2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have hh := Real.sqrt_le_sqrt hN4
      norm_num at hh
      exact hh
    have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
    calc
      _ ≤ P.N^(1/2 : ℝ)*P.N^(τ+1/2000) :=
        mul_le_mul h2 hTu P.T_pos.le (Real.rpow_nonneg hNp.le _)
      _ = P.N^(1/2+(τ+1/2000)) := (Real.rpow_add hNp _ _).symm
      _ ≤ P.N^6 := by
        simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
          (show (1/2 : ℝ)+(τ+1/2000) ≤ (6 : ℕ) by norm_num; linarith only [hτu])
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl

#print axioms endpoint_differenceSlab_uniform

example : ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
      P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
      ∀ H : ℝ, ‖anchorDifferenceSlab P H‖ ≤
        (P.ordinates.card : ℝ)*P.N^(2993/1000 : ℝ) :=
  endpoint_differenceSlab_uniform (by norm_num) (by norm_num)

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

/-- Direct pointwise control of the actual reflected complement. All
three original sums and all three reflection errors are bounded here. -/
theorem reflectedOutsideBand_pattern_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ≤ P.T → 2*P.T ≤ P.N^6 →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
      ∀ t ∈ P.ordinates, ∀ u ∈ P.ordinates, P.N^(10/3 : ℝ) < u-t →
        ‖reflectedOutsideBand P.N t (u-t) a b P.scale (2*P.scale) a b (wideMismatchBand P.N)‖ ≤
          2*P.N^(2943/1000 : ℝ) := by
  obtain ⟨C₀,hC₀,hsource⟩ := dirichlet_product_outsideBand_error (ε := 1/100) (by norm_num)
  obtain ⟨N₀,hN₀,hsmall⟩ := eventually_reflectionError_sqrt C₀ (zero_le_one.trans hC₀)
  obtain ⟨C₁,_,hsums⟩ := dirichletInterval_sixthRange_bound
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*Real.pi) (by positivity) 0 (η := 2/5) (by norm_num))
  obtain ⟨N₂,hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 9243 (by norm_num) 0 (η := 43/1000) (by norm_num))
  refine ⟨max N₀ (max C₁ (max N₁ N₂)),hN₀.trans (le_max_left _ _),?_⟩
  intro P hPN hNT hT
  obtain ⟨a,b,hab⟩ := P.active_isInterval
  refine ⟨a,b,hab,?_⟩
  intro t ht u hu hgap
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have htT : P.T ≤ t ∧ t ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have huT : P.T ≤ u ∧ u ≤ 2*P.T := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval u hu
  have htp : 0 < t := hTp.trans_le htT.1
  have hup : 0 < u := hTp.trans_le huT.1
  have hgp : 0 < u-t := (Real.rpow_pos_of_pos hNp _).trans hgap
  have hgupper : u-t ≤ t := by linarith only [htT.1,huT.2]
  have hshort : P.N^(7/5 : ℝ) ≤ u-t :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hgap.le
  have hpiN : 4*Real.pi*P.N ≤ u-t := by
    have hc : 4*Real.pi ≤ P.N^(2/5 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₁ P.N
        ((le_max_left N₁ N₂).trans ((le_max_right C₁ _).trans ((le_max_right _ _).trans hPN)))
    calc
      _ ≤ P.N^(2/5 : ℝ)*P.N := mul_le_mul_of_nonneg_right hc hNp.le
      _ = P.N^(7/5 : ℝ) := by
        nth_rw 2 [← Real.rpow_one P.N]
        rw [← Real.rpow_add hNp]
        norm_num
      _ ≤ _ := hshort
  have hb := P.active_interval_bounds hab (P.active_nonempty_of_mem_ordinates ht)
  have hsc : ((2*P.scale : ℕ) : ℝ) ≤ 2*P.N := by rw [P.N_eq_scale]; norm_num
  have herr := hsource P.N t (u-t) a b P.scale (2*P.scale) a b (wideMismatchBand P.N)
    P.one_lt_N.le hpiN hgupper hb.2.1 hb.2.2 P.N_eq_scale.le hsc hb.2.1 hb.2.2
  have htu : t+(u-t) = u := by ring
  rw [htu] at herr
  let E := C₀*(P.N/Real.sqrt ((u-t)/(2*Real.pi))+(u/(2*Real.pi))^(1/100 : ℝ))
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE : E ≤ P.N^(1/2 : ℝ) := by
    apply le_trans _ (hsmall P.N ((le_max_left _ _).trans hPN) P.T hTp (by linarith))
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC₀)
    apply add_le_add
    · exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hshort (by positivity)))
    · exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right huT.2 (by positivity)) (by norm_num)
  have hhalf : P.N^(1/2 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by norm_num : (1/2 : ℝ) ≤ 1)
  have hpower : P.N^2*P.N^(9/10 : ℝ) = P.N^(29/10 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNp]
    norm_num
  have hband : 3072*P.N^2*((wideMismatchBand P.N).card : ℝ) ≤ 9216*P.N^(29/10 : ℝ) := by
    calc
      _ ≤ 3072*P.N^2*(3*P.N^(9/10 : ℝ)) :=
        mul_le_mul_of_nonneg_left (wideMismatchBand_card P.one_lt_N.le) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hreflect : 3*E*(2*P.N+E)^2 ≤ 27*P.N^(29/10 : ℝ) := by
    calc
      _ ≤ 3*P.N^(1/2 : ℝ)*(2*P.N+P.N)^2 := by gcongr; exact hE.trans hhalf
      _ = 27*P.N^2*P.N^(1/2 : ℝ) := by ring
      _ ≤ 27*P.N^2*P.N^(9/10 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hconst : 9243 ≤ P.N^(43/1000 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₂ P.N
      ((le_max_right N₁ N₂).trans ((le_max_right C₁ _).trans ((le_max_right _ _).trans hPN)))
  have herror : 3072*P.N^2*((wideMismatchBand P.N).card : ℝ)+3*E*(2*P.N+E)^2 ≤
      P.N^(2943/1000 : ℝ) := by
    calc
      _ ≤ 9243*P.N^(29/10 : ℝ) := by linarith only [hband,hreflect]
      _ ≤ P.N^(43/1000 : ℝ)*P.N^(29/10 : ℝ) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hNC : C₁ ≤ P.N := (le_max_left C₁ _).trans ((le_max_right _ _).trans hPN)
  have hAt := hsums P.N t hNC (hNT.trans htT.1) (htT.2.trans hT) a b hb.2.1 hb.2.2
  have hAu := hsums P.N u hNC (hNT.trans huT.1) (huT.2.trans hT) a b hb.2.1 hb.2.2
  have hNg : P.N ≤ u-t := by
    apply le_trans _ hshort
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by norm_num : (1 : ℝ) ≤ 7/5)
  have hAg := hsums P.N (u-t) hNC hNg (by linarith) P.scale (2*P.scale) P.N_eq_scale.le hsc
  let A := (∑ n ∈ Finset.Icc a b,dirichletPhase n t)*
    (∑ n ∈ Finset.Icc P.scale (2*P.scale),dirichletPhase n (u-t))*
    conj (∑ n ∈ Finset.Icc a b,dirichletPhase n u)
  have hA : ‖A‖ ≤ P.N^(2943/1000 : ℝ) := by
    dsimp [A]
    rw [norm_mul,norm_mul,norm_conj]
    calc
      _ ≤ P.N^(981/1000 : ℝ)*P.N^(981/1000 : ℝ)*P.N^(981/1000 : ℝ) :=
        mul_le_mul (mul_le_mul hAt hAg (norm_nonneg _) (Real.rpow_nonneg hNp.le _))
          hAu (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp,← Real.rpow_add hNp]; norm_num
  let D := reflectedOutsideBand P.N t (u-t) a b P.scale (2*P.scale) a b (wideMismatchBand P.N)
  have hd : ‖A-D‖ ≤ P.N^(2943/1000 : ℝ) := herr.trans herror
  have htri : ‖D‖ ≤ ‖A-D‖+‖A‖ := by
    calc
      _ = ‖(D-A)+A‖ := by rw [sub_add_cancel]
      _ ≤ ‖D-A‖+‖A‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  change ‖D‖ ≤ _
  linarith only [hd,hA,htri]

#print axioms ordinate_local_count_pair
#print axioms reflectedOutsideBand_pattern_bound

def anchorOutsideDifferenceSlab (P : ZetaLargeValuePattern) (a b : ℕ) (H : ℝ) : ℂ :=
  ∑ t ∈ P.ordinates,
    ∑ u ∈ P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
      P.N^(10/3 : ℝ) < u-t),
      anchorOutsideBand P a b (wideMismatchBand P.N) t u

/-- The per-difference-interval bound on the very reflected complement
retained by endpoint_pairWideOutsideBand_dichotomy. -/
theorem anchorOutsideDifferenceSlab_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ≤ P.T → 2*P.T ≤ P.N^6 → P.N^(1951/2000 : ℝ) ≤ P.V →
      ∃ a b : ℕ, P.active = Finset.Icc a b ∧
        ∀ H : ℝ, ‖anchorOutsideDifferenceSlab P a b H‖ ≤
          2*(P.ordinates.card : ℝ)*P.N^(2993/1000 : ℝ) := by
  classical
  obtain ⟨C₀,hC₀,hsource⟩ := reflectedOutsideBand_pattern_bound
  obtain ⟨C₁,_,hlocal⟩ := ordinate_local_count_pair
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hNT hT hV
  obtain ⟨a,b,hab,hpoint⟩ := hsource P ((le_max_left _ _).trans hPN) hNT hT
  refine ⟨a,b,hab,?_⟩
  intro H
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hrow (t : ℝ) (ht : t ∈ P.ordinates) :
      ‖∑ u ∈ P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
        P.N^(10/3 : ℝ) < u-t),
        anchorOutsideBand P a b (wideMismatchBand P.N) t u‖ ≤ 2*P.N^(2993/1000 : ℝ) := by
    let S := P.ordinates.filter (fun u => H ≤ u-t ∧ u-t ≤ H+P.N^(10/3 : ℝ) ∧
      P.N^(10/3 : ℝ) < u-t)
    let B := P.ordinates.filter (fun u => t+H ≤ u ∧ u ≤ (t+H)+P.N^(10/3 : ℝ))
    have hSB : S ⊆ B := by
      intro u hu
      obtain ⟨hu,hlo,hhi,_⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu,by constructor <;> linarith⟩
    have hS : (S.card : ℝ) ≤ P.N^(1/20 : ℝ) :=
      (show (S.card : ℝ) ≤ B.card by exact_mod_cast Finset.card_le_card hSB).trans
        (hlocal P ((le_max_right _ _).trans hPN) hV (t+H))
    have hterm (u : ℝ) (hu : u ∈ S) :
        ‖anchorOutsideBand P a b (wideMismatchBand P.N) t u‖ ≤ 2*P.N^(2943/1000 : ℝ) := by
      have hui := (Finset.mem_filter.mp hu).1
      have hgap := (Finset.mem_filter.mp hu).2.2.2
      have htu : t ≤ u := by have := Real.rpow_pos_of_pos hNp (10/3 : ℝ); linarith
      simpa only [anchorOutsideBand,if_pos htu] using hpoint t ht u hui hgap
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _u ∈ S, 2*P.N^(2943/1000 : ℝ) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ)*(2*P.N^(2943/1000 : ℝ)) := by simp
      _ ≤ P.N^(1/20 : ℝ)*(2*P.N^(2943/1000 : ℝ)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 2*(P.N^(1/20 : ℝ)*P.N^(2943/1000 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  unfold anchorOutsideDifferenceSlab
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ P.ordinates, 2*P.N^(2993/1000 : ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem anchorOutsideDifferenceSlab_eq_far_restriction (P : ZetaLargeValuePattern)
    (a b : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    anchorOutsideDifferenceSlab P a b H =
      ∑ t : P.ordinates, ∑ u : P.ordinates,
        if H ≤ (u : ℝ)-t ∧ (u : ℝ)-t ≤ H+P.N^(10/3 : ℝ) then
          if P.N^(10/3 : ℝ) < |(u : ℝ)-t| then
            anchorOutsideBand P a b (wideMismatchBand P.N) t u else 0 else 0 := by
  classical
  unfold anchorOutsideDifferenceSlab
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h₁ : H ≤ (u : ℝ)-t
  · by_cases h₂ : (u : ℝ)-t ≤ H+P.N^(10/3 : ℝ)
    · rw [abs_of_nonneg (hH.trans h₁)]
      simp only [h₁,h₂,true_and,and_self,ite_true]
    · simp only [h₂,and_false,false_and,ite_false]
  · simp only [h₁,false_and,ite_false]

#print axioms anchorOutsideDifferenceSlab_bound
#print axioms anchorOutsideDifferenceSlab_eq_far_restriction

/-- Actual local nonconcentration controls the near operator even at the
pair-driven cutoff N^(10/3). The local count and analytic row estimate
are derived here, not supplied as assumptions. -/
theorem nearMatrix_pairGap_row {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V → ∀ t : P.ordinates,
      (∑ u : P.ordinates, ‖nearMatrix P.toLargeValuePattern (P.N^(10/3 : ℝ)) t u‖) ≤
        P.N^(1+ε) := by
  classical
  obtain ⟨C₀,hC₀,hrow⟩ := exponentPair_nearMatrix_local_row exponentPair_three_fortieths
    (ε := 1/10000) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (eventually_pairNear_scales hC₀ hε)
  obtain ⟨C₁,hC₁,hlocal⟩ := ordinate_local_mass_pair hε
  refine ⟨max C₁ N₀,hC₁.trans (le_max_left _ _),?_⟩
  intro P hPN hV t
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let L := P.N^(10/3 : ℝ)
  let S := P.ordinates.filter (fun u => |u-(t:ℝ)| ≤ L)
  let A := P.ordinates.filter (fun u => (t:ℝ)-L ≤ u ∧ u ≤ ((t:ℝ)-L)+L)
  let B := P.ordinates.filter (fun u => (t:ℝ) ≤ u ∧ u ≤ (t:ℝ)+L)
  have hsub : S ⊆ A ∪ B := by
    intro u hu
    obtain ⟨hu,hd⟩ := Finset.mem_filter.mp hu
    have hd' := abs_le.mp hd
    rcases le_total u (t:ℝ) with hut | htu
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,by constructor <;> linarith⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,htu,by linarith⟩)
  have hcard : (S.card : ℝ) ≤ A.card+B.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hA := hlocal P ((le_max_left _ _).trans hPN) hV ((t:ℝ)-L)
  have hB := hlocal P ((le_max_left _ _).trans hPN) hV (t:ℝ)
  change (A.card : ℝ)*P.V^2 ≤ _ at hA
  change (B.card : ℝ)*P.V^2 ≤ _ at hB
  have hmass : (S.card : ℝ)*P.V^2 ≤ 2*P.N^(2+ε) := by
    have hc := mul_le_mul_of_nonneg_right hcard (sq_nonneg P.V)
    nlinarith only [hc,hA,hB]
  have hv2 : P.N^(1951/1000 : ℝ) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  obtain ⟨hvalue,hdiag⟩ := hN₀ P.N ((le_max_right _ _).trans hPN)
  let F := C₀*((2*L)/P.N)^(3/40+1/10000 : ℝ)*P.N^(31/40+1/10000 : ℝ)
  let D := 2*P.N+4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*L)) : ℝ)
  have hlocalF : 4*P.N*((S.card : ℝ)*F) ≤ 2*P.N^(2+ε) := by
    have hh := mul_le_mul_of_nonneg_left (hvalue.trans hv2) (Nat.cast_nonneg S.card)
    change (S.card : ℝ)*(4*P.N*F) ≤ _ at hh
    nlinarith only [hh,hmass]
  have hdiag' : 8*P.N*D ≤ P.N^(2+ε) := by
    simpa only [D,L,mul_assoc] using hdiag
  have hr := hrow P.toLargeValuePattern L (Real.rpow_pos_of_pos hNp _) t
  have hbudget : 2*P.N+C₀*(S.card : ℝ)*((2*L)/P.N)^(3/40+1/10000 : ℝ)*
      P.N^(31/40+1/10000 : ℝ)+4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*L)) : ℝ) =
      D+(S.card : ℝ)*F := by dsimp [D,F]; ring
  change (∑ u : P.ordinates, ‖nearMatrix P.toLargeValuePattern L t u‖) ≤ _ at hr
  rw [hbudget] at hr
  apply hr.trans
  have hpow : P.N^(2+ε) = P.N*P.N^(1+ε) := by
    nth_rw 2 [← Real.rpow_one P.N]
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  rw [hpow] at hlocalF hdiag'
  have hpos := Real.rpow_pos_of_pos hNp (1+ε)
  nlinarith only [hlocalF,hdiag',hpos,hNp]

/-- The actual far matrix has no large negative spectrum at the enlarged
cutoff. This consumes the proved local near row and the original Gram
positivity, without a spectral hypothesis. -/
theorem farMatrix_pairGap_eigenvalue_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V → ∀ i : P.ordinates,
      -P.N^(1+ε) ≤
        (farMatrix_hermitian P.toLargeValuePattern (P.N^(10/3 : ℝ))).eigenvalues i := by
  obtain ⟨C,hC,hrow⟩ := nearMatrix_pairGap_row hε
  refine ⟨C,hC,?_⟩
  intro P hPN hV i
  let L := P.N^(10/3 : ℝ)
  let H := farMatrix_hermitian P.toLargeValuePattern L
  let x : P.ordinates → ℂ := H.eigenvectorBasis i
  have hx : (∑ j, ‖x j‖^2) = 1 := by
    have hn := H.eigenvectorBasis.orthonormal.1 i
    have hs := congrArg (fun r : ℝ => r^2) hn
    dsimp only at hs
    rw [EuclideanSpace.norm_sq_eq] at hs
    simpa only [one_pow] using hs
  have hnear := hermitian_quadratic_norm_le_row (nearMatrix_hermitian P.toLargeValuePattern L)
    (hrow P hPN hV) x
  rw [hx,mul_one] at hnear
  have hpos := (fullMatrix_posSemidef P.toLargeValuePattern).re_dotProduct_nonneg x
  rw [← near_add_far P.toLargeValuePattern L,Matrix.add_mulVec,dotProduct_add,map_add] at hpos
  have he := H.eigenvalues_eq i
  change H.eigenvalues i = (star x ⬝ᵥ (farMatrix P.toLargeValuePattern L *ᵥ x)).re at he
  have hn := (Complex.re_le_norm (star x ⬝ᵥ (nearMatrix P.toLargeValuePattern L *ᵥ x))).trans hnear
  change 0 ≤ (star x ⬝ᵥ (nearMatrix P.toLargeValuePattern L *ᵥ x)).re+
    (star x ⬝ᵥ (farMatrix P.toLargeValuePattern L *ᵥ x)).re at hpos
  change -P.N^(1+ε) ≤ H.eigenvalues i
  linarith only [hn,hpos,he]

#print axioms nearMatrix_pairGap_row
#print axioms farMatrix_pairGap_eigenvalue_lower

/-- A signed cubic bound for the actual anchored far correlation, now at
N^(10/3). All negative-spectrum control is discharged internally. -/
theorem anchorFar_pairGap_cube {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      (anchorFar P (P.N^(10/3 : ℝ))).re^3 ≤ anchorMass P^3*
        ((farTriangle P.toLargeValuePattern (P.N^(10/3 : ℝ))).re+
          (P.ordinates.card : ℝ)*P.N^(3+ε)) := by
  classical
  obtain ⟨C,hC,hlow⟩ := farMatrix_pairGap_eigenvalue_lower
    (ε := ε/3) (by positivity)
  refine ⟨C,hC,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  by_cases hW : P.ordinates.Nonempty
  · haveI : Nonempty P.ordinates := hW.to_subtype
    let x : P.ordinates → ℂ := fun t => conj (zetaAnchor P t)
    have hx : (∑ t, ‖x t‖^2) = anchorMass P := by
      simp only [x,Complex.norm_conj,anchorMass]
    have hf : star x ⬝ᵥ (farMatrix P.toLargeValuePattern (P.N^(10/3 : ℝ)) *ᵥ x) =
        anchorFar P (P.N^(10/3 : ℝ)) := by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,Complex.star_def,
        x,starRingEnd_self_apply,anchorFar]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      ring
    have hh := hermitian_quadratic_cube_le
      (farMatrix_hermitian P.toLargeValuePattern (P.N^(10/3 : ℝ)))
      (Real.rpow_nonneg hNp.le (1+ε/3)) (hlow P hPN hV) x hx.le
    have hp : (P.N^(1+ε/3))^3 = P.N^(3+ε) := by
      rw [← Real.rpow_mul_natCast hNp.le]
      congr 1
      ring
    rw [hf,hp,← farTriangle_trace] at hh
    simpa only [Fintype.card_coe] using hh
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    haveI : IsEmpty P.ordinates := by simpa only [he] using
      (inferInstance : IsEmpty (↥(∅ : Finset ℝ)))
    have hf : anchorFar P (P.N^(10/3 : ℝ)) = 0 :=
      Finset.sum_eq_zero (fun t _ => isEmptyElim t)
    have hm : anchorMass P = 0 := Finset.sum_eq_zero (fun t _ => isEmptyElim t)
    rw [hf,hm,Complex.zero_re,zero_pow (by decide : (3 : ℕ) ≠ 0),zero_mul]

#print axioms anchorFar_pairGap_cube

/-- The actual anchored Gram inequality consumes the enlarged-cutoff
spectral estimate. The remaining signed triangle is not replaced by an
absolute sum or by an assumed upper bound. -/
theorem anchorMass_pairGap_triangle_dichotomy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      anchorMass P ≤ 4*P.N^(2+ε/3) ∨
      anchorMass P^3 ≤ 64*P.N^3*
        ((farTriangle P.toLargeValuePattern (P.N^(10/3 : ℝ))).re+
          (P.ordinates.card : ℝ)*P.N^(3+ε)) := by
  obtain ⟨C₀,hC₀,hrow⟩ := nearMatrix_pairGap_row (ε := ε/3) (by positivity)
  obtain ⟨C₁,_,hcube⟩ := anchorFar_pairGap_cube hε
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let L := P.N^(10/3 : ℝ)
  let x : P.ordinates → ℂ := fun t => conj (zetaAnchor P t)
  have hn := hermitian_quadratic_norm_le_row (nearMatrix_hermitian P.toLargeValuePattern L)
    (hrow P ((le_max_left _ _).trans hPN) hV) x
  have hx : (∑ t, ‖x t‖^2) = anchorMass P := by
    simp only [x,Complex.norm_conj,anchorMass]
  rw [hx] at hn
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
  have hnear := (Complex.re_le_norm _).trans hn
  have hg' := hg.trans (mul_le_mul_of_nonneg_left (add_le_add hnear le_rfl)
    (show 0 ≤ 2*P.N by positivity))
  have hmass : 0 ≤ anchorMass P := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hs : anchorMass P ≤ 4*P.N^(2+ε/3)
  · exact Or.inl hs
  · right
    have hmpos : 0 < anchorMass P :=
      (by positivity : 0 < 4*P.N^(2+ε/3)).trans (lt_of_not_ge hs)
    have hp : P.N^(2+ε/3) = P.N*P.N^(1+ε/3) := by
      nth_rw 2 [← Real.rpow_one P.N]
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hs) hmass
    rw [hp] at hm
    have habs : anchorMass P^2 ≤ 4*P.N*(anchorFar P L).re := by
      nlinarith only [hg',hm]
    have hc := pow_le_pow_left₀ (sq_nonneg (anchorMass P)) habs 3
    have ht := mul_le_mul_of_nonneg_left
      (hcube P ((le_max_right _ _).trans hPN) hV) (show 0 ≤ 64*P.N^3 by positivity)
    have hfinal : anchorMass P^3*anchorMass P^3 ≤
        (64*P.N^3*((farTriangle P.toLargeValuePattern L).re+
          (P.ordinates.card : ℝ)*P.N^(3+ε)))*anchorMass P^3 := by
      calc
        _ = (anchorMass P^2)^3 := by ring
        _ ≤ (4*P.N*(anchorFar P L).re)^3 := hc
        _ = 64*P.N^3*(anchorFar P L).re^3 := by ring
        _ ≤ _ := by convert ht using 1; ring
    exact (mul_le_mul_iff_left₀ (pow_pos hmpos 3)).mp hfinal

#print axioms anchorMass_pairGap_triangle_dichotomy

/-- The literal increasing-ordinate portion of the far cubic trace. -/
def orderedFarTriangle (P : ZetaLargeValuePattern) (L : ℝ) : ℂ :=
  ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates, ∑ v ∈ P.ordinates,
    if L < u-t ∧ L < v-u then
      gramKernel P.toLargeValuePattern t u*gramKernel P.toLargeValuePattern u v*
        gramKernel P.toLargeValuePattern v t else 0

/-- Both adjacent positive gaps are retained in the actual dual phase.
The max/min only chooses the curvature estimate's orientation. -/
def orderedTriangleOutsideBand (P : ZetaLargeValuePattern) (K : Finset ℤ) (L : ℝ) : ℂ :=
  ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates, ∑ v ∈ P.ordinates,
    if L < u-t ∧ L < v-u then
      reflectedOutsideBand P.N (max (u-t) (v-u)) (min (u-t) (v-u))
        P.scale (2*P.scale) P.scale (2*P.scale) P.scale (2*P.scale) K else 0

theorem orderedFarTriangle_eq_far_restriction (P : ZetaLargeValuePattern)
    {L : ℝ} (hL : 0 ≤ L) :
    orderedFarTriangle P L =
      ∑ t : P.ordinates, ∑ u : P.ordinates, ∑ v : P.ordinates,
        if L < (u : ℝ)-t ∧ L < (v : ℝ)-u then
          farMatrix P.toLargeValuePattern L t u*farMatrix P.toLargeValuePattern L u v*
            farMatrix P.toLargeValuePattern L v t else 0 := by
  classical
  unfold orderedFarTriangle
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_attach P.ordinates]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hg
  · have htu : L < |(u : ℝ)-t| := hg.1.trans_le (le_abs_self _)
    have huv : L < |(v : ℝ)-u| := hg.2.trans_le (le_abs_self _)
    have hvt : L < |(t : ℝ)-v| := by
      rw [abs_sub_comm]
      exact (show L < (v : ℝ)-t by linarith only [hg.1,hg.2,hL]).trans_le (le_abs_self _)
    simp only [farMatrix,htu,huv,hvt,ite_true]
  · rfl

private theorem ordered_gram_product (P : ZetaLargeValuePattern) (t u v : ℝ) :
    gramKernel P.toLargeValuePattern t u*gramKernel P.toLargeValuePattern u v*
      gramKernel P.toLargeValuePattern v t =
    (∑ n ∈ Finset.Icc P.scale (2*P.scale),dirichletPhase n (max (u-t) (v-u)))*
    (∑ n ∈ Finset.Icc P.scale (2*P.scale),dirichletPhase n (min (u-t) (v-u)))*
    conj (∑ n ∈ Finset.Icc P.scale (2*P.scale),
      dirichletPhase n (max (u-t) (v-u)+min (u-t) (v-u))) := by
  rw [← gramKernel_conj P.toLargeValuePattern v t]
  simp only [gramKernel,P.indices_eq_dyadicInterval,max_add_min]
  rw [show u-t+(v-u)=v-t by ring]
  rcases le_total (u-t) (v-u) with h | h
  · rw [max_eq_right h,min_eq_left h]
    ring
  · rw [max_eq_left h,min_eq_right h]

/-- Discrete frequency cancellation on the actual increasing-ordinate
part of the cubic far trace. All moving stationary sets and all errors
are retained; there is no assumed estimate for the complementary sum. -/
theorem orderedFarTriangle_outsideBand_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ZetaLargeValuePattern) (L : ℝ) (K : Finset ℤ),
      4*Real.pi*P.N ≤ L →
      ‖orderedFarTriangle P L-orderedTriangleOutsideBand P K L‖ ≤
        (P.ordinates.card : ℝ)^3*(3072*P.N^2*(K.card : ℝ)+
          3*(C*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^ε))*
            (2*P.N+C*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^ε))^2) := by
  obtain ⟨C,hC,hsource⟩ := dirichlet_product_outsideBand_error hε
  refine ⟨C,hC,?_⟩
  intro P L K hL
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hπ : 0 < 2*Real.pi := by positivity
  have hLp : 0 < L := (by positivity : 0 < 4*Real.pi*P.N).trans_le hL
  let E := C*(P.N/Real.sqrt (L/(2*Real.pi))+((2*P.T)/(2*Real.pi))^ε)
  have hE : 0 ≤ E := by have := P.T_pos; dsimp [E]; positivity
  have hpoint (t u v : ℝ) (ht : t ∈ P.ordinates) (hv : v ∈ P.ordinates) :
      ‖(if L < u-t ∧ L < v-u then
          gramKernel P.toLargeValuePattern t u*gramKernel P.toLargeValuePattern u v*
            gramKernel P.toLargeValuePattern v t else 0)-
        (if L < u-t ∧ L < v-u then
          reflectedOutsideBand P.N (max (u-t) (v-u)) (min (u-t) (v-u))
            P.scale (2*P.scale) P.scale (2*P.scale) P.scale (2*P.scale) K else 0)‖ ≤
        3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2 := by
    by_cases hg : L < u-t ∧ L < v-u
    · simp only [if_pos hg]
      let A := max (u-t) (v-u)
      let B := min (u-t) (v-u)
      have hB : L < B := lt_min hg.1 hg.2
      have hAB : B ≤ A := min_le_max
      have hBp : 0 < B := hLp.trans hB
      have hAp : 0 < A := hBp.trans_le hAB
      have hsum : A+B = v-t := by dsimp [A,B]; rw [max_add_min]; ring
      have hrange : A+B ≤ 2*P.T := by
        have ht' := P.ordinates_in_interval t ht
        have hv' := P.ordinates_in_interval v hv
        rw [hsum]
        linarith [P.interval_length,P.T_pos]
      have hsc : P.N ≤ (P.scale : ℝ) := P.N_eq_scale.le
      have hsc' : ((2*P.scale : ℕ) : ℝ) ≤ 2*P.N := by rw [P.N_eq_scale]; norm_num
      have hh := hsource P.N A B P.scale (2*P.scale) P.scale (2*P.scale)
        P.scale (2*P.scale) K P.one_lt_N.le (hL.trans hB.le) hAB hsc hsc' hsc hsc' hsc hsc'
      rw [ordered_gram_product]
      apply hh.trans
      have herr : C*(P.N/Real.sqrt (B/(2*Real.pi))+((A+B)/(2*Real.pi))^ε) ≤ E := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
        apply add_le_add
        · exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (div_pos hLp hπ))
            (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB.le hπ.le))
        · exact Real.rpow_le_rpow (by positivity)
            (div_le_div_of_nonneg_right hrange hπ.le) hε.le
      have herrorNonneg : 0 ≤ C*(P.N/Real.sqrt (B/(2*Real.pi))+((A+B)/(2*Real.pi))^ε) := by
        positivity
      change 3072*P.N^2*(K.card : ℝ)+3*(C*(P.N/Real.sqrt (B/(2*Real.pi))+
        ((A+B)/(2*Real.pi))^ε))*(2*P.N+C*(P.N/Real.sqrt (B/(2*Real.pi))+
        ((A+B)/(2*Real.pi))^ε))^2 ≤ _
      gcongr
    · simp only [if_neg hg,sub_self,norm_zero]
      positivity
  unfold orderedFarTriangle orderedTriangleOutsideBand
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t ∈ P.ordinates, ∑ _u ∈ P.ordinates, ∑ _v ∈ P.ordinates,
        (3072*P.N^2*(K.card : ℝ)+3*E*(2*P.N+E)^2) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => hpoint t u v ht hv))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [E]; ring

#print axioms orderedFarTriangle_eq_far_restriction
#print axioms ordered_gram_product
#print axioms orderedFarTriangle_outsideBand_error

def traceMismatchBand (N : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊N^(4/5 : ℝ)⌋) ⌊N^(4/5 : ℝ)⌋

theorem traceMismatchBand_card {N : ℝ} (hN : 1 ≤ N) :
    ((traceMismatchBand N).card : ℝ) ≤ 3*N^(4/5 : ℝ) := by
  have hs : 1 ≤ N^(4/5 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hfloor := Int.floor_le (N^(4/5 : ℝ))
  have hm (k : ℤ) (hk : k ∈ traceMismatchBand N) :
      -N^(4/5 : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ N^(4/5 : ℝ) := by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
    have hl' : -((⌊N^(4/5 : ℝ)⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl
    have hu' : (k : ℝ) ≤ ((⌊N^(4/5 : ℝ)⌋ : ℤ) : ℝ) := by exact_mod_cast hu
    constructor <;> linarith
  have hc := integer_card_le_interval_length_add_one (traceMismatchBand N)
    (by linarith : -N^(4/5 : ℝ) ≤ N^(4/5 : ℝ)) hm
  linarith

/-- The actual cubic-trace portion loses only O(R^3 N^(14/5)) when the
N^(4/5) mismatch band and all three reflection errors are removed. -/
theorem orderedFarTriangle_traceBand_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      ‖orderedFarTriangle P (P.N^(10/3 : ℝ))-
        orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))‖ ≤
        9243*(P.ordinates.card : ℝ)^3*P.N^(14/5 : ℝ) := by
  obtain ⟨C₀,hC₀,hsource⟩ := orderedFarTriangle_outsideBand_error (ε := 1/100) (by norm_num)
  obtain ⟨N₀,hN₀,hsmall⟩ := eventually_reflectionError_sqrt C₀ (zero_le_one.trans hC₀)
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*Real.pi) (by positivity)
      0 (η := 2/5) (by norm_num))
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNL : P.N^(7/5 : ℝ) ≤ P.N^(10/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)
  have hc : 4*Real.pi ≤ P.N^(2/5 : ℝ) := by
    simpa only [pow_zero,mul_one] using hN₁ P.N ((le_max_right _ _).trans hPN)
  have hL : 4*Real.pi*P.N ≤ P.N^(10/3 : ℝ) := by
    apply le_trans _ hNL
    calc
      _ ≤ P.N^(2/5 : ℝ)*P.N := mul_le_mul_of_nonneg_right hc hNp.le
      _ = _ := by nth_rw 2 [← Real.rpow_one P.N]; rw [← Real.rpow_add hNp]; norm_num
  have herror := hsource P (P.N^(10/3 : ℝ)) (traceMismatchBand P.N) hL
  let E := C₀*(P.N/Real.sqrt (P.N^(10/3 : ℝ)/(2*Real.pi))+
    ((2*P.T)/(2*Real.pi))^(1/100 : ℝ))
  have hE0 : 0 ≤ E := by have := P.T_pos; dsimp [E]; positivity
  have hE : E ≤ P.N^(1/2 : ℝ) := by
    apply le_trans _ (hsmall P.N ((le_max_left _ _).trans hPN) P.T P.T_pos hT)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC₀)
    apply add_le_add _ le_rfl
    exact div_le_div_of_nonneg_left hNp.le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hNL (by positivity)))
  have hhalf : P.N^(1/2 : ℝ) ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (1/2 : ℝ) ≤ 1)
  have hpower : P.N^2*P.N^(4/5 : ℝ) = P.N^(14/5 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNp]
    norm_num
  have hband : 3072*P.N^2*((traceMismatchBand P.N).card : ℝ) ≤ 9216*P.N^(14/5 : ℝ) := by
    calc
      _ ≤ 3072*P.N^2*(3*P.N^(4/5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (traceMismatchBand_card P.one_lt_N.le) (by positivity)
      _ = _ := by rw [← hpower]; ring
  have hreflect : 3*E*(2*P.N+E)^2 ≤ 27*P.N^(14/5 : ℝ) := by
    calc
      _ ≤ 3*P.N^(1/2 : ℝ)*(2*P.N+P.N)^2 := by gcongr; exact hE.trans hhalf
      _ = 27*P.N^2*P.N^(1/2 : ℝ) := by ring
      _ ≤ 27*P.N^2*P.N^(4/5 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)) (by positivity)
      _ = _ := by rw [← hpower]; ring
  apply herror.trans
  calc
    _ ≤ (P.ordinates.card : ℝ)^3*(9243*P.N^(14/5 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hband,hreflect]) (by positivity)
    _ = _ := by ring

#print axioms traceMismatchBand_card
#print axioms orderedFarTriangle_traceBand_uniform

/-- Exact six-orientation identity for the real signed trace. Reversing a
cycle conjugates its value; it never replaces that value by its norm. -/
theorem farTriangle_re_eq_six_ordered (P : ZetaLargeValuePattern)
    {L : ℝ} (hL : 0 ≤ L) :
    (farTriangle P.toLargeValuePattern L).re = 6*(orderedFarTriangle P L).re := by
  classical
  let A := farMatrix P.toLargeValuePattern L
  let F (t u v : P.ordinates) : ℝ := (A t u*A u v*A v t).re
  let G (t u v : P.ordinates) : ℝ := if (t : ℝ) < u ∧ (u : ℝ) < v then F t u v else 0
  have hd (t : P.ordinates) : A t t = 0 := by
    simp only [A,farMatrix,sub_self,abs_zero,not_lt.mpr hL,ite_false]
  have hcyc (t u v : P.ordinates) : F u v t = F t u v := by
    dsimp [F]
    congr 1
    ring
  have hrev (t u v : P.ordinates) : F v u t = F t u v := by
    have hh (t u : P.ordinates) : conj (A u t) = A t u :=
      (farMatrix_hermitian P.toLargeValuePattern L).apply t u
    calc
      _ = (conj (A v u*A u t*A t v)).re := (Complex.conj_re _).symm
      _ = _ := by rw [map_mul,map_mul,hh,hh,hh]; dsimp [F]; congr 1; ring
  have hpoint (t u v : P.ordinates) : F t u v =
      G t u v+G u v t+G v t u+G t v u+G v u t+G u t v := by
    by_cases htu : t = u
    · subst u
      simp only [G,F,hd,mul_zero,zero_mul,Complex.zero_re,ite_self,add_zero]
    by_cases huv : u = v
    · subst v
      simp only [G,F,hd,mul_zero,zero_mul,Complex.zero_re,ite_self,add_zero]
    by_cases htv : t = v
    · subst v
      simp only [G,F,hd,mul_zero,zero_mul,Complex.zero_re,ite_self,add_zero]
    have htu' : (t : ℝ) ≠ u := fun he => htu (Subtype.ext he)
    have huv' : (u : ℝ) ≠ v := fun he => huv (Subtype.ext he)
    have htv' : (t : ℝ) ≠ v := fun he => htv (Subtype.ext he)
    have h₂ := hcyc t u v
    have h₃ := (hcyc u v t).trans h₂
    have h₄ := (hcyc u t v).trans ((hcyc v u t).trans (hrev t u v))
    have h₅ := hrev t u v
    have h₆ := (hcyc v u t).trans h₅
    simp only [G,h₂,h₃,h₄,h₅,h₆]
    rcases lt_or_gt_of_ne htu' with htu' | hut'
    <;> rcases lt_or_gt_of_ne huv' with huv' | hvu'
    <;> rcases lt_or_gt_of_ne htv' with htv' | hvt'
    <;> simp_all only [lt_asymm,and_true,and_false,
      ite_true,ite_false,add_zero,zero_add]
    <;> linarith
  let O : ℝ := ∑ t : P.ordinates, ∑ u : P.ordinates, ∑ v : P.ordinates, G t u v
  have hsumcyc (f : P.ordinates → P.ordinates → P.ordinates → ℝ) :
      (∑ t, ∑ u, ∑ v, f u v t) = ∑ t, ∑ u, ∑ v, f t u v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    exact Finset.sum_comm
  have hsumrev : (∑ t, ∑ u, ∑ v, G t v u) = O := by
    apply Finset.sum_congr rfl
    intro t _
    exact Finset.sum_comm
  have hs₂ : (∑ t, ∑ u, ∑ v, G u v t) = O := hsumcyc G
  have hs₃ : (∑ t, ∑ u, ∑ v, G v t u) = O :=
    (hsumcyc (fun t u v => G u v t)).trans hs₂
  have hs₅ : (∑ t, ∑ u, ∑ v, G v u t) = O :=
    (hsumcyc (fun t u v => G u t v)).trans
      ((hsumcyc (fun t u v => G t v u)).trans hsumrev)
  have hs₆ : (∑ t, ∑ u, ∑ v, G u t v) = O :=
    (hsumcyc (fun t u v => G t v u)).trans hsumrev
  have hsum : (farTriangle P.toLargeValuePattern L).re = 6*O := by
    change (∑ t, ∑ u, ∑ v, A t u*A u v*A v t).re = _
    simp only [Complex.re_sum]
    change (∑ t, ∑ u, ∑ v, F t u v) = _
    simp_rw [hpoint,Finset.sum_add_distrib]
    rw [hs₂,hs₃,hsumrev,hs₅,hs₆]
    change O+O+O+O+O+O = _
    ring
  rw [hsum]
  congr 1
  rw [orderedFarTriangle_eq_far_restriction P hL]
  simp only [Complex.re_sum,apply_ite Complex.re,Complex.zero_re]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change G t u v = if L < (u : ℝ)-t ∧ L < (v : ℝ)-u then F t u v else 0
  by_cases ho : (t : ℝ) < u ∧ (u : ℝ) < v
  · simp only [G,if_pos ho]
    by_cases hg : L < (u : ℝ)-t ∧ L < (v : ℝ)-u
    · rw [if_pos hg]
    · rw [if_neg hg]
      have hzero : A t u = 0 ∨ A u v = 0 := by
        rw [not_and_or] at hg
        rcases hg with htu | huv
        · left
          simp only [A,farMatrix,abs_of_nonneg (sub_nonneg.mpr ho.1.le),htu,ite_false]
        · right
          simp only [A,farMatrix,abs_of_nonneg (sub_nonneg.mpr ho.2.le),huv,ite_false]
      rcases hzero with h | h <;> simp only [F,h,mul_zero,zero_mul,Complex.zero_re]
  · have hg : ¬ (L < (u : ℝ)-t ∧ L < (v : ℝ)-u) := by
      intro h
      apply ho
      constructor <;> linarith only [h.1,h.2,hL]
    simp only [G,if_neg ho,if_neg hg]

#print axioms farTriangle_re_eq_six_ordered

/-- Cancellation of the stated mismatch band in the FULL actual signed
cubic trace, including every orientation and every reflection error. -/
theorem farTriangle_traceBand_re_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      |(farTriangle P.toLargeValuePattern (P.N^(10/3 : ℝ))).re-
        6*(orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))).re| ≤
        55458*(P.ordinates.card : ℝ)^3*P.N^(14/5 : ℝ) := by
  obtain ⟨C,hC,hsource⟩ := orderedFarTriangle_traceBand_uniform
  refine ⟨C,hC,?_⟩
  intro P hPN hT
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have he := (Complex.abs_re_le_norm _).trans (hsource P hPN hT)
  rw [Complex.sub_re] at he
  rw [farTriangle_re_eq_six_ordered P (Real.rpow_nonneg hNp.le _),
    ← mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 6)
  convert hh using 1
  ring

/-- The actual Gram/spectral consumer absorbs the complete band-removal
cost at the physical endpoint threshold. Only the signed outside-band
triangle and the explicit negative-spectrum remainder remain. -/
theorem anchorMass_triangleOutsideBand_dichotomy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      anchorMass P ≤ 4*P.N^(2+ε/3) ∨
      anchorMass P^3 ≤
        768*P.N^3*(orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))).re+
          128*(P.ordinates.card : ℝ)*P.N^(6+ε) := by
  obtain ⟨C₀,hC₀,hgram⟩ := anchorMass_pairGap_triangle_dichotomy hε
  obtain ⟨C₁,_,hband⟩ := farTriangle_traceBand_re_error
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 7098624 (by norm_num) 0
      (η := 53/1000) (by norm_num))
  refine ⟨max C₀ (max C₁ N₀),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  rcases hgram P ((le_max_left _ _).trans hPN) hV with hg | hg
  · exact Or.inl hg
  · right
    have herror := le_of_abs_le (hband P
      ((le_max_left C₁ N₀).trans ((le_max_right _ _).trans hPN)) hT)
    have hc : 7098624 ≤ P.N^(53/1000 : ℝ) := by
      simpa only [pow_zero,mul_one] using hN₀ P.N
        ((le_max_right C₁ N₀).trans ((le_max_right _ _).trans hPN))
    have hv6 : P.N^(5853/1000 : ℝ) ≤ P.V^6 := by
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 6
      rw [← Real.rpow_mul_natCast hNp.le] at hh
      norm_num at hh
      exact hh
    have hscale : 7098624*P.N^(29/5 : ℝ) ≤ P.V^6 := by
      calc
        _ ≤ P.N^(53/1000 : ℝ)*P.N^(29/5 : ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _)
        _ = P.N^(5853/1000 : ℝ) := by rw [← Real.rpow_add hNp]; norm_num
        _ ≤ _ := hv6
    have hm := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity)
      (anchorMass_lower P) 3
    have hp : P.N^3*P.N^(14/5 : ℝ) = P.N^(29/5 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hNp]
      norm_num
    have habs : 128*P.N^3*(55458*(P.ordinates.card : ℝ)^3*P.N^(14/5 : ℝ)) ≤
        anchorMass P^3 := by
      calc
        _ = (P.ordinates.card : ℝ)^3*(7098624*P.N^(29/5 : ℝ)) := by rw [← hp]; ring
        _ ≤ (P.ordinates.card : ℝ)^3*P.V^6 :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = ((P.ordinates.card : ℝ)*P.V^2)^3 := by ring
        _ ≤ _ := hm
    have herr := mul_le_mul_of_nonneg_left herror (show 0 ≤ 128*P.N^3 by positivity)
    have hrem : P.N^3*P.N^(3+ε) = P.N^(6+ε) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hNp]
      congr 1
      ring
    rw [← hrem]
    nlinarith only [hg,herr,habs]

#print axioms farTriangle_traceBand_re_error
#print axioms anchorMass_triangleOutsideBand_dichotomy

/-- Entry of the frozen endpoint's actual two-sided neighbourhoods into
the signed all-three-gaps-far, outside-mismatch-band estimate. -/
theorem endpoint_orderedOutsideBand_dichotomy {τ ε : ℝ}
    (hτu : τ < 340/63) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card : ℝ)*P.V^2 ≤ 4*P.N^(2+ε/3) ∨
        (P.ordinates.card : ℝ)^3*P.V^6 ≤
          768*P.N^3*(orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))).re+
            128*(P.ordinates.card : ℝ)*P.N^(6+ε) := by
  obtain ⟨C,hC,hsource⟩ := anchorMass_triangleOutsideBand_dichotomy hε
  refine ⟨C,hC,1/2000,by norm_num,?_⟩
  intro P hPN _hTl hTu hVl _hVu
  have hT : P.T ≤ P.N^6 := hTu.trans (by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show τ+1/2000 ≤ (6 : ℕ) by norm_num; linarith only [hτu]))
  have hV : P.N^(1951/2000 : ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hVl
  rcases hsource P hPN hT hV with h | h
  · exact Or.inl ((anchorMass_lower P).trans h)
  · right
    have hm := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity)
      (anchorMass_lower P) 3
    have he : (P.ordinates.card : ℝ)^3*P.V^6 = ((P.ordinates.card : ℝ)*P.V^2)^3 := by ring
    rw [he]
    exact hm.trans h

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N^(37/7-δ) ≤ P.T → P.T ≤ P.N^(37/7+δ) →
        P.N^(41/42-δ) ≤ P.V → P.V ≤ P.N^(41/42+δ) →
        (P.ordinates.card : ℝ)*P.V^2 ≤ 4*P.N^(2+ε/3) ∨
        (P.ordinates.card : ℝ)^3*P.V^6 ≤
          768*P.N^3*(orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))).re+
            128*(P.ordinates.card : ℝ)*P.N^(6+ε) :=
  endpoint_orderedOutsideBand_dichotomy (by norm_num) hε

#print axioms endpoint_orderedOutsideBand_dichotomy

/-- The explicit negative-spectrum remainder is also absorbed once the
actual cardinality exceeds N^(2/25), below the frozen target range.
The only surviving analytic quantity is the signed outside-band trace. -/
theorem orderedOutsideBand_largeCard_dichotomy :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N → P.T ≤ P.N^6 →
      P.N^(1951/2000 : ℝ) ≤ P.V →
      (P.ordinates.card : ℝ) ≤ P.N^(2/25 : ℝ) ∨
      (P.ordinates.card : ℝ)^3*P.V^6 ≤
        1536*P.N^3*(orderedTriangleOutsideBand P (traceMismatchBand P.N) (P.N^(10/3 : ℝ))).re := by
  obtain ⟨C₀,hC₀,hsource⟩ := anchorMass_triangleOutsideBand_dichotomy
    (ε := 1/1000) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 4 (by norm_num) 0 (η := 23/750) (by norm_num))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 256 (by norm_num) 0 (η := 3/250) (by norm_num))
  refine ⟨max C₀ (max N₀ N₁),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hT hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv2 : P.N^(1951/1000 : ℝ) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh
    exact hh
  by_cases hR : (P.ordinates.card : ℝ) ≤ P.N^(2/25 : ℝ)
  · exact Or.inl hR
  · right
    rcases hsource P ((le_max_left _ _).trans hPN) hT hV with hm | hm
    · exfalso
      have hc : 4 ≤ P.N^(23/750 : ℝ) := by
        simpa only [pow_zero,mul_one] using hN₀ P.N
          ((le_max_left N₀ N₁).trans ((le_max_right _ _).trans hPN))
      have hscale : 4*P.N^(2+(1/1000 : ℝ)/3) ≤
          P.N^(2/25 : ℝ)*P.N^(1951/1000 : ℝ) := by
        calc
          _ ≤ P.N^(23/750 : ℝ)*P.N^(2+(1/1000 : ℝ)/3) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _)
          _ = _ := by rw [← Real.rpow_add hNp,← Real.rpow_add hNp]; norm_num
      have hl := (mul_le_mul_of_nonneg_left hv2 (Nat.cast_nonneg P.ordinates.card)).trans
        ((anchorMass_lower P).trans (hm.trans hscale))
      exact hR ((mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hNp _)).mp hl)
    · have hc : 256 ≤ P.N^(3/250 : ℝ) := by
        simpa only [pow_zero,mul_one] using hN₁ P.N
          ((le_max_right N₀ N₁).trans ((le_max_right _ _).trans hPN))
      have hv6 : P.N^(5853/1000 : ℝ) ≤ P.V^6 := by
        have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (1951/2000 : ℝ)) hV 6
        rw [← Real.rpow_mul_natCast hNp.le] at hh
        norm_num at hh
        exact hh
      have hr2 : P.N^(4/25 : ℝ) ≤ (P.ordinates.card : ℝ)^2 := by
        have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le (2/25 : ℝ)) (le_of_not_ge hR) 2
        rw [← Real.rpow_mul_natCast hNp.le] at hh
        norm_num at hh
        exact hh
      have hscale : 256*P.N^(6+1/1000 : ℝ) ≤ (P.ordinates.card : ℝ)^2*P.V^6 := by
        calc
          _ ≤ P.N^(3/250 : ℝ)*P.N^(6+1/1000 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _)
          _ = P.N^(4/25 : ℝ)*P.N^(5853/1000 : ℝ) := by
            rw [← Real.rpow_add hNp,← Real.rpow_add hNp]
            norm_num
          _ ≤ _ := mul_le_mul hr2 hv6 (Real.rpow_nonneg hNp.le _) (sq_nonneg _)
      have habs := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg P.ordinates.card)
      have hl := pow_le_pow_left₀ (show 0 ≤ (P.ordinates.card : ℝ)*P.V^2 by positivity)
        (anchorMass_lower P) 3
      nlinarith only [hm,habs,hl]

#print axioms orderedOutsideBand_largeCard_dichotomy

/-- The genuine phase of n^(-it), in the native mean-value theorem's
exp(2*pi*i*f) normalization. -/
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

/-- These are the installed coefficient-torus cells of the actual
logarithmic phase, not cells chosen to imply a desired large-value bound. -/
def logarithmicTaylorCell (H : ℕ) (t n : ℝ) : Set (GafniTao.HeathBrownCoefficientTorus 7) :=
  GafniTao.heathBrownCoefficientCell 7 H (logarithmicTaylorPhase t) n

/-- Mixed-height overlap of the actual cells supplies the three highest
coordinate conditions used in the common-centre spacing argument. -/
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

/-- A quantitative common-centre spacing bound obtained from the actual
overlap, by removing wrapping in coordinates six, five and four. -/
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

#print axioms logarithmicTaylorPhase_character
#print axioms logarithmicTaylorPhase_coordinate
#print axioms logarithmicTaylorCell_overlap_coordinates
#print axioms logarithmicTaylorCell_commonCentre_spacing

/-- Equal Taylor centres cannot contribute to the actual far-height cell
correlation. The Taylor length is selected from the physical pattern,
and every scale condition in the spacing argument is discharged. -/
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

/-- The actual mixed-height, mixed-centre coefficient constraint. -/
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

/-- Two high-coordinate constraints, with all wrapping removed, exclude
unequal integer centres in a short relative height interval. The overlap
is literal; no bound for a cell count or a far sum is a premise. -/
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

#print axioms logarithmicTaylorCell_mixed_coordinate
#print axioms reciprocal_fifth_sixth
#print axioms reciprocal_fifth_integer_gap
#print axioms logarithmicTaylorCell_mixed_centres_eq

/-- Every actual Taylor-cell interaction vanishes in this medium far
range, including unequal centres. All scales and wrapping conditions
are derived from the original physical pattern. -/
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

/-- The highest-coordinate difference of actual overlapping cells is
small as a real number, not merely modulo an integer. -/
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

/-- Actual mixed cells lie close to the one-variable fifth-coordinate
curve, with their actual nearest-integer label. This retains the integer
label for the subsequent nonzero/zero-label counting decomposition. -/
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

#print axioms logarithmicTaylorSixthRatio_bounds
#print axioms logarithmicTaylorCell_sixth_raw
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

/-- Quantitative diameter of a nonzero-label fibre of the actual
projected fifth-coordinate curve. This is the geometric estimate used
before counting integer centres, not a hypothesis on the count. -/
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

#print axioms reciprocal_fifth_real_gap
#print axioms fifth_curve_label_diameter

/-- At the actual Taylor length, a fixed nonzero fifth label restricts
the first integer centre to a short interval. All projection-scale
conditions are derived here from N; none is a counting premise. -/
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

/-- For a fixed first centre and fifth label there is at most one second
integer centre. This applies to the literal mixed cells at the selected
Taylor length and derives its precision from the actual height range. -/
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

#print axioms logarithmicTaylorCell_fifth_label_error
#print axioms logarithmicTaylorCell_same_label_unique_second

/-- Literal mixed-cell pairs, grouped by their fifth-coordinate integer
label. Both centres range over the original dyadic integer support. -/
def logarithmicTaylorLabelPairs (P : ZetaLargeValuePattern) (t u : ℝ) (q : ℤ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (P.indices.product P.indices).filter (fun p =>
    (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
      logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 = q)

/-- An actual finite count for each nonzero fifth label. The short
first-centre interval and second-centre uniqueness are both proved and
consumed here; neither is an external counting certificate. -/
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

def logarithmicTaylorNonzeroPairs (P : ZetaLargeValuePattern) (t u : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (P.indices.product P.indices).filter (fun p =>
    (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t p.1 ∩
      logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) u p.2).Nonempty ∧
      logarithmicTaylorFifthLabel t u p.1 p.2 ≠ 0)

/-- Summing every nonzero label of the actual mixed-cell correlation.
The harmonic weight comes from the proved reciprocal-label diameter. -/
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

#print axioms logarithmicTaylorFifthLabel_range
#print axioms logarithmicTaylorNonzeroPairs_card_harmonic

/-- The entire nonzero-label contribution is sublinear, uniformly for
the physical height range needed by the endpoint research. -/
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

/-- A reciprocal fifth-power constraint controls the width of the
actual zero-label strip. Only an upper bound for the centres is needed. -/
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

/-- The sixth-coordinate discrepancy on a zero fifth-label strip is
controlled by that strip's precision, with its physical lower scale. -/
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

#print axioms logarithmicTaylorNonzeroPairs_card_uniform
#print axioms reciprocal_fifth_gap_upper
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

/-- The actual zero-label overlap forces the integer frequency pair
into a strip of width O(N^6/(T H^5)), with no spacing premise. -/
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

#print axioms logarithmicTaylorFifthRatio_bounds
#print axioms logarithmicTaylorCell_zero_label_strip

/-- The physical height difference gives a quantitative nonzero slope
for the zero-label strip. -/
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

/-- Combining the actual zero fifth label and the unwrapped sixth
coordinate bounds the slope of the integer strip, not just its width. -/
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

#print axioms logarithmicTaylorFifthRatio_gap
#print axioms logarithmicTaylorCell_zero_label_slope

/-- Count integer points in the literal thin strip by their integer
difference. Both the number of differences and every fibre are proved. -/
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

/-- All zero-label mixed cells are counted in the larger-gap range.
The strip, its nonzero slope, and all scale losses are derived from the
original pattern. No cardinality or correlation majorant is assumed. -/
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

/-- The full actual mixed-cell pair count, over all fifth-coordinate
labels and all far gaps, is strictly sublinear. -/
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

/-- Same-height zero-label cells inject into the original frequencies.
The already proved nonzero-label estimate controls all remaining cells. -/
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

#print axioms logarithmicTaylorMixedPairs_split
#print axioms logarithmicTaylorMixedPairs_card_far
#print axioms logarithmicTaylorMixedPairs_card_self

open MeasureTheory
open scoped ENNReal

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

theorem integrable_logarithmicTaylorNuAt_mul (P : ZetaLargeValuePattern) (t u : ℝ) :
    Integrable (fun α => logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α)
      (GafniTao.heathBrownCoefficientMeasure 7) := by
  have hh := integrable_finsetSum (P.indices.product P.indices)
    (fun p _ => integrable_logarithmicTaylorOverlapIndicator P t u p)
  apply hh.congr
  filter_upwards [] with α
  exact (logarithmicTaylorNuAt_mul P t u α).symm

theorem logarithmicTaylorCell_measureReal (P : ZetaLargeValuePattern)
    (hH : 2 ≤ Nat.ceil (P.N^(9/40 : ℝ))) (t : ℝ) (n : ℕ) :
    (GafniTao.heathBrownCoefficientMeasure 7).real
      (logarithmicTaylorCell (Nat.ceil (P.N^(9/40 : ℝ))) t n) =
      64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21 := by
  unfold GafniTao.heathBrownCoefficientMeasure logarithmicTaylorCell
  rw [GafniTao.measureReal_heathBrownCoefficientCell_exact hH]
  norm_num [GafniTao.heathBrownCriticalMoment,div_eq_mul_inv]

/-- The integral of the actual mixed-height multiplicities is bounded
by their proved, literal overlap count times the exact cell volume. -/
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

theorem logarithmicTaylorNu_sq (P : ZetaLargeValuePattern) (W : Finset ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) :
    (logarithmicTaylorNu P W α)^2 =
      ∑ t ∈ W, ∑ u ∈ W, logarithmicTaylorNuAt P t α*logarithmicTaylorNuAt P u α := by
  unfold logarithmicTaylorNu
  rw [pow_two,Finset.sum_mul_sum]

theorem integrable_logarithmicTaylorNu_sq (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    Integrable (fun α => (logarithmicTaylorNu P W α)^2)
      (GafniTao.heathBrownCoefficientMeasure 7) := by
  have hh := integrable_finsetSum W (fun t _ => integrable_finsetSum W
    (fun u _ => integrable_logarithmicTaylorNuAt_mul P t u))
  apply hh.congr
  filter_upwards [] with α
  exact (logarithmicTaylorNu_sq P W α).symm

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

#print axioms integrable_logarithmicTaylorOverlapIndicator
#print axioms logarithmicTaylorNuAt_mul
#print axioms integrable_logarithmicTaylorNuAt_mul
#print axioms logarithmicTaylorCell_measureReal
#print axioms integral_logarithmicTaylorNuAt_mul_le
#print axioms logarithmicTaylorNu_sq
#print axioms integrable_logarithmicTaylorNu_sq
#print axioms integral_logarithmicTaylorNu_sq_le

theorem logarithmicTaylorNu_nonneg (P : ZetaLargeValuePattern) (W : Finset ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 7) : 0 ≤ logarithmicTaylorNu P W α := by
  exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg
    (fun n _ => GafniTao.heathBrownCellIndicator_nonneg 7 _ n (logarithmicTaylorPhase t) α))

theorem integrable_logarithmicTaylorNuAt (P : ZetaLargeValuePattern) (t : ℝ) :
    Integrable (logarithmicTaylorNuAt P t) (GafniTao.heathBrownCoefficientMeasure 7) :=
  integrable_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator 7 _ n _)

theorem integrable_logarithmicTaylorNu (P : ZetaLargeValuePattern) (W : Finset ℝ) :
    Integrable (logarithmicTaylorNu P W) (GafniTao.heathBrownCoefficientMeasure 7) :=
  integrable_finsetSum _ (fun t _ => integrable_logarithmicTaylorNuAt P t)

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

/-- A second-moment bound for the literal joint multiplicity on an
actual separated subset. All individual mixed-pair counts are derived. -/
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

#print axioms logarithmicTaylorNu_nonneg
#print axioms integrable_logarithmicTaylorNuAt
#print axioms integrable_logarithmicTaylorNu
#print axioms integral_logarithmicTaylorNu
#print axioms integral_logarithmicTaylorNu_sq_uniform

/-- Holder is applied to the joint multiplicity, AFTER summing heights.
Its second-moment factor uses the newly proved actual mixed-cell count. -/
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

/-- The separated family is extracted from the actual large-value
ordinates, with the previously proved local occupancy loss. -/
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

/-- Reindex the already proved native translation average onto the
literal positive integer interval, without changing its phase. -/
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

/-- The first Abel step for the original logarithmic phase at an actual
dyadic frequency. Its Taylor-error coefficient is derived, not supplied. -/
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

#print axioms logarithmicTaylorPhase_seventh_norm
#print axioms logarithmicTaylor_shifted_Abel

/-- Entry from the original zeta-pattern large value into the actual
Taylor-centre sums, including the complete translation-boundary error. -/
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

/-- The coefficient-cell Abel inequality summed over the actual
frequencies AND heights, before applying any mean-value inequality. -/
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

/-- Actual joint centre sums are charged to the joint integrated Weyl
sums. Both finite Abel tails and the exact cell volume are retained. -/
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

#print axioms measurable_logarithmicTaylorNu
#print axioms logarithmicTaylor_joint_center_integral

def logarithmicTaylorJointMajorant (P : ZetaLargeValuePattern) (W : Finset ℝ) : ℝ :=
  (GafniTao.fordVinogradovMomentNat 21 6 (Nat.ceil (P.N^(9/40 : ℝ))) : ℝ)^(1/42 : ℝ)*
    ((3*(W.card : ℝ)*P.N+(W.card : ℝ)^2*P.N^(19/20 : ℝ))*
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(1/42 : ℝ)*
    ((W.card : ℝ)*(P.indices.card : ℝ)*
      (64/(Nat.ceil (P.N^(9/40 : ℝ)) : ℝ)^21))^(20/21 : ℝ)

/-- A common bound for every partial centre sum, using actual mixed
height counts. No moment or cardinality estimate is a theorem parameter. -/
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

/-- The original joint large values are bounded by the literal critical
moment and actual mixed-cell count, with every Abel/boundary factor visible. -/
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

/-- The critical VMVT is inserted from the proved native theorem.
This is the resulting actual ordinate inequality, after exact volume
cancellation; it assumes neither a large-value bound nor a moment bound. -/
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

/-- The off-height contribution is absorbed with a strict power saving.
The bound concerns a subset of the original large-value ordinates. -/
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

/-- The owner-frozen research target, via the mixed-height critical
moment argument, with its epsilon--delta scale neighbourhood explicit. -/
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

theorem pintz_second_endpoint_research_exponent {τ : ℝ}
    (hτlo : 37/7 ≤ τ) (hτhi : τ < 340/63) :
    zetaLargeValueExponent (41/42) τ ≤ ((3*τ/170 : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound (pintz_second_endpoint_research_largeValueBound hτlo hτhi)

example : ∀ τ : ℝ, 37/7 ≤ τ → τ < 340/63 →
    zetaLargeValueExponent (41/42) τ ≤ ((3*τ/170 : ℝ) : EReal) :=
  fun _ hτlo hτhi => pintz_second_endpoint_research_exponent hτlo hτhi

#print axioms pintz_second_endpoint_research_largeValueBound
#print axioms pintz_second_endpoint_research_exponent

/-- The frozen second Pintz endpoint, by the new joint-moment argument
and the already proved exact zero-density transfer. This is a research
strengthening, not reproduction of Pintz's strict-boundary theorem. -/
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

example : zeroDensityExponent (41/42) ≤ ((63/85 : ℝ) : EReal) :=
  pintz_second_endpoint_research_density

#print axioms pintz_second_endpoint_research_density

end PintzSignedGramScratch
