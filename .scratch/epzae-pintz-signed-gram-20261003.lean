import TaoTrudgianYang2025.LiteratureDensity
import TaoTrudgianYang2025.HeathBrownSharpNearRow
import TaoTrudgianYang2025.HeathBrownSharpAsymptotics

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

end PintzSignedGramScratch
