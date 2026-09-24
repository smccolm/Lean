import TaoTrudgianYang2025.HeathBrownSharpNearRow
import TaoTrudgianYang2025.HeathBrownSharpFarRow

/-!
# The actual finite Heath--Brown dichotomy

Sharp Gram duality, the near-difference estimate, and the proved far
twelfth moment are consumed here. No moment or cardinality bound is assumed.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_heathBrown_sharp_finite_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ P : LargeValuePattern, T₀ ≤ P.T →
      4*P.N*(2+200*Real.sqrt (P.N^(7/5 : ℝ))) ≤ P.V^2 →
      (P.ordinates.card : ℝ)*P.V^2 ≤
        8*P.N*(2*P.N+24*Real.pi*P.N*(harmonic (Nat.ceil (P.N^(7/5 : ℝ))) : ℝ)) ∨
      (P.ordinates.card : ℝ)*P.V^24 ≤ C*P.N^18*P.T^(2+ε) := by
  classical
  obtain ⟨D,T₀,hD,hT₀,hfar⟩ := exists_sharp_gram_far_twelfth hε
  refine ⟨(8 : ℝ)^12*D,T₀,by positivity,hT₀,?_⟩
  intro P hPT hvalue
  let R : ℝ := P.ordinates.card
  let L : ℝ := P.N^(7/5 : ℝ)
  let B : ℝ := 2+200*Real.sqrt L
  let H : ℝ := 2*P.N+24*Real.pi*P.N*(harmonic (Nat.ceil L) : ℝ)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hharm : (0 : ℝ) ≤ harmonic (Nat.ceil L) := by
    exact_mod_cast (Finset.sum_nonneg (fun i _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i+1))) : (0 : ℚ) ≤ harmonic (Nat.ceil L))
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  by_cases hempty : P.ordinates = ∅
  · left
    simpa only [hempty,Finset.card_empty,Nat.cast_zero,zero_mul] using
      (mul_nonneg (by positivity : 0 ≤ 8*P.N) hH0)
  have hne : P.ordinates.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hR : 0 < R := by
    change (0 : ℝ) < P.ordinates.card
    exact_mod_cast hne.card_pos
  obtain ⟨t,ht,hrow⟩ := P.exists_large_sharp_gram_row hne
  let S := {u ∈ P.ordinates | L < |u-t|}
  let F : ℝ := ∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖
  have hL0 : 0 ≤ L := Real.rpow_nonneg hNp.le _
  have hL2 : L ≤ P.N^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      P.one_lt_N.le (by norm_num : (7/5 : ℝ) ≤ 2)
  have hnear := P.sharp_gram_near_row ht hL0 hL2
  have hparts :
      (∑ u ∈ {u ∈ P.ordinates | |u-t| ≤ L},
        ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖)+F =
      ∑ u ∈ P.ordinates, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ := by
    simpa only [not_le,S,F] using Finset.sum_filter_add_sum_filter_not P.ordinates
      (fun u => |u-t| ≤ L) (fun u => ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖)
  have hrow' : R*P.V^2 ≤ 2*P.N*(H+R*B+F) := by
    rw [← hparts] at hrow
    apply hrow.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp [H,R,B]
    linarith
  change 4*P.N*B ≤ P.V^2 at hvalue
  have hvalueR := mul_le_mul_of_nonneg_left hvalue hR0
  by_cases hsmall : R*P.V^2 ≤ 8*P.N*H
  · exact Or.inl hsmall
  right
  have hrowF : R*P.V^2 ≤ 8*P.N*F := by
    nlinarith [lt_of_not_ge hsmall]
  have hsub : S ⊆ {u ∈ P.ordinates | P.N^(11/8 : ℝ) ≤ |u-t|} := by
    intro u hu
    have hh := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨hh.1,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by norm_num : (11/8 : ℝ) ≤ 7/5)).trans hh.2.le
  have hmoment : (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖^12) ≤
      D*P.N^6*P.T^(2+ε) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (hfar P t hPT ht)
  have hScard : (S.card : ℝ) ≤ R := by
    dsimp [S,R]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun u => L < |u-t|) P.ordinates)
  have hholder : F^12 ≤ (S.card : ℝ)^11*
      (∑ u ∈ S, ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖^12) :=
    pow_sum_le_card_mul_sum_pow (s:=S)
    (f:=fun u => ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖)
    (fun _ _ => norm_nonneg _) 11
  have hF : F^12 ≤ R^11*(D*P.N^6*P.T^(2+ε)) := by
    apply hholder.trans
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hScard 11) hmoment
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 12))
      (pow_nonneg hR0 _)
  have hpow := pow_le_pow_left₀ (mul_nonneg hR0 (sq_nonneg _)) hrowF 12
  have hfinal : R^11*(R*P.V^24) ≤
      R^11*(((8 : ℝ)^12*D)*P.N^18*P.T^(2+ε)) := calc
    _ = (R*P.V^2)^12 := by ring
    _ ≤ (8*P.N*F)^12 := hpow
    _ = (8*P.N)^12*F^12 := mul_pow _ _ _
    _ ≤ (8*P.N)^12*(R^11*(D*P.N^6*P.T^(2+ε))) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos hR 11)).mp hfinal

end TaoTrudgianYang2025
