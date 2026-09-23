import TaoTrudgianYang2025.HeathBrownPairParameters

/-! Ordered adjacent secants and an actual natural derivative-order choice. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem heathBrownPairSecant_adjacent_identity {r τ : ℝ} (hr : 3 ≤ r) :
    heathBrownPairSecant (r+1) τ-heathBrownPairSecant r τ =
      (heathBrownPairK (r+1)-heathBrownPairK r)*(τ-heathBrownPairRight r) := by
  have hj := heathBrownPairSecant_join hr
  unfold heathBrownPairSecant at hj ⊢
  nlinarith only [hj]

theorem heathBrownPairSecant_next_le {r τ : ℝ} (hr : 3 ≤ r)
    (hτ : heathBrownPairRight r ≤ τ) :
    heathBrownPairSecant (r+1) τ ≤ heathBrownPairSecant r τ := by
  have hd := heathBrownPairSecant_adjacent_identity (τ:=τ) hr
  have hp := heathBrownPairK_antitone hr (show r ≤ r+1 by linarith)
  have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (sub_nonneg.mpr hτ)
  linarith

theorem heathBrownPairSecant_le_next {r τ : ℝ} (hr : 3 ≤ r)
    (hτ : τ ≤ heathBrownPairRight r) :
    heathBrownPairSecant r τ ≤ heathBrownPairSecant (r+1) τ := by
  have hd := heathBrownPairSecant_adjacent_identity (τ:=τ) hr
  have hp := heathBrownPairK_antitone hr (show r ≤ r+1 by linarith)
  have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hp) (sub_nonpos.mpr hτ)
  linarith

theorem heathBrownPairSecant_le_later {j k : ℕ} (hj : 3 ≤ j) (hjk : j ≤ k)
    {τ : ℝ} (hτ : τ ≤ heathBrownPairRight j) :
    heathBrownPairSecant j τ ≤ heathBrownPairSecant k τ := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih =>
    have hi : (3:ℝ) ≤ i := by exact_mod_cast (show 3 ≤ i by omega)
    have hij : (j:ℝ) ≤ i := by exact_mod_cast hji
    have hright := heathBrownPairRight_mono (r:=(j:ℝ)) (s:=(i:ℝ))
      (by exact_mod_cast (show 2 ≤ j by omega)) hij
    have ha := heathBrownPairSecant_le_next hi (hτ.trans hright)
    simpa only [Nat.cast_add,Nat.cast_one] using ih.trans ha

theorem heathBrownPairSecant_le_earlier {k j : ℕ} (hk : 3 ≤ k) (hkj : k ≤ j) :
    ∀ τ : ℝ, heathBrownPairLeft j ≤ τ →
      heathBrownPairSecant j τ ≤ heathBrownPairSecant k τ := by
  induction j, hkj using Nat.le_induction with
  | base => intro τ hτ; exact le_rfl
  | succ i hki ih =>
    intro τ hτ
    have hi : (3:ℝ) ≤ i := by exact_mod_cast (show 3 ≤ i by omega)
    have hleft := heathBrownPairLeft_mono hi (show (i:ℝ) ≤ (i:ℝ)+1 by linarith)
    have hlower : heathBrownPairLeft (i:ℝ) ≤ τ := by
      exact hleft.trans (by simpa only [Nat.cast_add,Nat.cast_one] using hτ)
    have hright : heathBrownPairRight (i:ℝ) ≤ τ := by
      simpa only [Nat.cast_add,Nat.cast_one,heathBrownPairLeft_succ] using hτ
    have ha := heathBrownPairSecant_next_le hi hright
    simpa only [Nat.cast_add,Nat.cast_one] using ha.trans (ih τ hlower)

theorem heathBrownPairSecant_segment_le {j k : ℕ} (hj : 3 ≤ j) (hk : 3 ≤ k)
    {τ : ℝ} (hl : heathBrownPairLeft j ≤ τ) (hr : τ ≤ heathBrownPairRight j) :
    heathBrownPairSecant j τ ≤ heathBrownPairSecant k τ := by
  rcases le_total j k with h | h
  · exact heathBrownPairSecant_le_later hj h hr
  · exact heathBrownPairSecant_le_earlier hk h τ hl

theorem exists_heathBrownPair_segment {τ : ℝ} (hτ : 2 ≤ τ) :
    ∃ j : ℕ, 3 ≤ j ∧ heathBrownPairLeft j ≤ τ ∧ τ ≤ heathBrownPairRight j := by
  have hex : ∃ n : ℕ, τ ≤ heathBrownPairRight ((n+3:ℕ):ℝ) := by
    obtain ⟨n,hn⟩ := exists_nat_ge τ
    refine ⟨n,hn.trans ?_⟩
    have h := heathBrownPairRight_lower
      (r:=((n+3:ℕ):ℝ)) (by norm_num)
    push_cast at h ⊢
    linarith
  let n := Nat.find hex
  have hn : τ ≤ heathBrownPairRight ((n+3:ℕ):ℝ) := Nat.find_spec hex
  refine ⟨n+3,by omega,?_,hn⟩
  cases hcase : n with
  | zero =>
    norm_num [heathBrownPairLeft]
    linarith
  | succ m =>
    have hm : m < Nat.find hex := by change m < n; omega
    have hmin := Nat.find_min hex hm
    have hlt : heathBrownPairRight ((m+3:ℕ):ℝ) < τ := lt_of_not_ge hmin
    have heq : ((m+1+3:ℕ):ℝ) = ((m+3:ℕ):ℝ)+1 := by push_cast; ring
    rw [heq,heathBrownPairLeft_succ]
    exact hlt.le

end TaoTrudgianYang2025
