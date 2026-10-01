import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
namespace HuxleyReferenceHullHeightsScratch
private theorem actual_reference_hull_order_bound
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ := by
  obtain ⟨l,hl,u,hu,hlow,hupp⟩ := henclose
  have hup : 0 < u := hscale.trans_le hupp
  have hlneg : l < 0 := hlow.trans_lt (neg_neg_of_pos hscale)
  have hHp : 0 < H := lt_of_lt_of_le (by decide : (0:ℤ)<1) hH
  have hHR : (0:ℝ) < H := by exact_mod_cast hHp
  have hzero : (0:ℝ)∈S := by
    exact_mod_cast hhull l hl u hu 0
      (by simpa only [Rat.den_zero,Int.natCast_one] using hH)
      (by simpa only [Rat.cast_zero] using (show (0:ℝ)∈Icc l u from ⟨hlneg.le,hup.le⟩))
  have huwide : δ/4 < u := by
    simpa only [sub_zero,abs_of_pos hup] using hsep u hu 0 hzero hup.ne'
  by_contra hnot
  have hbig : 4/δ ≤ (H:ℝ) := le_of_not_gt hnot
  have hrecip : (1:ℝ)/H ≤ δ/4 := by
    have hh := (div_le_iff₀ hδ).mp hbig
    apply (div_le_iff₀ hHR).mpr
    nlinarith only [hh]
  have hunit : (1:ℝ)/H∈S := by
    have hq := hhull 0 hzero u hu (Rat.divInt 1 H)
      (Int.le_of_dvd hHp (Rat.den_dvd 1 H))
      (by
        rw [Rat.cast_divInt,Int.cast_one]
        exact ⟨(one_div_pos.mpr hHR).le,hrecip.trans huwide.le⟩)
    simpa only [Rat.cast_divInt,Int.cast_one] using hq
  have hsmall := hsep _ hunit _ hzero (one_div_ne_zero hHR.ne')
  rw [sub_zero,abs_of_pos (one_div_pos.mpr hHR)] at hsmall
  exact (not_lt_of_ge hrecip) hsmall

private theorem actual_reference_hull_label_heights
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ ∧
    ∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
      (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
  have hHbound := actual_reference_hull_order_bound S hH hδ hscale hhull henclose hsep
  refine ⟨hHbound,?_⟩
  have hfinish (z : ℝ) (hz : z∈S) (m n : ℤ)
      (hval : z=(m:ℝ)/n) (hcop : IsCoprime m n) (hn : 0 < n)
      (hnb : (n:ℝ)<4/δ) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
    refine ⟨m,n,hval,hcop,hn,hnb,?_⟩
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hnum : (m:ℝ)=z*(n:ℝ) := (div_eq_iff hnR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hnR]
    exact mul_le_mul (hpoints z hz) hnb.le hnR.le (by linarith only [hscale])
  intro z hz
  rcases hlabels z hz with ⟨q,hval,hqH⟩ | ⟨m,n,u,v,hval,hcop,hn,hv,hu,hdet⟩
  · apply hfinish z hz q.num q.den
    · simpa only [Rat.cast_def,Int.cast_natCast] using hval
    · exact q.isCoprime_num_den
    · exact_mod_cast q.pos
    · exact (show (q.den:ℝ) ≤ H by exact_mod_cast hqH).trans_lt hHbound
  · exact hfinish z hz m n hval hcop hn
      (separated_reference_parent_denominator_bound S hδ hn hv
        (hval ▸ hz) hu hdet hsep).2

example
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ :=
  HuxleyReferenceHullHeightsScratch.actual_reference_hull_order_bound S (H:=H) (δ:=δ) (scale:=scale) hH hδ hscale hhull henclose hsep

example
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ ∧
    ∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
      (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) :=
  HuxleyReferenceHullHeightsScratch.actual_reference_hull_label_heights S (H:=H) (δ:=δ) (scale:=scale) hH hδ hscale hhull henclose hpoints hlabels hsep

#print axioms actual_reference_hull_order_bound
#print axioms actual_reference_hull_label_heights
end HuxleyReferenceHullHeightsScratch
