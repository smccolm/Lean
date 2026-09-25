import TaoTrudgianYang2025.IntegerIntervalCount

/-! Counting frequency pairs in the actual affine band for one displacement. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_affine_band_pairs_card_le
    (S : Finset (ℤ × ℤ)) {d Q B : ℝ}
    (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hq : ∀ p ∈ S, |(p.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*d+(p.1:ℝ)-(p.2:ℝ)| ≤ B) :
    (S.card:ℝ) ≤ (4*Q+1)*(2*B+1) := by
  classical
  let X := S.image Prod.fst
  have hX : (X.card:ℝ) ≤ 4*Q+1 := by
    have hb := integer_card_le_of_abs_sub_le X (a := 0) (by positivity : 0 ≤ 2*Q)
      (fun n hn => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        simpa only [sub_zero] using hq p hp)
    nlinarith
  have hfiber : ∀ x : ℤ, ((S.filter (fun p => p.1 = x)).card:ℝ) ≤ 2*B+1 := by
    intro x
    let T := S.filter (fun p => p.1 = x)
    let Y := T.image Prod.snd
    have hinj : Set.InjOn (Prod.snd : ℤ × ℤ → ℤ) T := by
      intro p hp q hq he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm) he
    have hcard : Y.card = T.card := Finset.card_image_of_injOn hinj
    have hmem : ∀ n ∈ Y, |(n:ℝ)-(2*d+(x:ℝ))| ≤ B := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      rw [abs_sub_comm,← (Finset.mem_filter.mp hp).2]
      exact hband p (Finset.mem_filter.mp hp).1
    have hb := integer_card_le_of_abs_sub_le Y hB hmem
    rwa [hcard] at hb
  have hmaps : Set.MapsTo (Prod.fst : ℤ × ℤ → ℤ) S X := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcardR : (S.card:ℝ) =
      ∑ x ∈ X, ((S.filter (fun p => p.1 = x)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcardR
    _ ≤ ∑ _x ∈ X, (2*B+1) := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = (X.card:ℝ)*(2*B+1) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hX (by positivity)

theorem integer_fixed_displacement_band_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d : ℤ} {Q B : ℝ}
    (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hd : ∀ p ∈ S, p.1 = d)
    (hq : ∀ p ∈ S, |(p.2.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*(p.1:ℝ)+(p.2.1:ℝ)-(p.2.2:ℝ)| ≤ B) :
    (S.card:ℝ) ≤ (4*Q+1)*(2*B+1) := by
  classical
  have hinj : Set.InjOn (Prod.snd : ℤ × ℤ × ℤ → ℤ × ℤ) S := by
    intro p hp q hq he
    exact Prod.ext ((hd p hp).trans (hd q hq).symm) he
  have hcard := Finset.card_image_of_injOn hinj
  have hb := integer_affine_band_pairs_card_le (S.image Prod.snd)
    (d := (d:ℝ)) hQ hB
    (fun p hp => by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
      exact hq z hz)
    (fun p hp => by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
      rw [← hd z hz]
      exact hband z hz)
  rwa [hcard] at hb

end TaoTrudgianYang2025
