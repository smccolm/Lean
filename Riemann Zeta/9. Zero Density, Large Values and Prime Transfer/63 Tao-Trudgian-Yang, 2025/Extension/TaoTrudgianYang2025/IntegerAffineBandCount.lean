import TaoTrudgianYang2025.IntegerIntervalCount

/-! The actual finite number of displacement/frequency triples in an affine band. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_affine_band_triples_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {D Q B : ℝ}
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hd : ∀ p ∈ S, |(p.1:ℝ)| ≤ 2*D)
    (hq : ∀ p ∈ S, |(p.2.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*(p.1:ℝ)+(p.2.1:ℝ)-(p.2.2:ℝ)| ≤ B) :
    (S.card:ℝ) ≤ (4*D+1)*(4*Q+1)*(2*B+1) := by
  classical
  let X := S.image (fun p => p.1)
  let Y := S.image (fun p => p.2.1)
  let f : ℤ × ℤ × ℤ → ℤ × ℤ := fun p => (p.1,p.2.1)
  have hX : (X.card:ℝ) ≤ 4*D+1 := by
    have hb := integer_card_le_of_abs_sub_le X (a := 0) (by positivity : 0 ≤ 2*D)
      (fun n hn => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        simpa only [sub_zero] using hd p hp)
    nlinarith
  have hY : (Y.card:ℝ) ≤ 4*Q+1 := by
    have hb := integer_card_le_of_abs_sub_le Y (a := 0) (by positivity : 0 ≤ 2*Q)
      (fun n hn => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        simpa only [sub_zero] using hq p hp)
    nlinarith
  have hfiber : ∀ z : ℤ × ℤ, ((S.filter (fun p => f p = z)).card:ℝ) ≤ 2*B+1 := by
    intro z
    let T := S.filter (fun p => f p = z)
    let W := T.image (fun p => p.2.2)
    have hinj : Set.InjOn (fun p : ℤ × ℤ × ℤ => p.2.2) T := by
      intro p hp q hq he
      have hfp := (Finset.mem_filter.mp hp).2
      have hfq := (Finset.mem_filter.mp hq).2
      have hpair : (p.1,p.2.1) = (q.1,q.2.1) := hfp.trans hfq.symm
      exact Prod.ext (congrArg (fun z : ℤ × ℤ => z.1) hpair)
        (Prod.ext (congrArg (fun z : ℤ × ℤ => z.2) hpair) he)
    have hcard : W.card = T.card := Finset.card_image_of_injOn hinj
    have hmem : ∀ n ∈ W, |(n:ℝ)-(2*(z.1:ℝ)+(z.2:ℝ))| ≤ B := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have hpair := (Finset.mem_filter.mp hp).2
      have hp₁ : p.1 = z.1 := congrArg Prod.fst hpair
      have hp₂ : p.2.1 = z.2 := congrArg Prod.snd hpair
      rw [abs_sub_comm,← hp₁,← hp₂]
      exact hband p (Finset.mem_filter.mp hp).1
    have hb := integer_card_le_of_abs_sub_le W hB hmem
    rwa [hcard] at hb
  have hmaps : Set.MapsTo f S ((X ×ˢ Y : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro p hp
    change (p.1,p.2.1) ∈ (X ×ˢ Y : Finset (ℤ × ℤ))
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ X ×ˢ Y, ((S.filter (fun p => f p = z)).card:ℝ) := by
    exact_mod_cast hcard
  calc
    _ = _ := hcardR
    _ ≤ ∑ _z ∈ X ×ˢ Y, (2*B+1) := Finset.sum_le_sum (fun z _ => hfiber z)
    _ = (X.card:ℝ)*(Y.card:ℝ)*(2*B+1) := by
      simp only [Finset.sum_const,Finset.card_product,Nat.cast_mul,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hX hY (by positivity) (by positivity)) (by positivity)

theorem integer_affine_band_triples_card_le_dyadic
    (S : Finset (ℤ × ℤ × ℤ)) {D Q B : ℝ}
    (hD : 1 ≤ D) (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (hd : ∀ p ∈ S, |(p.1:ℝ)| ≤ 2*D)
    (hq : ∀ p ∈ S, |(p.2.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*(p.1:ℝ)+(p.2.1:ℝ)-(p.2.2:ℝ)| ≤ B) :
    (S.card:ℝ) ≤ 25*D*Q*(2*B+1) := by
  have hb := integer_affine_band_triples_card_le S (by linarith) (by linarith) hB hd hq hband
  have hprod : (4*D+1)*(4*Q+1) ≤ (5*D)*(5*Q) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  calc
    _ ≤ (4*D+1)*(4*Q+1)*(2*B+1) := hb
    _ ≤ (5*D)*(5*Q)*(2*B+1) := mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
