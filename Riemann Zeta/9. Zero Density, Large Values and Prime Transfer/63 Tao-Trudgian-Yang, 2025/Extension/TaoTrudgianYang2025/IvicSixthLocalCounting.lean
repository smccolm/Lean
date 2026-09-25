import TaoTrudgianYang2025.IvicSixthAbsorption

/-! Actual local-zeta-mean counting from the restricted-sixth exponent pair. -/

noncomputable section
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ivicSixth_card_le_of_local_packets {A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+ivicSixthAbsorptionLength A H Y) →
        (∑ t ∈ U, f t)^2 ≤
          A*((U.card : ℝ)*H/G+(U.card : ℝ)^2*
            ((ivicSixthAbsorptionLength A H Y)^(2/9:ℝ)*H^(7/18:ℝ)))) :
    (W.card : ℝ) ≤
      2*A*H/(G*Y^2)+1024*A^(11/2:ℝ)*H^(15/4:ℝ)/(G*Y^11) := by
  let L := ivicSixthAbsorptionLength A H Y
  have hL : 0 < L := ivicSixthAbsorptionLength_pos hA hH hY
  have hfiber (j : ℕ) :
      ((atkinsonHeightFiber H L W j).card : ℝ) ≤ 2*A*H/(G*Y^2) := by
    have hsub := atkinsonHeightFiber_subset H L W j
    have hlocal := atkinsonHeightFiber_interval j hL (fun t ht => (hrange t ht).1)
    have hp := hpacket (atkinsonHeightFiber H L W j) hsub (H+(j:ℝ)*L) hlocal
    apply atkinson_card_le_of_quadratic_packet hA hH.le hG hY
      (fun t ht => hlarge t (hsub ht)) hp
    convert ivicSixthAbsorptionLength_absorbs (Y := Y) hA hH using 1
    ring
  have hc := atkinson_card_le_of_height_fibers hL
    (fun t ht => (hrange t ht).2) (fun j _ => hfiber j)
  exact hc.trans (ivicSixth_covered_card_budget hA hH hG hY)

theorem ivicSixth_count_exponent_budget {D H G Y ν : ℝ}
    (hD : 0 ≤ D) (hH : 1 ≤ H) (hG : 0 < G) (hY : 0 < Y) (hν : 0 ≤ ν) :
    2*(D*H^(2*ν/11))*H/(G*Y^2)+
        1024*(D*H^(2*ν/11))^(11/2:ℝ)*H^(15/4:ℝ)/(G*Y^11) ≤
      (2*D+1024*D^(11/2:ℝ))*H^ν*
        (H/(G*Y^2)+H^(15/4:ℝ)/(G*Y^11)) := by
  have hH0 : 0 < H := by linarith
  have hp : H^(2*ν/11) ≤ H^ν :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have he : (D*H^(2*ν/11))^(11/2:ℝ) = D^(11/2:ℝ)*H^ν := by
    rw [Real.mul_rpow hD (by positivity),← Real.rpow_mul hH0.le]
    congr 2
    ring
  rw [he]
  calc
    _ ≤ 2*(D*H^ν)*H/(G*Y^2)+
        1024*(D^(11/2:ℝ)*H^ν)*H^(15/4:ℝ)/(G*Y^11) := by
      apply add_le_add _ le_rfl
      gcongr
    _ ≤ _ := by
      have hx : 0 ≤ 2*D*H^ν*(H^(15/4:ℝ)/(G*Y^11)) := by positivity
      have hy : 0 ≤ 1024*D^(11/2:ℝ)*H^ν*(H/(G*Y^2)) := by positivity
      ring_nf at hx hy ⊢
      nlinarith

theorem exists_ivicSixth_localMeanExcess_card_le {δ κ ν : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G Y : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < Y →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧
          G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
        (W.card : ℝ) ≤ D*H^ν*
          (H/(G*Y^2)+H^(15/4:ℝ)/(G*Y^11)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exponentPair_two_ninths_eleven_eighteenths.atkinson_localMean_pair_packet_above_fourthRoot
      hδ hκ (show 0 < 2*ν/11 by linarith)
  norm_num only [show (11/18:ℝ)-2/9 = 7/18 by norm_num,
    show (1:ℝ)+2/9-2*(11/18) = 0 by norm_num,
    Real.rpow_zero,mul_one] at hsource
  refine ⟨C,hC,2*D+1024*D^(11/2:ℝ),by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hsep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(2*ν/11) := by positivity
  have hL := ivicSixthAbsorptionLength_pos hA hH0 hY
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧
        t ≤ A+ivicSixthAbsorptionLength (D*H^(2*ν/11)) H Y) →
        (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
          (D*H^(2*ν/11))*((U.card : ℝ)*H/G+(U.card : ℝ)^2*
            ((ivicSixthAbsorptionLength (D*H^(2*ν/11)) H Y)^(2/9:ℝ)*H^(7/18:ℝ))) := by
    intro U hsub A hlocal
    have hsepU : IsSeparated G U := by
      intro x hx y hy hxy
      exact hsep x (hsub hx) y (hsub hy) hxy
    have hs := hsource H G (ivicSixthAbsorptionLength (D*H^(2*ν/11)) H Y)
      U hH hG hL hsepU (fun t ht => hrange t (hsub ht))
      (atkinson_height_interval_diameter hlocal)
    convert hs using 1
    ring
  have hc := ivicSixth_card_le_of_local_packets hA hH0 hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (ivicSixth_count_exponent_budget hD.le hH1 hG hY hν.le)

end TaoTrudgianYang2025
