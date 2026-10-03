import TaoTrudgianYang2025.IvicSixthGeneralLargeValues
import TaoTrudgianYang2025.IvicSixthGlobalExcess
import TaoTrudgianYang2025.IvicSixthLocalCounting
import TaoTrudgianYang2025.IvicSixthLargeValues
import TaoTrudgianYang2025.PointClusterCounting
import TaoTrudgianYang2025.PointValueRanges
import TaoTrudgianYang2025.PointValueWidth

noncomputable section
open Finset MeasureTheory Filter RiemannZeta.GuthMaynard
open scoped Interval
namespace IvicNineteenthScratch
open TaoTrudgianYang2025

private theorem pair : ExponentPair (2/7) (4/7) := by
  convert exponentPair_half_half.aProcess.aProcess.bProcess using 1 <;> norm_num

private def absorptionLength (A H G Y : ℝ) : ℝ :=
  (Y^2/(4*A*H^(2/7:ℝ)*G^(1/7:ℝ)))^(7/2:ℝ)

private theorem length_pos {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    0 < absorptionLength A H G Y := by
  unfold absorptionLength
  positivity

private theorem length_absorbs {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) :
    2*A*((absorptionLength A H G Y)^(2/7:ℝ)*H^(2/7:ℝ)*G^(1/7:ℝ)) ≤ Y^2 := by
  have hp : 0 ≤ Y^2/(4*A*H^(2/7:ℝ)*G^(1/7:ℝ)) := by positivity
  unfold absorptionLength
  rw [← Real.rpow_mul hp]
  norm_num only [show (7/2:ℝ)*(2/7)=1 by norm_num,Real.rpow_one]
  have he : 2*A*((Y^2/(4*A*H^(2/7:ℝ)*G^(1/7:ℝ)))*H^(2/7:ℝ)*G^(1/7:ℝ)) =
      Y^2/2 := by
    have hHp : H^(2/7:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
    have hGp : G^(1/7:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hG _).ne'
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg Y]

private theorem length_eq {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    absorptionLength A H G Y = Y^7/(128*A^(7/2:ℝ)*H*G^(1/2:ℝ)) := by
  have hc : (4:ℝ)^(7/2:ℝ) = 128 := by
    calc
      _ = ((2:ℝ)^(2:ℝ))^(7/2:ℝ) := by norm_num
      _ = (2:ℝ)^(7:ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ = _ := by norm_num
  unfold absorptionLength
  rw [Real.div_rpow (sq_nonneg Y) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ 4*A*H^(2/7:ℝ)) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ 4*A) (by positivity),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hA.le,hc,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le,
    ← Real.rpow_mul hH.le,← Real.rpow_mul hG.le]
  norm_num

private theorem covered_card_budget {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    ((Nat.floor (H/absorptionLength A H G Y)+1:ℕ):ℝ)*
      (2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+256*A^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) := by
  have hL := length_pos hA hH hG hY
  have hfloor := Nat.floor_le (div_nonneg hH.le hL.le)
  have hc : ((Nat.floor (H/absorptionLength A H G Y)+1:ℕ):ℝ) ≤
      H/absorptionLength A H G Y+1 := by
    push_cast
    linarith
  have ha : A^(9/2:ℝ) = A*A^(7/2:ℝ) := by
    calc
      _ = A^(1+(7/2:ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hA,Real.rpow_one]
  have hg : (G^(1/2:ℝ))^2 = G := by
    rw [← Real.rpow_mul_natCast hG.le]
    norm_num
  have hGc : G^(1/2:ℝ)/G = 1/G^(1/2:ℝ) := by
    apply (div_eq_div_iff hG.ne' (Real.rpow_pos_of_pos hG _).ne').mpr
    nlinarith [hg]
  calc
    _ ≤ (H/absorptionLength A H G Y+1)*(2*A*H/(G*Y^2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2*A*H/(G*Y^2)+256*A^(9/2:ℝ)*H^3/Y^9*(G^(1/2:ℝ)/G) := by
      rw [length_eq hA hH hG hY,ha]
      have hAp : A^(7/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
      have hGp : G^(1/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hG _).ne'
      field_simp
      ring
    _ = _ := by rw [hGc]; ring

private theorem card_le_of_local_packets {A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+absorptionLength A H G Y) →
        (∑ t ∈ U, f t)^2 ≤
          A*((U.card : ℝ)*H/G+(U.card : ℝ)^2*
            ((absorptionLength A H G Y)^(2/7:ℝ)*H^(2/7:ℝ)*G^(1/7:ℝ)))) :
    (W.card : ℝ) ≤
      2*A*H/(G*Y^2)+256*A^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) := by
  let L := absorptionLength A H G Y
  have hL : 0 < L := length_pos hA hH hG hY
  have hfiber (j : ℕ) :
      ((atkinsonHeightFiber H L W j).card : ℝ) ≤ 2*A*H/(G*Y^2) := by
    have hsub := atkinsonHeightFiber_subset H L W j
    have hlocal := atkinsonHeightFiber_interval j hL (fun t ht => (hrange t ht).1)
    have hp := hpacket (atkinsonHeightFiber H L W j) hsub (H+(j:ℝ)*L) hlocal
    exact atkinson_card_le_of_quadratic_packet hA hH.le hG hY
      (fun t ht => hlarge t (hsub ht)) hp (length_absorbs hA hH hG)
  have hc := atkinson_card_le_of_height_fibers hL
    (fun t ht => (hrange t ht).2) (fun j _ => hfiber j)
  exact hc.trans (covered_card_budget hA hH hG hY)

private theorem count_exponent_budget {D H G Y ν : ℝ}
    (hD : 0 ≤ D) (hH : 1 ≤ H) (hG : 0 < G) (hY : 0 < Y) (hν : 0 ≤ ν) :
    2*(D*H^(2*ν/9))*H/(G*Y^2)+
        256*(D*H^(2*ν/9))^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) ≤
      (2*D+256*D^(9/2:ℝ))*H^ν*
        (H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9)) := by
  have hH0 : 0 < H := by linarith
  have hp : H^(2*ν/9) ≤ H^ν :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have he : (D*H^(2*ν/9))^(9/2:ℝ) = D^(9/2:ℝ)*H^ν := by
    rw [Real.mul_rpow hD (by positivity),← Real.rpow_mul hH0.le]
    congr 2
    ring
  rw [he]
  calc
    _ ≤ 2*(D*H^ν)*H/(G*Y^2)+
        256*(D^(9/2:ℝ)*H^ν)*H^3/(G^(1/2:ℝ)*Y^9) := by
      apply add_le_add _ le_rfl
      gcongr
    _ ≤ _ := by
      have hx : 0 ≤ 2*D*H^ν*(H^3/(G^(1/2:ℝ)*Y^9)) := by positivity
      have hy : 0 ≤ 256*D^(9/2:ℝ)*H^ν*(H/(G*Y^2)) := by positivity
      ring_nf at hx hy ⊢
      nlinarith

private theorem localMeanExcess_card_le {δ κ ν : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G Y : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < Y →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧
          G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
        (W.card : ℝ) ≤ D*H^ν*
          (H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    pair.atkinson_localMean_pair_packet_above_fourthRoot
      hδ hκ (show 0 < 2*ν/9 by linarith)
  norm_num only [show (4/7:ℝ)-2/7 = 2/7 by norm_num,
    show (1:ℝ)+2/7-2*(4/7) = 1/7 by norm_num] at hsource
  refine ⟨C,hC,2*D+256*D^(9/2:ℝ),by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hsep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(2*ν/9) := by positivity
  have hL := length_pos hA hH0 hG hY
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧
        t ≤ A+absorptionLength (D*H^(2*ν/9)) H G Y) →
        (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
          (D*H^(2*ν/9))*((U.card : ℝ)*H/G+(U.card : ℝ)^2*
            ((absorptionLength (D*H^(2*ν/9)) H G Y)^(2/7:ℝ)*
              H^(2/7:ℝ)*G^(1/7:ℝ))) := by
    intro U hsub A hlocal
    have hsepU : IsSeparated G U := by
      intro x hx y hy hxy
      exact hsep x (hsub hx) y (hsub hy) hxy
    have hs := hsource H G (absorptionLength (D*H^(2*ν/9)) H G Y)
      U hH hG hL hsepU (fun t ht => hrange t (hsub ht))
      (atkinson_height_interval_diameter hlocal)
    convert hs using 1
    ring
  have hc := card_le_of_local_packets hA hH0 hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (count_exponent_budget hD.le hH1 hG hY hν.le)


private theorem exists_ivicNineteenth_pointCluster_superlevel_count
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^3/(G^(1/2:ℝ)*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^9)) := by
  obtain ⟨P,hP,hentry⟩ := exists_pointCluster_superlevel_entry
  obtain ⟨C,hC,D,hD,H₀,hH₀,hcount⟩ :=
    localMeanExcess_card_le hδ hκ hν
  refine ⟨P,C,D,H₀,hP,hC,hD,hH₀,?_⟩
  intro H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let Y : ℝ := (m:ℝ)*A
  let S : Finset ℕ := pointClusterSuperlevel H G W m
  have hHlarge : 20 ≤ H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hcolor : ∀ e : ℕ,
      ((S.filter (fun n => n%2 = e)).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9)) := by
    intro e
    let U := S.filter (fun n => n%2 = e)
    have hbase : ∀ n ∈ U, n ∈ pointClusterBins H G W := by
      intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hcentersSep := pointClusterCenters_separated (H := H) hG U e
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hcentersRange : ∀ t ∈ pointClusterCenters H G U,
        H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      exact ⟨hc.1,hc.2,hwidth _ hc.1 hc.2⟩
    have hcentersLarge : ∀ t ∈ pointClusterCenters H G U,
        Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t) := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hocc : m ≤ (pointCluster H G W n).card := (Finset.mem_filter.mp hnS).2
      have hlog : Real.log (pointClusterCenter H G n) ≤ Real.log (3*H) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      have herror : C*G*Real.log (pointClusterCenter H G n) ≤ A :=
        (mul_le_mul_of_nonneg_left hlog (by positivity)).trans herr
      apply (atkinsonLocalMeanExcess_threshold_iff hY).mpr
      exact hentry H G V (C*G*Real.log (pointClusterCenter H G n))
        W n m hHlarge hG hGH hV hfit hsep hrange hlarge
        (hbase n hn) hm hocc hVsize herror
    have hb := hcount H G Y (pointClusterCenters H G U)
      hH hG hY hcentersSep hcentersRange hcentersLarge
    simpa only [pointClusterCenters_card hG, U] using hb
  have hcards : (S.card:ℝ) = ((S.filter (fun n => n%2 = 0)).card:ℝ) +
      ((S.filter (fun n => n%2 = 1)).card:ℝ) := by
    exact_mod_cast card_eq_sum_parity_cards S
  change (S.card:ℝ) ≤ 2*D*H^ν*(H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9))
  rw [hcards]
  have h0 := hcolor 0
  have h1 := hcolor 1
  linarith

private theorem ivicNineteenth_occupancy_inverse_power_budget {H G A m : ℝ}
    (hH : 0 ≤ H) (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) :
    H/(G*(m*A)^2)+H^3/(G^(1/2:ℝ)*(m*A)^9) ≤
      (H/(G*A^2)+H^3/(G^(1/2:ℝ)*A^9))/m^2 := by
  have hm0 : 0 < m := by linarith
  have hp : m^2 ≤ m^9 := pow_le_pow_right₀ hm (by omega)
  rw [mul_pow,mul_pow]
  calc
    _ ≤ H/(G*(m^2*A^2))+H^3/(G^(1/2:ℝ)*(m^2*A^9)) := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_left (pow_nonneg hH 3) (by positivity)
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hp (by positivity)) (Real.rpow_nonneg hG.le _)))
    _ = _ := by field_simp

private theorem exists_ivicNineteenth_pointValue_card_le_with_width
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^3/(G^(1/2:ℝ)*(V^2/(16*P*Real.log (3*H)))^9)) := by
  obtain ⟨P,C,D,H₀,hP,hC,hD,hH₀,hcount⟩ :=
    exists_ivicNineteenth_pointCluster_superlevel_count hδ hκ hν
  refine ⟨P,C,4*D,H₀,hP,hC,by positivity,hH₀,?_⟩
  intro H G V W hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let B : ℝ := 2*D*H^ν*(H/(G*A^2)+H^3/(G^(1/2:ℝ)*A^9))
  have hHpos : 0 < H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith [hH₀.trans hH])
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsuper : ∀ m : ℕ, 0 < m →
      (((pointClusterBins H G W).filter
        (fun n => m ≤ (pointCluster H G W n).card)).card:ℝ) ≤ B/(m:ℝ)^2 := by
    intro m hm
    have hc := hcount H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hp := ivicNineteenth_occupancy_inverse_power_budget hHpos.le hG hA hm1
    calc
      _ ≤ 2*D*H^ν*(H/(G*((m:ℝ)*A)^2)+H^3/(G^(1/2:ℝ)*((m:ℝ)*A)^9)) := hc
      _ ≤ 2*D*H^ν*((H/(G*A^2)+H^3/(G^(1/2:ℝ)*A^9))/(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B/(m:ℝ)^2 := by dsimp only [B]; ring
  have hsum := sum_nat_occupancy_le_of_superlevels
    (pointClusterBins H G W) (fun n => (pointCluster H G W n).card) hB hsuper
  have hpartition : (W.card:ℝ) = ∑ n ∈ pointClusterBins H G W,
      ((pointCluster H G W n).card:ℝ) := by
    exact_mod_cast pointCluster_card_partition H G W
  rw [← hpartition] at hsum
  calc
    (W.card:ℝ) ≤ 2*B := hsum
    _ = (4*D)*H^ν*(H/(G*A^2)+H^3/(G^(1/2:ℝ)*A^9)) := by dsimp only [B]; ring

private theorem ivicNineteenth_pointValueWidth_count_identity {P K L V H : ℝ}
    (hP : 0 < P) (hK : 0 < K) (hL : 0 < L) (hV : 0 < V) :
    H/((V^2/(K*L^2))*(V^2/(16*P*L))^2) +
        H^3/((V^2/(K*L^2))^(1/2:ℝ)*(V^2/(16*P*L))^9) =
      K*(16*P)^2*(H*L^4/V^6) + K^(1/2:ℝ)*(16*P)^9*(H^3*L^10/V^19) := by
  have he : (V^2/(K*L^2))^(1/2:ℝ) = V/(K^(1/2:ℝ)*L) := by
    rw [Real.div_rpow (sq_nonneg V) (by positivity),
      Real.mul_rpow hK.le (sq_nonneg L)]
    rw [← Real.rpow_natCast V 2,← Real.rpow_mul hV.le,
      ← Real.rpow_natCast L 2,← Real.rpow_mul hL.le]
    norm_num
  rw [he]
  have hKh : K^(1/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
  field_simp

private theorem exists_ivicNineteenth_pointValue_card_le_source_range
    {δ κ ν : ℝ} (hδ : 0 < δ) (hδUpper : δ ≤ 1/4)
    (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^3*(Real.log (3*H))^10/V^19) := by
  obtain ⟨P,C,D,B,hP,hC,hD,hB,hcount⟩ :=
    exists_ivicNineteenth_pointValue_card_le_with_width hδ hκ hν
  let K : ℝ := 16*P*C+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKsize : 16*P*C ≤ K := by dsimp only [K]; linarith
  have hq : 0 < (1/4:ℝ)+κ := by linarith
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (eventually_pointValue_log_scales (P := P) hK hq)
  let D₁ : ℝ := D*(K*(16*P)^2+K^(1/2:ℝ)*(16*P)^9)
  have hD₁ : 0 < D₁ := by dsimp only [D₁]; positivity
  refine ⟨K,D₁,max B B₁,hK,hD₁,le_max_of_le_left hB,?_⟩
  intro H V W hH hV hLower hUpper hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  obtain ⟨hH20,hL1,hPL,hlogFit⟩ := hB₁ H ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  let L : ℝ := Real.log (3*H)
  let G : ℝ := V^2/(K*L^2)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hDen : 0 < K*L^2 := by positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hGlo : (2*H)^(1/4+κ) ≤ G := by
    dsimp only [G]
    exact (le_div_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hLower)
  have hGhi : G ≤ H^(1/2-δ) := by
    dsimp only [G]
    exact (div_le_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hUpper)
  have hGH : G ≤ H := by
    calc
      G ≤ H^(1/2-δ) := hGhi
      _ ≤ H^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H := Real.rpow_one H
  have hfit : 2*(Real.log (3*H))^2 ≤ G :=
    hlogFit.trans ((Real.rpow_le_rpow hH0.le (by linarith) hq.le).trans hGlo)
  have hwidth : ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
    intro t htlo hthi
    have ht0 : 0 ≤ t := hH0.le.trans htlo
    refine ⟨?_,?_,?_⟩
    · calc
        t^δ ≤ (2*H)^δ := Real.rpow_le_rpow ht0 hthi hδ.le
        _ ≤ (2*H)^(1/4+κ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ G := hGlo
    · exact hGhi.trans (Real.rpow_le_rpow hH0.le htlo (by linarith))
    · exact (Real.rpow_le_rpow ht0 hthi hq.le).trans hGlo
  have hOnePow : 1 ≤ (2*H)^(1/4+κ) :=
    Real.one_le_rpow (by linarith) hq.le
  have hLowerSimple : K*L^2 ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_left hOnePow hDen.le
    have hLower' : K*L^2*(2*H)^(1/4+κ) ≤ V^2 := hLower
    nlinarith
  have hVsize : 2*P*Real.log (3*H) ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_right hPL hL.le
    change 2*P*L ≤ V^2
    change 2*P*L ≤ K*L*L at hm
    nlinarith
  have herr : C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) :=
    pointValueWidth_error_absorption hP hK hL hKsize
  have hc := hcount H G V W hHB hG hGH hV hfit hwidth hVsize herr
    hsep hrange hlarge
  have he := ivicNineteenth_pointValueWidth_count_identity (K := K) (H := H) hP hK hL hV
  change H/(G*(V^2/(16*P*L))^2)+H^3/(G^(1/2:ℝ)*(V^2/(16*P*L))^9) = _ at he
  change (W.card:ℝ) ≤ D*H^ν*(H/(G*(V^2/(16*P*L))^2)+H^3/(G^(1/2:ℝ)*(V^2/(16*P*L))^9)) at hc
  rw [he] at hc
  have hx : 0 ≤ H*L^4/V^6 := by positivity
  have hy : 0 ≤ H^3*L^10/V^19 := by positivity
  have hkx : 0 ≤ K*(16*P)^2 := by positivity
  have hky : 0 ≤ K^(1/2:ℝ)*(16*P)^9 := by positivity
  calc
    (W.card:ℝ) ≤ D*H^ν*
        (K*(16*P)^2*(H*L^4/V^6)+K^(1/2:ℝ)*(16*P)^9*(H^3*L^10/V^19)) := hc
    _ ≤ D*H^ν*((K*(16*P)^2+K^(1/2:ℝ)*(16*P)^9)*
        (H*L^4/V^6+H^3*L^10/V^19)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hkx hy,mul_nonneg hky hx]
    _ = D₁*H^ν*(H*(Real.log (3*H))^4/V^6+H^3*(Real.log (3*H))^10/V^19) := by
      dsimp only [D₁,L]
      ring

private theorem exists_ivicNineteenth_pointValue_card_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card : ℝ) ≤ H^ε*(H/V^6+H^3/V^19) := by
  classical
  let η : ℝ := min (ε/4) (1/1000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηUpper : η ≤ 1/48 := (min_le_right _ _).trans (by norm_num)
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_ivicNineteenth_pointValue_card_le_source_range
      (δ := (1/48:ℝ)) (κ := η) (ν := η)
      (by norm_num) (by norm_num) hη hη
  obtain ⟨B₁,hB₁,hGrowth⟩ := exists_zetaMomentCriticalNorm_lt_sixth_power hη
  have hlower := eventually_pointValue_source_lower_range hK hη
  have hupper := eventually_pointValue_sixth_power_source_range hK hη hηUpper
  have hl4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := η) (b := ε) hD.le 4 hηε
  have hl10 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := η) (b := ε) hD.le 10 hηε
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (hlower.and (hupper.and (hl4.and hl10)))
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H V W hH hV hVlower hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith [hB.trans hHB]
  have hH1 : 1 ≤ H := by linarith [hB₁.trans hHB₁]
  obtain ⟨hl,hu,hl4,hl10⟩ := hB₂ H hHB₂
  rcases W.eq_empty_or_nonempty with rfl | ⟨t,ht⟩
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hVgrowth : V ≤ H^(1/6+η) :=
    (hlarge t ht).trans (hGrowth H t hHB₁ (hrange t ht).1 (hrange t ht).2).le
  have hVl : H^(1/8+η) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hVlower
  have hVsq := pow_le_pow_left₀ (by positivity : 0 ≤ H^(1/8+η)) hVl 2
  have hVupper := pow_le_pow_left₀ hV.le hVgrowth 2
  have hc := hcount H V W hHB hV (hl.trans hVsq) (hVupper.trans hu.2)
    hsep hrange hlarge
  calc
    _ ≤ D*H^η*(H*(Real.log (3*H))^4/V^6+
        H^3*(Real.log (3*H))^10/V^19) := hc
    _ = (D*(Real.log (3*H))^4*H^η)*(H/V^6)+
        (D*(Real.log (3*H))^10*H^η)*(H^3/V^19) := by ring
    _ ≤ H^ε*(H/V^6)+H^ε*(H^3/V^19) :=
      add_le_add (mul_le_mul_of_nonneg_right hl4 (by positivity))
        (mul_le_mul_of_nonneg_right hl10 (by positivity))
    _ = _ := by ring


private theorem volume_peak_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H V : ℝ,
      B ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      volume (pointValueSuperlevel H V) ≤
        ENNReal.ofReal (2*H^ε*(H/V^6+H^3/V^19)) := by
  obtain ⟨B,hB,hcount⟩ := exists_ivicNineteenth_pointValue_card_le hε
  refine ⟨B,hB,?_⟩
  intro H V hH hV hLower
  have hc : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      IsSeparated 1 W → (W.card:ℝ) ≤ H^ε*(H/V^6+H^3/V^19) := by
    intro W hWS hsep
    exact hcount H V W hH hV hLower hsep
      (fun t ht => ⟨(hWS t ht).1,(hWS t ht).2.1⟩)
      (fun t ht => (hWS t ht).2.2)
  convert volume_le_two_mul_of_separated_card_bound hc using 1
  congr 1
  ring

private theorem variable_restricted_sixth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H U : ℝ, B ≤ H → H^(1/8+ε) ≤ U →
      (∫ t in pointValueSuperlevel H U, zetaMomentCriticalNorm t^6) ≤
        H^ε*(H+H^3/U^13) := by
  let η : ℝ := ε/4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by dsimp [η]; linarith
  obtain ⟨A,hA,hcount⟩ := volume_peak_bound hη
  obtain ⟨D,hD,hGrowth⟩ := exists_ivicSixth_power_le_height_cube
  have hlog : ∀ᶠ H : ℝ in atTop, 2*H^η*(1+3*Real.log H) ≤ H^ε := by
    simpa only [show 1+(η-1)=η by ring,show 1+(ε-1)=ε by ring] using
      (eventually_ivicSixth_high_log_budget (η := η-1) (ε := ε-1) (by linarith))
  obtain ⟨B,hB⟩ := eventually_atTop.mp hlog
  refine ⟨max A (max D B),hA.trans (le_max_left _ _),?_⟩
  intro H U hH hU
  have hAH : A ≤ H := (le_max_left _ _).trans hH
  have hDH : D ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hBH : B ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hU0 : 0 < U := (Real.rpow_pos_of_pos hH0 _).trans_le hU
  have hU1 : 1 ≤ U := (Real.one_le_rpow hH1 (by linarith : 0 ≤ 1/8+ε)).trans hU
  have hVLower : H^(1/8+η) ≤ U :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hU
  by_cases hUM : U^6 ≤ H^3
  · have hvol : ∀ V : ℝ, U ≤ V →
        volume (pointValueSuperlevel H V) ≤
          ENNReal.ofReal ((2*H^η*(H+H^3/U^13))/V^6) := by
      intro V hUV
      have hV0 : 0 < V := hU0.trans_le hUV
      apply (hcount H V hAH hV0 (hVLower.trans hUV)).trans
      apply ENNReal.ofReal_le_ofReal
      have hpower : U^13 ≤ V^13 := pow_le_pow_left₀ hU0.le hUV 13
      have hquot : H^3/V^13 ≤ H^3/U^13 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpower
      calc
        _ = (2*H^η*(H+H^3/V^13))/V^6 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hquot) (by positivity))
          (by positivity)
    have hi := ivicSixth_high_integral_le_log hU0 hUM
      (by positivity : 0 ≤ 2*H^η*(H+H^3/U^13))
      (fun t ht => hGrowth H t hDH ht.1 ht.2.1) hvol
    have hl := log_height_cube_div_le hH1 (one_le_pow₀ hU1 : 1 ≤ U^6)
    calc
      _ ≤ (2*H^η*(H+H^3/U^13))*(1+Real.log (H^3/U^6)) := hi
      _ ≤ (2*H^η*(H+H^3/U^13))*(1+3*Real.log H) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2*H^η*(1+3*Real.log H))*(H+H^3/U^13) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB H hBH) (by positivity)
  · have hS : pointValueSuperlevel H U = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hp := pow_le_pow_left₀ hU0.le ht.2.2 6
      exact hUM (hp.trans (hGrowth H t hDH ht.1 ht.2.1))
    rw [hS]
    simp only [MeasureTheory.setIntegral_empty]
    positivity

private theorem variable_excess_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H U : ℝ, B ≤ H → H^(1/8+ε) ≤ U →
      (∫ t in H..2*H, ivicSixthExcess U t^6) ≤ H^ε*(H+H^3/U^13) := by
  obtain ⟨B,hB,hbound⟩ := variable_restricted_sixth_moment hε
  refine ⟨B,hB,?_⟩
  intro H U hH hU
  have hH0 : 0 ≤ H := by linarith
  have hU0 : 0 ≤ U := (Real.rpow_nonneg hH0 _).trans hU
  exact (ivicSixthExcess_dyadic_integral_le hH0 hU0 le_rfl).trans (hbound H U hH hU)

private theorem variable_excess_source {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 40000 ≤ B ∧ ∀ T U : ℝ,
      B ≤ T → (4*T)^(1/8+ε) ≤ U →
      (∫ t in T/2..3*T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) := by
  obtain ⟨A,hA,hbound⟩ := variable_excess_dyadic hε
  refine ⟨24*(2:ℝ)^ε,by positivity,2*A,by linarith,?_⟩
  intro T U hT hU
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := (Real.rpow_pos_of_pos (by positivity : 0 < 4*T) _).trans_le hU
  have hb (H : ℝ) (hAH : A ≤ H) (hHT : H ≤ 2*T) :
      (∫ t in H..2*H, ivicSixthExcess U t^6) ≤
        8*(2:ℝ)^ε*T^ε*(T+T^3/U^13) := by
    have hH0 : 0 < H := by linarith
    have hUH : H^(1/8+ε) ≤ U :=
      (Real.rpow_le_rpow hH0.le (by linarith : H ≤ 4*T) (by linarith)).trans hU
    apply (hbound H U hAH hUH).trans
    have hs : H+H^3/U^13 ≤ 8*(T+T^3/U^13) := by
      have hp := pow_le_pow_left₀ hH0.le hHT 3
      have hq := div_le_div_of_nonneg_right hp (by positivity : 0 ≤ U^13)
      calc
        _ ≤ 2*T+(2*T)^3/U^13 := add_le_add hHT hq
        _ ≤ _ := by
          have hq0 : 0 ≤ T^3/U^13 := by positivity
          ring_nf
          linarith
    have hm := mul_le_mul (Real.rpow_le_rpow hH0.le hHT hε.le) hs
      (by positivity : 0 ≤ H+H^3/U^13) (by positivity)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hT0.le] at hm
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
  have hh := hb (T/2) (by linarith) (by linarith)
  have hm := hb T (by linarith) (by linarith)
  have hl := hb (2*T) (by linarith) le_rfl
  rw [show 2*(T/2)=T by ring] at hh
  rw [show 2*(2*T)=4*T by ring] at hl
  have hs := ivicSixthExcess_source_le_three U hT0
  linarith


private theorem variable_excess_source_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ U : ℝ, (4*T)^(1/8+ε) ≤ U →
      zetaMomentLogLoss T^6*(∫ t in T/2..3*T, ivicSixthExcess U t^6) ≤
        T^(3*ε)*(T+T^3/U^13) := by
  obtain ⟨C,hC,A,hA,hsource⟩ := variable_excess_source hε
  have hlog : ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T^6 ≤ T^ε := by
    simpa only [Real.rpow_ofNat] using
      eventually_zetaMomentLogLoss_rpow_le_rpow (by norm_num : (0:ℝ) ≤ 6) hε
  have hconst := (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)
  filter_upwards [hlog,hconst,eventually_ge_atTop A] with T hl hc hT
  intro U hU
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := (Real.rpow_pos_of_pos (by positivity : 0 < 4*T) _).trans_le hU
  calc
    _ ≤ zetaMomentLogLoss T^6*(C*T^ε*(T+T^3/U^13)) :=
      mul_le_mul_of_nonneg_left (hsource T U hT hU) (by positivity)
    _ ≤ T^ε*(T^ε*T^ε*(T+T^3/U^13)) :=
      mul_le_mul hl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
          (by positivity)) (by positivity) (by positivity)
    _ = _ := by
      rw [show 3*ε=ε+(ε+ε) by ring,Real.rpow_add hT0,Real.rpow_add hT0]
      ring



private theorem zeta_loss_parameters {σ τ ε : ℝ}
    (hτ : 1 < τ) (hgap : τ/8 < σ-1/2) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ min (1/4) ((τ-1)/4) ∧
      (τ+θ)*(θ/(τ+1)) ≤ θ ∧
      θ+(τ+θ)*(1/8+θ/(τ+1)) ≤ σ-1/2-4*θ ∧
      3+(τ+θ)*(1+3*(θ/(τ+1))) ≤
        (max (τ+3-6*σ) (3*τ+19/2-19*σ)+ε)+6*(σ-θ) ∧
      3+(τ+θ)*(3+3*(θ/(τ+1)))-13*(σ-1/2-4*θ) ≤
        (max (τ+3-6*σ) (3*τ+19/2-19*σ)+ε)+6*(σ-θ) := by
  let g := σ-1/2-τ/8
  let θ := min (min (1/4) ((τ-1)/4)) (min (g/16) (ε/128))
  have hg : 0 < g := by dsimp [g]; linarith
  have hθ : 0 < θ :=
    lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by positivity) (by positivity))
  have hθs : θ ≤ min (1/4) ((τ-1)/4) := min_le_left _ _
  have hθ1 : θ ≤ 1 := (hθs.trans (min_le_left _ _)).trans (by norm_num)
  have hθg : θ ≤ g/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hθε : θ ≤ ε/128 := (min_le_right _ _).trans (min_le_right _ _)
  let ν := θ/(τ+1)
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hντ : ν*(τ+1)=θ := by dsimp [ν]; field_simp
  have hwin : (τ+θ)*ν ≤ θ := by nlinarith
  refine ⟨θ,hθ,hθs,hwin,?_,?_,?_⟩
  · dsimp [g] at hθg
    change θ+(τ+θ)*(1/8+ν) ≤ σ-1/2-4*θ
    nlinarith
  · change 3+(τ+θ)*(1+3*ν) ≤ _
    nlinarith [le_max_left (τ+3-6*σ) (3*τ+19/2-19*σ)]
  · change 3+(τ+θ)*(3+3*ν)-13*(σ-1/2-4*θ) ≤ _
    nlinarith [le_max_right (τ+3-6*σ) (3*τ+19/2-19*σ)]



private theorem zeta_largeValueBound {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hgap : τ/8 < σ-1/2) :
    IsZetaLargeValueBound σ τ (max (τ+3-6*σ) (3*τ+19/2-19*σ)) := by
  intro ε hε
  obtain ⟨θ,hθ,hθsmall,hwin,hgap',hexp1,hexp2⟩ := zeta_loss_parameters hτ hgap hε
  let ν : ℝ := θ/(τ+1)
  let u : ℝ := σ-1/2-4*θ
  let ρ : ℝ := max (τ+3-6*σ) (3*τ+19/2-19*σ)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hheight : 1 ≤ τ-θ := by
    have hh := hθsmall.trans (min_le_right _ _)
    linarith
  let C : ℝ := zetaLinePerronConstant (1/2)
  have hC : 0 < C := zetaLinePerronConstant_pos _
  have hl : ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T ≤ T^ν := by
    simpa only [Real.rpow_one] using
      eventually_zetaMomentLogLoss_rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hν
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hl.and (variable_excess_source_log hν))
  have hc := (tendsto_rpow_atTop hθ).eventually (eventually_ge_atTop (2*C))
  have hfour := (tendsto_rpow_atTop hθ).eventually
    (eventually_ge_atTop ((4:ℝ)^(1/8+ν)))
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hc.and hfour)
  obtain ⟨D,hD,hEntry⟩ := exists_zetaLinePerron_aboveOne_uniform_threshold
    (by norm_num : (1/2:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) hτ
  let K : ℝ := max 1 (max A (max B (max D (2*(2*C)^6))))
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : A ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : B ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hKD : D ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hKC : 2*(2*C)^6 ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨K,hK,θ,hθ,?_⟩
  intro P hPN hTl hTu hVl _
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT : 0 < P.T := P.T_pos
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTl
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hheight
  obtain ⟨hlog,hmoment⟩ := hA P.T ((hKA.trans hPN).trans hNT)
  obtain ⟨hc,hfour⟩ := hB P.N (hKB.trans hPN)
  have hTp (a : ℝ) (ha : 0 ≤ a) : P.T^a ≤ P.N^((τ+θ)*a) := by
    have hh := Real.rpow_le_rpow hT.le hTu ha
    rwa [← Real.rpow_mul hN.le] at hh
  have hU : (4*P.T)^(1/8+ν) ≤ P.N^u := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hT.le]
    calc
      _ ≤ P.N^θ*P.N^((τ+θ)*(1/8+ν)) :=
        mul_le_mul hfour (hTp _ (by linarith)) (by positivity) (by positivity)
      _ = P.N^(θ+(τ+θ)*(1/8+ν)) := (Real.rpow_add hN _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hgap'
  have hlogN : zetaMomentLogLoss P.T ≤ P.N^θ :=
    hlog.trans ((hTp ν hν.le).trans
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hwin))
  have hsmall : 2*(C*P.N^(1/2:ℝ))*P.N^u*zetaMomentLogLoss P.T ≤ P.V := by
    calc
      _ = (2*C)*(P.N^(1/2:ℝ)*P.N^u)*zetaMomentLogLoss P.T := by ring
      _ ≤ P.N^θ*(P.N^(1/2:ℝ)*P.N^u)*P.N^θ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hlogN
          (zetaMomentLogLoss_pos _).le (by positivity)
      _ = P.N^(σ-2*θ) := by
        rw [← Real.rpow_add hN,← Real.rpow_add hN,← Real.rpow_add hN]
        congr 1
        dsimp [u]
        ring
      _ ≤ P.N^(σ-θ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
      _ ≤ _ := hVl
  have hentry : ∀ t ∈ P.ordinates, P.V ≤ C*P.N^(1/2:ℝ)*zetaMomentConvolution P.T t :=
    hEntry P (hKD.trans hPN) σ θ hσ hθsmall hTl hVl
  have hp := P.ivicSixth_truncated_cardinality hC (by positivity : 0 ≤ P.N^u)
    hentry hsmall
  have hphysical : (P.ordinates.card:ℝ)*P.V^6 ≤
      (2*C)^6*(P.N^3*P.T^(1+3*ν)+P.N^3*P.T^(3+3*ν)/(P.N^u)^13) := by
    calc
      _ ≤ (2*C)^6*P.N^3*(zetaMomentLogLoss P.T^6*
          ∫ t in P.T/2..3*P.T, ivicSixthExcess (P.N^u) t^6) := by
        simpa only [mul_assoc] using hp
      _ ≤ (2*C)^6*P.N^3*(P.T^(3*ν)*(P.T+P.T^3/(P.N^u)^13)) :=
        mul_le_mul_of_nonneg_left (hmoment _ hU) (by positivity)
      _ = _ := by
        rw [Real.rpow_add hT,Real.rpow_add hT,Real.rpow_one,Real.rpow_ofNat]
        ring
  have hfirst : P.N^3*P.T^(1+3*ν) ≤ P.N^((ρ+ε)+6*(σ-θ)) := by
    calc
      _ ≤ P.N^3*P.N^((τ+θ)*(1+3*ν)) :=
        mul_le_mul_of_nonneg_left (hTp _ (by linarith)) (by positivity)
      _ = P.N^(3+(τ+θ)*(1+3*ν)) := by
        rw [← Real.rpow_ofNat,← Real.rpow_add hN]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hexp1
  have hsecond : P.N^3*P.T^(3+3*ν)/(P.N^u)^13 ≤
      P.N^((ρ+ε)+6*(σ-θ)) := by
    calc
      _ ≤ (P.N^3*P.N^((τ+θ)*(3+3*ν)))/(P.N^u)^13 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hTp _ (by linarith)) (by positivity))
          (by positivity)
      _ = P.N^(3+(τ+θ)*(3+3*ν)-13*u) := by
        rw [← Real.rpow_ofNat,← Real.rpow_add hN,← Real.rpow_mul_natCast hN.le,
          ← Real.rpow_sub hN]
        norm_num only [Nat.cast_ofNat]
        rw [mul_comm u]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hexp2
  have hVp : P.N^(6*(σ-θ)) ≤ P.V^6 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hVl 6
    rw [← Real.rpow_mul_natCast hN.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_comm] using hh
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN (6*(σ-θ)))).mp
  calc
    _ ≤ (P.ordinates.card:ℝ)*P.V^6 :=
      mul_le_mul_of_nonneg_left hVp (Nat.cast_nonneg _)
    _ ≤ (2*C)^6*(P.N^3*P.T^(1+3*ν)+P.N^3*P.T^(3+3*ν)/(P.N^u)^13) := hphysical
    _ ≤ (2*C)^6*(P.N^((ρ+ε)+6*(σ-θ))+P.N^((ρ+ε)+6*(σ-θ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by positivity)
    _ = (2*(2*C)^6)*P.N^((ρ+ε)+6*(σ-θ)) := by ring
    _ ≤ K*P.N^((ρ+ε)+6*(σ-θ)) :=
      mul_le_mul_of_nonneg_right hKC (by positivity)
    _ = _ := by rw [Real.rpow_add hN,mul_assoc]


private theorem variable_excess_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (4*T)^(1/8+ε) ≤ U →
      (∫ t in 0..T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) := by
  obtain ⟨B,hB,hdyad⟩ := variable_excess_dyadic hε
  let A : ℝ := |∫ t in 0..B, zetaMomentCriticalNorm t^6|+2
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg (∫ t in 0..B, zetaMomentCriticalNorm t^6)]
  have hBp : 0 < B := by linarith
  refine ⟨A*8*(2:ℝ)^ε,B,by positivity,hB,?_⟩
  intro T U hT hU
  have hTp : 0 < T := hBp.trans_le hT
  have hUp : 0 < U := (Real.rpow_pos_of_pos (by positivity : 0 < 4*T) _).trans_le hU
  let F : ℝ → ℝ := fun X => X^ε*(X+X^3/U^13)
  have hF0 {X : ℝ} (hX : 0 ≤ X) : 0 ≤ F X := by dsimp [F]; positivity
  have hFmono {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) : F X ≤ F Y := by
    apply mul_le_mul (Real.rpow_le_rpow hX hXY hε.le)
      (add_le_add hXY (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hX hXY 3) (by positivity))) (by positivity)
    exact Real.rpow_nonneg (hX.trans hXY) _
  have hFdouble {X : ℝ} (hX : 0 ≤ X) : 2*F X ≤ F (2*X) := by
    have hb : 2*(X+X^3/U^13) ≤ 2*X+(2*X)^3/U^13 := by
      have hq : 0 ≤ X^3/U^13 := by positivity
      ring_nf at hq ⊢
      nlinarith
    have hm := mul_le_mul (Real.rpow_le_rpow hX (by linarith : X ≤ 2*X) hε.le)
      hb (by positivity : 0 ≤ 2*(X+X^3/U^13)) (by positivity)
    simpa only [F,mul_assoc,mul_comm,mul_left_comm] using hm
  have hf := (continuous_ivicSixthExcess U).pow 6
  have hstep : ∀ m : ℕ, (2:ℝ)^m*B ≤ 2*T →
      (∫ t in 0..(2:ℝ)^m*B, ivicSixthExcess U t^6) ≤ A*F ((2:ℝ)^m*B) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [pow_zero,one_mul]
      have hnorm : (∫ t in 0..B, ivicSixthExcess U t^6) ≤
          ∫ t in 0..B, zetaMomentCriticalNorm t^6 := by
        apply intervalIntegral.integral_mono_on hBp.le (hf.intervalIntegrable _ _)
          ((continuous_zetaMomentCriticalNorm.pow 6).intervalIntegrable _ _)
        intro t _
        exact pow_le_pow_left₀ (ivicSixthExcess_nonneg _ _) (ivicSixthExcess_le_norm hUp.le _) 6
      have hBF : 1 ≤ F B := by
        have hp := Real.one_le_rpow (by linarith : 1 ≤ B) hε.le
        have hq : 0 ≤ B^3/U^13 := by positivity
        dsimp [F]
        nlinarith
      calc
        _ ≤ ∫ t in 0..B, zetaMomentCriticalNorm t^6 := hnorm
        _ ≤ |∫ t in 0..B, zetaMomentCriticalNorm t^6| := le_abs_self _
        _ ≤ A := by dsimp [A]; linarith
        _ ≤ A*F B := by nlinarith
    | succ m ih =>
      intro hterminal
      have hX : 0 ≤ (2:ℝ)^m*B := by positivity
      have hBX : B ≤ (2:ℝ)^m*B := by
        have hp : 1 ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
        nlinarith
      have heq : (2:ℝ)^(m+1)*B = 2*((2:ℝ)^m*B) := by rw [pow_succ']; ring
      rw [heq] at hterminal ⊢
      have hXT : (2:ℝ)^m*B ≤ 2*T := by linarith
      have hUX : ((2:ℝ)^m*B)^(1/8+ε) ≤ U :=
        (Real.rpow_le_rpow hX (by linarith : (2:ℝ)^m*B ≤ 4*T) (by linarith)).trans hU
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 ((2:ℝ)^m*B))
        (hf.intervalIntegrable ((2:ℝ)^m*B) (2*((2:ℝ)^m*B)))]
      calc
        _ ≤ A*F ((2:ℝ)^m*B)+F ((2:ℝ)^m*B) :=
          add_le_add (ih hXT) (hdyad _ _ hBX hUX)
        _ ≤ A*(2*F ((2:ℝ)^m*B)) := by
          have hp := hF0 hX
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (hFdouble hX) (by positivity)
  obtain ⟨m,hlo,hhi⟩ := exists_dyadic_cutoff
    ((le_div_iff₀ hBp).mpr (by simpa using hT))
  have hlo' : T ≤ (2:ℝ)^m*B := (div_le_iff₀ hBp).mp hlo
  have hhi' : (2:ℝ)^m*B ≤ 2*T := by
    have hh := (mul_le_mul_iff_left₀ hBp).mpr hhi
    field_simp at hh
    nlinarith
  have hFscale : F (2*T) ≤ 8*(2:ℝ)^ε*F T := by
    dsimp [F]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hTp.le]
    have hb : 2*T+(2*T)^3/U^13 ≤ 8*(T+T^3/U^13) := by
      ring_nf
      linarith
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2:ℝ)^ε*T^ε)
    convert hm using 1
    ring
  calc
    _ ≤ ∫ t in 0..(2:ℝ)^m*B, ivicSixthExcess U t^6 := by
      apply intervalIntegral.integral_mono_interval le_rfl hTp.le hlo'
      · exact Filter.Eventually.of_forall (fun _ => by positivity)
      · exact hf.intervalIntegrable _ _
    _ ≤ A*F ((2:ℝ)^m*B) := hstep m hhi'
    _ ≤ A*F (2*T) := mul_le_mul_of_nonneg_left (hFmono (by positivity) hhi') (by positivity)
    _ ≤ A*(8*(2:ℝ)^ε*F T) := mul_le_mul_of_nonneg_left hFscale (by positivity)
    _ = _ := by dsimp [F]; ring

private theorem variable_excess_symmetric {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (4*T)^(1/8+ε) ≤ U →
      (∫ t in -T..T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) := by
  obtain ⟨C,B,hC,hB,hzero⟩ := variable_excess_zero hε
  refine ⟨2*C,B,by positivity,hB,?_⟩
  intro T U hT hU
  have hi := (continuous_ivicSixthExcess U).pow 6
  have heven : (∫ t in -T..0, ivicSixthExcess U t^6) =
      ∫ t in 0..T, ivicSixthExcess U t^6 := by
    have hs := intervalIntegral.integral_comp_neg (fun t => ivicSixthExcess U t^6)
      (a := (0:ℝ)) (b := T)
    simpa only [ivicSixthExcess_neg,neg_zero] using hs.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (-T) 0)
    (hi.intervalIntegrable 0 T),heven]
  have hz := hzero T U hT hU
  nlinarith


private theorem variable_physical_pattern {η : ℝ} (hη : 0 < η)
    {q : ℕ} (hq : 0 < q) :
    ∃ C D T₀ : ℝ, 0 < C ∧ 0 < D ∧ 40000 ≤ T₀ ∧
      ∀ P : LargeValuePattern, T₀ ≤ P.T → ∀ H U : ℝ,
      0 ≤ H → H ≤ P.T → (8*P.T)^(1/8+η) ≤ U →
      4*C*P.N*Real.sqrt P.N*(2*H*U+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ D*P.N^2 ∨
      (P.ordinates.card:ℝ)*P.V^12 ≤
        D*P.N^9*(2*H)^5*(2*H+1)*P.T^η*(P.T+P.T^3/U^13) := by
  obtain ⟨C,hC,hcard⟩ := exists_ivicSixth_gram_cardinality hq
  obtain ⟨A,B,hA,hB,hmoment⟩ := variable_excess_symmetric hη
  let D : ℝ := max (32*C) ((8*C)^6*A*8*(2:ℝ)^η)
  have hD : 0 < D := lt_of_lt_of_le (by positivity : 0 < 32*C) (le_max_left _ _)
  refine ⟨C,D,B,hC,hD,hB,?_⟩
  intro P hT H U hH hHT hU hsmall
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hUp : 0 < U := (Real.rpow_pos_of_pos (by positivity : 0 < 8*P.T) _).trans_le hU
  rcases hcard P H U hH hsmall with hd | hm
  · left
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  right
  have hthreshold : (4*(P.T+H))^(1/8+η) ≤ U := by
    apply le_trans _ hU
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have him := hmoment (P.T+H) U (by linarith) hthreshold
  have hs : P.T+H+(P.T+H)^3/U^13 ≤ 8*(P.T+P.T^3/U^13) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ P.T+H)
      (by linarith : P.T+H ≤ 2*P.T) 3
    have hh := div_le_div_of_nonneg_right hp (by positivity : 0 ≤ U^13)
    calc
      _ ≤ 2*P.T+(2*P.T)^3/U^13 := add_le_add (by linarith) hh
      _ ≤ _ := by ring_nf; linarith
  have hp : (P.T+H)^η ≤ (2:ℝ)^η*P.T^η := by
    rw [← Real.mul_rpow (by norm_num) hTp.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hη.le
  have hint : (∫ v in -(P.T+H)..P.T+H,ivicSixthExcess U v^6) ≤
      (A*8*(2:ℝ)^η)*P.T^η*(P.T+P.T^3/U^13) := by
    apply him.trans
    have hb := mul_le_mul
      (mul_le_mul_of_nonneg_left hp hA.le) hs (by positivity) (by positivity)
    convert hb using 1
    ring
  calc
    _ ≤ (8*C)^6*P.N^9*(2*H)^5*(2*H+1)*
        ((A*8*(2:ℝ)^η)*P.T^η*(P.T+P.T^3/U^13)) :=
      hm.trans (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = ((8*C)^6*A*8*(2:ℝ)^η)*
        (P.N^9*(2*H)^5*(2*H+1)*P.T^η*(P.T+P.T^3/U^13)) := by ring
    _ ≤ D*(P.N^9*(2*H)^5*(2*H+1)*P.T^η*(P.T+P.T^3/U^13)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by ring

private theorem general_loss_parameters {σ τ ε : ℝ}
    (hτ : 0 < τ) (hgap : τ/8 < 2*σ-3/2) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ min (1/4) (τ/2) ∧ 2*θ ≤ ε ∧
      (τ+θ)*(θ/(τ+1)) ≤ θ ∧
      θ+(τ+θ)*(1/8+θ/(τ+1)) ≤ 2*σ-3/2-4*θ ∧
      9+(τ+θ)*(1+7*(θ/(τ+1))) ≤
        (max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ))+ε)+12*(σ-θ) ∧
      9+(τ+θ)*(3+7*(θ/(τ+1)))-13*(2*σ-3/2-4*θ) ≤
        (max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ))+ε)+12*(σ-θ) := by
  let g := 2*σ-3/2-τ/8
  let θ := min (min (1/4) (τ/2)) (min (g/16) (ε/256))
  have hg : 0 < g := by dsimp [g]; linarith
  have hθ : 0 < θ :=
    lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (by positivity))
  have hθs : θ ≤ min (1/4) (τ/2) := min_le_left _ _
  have hθ1 : θ ≤ 1 := (hθs.trans (min_le_left _ _)).trans (by norm_num)
  have hθg : θ ≤ g/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hθε : θ ≤ ε/256 := (min_le_right _ _).trans (min_le_right _ _)
  let ν := θ/(τ+1)
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hντ : ν*(τ+1)=θ := by dsimp [ν]; field_simp
  have hwin : (τ+θ)*ν ≤ θ := by nlinarith
  have hm1 : τ+9-12*σ ≤ max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hm2 : 3*τ+57/2-38*σ ≤ max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨θ,hθ,hθs,by linarith,hwin,?_,?_,?_⟩
  · dsimp [g] at hθg
    change θ+(τ+θ)*(1/8+ν) ≤ 2*σ-3/2-4*θ
    nlinarith
  · change 9+(τ+θ)*(1+7*ν) ≤ _
    nlinarith
  · change 9+(τ+θ)*(3+7*ν)-13*(2*σ-3/2-4*θ) ≤ _
    nlinarith

/- Exact source types; proof binders are unnamed when the type is nondependent. -/

example : ExponentPair (2/7) (4/7) := @pair

example : ∀ {A H G Y : ℝ}
    (_ : 0 < A) (_ : 0 < H) (_ : 0 < G) (_ : 0 < Y),
    0 < absorptionLength A H G Y := @length_pos

example : ∀ {A H G Y : ℝ}
    (_ : 0 < A) (_ : 0 < H) (_ : 0 < G),
    2*A*((absorptionLength A H G Y)^(2/7:ℝ)*H^(2/7:ℝ)*G^(1/7:ℝ)) ≤ Y^2 := @length_absorbs

example : ∀ {A H G Y : ℝ}
    (_ : 0 < A) (_ : 0 < H) (_ : 0 < G) (_ : 0 < Y),
    absorptionLength A H G Y = Y^7/(128*A^(7/2:ℝ)*H*G^(1/2:ℝ)) := @length_eq

example : ∀ {A H G Y : ℝ}
    (_ : 0 < A) (_ : 0 < H) (_ : 0 < G) (_ : 0 < Y),
    ((Nat.floor (H/absorptionLength A H G Y)+1:ℕ):ℝ)*
      (2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+256*A^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) := @covered_card_budget

example : ∀ {A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (_ : 0 < A) (_ : 0 < H) (_ : 0 < G) (_ : 0 < Y)
    (_ : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (_ : ∀ t ∈ W, Y ≤ f t)
    (_ : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+absorptionLength A H G Y) →
        (∑ t ∈ U, f t)^2 ≤
          A*((U.card : ℝ)*H/G+(U.card : ℝ)^2*
            ((absorptionLength A H G Y)^(2/7:ℝ)*H^(2/7:ℝ)*G^(1/7:ℝ)))),
    (W.card : ℝ) ≤
      2*A*H/(G*Y^2)+256*A^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) := @card_le_of_local_packets

example : ∀ {D H G Y ν : ℝ}
    (_ : 0 ≤ D) (_ : 1 ≤ H) (_ : 0 < G) (_ : 0 < Y) (_ : 0 ≤ ν),
    2*(D*H^(2*ν/9))*H/(G*Y^2)+
        256*(D*H^(2*ν/9))^(9/2:ℝ)*H^3/(G^(1/2:ℝ)*Y^9) ≤
      (2*D+256*D^(9/2:ℝ))*H^ν*
        (H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9)) := @count_exponent_budget

example : ∀ {δ κ ν : ℝ}
    (_ : 0 < δ) (_ : 0 < κ) (_ : 0 < ν),
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G Y : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < Y →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧
          G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
        (W.card : ℝ) ≤ D*H^ν*
          (H/(G*Y^2)+H^3/(G^(1/2:ℝ)*Y^9)) := @localMeanExcess_card_le

example : ∀ {δ κ ν : ℝ} (_ : 0 < δ) (_ : 0 < κ) (_ : 0 < ν),
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^3/(G^(1/2:ℝ)*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^9)) := @exists_ivicNineteenth_pointCluster_superlevel_count

example : ∀ {H G A m : ℝ}
    (_ : 0 ≤ H) (_ : 0 < G) (_ : 0 < A) (_ : 1 ≤ m),
    H/(G*(m*A)^2)+H^3/(G^(1/2:ℝ)*(m*A)^9) ≤
      (H/(G*A^2)+H^3/(G^(1/2:ℝ)*A^9))/m^2 := @ivicNineteenth_occupancy_inverse_power_budget

example : ∀ {δ κ ν : ℝ} (_ : 0 < δ) (_ : 0 < κ) (_ : 0 < ν),
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^3/(G^(1/2:ℝ)*(V^2/(16*P*Real.log (3*H)))^9)) := @exists_ivicNineteenth_pointValue_card_le_with_width

example : ∀ {P K L V H : ℝ}
    (_ : 0 < P) (_ : 0 < K) (_ : 0 < L) (_ : 0 < V),
    H/((V^2/(K*L^2))*(V^2/(16*P*L))^2) +
        H^3/((V^2/(K*L^2))^(1/2:ℝ)*(V^2/(16*P*L))^9) =
      K*(16*P)^2*(H*L^4/V^6) + K^(1/2:ℝ)*(16*P)^9*(H^3*L^10/V^19) := @ivicNineteenth_pointValueWidth_count_identity

example : ∀ {δ κ ν : ℝ} (_ : 0 < δ) (_ : δ ≤ 1/4)
    (_ : 0 < κ) (_ : 0 < ν),
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^3*(Real.log (3*H))^10/V^19) := @exists_ivicNineteenth_pointValue_card_le_source_range

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card : ℝ) ≤ H^ε*(H/V^6+H^3/V^19) := @exists_ivicNineteenth_pointValue_card_le

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H V : ℝ,
      B ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      volume (pointValueSuperlevel H V) ≤
        ENNReal.ofReal (2*H^ε*(H/V^6+H^3/V^19)) := @volume_peak_bound

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H U : ℝ, B ≤ H → H^(1/8+ε) ≤ U →
      (∫ t in pointValueSuperlevel H U, zetaMomentCriticalNorm t^6) ≤
        H^ε*(H+H^3/U^13) := @variable_restricted_sixth_moment

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H U : ℝ, B ≤ H → H^(1/8+ε) ≤ U →
      (∫ t in H..2*H, ivicSixthExcess U t^6) ≤ H^ε*(H+H^3/U^13) := @variable_excess_dyadic

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 40000 ≤ B ∧ ∀ T U : ℝ,
      B ≤ T → (4*T)^(1/8+ε) ≤ U →
      (∫ t in T/2..3*T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) := @variable_excess_source

example : ∀ {ε : ℝ} (_ : 0 < ε),
    ∀ᶠ T : ℝ in atTop, ∀ U : ℝ, (4*T)^(1/8+ε) ≤ U →
      zetaMomentLogLoss T^6*(∫ t in T/2..3*T, ivicSixthExcess U t^6) ≤
        T^(3*ε)*(T+T^3/U^13) := @variable_excess_source_log

example (A H G Y : ℝ) : absorptionLength A H G Y =
    (Y^2/(4*A*H^(2/7:ℝ)*G^(1/7:ℝ)))^(7/2:ℝ) := rfl

#print axioms pair
#print axioms length_pos
#print axioms length_absorbs
#print axioms length_eq
#print axioms covered_card_budget
#print axioms card_le_of_local_packets
#print axioms count_exponent_budget
#print axioms localMeanExcess_card_le
#print axioms exists_ivicNineteenth_pointCluster_superlevel_count
#print axioms ivicNineteenth_occupancy_inverse_power_budget
#print axioms exists_ivicNineteenth_pointValue_card_le_with_width
#print axioms ivicNineteenth_pointValueWidth_count_identity
#print axioms exists_ivicNineteenth_pointValue_card_le_source_range
#print axioms exists_ivicNineteenth_pointValue_card_le
#print axioms volume_peak_bound
#print axioms variable_restricted_sixth_moment
#print axioms variable_excess_dyadic
#print axioms variable_excess_source
#print axioms variable_excess_source_log
#print axioms absorptionLength


example : ∀ {σ τ ε : ℝ}, 1 < τ → τ/8 < σ-1/2 → 0 < ε →
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ min (1/4) ((τ-1)/4) ∧
      (τ+θ)*(θ/(τ+1)) ≤ θ ∧
      θ+(τ+θ)*(1/8+θ/(τ+1)) ≤ σ-1/2-4*θ ∧
      3+(τ+θ)*(1+3*(θ/(τ+1))) ≤
        (max (τ+3-6*σ) (3*τ+19/2-19*σ)+ε)+6*(σ-θ) ∧
      3+(τ+θ)*(3+3*(θ/(τ+1)))-13*(σ-1/2-4*θ) ≤
        (max (τ+3-6*σ) (3*τ+19/2-19*σ)+ε)+6*(σ-θ) := @zeta_loss_parameters
example : ∀ {σ τ : ℝ}, 1/2 ≤ σ → 1 < τ → τ/8 < σ-1/2 →
    IsZetaLargeValueBound σ τ (max (τ+3-6*σ) (3*τ+19/2-19*σ)) :=
  @zeta_largeValueBound
#print axioms zeta_loss_parameters
#print axioms zeta_largeValueBound


example : ∀ {ε : ℝ}, 0 < ε →
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (4*T)^(1/8+ε) ≤ U →
      (∫ t in 0..T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) :=
  @variable_excess_zero
example : ∀ {ε : ℝ}, 0 < ε →
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (4*T)^(1/8+ε) ≤ U →
      (∫ t in -T..T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) :=
  @variable_excess_symmetric
#print axioms variable_excess_zero
#print axioms variable_excess_symmetric


example : ∀ {η : ℝ}, 0 < η → ∀ {q : ℕ}, 0 < q →
    ∃ C D T₀ : ℝ, 0 < C ∧ 0 < D ∧ 40000 ≤ T₀ ∧
      ∀ P : LargeValuePattern, T₀ ≤ P.T → ∀ H U : ℝ,
      0 ≤ H → H ≤ P.T → (8*P.T)^(1/8+η) ≤ U →
      4*C*P.N*Real.sqrt P.N*(2*H*U+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ D*P.N^2 ∨
      (P.ordinates.card:ℝ)*P.V^12 ≤
        D*P.N^9*(2*H)^5*(2*H+1)*P.T^η*(P.T+P.T^3/U^13) := @variable_physical_pattern
example : ∀ {σ τ ε : ℝ}, 0 < τ → τ/8 < 2*σ-3/2 → 0 < ε →
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ min (1/4) (τ/2) ∧ 2*θ ≤ ε ∧
      (τ+θ)*(θ/(τ+1)) ≤ θ ∧
      θ+(τ+θ)*(1/8+θ/(τ+1)) ≤ 2*σ-3/2-4*θ ∧
      9+(τ+θ)*(1+7*(θ/(τ+1))) ≤
        (max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ))+ε)+12*(σ-θ) ∧
      9+(τ+θ)*(3+7*(θ/(τ+1)))-13*(2*σ-3/2-4*θ) ≤
        (max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ))+ε)+12*(σ-θ) :=
  @general_loss_parameters
#print axioms variable_physical_pattern
#print axioms general_loss_parameters

end IvicNineteenthScratch
