import TaoTrudgianYang2025.RobertSargosFrequencyWeightSums
import TaoTrudgianYang2025.RobertSargosFrequencyFibers

/-! Exact summation of frequency-fiber estimates over the source six-coordinate set.
The local fiber estimate in the summation helper is explicit; subsequent consumers
supply it from the proved conic and linear source bounds. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem RobertSargosPrimitiveSystem.displacement_natAbs_mem
    {R H Q δ : ℝ} {p : RobertSargosPoint}
    (h : RobertSargosPrimitiveSystem R H Q δ p)
    (hH : 0 < H) (hQ : 0 < Q) (hδ : δ ≤ 1) :
    p.d.natAbs ∈ Finset.Icc 1 ⌊9*Q⌋₊ := by
  have hd : (p.d.natAbs:ℝ) = |(p.d:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs p.d)
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr h.d_ne_zero)
  · apply (Nat.le_floor_iff (by positivity : 0 ≤ 9*Q)).mpr
    rw [hd]
    calc
      _ ≤ (δ+8)*Q := h.displacement_le hH hQ
      _ ≤ 9*Q := by nlinarith

theorem robertSargos_card_le_weighted_frequency_sum
    (S : Finset RobertSargosPoint) {R H Q δ ε A C : ℝ}
    (hH : 0 < H) (hQ : 1 ≤ Q) (hδ : δ ∈ Set.Icc 0 1)
    (hR : 0 ≤ R) (hε : 0 < ε) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p)
    (hfiber : ∀ z : ℤ × ℤ × ℤ,
      ((S.filter (fun p => robertSargosFrequencyKey p = z)).card:ℝ) ≤
        C*(z.1.natAbs:ℝ)^(ε/2)*(1+A/z.1.natAbs)) :
    (S.card:ℝ) ≤ C*(2*(1+2/ε)*(4*Q+1)*
      (2*(δ*Q+99*R*Q/H)+1)*(⌊9*Q⌋₊:ℝ)^ε*((⌊9*Q⌋₊:ℝ)+A)) := by
  classical
  let U := S.image robertSargosFrequencyKey
  have hQp : 0 < Q := by linarith
  have hδ0 : 0 ≤ δ := hδ.1
  have hmaps : Set.MapsTo robertSargosFrequencyKey S U := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ U, ((S.filter (fun p => robertSargosFrequencyKey p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hs := sum_affine_frequency_rpow_weight_le U hQp.le
    (show 0 ≤ δ*Q+99*R*Q/H by positivity) hε hA
    ((Nat.one_le_floor_iff (9*Q)).mpr (by linarith))
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).displacement_natAbs_mem hH hQp hδ.2)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).q₁_support.2)
    (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hmem p hp).affine_band hH hQp hδ.2)
  calc
    _ = _ := hcardR
    _ ≤ ∑ z ∈ U, C*(z.1.natAbs:ℝ)^(ε/2)*(1+A/z.1.natAbs) :=
      Finset.sum_le_sum (fun z _ => hfiber z)
    _ = C*(∑ z ∈ U, (z.1.natAbs:ℝ)^(ε/2)*(1+A/z.1.natAbs)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC

end TaoTrudgianYang2025
