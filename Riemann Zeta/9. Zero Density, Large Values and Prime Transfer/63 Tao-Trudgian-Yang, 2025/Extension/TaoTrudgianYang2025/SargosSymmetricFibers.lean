import TaoTrudgianYang2025.SargosSymmetricAveraging

/-! Literal parity fibers for symmetric, nonconjugated products. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSymmetricFiber (H j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range H ×ˢ Finset.range H).filter (fun q => q.1+q.2=j)

def sargosSymmetricOffsets (H j : ℕ) : Finset ℤ :=
  (sargosSymmetricFiber H j).image (fun q => (q.1:ℤ)-q.2)

theorem mem_sargosSymmetricFiber {H j h k : ℕ} :
    (h,k) ∈ sargosSymmetricFiber H j ↔ h < H ∧ k < H ∧ h+k=j := by
  simp only [sargosSymmetricFiber,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  tauto

theorem sargosSymmetricOffsets_mem {H j : ℕ} {n : ℤ} :
    n ∈ sargosSymmetricOffsets H j ↔
      ∃ h < H, ∃ k < H, h+k=j ∧ (h:ℤ)-k=n := by
  simp only [sargosSymmetricOffsets,Finset.mem_image]
  constructor
  · rintro ⟨⟨h,k⟩,hq,hn⟩
    obtain ⟨hh,hk,hj⟩ := mem_sargosSymmetricFiber.mp hq
    exact ⟨h,hh,k,hk,hj,hn⟩
  · rintro ⟨h,hh,k,hk,hj,hn⟩
    exact ⟨(h,k),mem_sargosSymmetricFiber.mpr ⟨hh,hk,hj⟩,hn⟩

theorem sargosSymmetricOffsets_neg {H j : ℕ} {n : ℤ}
    (hn : n ∈ sargosSymmetricOffsets H j) :
    -n ∈ sargosSymmetricOffsets H j := by
  obtain ⟨h,hh,k,hk,hj,hn⟩ := sargosSymmetricOffsets_mem.mp hn
  apply sargosSymmetricOffsets_mem.mpr
  exact ⟨k,hk,h,hh,by omega,by omega⟩

theorem sargosSymmetricOffsets_bounds {H j : ℕ} {n : ℤ}
    (hn : n ∈ sargosSymmetricOffsets H j) :
    -(H:ℤ) < n ∧ n < H := by
  obtain ⟨h,hh,k,hk,hj,hn⟩ := sargosSymmetricOffsets_mem.mp hn
  omega

theorem sargosSymmetricFiber_sum (φ : ℤ → ℂ) (H j : ℕ) (m : ℤ) :
    (∑ q ∈ sargosSymmetricFiber H j, φ (m+2*q.1)*φ (m+2*q.2)) =
      ∑ n ∈ sargosSymmetricOffsets H j, φ (m+j+n)*φ (m+j-n) := by
  rw [sargosSymmetricOffsets,Finset.sum_image]
  · apply Finset.sum_congr rfl
    rintro ⟨h,k⟩ hq
    have hj := (mem_sargosSymmetricFiber.mp hq).2.2
    have e1 : m+2*(h:ℤ) = m+j+((h:ℤ)-k) := by omega
    have e2 : m+2*(k:ℤ) = m+j-((h:ℤ)-k) := by omega
    rw [e1,e2]
  · rintro ⟨h,k⟩ hq ⟨h',k'⟩ hq' he
    have hj := (mem_sargosSymmetricFiber.mp hq).2.2
    have hj' := (mem_sargosSymmetricFiber.mp hq').2.2
    dsimp at he
    congr 1 <;> omega

theorem sargos_even_shift_square (φ : ℤ → ℂ) (H : ℕ) (m : ℤ) :
    (∑ h ∈ Finset.range H, φ (m+2*h))^2 =
      ∑ j ∈ Finset.range (2*H),
        ∑ n ∈ sargosSymmetricOffsets H j, φ (m+j+n)*φ (m+j-n) := by
  have hmap : ∀ q ∈ Finset.range H ×ˢ Finset.range H, q.1+q.2 ∈ Finset.range (2*H) := by
    rintro ⟨h,k⟩ hq
    simp only [Finset.mem_product,Finset.mem_range] at hq ⊢
    omega
  calc
    _ = ∑ q ∈ Finset.range H ×ˢ Finset.range H, φ (m+2*q.1)*φ (m+2*q.2) := by
      rw [pow_two,Finset.sum_mul_sum,Finset.sum_product]
    _ = ∑ j ∈ Finset.range (2*H),
        ∑ q ∈ sargosSymmetricFiber H j, φ (m+2*q.1)*φ (m+2*q.2) := by
      exact (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sargosSymmetricFiber_sum φ H j m

theorem sargos_even_shift_norm_sq (φ : ℤ → ℂ) (H : ℕ) (m : ℤ) :
    ‖∑ h ∈ Finset.range H, φ (m+2*h)‖^2 ≤
      ∑ j ∈ Finset.range (2*H),
        ‖∑ n ∈ sargosSymmetricOffsets H j, φ (m+j+n)*φ (m+j-n)‖ := by
  rw [← norm_pow,sargos_even_shift_square]
  exact norm_sum_le _ _

end TaoTrudgianYang2025
