import TaoTrudgianYang2025.RobertSargosZeroProjection
import TaoTrudgianYang2025.IntegerProductCount

/-! Actual zero-displacement seven-variable fibers inject into nonzero integer factor pairs. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_zero_fiber_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ)
      (z : (ℤ × ℤ × ℤ) × ℤ), 0 < H → 0 < Q →
      (∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) →
      (∀ p ∈ S, robertSargosZeroKey p = z) →
      (∀ p ∈ S, p.n₁ = p.n₂) →
      (S.card:ℝ) ≤ C*(4*H*Q)^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_positive_integer_product_pairs_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N δ z hH hQ hmem hfix hzero
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    let m : ℤ := z.1.2.1*z.1.2.2
    let f : RobertSargosSevenPoint → ℤ × ℤ := fun p => (p.h₂,p.q₂)
    let T := S.image f
    have hprod : ∀ p ∈ S, p.h₂*p.q₂ = m := by
      intro p hp
      have hh : p.h₁ = z.1.2.1 :=
        congrArg (fun w : (ℤ × ℤ × ℤ) × ℤ => w.1.2.1) (hfix p hp)
      have hq : p.q₁ = z.1.2.2 :=
        congrArg (fun w : (ℤ × ℤ × ℤ) × ℤ => w.1.2.2) (hfix p hp)
      dsimp [m]
      rw [← hh,← hq]
      exact (hmem p hp).zero_product (hzero p hp)
    have hpos : ∀ p ∈ S, 0 < p.h₂ := by
      intro p hp
      have hh : (0:ℝ) < p.h₂ := lt_of_lt_of_le hH (hmem p hp).h₂_support.1
      exact_mod_cast hh
    have hqne : p₀.q₂ ≠ 0 := by
      have hq : (p₀.q₂:ℝ) ≠ 0 :=
        abs_pos.mp (lt_of_lt_of_le hQ (hmem p₀ hp₀).q₂_support.1)
      exact_mod_cast hq
    have hm : m ≠ 0 := by
      rw [← hprod p₀ hp₀]
      exact mul_ne_zero (ne_of_gt (hpos p₀ hp₀)) hqne
    have hM : (m.natAbs:ℝ) ≤ 4*H*Q := by
      have hcast : (m.natAbs:ℝ) = |(m:ℝ)| := by
        simpa only [Int.cast_natCast,Int.cast_abs] using
          congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs m)
      have hh : (0:ℝ) < p₀.h₂ := by exact_mod_cast hpos p₀ hp₀
      rw [hcast,← hprod p₀ hp₀,Int.cast_mul,abs_mul,abs_of_pos hh]
      calc
        _ ≤ (2*H)*(2*Q) := mul_le_mul (hmem p₀ hp₀).h₂_support.2
          (hmem p₀ hp₀).q₂_support.2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hinj : Set.InjOn f S := by
      intro p hp q hq he
      exact robertSargos_zero_key_injective ((hfix p hp).trans (hfix q hq).symm)
        (congrArg (fun x : ℤ × ℤ => x.1) he)
        (congrArg (fun x : ℤ × ℤ => x.2) he) (hzero p hp) (hzero q hq)
    have hcard : T.card = S.card := Finset.card_image_of_injOn hinj
    have hb := hbound T m (4*H*Q) hm hM
      (fun t ht => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
        exact hpos p hp)
      (fun t ht => by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
        exact hprod p hp)
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025
