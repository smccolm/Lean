import TaoTrudgianYang2025.SargosFourthNearCount
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Cast.Order.Field

/-! Finite signed hyperbola counting with an explicit harmonic loss. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosNatHyperbola (L M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (L+1)) ×ˢ (Finset.range (L+1))).filter (fun x => x.1*x.2 ≤ M)

theorem card_sargosNatHyperbola_eq_sum (L M : ℕ) :
    (sargosNatHyperbola L M).card =
      ∑ x ∈ Finset.range (L+1), ((Finset.range (L+1)).filter (fun y => x*y ≤ M)).card := by
  simp only [sargosNatHyperbola,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.sum_product]

theorem sargosNatHyperbola_fiber_bound (L M : ℕ) {x : ℕ} (hx : 0 < x) :
    ((Finset.range (L+1)).filter (fun y => x*y ≤ M)).card ≤ M/x+1 := by
  calc
    _ ≤ (Finset.range (M/x+1)).card := by
      apply Finset.card_le_card
      intro y hy
      have hm := (Finset.mem_filter.mp hy).2
      have hd : y ≤ M/x := (Nat.le_div_iff_mul_le hx).mpr (by simpa [mul_comm] using hm)
      exact Finset.mem_range.mpr (by omega)
    _ = M/x+1 := Finset.card_range _

theorem card_sargosNatHyperbola_le (L M : ℕ) :
    ((sargosNatHyperbola L M).card : ℝ) ≤
      2*(L : ℝ)+1+(M : ℝ)*(1+Real.log L) := by
  have hzero : ((Finset.range (L+1)).filter (fun y => 0*y ≤ M)).card = L+1 := by simp
  have hr : Finset.range (L+1) = insert 0 (Finset.Icc 1 L) := by
    ext x
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  have hsum : ∑ x ∈ Finset.Icc 1 L, ((M/x : ℕ) : ℝ) ≤
      (M : ℝ)*(1+Real.log L) := by
    calc
      _ ≤ ∑ x ∈ Finset.Icc 1 L, (M : ℝ)/(x : ℝ) :=
        Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
      _ = (M : ℝ)*(harmonic L : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (Nat.cast_nonneg M)
  have hsplit := congrArg (fun t : Finset ℕ =>
    ∑ x ∈ t, ((Finset.range (L+1)).filter (fun y => x*y ≤ M)).card) hr
  dsimp only at hsplit
  rw [Finset.sum_insert (by simp)] at hsplit
  rw [card_sargosNatHyperbola_eq_sum,hsplit,hzero,Nat.cast_add,
    Nat.cast_sum,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ (L : ℝ)+1+∑ x ∈ Finset.Icc 1 L, (((M/x : ℕ) : ℝ)+1) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro x hx
      exact_mod_cast sargosNatHyperbola_fiber_bound L M (show 0 < x by
        have := Finset.mem_Icc.mp hx
        omega)
    _ = 2*(L : ℝ)+1+∑ x ∈ Finset.Icc 1 L, ((M/x : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
      ring
    _ ≤ _ := add_le_add le_rfl hsum

def sargosSignedCoordinate (z : ℤ) : Bool × ℕ := (decide (z < 0),z.natAbs)

theorem sargosSignedCoordinate_injective : Function.Injective sargosSignedCoordinate := by
  intro a b h
  have hs := congrArg Prod.fst h
  have hn := congrArg Prod.snd h
  dsimp [sargosSignedCoordinate] at hs hn
  have ha : |a| = |b| := by
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hn
    simpa only [Int.natCast_natAbs] using hc
  by_cases hneg : a < 0
  · have hb : b < 0 := by simpa [hneg] using hs.symm
    rw [abs_of_neg hneg,abs_of_neg hb] at ha
    omega
  · have hb : ¬b < 0 := by simpa [hneg] using hs.symm
    rw [abs_of_nonneg (le_of_not_gt hneg),abs_of_nonneg (le_of_not_gt hb)] at ha
    exact ha

def sargosHyperbolaEncoding (p : ℤ × ℤ) : (Bool × Bool) × (ℕ × ℕ) :=
  ((decide (p.1 < 0),decide (p.2 < 0)),(p.1.natAbs,p.2.natAbs))

theorem sargosHyperbolaEncoding_injective : Function.Injective sargosHyperbolaEncoding := by
  intro p q h
  have hfirst : sargosSignedCoordinate p.1 = sargosSignedCoordinate q.1 := by
    exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)
  have hsecond : sargosSignedCoordinate p.2 = sargosSignedCoordinate q.2 := by
    exact Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2.2) h)
  exact Prod.ext (sargosSignedCoordinate_injective hfirst)
    (sargosSignedCoordinate_injective hsecond)

theorem card_sargosSignedHyperbola_le_nat (L M : ℕ) :
    (sargosSignedHyperbola L M).card ≤ 4*(sargosNatHyperbola L M).card := by
  have hmap : ∀ p ∈ sargosSignedHyperbola L M,
      sargosHyperbolaEncoding p ∈
        (Finset.univ : Finset (Bool × Bool)).product (sargosNatHyperbola L M) := by
    intro p hp
    obtain ⟨hpI,hpM⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpI
    have ha' : p.1.natAbs ≤ L := by
      have hc : (p.1.natAbs : ℤ) ≤ L := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr (Finset.mem_Icc.mp ha)
      exact_mod_cast hc
    have hb' : p.2.natAbs ≤ L := by
      have hc : (p.2.natAbs : ℤ) ≤ L := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr (Finset.mem_Icc.mp hb)
      exact_mod_cast hc
    have hm : p.1.natAbs*p.2.natAbs ≤ M := by
      have hc : ((p.1.natAbs*p.2.natAbs : ℕ) : ℤ) ≤ M := by
        simpa only [Nat.cast_mul,Int.natCast_natAbs,← abs_mul] using hpM
      exact_mod_cast hc
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (p.1.natAbs,p.2.natAbs) ∈ sargosNatHyperbola L M
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,hm⟩
  have hc := Finset.card_le_card_of_injOn sargosHyperbolaEncoding hmap
    sargosHyperbolaEncoding_injective.injOn
  simpa using hc

theorem card_sargosSignedHyperbola_le (L M : ℕ) :
    ((sargosSignedHyperbola L M).card : ℝ) ≤
      4*(2*(L : ℝ)+1+(M : ℝ)*(1+Real.log L)) := by
  calc
    _ ≤ 4*((sargosNatHyperbola L M).card : ℝ) := by
      exact_mod_cast card_sargosSignedHyperbola_le_nat L M
    _ ≤ _ := mul_le_mul_of_nonneg_left (card_sargosNatHyperbola_le L M) (by norm_num)

end TaoTrudgianYang2025
