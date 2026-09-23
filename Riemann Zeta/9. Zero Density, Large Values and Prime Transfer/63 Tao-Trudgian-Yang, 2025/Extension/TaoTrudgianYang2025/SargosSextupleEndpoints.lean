import TaoTrudgianYang2025.SargosSquareDiagonalCount

/-! Actual endpoint removal with at most two unit terms per sextuple. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_interval_endpoint_loss (f : ℤ → ℂ) (a b : ℤ)
    (hf : ∀ n ∈ Finset.Icc a b, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc a b, f n)-(∑ n ∈ Finset.Ioo a b, f n)‖ ≤ 2 := by
  have hs : Finset.Ioo a b ⊆ Finset.Icc a b := by
    intro n hn
    have h := Finset.mem_Ioo.mp hn
    exact Finset.mem_Icc.mpr ⟨h.1.le,h.2.le⟩
  have hb : Finset.Icc a b \ Finset.Ioo a b ⊆ ({a,b}:Finset ℤ) := by
    intro n hn
    have h := Finset.mem_sdiff.mp hn
    have hc := Finset.mem_Icc.mp h.1
    have ho : ¬(a<n ∧ n<b) := by simpa only [Finset.mem_Ioo] using h.2
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have hcard : (Finset.Icc a b \ Finset.Ioo a b).card ≤ 2 := by
    calc
      _ ≤ ({a,b}:Finset ℤ).card := Finset.card_le_card hb
      _ ≤ 2 := by simpa using Finset.card_insert_le a ({b}:Finset ℤ)
  rw [← Finset.sum_sdiff_eq_sub hs]
  calc
    _ ≤ ∑ n ∈ Finset.Icc a b \ Finset.Ioo a b, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc a b \ Finset.Ioo a b, (1:ℝ) :=
      Finset.sum_le_sum (fun n hn => hf n (Finset.mem_sdiff.mp hn).1)
    _ = ((Finset.Icc a b \ Finset.Ioo a b).card:ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hcard

theorem sargos_interval_norm_le_interior (f : ℤ → ℂ) (a b : ℤ)
    (hf : ∀ n ∈ Finset.Icc a b, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc a b, f n‖ ≤ ‖∑ n ∈ Finset.Ioo a b, f n‖+2 := by
  have h := sargos_interval_endpoint_loss f a b hf
  calc
    _ = ‖(∑ n ∈ Finset.Ioo a b, f n)+
        ((∑ n ∈ Finset.Icc a b, f n)-(∑ n ∈ Finset.Ioo a b, f n))‖ := by
      congr 1
      abel
    _ ≤ ‖∑ n ∈ Finset.Ioo a b, f n‖+
        ‖(∑ n ∈ Finset.Icc a b, f n)-(∑ n ∈ Finset.Ioo a b, f n)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl h

def sargosSextupleInterior {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : Finset ℤ :=
  Finset.Ioo (sargosSextupleRadius q+1) ((M:ℤ)-sargosSextupleRadius q)

def sargosInteriorSextupleCorrelation (f : ℝ → ℝ) (M H : ℕ) : ℝ :=
  ∑ q ∈ sargosSquareDiagonal H,
    ‖∑ m ∈ sargosSextupleInterior M q, fordAdditiveCharacter (sargosSextuplePhase f q m)‖

theorem sargosInteriorSextupleCorrelation_nonneg (f : ℝ → ℝ) (M H : ℕ) :
    0 ≤ sargosInteriorSextupleCorrelation f M H :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem sargosSourceSextupleCorrelation_le_interior (f : ℝ → ℝ) (M H : ℕ) :
    sargosSourceSextupleCorrelation (fun n => fordAdditiveCharacter (f n)) M H ≤
      sargosInteriorSextupleCorrelation f M H+2*((sargosSquareDiagonal H).card:ℝ) := by
  rw [sargosSourceSextupleCorrelation_eq_phase]
  calc
    _ ≤ ∑ q ∈ sargosSquareDiagonal H,
        (‖∑ m ∈ sargosSextupleInterior M q, fordAdditiveCharacter (sargosSextuplePhase f q m)‖+2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact sargos_interval_norm_le_interior _ _ _ (fun m hm => by simp [sargos_character_norm])
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [sargosInteriorSextupleCorrelation,mul_comm]

theorem sargosSourceSextupleCorrelation_interior_error (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ M : ℕ, ∀ f : ℝ → ℝ,
      sargosSourceSextupleCorrelation (fun n => fordAdditiveCharacter (f n)) M H ≤
        sargosInteriorSextupleCorrelation f M H+C*(H:ℝ)^(4+ε) := by
  obtain ⟨C,hC,hcount⟩ := sargosSquareDiagonal_card_bound ε hε
  refine ⟨2*C,by linarith,?_⟩
  intro H hH M f
  exact (sargosSourceSextupleCorrelation_le_interior f M H).trans
    (add_le_add le_rfl (by nlinarith only [hcount H hH]))

end TaoTrudgianYang2025
