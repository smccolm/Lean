import TaoTrudgianYang2025.SargosFourthGeometry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-!
# The literal fourth-power near-solution set

The source support is (N,2N], with widths N and N cubed.
Every source quadruple is injected into the finite hyperbolic
coordinate region derived in SargosFourthGeometry.
-/

namespace TaoTrudgianYang2025

def sargosFourthNearSolutions (N : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset (fun _ : Fin 4 => Finset.Ioc (N : ℤ) (2*N))).filter
    (fun q => |q 0^2+q 1^2-q 2^2-q 3^2| ≤ N ∧
      |q 0^4+q 1^4-q 2^4-q 3^4| ≤ (N : ℤ)^3)

def sargosSignedHyperbola (L M : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(L : ℤ)) L) ×ˢ (Finset.Icc (-(L : ℤ)) L)).filter
    (fun x => |x.1*x.2| ≤ M)

theorem sargosFourthNearSolutions_coordinates {N : ℕ} (hN : 1 ≤ N)
    {q : Fin 4 → ℤ} (hq : q ∈ sargosFourthNearSolutions N) :
    sargosFourthCoordinates q ∈
      (Finset.Icc (2*(N : ℤ)) (4*N)) ×ˢ
        ((Finset.Icc (-3 : ℤ) 3) ×ˢ sargosSignedHyperbola (2*N) (11*N)) := by
  obtain ⟨hqI,hq₂,hq₄⟩ := Finset.mem_filter.mp hq
  have hI := Fintype.mem_piFinset.mp hqI
  have hr (i : Fin 4) : (q i : ℝ) ∈ Set.Icc (N : ℝ) (2*N) := by
    have hi := Finset.mem_Ioc.mp (hI i)
    constructor
    · exact_mod_cast hi.1.le
    · exact_mod_cast hi.2
  have h₂ : |(q 0 : ℝ)^2+(q 1 : ℝ)^2-(q 2 : ℝ)^2-(q 3 : ℝ)^2| ≤ N := by
    exact_mod_cast hq₂
  have h₄ : |(q 0 : ℝ)^4+(q 1 : ℝ)^4-(q 2 : ℝ)^4-(q 3 : ℝ)^4| ≤ (N : ℝ)^3 := by
    exact_mod_cast hq₄
  obtain ⟨hA,hD,hu,hv,hprod⟩ := sargos_fourth_coordinate_bounds
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))
    (hr 0) (hr 1) (hr 2) (hr 3) h₂ h₄
  have hA' : 2*(N : ℤ) ≤ q 0+q 1 ∧ q 0+q 1 ≤ 4*N := by
    exact ⟨by exact_mod_cast hA.1,by exact_mod_cast hA.2⟩
  have hD' : |q 2+q 3-q 0-q 1| ≤ (3 : ℤ) := by exact_mod_cast hD
  have hu' : |q 0-q 1-q 2+q 3| ≤ (2*N : ℕ) := by exact_mod_cast hu
  have hv' : |q 0-q 1+q 2-q 3| ≤ (2*N : ℕ) := by exact_mod_cast hv
  have hp' : |(q 0-q 1-q 2+q 3)*(q 0-q 1+q 2-q 3)| ≤ (11*N : ℕ) := by
    exact_mod_cast hprod
  simp only [sargosFourthCoordinates,Finset.mem_product,Finset.mem_Icc,
    sargosSignedHyperbola,Finset.mem_filter]
  exact ⟨hA',abs_le.mp hD',⟨abs_le.mp hu',abs_le.mp hv'⟩,hp'⟩

theorem card_sargosFourthNearSolutions_le_hyperbola {N : ℕ} (hN : 1 ≤ N) :
    (sargosFourthNearSolutions N).card ≤
      (2*N+1)*7*(sargosSignedHyperbola (2*N) (11*N)).card := by
  have hi := Finset.card_le_card_of_injOn sargosFourthCoordinates
    (fun q hq => sargosFourthNearSolutions_coordinates hN hq)
    sargosFourthCoordinates_injective.injOn
  have hA : (Finset.Icc (2*(N : ℤ)) (4*N)).card = 2*N+1 := by
    rw [Int.card_Icc]
    omega
  have hD : (Finset.Icc (-3 : ℤ) 3).card = 7 := by decide
  simpa only [Finset.card_product,hA,hD,mul_assoc] using hi

end TaoTrudgianYang2025
