import TaoTrudgianYang2025.SargosSextupleEndpoints

/-! The actual source character estimate after quantitatively removing boundary centers. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_character_interior_differencing (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ M : ℕ, H ≤ M → ∀ f : ℝ → ℝ,
      ‖∑ m ∈ Finset.Ioc (0:ℤ) M, fordAdditiveCharacter (f m)‖^12 ≤
        1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosInteriorSextupleCorrelation f M H+
        C*(M:ℝ)^11*(H:ℝ)^ε := by
  obtain ⟨C,hC,herror⟩ := sargosSourceSextupleCorrelation_interior_error ε hε
  refine ⟨382205952*C,by linarith,?_⟩
  intro H hH M hHM f
  have hHpos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have h := sargos_source_sextuple_differencing (fun n => fordAdditiveCharacter (f n)) hH hHM
  have he : (∑ m ∈ Finset.Ioc (0:ℤ) M, ‖fordAdditiveCharacter (f m)‖^2) = (M:ℝ) := by
    simp [sargos_character_norm]
  rw [he] at h
  have hp : (H:ℝ)^(4+ε) = (H:ℝ)^4*(H:ℝ)^ε := by
    rw [Real.rpow_add hHpos]
    norm_num
  have hscale :
      (382205952*(M:ℝ)^11/(H:ℝ)^4)*(C*(H:ℝ)^(4+ε)) =
        (382205952*C)*(M:ℝ)^11*(H:ℝ)^ε := by
    rw [hp]
    field_simp
  calc
    _ ≤ 1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*
          sargosSourceSextupleCorrelation (fun n => fordAdditiveCharacter (f n)) M H := h
    _ ≤ 1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*
          (sargosInteriorSextupleCorrelation f M H+C*(H:ℝ)^(4+ε)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (herror H hH M f) (by positivity))
    _ = _ := by rw [mul_add,hscale]; ring

end TaoTrudgianYang2025
