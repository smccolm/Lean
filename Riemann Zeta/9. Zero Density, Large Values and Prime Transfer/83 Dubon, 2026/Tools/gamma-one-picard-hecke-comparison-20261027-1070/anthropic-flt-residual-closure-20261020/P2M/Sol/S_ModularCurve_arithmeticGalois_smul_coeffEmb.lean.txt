import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_coeffEmb

open ModularCurve AlgebraicCurve IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries ℚ} (hx : x ∈ F₀) : ModularCurve.arithmeticGalois F₀ σ • (⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L F₀) = ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ :=
  by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  exact coeffMap_coeffEmb σ x
