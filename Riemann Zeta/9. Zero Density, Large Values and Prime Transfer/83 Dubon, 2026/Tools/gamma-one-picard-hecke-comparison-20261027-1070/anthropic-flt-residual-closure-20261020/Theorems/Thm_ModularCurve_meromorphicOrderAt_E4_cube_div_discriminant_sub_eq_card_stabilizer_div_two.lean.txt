import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
    (τ : ℍ) :
    meromorphicOrderAt
        (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) (τ : ℂ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.solution
