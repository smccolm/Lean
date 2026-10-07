import Dubon2026.CoefficientShift
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! # Actual cusp-form Fourier coefficients in the two source normalizations

These objects use Mathlib's holomorphic cusp forms on Γ₀(Q) with trivial
character and their actual q-expansions. No Hecke, newform, non-CM, or classical
analytic input is encoded as an assumed conclusion here.
-/

namespace Dubon2026

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The actual classical Fourier coefficient, with cusp parameter exp(2πiτ). -/
def cuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

/-- The source's automorphic normalization λ_f(n)=a_f(n)n^{-(k-1)/2}. -/
def normalizedCuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) : ℕ → ℂ :=
  shiftedCoefficients (cuspCoefficients f) (-((k : ℝ) - 1) / 2)

theorem cuspCoefficients_hasSum {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    HasSum (fun n => cuspCoefficients f n * (Function.Periodic.qParam 1 τ) ^ n) (f τ) := by
  have hp : (1 : ℝ) ∈ (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  letI : Fact (IsCusp OnePoint.infty (Gamma0 Q : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  simpa only [cuspCoefficients, smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion
    zero_lt_one (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

theorem cuspCoefficients_zero {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) : cuspCoefficients f 0 = 0 := by
  have hp : (1 : ℝ) ∈ (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  letI : Fact (IsCusp OnePoint.infty (Gamma0 Q : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  rw [cuspCoefficients, UpperHalfPlane.qExpansion_coeff_zero zero_lt_one
    (ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one hp)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hp)]
  exact (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero

theorem norm_normalizedCuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    ‖normalizedCuspCoefficients f n‖ =
      ‖cuspCoefficients f n‖ * (n : ℝ) ^ (-((k : ℝ) - 1) / 2) := by
  rw [normalizedCuspCoefficients, shiftedCoefficients, norm_mul,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

theorem normalizedCuspCoefficients_one {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (qExpansion 1 f).coeff 1 = 1) : normalizedCuspCoefficients f 1 = 1 := by
  rw [normalizedCuspCoefficients, shiftedCoefficients_one]
  exact hf

theorem dirichletSum_normalizedCuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (N : ℕ) (s : ℂ) :
    dirichletSum (normalizedCuspCoefficients f) N s =
      dirichletSum (cuspCoefficients f) N (s + ((k : ℂ) - 1) / 2) := by
  rw [normalizedCuspCoefficients, dirichletSum_shiftedCoefficients]
  congr 1
  push_cast
  ring

theorem dirichletSum_classicalCuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (N : ℕ) (s : ℂ) :
    dirichletSum (cuspCoefficients f) N s =
      dirichletSum (normalizedCuspCoefficients f) N (s - ((k : ℂ) - 1) / 2) := by
  rw [dirichletSum_normalizedCuspCoefficients]
  congr 1
  ring

theorem normalizedCuspCoefficients_lastIndex {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (N : ℕ) :
    lastIndex (normalizedCuspCoefficients f) N = lastIndex (cuspCoefficients f) N :=
  lastIndex_shiftedCoefficients _ _ _

theorem classical_cusp_concentration_line (k : ℤ) :
    (1 / 2 : ℝ) + ((k : ℝ) - 1) / 2 = (k : ℝ) / 2 := by ring

end

end Dubon2026
