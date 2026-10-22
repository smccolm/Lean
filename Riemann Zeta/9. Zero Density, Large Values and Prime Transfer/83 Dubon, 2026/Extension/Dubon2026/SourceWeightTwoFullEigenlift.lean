import Dubon2026.SourceParabolicCuspEigenlift
import Dubon2026.SourceCommutingCommonEigenvector
import Dubon2026.PrimitiveMultiplicityOne

/-! DUB-17/18 -> residual modular Galois association -> a normalized
weight-two cusp eigensystem. Restrict the already proved commuting family
of all classical Hecke operators to the nonzero prescribed good-prime
eigenspace. The existing common-eigenvector theorem retains the prescribed
values and adds every remaining index. The actual coefficient identity
then proves that the first coefficient is nonzero, so scaling normalizes it.
This avoids a second Hecke-algebra or maximal-ideal construction.+-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

theorem sourceWeightTwoGoodEigen_exists_fullEigen (N : ℕ) [NeZero N]
    (θ : sourceBinaryHeckePrime N → ℂ)
    (f : CuspForm (Gamma0 N) 2) (hf : f ≠ 0)
    (he : ∀ ell, cuspHeckeLinear N 2 ell.val f = θ ell • f) :
    ∃ (g : CuspForm (Gamma0 N) 2) (a : ℕ → ℂ), g ≠ 0 ∧
      (∀ ell, cuspHeckeLinear N 2 ell.val g = θ ell • g) ∧
      ∀ n, cuspHeckeLinear N 2 n g = a n • g := by
  letI := SourceFunctionField.original_weight_two_cusp_finite N
  let P : Submodule ℂ (CuspForm (Gamma0 N) 2) :=
    ⨅ ell : sourceBinaryHeckePrime N, Module.End.eigenspace (cuspHeckeLinear N 2 ell.val) (θ ell)
  have hmem (g : CuspForm (Gamma0 N) 2) :
      g ∈ P ↔ ∀ ell, cuspHeckeLinear N 2 ell.val g = θ ell • g := by
    simp only [P, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hstab (n : ℕ) (g : CuspForm (Gamma0 N) 2) (hg : g ∈ P) :
      cuspHeckeLinear N 2 n g ∈ P := by
    apply (hmem _).mpr
    intro ell
    rw [← Module.End.mul_apply, (cuspHeckeLinear_commute N 2 ell.val n).eq,
      Module.End.mul_apply, (hmem g).mp hg ell, map_smul]
  let T : ℕ → Module.End ℂ P := fun n => (cuspHeckeLinear N 2 n).restrict (hstab n)
  have hc (m n : ℕ) : Commute (T m) (T n) :=
    LinearMap.ext fun g => Subtype.ext (LinearMap.congr_fun (cuspHeckeLinear_commute N 2 m n).eq g.val)
  let v : P := ⟨f, (hmem f).mpr he⟩
  have hv : v ≠ 0 := fun h => hf (congrArg Subtype.val h)
  letI : Nontrivial P := nontrivial_of_ne v 0 hv
  obtain ⟨a, g, hg, hga⟩ := sourceCommutingOperators_exists_commonEigenvector T hc
  exact ⟨g.val, a, fun h => hg (Subtype.ext h), (hmem g.val).mp g.property,
    fun n => congrArg Subtype.val (hga n)⟩

theorem sourceWeightTwoGoodEigen_exists_normalized (N : ℕ) [NeZero N]
    (θ : sourceBinaryHeckePrime N → ℂ)
    (f : CuspForm (Gamma0 N) 2) (hf : f ≠ 0)
    (he : ∀ ell, cuspHeckeLinear N 2 ell.val f = θ ell • f) :
    ∃ g : CuspForm (Gamma0 N) 2, cuspCoefficients g 1 = 1 ∧
      (∀ ell, cuspCoefficients g ell.val = θ ell) ∧
      ∀ n, n ≠ 0 → cuspHeckeLinear N 2 n g = cuspCoefficients g n • g := by
  obtain ⟨g, a, hg, hgood, hall⟩ := sourceWeightTwoGoodEigen_exists_fullEigen N θ f hf he
  have hc : cuspCoefficients g 1 ≠ 0 := by
    intro hz
    apply hg
    apply cuspCoefficients_injective N 2
    funext n
    change cuspCoefficients g n = cuspCoefficientLinear N 2 n 0
    rw [map_zero]
    by_cases hn : n = 0
    · subst n
      exact cuspCoefficients_zero g
    · rw [cuspHeckeLinear_eigen_coefficient g hn (a n) (hall n), hz, mul_zero]
  let g' := (cuspCoefficients g 1)⁻¹ • g
  have hnorm : cuspCoefficients g' 1 = 1 := by
    change cuspCoefficientLinear N 2 1 ((cuspCoefficients g 1)⁻¹ • g) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ hc
  have hall' (n : ℕ) : cuspHeckeLinear N 2 n g' = a n • g' := by
    change cuspHeckeLinear N 2 n ((cuspCoefficients g 1)⁻¹ • g) = _
    rw [map_smul, hall, smul_comm]
  have hgood' (ell : sourceBinaryHeckePrime N) :
      cuspHeckeLinear N 2 ell.val g' = θ ell • g' := by
    change cuspHeckeLinear N 2 ell.val ((cuspCoefficients g 1)⁻¹ • g) = _
    rw [map_smul, hgood, smul_comm]
  refine ⟨g', hnorm, fun ell => ?_, fun n hn => ?_⟩
  · rw [cuspHeckeLinear_eigen_coefficient g' ell.property.1.ne_zero (θ ell) (hgood' ell),
      hnorm, mul_one]
  · rw [cuspHeckeLinear_eigen_coefficient g' hn (a n) (hall' n), hnorm, mul_one]
    exact hall' n

end
end Dubon2026
