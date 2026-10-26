import Dubon2026.SourceWeightTwoFullEigenlift
import Dubon2026.CuspCoprimeOldspace
import Dubon2026.HeckeOldNewStability

/-! DUB-17/18 -> close the parabolic branch -> actual primitive form.
Inside the genuine newspace, extend the prescribed original good-prime
eigensystem using the existing commuting-family theorem. Newspace
uniqueness from coprime Fourier coefficients makes the first coefficient
nonzero, so normalization produces the actual primitive-form object. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

theorem sourceWeightTwoNewEigen_exists_primitive
    (Q M : ℕ) [NeZero Q] [NeZero M]
    (θ : sourceBinaryHeckePrime Q → ℂ)
    (f : CuspForm (Gamma0 M) 2) (hf : f ≠ 0)
    (hfnew : f ∈ cuspNewspace M 2)
    (he : ∀ ell, cuspHeckeLinear M 2 ell.val f = θ ell • f) :
    ∃ g : PrimitiveCuspForm M 2,
      ∀ ell, cuspCoefficients g.toCuspForm ell.val = θ ell := by
  letI := SourceFunctionField.original_weight_two_cusp_finite M
  let P : Submodule ℂ (CuspForm (Gamma0 M) 2) :=
    cuspNewspace M 2 ⊓
      ⨅ ell : sourceBinaryHeckePrime Q, Module.End.eigenspace (cuspHeckeLinear M 2 ell.val) (θ ell)
  have hmem (v : CuspForm (Gamma0 M) 2) :
      v ∈ P ↔ v ∈ cuspNewspace M 2 ∧
        ∀ ell, cuspHeckeLinear M 2 ell.val v = θ ell • v := by
    simp only [P, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  let J := {n : ℕ // 0 < n ∧ Nat.Coprime n M}
  have hstab (n : J) (v : CuspForm (Gamma0 M) 2) (hv : v ∈ P) :
      cuspHeckeLinear M 2 n.val v ∈ P := by
    refine (hmem _).mpr ⟨cuspNewspace_hecke_coprime n.val n.property.2 v ((hmem v).mp hv).1, ?_⟩
    intro ell
    rw [← Module.End.mul_apply, (cuspHeckeLinear_commute M 2 ell.val n.val).eq,
      Module.End.mul_apply, ((hmem v).mp hv).2 ell, map_smul]
  let T : J → Module.End ℂ P := fun n => (cuspHeckeLinear M 2 n.val).restrict (hstab n)
  have hc (m n : J) : Commute (T m) (T n) :=
    LinearMap.ext fun v => Subtype.ext
      (LinearMap.congr_fun (cuspHeckeLinear_commute M 2 m.val n.val).eq v.val)
  let v : P := ⟨f, (hmem f).mpr ⟨hfnew, he⟩⟩
  have hv : v ≠ 0 := fun h => hf (congrArg Subtype.val h)
  letI : Nontrivial P := nontrivial_of_ne v 0 hv
  obtain ⟨a, g, hg, hga⟩ := sourceCommutingOperators_exists_commonEigenvector T hc
  have hgn : g.val ∈ cuspNewspace M 2 := ((hmem g.val).mp g.property).1
  have hgood (ell : sourceBinaryHeckePrime Q) :
      cuspHeckeLinear M 2 ell.val g.val = θ ell • g.val :=
    ((hmem g.val).mp g.property).2 ell
  have hall (n : J) : cuspHeckeLinear M 2 n.val g.val = a n • g.val :=
    congrArg Subtype.val (hga n)
  have hfirst : cuspCoefficients g.val 1 ≠ 0 := by
    intro hz
    apply hg
    apply Subtype.ext
    apply cusp_new_coprime_eq_zero M 2 g.val hgn
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact cuspCoefficients_zero g.val
    · let j : J := ⟨n, Nat.pos_of_ne_zero hn0, hn.symm⟩
      rw [cuspHeckeLinear_eigen_coefficient g.val hn0 (a j) (hall j), hz, mul_zero]
  let g' := (cuspCoefficients g.val 1)⁻¹ • g.val
  have hnorm : cuspCoefficients g' 1 = 1 := by
    change cuspCoefficientLinear M 2 1 ((cuspCoefficients g.val 1)⁻¹ • g.val) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ hfirst
  have hall' (n : J) : cuspHeckeLinear M 2 n.val g' = a n • g' := by
    change cuspHeckeLinear M 2 n.val ((cuspCoefficients g.val 1)⁻¹ • g.val) = _
    rw [map_smul, hall, smul_comm]
  have hgood' (ell : sourceBinaryHeckePrime Q) :
      cuspHeckeLinear M 2 ell.val g' = θ ell • g' := by
    change cuspHeckeLinear M 2 ell.val ((cuspCoefficients g.val 1)⁻¹ • g.val) = _
    rw [map_smul, hgood, smul_comm]
  let result : PrimitiveCuspForm M 2 := {
    toCuspForm := g'
    normalized := hnorm
    isNew := (cuspNewspace M 2).smul_mem _ hgn
    isEigen := by
      intro n hn hnM
      let j : J := ⟨n, hn, hnM⟩
      refine ⟨a j, fun z => ?_⟩
      have h := congrArg (fun u : CuspForm (Gamma0 M) 2 => u z) (hall' j)
      change cuspHecke n g' z = a j * g' z at h
      rwa [cuspHecke_apply] at h }
  refine ⟨result, fun ell => ?_⟩
  change cuspCoefficients g' ell.val = θ ell
  rw [cuspHeckeLinear_eigen_coefficient g' ell.property.1.ne_zero (θ ell) (hgood' ell),
    hnorm, mul_one]

end
end Dubon2026
