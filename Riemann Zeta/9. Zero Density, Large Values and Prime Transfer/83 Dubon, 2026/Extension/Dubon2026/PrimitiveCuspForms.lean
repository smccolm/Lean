import Dubon2026.ClassicalHeckeFunctions
import Dubon2026.ModularNewspace

/-! # Actual normalized primitive cusp forms

Newness means the Petersson complement of the full oldspace. The eigenform
condition uses the literal finite Hecke function for every positive index
coprime to the level. Upgrading this to all indices is a separate theorem;
it is not assumed in the primitive-form object. No Rankin--Selberg,
Ramanujan--Petersson or Sato--Tate assertion occurs in these definitions.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset
open scoped MatrixGroups ModularForm

noncomputable section

/-- Simultaneous eigenfunction of all classical good Hecke operators. -/
def IsCuspHeckeEigenform {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ, 0 < n → Nat.Coprime n Q →
    ∃ eigenvalue : ℂ, ∀ τ, classicalHeckeFunction Q k n f τ = eigenvalue * f τ

/-- The stronger all-index eigenform property, separated from good-index newness. -/
def IsFullCuspHeckeEigenform {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ eigenvalue : ℂ, ∀ τ, classicalHeckeFunction Q k n f τ = eigenvalue * f τ

/-- A normalized primitive cusp form, using genuine holomorphy, cusp conditions,
full-oldspace orthogonality and the classical good Hecke operators. -/
structure PrimitiveCuspForm (Q : ℕ) [NeZero Q] (k : ℤ)
    extends CuspForm ((Gamma0 Q).map (mapGL ℝ)) k where
  /-- Normalization of the actual first q-expansion coefficient. -/
  normalized : cuspCoefficients toCuspForm 1 = 1
  /-- Orthogonality to the full degeneracy oldspace. -/
  isNew : toCuspForm ∈ cuspNewspace Q k
  /-- Simultaneous eigenfunction property at all good positive indices. -/
  isEigen : IsCuspHeckeEigenform toCuspForm

/-- The actual cusp form underlying a primitive form. -/
add_decl_doc PrimitiveCuspForm.toCuspForm

/-- All-index eigenbehavior implies the good-index property. -/
theorem fullCuspHeckeEigenform_good {Q : ℕ} {k : ℤ}
    {f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k} (hf : IsFullCuspHeckeEigenform f) :
    IsCuspHeckeEigenform f := fun n hn _ => hf n hn

/-- The eigenvalues of a normalized good eigenform are its actual coefficients. -/
theorem cuspHeckeEigenform_normalized_action {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1)
    (he : IsCuspHeckeEigenform f) {n : ℕ} (hn : 0 < n) (hnQ : Nat.Coprime n Q)
    (τ : ℍ) : classicalHeckeFunction Q k n f τ = cuspCoefficients f n * f τ := by
  obtain ⟨eigenvalue, heigenvalue⟩ := he n hn hnQ
  rw [heigenvalue, cusp_hecke_eigenvalue_eq_coefficient f hf hn.ne' eigenvalue heigenvalue]

/-- Normalization makes every primitive cusp form nonzero. -/
theorem primitiveCuspForm_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : f.toCuspForm ≠ 0 := by
  intro hz
  have hf := f.normalized
  change cuspCoefficientLinear Q k 1 f.toCuspForm = 1 at hf
  rw [hz, map_zero] at hf
  exact zero_ne_one hf

/-- The divisor sum collapses to the product index for coprime m,n. -/
theorem classicalHeckeCoefficient_coprime (Q : ℕ) (k : ℤ) {n m : ℕ}
    (hn : n ≠ 0) (h : Nat.Coprime n m) (a : ℕ → ℂ) :
    classicalHeckeCoefficient Q k n a m = a (n * m) := by
  rw [classicalHeckeCoefficient, Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hnd : ¬d ∣ m := fun hdm => hd1
      (Nat.eq_one_of_dvd_coprimes h (Nat.dvd_of_mem_divisors hd) hdm)
    simp [hnd]
  · intro hn1
    exact (hn1 (Nat.one_mem_divisors.mpr hn)).elim

/-- Genuine good-index Hecke eigenbehavior proves Fourier multiplicativity. -/
theorem cuspHeckeEigenform_coefficient_mul {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1)
    (he : IsCuspHeckeEigenform f) {n m : ℕ} (hn : 0 < n) (hnQ : Nat.Coprime n Q)
    (hnm : Nat.Coprime n m) :
    cuspCoefficients f (n * m) = cuspCoefficients f n * cuspCoefficients f m := by
  have hc := cusp_hecke_eigenfunction_coefficients f n (cuspCoefficients f n)
    (cuspHeckeEigenform_normalized_action f hf he hn hnQ) m
  rwa [classicalHeckeCoefficient_coprime Q k hn.ne' hnm] at hc

/-- Every normalized level-one Hecke eigenform has the actual primitive-form structure. -/
def primitiveCuspFormLevelOne {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1)
    (he : IsCuspHeckeEigenform f) : PrimitiveCuspForm 1 k where
  toCuspForm := f
  normalized := hf
  isNew := by rw [cuspNewspace_one]; trivial
  isEigen := he

end
end Dubon2026
