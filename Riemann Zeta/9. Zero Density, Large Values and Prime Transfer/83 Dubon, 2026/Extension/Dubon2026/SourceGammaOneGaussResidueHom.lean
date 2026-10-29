import Dubon2026.SourceGammaOneGaussValuation

/-! DUB-17/18 -> original Gamma1 Tate Frobenius/inertia -> original
good reduction -> literal coefficient reduction. Reuse the original
integral-fraction residue proof on the actual Gamma1 scalar-extended field.
The residue formula is independent of its integral fraction witness.
These maps and kernel/constant identities do not assert genus preservation
or good reduction; those remain subsequent mathematical obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open Polynomial IntermediateField GaussReduction

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "FF" => functionFieldOver Γ L
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_witness (f : coefficientGaussRing Γ A) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

/-- An integral numerator and denominator representing the given Gauss-ring element. -/
def wit (f : coefficientGaussRing Γ A) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A Γ f)

theorem wit_spec (f : coefficientGaussRing Γ A) :
    ϖ A (wit A Γ f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A Γ f).2 = ι A (wit A Γ f).1 :=
  Classical.choose_spec (exists_witness A Γ f)

/-- The quotient of the reduced integral fraction; `resL_eq` proves choice independence. -/
def resL (f : coefficientGaussRing Γ A) : LaurentSeries kk :=
  ϖ A (wit A Γ f).1 / ϖ A (wit A Γ f).2

theorem resL_eq {f : coefficientGaussRing Γ A} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A Γ f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A Γ f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

/-- Coefficient reduction of actual Gauss-ring elements as a Laurent-series ring homomorphism. -/
def resHom : coefficientGaussRing Γ A →+* LaurentSeries kk where
  toFun := resL A Γ
  map_one' := by
    rw [resL_eq A Γ (x := 1) (y := 1) (by simp) (by simp)]; simp
  map_mul' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A Γ f
    obtain ⟨hg, hg'⟩ := wit_spec A Γ g
    have h : (((f * g : coefficientGaussRing Γ A) : FF) : LaurentSeries L) * ι A ((wit A Γ f).2 * (wit A Γ g).2)
        = ι A ((wit A Γ f).1 * (wit A Γ g).1) := by
      rw [map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A Γ (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A Γ f * resL A Γ g
    rw [resL, resL, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    rw [resL_eq A Γ (x := 0) (y := 1) (by simp) (by simp)]; simp
  map_add' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A Γ f
    obtain ⟨hg, hg'⟩ := wit_spec A Γ g
    have h : (((f + g : coefficientGaussRing Γ A) : FF) : LaurentSeries L) * ι A ((wit A Γ f).2 * (wit A Γ g).2)
        = ι A ((wit A Γ f).1 * (wit A Γ g).2 + (wit A Γ g).1 * (wit A Γ f).2) := by
      rw [map_add, map_mul, map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A Γ (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A Γ f + resL A Γ g
    rw [resL, resL, div_add_div _ _ hf hg, map_add, map_mul, map_mul, map_mul]
    ring

theorem resHom_apply (f : coefficientGaussRing Γ A) : resHom A Γ f = resL A Γ f := rfl

theorem resHom_eq {f : coefficientGaussRing Γ A} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A Γ f = ϖ A x / ϖ A y :=
  resL_eq A Γ hy h

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ coefficientGaussRing Γ A :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A Γ ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A Γ hyF⟩ = ϖ A y := by
  rw [resHom_eq A Γ (x := y) (y := 1) (by simp) (by simp)]; simp


end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
