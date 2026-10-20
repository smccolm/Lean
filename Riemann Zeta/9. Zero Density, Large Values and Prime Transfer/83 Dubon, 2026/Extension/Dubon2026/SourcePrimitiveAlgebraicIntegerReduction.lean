import Dubon2026.SourceIntegralReductionExtension
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! The original Hecke reduction extends to all complex algebraic integers.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular residual Galois
association -> the specialization required by the published all-weight
residual construction. This extends the actual local reduction; its Hecke
values are proved equal to the original residual eigencharacter.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original integral Hecke eigensystem valued in complex algebraic integers. -/
def sourcePrimitiveIntegralHeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalIntegralHeckeAlgebra Q k →ₐ[ℤ] integralClosure ℤ ℂ :=
  (sourcePrimitiveHeckeCharacter f).codRestrict _ (fun T => by
    exact (sourcePrimitiveFieldHeckeCharacter_isIntegral f hk T).map
      ((sourcePrimitiveCoefficientField f).val.restrictScalars ℤ))

/-- The integral eigencharacter has the exact original complex Hecke values. -/
theorem sourcePrimitiveIntegralHeckeCharacter_coe (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceOriginalIntegralHeckeAlgebra Q k) :
    (sourcePrimitiveIntegralHeckeCharacter f hk T : ℂ) = sourcePrimitiveHeckeCharacter f T :=
  rfl

/-- The given original coefficient reduction extends to all complex algebraic
integers in an algebraically closed residue field, preserving every Hecke value. -/
theorem sourcePrimitive_exists_algebraicIntegerReduction
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type*} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ T : sourceOriginalIntegralHeckeAlgebra Q k,
        φ (sourcePrimitiveIntegralHeckeCharacter f hk T) =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ T) := by
  let F := sourcePrimitiveCoefficientField f
  let A := integralClosure ℤ F
  let B := integralClosure ℤ ℂ
  let i : A →ₐ[ℤ] B := (F.val.restrictScalars ℤ).mapIntegralClosure
  letI : Algebra A B := i.toRingHom.toAlgebra
  letI : IsScalarTower ℤ A B := IsScalarTower.of_algebraMap_eq i.commutes
  letI : Algebra.IsIntegral A B :=
    ⟨fun x => (integralClosure.isIntegral x).tower_top⟩
  have hi : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : B => (b : ℂ)) hxy
  let ψ : A →+* 𝒪[E] :=
    (τ.toRingHom.comp (algebraMap A F)).codRestrict (ValuativeRel.valuation E).integer
      (fun x => by
        have hx := x.property.map (τ.restrictScalars ℤ)
        exact (Valuation.integer.integers (ValuativeRel.valuation E)).isIntegral_iff_v_le_one.mp
          hx.tower_top)
  let χ := (algebraMap 𝓀[E] K).comp ((IsLocalRing.residue 𝒪[E]).comp ψ)
  obtain ⟨φ, hφ⟩ := sourceIntegralReduction_exists_extension hi χ
  refine ⟨φ, fun T => ?_⟩
  let x : A := ⟨sourcePrimitiveFieldHeckeCharacter f T,
    sourcePrimitiveFieldHeckeCharacter_isIntegral f hk T⟩
  exact RingHom.congr_fun hφ x

private theorem residualClosureSpecialization
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    (ell : ℕ) [CharP 𝓀[E] ell]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    CharP (AlgebraicClosure 𝓀[E]) ell ∧
      ∃ φ : integralClosure ℤ ℂ →+* AlgebraicClosure 𝓀[E],
        ∀ T : sourceOriginalIntegralHeckeAlgebra Q k,
          φ (sourcePrimitiveIntegralHeckeCharacter f hk T) =
            algebraMap 𝓀[E] (AlgebraicClosure 𝓀[E])
              (sourcePrimitiveResidualHeckeCharacter f hk τ T) :=
  ⟨inferInstance, sourcePrimitive_exists_algebraicIntegerReduction
    (E := E) (K := AlgebraicClosure 𝓀[E]) f hk τ⟩

/-- At every prescribed rational prime, the actual primitive eigensystem admits
the required specialization of all algebraic integers in the algebraic closure
of its genuine finite local residue field. No coefficient specialization or
residue-characteristic assumption is supplied. -/
theorem sourcePrimitive_exists_algebraicIntegerReduction_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      CharP (AlgebraicClosure 𝓀[L]) ell ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L)
        (φ : integralClosure ℤ ℂ →+* AlgebraicClosure 𝓀[L]),
        ∀ T : sourceOriginalIntegralHeckeAlgebra Q k,
          φ (sourcePrimitiveIntegralHeckeCharacter f hk T) =
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ T) := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero ell hell
  let F := rationalPrimeLocalField ell hell
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualHeckeCharacter_charP f hk ell hell
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, hchar, hres, τ, _, _⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : CharP 𝓀[L] ell := hchar
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  have hd := residualClosureSpecialization (E := L) ell f hk τ
  exact ⟨u, v, hu, hv, hext, hfin, hres, hd.1, τ, hd.2⟩

end
end Dubon2026
