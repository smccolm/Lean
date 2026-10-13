import Dubon2026.NumberFieldIdeleIdeal
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # A finite support on which original ideles generate every original class

Choose original fractional-ideal representatives of the finite ordinary
class group and retain the finite union of their prime supports. For an
arbitrary original idele, its associated ideal differs from the chosen
representative by an actual principal ideal. Dividing by that same global
unit leaves an idele supported on this finite union. This avoids an
unneeded construction of ideles representing arbitrary ideals and proves
the surjectivity input to DUB-17's supported-idele and global norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]

/-- A finite enlargement of any prescribed support captures every original idele modulo an actual principal idele. -/
theorem numberField_exists_finite_principal_idele_support
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ∃ x : Kˣ,
        a / numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S := by
  classical
  let C := (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range
  letI : Finite C := Finite.of_equiv (ClassGroup (𝓞 K)) (ClassGroup.equiv K).toEquiv
  letI : Fintype C := Fintype.ofFinite C
  let q := QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range
  have hrep (c : C) : ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, q J = c :=
    QuotientGroup.mk'_surjective _ c
  choose J hJ using hrep
  have hsupport (c : C) :
      {v : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K v (J c).val ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (J c).val)
  let S := S₀ ∪ Finset.univ.biUnion (fun c : C => (hsupport c).toFinset)
  refine ⟨S, Finset.subset_union_left, ?_⟩
  intro a
  let I := numberFieldIdeleIdeal K a
  let c : C := q I
  have hq : q (I / J c) = 1 := by
    rw [map_div, hJ]
    exact div_self' _
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (I / J c)).mp hq
  refine ⟨x, ?_⟩
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro v hv
  have hJzero : FractionalIdeal.count K v (J c).val = 0 := by
    by_contra h
    apply hv
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ _, by simpa only [Set.Finite.mem_toFinset] using h⟩)
  have hc : FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K x).val =
      FractionalIdeal.count K v I.val - FractionalIdeal.count K v (J c).val := by
    rw [hx]
    rw [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [FractionalIdeal.count_mul K v I.ne_zero (inv_ne_zero (J c).ne_zero), FractionalIdeal.count_inv]
    rfl
  rw [hJzero, sub_zero] at hc
  have hord : numberFieldIdeleOrder K a v =
      numberFieldIdeleOrder K (numberFieldPrincipalIdele K x) v := by
    rw [numberFieldIdeleOrder_principal, ← numberFieldIdeleIdeal_count]
    exact hc.symm
  change -WithZero.log (Valued.v (numberFieldIdeleFiniteComponent K v a).val) =
    -WithZero.log (Valued.v (numberFieldIdeleFiniteComponent K v (numberFieldPrincipalIdele K x)).val) at hord
  have hval : Valued.v (numberFieldIdeleFiniteComponent K v a).val =
      Valued.v (numberFieldIdeleFiniteComponent K v (numberFieldPrincipalIdele K x)).val := by
    have he := congrArg WithZero.exp (neg_injective hord)
    simpa only [WithZero.exp_log (by simp : Valued.v (numberFieldIdeleFiniteComponent K v a).val ≠ 0),
      WithZero.exp_log (by simp : Valued.v (numberFieldIdeleFiniteComponent K v (numberFieldPrincipalIdele K x)).val ≠ 0)] using he
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
    map_div, Units.val_div_eq_div_val, map_div₀, hval]
  exact div_self (by simp)

end
end Dubon2026
