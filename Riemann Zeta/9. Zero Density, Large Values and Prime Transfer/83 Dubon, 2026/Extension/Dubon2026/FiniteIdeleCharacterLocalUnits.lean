import Dubon2026.FiniteAdelicLocalUnitHom
import Dubon2026.FiniteIdeleDirichletContinuity
import Dubon2026.FiniteAdelicLocalIntegral

/-! # Actual local integral units away from the Dirichlet modulus have trivial idèle character -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- Inserting an original integral local unit value gives an everywhere-integral finite adele. -/
theorem finiteAdeleLocalUnit_integral (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : u.val ∈ v.adicCompletionIntegers ℚ) :
    (finiteAdeleLocalUnit v u).val ∈ finiteAdeleIntegerSubring := by
  intro w
  change finiteAdelePlace w (finiteAdeleLocalUnit v u).val ∈ w.adicCompletionIntegers ℚ
  by_cases h : w = v
  · subst w
    have he := congrArg Units.val (finiteAdeleLocalUnit_same v u)
    change finiteAdelePlace v (finiteAdeleLocalUnit v u).val = u.val at he
    rw [he]
    exact hu
  · have he := congrArg Units.val (finiteAdeleLocalUnit_ne v w h u)
    change finiteAdelePlace w (finiteAdeleLocalUnit v u).val = 1 at he
    rw [he]
    exact (w.adicCompletionIntegers ℚ).one_mem

/-- The inverse value of the actual inserted unit remains integral when the original local inverse is integral. -/
theorem finiteAdeleLocalUnit_inverse_integral (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : u.inv ∈ v.adicCompletionIntegers ℚ) :
    (finiteAdeleLocalUnit v u).inv ∈ finiteAdeleIntegerSubring := by
  have he := congrArg Units.val ((finiteAdeleLocalUnitHom v).map_inv u)
  change (finiteAdeleLocalUnit v u⁻¹).val = (finiteAdeleLocalUnit v u).inv at he
  rw [← he]
  exact finiteAdeleLocalUnit_integral v u⁻¹ hu

/-- Away from the modulus, the actual inserted local integral unit is congruent to one in the original global residue ring. -/
theorem finiteAdeleLocalUnit_congruent_one (D : ℕ) [NeZero D] (v : HeightOneSpectrum ℤ)
    (hD : (D : ℤ) ∉ v.asIdeal) (u : (v.adicCompletion ℚ)ˣ)
    (hu : u.val ∈ v.adicCompletionIntegers ℚ) :
    finiteAdeleLevelMultiple D ((finiteAdeleLocalUnit v u).val - 1) := by
  apply (finiteAdeleLevelMultiple_iff D _).mpr
  intro w
  change algebraMap ℚ (w.adicCompletion ℚ) ((D : ℚ)⁻¹) *
    (finiteAdelePlace w (finiteAdeleLocalUnit v u).val - 1) ∈ w.adicCompletionIntegers ℚ
  by_cases h : w = v
  · subst w
    have he := congrArg Units.val (finiteAdeleLocalUnit_same v u)
    change finiteAdelePlace v (finiteAdeleLocalUnit v u).val = u.val at he
    rw [he]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem
      (finitePlace_inverse_level_integral D v hD)
      ((v.adicCompletionIntegers ℚ).toSubring.sub_mem hu (v.adicCompletionIntegers ℚ).one_mem)
  · have he := congrArg Units.val (finiteAdeleLocalUnit_ne v w h u)
    change finiteAdelePlace w (finiteAdeleLocalUnit v u).val = 1 at he
    rw [he, sub_self, mul_zero]
    exact (w.adicCompletionIntegers ℚ).zero_mem

/-- The constructed original finite Dirichlet character is unramified at every actual place away from its modulus. -/
theorem finiteIdeleDirichletCharacter_local_integral {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (v : HeightOneSpectrum ℤ) (hD : (D : ℤ) ∉ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : u.val ∈ v.adicCompletionIntegers ℚ)
    (hui : u.inv ∈ v.adicCompletionIntegers ℚ) :
    finiteIdeleDirichletCharacter χ (finiteAdeleLocalUnit v u) = 1 :=
  finiteIdeleDirichletCharacter_congruence_one χ _ (finiteAdeleLocalUnit_integral v u hu)
    (finiteAdeleLocalUnit_inverse_integral v u hui) (finiteAdeleLocalUnit_congruent_one D v hD u hu)

end
end Dubon2026
