import Dubon2026.SourceModularQuotientIntegral
import Dubon2026.SourceOriginalAnalyticJFibers
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! DUB-17/18 -> finite-place exhaustion -> bounded original functions
integral over C[j]. The norm polynomial applies to actual Gamma0 forms;
the proved j-expansion identity identifies its coefficient ring with
the literal original C[j]. Injective subfield transport then gives
integrality inside the original field whenever multiplying the element
by a discriminant power yields the actual modular expansion.
That clearing-of-cusp-poles condition is explicit here and remains to
be derived from boundedness; this theorem does not claim that step.
The subfield transport adapts anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem isIntegral_adjoin_subfield {L F : Type*} [Field L] [Field F] [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E) (h : IsIntegral (Algebra.adjoin L {j}) x) : IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E) := by
  have hmapeq : (Algebra.adjoin L {(⟨j, hj⟩ : E)}).map E.val
      = Algebra.adjoin L {j} := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  let ψfwd : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) →ₐ[L] ↥(Algebra.adjoin L {j}) :=
    (Subalgebra.equivOfEq _ _ hmapeq).toAlgHom.comp
      (E.val.subalgebraMap (Algebra.adjoin L {(⟨j, hj⟩ : E)}))
  have hcoeF : ∀ b : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}),
      ((ψfwd b : ↥(Algebra.adjoin L {j})) : F) = ((b : E) : F) := fun b => rfl
  have hinjE : Function.Injective ((↑) : E → F) := Subtype.coe_injective
  have hbij : Function.Bijective ψfwd := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinjE (by
        have := congrArg (Subtype.val : ↥(Algebra.adjoin L {j}) → F) hab
        rwa [hcoeF a, hcoeF b] at this))
    · exact (Subalgebra.equivOfEq _ _ hmapeq).surjective.comp
        (E.val.subalgebraMap_surjective _)
  let e := RingEquiv.ofBijective ψfwd hbij
  have hcoe : ∀ a : ↥(Algebra.adjoin L {j}),
      (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F) = (a : F) := by
    intro a
    have h2 : ψfwd (e.symm a) = a := e.apply_symm_apply a
    calc (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F)
        = ((ψfwd (e.symm a) : ↥(Algebra.adjoin L {j})) : F) := (hcoeF _).symm
      _ = (a : F) := by rw [h2]
  letI : Algebra ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) F :=
    ((algebraMap E F).comp (algebraMap ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) E)).toAlgebra
  have hxT : IsIntegral ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) x :=
    IsIntegral.map_of_comp_eq e.symm.toRingHom (RingHom.id F)
      (by ext a; exact hcoe a) h
  let f : E →ₐ[↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})] F :=
    { toRingHom := (E.val : E →+* F), commutes' := fun t => rfl }
  have hinjf : Function.Injective f := hinjE
  exact (isIntegral_algHom_iff f hinjf).mp hxT

theorem isIntegral_gamma0_modular_quotient (N : ℕ) [NeZero N] (m : ℕ)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * (m : ℤ))) :
    IsIntegral (Algebra.adjoin ℂ {coeffEmb ℂ jq})
      ((qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) /
        (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m) := by
  have h := isIntegral_modular_quotient (ModularRatios.one_mem_strictPeriods N) m rfl g
  rw [← jqModC_eq_modular_quotient, ← coeffEmb_jq] at h
  exact h

theorem isIntegral_original_of_discriminant_power (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (m : ℕ)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * (m : ℤ)))
    (hx : (x : LaurentSeries ℂ) *
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m =
        (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ {jOver N ℂ}) x := by
  have hq := isIntegral_gamma0_modular_quotient N m g
  have hx' := (eq_div_iff (pow_ne_zero m discriminant_expansion_ne_zero)).mpr hx
  rw [← hx'] at hq
  exact isIntegral_adjoin_subfield (modularFunctionFieldOver N ℂ) (jOver N ℂ).2 x.2 hq

end
end Dubon2026.SourceFunctionField
