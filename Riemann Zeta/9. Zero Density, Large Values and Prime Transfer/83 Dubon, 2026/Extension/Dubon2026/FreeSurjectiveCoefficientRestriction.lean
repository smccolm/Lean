import Dubon2026.FreeAuxiliaryModuleAnnihilator
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A surjective coefficient action identifies its target with the source
modulo the annihilator of a faithful module. Actual auxiliary-module freeness
therefore gives the precise quotient freeness required by the reused patching
theorem, without treating quotient freeness as an additional arithmetic input. -/

namespace Dubon2026
noncomputable section

/-- A faithful module over a surjective coefficient image identifies the
source modulo its module annihilator with that image. -/
def faithfulRestrictedModuleQuotientEquiv
    {Λ B M : Type*} [CommRing Λ] [CommRing B] [AddCommGroup M]
    [Module B M] [FaithfulSMul B M] (f : Λ →+* B) (hf : Function.Surjective f) :
    letI : Module Λ M := Module.compHom M f
    Λ ⧸ Module.annihilator Λ M ≃+* B :=
  letI : Module Λ M := Module.compHom M f
  (Ideal.quotEquivOfEq (faithfulRestrictedModule_annihilator (M := M) f)).trans
    (f.quotientKerEquivOfSurjective hf)

/-- The annihilator quotient comparison preserves the original scalar map. -/
theorem faithfulRestrictedModuleQuotientEquiv_mk
    {Λ B M : Type*} [CommRing Λ] [CommRing B] [AddCommGroup M]
    [Module B M] [FaithfulSMul B M] (f : Λ →+* B) (hf : Function.Surjective f) (x : Λ) :
    letI : Module Λ M := Module.compHom M f
    faithfulRestrictedModuleQuotientEquiv (M := M) f hf
      (Ideal.Quotient.mk (Module.annihilator Λ M) x) = f x := by
  simp only [faithfulRestrictedModuleQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Freeness over the actual coefficient image gives freeness over the source
modulo the annihilator, for its canonical quotient module structure. -/
theorem freeRestrictedModule_quotientAnnihilator
    {Λ B M : Type*} [CommRing Λ] [CommRing B] [AddCommGroup M] [Nontrivial M]
    [Module B M] [Module.Free B M] (f : Λ →+* B) (hf : Function.Surjective f) :
    letI : Module Λ M := Module.compHom M f
    letI : Module (Λ ⧸ Module.annihilator Λ M) M := Module.quotientAnnihilator (R := Λ) (M := M)
    Module.Free (Λ ⧸ Module.annihilator Λ M) M := by
  letI : Module Λ M := Module.compHom M f
  letI : Module (Λ ⧸ Module.annihilator Λ M) M := Module.quotientAnnihilator (R := Λ) (M := M)
  let e := faithfulRestrictedModuleQuotientEquiv (M := M) f hf
  apply Module.Free.of_basis ((Module.Free.chooseBasis B M).mapCoeffs e.symm ?_)
  intro b m
  obtain ⟨x, rfl⟩ := hf b
  have he : e.symm (f x) = Ideal.Quotient.mk (Module.annihilator Λ M) x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (faithfulRestrictedModuleQuotientEquiv_mk (M := M) f hf x).symm
  rw [he]
  rfl

/-- The annihilator quotient preserves the actual module rank, so a uniform
rank bound over the auxiliary algebras transfers without an additional bound. -/
theorem faithfulRestrictedModule_quotient_rank
    {Λ B M : Type} [CommRing Λ] [CommRing B] [AddCommGroup M]
    [Module B M] [FaithfulSMul B M] (f : Λ →+* B) (hf : Function.Surjective f) :
    letI : Module Λ M := Module.compHom M f
    letI : Module (Λ ⧸ Module.annihilator Λ M) M := Module.quotientAnnihilator (R := Λ) (M := M)
    Module.rank (Λ ⧸ Module.annihilator Λ M) M = Module.rank B M := by
  letI : Module Λ M := Module.compHom M f
  letI : Module (Λ ⧸ Module.annihilator Λ M) M := Module.quotientAnnihilator (R := Λ) (M := M)
  let e := faithfulRestrictedModuleQuotientEquiv (M := M) f hf
  apply rank_eq_of_equiv_equiv e (AddEquiv.refl M) e.bijective
  intro c m
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  change Ideal.Quotient.mk (Module.annihilator Λ M) x • m =
    e (Ideal.Quotient.mk (Module.annihilator Λ M) x) • m
  rw [faithfulRestrictedModuleQuotientEquiv_mk]
  rfl

end
end Dubon2026
