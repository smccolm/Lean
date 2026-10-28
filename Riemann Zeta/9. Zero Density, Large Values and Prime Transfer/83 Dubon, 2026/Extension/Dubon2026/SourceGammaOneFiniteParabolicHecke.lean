import Dubon2026.SourceGammaOneFiniteParabolicH1
import Dubon2026.SourceGammaOnePeriodTateHecke

/-! DUB17/18 -> original all-weight arithmetic realization -> finite H1
and arithmetic Tate comparison. The native constant-coefficient H1
Hecke correspondence is the transpose of the actual period-lattice
Hecke action. Both sides are independently defined original operators.
The proof uses their actual common coset trace, retaining every nonzero
index and every modulus. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup groupCohomology CategoryTheory
variable (M : ℕ) [NeZero M] (n d : ℕ) [NeZero d]

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem periodLatticeHecke_latticePeriod (γ : Gamma1 M) :
    periodLatticeHecke M d (latticePeriodHom M (Additive.ofMul γ)) =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        latticePeriodHom M (Additive.ofMul (sourceGammaOneHeckeConjugation M d
          (cosetTransition (sourceGammaOneHeckeUpper M d) γ q))) := by
  apply Subtype.ext
  simpa only [periodLatticeHecke_val, latticePeriodHom, dualPeriodHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Submodule.coe_sum] using
    periodHeckeLinear_dualPeriod M d γ

theorem finiteLatticeH1Equiv_hecke
    (ψ : sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod n) :
    (finiteLatticeH1Equiv M n (ψ.comp (periodLatticeHecke M d).toAddMonoidHom)).val =
      sourceGammaOneConstantHeckeH1 (ZMod n) (ZMod n) M d LinearMap.id
        (finiteLatticeH1Equiv M n ψ).val := by
  apply (ConcreteCategory.bijective_of_isIso
    (H1IsoOfIsTrivial (Rep.trivial (ZMod n) (Gamma1 M) (ZMod n))).hom).injective
  apply AddMonoidHom.ext
  intro γ
  have hγ : γ = Additive.ofMul γ.toMul := rfl
  rw [hγ, finiteLatticeH1Equiv_hom_apply, sourceGammaOneConstantHeckeH1_hom_apply]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    periodLatticeHecke_latticePeriod, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (finiteLatticeH1Equiv_hom_apply M n ψ _).symm

theorem finiteParabolicH1_hecke_mem
    {x : H1 (Rep.trivial (ZMod n) (Gamma1 M) (ZMod n))}
    (hx : x ∈ finiteParabolicH1 M n) :
    sourceGammaOneConstantHeckeH1 (ZMod n) (ZMod n) M d LinearMap.id x ∈
      finiteParabolicH1 M n := by
  obtain ⟨ψ, hψ⟩ := (finiteLatticeH1Equiv M n).surjective ⟨x, hx⟩
  have he : (finiteLatticeH1Equiv M n ψ).val = x := congrArg Subtype.val hψ
  rw [← he, ← finiteLatticeH1Equiv_hecke]
  exact (finiteLatticeH1Equiv M n _).property

/-- Restrict the existing native finite H1 Hecke operator to the proved stable submodule. -/
def finiteParabolicHecke : Module.End (ZMod n) (finiteParabolicH1 M n) :=
  (sourceGammaOneConstantHeckeH1 (ZMod n) (ZMod n) M d LinearMap.id).restrict
    (fun _ hx => finiteParabolicH1_hecke_mem M n d hx)

theorem finiteLatticeH1Equiv_hecke_restrict
    (ψ : sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod n) :
    finiteLatticeH1Equiv M n (ψ.comp (periodLatticeHecke M d).toAddMonoidHom) =
      finiteParabolicHecke M n d (finiteLatticeH1Equiv M n ψ) :=
  Subtype.ext (finiteLatticeH1Equiv_hecke M n d ψ)

end
end Dubon2026.SourceFunctionField.GammaOne
