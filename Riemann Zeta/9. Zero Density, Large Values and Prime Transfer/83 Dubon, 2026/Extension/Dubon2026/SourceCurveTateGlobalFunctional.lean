import Dubon2026.SourceCurveTateVanishing
import Dubon2026.SourceCurveGlobalResidueMap

/-! Finite principal supports suffice to sum the actual Tate pairing.
No differential or canonical-divisor infrastructure is needed for the
rational-coordinate base case. This is the linearity input for the already
proved partial-fraction span in the DUB-17/18 global residue argument. -/

noncomputable section

namespace Dubon2026.SourceCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Principal supports bound the support of the actual local Tate residues. -/
theorem tateResidue_support_finite_of_principal
    (hres : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (f g : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite)
    (hg : {v : Place K F | v.ord g ≠ 0}.Finite) :
    (Function.support (fun v : Place K F => v.tateResidue f g)).Finite := by
  refine (hf.union hg).subset ?_
  intro v hv
  by_contra hn
  have hnf : v.ord f = 0 := not_not.mp (not_or.mp hn).1
  have hng : v.ord g = 0 := not_not.mp (not_or.mp hn).2
  exact hv (v.tateResidue_of_mem (hres v)
    (v.mem_of_ord_nonneg hnf.ge) (v.mem_of_ord_nonneg hng.ge))

/-- The literal global sum against a fixed second argument, as a linear functional. -/
def globalTateFunctional
    (hres : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hfun : ∀ f : F, {v : Place K F | v.ord f ≠ 0}.Finite) (g : F) : F →ₗ[K] K where
  toFun f := ∑ᶠ v : Place K F, v.tateResidue f g
  map_add' f h := by
    rw [← finsum_add_distrib
      (tateResidue_support_finite_of_principal hres f g (hfun f) (hfun g))
      (tateResidue_support_finite_of_principal hres h g (hfun h) (hfun g))]
    exact finsum_congr fun v => v.tateResidue_add_fst (hres v) f h g
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    exact finsum_congr fun v => v.tateResidue_smul_fst (hres v) c f g

/-- Evaluation is exactly the actual global Tate residue sum. -/
theorem globalTateFunctional_apply
    (hres : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hfun : ∀ f : F, {v : Place K F | v.ord f ≠ 0}.Finite) (f g : F) :
    globalTateFunctional hres hfun g f = ∑ᶠ v : Place K F, v.tateResidue f g := rfl

end Dubon2026.SourceCurve
