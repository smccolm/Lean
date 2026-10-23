import Dubon2026.SourceCurveLocalTateBilinear
import Dubon2026.SourceCurveResidueDual

/-! The actual local Tate pairing factors through Kaehler differentials.
The derivation is constructed from the proved bilinearity and Leibniz
identities, and the native universal property gives its exact uniformizer
coefficient formula. This is the local differential chain rule required
for residue/trace compatibility and global residue vanishing, DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Fixing the second argument gives the actual linear residue functional. -/
def tateResidueFunctional
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (g : F) : ResidueDual K F :=
  { toFun := fun f => v.tateResidue f g
    map_add' := fun f h => v.tateResidue_add_fst hres f h g
    map_smul' := fun c f => v.tateResidue_smul_fst hres c f g }

/-- The actual residue pairing, as a derivation in its second argument. -/
def tateResidueDerivation
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Derivation K F (ResidueDual K F) :=
  Derivation.mk'
    { toFun := fun g => v.tateResidueFunctional hres g
      map_add' := fun g h => residueDual_ext fun f => by
        change v.tateResidue f (g + h) = v.tateResidue f g + v.tateResidue f h
        exact v.tateResidue_add_snd hres f g h
      map_smul' := fun c g => residueDual_ext fun f => by
        change v.tateResidue f (c • g) = c • v.tateResidue f g
        exact v.tateResidue_smul_snd hres c f g }
    (fun g h => residueDual_ext fun f => by
      change v.tateResidue f (g * h) = v.tateResidue (g * f) h + v.tateResidue (h * f) g
      rw [v.tateResidue_leibniz hres, mul_comm g f, mul_comm h f])

/-- Evaluation of the constructed derivation is the literal commutator residue. -/
theorem tateResidueDerivation_apply
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g : F) :
    residueDualLinearMap K F (v.tateResidueDerivation hres g) f = v.tateResidue f g := rfl

/-- The residue pairing factors through the actual coefficient of the universal differential. -/
theorem tateResidue_eq_differentialCoeff
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates] (f g : F) :
    v.tateResidue f g =
      v.tateResidue (f * v.differentialCoeff (D K F g)) v.uniformizer := by
  let δ := v.tateResidueDerivation hres
  have hL := Derivation.liftKaehlerDifferential_comp_D δ
  have hLπ : δ.liftKaehlerDifferential v.dCoord = δ v.uniformizer := hL v.uniformizer
  have hd : δ g = v.differentialCoeff (D K F g) • δ v.uniformizer := by
    calc δ g = δ.liftKaehlerDifferential (D K F g) := (hL g).symm
      _ = δ.liftKaehlerDifferential (v.differentialCoeff (D K F g) • v.dCoord) := by
        rw [v.differentialCoeff_smul_dCoord]
      _ = v.differentialCoeff (D K F g) • δ v.uniformizer := by
        rw [map_smul, hLπ]
  have he := congrArg (fun φ : ResidueDual K F => residueDualLinearMap K F φ f) hd
  change v.tateResidue f g = v.tateResidue (v.differentialCoeff (D K F g) * f) v.uniformizer at he
  simpa only [mul_comm] using he

end Dubon2026.SourceCurve.Place
