import Dubon2026.AdelicClassicalHeckeEigenBridge
import Dubon2026.AdelicIntertwinerClassical
import Dubon2026.PrimitivePrimeMultiplicityOne

/-! # Genuine full adelic intertwiners preserve the original primitive cusp generator line -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Every actual bounded full adelic intertwiner sends the original positive-weight primitive cusp generator to a scalar multiple of itself, by the genuine Hecke bridge and classical multiplicity one. -/
theorem adelicPrimitiveIntertwiner_generator_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hk : 0 < k)
    (A : AdelicCyclicHilbert f.toCuspForm →L[ℂ] AdelicCyclicHilbert f.toCuspForm)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f.toCuspForm g v) =
      adelicCyclicHilbertRepresentation f.toCuspForm g (A v)) :
    ∃ c : ℂ, A (adelicCyclicHilbertGenerator f.toCuspForm) = c • adelicCyclicHilbertGenerator f.toCuspForm := by
  obtain ⟨w, _, hw, F, hF, _⟩ := adelicIntertwiner_generator_classical f.toCuspForm
    (primitiveCuspForm_ne_zero f) hk A hA
  have he (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) :
      cuspHeckeLinear N k p F = cuspCoefficients f.toCuspForm p • F := by
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    apply adelicCyclic_classical_Hecke_eigen f.toCuspForm hpN w F hF
    rw [hw, ← adelicHilbertHeckeTrace_intertwiner f.toCuspForm p hpN A hA,
      adelicHilbertHeckeTrace_primitive_generator, map_smul]
  have hf := primitiveCuspForm_good_prime_eigensystem_scalar f F he
  have hwfun : w.val = cuspCoefficients F 1 • (adelicCyclicGenerator N f.toCuspForm).val := by
    rw [hF]
    calc
      _ = canonicalAdelicGL2CuspLift N k (cuspCoefficients F 1 • f.toCuspForm) :=
        congrArg (fun G : CuspForm (Gamma0 N) k => canonicalAdelicGL2CuspLift N k G) hf
      _ = _ := canonicalAdelicGL2CuspLift_smul N k (cuspCoefficients F 1) f.toCuspForm
  have hwcore : w = cuspCoefficients F 1 • adelicCyclicGenerator N f.toCuspForm := Subtype.ext hwfun
  refine ⟨cuspCoefficients F 1, ?_⟩
  rw [← hw, hwcore, map_smul]
  rfl

end
end Dubon2026
