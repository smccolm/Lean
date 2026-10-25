import Dubon2026.SourcePrimitiveGoodCoefficientProjection

/-! DUB-17/18 -> primitive determinant -> identification of the exact
primitive component after scalar extension. The projector built only from
good Hecke operators nevertheless has the prescribed scalar action for
every positive Hecke index, by the already proved full primitive eigenline. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2

/-- Evaluate an arithmetic polynomial at the actual finite good-prime annihilator. -/
def primitiveGoodCoefficientProjector (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : Polynomial (sourcePrimitiveCoefficientField f)) : Module.End ℂ S :=
  aeval (primitiveGoodAnnihilator N f s)
    (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ))

theorem primitive_projection_hecke_scalar (f : PrimitiveCuspForm N 2) (Q : Module.End ℂ S)
    (hQ : LinearMap.range Q = Submodule.span ℂ {f.toCuspForm}) (n : ℕ) (hn : 0 < n) :
    cuspHeckeLinear N 2 n * Q = cuspCoefficients f.toCuspForm n • Q := by
  apply LinearMap.ext
  intro x
  have hx : Q x ∈ Submodule.span ℂ {f.toCuspForm} := hQ ▸ LinearMap.mem_range_self Q x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  change cuspHeckeLinear N 2 n (Q x) = cuspCoefficients f.toCuspForm n • Q x
  rw [← hc, map_smul, primitiveCuspForm_eigenvector_all f hn]
  exact smul_comm c (cuspCoefficients f.toCuspForm n) f.toCuspForm

theorem exists_primitive_good_coefficient_hecke_projection (f : PrimitiveCuspForm N 2) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : Polynomial (sourcePrimitiveCoefficientField f)),
      P.eval 0 = 1 ∧
      primitiveGoodAnnihilator N f s * primitiveGoodCoefficientProjector N f s P = 0 ∧
      LinearMap.range (primitiveGoodCoefficientProjector N f s P) =
        Submodule.span ℂ {f.toCuspForm} ∧
      IsIdempotentElem (primitiveGoodCoefficientProjector N f s P) ∧
      ∀ n : ℕ, 0 < n → cuspHeckeLinear N 2 n * primitiveGoodCoefficientProjector N f s P =
        cuspCoefficients f.toCuspForm n • primitiveGoodCoefficientProjector N f s P := by
  obtain ⟨s, P, hP, hHP, hRange, hIdem⟩ := exists_primitive_good_coefficient_projection N f
  refine ⟨s, P, hP, hHP, hRange, hIdem, ?_⟩
  intro n hn
  exact primitive_projection_hecke_scalar N f _ hRange n hn

end
end Dubon2026
