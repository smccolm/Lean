import Dubon2026.PrimitivePrimeMultiplicityOne
import Dubon2026.ModularFiniteDimension
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! DUB-17/18 -> primitive Frobenius determinant -> actual primitive-component
restriction of the rational Weil pairing. The already proved original-level
good-prime multiplicity-one theorem and native Artinian finite intersection
select finitely many permitted Hecke equations that cut out exactly the
primitive cusp line. No newness or spectral-isolation premise is added. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]

theorem exists_primitive_finite_good_eigensystem (f : PrimitiveCuspForm N 2) :
    ∃ s : Finset {q : Nat.Primes // q.val.Coprime N},
      ∀ g : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2,
        (∀ q ∈ s, cuspHeckeLinear N 2 q.val.val g =
          cuspCoefficients f.toCuspForm q.val.val • g) ↔
        g = cuspCoefficients g 1 • f.toCuspForm := by
  classical
  letI : FiniteDimensional ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) :=
    ModularDimension.cuspForm_finiteDimensional (Gamma0 N) 2
  let F (q : {q : Nat.Primes // q.val.Coprime N}) :=
    Module.End.eigenspace (cuspHeckeLinear N 2 q.val.val)
      (cuspCoefficients f.toCuspForm q.val.val)
  obtain ⟨s, hs⟩ := Finset.exists_inf_le F
  refine ⟨s, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    apply primitiveCuspForm_good_prime_eigensystem_scalar f g
    intro q hq hqN
    have hmem : g ∈ s.inf F := Submodule.mem_finsetInf.mpr fun i hi =>
      Module.End.mem_eigenspace_iff.mpr (hg i hi)
    exact Module.End.mem_eigenspace_iff.mp (hs ⟨⟨q, hq⟩, hqN⟩ hmem)
  · intro hg q _
    apply Module.End.mem_eigenspace_iff.mp
    change g ∈ F q
    rw [hg]
    apply Submodule.smul_mem
    exact Module.End.mem_eigenspace_iff.mpr
      (primitiveCuspForm_eigenvector f q.val.property.pos q.property)

end
end Dubon2026
