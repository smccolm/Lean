import Dubon2026.ArtinianAlgebraPointKernelOrbit
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-! # Actual finite-group invariants distinguish geometric point orbits -/

namespace Dubon2026
noncomputable section
open scoped Pointwise

variable {K A G : Type*} [Field K] [CommRing A] [Algebra K A]
  [Module.Finite K A] [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G K A]

/-- Two original algebra-valued points with the same restriction to the literal finite-group invariant subalgebra differ by the given group action. The pinned invariant-ring prime-orbit theorem and actual point kernels derive the conclusion. -/
theorem finiteGroupInvariantPoint_sameRestriction_orbit (p q : A →ₐ[K] K)
    (h : p.comp (FixedPoints.subalgebra K A G).val =
      q.comp (FixedPoints.subalgebra K A G).val) :
    ∃ g : G, p.comp (MulSemiringAction.toAlgHom K A g) = q := by
  let S := FixedPoints.subalgebra K A G
  letI : Algebra.IsInvariant S A G := ⟨fun a ha => ⟨⟨a, ha⟩, rfl⟩⟩
  letI : SMulCommClass G S A := ⟨fun g s a => by
    change g • (s.val * a) = s.val * (g • a)
    rw [smul_mul', s.property g]⟩
  let P := RingHom.ker p.toRingHom
  let Q := RingHom.ker q.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime p.toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime q.toRingHom
  have hPQ : P.under S = Q.under S := by
    ext s
    change p s.val = 0 ↔ q s.val = 0
    rw [show p s.val = q s.val from AlgHom.congr_fun h s]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq S A G P Q hPQ
  let r := p.comp (MulSemiringAction.toAlgHom K A g⁻¹)
  have hk : RingHom.ker r.toRingHom = RingHom.ker q.toRingHom := by
    ext a
    change g⁻¹ • a ∈ P ↔ a ∈ Q
    rw [hg]
    exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.symm
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, he⟩ := artinianAlgebraPoint_sameKernel_galois r q hk
  refine ⟨g⁻¹, ?_⟩
  apply AlgHom.ext
  intro a
  calc
    r a = e (r a) := (e.commutes (r a)).symm
    _ = q a := AlgHom.congr_fun he a

end
end Dubon2026
