import Dubon2026.SourceEllipticCanonicalPrimeHom
import Dubon2026.SourceCyclicPrimeKernel
import Dubon2026.SourceEllipticPrimeAbscissaRoot

/-! Fix the specific composite-quotient prime step: its kernel is the original
cyclic subgroup's literal p-torsion, and its map is the original coordinate
map or ideal norm with target equality transport. All kernel, surjectivity,
image-order, ellipticity and exact prime polynomial claims are derived.
This fixes the objects needed for iteration and field-map compatibility on
the DUB-17/18 all-level exceptional-fiber census chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate SourceEllipticCyclicCount
noncomputable section

/-- The specific canonical prime step has the original torsion kernel and the correct cyclic image and modular relation. -/
theorem canonical_cyclic_prime_step
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (p m : ℕ) [hp : Fact p.Prime] (hpF : (p : F) ≠ 0) (hm : m ≠ 0)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = p * m) :
    let C : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = p} :=
      ⟨cyclicPrimeKernel H p, cyclicPrimeKernel_cyclic_card H hcyc hp.out.ne_zero hm hcard⟩
    letI := primeAbscissaQuotient_isElliptic W p hpF C
    let φ := primeAbscissaHom W p hpF C
    φ.ker = cyclicPrimeKernel H p ∧ Function.Surjective φ ∧
      IsAddCyclic (H.map φ) ∧ Nat.card (H.map φ) = m ∧
        (SourceFunctionField.relationAtSeed (modularPolynomial p) W.j).IsRoot
          (primeAbscissaQuotient W p C).j := by
  let C : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = p} :=
    ⟨cyclicPrimeKernel H p, cyclicPrimeKernel_cyclic_card H hcyc hp.out.ne_zero hm hcard⟩
  have hker := primeAbscissaHom_ker W p hpF C
  have hCH : C.1 ≤ H := inf_le_left
  have hmap := cyclic_image_card_of_kernel (primeAbscissaHom W p hpF C)
    hp.out.ne_zero H hcyc hcard (hker ▸ hCH) (hker ▸ C.2.2)
  exact ⟨hker, primeAbscissaHom_surjective W p hpF C, hmap.1, hmap.2,
    primeAbscissaQuotient_isRoot W p hpF C⟩

end
end Dubon2026.SourceEllipticVelu
