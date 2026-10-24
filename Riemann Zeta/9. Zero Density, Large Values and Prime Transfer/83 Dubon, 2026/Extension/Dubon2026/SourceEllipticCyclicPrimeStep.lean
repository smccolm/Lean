import Dubon2026.SourceEllipticPrimeAbscissaRoot
import Dubon2026.SourceCyclicQuotientOrder

/-! The actual inductive step for composite cyclic quotients. Starting with
an original cyclic subgroup of order p*m, construct its prime kernel, the
intrinsic elliptic quotient, and a surjective homomorphism. Its image subgroup
has order m and its j satisfies the original prime modular polynomial.
These are derived outputs, not certificates. The composite root theorem and
inertia specialization remain on the DUB-17/18 exceptional-fiber chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate SourceEllipticCyclicCount
noncomputable section

/-- A genuine prime quotient step with exact kernel, image order and original polynomial relation. -/
theorem exists_cyclic_prime_step
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (p m : ℕ) [hp : Fact p.Prime] (hpF : (p : F) ≠ 0) (hm : m ≠ 0)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = p * m) :
    ∃ C : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = p},
      C.1 ≤ H ∧ ∃ hE : (primeAbscissaQuotient W p C).IsElliptic,
        ∃ φ : W.toAffine.Point →+ (primeAbscissaQuotient W p C).toAffine.Point,
          φ.ker = C.1 ∧ Function.Surjective φ ∧
            IsAddCyclic (H.map φ) ∧ Nat.card (H.map φ) = m ∧
              (SourceFunctionField.relationAtSeed (modularPolynomial p) W.j).IsRoot
                (@WeierstrassCurve.j F _ (primeAbscissaQuotient W p C) hE) := by
  obtain ⟨C, hCH, hCc, hCn⟩ := exists_cyclic_subgroup_card_factor H hcyc hm hcard
  let C' : {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = p} :=
    ⟨C, hCc, hCn⟩
  obtain ⟨φ, hker, hsurj⟩ := exists_primeAbscissaHom W p hpF C'
  have hmap := cyclic_image_card_of_kernel φ hp.out.ne_zero H hcyc hcard
    (hker ▸ hCH) (hker ▸ hCn)
  exact ⟨C', hCH, primeAbscissaQuotient_isElliptic W p hpF C', φ, hker, hsurj,
    hmap.1, hmap.2, primeAbscissaQuotient_isRoot W p hpF C'⟩

end
end Dubon2026.SourceEllipticVelu
