import GafniTao.FordFiniteCollision

/-!
# Ford Lemma 3.2: Cauchy--Schwarz over the exact `B*` fibres

This file identifies the fibres of Ford's mixed residue signature with the
literal `B*(m)` type and applies the finite collision inequality.  Thus the
factor in the Cauchy--Schwarz step is the proved source bound, not an abstract
cardinality hypothesis.
-/

namespace GafniTao

noncomputable section

def FordSourceBStarResidue (k d p r : ℕ) :=
  Σ _tail : Fin d → ZMod (p ^ r),
    {head : Fin (k - d) → ZMod (p ^ r) //
      Function.Injective (fun i => fordPrimeReduction (head i))}

def fordSourceBStarSignature
    {k d T p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (z : FordSourceBStarResidue k d p r) :
    ∀ j : Fin (k - d), ZMod (p ^ fordBStarModulusExponent d r j) :=
  fun j =>
    fordPrimePowerCastHom p r (fordBStarModulusExponent d r j)
        (fordBStarModulusExponent_le j)
        (fordPolynomialEvalSum
            ((fordTranslatedSystemAboveModPrimePower
              Ψ c hp hr hk2 hkp hdk hpT).1 j) z.2.1 +
          fordPolynomialEvalSum
            ((fordTranslatedSystemAboveModPrimePower
              Ψ c hp hr hk2 hkp hdk hpT).1 j) z.1)

def fordSourceBStarFiberEquiv
    {k d T p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :
    FordMapFiber
        (fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT) m ≃
      FordSourceBStarCongruence Ψ c hp hr hk2 hkp hdk hpT m where
  toFun z := ⟨z.1.1, ⟨z.1.2.1, z.1.2.2, fun j => congrFun z.2 j⟩⟩
  invFun z :=
    ⟨⟨z.1, ⟨z.2.1, z.2.2.1⟩⟩, funext z.2.2.2⟩
  left_inv z := by
    rcases z with ⟨⟨tail, head, hinj⟩, hsig⟩
    rfl
  right_inv z := by
    rcases z with ⟨tail, head, hinj, hsig⟩
    rfl

def fordSourceBStarCoarsening
    {k d T p r : ℕ} {Moment : Type*}
    (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T) :
    Moment × FordSourceBStarResidue k d p r →
      Moment × (∀ j : Fin (k - d),
        ZMod (p ^ fordBStarModulusExponent d r j)) :=
  fun z => (z.1,
    fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT z.2)

def fordSourceBStarCoarseningFiberEquiv
    {k d T p r : ℕ} {Moment : Type*}
    (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (target : Moment × (∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j))) :
    FordMapFiber
        (fordSourceBStarCoarsening (Moment := Moment)
          Ψ c hp hr hk2 hkp hdk hpT) target ≃
      FordSourceBStarCongruence
        Ψ c hp hr hk2 hkp hdk hpT target.2 where
  toFun z := by
    have hm : z.1.1 = target.1 := congrArg Prod.fst z.2
    have hs : fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT z.1.2 =
        target.2 := congrArg Prod.snd z.2
    exact (fordSourceBStarFiberEquiv Ψ c hp hr hk2 hkp hdk hpT target.2)
      ⟨z.1.2, hs⟩
  invFun z := by
    let residue : FordSourceBStarResidue k d p r :=
      ⟨z.1, ⟨z.2.1, z.2.2.1⟩⟩
    have hs : fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT residue =
        target.2 := funext z.2.2.2
    exact ⟨(target.1, residue), Prod.ext rfl hs⟩
  left_inv z := by
    rcases z with ⟨⟨moment, tail, head, hinj⟩, htarget⟩
    have hm : moment = target.1 := congrArg Prod.fst htarget
    subst moment
    rfl
  right_inv z := by
    rcases z with ⟨tail, head, hinj, hsig⟩
    rfl

theorem ford_sourceBStarCoarsening_fiber_card_le
    {k d T p r : ℕ} {Moment : Type*}
    (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T)
    (target : Moment × (∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j))) :
    Nat.card (FordMapFiber
        (fordSourceBStarCoarsening (Moment := Moment)
          Ψ c hp hr hk2 hkp hdk hpT) target) ≤
      (k - d).factorial *
        p ^ ((r - d - 1) * (r - d) / 2 + r * d) := by
  rw [Nat.card_congr
    (fordSourceBStarCoarseningFiberEquiv
      Ψ c hp hr hk2 hkp hdk hpT target)]
  exact ford_sourceBStarCongruence_card_le
    Ψ c hp hr hk2 hkp hdk hdr hrk hpT target.2

/-- The exact finite Cauchy--Schwarz step over Ford's literal mixed-modulus
`B*` residue signatures. -/
theorem ford_sourceBStar_collision_le
    {k d T p r : ℕ} {X Moment : Type*}
    [Fintype X] [Fintype Moment]
    (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T)
    (fine : X → Moment × FordSourceBStarResidue k d p r) :
    Nat.card (FordCollisionPairs
        (fordSourceBStarCoarsening (Moment := Moment)
          Ψ c hp hr hk2 hkp hdk hpT ∘ fine)) ≤
      ((k - d).factorial *
          p ^ ((r - d - 1) * (r - d) / 2 + r * d)) *
        Nat.card (FordCollisionPairs fine) := by
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  letI : Fact (1 < p ^ r) := ⟨one_lt_pow₀ hp.one_lt hr.ne'⟩
  letI (j : Fin (k - d)) : Fact
      (1 < p ^ fordBStarModulusExponent d r j) :=
    ⟨one_lt_pow₀ hp.one_lt (fordBStarModulusExponent_pos hdr j).ne'⟩
  letI : Finite (FordSourceBStarResidue k d p r) := by
    unfold FordSourceBStarResidue
    infer_instance
  letI : Fintype (FordSourceBStarResidue k d p r) := Fintype.ofFinite _
  letI : Fintype (∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) := Fintype.ofFinite _
  exact ford_collision_comp_le fine
    (fordSourceBStarCoarsening (Moment := Moment)
      Ψ c hp hr hk2 hkp hdk hpT)
    ((k - d).factorial *
      p ^ ((r - d - 1) * (r - d) / 2 + r * d))
    (ford_sourceBStarCoarsening_fiber_card_le
      Ψ c hp hr hk2 hkp hdk hdr hrk hpT)

#print axioms fordSourceBStarFiberEquiv
#print axioms fordSourceBStarCoarseningFiberEquiv
#print axioms ford_sourceBStarCoarsening_fiber_card_le
#print axioms ford_sourceBStar_collision_le

end

end GafniTao
