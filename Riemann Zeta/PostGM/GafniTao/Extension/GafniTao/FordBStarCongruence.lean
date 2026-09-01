import GafniTao.FordBStarSource

/-!
# Ford Lemma 3.2: the literal mixed-congruence `B*` fibre

Ford's `B*(m)` is first defined by congruences modulo
`p^min(d+j+1,r)`.  The cardinality proof subsequently fixes the last `d`
coordinates and lifts every congruence target to modulus `p^r`.  This file
embeds the literal source fibre into that resolved count, exactly in the
direction needed for Ford's estimate.
-/

namespace GafniTao

noncomputable section

def FordSourceBStarCongruence
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :=
  Σ tail : Fin d → ZMod (p ^ r),
    {head : Fin (k - d) → ZMod (p ^ r) //
      Function.Injective (fun i => fordPrimeReduction (head i)) ∧
      ∀ j : Fin (k - d),
        fordPrimePowerCastHom p r (fordBStarModulusExponent d r j)
            (fordBStarModulusExponent_le j)
            (fordPolynomialEvalSum
                ((fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT).1 j)
                head +
              fordPolynomialEvalSum
                ((fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT).1 j)
                tail) = m j}

def fordSourceBStarToResolved
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :
    FordSourceBStarCongruence ψ c hp hr hk2 hkp hdk hpT m →
      FordSourceResolvedBStar ψ c hp hr hk2 hkp hdk hpT m := fun z => by
    let lifts : FordBStarLiftFamily p d r (k - d) m := fun j =>
      ⟨fordPolynomialEvalSum
            ((fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT).1 j)
            z.2.1 +
          fordPolynomialEvalSum
            ((fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT).1 j)
            z.1,
        z.2.2.2 j⟩
    refine ⟨z.1, lifts, ⟨⟨z.2.1, ?_⟩, z.2.2.1⟩⟩
    intro j
    change _ =
      (fordPolynomialEvalSum _ z.2.1 + fordPolynomialEvalSum _ z.1) -
        fordPolynomialEvalSum _ z.1
    abel

theorem fordSourceBStarToResolved_injective
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :
    Function.Injective
      (fordSourceBStarToResolved ψ c hp hr hk2 hkp hdk hpT m) := by
  rintro ⟨tail₁, head₁, hinj₁, hcong₁⟩
    ⟨tail₂, head₂, hinj₂, hcong₂⟩ h
  have htail : tail₁ = tail₂ := congrArg Sigma.fst h
  subst tail₂
  have hhead : head₁ = head₂ := congrArg
    (fun z : FordSourceResolvedBStar ψ c hp hr hk2 hkp hdk hpT m =>
      z.2.2.1.1) h
  subst head₂
  rfl

/-- Ford's displayed `B*` bound for the literal mixed-congruence fibre. -/
theorem ford_sourceBStarCongruence_card_le
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :
    Nat.card (FordSourceBStarCongruence ψ c hp hr hk2 hkp hdk hpT m) ≤
      (k - d).factorial *
        p ^ ((r - d - 1) * (r - d) / 2 + r * d) := by
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  letI : Fact (1 < p ^ r) := ⟨one_lt_pow₀ hp.one_lt hr.ne'⟩
  letI (j : Fin (k - d)) : Fact
      (1 < p ^ fordBStarModulusExponent d r j) :=
    ⟨one_lt_pow₀ hp.one_lt (fordBStarModulusExponent_pos hdr j).ne'⟩
  letI (j : Fin (k - d)) : Finite
      (FordPrimePowerLiftFiber p r (fordBStarModulusExponent d r j)
        (fordBStarModulusExponent_le j) (m j)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (FordBStarLiftFamily p d r (k - d) m) := by
    unfold FordBStarLiftFamily
    infer_instance
  letI (tail : Fin d → ZMod (p ^ r))
      (lifts : FordBStarLiftFamily p d r (k - d) m) : Finite
      (FordPrimePowerNonsingularTriangularFiber
        (fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT)
        (fordSourceBStarTarget ψ c hp hr hk2 hkp hdk hpT m tail lifts)) :=
    Finite.of_injective (fun x => x.1.1) (by
      intro x y h
      exact Subtype.ext (Subtype.ext h))
  letI : Finite (FordSourceResolvedBStar ψ c hp hr hk2 hkp hdk hpT m) := by
    unfold FordSourceResolvedBStar FordResolvedBStar
    infer_instance
  exact (Nat.card_le_card_of_injective
      (fordSourceBStarToResolved ψ c hp hr hk2 hkp hdk hpT m)
      (fordSourceBStarToResolved_injective ψ c hp hr hk2 hkp hdk hpT m)).trans
    (ford_source_resolvedBStar_card_le
      ψ c hp hr hk2 hkp hdk hdr hrk hpT m)

#print axioms fordSourceBStarToResolved_injective
#print axioms ford_sourceBStarCongruence_card_le

end

end GafniTao
