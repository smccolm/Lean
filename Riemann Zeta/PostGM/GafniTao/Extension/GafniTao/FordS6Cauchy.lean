import GafniTao.FordS6Signature

/-!
# Ford equation (3.7): the exact `S_6` Cauchy step

The integral moment range is made into a finite type, so the collision-energy
argument sums only over values actually attained by equation (3.6).  Equality
of moments implies equality of Ford's mixed residue signature by the preceding
module.  Consequently the literal `S_6` collision count is bounded by the
proved `B*(m)` factor times the residue-diagonal collision count.
-/

namespace GafniTao

noncomputable section

def FordS6MomentRange
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :=
  Set.range (fun z : FordS6Half k d s P Q p r hdk =>
    fordS6Moment (p := p) (q := q) Φ z.1)

def fordS6MomentRangeMap
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    {hdk : d ≤ k} (z : FordS6Half k d s P Q p r hdk) :
    FordS6MomentRange (s := s) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) Φ hdk :=
  ⟨fordS6Moment (p := p) (q := q) Φ z.1, z, rfl⟩

def fordS6FineRangeMap
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    {hdk : d ≤ k} (z : FordS6Half k d s P Q p r hdk) :
    FordS6MomentRange (s := s) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) Φ hdk ×
      FordSourceBStarResidue k d p r :=
  (fordS6MomentRangeMap (s := s) (P := P) (Q := Q) Φ z,
    fordS6HalfResidue z)

def fordS6MomentCollisionEquivCoarsened
    {k d T s P Q p q r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ℤ) (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T) :
    FordCollisionPairs (fun z : FordS6Half k d s P Q p r hdk =>
        fordS6Moment (p := p) (q := q)
          (fordBinomialTranslateSystem Ψ c) z.1) ≃
      FordCollisionPairs
        (fordSourceBStarCoarsening
          (Moment := FordS6MomentRange (s := s) (P := P) (Q := Q)
            (p := p) (q := q) (r := r)
            (fordBinomialTranslateSystem Ψ c) hdk)
          Ψ c hp hr hk2 hkp hdk hpT ∘
            fordS6FineRangeMap (s := s) (P := P) (Q := Q)
              (p := p) (q := q) (r := r) (hdk := hdk)
              (fordBinomialTranslateSystem Ψ c)) where
  toFun z := ⟨z.1, by
    apply Prod.ext
    · exact Subtype.ext z.2
    · change fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT
          (fordS6HalfResidue z.1.1) =
        fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT
          (fordS6HalfResidue z.1.2)
      rw [fordS6_signature_eq_moment_cast Ψ c hp hr hk2 hkp hdk hpT,
        fordS6_signature_eq_moment_cast Ψ c hp hr hk2 hkp hdk hpT]
      funext j
      exact congrArg
        (fun x : ℤ => (x : ZMod (p ^ fordBStarModulusExponent d r j)))
        (congrFun z.2 (fordAboveIndex hdk j))⟩
  invFun z := ⟨z.1, by
    have h := congrArg (fun x => x.1.1) z.2
    exact h⟩
  left_inv z := by
    rcases z with ⟨⟨x, y⟩, h⟩
    rfl
  right_inv z := by
    rcases z with ⟨⟨x, y⟩, h⟩
    rfl

/-- Ford's Cauchy--Schwarz estimate for the literal equation-(3.6) moment
collisions, before identifying the residue-diagonal collisions with `L_s`. -/
theorem ford_S6_moment_collision_le_residue_diagonal
    {k d T s P Q p q r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ℤ) (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T) :
    Nat.card (FordCollisionPairs
        (fun z : FordS6Half k d s P Q p r hdk =>
          fordS6Moment (p := p) (q := q)
            (fordBinomialTranslateSystem Ψ c) z.1)) ≤
      ((k - d).factorial *
          p ^ ((r - d - 1) * (r - d) / 2 + r * d)) *
        Nat.card (FordCollisionPairs
          (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
            (p := p) (q := q) (r := r) (hdk := hdk)
            (fordBinomialTranslateSystem Ψ c))) := by
  letI : Finite (FordS6Half k d s P Q p r hdk) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (FordS6Half k d s P Q p r hdk) := Fintype.ofFinite _
  letI : Fintype (FordS6MomentRange (s := s) (P := P) (Q := Q)
      (p := p) (q := q) (r := r)
      (fordBinomialTranslateSystem Ψ c) hdk) :=
    (Set.finite_range (fun z : FordS6Half k d s P Q p r hdk =>
      fordS6Moment (p := p) (q := q)
        (fordBinomialTranslateSystem Ψ c) z.1)).fintype
  rw [Nat.card_congr
    (fordS6MomentCollisionEquivCoarsened
      Ψ c hp hr hk2 hkp hdk hpT)]
  exact ford_sourceBStar_collision_le
    Ψ c hp hr hk2 hkp hdk hdr hrk hpT
    (fordS6FineRangeMap (s := s) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) (hdk := hdk)
      (fordBinomialTranslateSystem Ψ c))

#print axioms fordS6MomentCollisionEquivCoarsened
#print axioms ford_S6_moment_collision_le_residue_diagonal

end

end GafniTao
