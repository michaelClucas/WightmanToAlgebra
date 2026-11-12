import WightmanToAlgebra.PolynomialNet

/-! Locality of the polynomial algebras: W3 makes `P(A)` and `P(B)` commute
elementwise when `A` and `B` are causally disjoint. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- Generators localised in causally disjoint sets commute, by W3. -/
theorem localGenerators_commute (F : FieldSystem H Labels) (hF : F.LocalCommutativity)
    {A B : Set Spacetime} (hAB : CausallyDisjoint A B) {X Y : Module.End ℂ F.domain}
    (hX : X ∈ localGenerators F A) (hY : Y ∈ localGenerators F B) : X * Y = Y * X := by
  obtain ⟨l, f, hf, rfl⟩ := hX
  obtain ⟨l', f', hf', rfl⟩ := hY
  have hsep : FieldSystem.SpacelikeSeparated f f' := fun x hx y hy => hAB x (hf hx) y (hf' hy)
  exact LinearMap.ext fun v => hF l l' f f' hsep v

/-- Polynomial algebras of causally disjoint sets commute elementwise. -/
theorem polynomialAlgebra_commute (F : FieldSystem H Labels) (hF : F.LocalCommutativity)
    {A B : Set Spacetime} (hAB : CausallyDisjoint A B) {X Y : Module.End ℂ F.domain}
    (hX : X ∈ polynomialAlgebra F A) (hY : Y ∈ polynomialAlgebra F B) : Commute X Y := by
  have h₂ : polynomialAlgebra F B ≤ Subalgebra.centralizer ℂ (localGenerators F A) :=
    Algebra.adjoin_le fun Y hY X hX => localGenerators_commute F hF hAB hX hY
  have h₁ : polynomialAlgebra F A ≤
      Subalgebra.centralizer ℂ (polynomialAlgebra F B : Set (Module.End ℂ F.domain)) :=
    Algebra.adjoin_le fun X hX Y hY => (h₂ hY X hX).symm
  exact (h₁ hX Y hY).symm

end WightmanToAlgebra
