import WightmanToAlgebra.Regions

/-! Haag–Kastler axioms for a net of unital *-algebras on Minkowski space,
following Fewster–Rejzner, "Algebraic Quantum Field Theory – an introduction"
(arXiv:1904.04051).

Fewster–Rejzner allow general unital *-algebras (not only C*-algebras), which
is what makes a direct construction from Wightman fields possible: the local
algebras below can be unbounded-operator algebras on the Wightman domain.

Axioms:
* isotony: injective unital *-homomorphisms for inclusions of regions, functorial;
* Einstein causality: images of causally disjoint regions commute;
* timeslice: the inclusion is onto when the larger region lies in the domain
  of dependence of the smaller one;
* Poincaré covariance: *-isomorphisms `A(O) ≃ A(gO)` compatible with inclusions
  and the group law. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills

/-- A net of unital *-algebras indexed by regions, with the inclusion maps. -/
structure Net where
  Alg : Region → Type
  [ring : ∀ O, Ring (Alg O)]
  [algebra : ∀ O, Algebra ℂ (Alg O)]
  [starRing : ∀ O, StarRing (Alg O)]
  [starModule : ∀ O, StarModule ℂ (Alg O)]
  incl : ∀ {O₁ O₂ : Region}, O₁.carrier ⊆ O₂.carrier → Alg O₁ →⋆ₐ[ℂ] Alg O₂

attribute [instance] Net.ring Net.algebra Net.starRing Net.starModule

namespace Net

variable (N : Net)

/-- Isotony, including functoriality of the inclusion maps. -/
structure Isotony : Prop where
  injective {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier) :
    Function.Injective (N.incl h)
  refl (O : Region) : N.incl (Set.Subset.refl O.carrier) = StarAlgHom.id ℂ (N.Alg O)
  trans {O₁ O₂ O₃ : Region} (h₁₂ : O₁.carrier ⊆ O₂.carrier)
      (h₂₃ : O₂.carrier ⊆ O₃.carrier) :
    (N.incl h₂₃).comp (N.incl h₁₂) = N.incl (h₁₂.trans h₂₃)

/-- Einstein causality. -/
def EinsteinCausality : Prop :=
  ∀ {O₁ O₂ O : Region} (h₁ : O₁.carrier ⊆ O.carrier) (h₂ : O₂.carrier ⊆ O.carrier),
    CausallyDisjoint O₁.carrier O₂.carrier →
      ∀ a b, Commute (N.incl h₁ a) (N.incl h₂ b)

/-- Timeslice. -/
def Timeslice : Prop :=
  ∀ {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier),
    O₂.carrier ⊆ dependenceDomain O₁.carrier → Function.Surjective (N.incl h)

/-- Poincaré action on the net, as data. -/
structure Covariance where
  act (g : PoincareCoordinates) (O : Region) : N.Alg O ≃⋆ₐ[ℂ] N.Alg (O.map g)

/-- The covariance laws. Composition and the identity are stated through the
inclusion maps so that no casts between `Alg` of equal regions are needed. -/
structure Covariant (α : N.Covariance) : Prop where
  natural (g : PoincareCoordinates) {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier)
      (a : N.Alg O₁) :
    N.incl (Region.map_mono g h) (α.act g O₁ a) = α.act g O₂ (N.incl h a)
  one (O : Region) (a : N.Alg O) :
    α.act poincareOne O a = N.incl (Region.map_one O).symm.subset a
  mul (g h : PoincareCoordinates) (O : Region) (a : N.Alg O) :
    α.act g (O.map h) (α.act h O a) =
      N.incl (Region.map_mul g h O).symm.subset (α.act (poincareMul g h) O a)

/-- All Haag–Kastler axioms in the Fewster–Rejzner formulation. -/
structure Axioms (α : N.Covariance) : Prop where
  isotony : N.Isotony
  causality : N.EinsteinCausality
  timeslice : N.Timeslice
  covariant : N.Covariant α

end Net

end WightmanToAlgebra
