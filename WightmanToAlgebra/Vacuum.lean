import WightmanToAlgebra.Main

/-! Stretch 1: states on the net, the spectrum condition, vacuum states and GNS
representations (Fewster–Rejzner Sec. 3 Thm 10, Sec. 5.1 Def. 24, Def. 25).

The quasi-local algebra `A(M)` of FR A1 is the colimit of the net over the
directed set of regions. A state on `A(M)` is the same as a compatible family of
states on the local algebras, and a representation of `A(M)` the same as a
compatible family of representations; we state everything in that form so no
colimit construction is needed. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills MeasureTheory
open scoped ComplexOrder

/-- Any two regions lie in a common region (directedness of the index set). -/
theorem Region.exists_common (O₁ O₂ : Region) :
    ∃ O : Region, O₁.carrier ⊆ O.carrier ∧ O₂.carrier ⊆ O.carrier := by
  sorry

/-- Pure translation by `x` in Poincaré coordinates. -/
def translationCoords (x : Spacetime) : PoincareCoordinates :=
  (⟨1, properLorentz_one_mem⟩, x)

namespace Net

variable {N : Net}

/-- A state on the quasi-local algebra: normalized positive linear functionals on the
local algebras, compatible with the inclusions. -/
structure State (N : Net) where
  ω (O : Region) : N.Alg O →ₗ[ℂ] ℂ
  normalized (O : Region) : ω O 1 = 1
  positive (O : Region) (a : N.Alg O) : 0 ≤ ω O (star a * a)
  compatible {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier) (a : N.Alg O₁) :
    ω O₂ (N.incl h a) = ω O₁ a

/-- Poincaré invariance `ω ∘ α(g) = ω`. -/
def State.Invariant (ω : N.State) (α : N.Covariance) : Prop :=
  ∀ (g : PoincareCoordinates) (O : Region) (a : N.Alg O), ω.ω (O.map g) (α.act g O a) = ω.ω O a

/-- A GNS representation of `ω` (FR Thm 10): a Hilbert space `K`, a dense domain `D`,
a *-representation of the quasi-local algebra by operators on `D` (formal adjoints),
and a vector `Ω` with `D = π(A(M)) Ω` and `ω(a) = ⟨Ω, π(a) Ω⟩`. -/
structure GNSRepresentation (ω : N.State) where
  K : HilbertSpace
  domain : Submodule ℂ K.carrier
  dense : Dense (domain : Set K.carrier)
  vector : domain
  π (O : Region) : N.Alg O →ₐ[ℂ] Module.End ℂ domain
  compatible {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier) (a : N.Alg O₁) :
    π O₂ (N.incl h a) = π O₁ a
  star (O : Region) (a : N.Alg O) (u v : domain) :
    inner ℂ (π O a u).1 v.1 = inner ℂ u.1 (π O (star a) v).1
  cyclic (u : domain) : ∃ (O : Region) (a : N.Alg O), u = π O a vector
  expectation (O : Region) (a : N.Alg O) : ω.ω O a = inner ℂ vector.1 (π O a vector).1

/-- Unitary equivalence of two GNS representations on their domains: an
inner-product preserving linear bijection of the domains mapping vector to vector
and intertwining the representations. (It extends to a unitary of the Hilbert
spaces since the domains are dense.) -/
def GNSRepresentation.Equivalent {ω : N.State} (R S : N.GNSRepresentation ω) : Prop :=
  ∃ V : R.domain ≃ₗ[ℂ] S.domain,
    (∀ u v : R.domain, inner ℂ (V u).1 (V v).1 = inner ℂ u.1 v.1) ∧
    V R.vector = S.vector ∧
    ∀ (O : Region) (a : N.Alg O) (u : R.domain), V (R.π O a u) = S.π O a (V u)

/-- GNS uniqueness (FR Thm 10). -/
theorem GNSRepresentation.equivalent {ω : N.State} (R S : N.GNSRepresentation ω) :
    R.Equivalent S := by
  sorry

/-- A strongly continuous unitary representation of translations on the GNS space
that fixes the GNS vector and implements `α` on translations (FR Thm 23, Def. 24). -/
structure GNSRepresentation.TranslationImplementation {ω : N.State}
    (R : N.GNSRepresentation ω) (α : N.Covariance) where
  U : TranslationAction R.K
  fixes (x : Spacetime) : U.operator x R.vector.1 = R.vector.1
  implements (x : Spacetime) (O : Region) (a : N.Alg O) :
    U.operator x (R.π O a R.vector).1 =
      (R.π (O.map (translationCoords x)) (α.act (translationCoords x) O a) R.vector).1

/-- Spectrum condition (FR Def. 24): the joint spectrum of the translation generators
lies in the closed forward cone. Stated through the spectral measures of vector states:
for every `ψ` the function `x ↦ ⟨ψ, U(x) ψ⟩` is the Fourier transform of a finite
measure supported in the closed forward cone (`supp E ⊆ V₊` by the spectral theorem).
Fourier convention as in upstream W0 (`charFun`). -/
def GNSRepresentation.TranslationImplementation.SpectrumCondition {ω : N.State}
    {R : N.GNSRepresentation ω} {α : N.Covariance} (U : R.TranslationImplementation α) :
    Prop :=
  ∀ ψ : R.K.carrier, ∃ μ : Measure Spacetime, IsFiniteMeasure μ ∧
    (∀ x : Spacetime, charFun μ x = inner ℂ ψ (U.U.operator x ψ)) ∧ μ forwardConeᶜ = 0

/-- The state satisfies the spectrum condition (FR Def. 24). -/
def State.SpectrumCondition (ω : N.State) (α : N.Covariance) : Prop :=
  ∃ (R : N.GNSRepresentation ω) (U : R.TranslationImplementation α), U.SpectrumCondition

/-- Vacuum state (FR Def. 25), with Poincaré invariance (not only translation
invariance): spectrum condition and the GNS vector is the unique translation-invariant
vector up to scalars. -/
structure State.IsVacuum (ω : N.State) (α : N.Covariance) : Prop where
  invariant : ω.Invariant α
  vacuum : ∃ (R : N.GNSRepresentation ω) (U : R.TranslationImplementation α),
    U.SpectrumCondition ∧
    ∀ ψ : R.K.carrier, (∀ x, U.U.operator x ψ = ψ) → ∃ c : ℂ, ψ = c • R.vector.1

end Net

end WightmanToAlgebra
