import WightmanToAlgebra.Main
import WightmanToAlgebra.DoubleCone

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
  obtain ⟨r, hr, h⟩ := exists_doubleCone_superset (O₁.bounded.union O₂.bounded)
  exact ⟨doubleCone r hr, Set.subset_union_left.trans h, Set.subset_union_right.trans h⟩

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

/-- `⟨π(a)Ω, π(b)Ω⟩ = ω(a* b)` computed in a region containing both. -/
theorem GNSRepresentation.inner_pi_vector {ω : N.State} (R : N.GNSRepresentation ω)
    {O O' O'' : Region} (h : O.carrier ⊆ O''.carrier) (h' : O'.carrier ⊆ O''.carrier)
    (a : N.Alg O) (b : N.Alg O') :
    inner ℂ (R.π O a R.vector).1 (R.π O' b R.vector).1 =
      ω.ω O'' (Star.star (N.incl h a) * N.incl h' b) := by
  rw [← R.compatible h a, ← R.compatible h' b, R.star, ← Module.End.mul_apply, ← map_mul,
    R.expectation]

/-- Inner products of vectors `π(a)Ω` agree in any two GNS representations. -/
theorem GNSRepresentation.inner_pi_vector_eq {ω : N.State} (R S : N.GNSRepresentation ω)
    {O O' : Region} (a : N.Alg O) (b : N.Alg O') :
    inner ℂ (R.π O a R.vector).1 (R.π O' b R.vector).1 =
      inner ℂ (S.π O a S.vector).1 (S.π O' b S.vector).1 := by
  obtain ⟨O'', h, h'⟩ := Region.exists_common O O'
  rw [R.inner_pi_vector h h', S.inner_pi_vector h h']

/-- `π(a) π(b) = π(a b)` in a region containing both. -/
theorem GNSRepresentation.pi_pi {ω : N.State} (R : N.GNSRepresentation ω)
    {O O' O'' : Region} (h : O.carrier ⊆ O''.carrier) (h' : O'.carrier ⊆ O''.carrier)
    (a : N.Alg O) (b : N.Alg O') (u : R.domain) :
    R.π O a (R.π O' b u) = R.π O'' (N.incl h a * N.incl h' b) u := by
  rw [map_mul, Module.End.mul_apply, R.compatible, R.compatible]

/-- A domain vector orthogonal to all `π(b)Ω` vanishes (cyclicity). -/
theorem GNSRepresentation.eq_zero_of_inner {ω : N.State} (S : N.GNSRepresentation ω)
    (d : S.domain) (h : ∀ (O : Region) (b : N.Alg O), inner ℂ d.1 (S.π O b S.vector).1 = 0) :
    d = 0 := by
  obtain ⟨O, b, hd⟩ := S.cyclic d
  have := h O b
  rw [← hd] at this
  exact Subtype.ext (inner_self_eq_zero.mp this)

/-- GNS uniqueness (FR Thm 10). -/
theorem GNSRepresentation.equivalent {ω : N.State} (R S : N.GNSRepresentation ω) :
    R.Equivalent S := by
  choose O a ha using R.cyclic
  obtain ⟨f, hf⟩ : ∃ f : R.domain → S.domain, ∀ u, f u = S.π (O u) (a u) S.vector :=
    ⟨_, fun _ ↦ rfl⟩
  have key : ∀ u (O' : Region) (b : N.Alg O'),
      inner ℂ (f u).1 (S.π O' b S.vector).1 = inner ℂ u.1 (R.π O' b R.vector).1 := by
    intro u O' b
    rw [hf, ← R.inner_pi_vector_eq S, ← ha u]
  have map_pi : ∀ (O' : Region) (b : N.Alg O'), f (R.π O' b R.vector) = S.π O' b S.vector := by
    intro O' b
    refine sub_eq_zero.mp (S.eq_zero_of_inner _ fun O'' c ↦ ?_)
    rw [Submodule.coe_sub, inner_sub_left, key, R.inner_pi_vector_eq S, sub_self]
  have map_add : ∀ u v, f (u + v) = f u + f v := by
    intro u v
    refine sub_eq_zero.mp (S.eq_zero_of_inner _ fun O'' c ↦ ?_)
    rw [Submodule.coe_sub, Submodule.coe_add, inner_sub_left, inner_add_left, key, key, key,
      Submodule.coe_add, inner_add_left, sub_self]
  have map_smul : ∀ (z : ℂ) u, f (z • u) = z • f u := by
    intro z u
    refine sub_eq_zero.mp (S.eq_zero_of_inner _ fun O'' c ↦ ?_)
    rw [Submodule.coe_sub, Submodule.coe_smul, inner_sub_left, inner_smul_left, key, key,
      Submodule.coe_smul, inner_smul_left, sub_self]
  have iso : ∀ u v, inner ℂ (f u).1 (f v).1 = inner ℂ u.1 v.1 := by
    intro u v
    conv_lhs => rw [hf v]
    rw [key, ← ha v]
  let F : R.domain →ₗ[ℂ] S.domain :=
    { toFun := f
      map_add' := map_add
      map_smul' := map_smul }
  have hF : ∀ u, F u = f u := fun _ ↦ rfl
  have inj : Function.Injective F := by
    refine (injective_iff_map_eq_zero F).mpr fun u hu ↦ ?_
    have := iso u u
    rw [← hF, hu, ZeroMemClass.coe_zero, inner_zero_left] at this
    exact Subtype.ext (inner_self_eq_zero.mp this.symm)
  have surj : Function.Surjective F := by
    intro w
    obtain ⟨O', b, rfl⟩ := S.cyclic w
    exact ⟨R.π O' b R.vector, map_pi O' b⟩
  refine ⟨LinearEquiv.ofBijective F ⟨inj, surj⟩, fun u v ↦ ?_, ?_, fun O' c u ↦ ?_⟩
  · simp only [LinearEquiv.ofBijective_apply, hF]
    exact iso u v
  · obtain ⟨O0, -, -⟩ := R.cyclic R.vector
    simp only [LinearEquiv.ofBijective_apply, hF]
    calc f R.vector = f (R.π O0 1 R.vector) := by rw [map_one, Module.End.one_apply]
      _ = S.π O0 1 S.vector := map_pi O0 1
      _ = S.vector := by rw [map_one, Module.End.one_apply]
  · obtain ⟨O1, b, rfl⟩ := R.cyclic u
    obtain ⟨O'', h, h'⟩ := Region.exists_common O' O1
    simp only [LinearEquiv.ofBijective_apply, hF]
    rw [map_pi, R.pi_pi h h', S.pi_pi h h', map_pi]

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
