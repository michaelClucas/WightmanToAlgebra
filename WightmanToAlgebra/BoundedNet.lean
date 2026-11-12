import WightmanToAlgebra.Main

/-! Stretch 3: a net of von Neumann algebras from a Wightman theory, under explicit
hypotheses.

Bounded local data: for each region `O` a set `S(O)` of bounded operators (the intended
example: spectral projections of the closures of hermitian smeared fields `φ(l, f)`,
`tsupport f ⊆ O`), closed under adjoints, monotone in `O`, commuting at spacelike
separation (strong locality: this is the hypothesis that does not follow from W3), and
covariant under `U(g)`. The local algebra is the double commutant
`M(O) = S(O)''`, a von Neumann algebra. The field `affiliated` ties `S(O)` to the
Wightman fields: every bounded operator commuting with `S(O)` and preserving the
domain commutes on the domain with the fields localised in `O` (i.e. those fields are
affiliated with `M(O)`); this rules out degenerate choices such as `S(O) = ∅`. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- `U(g)` for Poincaré coordinates `g`. -/
def unitaryOf (T : WightmanTheory H Labels) (g : PoincareCoordinates) : H.Operator :=
  T.poincare.onStates (T.poincare.coordinates.symm g)

/-- Hypotheses for the bounded net. -/
structure BoundedLocalData (T : WightmanTheory H Labels) where
  S : Region → Set H.Operator
  adjoint_mem {O : Region} {A : H.Operator} : A ∈ S O → ContinuousLinearMap.adjoint A ∈ S O
  mono {O₁ O₂ : Region} : O₁.carrier ⊆ O₂.carrier → S O₁ ⊆ S O₂
  commute {O₁ O₂ : Region} : CausallyDisjoint O₁.carrier O₂.carrier →
    ∀ A ∈ S O₁, ∀ B ∈ S O₂, Commute A B
  covariant (g : PoincareCoordinates) (O : Region) :
    (fun A ↦ unitaryOf T g * A * ContinuousLinearMap.adjoint (unitaryOf T g)) '' S O =
      S (O.map g)
  affiliated (O : Region) (l : Labels.carrier) (f : TestFunction)
      (hf : tsupport (f : Spacetime → ℂ) ⊆ O.carrier) (B : H.Operator)
      (hB : ∀ A ∈ S O, Commute A B)
      (hD : Set.MapsTo B (T.fields.domain : Set H.carrier) T.fields.domain)
      (u : T.fields.domain) :
    B (T.fields.field l f u).1 = (T.fields.field l f ⟨B u.1, hD u.2⟩).1

/-- `M(O) = S(O)''`. -/
def boundedAlgebra {T : WightmanTheory H Labels} (B : BoundedLocalData T) (O : Region) :
    StarSubalgebra ℂ H.Operator :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (B.S O) : Set H.Operator)

theorem boundedAlgebra_mono {T : WightmanTheory H Labels} (B : BoundedLocalData T)
    {O₁ O₂ : Region} (h : O₁.carrier ⊆ O₂.carrier) : boundedAlgebra B O₁ ≤ boundedAlgebra B O₂ :=
  StarSubalgebra.centralizer_le _ _ _ (StarSubalgebra.centralizer_le _ _ _ (B.mono h))

/-- The von Neumann net `O ↦ S(O)''`, with the subalgebra inclusions. -/
def boundedNet {T : WightmanTheory H Labels} (B : BoundedLocalData T) : Net where
  Alg O := boundedAlgebra B O
  incl h := StarSubalgebra.inclusion (boundedAlgebra_mono B h)

section BoundedAux

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- A *-automorphism carries commutants to commutants, pointwise. -/
theorem mem_centralizer_map (φ : A ≃⋆ₐ[ℂ] A) (s : Set A) (x : A) :
    φ x ∈ StarSubalgebra.centralizer ℂ (φ '' s) ↔ x ∈ StarSubalgebra.centralizer ℂ s := by
  simp only [StarSubalgebra.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · intro h g hg
    obtain ⟨h1, h2⟩ := h hg
    rw [← map_star, ← map_mul, ← map_mul] at h2
    rw [← map_mul, ← map_mul] at h1
    exact ⟨φ.injective h1, φ.injective h2⟩
  · intro h g hg
    obtain ⟨h1, h2⟩ := h g hg
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, h2]
    exact ⟨rfl, rfl⟩

theorem image_centralizer (φ : A ≃⋆ₐ[ℂ] A) (s : Set A) :
    φ '' (StarSubalgebra.centralizer ℂ s : Set A) = StarSubalgebra.centralizer ℂ (φ '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_centralizer_map φ s x).2 hx
  · intro hy
    refine ⟨φ.symm y, (mem_centralizer_map φ s _).1 ?_, φ.apply_symm_apply y⟩
    rw [φ.apply_symm_apply]
    exact hy

theorem mem_double_centralizer_map (φ : A ≃⋆ₐ[ℂ] A) (s : Set A) (x : A) :
    φ x ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (φ '' s) : Set A) ↔
      x ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A) := by
  rw [← image_centralizer, mem_centralizer_map]

/-- Restriction of a *-automorphism to subalgebras it maps onto each other. -/
def restrictStarAlgEquiv (φ : A ≃⋆ₐ[ℂ] A) (M N : StarSubalgebra ℂ A)
    (h : ∀ x, φ x ∈ N ↔ x ∈ M) : M ≃⋆ₐ[ℂ] N where
  toFun a := ⟨φ a, (h a).2 a.2⟩
  invFun b := ⟨φ.symm b, (h _).1 (by rw [φ.apply_symm_apply]; exact b.2)⟩
  left_inv a := Subtype.ext (φ.symm_apply_apply a)
  right_inv b := Subtype.ext (φ.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul φ a b)
  map_add' a b := Subtype.ext (map_add φ a b)
  map_star' a := Subtype.ext (map_star φ a)
  map_smul' c a := Subtype.ext (map_smul φ c a)

end BoundedAux

theorem unitaryOf_mul_inv (T : WightmanTheory H Labels) (g : PoincareCoordinates) :
    unitaryOf T g * unitaryOf T (poincareInv g) = 1 := by
  ext x
  exact PoincareActionAux.onStates_apply_apply T.poincare
    (PoincareActionAux.symm_mul_symm_inv T.poincare g) x

theorem unitaryOf_mem (T : WightmanTheory H Labels) (g : PoincareCoordinates) :
    unitaryOf T g ∈ unitary H.Operator := by
  have h1 : ContinuousLinearMap.adjoint (unitaryOf T g) * unitaryOf T g = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (T.poincare.unitary _)
  refine Unitary.mem_iff.2 ⟨by rw [ContinuousLinearMap.star_eq_adjoint]; exact h1, ?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint]
  calc unitaryOf T g * ContinuousLinearMap.adjoint (unitaryOf T g)
      = unitaryOf T g * ContinuousLinearMap.adjoint (unitaryOf T g) *
          (unitaryOf T g * unitaryOf T (poincareInv g)) := by
        rw [unitaryOf_mul_inv, mul_one]
    _ = unitaryOf T g * (ContinuousLinearMap.adjoint (unitaryOf T g) * unitaryOf T g) *
          unitaryOf T (poincareInv g) := by
        simp only [mul_assoc]
    _ = 1 := by rw [h1, mul_one, unitaryOf_mul_inv]

theorem unitaryOf_one (T : WightmanTheory H Labels) : unitaryOf T poincareOne = 1 := by
  rw [unitaryOf, PoincareActionAux.symm_poincareOne, T.poincare.identity]
  rfl

theorem unitaryOf_poincareMul (T : WightmanTheory H Labels) (g h : PoincareCoordinates) :
    unitaryOf T (poincareMul g h) = unitaryOf T g * unitaryOf T h := by
  rw [unitaryOf, PoincareActionAux.symm_poincareMul, T.poincare.composition]
  rfl

/-- `Ad U(g)` as a *-automorphism of `B(H)`. -/
def adU (T : WightmanTheory H Labels) (g : PoincareCoordinates) :
    H.Operator ≃⋆ₐ[ℂ] H.Operator :=
  Unitary.conjStarAlgAut ℂ H.Operator ⟨unitaryOf T g, unitaryOf_mem T g⟩

theorem adU_apply (T : WightmanTheory H Labels) (g : PoincareCoordinates) (A : H.Operator) :
    adU T g A = unitaryOf T g * A * ContinuousLinearMap.adjoint (unitaryOf T g) := rfl

theorem adU_mem_iff {T : WightmanTheory H Labels} (B : BoundedLocalData T)
    (g : PoincareCoordinates) (O : Region) (x : H.Operator) :
    adU T g x ∈ boundedAlgebra B (O.map g) ↔ x ∈ boundedAlgebra B O := by
  have himg : (adU T g) '' B.S O = B.S (O.map g) := by
    rw [← B.covariant g O]
    rfl
  unfold boundedAlgebra
  rw [← himg, mem_double_centralizer_map]

/-- Covariance `A ↦ U(g) A U(g)*`. -/
def boundedCovariance (T : WightmanTheory H Labels) (hT : T.Axioms) (B : BoundedLocalData T) :
    (boundedNet B).Covariance where
  act g O := restrictStarAlgEquiv (adU T g) (boundedAlgebra B O) (boundedAlgebra B (O.map g))
    (adU_mem_iff B g O)

theorem boundedCovariance_apply (T : WightmanTheory H Labels) (hT : T.Axioms)
    (B : BoundedLocalData T) (g : PoincareCoordinates) (O : Region)
    (a : boundedAlgebra B O) :
    ((show boundedAlgebra B (O.map g) from (boundedCovariance T hT B).act g O a) : H.Operator) =
      unitaryOf T g * (a : H.Operator) * ContinuousLinearMap.adjoint (unitaryOf T g) := by
  rfl

/-- Stretch 3: Haag–Kastler (isotony, Einstein causality, covariance) for the von
Neumann net under the explicit hypotheses `BoundedLocalData`. -/
theorem bounded_haagKastler (T : WightmanTheory H Labels) (hT : T.Axioms)
    (B : BoundedLocalData T) :
    (boundedNet B).Isotony ∧ (boundedNet B).EinsteinCausality ∧
      (boundedNet B).Covariant (boundedCovariance T hT B) := by
  refine ⟨⟨fun h ↦ StarSubalgebra.inclusion_injective _, fun O ↦ StarAlgHom.ext fun _ ↦ rfl,
    fun _ _ ↦ StarAlgHom.ext fun _ ↦ rfl⟩, ?_, ⟨?_, ?_, ?_⟩⟩
  · intro O₁ O₂ O h₁ h₂ hd a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    apply Subtype.ext
    show a * b = b * a
    have hS : B.S O₁ ⊆ (StarSubalgebra.centralizer ℂ (B.S O₂) : Set H.Operator) :=
      fun A hA ↦ StarSubalgebra.mem_centralizer_iff.2 fun g hg ↦
        ⟨(B.commute hd A hA g hg).eq.symm, (B.commute hd A hA _ (B.adjoint_mem hg)).eq.symm⟩
    have hb' : b ∈ StarSubalgebra.centralizer ℂ (B.S O₁) :=
      StarSubalgebra.centralizer_le _ _ hS hb
    exact ((StarSubalgebra.mem_centralizer_iff.1 ha) b hb').1.symm
  · intro g O₁ O₂ h a
    rfl
  · intro O a
    obtain ⟨a, ha⟩ := a
    apply Subtype.ext
    show adU T poincareOne a = a
    rw [adU_apply, unitaryOf_one, ← ContinuousLinearMap.star_eq_adjoint, star_one, one_mul,
      mul_one]
  · intro g h O a
    obtain ⟨a, ha⟩ := a
    apply Subtype.ext
    show adU T g (adU T h a) = adU T (poincareMul g h) a
    rw [adU_apply, adU_apply, adU_apply, unitaryOf_poincareMul,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, star_mul]
    simp only [mul_assoc]

end WightmanToAlgebra
