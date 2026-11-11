import PublicTheory

/-! Causal structure of Minkowski space and the index set of an AQFT net.

Spacetime, the forward cone and `spacelike` are reused from the upstream
`PublicTheory` so that the AQFT statement and the Wightman statement refer to
literally the same geometry (time is the last coordinate). -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills Set Filter

/-- `CausalLE x y`: `y` lies in the closed causal future of `x`. -/
def CausalLE (x y : Spacetime) : Prop := y - x ∈ forwardCone

/-- Every point of `A` is spacelike to every point of `B`. -/
def CausallyDisjoint (A B : Set Spacetime) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x - y ∈ spacelike

/-- Order-convexity for the causal order. In Minkowski space this is
equivalent to containing every causal curve that starts and ends in `A`. -/
def CausallyConvex (A : Set Spacetime) : Prop :=
  ∀ x ∈ A, ∀ z ∈ A, ∀ y, CausalLE x y → CausalLE y z → y ∈ A

/-- A future-directed causal curve that is inextendible in both directions. -/
structure InextendibleCausalCurve where
  path : ℝ → Spacetime
  continuous : Continuous path
  causal : ∀ s t, s ≤ t → CausalLE (path s) (path t)
  toFuture : Tendsto (fun t ↦ time (path t)) atTop atTop
  toPast : Tendsto (fun t ↦ time (path t)) atBot atBot

/-- Domain of dependence: points every inextendible causal curve through which
meets `A`. -/
def dependenceDomain (A : Set Spacetime) : Set Spacetime :=
  {x | ∀ γ : InextendibleCausalCurve, x ∈ range γ.path → (range γ.path ∩ A).Nonempty}

/-- Index set of the net: nonempty open bounded causally convex regions. -/
structure Region where
  carrier : Set Spacetime
  isOpen : IsOpen carrier
  bounded : Bornology.IsBounded carrier
  nonempty : carrier.Nonempty
  causallyConvex : CausallyConvex carrier

/-! ## Poincaré action on regions -/

/-- Affine action `x ↦ Λ x + a` of `(Λ, a)`. -/
def poincareAct (g : PoincareCoordinates) (x : Spacetime) : Spacetime :=
  g.1.val.val x + g.2

theorem properLorentz_mul_mem (Λ M : ProperLorentz) :
    LinearMap.det (Λ.val * M.val).val.toLinearMap = 1 ∧
    (∀ x, minkowskiSquare ((Λ.val * M.val).val x) = minkowskiSquare x) ∧
    (∀ x, (Λ.val * M.val).val x ∈ forwardCone ↔ x ∈ forwardCone) := by
  sorry

theorem properLorentz_one_mem :
    LinearMap.det (1 : (Spacetime →L[ℝ] Spacetime)ˣ).val.toLinearMap = 1 ∧
    (∀ x, minkowskiSquare ((1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x) = minkowskiSquare x) ∧
    (∀ x, (1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x ∈ forwardCone ↔ x ∈ forwardCone) := by
  sorry

def poincareOne : PoincareCoordinates := (⟨1, properLorentz_one_mem⟩, 0)

/-- Group law in coordinates, matching `PoincareAction.productCoordinates`. -/
def poincareMul (g h : PoincareCoordinates) : PoincareCoordinates :=
  (⟨g.1.val * h.1.val, properLorentz_mul_mem g.1 h.1⟩, g.1.val.val h.2 + g.2)

theorem poincareAct_isOpen (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : IsOpen A) : IsOpen (poincareAct g '' A) := by
  sorry

theorem poincareAct_bounded (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : Bornology.IsBounded A) : Bornology.IsBounded (poincareAct g '' A) := by
  sorry

theorem poincareAct_causallyConvex (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : CausallyConvex A) : CausallyConvex (poincareAct g '' A) := by
  sorry

namespace Region

def map (g : PoincareCoordinates) (O : Region) : Region where
  carrier := poincareAct g '' O.carrier
  isOpen := poincareAct_isOpen g O.isOpen
  bounded := poincareAct_bounded g O.bounded
  nonempty := O.nonempty.image _
  causallyConvex := poincareAct_causallyConvex g O.causallyConvex

theorem map_mono (g : PoincareCoordinates) {O₁ O₂ : Region}
    (h : O₁.carrier ⊆ O₂.carrier) : (O₁.map g).carrier ⊆ (O₂.map g).carrier :=
  image_mono h

theorem map_one (O : Region) : (O.map poincareOne).carrier = O.carrier := by
  sorry

theorem map_mul (g h : PoincareCoordinates) (O : Region) :
    ((O.map h).map g).carrier = (O.map (poincareMul g h)).carrier := by
  sorry

end Region

end WightmanToAlgebra
