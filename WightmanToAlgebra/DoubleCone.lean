import WightmanToAlgebra.Regions

/-! Open double cones `{y | ‖spatial y‖ + |time y| < r}` centred at the origin, and
directedness of the set of regions. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills Set

theorem spatial_sub (x y : Spacetime) : spatial (x - y) = spatial x - spatial y := by
  ext i
  simp [spatial]

theorem time_sub (x y : Spacetime) : time (x - y) = time x - time y := by
  simp [time]

theorem spatial_zero : spatial 0 = 0 := by
  ext i
  simp [spatial]

theorem time_zero : time 0 = 0 := by
  simp [time]

theorem continuous_spatial : Continuous spatial := by
  unfold spatial
  fun_prop

theorem continuous_time : Continuous time := by
  unfold time
  fun_prop

theorem norm_sq_eq_spatial_time (x : Spacetime) :
    ‖x‖ ^ 2 = ‖spatial x‖ ^ 2 + time x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [spatial, time, Real.norm_eq_abs, sq_abs]
  rfl

theorem norm_spatial_le (x : Spacetime) : ‖spatial x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_spatial_time x
  have : ‖spatial x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (time x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem abs_time_le (x : Spacetime) : |time x| ≤ ‖x‖ := by
  have h := norm_sq_eq_spatial_time x
  have : |time x| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg ‖spatial x‖]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem norm_le_spatial_add_time (x : Spacetime) : ‖x‖ ≤ ‖spatial x‖ + |time x| := by
  have h := norm_sq_eq_spatial_time x
  have : ‖x‖ ^ 2 ≤ (‖spatial x‖ + |time x|) ^ 2 := by
    rw [h, add_sq, sq_abs]
    nlinarith [norm_nonneg (spatial x), abs_nonneg (time x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (abs_nonneg _)) two_ne_zero).mp this

/-- The open double cone of radius `r` centred at the origin. -/
def doubleConeSet (r : ℝ) : Set Spacetime := {y | ‖spatial y‖ + |time y| < r}

theorem doubleConeSet_isOpen (r : ℝ) : IsOpen (doubleConeSet r) :=
  isOpen_lt ((continuous_norm.comp continuous_spatial).add
    (continuous_abs.comp continuous_time)) continuous_const

theorem doubleConeSet_bounded (r : ℝ) : Bornology.IsBounded (doubleConeSet r) := by
  refine (Metric.isBounded_ball (x := (0 : Spacetime)) (r := r)).subset fun y hy ↦ ?_
  rw [Metric.mem_ball, dist_zero_right]
  exact (norm_le_spatial_add_time y).trans_lt hy

theorem doubleConeSet_nonempty {r : ℝ} (hr : 0 < r) : (doubleConeSet r).Nonempty :=
  ⟨0, by simp [doubleConeSet, spatial_zero, time_zero, hr]⟩

theorem doubleConeSet_causallyConvex (r : ℝ) : CausallyConvex (doubleConeSet r) := by
  intro x hx z hz y hxy hyz
  simp only [CausalLE, forwardCone, mem_setOf_eq, spatial_sub, time_sub] at hxy hyz
  simp only [doubleConeSet, mem_setOf_eq] at hx hz ⊢
  have h1 : ‖spatial y‖ ≤ ‖spatial x‖ + ‖spatial y - spatial x‖ := by
    have := norm_add_le (spatial x) (spatial y - spatial x)
    rwa [add_sub_cancel] at this
  have h2 : ‖spatial y‖ ≤ ‖spatial z‖ + ‖spatial z - spatial y‖ := by
    have := norm_sub_le (spatial z) (spatial z - spatial y)
    rwa [sub_sub_cancel] at this
  have hx1 := le_abs_self (time x)
  have hx2 := neg_abs_le (time x)
  have hz1 := le_abs_self (time z)
  have hz2 := neg_abs_le (time z)
  rw [← lt_sub_iff_add_lt', abs_lt]
  constructor <;> linarith

theorem doubleConeSet_subset_of_norm {r : ℝ} {y : Spacetime} (hy : 2 * ‖y‖ < r) :
    y ∈ doubleConeSet r := by
  show ‖spatial y‖ + |time y| < r
  linarith [norm_spatial_le y, abs_time_le y]

/-- The open double cone of radius `r > 0` as a region. -/
def doubleCone (r : ℝ) (hr : 0 < r) : Region where
  carrier := doubleConeSet r
  isOpen := doubleConeSet_isOpen r
  bounded := doubleConeSet_bounded r
  nonempty := doubleConeSet_nonempty hr
  causallyConvex := doubleConeSet_causallyConvex r

/-- Every bounded set lies in some double cone region. -/
theorem exists_doubleCone_superset {A : Set Spacetime} (hA : Bornology.IsBounded A) :
    ∃ (r : ℝ) (hr : 0 < r), A ⊆ (doubleCone r hr).carrier := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  refine ⟨2 * |R| + 1, by positivity, fun y hy ↦ doubleConeSet_subset_of_norm ?_⟩
  have := hR hy
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_abs_self R]

end WightmanToAlgebra
