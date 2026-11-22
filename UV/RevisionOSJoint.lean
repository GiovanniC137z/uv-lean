import UV.StablePoisson

/-! The real two-source reflection test. This module constructs the spatial
Poisson-kernel witness. The identities moving the massive differential
operator through the covariance are the interface to the continuum source. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UV

abbrev OSFourSpace := EuclideanSpace ℝ (Fin 4)

/-- Actual convolution against the positive transfer kernel. -/
def osPoissonTransfer (r : ℝ) (g : OSFourSpace → ℝ) (x : OSFourSpace) : ℝ :=
  ∫ y, stablePoissonKernel r (x - y) * g y

theorem osPoissonTransfer_pos {r : ℝ} (hr : 0 < r) {g : OSFourSpace → ℝ}
    (hgc : Continuous g) (hgk : HasCompactSupport g) (hg0 : 0 ≤ g)
    (hg : ∃ y, 0 < g y) (x : OSFourSpace) : 0 < osPoissonTransfer r g x := by
  obtain ⟨y, hy⟩ := hg
  have hc : Continuous (fun y ↦ stablePoissonKernel r (x - y) * g y) :=
    ((stablePoissonKernel_continuous hr).comp (continuous_const.sub continuous_id)).mul hgc
  have hk : HasCompactSupport (fun y ↦ stablePoissonKernel r (x - y) * g y) :=
    hgk.mul_left
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport hk)
    (fun z ↦ mul_nonneg (stablePoissonKernel_pos hr _).le (hg0 z))
    (mul_pos (stablePoissonKernel_pos hr _) hy).ne'

theorem osPoissonTransfer_continuous {r : ℝ} (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hgc : Continuous g) (hgi : Integrable g) :
    Continuous (osPoissonTransfer r g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y ↦ stablePoissonKernel r 0 * ‖g y‖)
  · exact Eventually.of_forall fun z ↦ (((stablePoissonKernel_continuous hr).comp
      (continuous_const.sub continuous_id)).mul hgc).aestronglyMeasurable
  · exact Eventually.of_forall fun z ↦ Eventually.of_forall fun y ↦ by
      rw [norm_mul, Real.norm_of_nonneg (stablePoissonKernel_pos hr _).le]
      exact mul_le_mul_of_nonneg_right (stablePoissonKernel_le_zero hr _) (norm_nonneg _)
  · exact hgi.norm.const_mul _
  · exact Eventually.of_forall fun y ↦ (((stablePoissonKernel_continuous hr).comp
      (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

/-- Time reflection on four Euclidean coordinates, keeping the spatial
coordinates fixed. -/
def osTimeReflect (x : OSFourSpace) : OSFourSpace :=
  WithLp.toLp 2 (fun i ↦ if i = 0 then -x i else x i)

@[simp] theorem osTimeReflect_time (x : OSFourSpace) : osTimeReflect x 0 = -x 0 := by
  simp [osTimeReflect]

theorem osTimeReflect_continuous : Continuous osTimeReflect := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [if_pos hi]
    exact (PiLp.continuous_apply 2 _ i).neg
  · simp only [if_neg hi]
    exact PiLp.continuous_apply 2 _ i

@[simp] theorem osTimeReflect_involutive : Function.Involutive osTimeReflect := by
  intro x
  ext i
  by_cases hi : i = 0
  · subst i
    simp
  · simp [osTimeReflect, hi]

def osTimeReflectionHomeomorph : OSFourSpace ≃ₜ OSFourSpace where
  toFun := osTimeReflect
  invFun := osTimeReflect
  left_inv := osTimeReflect_involutive
  right_inv := osTimeReflect_involutive
  continuous_toFun := osTimeReflect_continuous
  continuous_invFun := osTimeReflect_continuous

/-- Separation of reflected supports makes the diagonal free pairing vanish
once the free covariance has canceled the local differential operator. -/
theorem os_local_reflected_integral_zero {u f : OSFourSpace → ℝ}
    (hu : ∀ x, x 0 ≤ 0 → u x = 0) (hf : ∀ x, x 0 ≤ 0 → f x = 0) :
    (∫ x, f (osTimeReflect x) * u x) = 0 := by
  have h : (fun x ↦ f (osTimeReflect x) * u x) = 0 := by
    funext x
    by_cases hx : x 0 ≤ 0
    · simp [hu x hx]
    · have hθ : osTimeReflect x 0 ≤ 0 := by
        rw [osTimeReflect_time]
        linarith
      simp [hf _ hθ]
  simp [h]

/-- The reflected mixed pairing of a nonzero nonnegative witness with the
positivity-improving transfer is strictly positive. -/
theorem os_poisson_mixed_reflected_pos {r : ℝ} (hr : 0 < r)
    {u g : OSFourSpace → ℝ} (hgc : Continuous g) (hgk : HasCompactSupport g)
    (hg0 : 0 ≤ g) (hg : ∃ y, 0 < g y) (hu0 : 0 ≤ u)
    (huc : Continuous u) (huk : HasCompactSupport u) (hu : ∃ x, 0 < u x) :
    0 < ∫ x, u (osTimeReflect x) * osPoissonTransfer r g x := by
  obtain ⟨x, hx⟩ := hu
  have hp := osPoissonTransfer_pos hr hgc hgk hg0 hg
  have hmc : Continuous (fun x ↦ u (osTimeReflect x) * osPoissonTransfer r g x) :=
    (huc.comp osTimeReflect_continuous).mul (osPoissonTransfer_continuous hr hgc
      (hgc.integrable_of_hasCompactSupport hgk))
  have hmk : HasCompactSupport (fun x ↦ u (osTimeReflect x) * osPoissonTransfer r g x) :=
    (huk.comp_homeomorph osTimeReflectionHomeomorph).mul_right
  have hθ : 0 < u (osTimeReflect (osTimeReflect x)) := by
    rw [osTimeReflect_involutive x]
    exact hx
  exact integral_pos_of_integrable_nonneg_nonzero hmc (hmc.integrable_of_hasCompactSupport hmk)
    (fun y ↦ mul_nonneg (hu0 _) (hp y).le) (mul_pos hθ (hp (osTimeReflect x))).ne'

/-- A null diagonal and nonzero mixed entry give an explicit negative norm
regardless of the second diagonal. The witness has second coefficient one. -/
theorem os_negative_of_zero_diagonal_nonzero_mixed {b : ℝ} (hb : b ≠ 0) (d : ℝ) :
    ∃ t : ℝ, 2 * b * t + d < 0 := by
  let t := -(|d| + 1) / (2 * b)
  have hn : 2 * b ≠ 0 := by positivity
  have ht : 2 * b * t = -(|d| + 1) := by
    dsimp [t]
    field_simp
  exact ⟨t, by rw [ht]; linarith [le_abs_self d]⟩

/-- For the real restriction of the joint form, the exact convolution and
local-support identities imply an explicit obstruction. Here the first
source has already been amputated using the free inverse identity. -/
theorem os_joint_negative_reduced_covariance {r : ℝ} (hr : 0 < r)
    {u f g : OSFourSpace → ℝ} (hup : ∀ x, x 0 ≤ 0 → u x = 0)
    (hfp : ∀ x, x 0 ≤ 0 → f x = 0)
    (hgc : Continuous g) (hgk : HasCompactSupport g) (hg0 : 0 ≤ g)
    (hg : ∃ y, 0 < g y) (hu0 : 0 ≤ u)
    (huc : Continuous u) (huk : HasCompactSupport u) (hu : ∃ x, 0 < u x)
    (d : ℝ) :
    ∃ t : ℝ, t ^ 2 * (∫ x, f (osTimeReflect x) * u x) +
      2 * (∫ x, u (osTimeReflect x) * osPoissonTransfer r g x) * t + d < 0 := by
  rw [os_local_reflected_integral_zero hup hfp]
  simp only [mul_zero, zero_add]
  exact os_negative_of_zero_diagonal_nonzero_mixed
    (os_poisson_mixed_reflected_pos hr hgc hgk hg0 hg hu0 huc huk hu).ne' d

end UV
