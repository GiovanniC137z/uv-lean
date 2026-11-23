import UV.ContinueCollarGreen
import UV.ContinueRoughCurvatureCycles

/-! The actual quartic-collar Green factors in the radial coordinate
z=(r⁻³−1)/3 and the absolute curvature insertion at a vertex. -/

noncomputable section
open Real MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.Frobenius
namespace UV.RoughCurvature

def collarDepth (r : ℝ) : ℝ := ((r^3)⁻¹ - 1) / 3

def collarModeGreen (j : ℤ) (z w : ℝ) : ℝ :=
  if j = 0 then min z w else
    (exp (-|(j:ℝ)| * |z-w|) - exp (-|(j:ℝ)| * (z+w))) / (2 * |(j:ℝ)|)

theorem collarModeGreen_nonnegative (j : ℤ) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ collarModeGreen j z w := by
  unfold collarModeGreen
  split_ifs with hj
  · exact le_min hz hw
  · apply div_nonneg _ (by positivity)
    apply sub_nonneg.mpr (exp_le_exp.mpr _)
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (abs_nonneg _))
    exact abs_le.2 ⟨by linarith, by linarith⟩

def collarNeutralScale (j : ℤ) (z : ℝ) : ℝ :=
  if j = 0 then sqrt (1+3*z) else 1

theorem collarNeutralScale_nonnegative (j : ℤ) (z : ℝ) :
    0 ≤ collarNeutralScale j z := by unfold collarNeutralScale; split <;> positivity

theorem collarModeGreen_upper (j : ℤ) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    collarModeGreen j z w ≤ angularWeight j * collarNeutralScale j z * collarNeutralScale j w := by
  by_cases hj : j = 0
  · simp only [collarModeGreen, angularWeight, collarNeutralScale, hj, if_true, one_mul]
    have h₁ : min z w ≤ sqrt (1+3*z) * sqrt (1+3*w) := by
      apply (sq_le_sq₀ (le_min hz hw) (by positivity)).1
      rw [mul_pow, sq_sqrt (by positivity), sq_sqrt (by positivity), pow_two]
      exact mul_le_mul ((min_le_left _ _).trans (by linarith))
        ((min_le_right _ _).trans (by linarith)) (le_min hz hw) (by positivity)
    exact h₁
  · simp only [collarModeGreen, angularWeight, collarNeutralScale, hj, if_false, mul_one]
    rw [← one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (sub_le_self _ (exp_pos _).le).trans (exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (abs_nonneg _)) (abs_nonneg _)))

/-- The normalized zero-mean profile pays for at most one adjacent
neutral interval at each vertex. Two neutral intervals force the
zeroth Fourier coefficient. -/
theorem collar_vertex_neutral_bound {z : ℝ} (hz : 0 ≤ z) {a : ℤ → ℂ} (ha : a 0 = 0)
    (j k : ℤ) :
    collarNeutralScale j z * collarNeutralScale k z * ‖a (j-k)‖
      ≤ sqrt (1+3*z) * ‖a (j-k)‖ := by
  by_cases hj : j = 0 <;> by_cases hk : k = 0
  · simp [hj,hk,ha]
  · simp [collarNeutralScale,hj,hk]
  · simp [collarNeutralScale,hj,hk]
  · simp only [collarNeutralScale,hj,hk,if_false,one_mul]
    have hQ : (1:ℝ) ≤ sqrt (1+3*z) := calc
      _ = sqrt 1 := sqrt_one.symm
      _ ≤ _ := sqrt_le_sqrt (by linarith)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ (norm_nonneg (a (j-k)))

def collarVertexWeight (z : ℝ) := (1+3*z)^(-2:ℝ)
def collarVertexMajorant (z : ℝ) := (1+3*z)^(-3/2:ℝ)

theorem collar_vertex_weight_exact {z : ℝ} (hz : 0 ≤ z) :
    collarVertexWeight z * sqrt (1+3*z) = collarVertexMajorant z := by
  rw [collarVertexWeight, sqrt_eq_rpow, ← rpow_add (by positivity : 0 < 1+3*z), collarVertexMajorant]
  norm_num

theorem collar_green_is_actual_charged (j : ℤ) (hj : j ≠ 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    UV.CollarEigenmode.green (|(j:ℝ)|/3) r s =
      r^2*s^2 * collarModeGreen j (collarDepth r) (collarDepth s) := by
  wlog h : r ≤ s generalizing r s
  · rw [UV.CollarEigenmode.green_symm, this hs hr (le_of_not_ge h)]
    rw [mul_comm (s^2)]
    simp only [collarModeGreen,if_neg hj,abs_sub_comm (collarDepth s) (collarDepth r),
      add_comm (collarDepth s) (collarDepth r)]
  have hjR : 0 < |(j:ℝ)| := by
    apply abs_pos.2
    exact_mod_cast hj
  have hdepth : collarDepth s ≤ collarDepth r := by
    unfold collarDepth
    have hh := inv_anti₀ (pow_pos hr 3) (pow_le_pow_left₀ hr.le h 3)
    linarith
  let a := |(j:ℝ)|
  have ha : a ≠ 0 := hjR.ne'
  unfold UV.CollarEigenmode.green UV.CollarEigenmode.rightSolution UV.CollarEigenmode.barrier
  rw [min_eq_left h, max_eq_right h, collarModeGreen, if_neg hj, abs_of_nonneg (sub_nonneg.mpr hdepth)]
  have hA : -(a/3)/r^3 + (-(-(a/3)))/s^3 = -a*(collarDepth r - collarDepth s) := by
    unfold collarDepth
    ring
  have hB : -(a/3)/r^3 + (2*(a/3) + (-(a/3))/s^3) = -a*(collarDepth r + collarDepth s) := by
    unfold collarDepth
    ring
  change (r^2*exp (-(a/3)/r^3) * (s^2*exp (-(-(a/3))/s^3) - exp (2*(a/3))*(s^2*exp (-(a/3)/s^3))))/(6*(a/3)) =
    r^2*s^2 * ((exp (-a*(collarDepth r-collarDepth s)) - exp (-a*(collarDepth r+collarDepth s)))/(2*a))
  rw [← hA, ← hB, exp_add, exp_add, exp_add]
  ring

def collarCyclicWeight {n : ℕ} (z : Fin (n+1) → ℝ)
    (a : Fin (n+1) → ℤ → ℂ) (k : Fin (n+1) → ℤ) : ℝ :=
  ∏ i, collarVertexWeight (z i) * ‖a i (k i - k (i+1))‖ *
    collarModeGreen (k (i+1)) (z i) (z (i+1))

theorem collarCyclicWeight_nonneg {n : ℕ} {z : Fin (n+1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (a : Fin (n+1) → ℤ → ℂ) (k : Fin (n+1) → ℤ) :
    0 ≤ collarCyclicWeight z a k := by
  unfold collarCyclicWeight
  exact Finset.prod_nonneg (fun i _ => mul_nonneg (mul_nonneg (rpow_nonneg (by linarith [hz i]) _) (norm_nonneg _))
    (collarModeGreen_nonnegative _ (hz i) (hz _)))

private theorem cyclic_prod_shift {n : ℕ} (g : Fin (n+1) → ℝ) :
    (∏ i, g (i+1)) = ∏ i, g i :=
  Equiv.prod_comp (Equiv.addRight (1 : Fin (n+1))) g

/-- Pointwise domination of a closed route before any angular or radial
integration. The same mode belongs to both ends of each edge. -/
theorem collar_cyclic_route_bound {n : ℕ} (z : Fin (n+1) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (a : Fin (n+1) → ℤ → ℂ) (ha : ∀ i, a i 0 = 0) (k : Fin (n+1) → ℤ) :
    collarCyclicWeight z a k ≤
      ∏ i, collarVertexMajorant (z i) * (sqrt (angularWeight (k i)*angularWeight (k (i+1))) * ‖a i (k i - k (i+1))‖) := by
  let f := fun i => collarVertexWeight (z i) * ‖a i (k i-k (i+1))‖
  let h := fun i => angularWeight (k i)
  let N := fun j i => collarNeutralScale (k j) (z i)
  have hh (i) : 0 ≤ h i := angularWeight_nonneg _
  have hf (i) : 0 ≤ f i := mul_nonneg (rpow_nonneg (by linarith [hz i]) _) (norm_nonneg _)
  have hN (i j) : 0 ≤ N j i := collarNeutralScale_nonnegative _ _
  have hroot : (∏ i, h (i+1)) = ∏ i, sqrt (h i * h (i+1)) := by
    rw [cyclic_prod_shift]
    simp_rw [sqrt_mul (hh _), Finset.prod_mul_distrib]
    rw [cyclic_prod_shift (fun i => sqrt (h i)), ← Finset.prod_mul_distrib]
    simp_rw [mul_self_sqrt (hh _)]
  calc
    _ ≤ ∏ i, f i * (h (i+1) * N (i+1) i * N (i+1) (i+1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (hf i) (collarModeGreen_nonnegative _ (hz i) (hz _))
      · intro i _
        exact mul_le_mul_of_nonneg_left (collarModeGreen_upper _ (hz i) (hz _)) (hf i)
    _ = ∏ i, sqrt (h i*h (i+1)) * (collarVertexWeight (z i) * (N i i*N (i+1) i*‖a i (k i-k (i+1))‖)) := by
      simp_rw [Finset.prod_mul_distrib]
      rw [hroot, cyclic_prod_shift (fun i => N i i)]
      simp_rw [f, Finset.prod_mul_distrib]
      ring
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (sqrt_nonneg _) (mul_nonneg (rpow_nonneg (by linarith [hz i]) _)
          (mul_nonneg (mul_nonneg (hN _ _) (hN _ _)) (norm_nonneg _)))
      · intro i _
        rw [← collar_vertex_weight_exact (hz i)]
        have hineq := mul_le_mul_of_nonneg_left (collar_vertex_neutral_bound (hz i) (ha i) (k i) (k (i+1)))
          (show 0 ≤ sqrt (h i*h (i+1))*collarVertexWeight (z i) from
            mul_nonneg (sqrt_nonneg _) (rpow_nonneg (by linarith [hz i]) _))
        calc
          _ = _ := by ring
          _ ≤ _ := hineq
          _ = _ := by dsimp only [h]; ring

end UV.RoughCurvature
