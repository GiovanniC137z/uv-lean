import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! Actual polynomial approximation of continuous square homotopies.
Both variables are Bernstein-approximated with the same degree. Uniform
convergence follows from the vector-valued Bernstein theorem and the proved
norm contraction, rather than being a homotopy approximation premise. -/

noncomputable section
open Filter
open scoped unitInterval Topology

namespace UV

theorem bernsteinApproximation_dist_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f g : C(I, E)) :
    dist (bernsteinApproximation n f) (bernsteinApproximation n g) ≤ dist f g := by
  apply (ContinuousMap.dist_le (dist_nonneg : (0:ℝ) ≤ dist f g)).mpr
  intro x
  rw [dist_eq_norm, bernsteinApproximation.apply, bernsteinApproximation.apply,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin (n+1), ‖bernstein n k x • f (bernstein.z k) -
        bernstein n k x • g (bernstein.z k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (n+1), bernstein n k x * dist f g := by
      apply Finset.sum_le_sum
      intro k _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using
          (ContinuousMap.dist_apply_le_dist (f:=f) (g:=g) (bernstein.z k))) bernstein_nonneg
    _ = dist f g := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

def bernsteinSquareFlip (H : C(I, C(I, ℂ))) : C(I, C(I, ℂ)) :=
  (H.uncurry.comp ContinuousMap.prodSwap).curry

@[simp] theorem bernsteinSquareFlip_apply (H : C(I, C(I, ℂ))) (s t : I) :
    bernsteinSquareFlip H s t = H t s := rfl

@[simp] theorem bernsteinSquareFlip_flip (H : C(I, C(I, ℂ))) :
    bernsteinSquareFlip (bernsteinSquareFlip H) = H := by ext s t; rfl

theorem bernsteinSquareFlip_dist_le (H G : C(I, C(I, ℂ))) :
    dist (bernsteinSquareFlip H) (bernsteinSquareFlip G) ≤ dist H G := by
  apply (ContinuousMap.dist_le (dist_nonneg : (0:ℝ) ≤ dist H G)).mpr
  intro s
  apply (ContinuousMap.dist_le (dist_nonneg : (0:ℝ) ≤ dist H G)).mpr
  intro t
  exact (ContinuousMap.dist_apply_le_dist (f:=H t) (g:=G t) s).trans
    (ContinuousMap.dist_apply_le_dist (f:=H) (g:=G) t)

theorem bernsteinSquareFlip_isometry : Isometry bernsteinSquareFlip := by
  apply isometry_iff_dist_eq.mpr
  intro H G
  exact le_antisymm (bernsteinSquareFlip_dist_le H G)
    (by simpa only [bernsteinSquareFlip_flip] using
      bernsteinSquareFlip_dist_le (bernsteinSquareFlip H) (bernsteinSquareFlip G))

def bernsteinTensor (n m : ℕ) (H : C(I, C(I, ℂ))) : C(I, C(I, ℂ)) :=
  bernsteinApproximation n (bernsteinSquareFlip (bernsteinApproximation m (bernsteinSquareFlip H)))

theorem bernsteinTensor_apply (n m : ℕ) (H : C(I, C(I, ℂ))) (s t : I) :
    bernsteinTensor n m H s t =
      ∑ i : Fin (n+1), ∑ j : Fin (m+1),
        (bernstein n i s * bernstein m j t) • H (bernstein.z i) (bernstein.z j) := by
  simp [bernsteinTensor, bernsteinApproximation.apply, Finset.smul_sum, mul_assoc]

theorem bernsteinTensor_start (n m : ℕ) (H : C(I, C(I, ℂ))) :
    bernsteinTensor n m H 0 = bernsteinApproximation m (H 0) := by
  unfold bernsteinTensor
  rw [bernsteinApproximation.apply_zero]
  ext t
  simp [bernsteinApproximation.apply]

theorem bernsteinTensor_end {n : ℕ} (hn : n ≠ 0) (m : ℕ) (H : C(I, C(I, ℂ))) :
    bernsteinTensor n m H 1 = bernsteinApproximation m (H 1) := by
  unfold bernsteinTensor
  rw [bernsteinApproximation.apply_one hn]
  ext t
  simp [bernsteinApproximation.apply]

theorem bernsteinApproximation_const (n : ℕ) (z : ℂ) :
    bernsteinApproximation n (ContinuousMap.const I z) = ContinuousMap.const I z := by
  ext t
  simp only [bernsteinApproximation.apply, ContinuousMap.const_apply]
  rw [← Finset.sum_smul, bernstein.probability, one_smul]

/-- If every original slice is closed, every polynomial slice is exactly
closed, rather than merely having asymptotically equal endpoints. -/
theorem bernsteinTensor_closed {n m : ℕ} (hm : m ≠ 0)
    (H : C(I, C(I, ℂ))) (hclosed : ∀ s : I, H s 0 = H s 1) :
    ∀ s : I, bernsteinTensor n m H s 0 = bernsteinTensor n m H s 1 := by
  intro s
  let G := bernsteinSquareFlip (bernsteinApproximation m (bernsteinSquareFlip H))
  have hG : ∀ u : I, G u 0 = G u 1 := by
    intro u
    simp only [G, bernsteinSquareFlip_apply, bernsteinApproximation.apply_zero,
      bernsteinApproximation.apply_one hm]
    exact hclosed u
  change (bernsteinApproximation n G s) 0 = (bernsteinApproximation n G s) 1
  rw [bernsteinApproximation.apply]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hG]

theorem bernsteinTensor_constant_end {n : ℕ} (hn : n ≠ 0) (m : ℕ)
    (H : C(I, C(I, ℂ))) {z : ℂ} (hend : ∀ t : I, H 1 t = z) :
    bernsteinTensor n m H 1 = ContinuousMap.const I z := by
  rw [bernsteinTensor_end hn]
  have he : H 1 = ContinuousMap.const I z := by ext t; exact hend t
  rw [he, bernsteinApproximation_const]

def bernsteinTensorExtension (n m : ℕ) (H : C(I, C(I, ℂ))) (p : ℝ × ℝ) : ℂ :=
  ∑ i : Fin (n+1), ∑ j : Fin (m+1),
    (((n.choose i : ℝ) * p.1^i.val * (1-p.1)^(n-i.val)) *
      ((m.choose j : ℝ) * p.2^j.val * (1-p.2)^(m-j.val))) • H (bernstein.z i) (bernstein.z j)

theorem bernsteinTensorExtension_eq (n m : ℕ) (H : C(I, C(I, ℂ))) (s t : I) :
    bernsteinTensorExtension n m H ((s:ℝ),(t:ℝ)) = bernsteinTensor n m H s t := by
  rw [bernsteinTensor_apply]
  simp only [bernsteinTensorExtension, bernstein_apply]

/-- The actual finite double Bernstein formula is globally smooth on the
whole real plane; no smooth approximation theorem is assumed. -/
theorem bernsteinTensorExtension_contDiff (n m : ℕ) (H : C(I, C(I, ℂ))) :
    ContDiff ℝ ⊤ (bernsteinTensorExtension n m H) := by
  unfold bernsteinTensorExtension
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  fun_prop

/-- Genuine uniform convergence on the whole square in its double supremum
norm. No modulus, polynomial approximation or boundary equality is assumed. -/
theorem bernsteinTensor_uniform (H : C(I, C(I, ℂ))) :
    Tendsto (fun n : ℕ => bernsteinTensor n n H) atTop (𝓝 H) := by
  let G : ℕ → C(I, C(I, ℂ)) :=
    fun n => bernsteinSquareFlip (bernsteinApproximation n (bernsteinSquareFlip H))
  have hG : Tendsto G atTop (𝓝 H) := by
    have h := (bernsteinSquareFlip_isometry.continuous.tendsto (bernsteinSquareFlip H)).comp
      (bernsteinApproximation_uniform (bernsteinSquareFlip H))
    simpa only [bernsteinSquareFlip_flip] using h
  have hB := bernsteinApproximation_uniform H
  have hGdist : Tendsto (fun n => dist (G n) H) atTop (𝓝 (0:ℝ)) :=
    (tendsto_iff_dist_tendsto_zero (f:=G) (a:=H)).mp hG
  have hBdist : Tendsto (fun n => dist (bernsteinApproximation n H) H) atTop (𝓝 (0:ℝ)) :=
    (tendsto_iff_dist_tendsto_zero (f:=fun n => bernsteinApproximation n H) (a:=H)).mp hB
  have hbound : ∀ n,
      dist (bernsteinTensor n n H) H ≤ dist (G n) H + dist (bernsteinApproximation n H) H := by
    intro n
    exact (dist_triangle _ (bernsteinApproximation n H) H).trans
      (add_le_add_right (bernsteinApproximation_dist_le n (G n) H) _)
  apply (tendsto_iff_dist_tendsto_zero (f:=fun n : ℕ => bernsteinTensor n n H) (a:=H)).mpr
  exact squeeze_zero (fun n => dist_nonneg) hbound
    (by simpa using hGdist.add hBdist)

theorem bernsteinTensor_uniform_succ (H : C(I, C(I, ℂ))) :
    Tendsto (fun n : ℕ => bernsteinTensor (n+1) (n+1) H) atTop (𝓝 H) :=
  (bernsteinTensor_uniform H).comp (tendsto_add_atTop_nat 1)

theorem bernsteinTensor_point_dist_le (n m : ℕ) (H : C(I, C(I, ℂ))) (s t : I) :
    dist (bernsteinTensor n m H s t) (H s t) ≤ dist (bernsteinTensor n m H) H :=
  (ContinuousMap.dist_apply_le_dist (f:=bernsteinTensor n m H s) (g:=H s) t).trans
    (ContinuousMap.dist_apply_le_dist (f:=bernsteinTensor n m H) (g:=H) s)

theorem bernsteinTensorExtension_uniform (H : C(I, C(I, ℂ))) :
    TendstoUniformly
      (fun n : ℕ => fun p : I × I => bernsteinTensorExtension (n+1) (n+1) H ((p.1:ℝ),(p.2:ℝ)))
      (fun p : I × I => H p.1 p.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hdist : Tendsto (fun n : ℕ => dist (bernsteinTensor (n+1) (n+1) H) H) atTop (𝓝 (0:ℝ)) :=
    (tendsto_iff_dist_tendsto_zero
      (f:=fun n : ℕ => bernsteinTensor (n+1) (n+1) H) (a:=H)).mp (bernsteinTensor_uniform_succ H)
  have h := hdist.eventually (Iio_mem_nhds hε)
  filter_upwards [h] with n hn p
  rw [bernsteinTensorExtension_eq, dist_comm]
  exact (bernsteinTensor_point_dist_le _ _ H p.1 p.2).trans_lt hn

/-- A polynomial approximation eventually stays in every original open
homotopy domain. Compactness supplies the uniform clearance internally. -/
theorem bernsteinTensorExtension_eventually_mem (H : C(I, C(I, ℂ)))
    {U : Set ℂ} (hU : IsOpen U) (hH : ∀ s t : I, H s t ∈ U) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : I,
      bernsteinTensorExtension (n+1) (n+1) H ((s:ℝ),(t:ℝ)) ∈ U := by
  have hsub : Set.range H.uncurry ⊆ U := by
    rintro z ⟨p, rfl⟩
    exact hH p.1 p.2
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_range H.uncurry.continuous).exists_thickening_subset_open hU hsub
  have hclose := (Metric.tendstoUniformly_iff.mp (bernsteinTensorExtension_uniform H)) δ hδ
  filter_upwards [hclose] with n hn s t
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨H s t, ⟨(s,t), rfl⟩, ?_⟩
  simpa only [dist_comm] using hn (s,t)

end UV
