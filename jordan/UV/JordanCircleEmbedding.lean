import Schoenflies.Curve
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
A continuous injective map from the actual complex unit circle gives the interval
parameterization used by the Schoenflies library's definition of a Jordan curve.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace UV

/-- The usual once-around traversal, with its values in the actual unit circle. -/
def unitCircleTraversal (t : ℝ) : sphere (0 : ℂ) 1 :=
  ⟨circleMap 0 1 (2 * Real.pi * t), circleMap_mem_sphere 0 (by norm_num) _⟩

theorem continuous_unitCircleTraversal : Continuous unitCircleTraversal := by
  apply Continuous.subtype_mk
  exact (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)

theorem unitCircleTraversal_closes : unitCircleTraversal 0 = unitCircleTraversal 1 := by
  apply Subtype.ext
  simp [unitCircleTraversal, circleMap, Complex.exp_two_pi_mul_I]

theorem unitCircleTraversal_injOn : InjOn unitCircleTraversal (Ico 0 1) := by
  intro s hs t ht hst
  have heq : circleMap 0 1 (2 * Real.pi * s) = circleMap 0 1 (2 * Real.pi * t) :=
    congrArg Subtype.val hst
  have hangle : 2 * Real.pi * s = 2 * Real.pi * t := by
    apply injOn_circleMap_of_abs_sub_le' (by norm_num : (1 : ℝ) ≠ 0)
      (by simp : 2 * Real.pi - 0 ≤ 2 * Real.pi)
    · exact ⟨mul_nonneg Real.two_pi_pos.le hs.1,
        (mul_lt_mul_of_pos_left hs.2 Real.two_pi_pos).trans_eq (mul_one _)⟩
    · exact ⟨mul_nonneg Real.two_pi_pos.le ht.1,
        (mul_lt_mul_of_pos_left ht.2 Real.two_pi_pos).trans_eq (mul_one _)⟩
    · exact heq
  exact mul_left_cancel₀ Real.two_pi_pos.ne' hangle

theorem unitCircleTraversal_image : unitCircleTraversal '' unitInterval = univ := by
  apply eq_univ_of_forall
  intro z
  have hz : (z : ℂ) ∈ circleMap 0 1 '' Ioc 0 (2 * Real.pi) := by
    simpa only [image_circleMap_Ioc, abs_one] using z.property
  obtain ⟨θ, hθ, hθz⟩ := hz
  refine ⟨θ / (2 * Real.pi), ?_, ?_⟩
  · exact ⟨div_nonneg hθ.1.le Real.two_pi_pos.le,
      (div_le_one Real.two_pi_pos).2 hθ.2⟩
  · apply Subtype.ext
    change circleMap 0 1 (2 * Real.pi * (θ / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ Real.two_pi_pos.ne', hθz]

/-- A genuine embedded unit circle is a Jordan curve in the external plane model. -/
theorem isJordanCurve_of_circle_embedding
    (h : ℂ ≃ₜ Schoenflies.Plane)
    (e : sphere (0 : ℂ) 1 → ℂ) (he : Continuous e) (hi : Function.Injective e) :
    Schoenflies.IsJordanCurve (h '' range e) := by
  refine ⟨fun t => h (e (unitCircleTraversal t)), ?_, ?_⟩
  · exact ⟨(h.continuous.comp (he.comp continuous_unitCircleTraversal)).continuousOn,
      congrArg (fun z => h (e z)) unitCircleTraversal_closes,
      fun s hs t ht hst => unitCircleTraversal_injOn hs ht (hi (h.injective hst))⟩
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e (unitCircleTraversal t), ⟨unitCircleTraversal t, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      have hz : z ∈ unitCircleTraversal '' unitInterval := by
        rw [unitCircleTraversal_image]
        trivial
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨t, ht, rfl⟩

/-- The same geometric image supplies the Jordan certificate for any chosen traversal. -/
theorem isJordanCurve_of_circle_embedding_range
    (h : ℂ ≃ₜ Schoenflies.Plane)
    (e : sphere (0 : ℂ) 1 → ℂ) (he : Continuous e) (hi : Function.Injective e)
    {S : Set ℂ} (hS : S = range e) : Schoenflies.IsJordanCurve (h '' S) := by
  rw [hS]
  exact isJordanCurve_of_circle_embedding h e he hi

end UV
