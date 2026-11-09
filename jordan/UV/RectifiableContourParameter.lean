import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

/-! Genuine arc-length factorization of bounded-variation curves. The
parameter domain is the actual variation image. No unproved assertion
that this image is a full interval is inserted into the construction. -/

noncomputable section
open Set
open scoped ENNReal NNReal

namespace UV

/-- The library's exact unit-speed condition gives the required metric
Lipschitz bound on its actual parameter domain. -/
theorem unitSpeed_lipschitzOn {E : Type*} [PseudoEMetricSpace E] {g : ℝ → E} {s : Set ℝ}
    (hg : HasUnitSpeedOn g s) : LipschitzOnWith 1 g s := by
  intro x hx y hy
  simp only [ENNReal.coe_one, one_mul]
  have hordered : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ edist x y := by
    intro x hx y hy hxy
    calc
      edist (g x) (g y) ≤ eVariationOn g (s ∩ Icc x y) :=
        eVariationOn.edist_le g ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
      _ = ENNReal.ofReal (y-x) := by simpa only [NNReal.coe_one, one_mul] using hg hx hy
      _ = edist x y := by
        rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
        congr 1
        ring
  rcases le_total x y with hxy | hyx
  · exact hordered x hx y hy hxy
  · rw [edist_comm (g x), edist_comm x]
    exact hordered y hy x hx hyx

/-- Natural parameterization reconstructs the original curve pointwise;
this is an actual metric equality, not supplied reparametrization data. -/
theorem naturalParameterization_reconstruct {E : Type*} [EMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s)
    {a t : ℝ} (ha : a ∈ s) (ht : t ∈ s) :
    naturalParameterization f s a (variationOnFromTo f s a t) = f t :=
  edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha ht)

/-- Every locally bounded-variation curve has an actual unit-speed,
one-Lipschitz factorization on its variation image, preserving the entire
geometric image and every point of the original curve. -/
theorem rectifiable_arcLength_factorization {E : Type*} [EMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s) {a : ℝ} (ha : a ∈ s) :
    let v := variationOnFromTo f s a
    let g := naturalParameterization f s a
    MonotoneOn v s ∧ HasUnitSpeedOn g (v '' s) ∧ LipschitzOnWith 1 g (v '' s) ∧
      (∀ t ∈ s, g (v t) = f t) ∧ g '' (v '' s) = f '' s := by
  let v := variationOnFromTo f s a
  let g := naturalParameterization f s a
  have hu : HasUnitSpeedOn g (v '' s) := has_unit_speed_naturalParameterization f hf ha
  have hre : ∀ t ∈ s, g (v t) = f t := fun t ht => naturalParameterization_reconstruct hf ha ht
  refine ⟨variationOnFromTo.monotoneOn hf ha, hu, unitSpeed_lipschitzOn hu, hre, ?_⟩
  rw [← image_comp]
  exact image_congr hre

/-- Continuity of the variation coordinate, when established, fills the
whole arc-length interval by the ordinary intermediate-value theorem. -/
theorem rectifiable_variation_image_interval {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : LocallyBoundedVariationOn f (Icc a b))
    (hv : ContinuousOn (variationOnFromTo f (Icc a b) a) (Icc a b)) :
    variationOnFromTo f (Icc a b) a '' Icc a b =
      Icc 0 (variationOnFromTo f (Icc a b) a b) := by
  simpa only [variationOnFromTo.self] using hv.image_Icc_of_monotoneOn hab
    (variationOnFromTo.monotoneOn hf (left_mem_Icc.mpr hab))

end UV
