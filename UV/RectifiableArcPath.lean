import UV.RectifiableArcLength
import UV.RectifiableContourIntegral

/-! An actual normalized arc-length path for every continuous rectifiable
path. The construction preserves ordered traversal, endpoints, geometric
image and total variation. Its integrated speed has the original geometric
length as a proved bound. No contour-integral identity is assumed. -/

noncomputable section
open Set
open scoped NNReal ENNReal

namespace UV

variable {E : Type*} [MetricSpace E] {a b : E}

/-- The finite geometric length, as the real total variation of the given
path. Finiteness is required by the construction theorems below. -/
def rectifiablePathLength (γ : Path a b) : ℝ≥0 :=
  ⟨(eVariationOn γ.extend (Icc (0 : ℝ) 1)).toReal, ENNReal.toReal_nonneg⟩

/-- The genuine natural parameterization, rescaled to the unit interval. -/
def rectifiableArcCurve (γ : Path a b) (t : ℝ) : E :=
  naturalParameterization γ.extend (Icc (0 : ℝ) 1) 0 (rectifiablePathLength γ * t)

theorem rectifiable_scale_mem (γ : Path a b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (rectifiablePathLength γ : ℝ) * t ∈ Icc 0 (rectifiablePathLength γ : ℝ) := by
  exact ⟨mul_nonneg (rectifiablePathLength γ).property ht.1,
    by simpa using mul_le_mul_of_nonneg_left ht.2 (rectifiablePathLength γ).property⟩

theorem rectifiable_scale_image (γ : Path a b) :
    (fun t : ℝ => (rectifiablePathLength γ : ℝ) * t) '' Icc 0 1 =
      Icc 0 (rectifiablePathLength γ : ℝ) := by
  have hc : ContinuousOn (fun t : ℝ => (rectifiablePathLength γ : ℝ) * t) (Icc 0 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hm : MonotoneOn (fun t : ℝ => (rectifiablePathLength γ : ℝ) * t) (Icc 0 1) :=
    fun _ _ _ _ h => mul_le_mul_of_nonneg_left h (rectifiablePathLength γ).property
  simpa only [mul_zero, mul_one] using hc.image_Icc_of_monotoneOn zero_le_one hm

theorem rectifiableArcCurve_lipschitzOn (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    LipschitzOnWith (rectifiablePathLength γ) (rectifiableArcCurve γ) (Icc 0 1) := by
  have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
    γ.continuous_extend.continuousOn
  have hg := h.2.2.2.2.2.1
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hd := hg.dist_le_mul _ (rectifiable_scale_mem γ hx) _ (rectifiable_scale_mem γ hy)
  have hnorm : |(rectifiablePathLength γ : ℝ)| = (rectifiablePathLength γ : ℝ) :=
    abs_of_nonneg (rectifiablePathLength γ).property
  simpa only [rectifiableArcCurve, one_mul, NNReal.coe_one, Real.dist_eq,
    ← mul_sub, abs_mul, hnorm] using hd

/-- The normalized arc-length representative of the original rectifiable
path. This is a constructed `Path`, including its actual endpoint proofs. -/
def rectifiableArcPath (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) : Path a b :=
  Path.ofLine (rectifiableArcCurve_lipschitzOn γ hBV).continuousOn
    (by
      have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
        γ.continuous_extend.continuousOn
      simpa only [rectifiableArcCurve, mul_zero, Path.extend_zero] using h.2.2.2.2.2.2.2.1)
    (by
      have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
        γ.continuous_extend.continuousOn
      simpa only [rectifiableArcCurve, mul_one, rectifiablePathLength, Path.extend_one] using
        h.2.2.2.2.2.2.2.2.1)

theorem rectifiableArcPath_extend (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (rectifiableArcPath γ hBV).extend t = rectifiableArcCurve γ t := by
  rw [Path.extend_extends _ ht]
  rfl

/-- Clamping the constructed representative gives a global Lipschitz
extension with exactly the original geometric length as constant. -/
theorem rectifiableArcPath_lipschitz (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    LipschitzWith (rectifiablePathLength γ) (rectifiableArcPath γ hBV).extend := by
  have hg : LipschitzWith (rectifiablePathLength γ)
      (fun t : Icc (0 : ℝ) 1 => rectifiableArcCurve γ t) :=
    LipschitzWith.of_dist_le_mul fun x y =>
      (rectifiableArcCurve_lipschitzOn γ hBV).dist_le_mul x x.property y y.property
  simpa only [mul_one] using hg.comp (LipschitzWith.projIcc (a := (0 : ℝ)) zero_le_one)

theorem rectifiableArcPath_image (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    (rectifiableArcPath γ hBV).extend '' Icc (0 : ℝ) 1 = γ.extend '' Icc 0 1 := by
  have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
    γ.continuous_extend.continuousOn
  calc
    _ = rectifiableArcCurve γ '' Icc 0 1 := image_congr fun _ ht => rectifiableArcPath_extend γ hBV ht
    _ = naturalParameterization γ.extend (Icc (0 : ℝ) 1) 0 ''
        ((fun t : ℝ => (rectifiablePathLength γ : ℝ) * t) '' Icc 0 1) := by
      rw [← image_comp]
      rfl
    _ = γ.extend '' Icc 0 1 := by
      rw [rectifiable_scale_image]
      exact h.2.2.2.2.2.2.2.2.2.1

theorem rectifiableArcPath_variation (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    eVariationOn (rectifiableArcPath γ hBV).extend (Icc (0 : ℝ) 1) =
      eVariationOn γ.extend (Icc 0 1) := by
  have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
    γ.continuous_extend.continuousOn
  calc
    _ = eVariationOn (rectifiableArcCurve γ) (Icc 0 1) :=
      eVariationOn.eq_of_eqOn fun _ ht => rectifiableArcPath_extend γ hBV ht
    _ = eVariationOn (naturalParameterization γ.extend (Icc (0 : ℝ) 1) 0)
        ((fun t : ℝ => (rectifiablePathLength γ : ℝ) * t) '' Icc 0 1) :=
      eVariationOn.comp_eq_of_monotoneOn _ _
        (fun _ _ _ _ hxy => mul_le_mul_of_nonneg_left hxy (rectifiablePathLength γ).property)
    _ = ENNReal.ofReal (rectifiablePathLength γ : ℝ) := by
      rw [rectifiable_scale_image]
      exact h.2.2.2.2.2.2.2.2.2.2
    _ = eVariationOn γ.extend (Icc 0 1) := ENNReal.ofReal_toReal hBV

/-- The original traversal is recovered through a continuous increasing
surjection of the unit interval fixing both endpoints. The zero-length
case is handled explicitly, without division by its length. -/
theorem rectifiableArcPath_ordered_reconstruction (γ : Path a b)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ (Icc 0 1) ∧ MonotoneOn τ (Icc 0 1) ∧
      τ 0 = 0 ∧ τ 1 = 1 ∧ τ '' Icc 0 1 = Icc 0 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, (rectifiableArcPath γ hBV).extend (τ t) = γ.extend t := by
  let L : ℝ := rectifiablePathLength γ
  let v := variationOnFromTo γ.extend (Icc (0 : ℝ) 1) 0
  let g := naturalParameterization γ.extend (Icc (0 : ℝ) 1) 0
  have h := continuous_rectifiable_arcLength_factorization zero_le_one hBV
    γ.continuous_extend.continuousOn
  have hv : v '' Icc 0 1 = Icc 0 L := h.2.2.2.1
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, g (v t) = γ.extend t := h.2.2.2.2.2.2.1
  by_cases hL : L = 0
  · refine ⟨id, continuousOn_id, monotoneOn_id, rfl, rfl, image_id _, ?_⟩
    intro t ht
    have hvt : v t = 0 := by
      have hm : v t ∈ Icc 0 L := hv ▸ mem_image_of_mem v ht
      exact le_antisymm (hL ▸ hm.2) hm.1
    change (rectifiableArcPath γ hBV).extend t = γ.extend t
    rw [rectifiableArcPath_extend γ hBV ht]
    change g (L * t) = γ.extend t
    rw [hL, zero_mul, ← hvt]
    exact hr t ht
  · let τ : ℝ → ℝ := fun t => v t / L
    have hc : ContinuousOn τ (Icc 0 1) := h.2.1.div_const L
    have hm : MonotoneOn τ (Icc 0 1) := fun x hx y hy hxy =>
      div_le_div_of_nonneg_right (h.2.2.1 hx hy hxy) (rectifiablePathLength γ).property
    have hvone : v 1 = L := by
      change variationOnFromTo γ.extend (Icc (0 : ℝ) 1) 0 1 = _
      rw [variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self]
      rfl
    have ht0 : τ 0 = 0 := by simp only [τ, v, variationOnFromTo.self, zero_div]
    have ht1 : τ 1 = 1 := by simp only [τ, hvone, div_self hL]
    have hi : τ '' Icc 0 1 = Icc 0 1 := by
      simpa only [ht0, ht1] using hc.image_Icc_of_monotoneOn zero_le_one hm
    refine ⟨τ, hc, hm, ht0, ht1, hi, ?_⟩
    intro t ht
    have htt : τ t ∈ Icc (0 : ℝ) 1 := hi ▸ mem_image_of_mem τ ht
    rw [rectifiableArcPath_extend γ hBV htt]
    change g (L * (v t / L)) = γ.extend t
    have hcancel : L * (v t / L) = v t := by field_simp
    rw [hcancel]
    exact hr t ht

/-- For complex contours the actual integrated speed is bounded by the
original geometric total variation. -/
theorem rectifiableArcPath_length_le {z w : ℂ} (γ : Path z w)
    (hBV : BoundedVariationOn γ.extend (Icc (0 : ℝ) 1)) :
    parametrizedContourLength (rectifiableArcPath γ hBV) ≤ (rectifiablePathLength γ : ℝ) :=
  parametrizedContourLength_le_lipschitz _ (rectifiableArcPath_lipschitz γ hBV)

end UV
