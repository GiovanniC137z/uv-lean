import UV.RevisionJointHeatMoments

/-! The stronger marginal moments that control joint inverse-lapse budgets. -/

noncomputable section
open MeasureTheory Set Filter Real
open scoped BigOperators ENNReal

namespace UV.ContinuationGraph

/-- Hölder with the actual coordinate marginals of one joint measure. Each
inverse moment must be tested at `p j * u j` before taking its `1 / p j` power. -/
theorem joint_inverseMoment_holder {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ρ : Measure X) (lapse : ι → X → ℝ) (hlapse : ∀ j, Measurable (lapse j))
    (hpos : ∀ᵐ x ∂ρ, ∀ j, 0 < lapse j x) (p u : ι → ℝ)
    (hp : ∀ j, 0 < p j) (hp_sum : ∑ j, 1 / p j = 1) :
    (∫⁻ x, ∏ j, ENNReal.ofReal ((lapse j x) ^ (-u j)) ∂ρ) ≤
      ∏ j, ((∫⁻ t : ℝ, ENNReal.ofReal (t ^ (-(p j * u j))) ∂ρ.map (lapse j)) ^ (1 / p j)) := by
  classical
  let f (j : ι) (x : X) := ENNReal.ofReal ((lapse j x) ^ (-(p j * u j)))
  have hf (j : ι) : Measurable (f j) := by
    unfold f
    have h := hlapse j
    fun_prop
  have hmom (j : ι) : 0 ≤ 1 / p j := one_div_nonneg.mpr (hp j).le
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := ρ) Finset.univ
    (f := f) (fun j _ => (hf j).aemeasurable) hp_sum (fun j _ => hmom j)
  calc
    _ = ∫⁻ x, ∏ j, f j x ^ (1 / p j) ∂ρ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      apply Finset.prod_congr rfl
      intro j _
      unfold f
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (hx j) _),
        ← Real.rpow_mul (hx j).le]
      congr 2
      field_simp [(hp j).ne']
    _ ≤ ∏ j, (∫⁻ x, f j x ∂ρ) ^ (1 / p j) := h
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rw [lintegral_map (by fun_prop) (hlapse j)]

end UV.ContinuationGraph
