import UV.ContinueFourierHoppingLoop
import UV.ContinueOrderedTorusMarks

/-! One closed charged Fourier circulation on the actual reciprocal lattice
of a rectangular spatial box. The charged zero mode is included. -/

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace UV.SectorPlane

private theorem torus_head {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {σ : ℝ} (hσ : 0<σ)
    (n : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial),
    let F := fun k => twoBandGaussianWilsonMark 1 σ u b q (orderedTorusMomentum δ k)
    Integrable F Measure.count ∧ (∫ k, ‖F k‖ ∂Measure.count) ≤ D := by
  have hκ : 0<σ^2 := by positivity
  obtain ⟨B,hB,h⟩ := ordered_torus_averaged_marks hδ hκ 1 n (twoBandPathFractions n)
  refine ⟨B*σ^n,by positivity,?_⟩
  intro u b q F
  have hsum := h 1 zero_lt_one le_rfl u (fun s => b+∑ j, s j • q j) (by fun_prop)
  simp only [mul_one,Real.sqrt_sq hσ.le,Real.sqrt_one,inv_one,one_pow] at hsum
  have hL : (∫⁻ k, ‖F k‖ₑ ∂Measure.count) ≤ ENNReal.ofReal (B*σ^n) := by
    rw [lintegral_count]; exact hsum
  have hi : Integrable F Measure.count := ⟨(measurable_of_countable F).aestronglyMeasurable,
    hL.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_norm_eq_lintegral_enorm hi] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hL

def hoppingTorusHeadBudget {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {σ : ℝ} (hσ : 0<σ) (M : ℕ) : ℝ :=
  ∑ n : Fin (M+1), (torus_head hδ hσ n.val).choose

theorem hopping_torus_head_nonneg {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {σ : ℝ} (hσ : 0<σ) (M : ℕ) :
    0 ≤ hoppingTorusHeadBudget hδ hσ M :=
  Finset.sum_nonneg fun n _ => (torus_head hδ hσ n.val).choose_spec.1

def hoppingTorusBudget (m g : ℝ) {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) {σ : ℝ} (hσ : 0<σ) (M : ℕ) : ℝ :=
  |g|^2*(Real.pi/m)*(hoppingOrderConstant m M)^(M+2)*
    (hoppingTorusHeadBudget hδ hσ M*(hoppingSpatialBudget hσ M)^M)

theorem hopping_torus_budget_nonneg {m : ℝ} (hm : 0<m) (g : ℝ) {δ : Fin 3 → ℝ}
    (hδ : ∀ i, 0 < δ i) {σ : ℝ} (hσ : 0<σ) (M : ℕ) : 0 ≤ hoppingTorusBudget m g hδ hσ M := by
  have h₁ := zero_le_one.trans (hopping_order_constant_one m M)
  have h₂ := zero_le_one.trans (hopping_spatial_budget_one hσ M)
  have h₃ := hopping_torus_head_nonneg hδ hσ M
  unfold hoppingTorusBudget
  positivity

theorem HoppingFourierLoop.torus_cost {N : ℕ} (L : HoppingFourierLoop N) {m σ : ℝ} (hm : 0<m) (hσ : 0<σ)
    {δ : Fin 3 → ℝ} (hδ : ∀ i, 0 < δ i) (g : ℝ) {M : ℕ} (hL : L.valid m M) :
    let F := fun x : ℝ × OrderedHopWinding => L.word g σ (x.1,orderedTorusMomentum δ x.2)
    Integrable F (volume.prod Measure.count) ∧ (∫ x, ‖F x‖ ∂volume.prod Measure.count) ≤
      (hoppingTorusBudget m g hδ hσ M * (|g|/m)^N)*L.weight := by
  apply L.cost_for hm g σ hL Measure.count (orderedTorusMomentum δ)
  intro H
  let S := List.ofFn (fun j : Fin (N+1) => L.space j.succ)
  let t := L.space 0
  have hs := hL.2.2
  rw [Fin.sum_univ_succ] at hs
  have hD : t.degree+hoppingSpatialDegree S ≤ M := by
    simpa only [t,S,hoppingSpatialDegree,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hs
  let i : Fin (M+1) := ⟨t.degree,by omega⟩
  have h := (torus_head hδ hσ i.val).choose_spec.2 t.direction t.shift t.marks
  have hB : (torus_head hδ hσ i.val).choose ≤ hoppingTorusHeadBudget hδ hσ M :=
    Finset.single_le_sum (fun (j : Fin (M+1)) _ => (torus_head hδ hσ j.val).choose_spec.1) (Finset.mem_univ i)
  let K := hoppingSpatialBudget hσ M
  have hK : 1 ≤ K := hopping_spatial_budget_one hσ M
  have he (k) : H k = (t.value σ (orderedTorusMomentum δ k))*hoppingSpatialProduct σ S (orderedTorusMomentum δ k) := by
    simp only [H,t,S,Fin.prod_univ_succ,hoppingSpatialProduct,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  have hp (k) : ‖H k‖ ≤ ‖t.value σ (orderedTorusMomentum δ k)‖*K^M := by
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_left ((hopping_spatial_product_sup hσ S (by omega : hoppingSpatialDegree S ≤ M) _).trans
      (pow_le_pow_right₀ hK (by omega))) (norm_nonneg _)
  have hdom := h.1.norm.mul_const (K^M)
  have hi : Integrable H Measure.count := hdom.mono' (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ hp)
  refine ⟨hi,(integral_mono hi.norm hdom hp).trans ?_⟩
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (h.2.trans hB) (pow_nonneg (zero_le_one.trans hK) _)

end UV.SectorPlane
