import UV.ContinueNormalCircleWord
import Mathlib.Analysis.Fourier.Inversion

/-! Integration of ordered independent Dirac factors and Fourier
transformation of their constrained normal displacements. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology FourierTransform

namespace UV

local instance normalConvolutionMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalConvolutionMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_ordered_measurable {Z : Type*} [MeasurableSpace Z] {r : ℕ} (A : Fin r → Z → DiracMatrix)
    (hm : ∀ i, Measurable (A i)) : Measurable (fun z => normalOrderedWord (fun i => A i z)) := by
  induction r with
  | zero => simp only [normalOrderedWord,List.ofFn_zero,List.prod_nil]; exact measurable_const
  | succ r ih =>
    simpa only [normalOrderedWord,List.ofFn_succ,List.prod_cons] using (hm 0).mul (ih (fun i => A i.succ) (fun i => hm i.succ))

theorem normal_ordered_integrable {r : ℕ} (A : Fin r → ℝ → DiracMatrix) (hm : ∀ i, Measurable (A i))
    (hi : ∀ i, Integrable (A i)) : Integrable (fun x : Fin r → ℝ => normalOrderedWord (fun i => A i (x i))) := by
  apply (Integrable.fintype_prod (fun i => (hi i).norm)).mono'
    (normal_ordered_measurable _ (fun i => (hm i).comp (measurable_pi_apply i))).aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [List.map_ofFn,List.prod_ofFn,Function.comp_def] using
    (List.ofFn (fun i => A i (x i))).norm_prod_le

theorem normal_ordered_integral {r : ℕ} (A : Fin r → ℝ → DiracMatrix) (hm : ∀ i, Measurable (A i))
    (hi : ∀ i, Integrable (A i)) :
    (∫ x : Fin r → ℝ, normalOrderedWord (fun i => A i (x i))) = normalOrderedWord (fun i => ∫ y, A i y) := by
  induction r with
  | zero => simp [normalOrderedWord,measureReal_def,volume_pi]
  | succ r ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => ℝ) 0
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (r+1) => ℝ) 0).symm e
    let f := fun x : Fin (r+1) → ℝ => normalOrderedWord (fun i => A i (x i))
    have hF := normal_ordered_integrable A hm hi
    have ht := normal_ordered_integrable (fun i => A i.succ) (fun i => hm i.succ) (fun i => hi i.succ)
    have hsplit (x : ℝ × (Fin r → ℝ)) : f (e.symm x) = A 0 x.1*normalOrderedWord (fun i => A i.succ (x.2 i)) := by
      have hcons : e.symm x = Fin.cons x.1 x.2 := Fin.insertNth_zero' _ _
      rw [hcons]
      simp only [f,normalOrderedWord,List.ofFn_succ,List.prod_cons,Fin.cons_zero,Fin.cons_succ]
    change (∫ x, f x) = _
    rw [←he.integral_comp e.symm.measurableEmbedding f,Measure.volume_eq_prod ℝ (Fin r → ℝ),
      integral_prod (fun z => f (e.symm z)) (he.integrable_comp_of_integrable hF)]
    simp_rw [hsplit,integral_const_mul_of_integrable ht]
    rw [integral_mul_const_of_integrable (hi 0),ih _ (fun i => hm i.succ) (fun i => hi i.succ)]
    simp only [normalOrderedWord,List.ofFn_succ,List.prod_cons]

/-- At positive tail length, the discontinuity of the first oriented
cover factor is a carrier-independent null hyperplane in the increments. -/
theorem normal_sum_ne_ae (n : ℕ) (D : ℝ) : ∀ᵐ x : Fin (n+1) → ℝ, ∑ i, x i ≠ D := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm e
  rw [←he.map_eq]
  have hm : MeasurableSet {x : Fin (n+1) → ℝ | ∑ i, x i ≠ D} := (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.measurableSet
  apply (ae_map_iff he.measurable.aemeasurable hm).mpr
  have h : ∀ᵐ x ∂(volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)), x.1 + (∑ i, x.2 i) ≠ D := by
    have hme : MeasurableSet {x : ℝ × (Fin n → ℝ) | x.1 + (∑ i, x.2 i) ≠ D} := (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.measurableSet
    apply (ae_prod_iff_ae_ae hme).mpr
    apply (ae_ae_comm (p := fun t (y : Fin n → ℝ) => t+(∑ i, y i)≠D) hme).mpr
    refine Eventually.of_forall fun y => ?_
    have ht : ∀ᵐ t : ℝ, t ≠ D-∑ i, y i := by simp [ae_iff]
    exact ht.mono fun t hne heq => hne (by linarith)
  filter_upwards [h] with x hx
  have hcons : e.symm x = Fin.cons x.1 x.2 := Fin.insertNth_zero' _ _
  change (∑ i, e.symm x i) ≠ D
  simpa only [hcons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ] using hx

end UV
