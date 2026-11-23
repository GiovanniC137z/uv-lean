import UV.ContinueWilsonPolygonMeasure

/-! Explicit finite index contraction for the ordered four-spinor product.
The endpoints are identified when taking the trace, with no change in
multiplication order, for arbitrary nonempty marked words. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped BigOperators Matrix.Norms.L2Operator

namespace UV

def wilsonSpinPath {n : ℕ} (A : Fin (n+1) → DiracMatrix) (i j : Fin 4) (s : Fin n → Fin 4) : ℂ :=
  ∏ k, A k (Fin.cons (α := fun _ => Fin 4) i s k) (Fin.snoc (α := fun _ => Fin 4) s j k)

theorem wilson_spin_path_expand {n : ℕ} (A : Fin (n+1) → DiracMatrix) (i j : Fin 4) :
    (List.ofFn A).prod i j = ∑ s : Fin n → Fin 4, wilsonSpinPath A i j s := by
  classical
  induction n generalizing i with
  | zero => simp [List.ofFn_succ,wilsonSpinPath,Fin.snoc_zero]
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons,Matrix.mul_apply]
    simp_rw [ih]
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 4)
    rw [←e.sum_comp (wilsonSpinPath A i j),Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    change A 0 i k * wilsonSpinPath (fun z => A z.succ) k j s = wilsonSpinPath A i j (Fin.cons k s)
    simp only [wilsonSpinPath]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [←Fin.cons_snoc_eq_snoc_cons,Fin.cons_zero,Fin.cons_succ]

theorem wilson_spin_trace_expand {n : ℕ} (A : Fin (n+1) → DiracMatrix) :
    (List.ofFn A).prod.trace = ∑ i : Fin 4, ∑ s : Fin n → Fin 4, wilsonSpinPath A i i s := by
  simp only [Matrix.trace,Matrix.diag_apply,wilson_spin_path_expand]

variable {ι J : Type*} [Fintype ι] [Fintype J]

theorem WilsonSpinEntry.hop_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (e : WilsonSpinEntry) (p : OSFourSpace) : ‖e.hop L T p‖ ≤ 2*(2*L)^e.marks.length := by
  change ‖wilsonMarkedSpinHop L T e.marks e.row e.col p‖ ≤ _
  rw [←wilson_spin_hop_entry hL T]
  exact (wilson_matrix_entry_le_opnorm _ _ _).trans (wilson_spin_hop_opnorm hL T _ _)

theorem wilson_spin_path_momentum_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (head : WilsonSpinEntry) (tail : J → WilsonSpinEntry) (b : OSFourSpace) (q : J → OSFourSpace) :
    Integrable (fun p => head.hop L T (p+b) * ∏ j, (tail j).hop L T (p+q j)) := by
  have hH : Integrable (fun p => head.hop L T (p+b)) := ((measurePreserving_add_right (volume : Measure OSFourSpace) b).integrable_comp_emb
    (Homeomorph.addRight b).measurableEmbedding).mpr (wilson_marked_spin_hop_integrable hL T _ _ _)
  apply (hH.norm.mul_const (∏ j, 2*(2*L)^(tail j).marks.length)).mono'
    ((((head.hop_measurable L T).comp (measurable_id.add measurable_const)).mul (Finset.measurable_prod _
      (fun j _ => ((tail j).hop_measurable L T).comp (measurable_id.add measurable_const)))).aestronglyMeasurable)
  apply Eventually.of_forall fun p => ?_
  rw [norm_mul,norm_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => (tail j).hop_bound hL T _)) (norm_nonneg _)

theorem wilson_spin_path_return_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (head : WilsonSpinEntry) (tail : J → WilsonSpinEntry) (b : OSFourSpace) (q : J → OSFourSpace) :
    Integrable (fun d => (thinPlaneWave b (-(∑ j, d j)) * head.density L T (-(∑ j, d j))) * wilsonTailEntryWeight L tail q d)
      (Measure.pi (fun _ => wilsonDisplacementMeasure L T)) := by
  have hc := wilson_entry_density_continuous hL T head.marks head.row head.col
  have hcomp := wilson_entry_density_compact hL T head.marks head.row head.col
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuous hc
  have hS : Continuous (fun d : J → OSFourSpace => -(∑ j, d j)) := (continuous_finset_sum _ fun j _ => continuous_apply j).neg
  have hW : Continuous (thinPlaneWave b) := by unfold thinPlaneWave; fun_prop
  apply ((wilson_tail_weight_integrable hL T tail q).norm.const_mul C).mono'
    ((((hW.comp hS).mul (hc.comp hS)).mul (wilson_tail_weight_continuous L tail q)).aestronglyMeasurable)
  apply Eventually.of_forall fun d => ?_
  simp only [Function.comp_apply,norm_mul,wilson_wave_norm,one_mul]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

end UV
