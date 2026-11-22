import UV.ResumeConvergenceNetwork

/-! Positive finite-product Tonelli, retaining infinite zero-mark costs. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace UV

theorem network_lintegral_fin_prod {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : Fin n) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ t, f i t ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : X 0 × ((i : Fin n) → X (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ t, f 0 t ∂μ 0) * ∏ i : Fin n, ∫⁻ t, f i.succ t ∂μ i.succ := by
          rw [lintegral_prod_mul (f := f 0)
            (g := fun x : (i : Fin n) → X i.succ => ∏ i, f i.succ (x i))
            (hf 0).aemeasurable
              ((Finset.measurable_prod Finset.univ fun i _ =>
                (hf i.succ).comp (measurable_pi_apply i)).aemeasurable),
            ih _ _ (fun i => hf i.succ)]
        _ = _ := by rw [Fin.prod_univ_succ]

theorem network_lintegral_fintype_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ t, f i t ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply, network_lintegral_fin_prod _ _ (fun i => hf (e i))]

theorem networkDurationCost_product {E : Type*} [Fintype E] (m z : E → ℝ) :
    networkDurationCost m z = ∏ e, networkEdgeCost (m e) (z e) := by
  unfold networkDurationCost networkEdgeCost
  calc
    _ = ∫⁻ s : E → ℝ, ∏ e, ENNReal.ofReal (networkHeatFive (m e) (z e) (s e))
        ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ))) := by
      apply lintegral_congr_ae
      have ha : ∀ᵐ s : E → ℝ ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ))),
          ∀ e, 0 < s e := by
        apply ae_all_iff.mpr
        intro e
        exact (Measure.quasiMeasurePreserving_eval _ e).ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [ha] with s hs
      exact ENNReal.ofReal_prod_of_nonneg (fun e _ => networkHeatFive_nonneg (hs e).le _ _)
    _ = _ := network_lintegral_fintype_prod
      (fun _ : E => volume.restrict (Ioi (0 : ℝ)))
      (fun e s => ENNReal.ofReal (networkHeatFive (m e) (z e) s))
      (fun e => by unfold networkHeatFive; fun_prop)

/-- The displayed Green product is interpreted in the extended nonnegative
reals: a zero transverse mark is an infinite factor. -/
def networkExtendedGreen (m z : ℝ) : ℝ≥0∞ :=
  if z = 0 then ⊤ else ENNReal.ofReal (networkEdgeGreen m z)

theorem networkEdgeCost_extended {m z : ℝ} (hm : 0 < m) (hz : 0 ≤ z) :
    networkEdgeCost m z = networkExtendedGreen m z := by
  unfold networkExtendedGreen
  split_ifs with h
  · rw [h, networkEdgeCost_zero]
  · exact networkEdgeCost_positive hm (lt_of_le_of_ne hz (Ne.symm h))

theorem networkDurationCost_extended {E : Type*} [Fintype E]
    (m z : E → ℝ) (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 ≤ z e) :
    networkDurationCost m z = ∏ e, networkExtendedGreen (m e) (z e) := by
  rw [networkDurationCost_product]
  exact Finset.prod_congr rfl (fun e _ => networkEdgeCost_extended (hm e) (hz e))

theorem networkExtendedGreen_ne_zero {m z : ℝ} (hm : 0 < m) (hz : 0 ≤ z) :
    networkExtendedGreen m z ≠ 0 := by
  unfold networkExtendedGreen
  split_ifs with h
  · exact ENNReal.top_ne_zero
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm h)
    unfold networkEdgeGreen
    positivity

theorem networkDurationCost_zero_mark {E : Type*} [Fintype E]
    (m z : E → ℝ) (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 ≤ z e)
    (e : E) (he : z e = 0) : networkDurationCost m z = ⊤ := by
  classical
  rw [networkDurationCost_extended m z hm hz,
    ← Finset.mul_prod_erase Finset.univ (fun i => networkExtendedGreen (m i) (z i)) (Finset.mem_univ e)]
  have hzero : networkExtendedGreen (m e) (z e) = ⊤ := by simp [networkExtendedGreen, he]
  rw [hzero, ENNReal.top_mul]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => networkExtendedGreen_ne_zero (hm i) (hz i))

end UV
