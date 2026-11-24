import UV.ContinueOrderedTorusDepth
import UV.ContinueOrderedTorusTree

/-! The combined lattice-frequency photon graph at a common depth, with
arbitrary external momenta and a tree that shares all the chord variables. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace UV.SectorPlane

private theorem line_power_cost {δ : Fin 3 → ℝ} {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ t : OrderedPhotonKind,
      (∫ p, t.torusLine δ r p ∂orderedTorusTransferMeasure) ≤ B * (1+r⁻¹)^2 := by
  obtain ⟨CT,CC,hT,hC,hb⟩ := ordered_torus_integrated_chord_costs hd hδ
  refine ⟨max CT.toReal CC.toReal,(ENNReal.toReal_nonneg).trans (le_max_left _ _),?_⟩
  intro r hr hr₁ t
  have hi := t.torusLine_integrable hd hδ hr
  have he : ENNReal.ofReal (∫ p, t.torusLine δ r p ∂orderedTorusTransferMeasure) =
      ∑' k, ∫⁻ ν : ℝ, ENNReal.ofReal (t.torusLine δ r (k,ν)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (t.torusLine_nonneg _ _)),
      orderedTorusTransferMeasure,lintegral_prod _ (t.torusLine_measurable δ r).ennreal_ofReal.aemeasurable,
      lintegral_count]
  have hp : 0 ≤ ∫ p, t.torusLine δ r p ∂orderedTorusTransferMeasure := integral_nonneg (t.torusLine_nonneg _ _)
  cases t with
  | transverse =>
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hT.ne ENNReal.ofReal_ne_top)
      (he.le.trans (hb r hr hr₁).1)
    rw [ENNReal.toReal_ofReal hp,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),←inv_pow] at h
    exact h.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
      (by positivity) (ENNReal.toReal_nonneg.trans (le_max_left _ _)))
  | coulomb =>
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC.ne ENNReal.ofReal_ne_top)
      (he.le.trans (hb r hr hr₁).2)
    rw [ENNReal.toReal_ofReal hp,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at h
    have hpow : r⁻¹ ≤ (1+r⁻¹)^2 := by nlinarith [inv_nonneg.mpr hr.le,sq_nonneg r⁻¹]
    exact h.trans (mul_le_mul (le_max_right _ _) hpow (by positivity)
      (ENNReal.toReal_nonneg.trans (le_max_left _ _)))

/-- Fixed-order product bound with one frequency and one spatial winding
per photon chord. Every tree transfer may depend on all chords, on the
depth and on external data. No Jacobian or independent chord variables
are assigned to a bridge. -/
theorem ordered_torus_graph_chord_budget {J : Type*} [Fintype J] {n : ℕ}
    (tree : Fin n → OrderedPhotonKind) (chord : J → OrderedPhotonKind) {δ : Fin 3 → ℝ}
    {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (T : (J → OrderedTorusTransfer) → Fin n → OrderedTorusTransfer)
        (A : (J → OrderedTorusTransfer) → ℂ)
        (K : ℝ), 0 ≤ K →
      AEStronglyMeasurable A (Measure.pi fun _ : J => orderedTorusTransferMeasure) →
      (∀ᵐ q ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure), ‖A q‖ ≤
        K*((∏ i, (tree i).torusLine δ r (T q i))*∏ j, (chord j).torusLine δ r (q j))) →
      Integrable A (Measure.pi fun _ : J => orderedTorusTransferMeasure) ∧
      (∫ q, ‖A q‖ ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure)) ≤
        K*B*((1+r⁻¹)^(2*Fintype.card J)) := by
  obtain ⟨B,hB,hcost⟩ := line_power_cost hd hδ
  let C := ((d^2)⁻¹)^n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C*B^Fintype.card J,by positivity,?_⟩
  intro r hr hr₁ T A K hK hA hmajor
  let F (q : J → OrderedTorusTransfer) := ∏ j, (chord j).torusLine δ r (q j)
  have hF := Integrable.fintype_prod fun j => (chord j).torusLine_integrable hd hδ hr
  have hI : Integrable (fun q => (K*C)*F q) (Measure.pi fun _ : J => orderedTorusTransferMeasure) :=
    hF.const_mul (K*C)
  have hdom : ∀ᵐ q ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure), ‖A q‖ ≤ (K*C)*F q := by
    filter_upwards [hmajor] with q hq
    have ht : ∏ i, (tree i).torusLine δ r (T q i) ≤ C := by
      calc
        _ ≤ ∏ _ : Fin n, (d^2)⁻¹ := by
          apply Finset.prod_le_prod (fun i _ => (tree i).torusLine_nonneg _ _ _)
          intro i _
          have h := ordered_torus_bridge_bound hd hδ hr.le (T q i).1 (T q i).2
          cases tree i <;> first | exact h.1 | exact h.2
        _ = _ := by simp [C]
    rw [mul_assoc]
    exact hq.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht
      (Finset.prod_nonneg (fun j _ => (chord j).torusLine_nonneg _ _ _))) hK)
  have hAI := hI.mono' hA hdom
  refine ⟨hAI,(integral_mono_ae hAI.norm hI hdom).trans ?_⟩
  rw [integral_const_mul,show (∫ q, F q ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure)) =
    ∏ j, ∫ p, (chord j).torusLine δ r p ∂orderedTorusTransferMeasure from integral_fintype_prod_eq_prod _]
  calc
    _ ≤ K*C*(∏ _ : J, B*(1+r⁻¹)^2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hC)
      exact Finset.prod_le_prod (fun j _ => integral_nonneg ((chord j).torusLine_nonneg _ _))
        (fun j _ => hcost r hr hr₁ (chord j))
    _ = _ := by simp [mul_pow,pow_mul,mul_assoc,mul_left_comm]

/-- One depth integral for the graph with its vacuum factor. The charged
word budget may carry a finite inverse-depth power and an exponential
vacuum cost. The photon powers in the integral are derived from the
actual line kernels and the number of chords. -/
theorem ordered_torus_shared_depth_graph {J : Type*} [Fintype J] {n : ℕ}
    (tree : Fin n → OrderedPhotonKind) (chord : J → OrderedPhotonKind) {δ : Fin 3 → ℝ}
    {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i) (μ : Measure ℝ) {c C K : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) (m : ℕ) (hs : ∀ᵐ r ∂μ, r ∈ Ioc (0:ℝ) 1)
    (hμ : Integrable (fun r : ℝ => exp (c/r^3)) μ)
    (T : ℝ → (J → OrderedTorusTransfer) → Fin n → OrderedTorusTransfer)
    (A : ℝ × (J → OrderedTorusTransfer) → ℂ)
    (hA : AEStronglyMeasurable A (μ.prod (Measure.pi fun _ : J => orderedTorusTransferMeasure)))
    (hdom : ∀ᵐ r ∂μ, ∀ᵐ q ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure),
      ‖A (r,q)‖ ≤ (K*(1+r⁻¹)^m*exp (C*(1+(sqrt r)⁻¹^3)))*
        ((∏ i, (tree i).torusLine δ r (T r q i))*∏ j, (chord j).torusLine δ r (q j))) :
    Integrable A (μ.prod (Measure.pi fun _ : J => orderedTorusTransferMeasure)) := by
  obtain ⟨B,hB,h⟩ := ordered_torus_graph_chord_budget tree chord hd hδ
  let ν := Measure.pi fun _ : J => orderedTorusTransferMeasure
  let N := m+2*Fintype.card J
  have ha : ∀ᵐ r ∂μ, Integrable (fun q => A (r,q)) ν ∧
      (∫ q, ‖A (r,q)‖ ∂ν) ≤ K*B*((1+r⁻¹)^N*exp (C*(1+(sqrt r)⁻¹^3))) := by
    filter_upwards [hs,hdom,hA.prodMk_left] with r hr hdom' hAr
    have hrp := hr.1
    obtain ⟨hi,hi'⟩ := h r hr.1 hr.2 (T r) (fun q => A (r,q)) _ (by positivity) hAr hdom'
    exact ⟨hi,hi'.trans_eq (by dsimp [N]; rw [pow_add]; ring)⟩
  apply (integrable_prod_iff hA).mpr
  refine ⟨ha.mono (fun _ hq => hq.1),?_⟩
  apply ((hμ.const_mul (exp (C+((N:ℝ)+C)^2/(4*c)))).const_mul (K*B)).mono'
    hA.norm.integral_prod_right'
  filter_upwards [ha,hs] with r hr ht
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact hr.2.trans (mul_le_mul_of_nonneg_left (ordered_torus_depth_domination hc ht.1 ht.2 N) (mul_nonneg hK hB))

/-- An external momentum packet may be integrated after a fixed-endpoint
bound uniform in its momenta. The weight can live on a mixed discrete and
continuous space and need only have finite absolute integral. -/
theorem ordered_torus_external_packet {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]
    (μ : Measure P) (ν : Measure Q) [SFinite ν] (w : P → ℝ) (hw : Integrable w μ)
    (A : P × Q → ℂ) (hA : AEStronglyMeasurable A (μ.prod ν))
    (hf : ∀ᵐ p ∂μ, Integrable (fun q => A (p,q)) ν)
    {C : ℝ} (hb : ∀ᵐ p ∂μ, ∫ q, ‖A (p,q)‖ ∂ν ≤ C*‖w p‖) :
    Integrable A (μ.prod ν) := by
  apply (integrable_prod_iff hA).mpr
  refine ⟨hf,(hw.norm.const_mul C).mono' hA.norm.integral_prod_right' ?_⟩
  filter_upwards [hb] with p hp
  simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using hp

end UV.SectorPlane
