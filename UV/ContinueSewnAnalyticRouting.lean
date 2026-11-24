import UV.ContinueSewnAnalyticMoments
import UV.ContinueSewnFlagMomentum

/-! The analytic test uses components of the actual projected displacement in
the locked Euclidean chart. Its positive measure is the pushforward of the
magnitude of the complete paired density. -/

noncomputable section
open Real Set MeasureTheory Matrix
open scoped ENNReal Topology
namespace UV.SewnFlags

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One coordinate of `(proj V_S ⊗ I₄)d`, retaining both the loop index and
the intrinsic four-coordinate label. -/
def routedProjectedCoordinate {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (S : Finset (Fin N))
    (a : Fin L × Fin 4) : EuclideanSpace ℝ (Fin L × Fin 4) →L[ℝ] ℝ :=
  let Q : EuclideanSpace ℝ (Fin L × Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin L) :=
    { toFun := fun d => WithLp.toLp 2 (fun j => d (j,a.2))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  (EuclideanSpace.proj a.1).comp ((routingFace C S).starProjection.comp Q.toContinuousLinearMap)

theorem routedProjectedCoordinate_le {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (S : Finset (Fin N))
    (a : Fin L × Fin 4) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    |routedProjectedCoordinate C S a d| ≤ projectedDisplacement C S d := by
  let P (k : Fin 4) := (routingFace C S).starProjection (WithLp.toLp 2 (fun j => d (j,k)))
  have h := PiLp.norm_apply_le (P a.2) a.1
  apply h.trans
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun k => ‖P k‖^2) (fun i _ => sq_nonneg _) (Finset.mem_univ a.2)

/-- The dominating displacement measure induced by one occupied paired chart. -/
def pairedChartLaw {L : ℕ} (K : Set E) (d : E → EuclideanSpace ℝ (Fin L × Fin 4)) (w : E → ℂ) :=
  Measure.map d ((volume.restrict K).withDensity (fun x => ‖w x‖ₑ))

theorem pairedChartLaw_finite {L : ℕ} {K : Set E} (hK : IsCompact K)
    (d : E → EuclideanSpace ℝ (Fin L × Fin 4)) {p : ℝ} (hp : 1 < p) (w : E → ℂ)
    (hw : MemLp w (ENNReal.ofReal p) (volume.restrict K)) : IsFiniteMeasure (pairedChartLaw K d w) := by
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  have hi := hw.integrable ((ENNReal.one_lt_ofReal.mpr hp).le)
  letI := isFiniteMeasure_withDensity (f := fun x => ‖w x‖ₑ) hi.hasFiniteIntegral.ne
  exact Measure.isFiniteMeasure_map _ _

/-- Actual routed joint moments on the analytic chart, with nonidentity
required only for marginal faces. Power-regular faces need no surviving
coordinate. Repeated and overlapping projected faces are allowed. -/
theorem routed_analytic_chart_joint {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    {U K : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (d : E → EuclideanSpace ℝ (Fin L × Fin 4)) (hd : AnalyticOnNhd ℝ d U)
    {p : ℝ} (hp : 1 < p) (w : E → ℂ) (hw : MemLp w (ENNReal.ofReal p) (volume.restrict K))
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin N)) (δ : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hnon : ∀ i, δ i = 0 → ∃ a : Fin L × Fin 4, ¬EqOn (fun x => routedProjectedCoordinate C (S i) a (d x)) 0 U) :
    (∫⁻ z, ∏ i, displacementCost (δ i) (projectedDisplacement C (S i) z) ∂pairedChartLaw K d w) < ⊤ := by
  classical
  let μ := volume.restrict K
  have hdm : AEMeasurable d μ := ContinuousOn.aemeasurable
    (fun x hx => (hd _ (hKU hx)).continuousAt.continuousWithinAt) hK.isClosed.measurableSet
  let H (z : EuclideanSpace ℝ (Fin L × Fin 4)) :=
    ∏ i, displacementCost (δ i) (projectedDisplacement C (S i) z)
  have hH : Measurable H := Finset.measurable_prod _ (fun i _ =>
    (measurable_displacementCost _).comp (projectedDisplacement_measurable C _))
  change (∫⁻ z, H z ∂Measure.map d (μ.withDensity (fun x => ‖w x‖ₑ))) < ⊤
  rw [lintegral_map' hH.aemeasurable (hdm.mono' (withDensity_absolutelyContinuous μ _)),
    lintegral_withDensity_eq_lintegral_mul₀ (μ := μ) (g := fun x => H (d x))
      hw.aestronglyMeasurable.aemeasurable.enorm (hH.comp_aemeasurable hdm)]
  by_cases hu : U.Nonempty
  · let f (i : ι) (x : E) := if h : δ i = 0 then routedProjectedCoordinate C (S i) (hnon i h).choose (d x) else 1
    let r (i : ι) (x : E) := if δ i = 0 then projectedDisplacement C (S i) (d x) else 1
    have hf (i) : AnalyticOnNhd ℝ (f i) U := by
      intro x hx
      by_cases h : δ i = 0
      · simpa only [f,dif_pos h] using
          ((routedProjectedCoordinate C (S i) (hnon i h).choose).analyticAt (d x)).comp (f := d) (hd x hx)
      · simpa only [f,dif_neg h] using (analyticAt_const : AnalyticAt ℝ (fun _ : E => (1:ℝ)) x)
    have hfn (i) : ¬EqOn (f i) 0 U := by
      by_cases h : δ i = 0
      · simpa only [f,dif_pos h] using (hnon i h).choose_spec
      · obtain ⟨x,hx⟩ := hu
        intro he; simpa [f,h] using he hx
    have hr (i x) (_ : x ∈ K) : |f i x| ≤ r i x := by
      by_cases h : δ i = 0
      · simpa only [f,r,dif_pos h,if_pos h] using routedProjectedCoordinate_le C (S i) (hnon i h).choose (d x)
      · simp [f,r,h]
    have hJ := analytic_chart_weighted_joint_marginals hU hconn hK hKU f hf hfn r hr hp w hw
    convert hJ using 1
    apply lintegral_congr
    intro x
    change ‖w x‖ₑ * H (d x) = _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : δ i = 0
    · simp only [r,h,if_pos]
    · simp [r,h,displacementCost,(hδ i).lt_of_ne' h]
  · have hKe : K = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ hx => hu ⟨_,hKU hx⟩)
    simp [μ,hKe]

/-- With nonnegative residual powers, the finite-chart nonidentity test
implies absolute convergence of the bare massive graph. Different charts can
have different dimensions, densities, exponents and projected witnesses.
The characteristic majorant must be nonnegative on the locked Euclidean chart. -/
theorem analytic_paired_charts_routed_graph {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν m : Fin N → ℝ) (hν : ∀ i, 0 < ν i) (hm : ∀ i, 0 < m i)
    (p : Fin N → ScalarMomentum)
    {J : Type*} [Fintype J] (dim : J → ℕ)
    (U K : ∀ j, Set (EuclideanSpace ℝ (Fin (dim j))))
    (hU : ∀ j, IsOpen (U j)) (hconn : ∀ j, IsPreconnected (U j))
    (hK : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U j)
    (d : ∀ j, EuclideanSpace ℝ (Fin (dim j)) → EuclideanSpace ℝ (Fin L × Fin 4))
    (hd : ∀ j, AnalyticOnNhd ℝ (d j) (U j))
    (pD : J → ℝ) (hpD : ∀ j, 1 < pD j) (w : ∀ j, EuclideanSpace ℝ (Fin (dim j)) → ℂ)
    (hw : ∀ j, MemLp (w j) (ENNReal.ofReal (pD j)) (volume.restrict (K j)))
    (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4))) (hμ : μ = ∑ j, pairedChartLaw (K j) (d j) (w j))
    (phase : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hphase : Measurable phase)
    (hphase₁ : ∀ᵐ z ∂μ, ‖phase z‖ ≤ 1) (hγ : ∀ k, 0 ≤ (routedCharacteristic μ phase k).re)
    (hδ : ∀ S : Finset (Fin N), S.Nonempty → 0 ≤ (∑ e ∈ S, ν e) - 2*Module.finrank ℝ (routingFace C S))
    (hnon : ∀ j (S : Finset (Fin N)), S.Nonempty → (∑ e ∈ S, ν e) - 2*Module.finrank ℝ (routingFace C S) = 0 →
      ∃ a : Fin L × Fin 4, ¬ EqOn (fun x => routedProjectedCoordinate C S a (d j x)) 0 (U j))
    (A : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hA : AEStronglyMeasurable A volume)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ k, ‖A k‖ ≤ B*(routedCharacteristic μ phase k).re*routedDenominator C ν m p k) :
    Integrable A := by
  classical
  letI (j : J) : IsFiniteMeasure (pairedChartLaw (K j) (d j) (w j)) :=
    pairedChartLaw_finite (hK j) (d j) (hpD j) (w j) (hw j)
  letI : IsFiniteMeasure μ := hμ ▸ inferInstance
  apply routed_bare_momentum_integrable C hC ν m hν hm p μ phase hphase hphase₁ hγ _ A hA hB hbound
  intro e
  let S (i : Fin N) := (routingShortPrefix i).map e.toEmbedding
  let δ (i : Fin N) := (∑ k ∈ S i, ν k) - 2*Module.finrank ℝ (routingFace C (S i))
  have hs (i : Fin N) : (S i).Nonempty := by
    apply Finset.Nonempty.map
    exact ⟨i, by simp [routingShortPrefix]⟩
  change (∫⁻ z, ∏ i, displacementCost (δ i) (projectedDisplacement C (S i) z) ∂μ) < ⊤
  rw [hμ, lintegral_finset_sum_measure]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  exact routed_analytic_chart_joint C (hU j) (hconn j) (hK j) (hKU j) (d j) (hd j)
    (hpD j) (w j) (hw j) S δ (fun i => hδ _ (hs i)) (fun i => hnon j _ (hs i))

end UV.SewnFlags
