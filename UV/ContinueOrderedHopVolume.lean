import UV.ContinueOrderedHopCells

/-! Simultaneous density limit for bounded, polynomially marked two-band
path coefficients. The slab and the expanding cubic spatial torus may tend
to infinity at independent rates. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace UV.SectorPlane

/-- A winding family can carry complex signs, phases and mark allocations
depending on the volume. Its zero winding is removed inside the sum. -/
def orderedHopNonzeroWord {n : ℕ} (W : OrderedHopWinding → (Fin n → OrderedHopStep) → ℂ)
    (d : Fin n → OrderedHopStep) : ℂ := ∑' w : OrderedHopWinding, if w=0 then 0 else W w d

theorem orderedHop_signed_winding_error {m σ g D : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m)
    (hD : 0 ≤ D) (a b : ℕ)
    (W : ℝ → (n : ℕ) → OrderedHopWinding → (Fin n → OrderedHopStep) → ℂ)
    (hW : ∀ L n w, Measurable (W L n w))
    (hB : ∀ L, 1 ≤ L → ∀ n w d, w ≠ 0 → ‖W L n w d‖ ≤ D*orderedHopWindCost m σ g L a b w d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∀ n, Integrable (orderedHopNonzeroWord (W L n))) ∧
      Summable (fun n => ∫ d, ‖orderedHopNonzeroWord (W L n) d‖) ∧
      (∑' n, ∫ d, ‖orderedHopNonzeroWord (W L n) d‖) ≤ Real.exp (-δ*L)*C := by
  obtain ⟨δ,C,hδ,hC,hE⟩ := orderedHop_all_winding_error hσ hg a b
  refine ⟨δ,D*C,hδ,mul_nonneg hD hC,?_⟩
  intro L hL
  obtain ⟨hI,hS,hCost⟩ := hE L hL
  let f := fun (n : ℕ) (w : OrderedHopWinding) (d : Fin n → OrderedHopStep) => if w=0 then 0 else W L n w d
  have hfield (n w) : Measurable (f n w) := by
    by_cases hw : w=0
    · simp only [f,hw,↓reduceIte]; exact measurable_const
    · simpa only [f,hw,↓reduceIte] using hW L n w
  have hnorm (n w d) : ‖f n w d‖ ≤ D*(if w=0 then 0 else orderedHopWindCost m σ g L a b w d) := by
    by_cases hw : w=0
    · simp [f,hw]
    · simpa only [f,hw,↓reduceIte] using hB L hL n w d hw
  have hSum (n : ℕ) (d : Fin n → OrderedHopStep) := (orderedHop_nonzero_cost_summable hσ hg hL a b d).mul_left D
  have hWord (n : ℕ) (d : Fin n → OrderedHopStep) : Summable (fun w => ‖f n w d‖) :=
    (hSum n d).of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => hnorm n w d)
  have hMeas (n) : Measurable (orderedHopNonzeroWord (W L n)) :=
    measurable_of_tendsto_metrizable' atTop (fun I : Finset OrderedHopWinding =>
      Finset.measurable_sum I (fun w _ => hfield n w))
      (tendsto_pi_nhds.mpr (fun d => (hWord n d).of_norm.hasSum))
  have hPaid (n : ℕ) (d : Fin n → OrderedHopStep) :
      ‖orderedHopNonzeroWord (W L n) d‖ ≤ D*orderedHopWindRemainder m σ g L a b d := by
    apply (norm_tsum_le_tsum_norm (hWord n d)).trans
    exact ((hWord n d).tsum_le_tsum (fun w => hnorm n w d) (hSum n d)).trans_eq (tsum_mul_left.symm.symm)
  have hi (n) := ((hI n).const_mul D).mono' (hMeas n).aestronglyMeasurable (Eventually.of_forall (hPaid n))
  have hb (n : ℕ) : (∫ d, ‖orderedHopNonzeroWord (W L n) d‖) ≤ D*∫ d, orderedHopWindRemainder (n := n) m σ g L a b d := by
    simpa only [integral_const_mul] using integral_mono (hi n).norm ((hI n).const_mul D) (hPaid n)
  have hs := (hS.mul_left D).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hb
  refine ⟨hi,hs,(hs.tsum_le_tsum hb (hS.mul_left D)).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hCost hD).trans_eq (by ring)

/-- For the zero-winding signed trace and its separately bounded winding
images, use the actual clipped slab factor and any joint exhaustion of
time and space. The limit is the original Euclidean closed-word series. -/
theorem orderedHop_joint_density_limit {m σ g D : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (hD : 0 ≤ D)
    (a b : ℕ) (φ : (n : ℕ) → OrderedHopPhases n) (hφ : ∀ n j s, Measurable (φ n j s))
    (M : (n : ℕ) → (Fin n → OrderedHopStep) → ℂ) (hM : ∀ n, Measurable (M n))
    (hBound : ∀ n d, ‖M n d‖ ≤ D*(1+(n:ℝ))^a*(1+orderedHopPathLength d)^b)
    (W : ℝ → (n : ℕ) → OrderedHopWinding → (Fin n → OrderedHopStep) → ℂ)
    (hW : ∀ L n w, Measurable (W L n w))
    (hB : ∀ L, 1 ≤ L → ∀ n w d, w ≠ 0 → ‖W L n w d‖ ≤ D*orderedHopWindCost m σ g L a b w d)
    (T L : ℝ → ℝ) (hT : Tendsto T atTop atTop) (hL : Tendsto L atTop atTop) :
    let F := fun n d => M n d * orderedHopLogWord m σ g (φ n) d
    Tendsto (fun R : ℝ => ∑' n, ∫ d, (orderedHopReturnSlabFraction (T R) d : ℂ) *
        (F n d+orderedHopNonzeroWord (W (L R) n) d))
      atTop (𝓝 (∑' n, ∫ d, F n d)) := by
  let F := fun n d => M n d * orderedHopLogWord m σ g (φ n) d
  let χ := fun (R : ℝ) {n : ℕ} (d : Fin n → OrderedHopStep) => (orderedHopReturnSlabFraction (T R) d : ℂ)
  obtain ⟨hFI,hFS⟩ := orderedHop_marked_log_words_summable hσ hg hD a b φ hφ M hM hBound
  obtain ⟨δ,C,hδ,hC,hErr⟩ := orderedHop_signed_winding_error hσ hg hD a b W hW hB
  have hgood := (hT.eventually (eventually_gt_atTop (0:ℝ))).and (hL.eventually (eventually_ge_atTop (1:ℝ)))
  have hχI (R : ℝ) (n : ℕ) : Measurable (χ R (n := n)) :=
    (Complex.continuous_ofReal.comp (orderedHop_return_slab_continuous _ _)).measurable
  have hχ (R : ℝ) (hR : 0 < T R) (n : ℕ) (d : Fin n → OrderedHopStep) : ‖χ R d‖ ≤ 1 := by
    have h := orderedHop_slab_fraction_unit hR (fun j : Fin (n+1) => (OrderedTwoBandPath.returnPath d).time j)
    simpa only [χ,Complex.norm_real,orderedHopReturnSlabFraction,Real.norm_of_nonneg h.1] using h.2
  have hcut (R : ℝ) (hR : 0 < T R) {n : ℕ} {U : (Fin n → OrderedHopStep) → ℂ} (hi : Integrable U) :
      Integrable (fun d => χ R d * U d) ∧ (∫ d, ‖χ R d * U d‖) ≤ ∫ d, ‖U d‖ := by
    have hb (d : Fin n → OrderedHopStep) : ‖χ R d*U d‖ ≤ ‖U d‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχ R hR n d)
    have hh := hi.norm.mono' ((hχI R n).aestronglyMeasurable.mul hi.aestronglyMeasurable) (Eventually.of_forall hb)
    exact ⟨hh,integral_mono hh.norm hi.norm hb⟩
  let G := fun (R : ℝ) n => ∫ d, χ R d*orderedHopNonzeroWord (W (L R) n) d
  have hg0 : Tendsto (fun R : ℝ => ∑' n, G R n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (show
        Tendsto (fun R : ℝ => Real.exp (-δ*(L R))*C) atTop (𝓝 0) by
      simpa only [neg_mul,zero_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hL.const_mul_atTop hδ)).mul_const C)
    filter_upwards [hgood] with R hR
    obtain ⟨hi,hs,he⟩ := hErr (L R) hR.2
    have hb (n) := (norm_integral_le_integral_norm _).trans ((hcut R hR.1 (hi n)).2)
    have hN := hs.of_nonneg_of_le (fun n => norm_nonneg (G R n)) hb
    exact (norm_tsum_le_tsum_norm hN).trans ((hN.tsum_le_tsum hb hs).trans he)
  have hzero := (orderedHop_slab_remove F hFI hFS).comp hT
  apply (show Tendsto (fun R : ℝ => (∑' n, ∫ d, χ R d * F n d) + ∑' n, G R n) atTop
    (𝓝 (∑' n, ∫ d, F n d)) by simpa only [add_zero] using hzero.add hg0).congr'
  filter_upwards [hgood] with R hR
  obtain ⟨hi,hs,_⟩ := hErr (L R) hR.2
  have hA := hFS.of_norm_bounded (fun n => (norm_integral_le_integral_norm _).trans ((hcut R hR.1 (hFI n)).2))
  have hB' := hs.of_norm_bounded (fun n => (norm_integral_le_integral_norm _).trans ((hcut R hR.1 (hi n)).2))
  rw [←hA.tsum_add hB']
  apply tsum_congr
  intro n
  simp only [mul_add]
  exact (integral_add (hcut R hR.1 (hFI n)).1 (hcut R hR.1 (hi n)).1).symm

end UV.SectorPlane
