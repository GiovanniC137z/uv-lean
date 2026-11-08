import UV.HeatMeasure
import UV.GlobalAssembly
import UV.ResidualCoercivity
import UV.FiniteOrders

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV

/-- The actual dimensional O--QED kernel supplies every source endpoint
budget through its proved representing measure. No moment is an assumption. -/
theorem oqed_kernel_graph_admissible {a M D : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    IsProbabilityMeasure (oqedHeatMeasure a M) ∧
      oqedHeatMeasure a M (Iio 0) = 0 ∧ GapOrEndpoint (oqedHeatMeasure a M) D := by
  refine ⟨oqedHeatMeasure_probability ha.le hM, ?_, Or.inr ⟨?_, ?_⟩⟩
  · exact measure_mono_null (show Iio (0 : ℝ) ⊆ Iic 0 from fun x h => (show x < 0 from h).le)
      (oqedHeatMeasure_nonnegative_support ha M)
  · exact oqedHeatMeasure_no_atom_zero ha M
  · exact oqedHeatMeasure_inverseMoment_finite ha M (by linarith)

/-- The actual O--QED factor, with the declared infrared covariance. -/
def oqedLine (a M : ℝ) (E : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  kernel a M (‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)

theorem oqedLine_eq_schwingerLine {a : ℝ} (ha : 0 < a) (M : ℝ)
    (E : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin 4)) :
    oqedLine a M E q = schwingerLine (oqedHeatMeasure a M) E 1 q := by
  unfold oqedLine schwingerLine
  rw [one_pow, one_mul, oqedHeatMeasure_laplace ha.le (sq_nonneg _) M]

/-- Polynomial-numerator alternative of the O--QED fixed-graph theorem. The
selected lines carry the actual dimensional kernels; all other multipliers
remain arbitrary bounded measurable functions. Kernel normalization, positive
support, no zero atom, and the endpoint moments are derived from subordination. -/
theorem oqed_fixed_graph_polynomial
    {κ P F : Type*} [Fintype κ] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Croute : Matrix (Fin L ⊕ κ) (Fin L) ℝ)
    (hminor : Matrix.det (Croute.submatrix Sum.inl id) ≠ 0)
    (R : P → (Fin L ⊕ κ) → LoopMomentum) {B C D : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : ∀ p, ‖R p‖ ≤ B)
    (a M : Fin L → ℝ) (ha : ∀ j, 0 < a j) (hM : ∀ j, 0 ≤ M j)
    (E : Fin L → ℝ → ℝ) (α0 K : Fin L → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (Φ Eu : κ → ℝ → ℝ) (Menv : κ → ℝ)
    (hmΦ : ∀ u, Measurable (Φ u)) (hΦ : ∀ u z, 0 ≤ z → ‖Φ u z‖ ≤ Menv u)
    (hmEu : ∀ u, Measurable (Eu u)) (hEu : ∀ u, IntegrableOn (Eu u) (Ioi 0))
    (hposu : ∀ u α, 0 < α → 0 ≤ Eu u α)
    (N : P → (Fin L → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k =>
        ((∏ j, oqedLine (a j) (M j) (E j)
          (rectangularMomentum Croute R (Sum.inl j) p k)) *
          (∏ u, boundedCovariance (Φ u) (Eu u)
            (rectangularMomentum Croute R (Sum.inr u) p k))) • N p k)
          (Measure.pi fun _ : Fin L => volume) ∧
      (∫ k, ‖((∏ j, oqedLine (a j) (M j) (E j)
          (rectangularMomentum Croute R (Sum.inl j) p k)) *
          (∏ u, boundedCovariance (Φ u) (Eu u)
            (rectangularMomentum Croute R (Sum.inr u) p k))) • N p k‖
          ∂(Measure.pi fun _ : Fin L => volume)) ≤ A := by
  have hadm j := oqed_kernel_graph_admissible (ha j) (hM j) hD
  have h := damped_basis_rectangular Croute hminor R hB hC hD hR
    (fun j => oqedHeatMeasure (a j) (M j)) (fun j => (hadm j).2.1)
    (fun j => (hadm j).2.2) E (fun _ => 1) α0 K hmE hE hpos hα0 hK
    (fun _ => by norm_num) Φ Eu Menv hmΦ hΦ hmEu hEu hposu N hmN hN
  simpa only [oqedLine_eq_schwingerLine (ha _)] using h

/-- Actual O--QED kernels and the merely bounded comparison multipliers on
other lines remain separate functions; no model placement rule is altered. -/
def oqedOrBoundedMultiplier {I κ : Type*} (a M : I → ℝ)
    (Φ : κ → EuclideanSpace ℝ (Fin 4) → ℝ) :
    (I ⊕ κ) → EuclideanSpace ℝ (Fin 4) → ℝ :=
  Sum.elim (fun i q => kernel (a i) (M i) (‖q‖ ^ 2)) Φ

/-- Signed-linear-residual alternative of the O--QED fixed-graph theorem.
Bounded nonselected factors may have either sign; their absolute comparison
uses zero exponential depth and zero growth budget. Actual kernel envelopes
retain the constants exp(aᵢMᵢ), without changing their normalized measures. -/
theorem oqed_fixed_graph_residual
    {I κ P F : Type*} [Fintype I] [Fintype κ] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Croute : Matrix (I ⊕ κ) (Fin L) ℝ)
    (R : (I ⊕ κ) → P → EuclideanSpace ℝ (Fin 4)) (b : (I ⊕ κ) → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hR : ∀ i p, ‖R i p‖ ≤ b i)
    (a M v : I → ℝ) (ha : ∀ i, 0 < a i) (hM : ∀ i, 0 ≤ M i)
    (Φ : κ → EuclideanSpace ℝ (Fin 4) → ℝ) (Menv : κ → ℝ)
    (hmΦ : ∀ u, Measurable (Φ u)) (hΦ : ∀ u q, ‖Φ u q‖ ≤ Menv u)
    (cov : (I ⊕ κ) → EuclideanSpace ℝ (Fin 4) → ℝ) (Ienv : (I ⊕ κ) → ℝ)
    (hmcov : ∀ i, Measurable (cov i))
    (hcov : ∀ i q, 0 ≤ cov i q ∧ cov i q ≤ Ienv i)
    (N : P → EuclideanSpace ℝ (Fin L × Fin 4) → F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D) * exp
      (∑ i : I, v i * ‖residualRouting Croute (Sum.inl i) k + R (Sum.inl i) p‖))
    (hcontrol : ∀ k : EuclideanSpace ℝ (Fin L × Fin 4), ‖k‖ = 1 →
      0 < ∑ i : I, (a i - v i) * ‖residualRouting Croute (Sum.inl i) k‖) :
    ∃ Mmajorant : EuclideanSpace ℝ (Fin L × Fin 4) → ℝ, Integrable Mmajorant volume ∧
      (∀ p k, ‖residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (oqedOrBoundedMultiplier a M Φ) N p k‖ ≤ Mmajorant k) ∧
      ∀ p, Integrable (residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (oqedOrBoundedMultiplier a M Φ) N p) volume ∧
        (∫ k, ‖residualGraph (fun i p k => residualRouting Croute i k + R i p)
          cov (oqedOrBoundedMultiplier a M Φ) N p k‖) ≤ ∫ k, Mmajorant k := by
  let Ψ := oqedOrBoundedMultiplier a M Φ
  let q := fun i p k => residualRouting Croute i k + R i p
  let d : I ⊕ κ → ℝ := Sum.elim a (fun _ => 0)
  let growth : I ⊕ κ → ℝ := Sum.elim v (fun _ => 0)
  let Benv : I ⊕ κ → ℝ := Sum.elim (fun i => exp (a i * M i)) Menv
  have hmΨ : ∀ i, Measurable (Ψ i) := by
    intro i
    cases i with
    | inl i => dsimp [Ψ, oqedOrBoundedMultiplier, kernel, depthProfile]; fun_prop
    | inr u => exact hmΦ u
  have hBenv : ∀ i, 0 ≤ Benv i := by
    intro i
    cases i with
    | inl i => exact exp_nonneg _
    | inr u => exact (norm_nonneg (Φ u 0)).trans (hΦ u 0)
  have hΨ : ∀ i x, 0 ≤ |Ψ i x| ∧
      |Ψ i x| ≤ Benv i * exp (-d i * residualSize false x) := by
    intro i x
    refine ⟨abs_nonneg _, ?_⟩
    cases i with
    | inl i =>
      have hn : 0 ≤ kernel (a i) (M i) (‖x‖ ^ 2) :=
        (exp_nonneg _).trans (kernel_lower (ha i).le (hM i) (sq_nonneg _))
      change |kernel (a i) (M i) (‖x‖ ^ 2)| ≤
        exp (a i * M i) * exp (-a i * residualSize false x)
      rw [abs_of_nonneg hn]
      simpa only [residualSize, Bool.false_eq_true, ite_false, Real.sqrt_sq (norm_nonneg x)] using
        kernel_upper (M := M i) (ha i).le (sq_nonneg ‖x‖)
    | inr u => simpa [Ψ, oqedOrBoundedMultiplier, Benv, d, residualSize] using hΦ u x
  have hN' : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D) * exp
      (∑ i, growth i * residualSize false (q i p k)) := by
    intro p k
    simpa [growth, q, residualSize, Fintype.sum_sum_type] using hN p k
  have hcontrol' : ∀ k, ‖k‖ = 1 →
      0 < ∑ i, (d i - growth i) * ‖residualRouting Croute i k‖ := by
    intro k hk
    simpa [d, growth, Fintype.sum_sum_type] using hcontrol k hk
  obtain ⟨Mmaj, hiM, hbM, hgraph⟩ := residual_coercivity_graph false Croute R b hb hR
    cov (fun i x => |Ψ i x|) Ienv Benv d growth hmcov
    (fun i => by simpa only [Real.norm_eq_abs] using (hmΨ i).norm)
    hBenv hcov hΨ N hC hD hmN hN' hcontrol'
  have hnorm p k : ‖residualGraph q cov Ψ N p k‖ =
      ‖residualGraph q cov (fun i x => |Ψ i x|) N p k‖ := by
    simp [residualGraph, norm_smul, norm_prod, norm_mul]
  have hbound p k : ‖residualGraph q cov Ψ N p k‖ ≤ Mmaj k := by
    rw [hnorm]
    exact hbM p k
  have hmgraph p : StronglyMeasurable (residualGraph q cov Ψ N p) := by
    apply StronglyMeasurable.smul _ (hmN p)
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    have hq : Measurable (q i p) := by dsimp [q]; fun_prop
    exact ((hmcov i).comp hq).mul ((hmΨ i).comp hq)
  refine ⟨Mmaj, hiM, hbound, ?_⟩
  intro p
  have hi := hiM.mono' (hmgraph p).aestronglyMeasurable (Filter.Eventually.of_forall (hbound p))
  exact ⟨hi, integral_mono_ae hi.norm hiM (Filter.Eventually.of_forall (hbound p))⟩

/-- A verified forest certificate for the actual O--QED graph transfers its
uniform bound. The certificate stores sector scales, Jacobians, infrared
control, and the actual simultaneous envelope; graph integrability is derived. -/
theorem oqed_fixed_graph_forest
    {I P H : Type} [Fintype I] [Fintype H] {L : ℕ}
    {A : H → Type} [∀ h, MeasurableSpace (A h)]
    (g : ForestGraphData P (EuclideanSpace ℝ (Fin L × Fin 4)) H A)
    (Croute : Matrix I (Fin L) ℝ)
    (R : I → P → EuclideanSpace ℝ (Fin 4)) (a M : I → ℝ)
    (cov : I → EuclideanSpace ℝ (Fin 4) → ℝ)
    (N : P → EuclideanSpace ℝ (Fin L × Fin 4) → ℂ)
    (hmeasure : g.μ = volume)
    (hactual : ∀ p k, g.integrand p k =
      residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (fun i q => kernel (a i) (M i) (‖q‖ ^ 2)) N p k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (fun i q => kernel (a i) (M i) (‖q‖ ^ 2)) N p) volume ∧
      (∫ k, ‖residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (fun i q => kernel (a i) (M i) (‖q‖ ^ 2)) N p k‖) ≤ B := by
  have h := (SourceGraph.forest g).bounded
  have heq : g.integrand = (fun p k =>
      residualGraph (fun i p k => residualRouting Croute i k + R i p)
        cov (fun i q => kernel (a i) (M i) (‖q‖ ^ 2)) N p k) :=
    funext fun p => funext (hactual p)
  simpa only [SourceGraph.integrand, SourceGraph.measure, heq, hmeasure] using h

end UV
