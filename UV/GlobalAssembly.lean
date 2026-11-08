import UV.SchwingerEnvelope
import UV.JointMajorant
import UV.Gap
import UV.RankMinor

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV

/-- The two source alternatives, with the zero atom stated independently of
its inverse moment. Positive support is a separate representing-measure datum. -/
def GapOrEndpoint (ρ : Measure ℝ) (D : ℝ) : Prop :=
  (∃ τstar : ℝ, 0 < τstar ∧ ∀ᵐ τ ∂ρ, τstar ≤ τ) ∨
    (ρ {0} = 0 ∧ inverseMoment ρ (1 + D / 2) < ⊤)

theorem GapOrEndpoint.no_atom {ρ : Measure ℝ} {D : ℝ}
    (h : GapOrEndpoint ρ D) : ρ {0} = 0 := by
  rcases h with ⟨τstar, hτstar, hgap⟩ | ⟨hzero, _⟩
  · exact (positive_gap_support_no_atom ρ hτstar hgap).2
  · exact hzero

theorem GapOrEndpoint.endpoint {ρ : Measure ℝ} [IsFiniteMeasure ρ] {D : ℝ}
    (h : GapOrEndpoint ρ D) (hD : 0 ≤ D) :
    inverseMoment ρ (1 + D / 2) < ⊤ := by
  rcases h with ⟨τstar, hτstar, hgap⟩ | ⟨_, hM⟩
  · exact positive_gap_selected_endpoint ρ hτstar hgap hD
  · exact hM

/-- Arbitrary bounded multipliers on nonselected lines include the identity. -/
def boundedCovariance (Φ E : ℝ → ℝ) (q : LoopMomentum) : ℝ :=
  Φ (‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)

theorem boundedCovariance_measurable {Φ E : ℝ → ℝ}
    (hΦ : Measurable Φ) (hE : Measurable E) : Measurable (boundedCovariance Φ E) :=
  (hΦ.comp (by fun_prop)).mul ((schwinger_covariance_measurable hE).comp (by fun_prop))

theorem boundedCovariance_norm_le {Φ E : ℝ → ℝ} {M : ℝ}
    (hΦ : ∀ z, 0 ≤ z → ‖Φ z‖ ≤ M)
    (hE : IntegrableOn E (Ioi 0)) (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (q : LoopMomentum) :
    ‖boundedCovariance Φ E q‖ ≤ M * ∫ α : ℝ in Ioi 0, E α := by
  have hM : 0 ≤ M := (norm_nonneg (Φ 0)).trans (hΦ 0 le_rfl)
  rw [boundedCovariance, norm_mul,
    Real.norm_of_nonneg (schwinger_covariance_nonneg hpos _)]
  exact mul_le_mul (hΦ _ (sq_nonneg _))
    (schwinger_covariance_le_integral hE hpos (sq_nonneg _))
    (schwinger_covariance_nonneg hpos _) hM

/-- Full damped-basis corollary: only selected lines require representing
measures and a gap or endpoint moment. Every other multiplier may be an
arbitrary bounded measurable function. The original polynomial numerator
and bounded external shift are the source hypotheses, not a routed envelope. -/
theorem damped_basis_graph
    {ι κ P F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0)
    (E : ι → ℝ → ℝ) (a α0 K : ι → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j) {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcontrol : ∀ j, GapOrEndpoint (ρ j) D)
    (Φ Eu : κ → ℝ → ℝ) (M : κ → ℝ)
    (hmΦ : ∀ u, Measurable (Φ u)) (hΦ : ∀ u z, 0 ≤ z → ‖Φ u z‖ ≤ M u)
    (hmEu : ∀ u, Measurable (Eu u)) (hEu : ∀ u, IntegrableOn (Eu u) (Ioi 0))
    (hposu : ∀ u α, 0 < α → 0 ≤ Eu u α)
    (qu : κ → P → (ι → LoopMomentum) → LoopMomentum)
    (hmqu : ∀ u p, Measurable (qu u p))
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum)) (hb : ∀ p, ‖b p‖ ≤ B)
    (N : P → (ι → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k =>
        ((∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) *
          (∏ u, boundedCovariance (Φ u) (Eu u) (qu u p k))) • N p k)
          (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖((∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) *
          (∏ u, boundedCovariance (Φ u) (Eu u) (qu u p k))) • N p k‖
          ∂(Measure.pi fun _ : ι => volume)) ≤ A := by
  let U := ∏ u, M u * (∫ α : ℝ in Ioi 0, Eu u α)
  have hU : 0 ≤ U := by
    apply Finset.prod_nonneg
    intro u _
    apply mul_nonneg ((norm_nonneg (Φ u 0)).trans (hΦ u 0 le_rfl))
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hposu u α hα
  let Nu : P → (ι → LoopMomentum) → F := fun p k =>
    (∏ u, boundedCovariance (Φ u) (Eu u) (qu u p k)) • N p k
  have hmNu : ∀ p, StronglyMeasurable (Nu p) := by
    intro p
    apply StronglyMeasurable.smul _ (hmN p)
    exact (Finset.measurable_prod _ fun u _ =>
      (boundedCovariance_measurable (hmΦ u) (hmEu u)).comp (hmqu u p)).stronglyMeasurable
  have hNu : ∀ p k, ‖Nu p k‖ ≤ (U * C) * (1 + ‖k‖ ^ D) := by
    intro p k
    have hp : ‖∏ u, boundedCovariance (Φ u) (Eu u) (qu u p k)‖ ≤ U := by
      rw [norm_prod]
      apply Finset.prod_le_prod
      · intro u _; exact norm_nonneg _
      · intro u _; exact boundedCovariance_norm_le (hΦ u) (hEu u) (hposu u) _
    change ‖(∏ u, boundedCovariance (Φ u) (Eu u) (qu u p k)) • N p k‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ U * (C * (1 + ‖k‖ ^ D)) := mul_le_mul hp (hN p k) (norm_nonneg _) hU
      _ = _ := by ring
  have h := schwinger_routed_graph ρ hneg (fun j => (hcontrol j).no_atom) E a α0 K
    hmE hE hpos hα0 hK ha hB (mul_nonneg hU hC) hD
    (fun j => (hcontrol j).endpoint hD) e b hb Nu hmNu hNu
  let A := |(LinearMap.det e.toLinearMap)⁻¹| *
    (U * C * (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)) *
      ∏ j, (schwingerMomentBound (ρ j) (E j) (a j) 0 (α0 j) (K j) +
        schwingerMomentBound (ρ j) (E j) (a j) D (α0 j) (K j))
  refine ⟨max 0 A, le_max_left _ _, ?_⟩
  intro p
  have hp := h p
  simp only [Nu, smul_smul] at hp
  exact ⟨hp.1, hp.2.trans (le_max_right _ _)⟩

/-- Compact external data supply the uniform shift bound used in the graph
proof. Restricting `P` to the compact set gives the preceding bounded form. -/
theorem compact_routing_shift_bound {P V : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] {K : Set P} (hK : IsCompact K)
    (b : P → V) (hb : ContinuousOn b K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K, ‖b p‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hb
  exact ⟨max 0 B, le_max_left _ _, fun p hp => (hB p hp).trans (le_max_right _ _)⟩

/-- The actual nonnegative line-parameter absolute majorant of a graph. -/
def jointAbsolute {I X F : Type*} [Fintype I] [NormedAddCommGroup F]
    (E : I → ℝ → ℝ) (a : I → ℝ) (q : I → X → LoopMomentum) (N : X → F)
    (z : X × (I → ℝ × ℝ)) : ℝ :=
  ‖N z.1‖ * ∏ i, exp (-(z.2 i).1 * ((a i) ^ 2 * ‖q i z.1‖ ^ 2)) *
    (E i (z.2 i).2 * exp (-(z.2 i).2 * ‖q i z.1‖ ^ 2))

theorem jointAbsolute_measurable {I X F : Type*} [Fintype I]
    [MeasurableSpace X] [NormedAddCommGroup F]
    (E : I → ℝ → ℝ) (a : I → ℝ) (q : I → X → LoopMomentum) (N : X → F)
    (hmE : ∀ i, Measurable (E i)) (hmq : ∀ i, Measurable (q i))
    (hmN : StronglyMeasurable N) : Measurable (jointAbsolute E a q N) := by
  apply ((hmN.norm.measurable).comp measurable_fst).mul
  apply Finset.measurable_prod
  intro i _
  have hq : Measurable (fun z : X × (I → ℝ × ℝ) => ‖q i z.1‖ ^ 2) :=
    ((hmq i).comp measurable_fst).norm.pow_const 2
  have hα : Measurable (fun z : X × (I → ℝ × ℝ) => (z.2 i).2) := by fun_prop
  have hτ : Measurable (fun z : X × (I → ℝ × ℝ) => (z.2 i).1) := by fun_prop
  exact (hτ.neg.mul (hq.const_mul ((a i) ^ 2))).exp.mul
    (((hmE i).comp hα).mul (hα.neg.mul hq).exp)

/-- Full routed graph integrability entails its actual joint-parameter
integrability; measurability of the latter is derived from line and graph data. -/
theorem jointAbsolute_integrable_of_graph
    {I X F : Type*} [Fintype I] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) [SigmaFinite μ]
    (ρ : I → Measure ℝ) [∀ i, IsFiniteMeasure (ρ i)]
    (hneg : ∀ i, ρ i (Iio 0) = 0) (hzero : ∀ i, ρ i {0} = 0)
    (E : I → ℝ → ℝ) (a : I → ℝ) (q : I → X → LoopMomentum) (N : X → F)
    (hmE : ∀ i, Measurable (E i)) (hE : ∀ i, IntegrableOn (E i) (Ioi 0))
    (hpos : ∀ i α, 0 < α → 0 ≤ E i α)
    (hmq : ∀ i, Measurable (q i)) (hmN : StronglyMeasurable N)
    (hgraph : Integrable (fun k => (∏ i, schwingerLine (ρ i) (E i) (a i) (q i k)) • N k) μ) :
    Integrable (jointAbsolute E a q N)
      (μ.prod (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0))))) := by
  apply actual_joint_majorant_integrable μ ρ E a (fun i k => ‖q i k‖ ^ 2) (fun k => ‖N k‖)
    hneg hzero hE hpos (fun _ _ => sq_nonneg _)
    (jointAbsolute_measurable E a q N hmE hmq hmN).stronglyMeasurable.aestronglyMeasurable
  have heq : (fun k => ‖(∏ i, schwingerLine (ρ i) (E i) (a i) (q i k)) • N k‖) =
      (fun k => ‖‖N k‖‖ * ∏ i,
        (laplace (ρ i) ((a i) ^ 2 * ‖q i k‖ ^ 2) *
          schwingerCovariance (E i) (‖q i k‖ ^ 2))) := by
    ext k
    rw [norm_smul, Real.norm_of_nonneg
      (Finset.prod_nonneg fun i _ => schwingerLine_nonneg (ρ i) (hpos i) (a i) (q i k)),
      norm_norm]
    simp only [schwingerLine]
    ring
  exact heq ▸ hgraph.norm

/-- Selected and nonselected routings, indexed by their actual disjoint union. -/
def assembledMomentum {ι κ P : Type*} [Fintype ι]
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum))
    (qu : κ → P → (ι → LoopMomentum) → LoopMomentum)
    (p : P) : (ι ⊕ κ) → (ι → LoopMomentum) → LoopMomentum :=
  Sum.elim (fun j k => (e k + b p) j) (fun u k => qu u p k)

/-- Global Euclidean convergence, including the actual joint majorant. All
virtual lines occur in the graph. The selected full-rank routing, original
polynomial numerator, infrared data, and either source moment alternative
are the only substantive assumptions. -/
theorem global_uv_graph
    {ι κ P F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0)
    (E : ι → ℝ → ℝ) (a α0 K : ι → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j) {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcontrol : ∀ j, GapOrEndpoint (ρ j) D)
    (ρu : κ → Measure ℝ) [∀ u, IsFiniteMeasure (ρu u)]
    (hnegu : ∀ u, ρu u (Iio 0) = 0) (hzerou : ∀ u, ρu u {0} = 0)
    (Eu : κ → ℝ → ℝ) (au : κ → ℝ)
    (hmEu : ∀ u, Measurable (Eu u)) (hEu : ∀ u, IntegrableOn (Eu u) (Ioi 0))
    (hposu : ∀ u α, 0 < α → 0 ≤ Eu u α)
    (qu : κ → P → (ι → LoopMomentum) → LoopMomentum)
    (hmqu : ∀ u p, Measurable (qu u p))
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum)) (hb : ∀ p, ‖b p‖ ≤ B)
    (N : P → (ι → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k =>
        (∏ v, schwingerLine (Sum.elim ρ ρu v) (Sum.elim E Eu v) (Sum.elim a au v)
          (assembledMomentum e b qu p v k)) • N p k)
          (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖(∏ v, schwingerLine (Sum.elim ρ ρu v) (Sum.elim E Eu v) (Sum.elim a au v)
          (assembledMomentum e b qu p v k)) • N p k‖
          ∂(Measure.pi fun _ : ι => volume)) ≤ A ∧
      Integrable (jointAbsolute (Sum.elim E Eu) (Sum.elim a au)
        (assembledMomentum e b qu p) (N p))
        ((Measure.pi fun _ : ι => volume).prod
          (Measure.pi (fun v => (Sum.elim ρ ρu v).prod (volume.restrict (Ioi 0))))) := by
  have hzero : ∀ j, ρ j {0} = 0 := fun j => (hcontrol j).no_atom
  have h := global_schwinger_graph ρ hneg hzero E a α0 K hmE hE hpos hα0 hK ha hB hC hD
    (fun j => (hcontrol j).endpoint hD) ρu hnegu hzerou Eu au hmEu hEu hposu qu hmqu e b hb N hmN hN
  let A := |(LinearMap.det e.toLinearMap)⁻¹| *
    (((∏ u, (ρu u (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, Eu u α)) * C) *
      (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)) *
      ∏ j, (schwingerMomentBound (ρ j) (E j) (a j) 0 (α0 j) (K j) +
        schwingerMomentBound (ρ j) (E j) (a j) D (α0 j) (K j))
  refine ⟨max 0 A, le_max_left _ _, ?_⟩
  intro p
  have hp : Integrable (fun k =>
      (∏ v, schwingerLine (Sum.elim ρ ρu v) (Sum.elim E Eu v) (Sum.elim a au v)
        (assembledMomentum e b qu p v k)) • N p k)
        (Measure.pi fun _ : ι => volume) := by
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, assembledMomentum] using (h p).1
  refine ⟨hp, ?_, ?_⟩
  · have hbound := (h p).2.trans (le_max_right 0 A)
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, assembledMomentum] using hbound
  · haveI : ∀ v : ι ⊕ κ, IsFiniteMeasure (Sum.elim ρ ρu v) := by
      intro v; cases v <;> dsimp <;> infer_instance
    apply jointAbsolute_integrable_of_graph _ (Sum.elim ρ ρu)
      (Sum.rec hneg hnegu) (Sum.rec hzero hzerou) (Sum.elim E Eu) (Sum.elim a au)
      (assembledMomentum e b qu p) (N p) (Sum.rec hmE hmEu) (Sum.rec hE hEu)
      (Sum.rec hpos hposu) _ (hmN p) hp
    intro v
    cases v with
    | inl j => dsimp [assembledMomentum]; fun_prop
    | inr u => exact hmqu u p

/-- The original rectangular affine momentum routing, before row selection. -/
def rectangularMomentum {I P : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (R : P → I → LoopMomentum)
    (i : I) (p : P) (k : Fin L → LoopMomentum) : LoopMomentum :=
  (∑ j, C i j • k j) + R p i

theorem rectangularMomentum_measurable {I P : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (R : P → I → LoopMomentum) (i : I) (p : P) :
    Measurable (rectangularMomentum C R i p) := by
  unfold rectangularMomentum
  fun_prop

theorem rectangularMomentum_apply {I P : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (R : P → I → LoopMomentum)
    (i : I) (p : P) (k : Fin L → LoopMomentum) (ν : Fin 4) :
    rectangularMomentum C R i p k ν = (∑ j, C i j * k j ν) + R p i ν := by
  unfold rectangularMomentum
  rw [PiLp.add_apply]
  congr 1
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) ν) (∑ j, C i j • k j) = _
  rw [map_sum]
  simp [PiLp.projₗ]

private def rowPartition {J I : Type*} (s : J ↪ I) :
    J ⊕ {i : I // i ∉ Set.range s} ≃ I := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective s s.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range s))

private theorem rowPartition_inl {J I : Type*} (s : J ↪ I) (j : J) :
    rowPartition s (Sum.inl j) = s j := rfl

private theorem rowPartition_inr {J I : Type*} (s : J ↪ I)
    (u : {i : I // i ∉ Set.range s}) : rowPartition s (Sum.inr u) = u.val := rfl

/-- The source's rectangular full-column-rank routing selects its own
invertible block. No independent-line routing or graph integrability is
postulated. The conclusion includes every original virtual line and all of
its actual proper-time and Laplace parameters. -/
theorem global_uv_rectangular
    {I P F : Type*} [Fintype I] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Croute : Matrix I (Fin L) ℝ) (hrank : Croute.rank = L)
    (R : P → I → LoopMomentum) {B C D : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : ∀ p, ‖R p‖ ≤ B)
    (ρ : I → Measure ℝ) [∀ i, IsFiniteMeasure (ρ i)]
    (hneg : ∀ i, ρ i (Iio 0) = 0) (hcontrol : ∀ i, GapOrEndpoint (ρ i) D)
    (E : I → ℝ → ℝ) (a α0 K : I → ℝ)
    (hmE : ∀ i, Measurable (E i)) (hE : ∀ i, IntegrableOn (E i) (Ioi 0))
    (hpos : ∀ i α, 0 < α → 0 ≤ E i α)
    (hα0 : ∀ i, 0 < α0 i) (hK : ∀ i, ∀ α ∈ Ioc 0 (α0 i), E i α ≤ K i)
    (ha : ∀ i, 0 < a i)
    (N : P → (Fin L → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k => (∏ i, schwingerLine (ρ i) (E i) (a i)
        (rectangularMomentum Croute R i p k)) • N p k)
        (Measure.pi fun _ : Fin L => volume) ∧
      (∫ k, ‖(∏ i, schwingerLine (ρ i) (E i) (a i)
        (rectangularMomentum Croute R i p k)) • N p k‖
        ∂(Measure.pi fun _ : Fin L => volume)) ≤ A ∧
      Integrable (jointAbsolute E a (fun i => rectangularMomentum Croute R i p) (N p))
        ((Measure.pi fun _ : Fin L => volume).prod
          (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0))))) := by
  classical
  obtain ⟨s, hs⟩ := exists_invertible_row_minor Croute hrank
  obtain ⟨e, he⟩ := exists_selected_routing (Croute.submatrix s id) hs
  let U := {i : I // i ∉ Set.range s}
  let b : P → (Fin L → LoopMomentum) := fun p j => R p (s j)
  let qu : U → P → (Fin L → LoopMomentum) → LoopMomentum :=
    fun u => rectangularMomentum Croute R u.val
  have hb : ∀ p, ‖b p‖ ≤ B := by
    intro p
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    exact (norm_le_pi_norm (R p) (s j)).trans (hR p)
  have hselected : ∀ p k j, (e k + b p) j = rectangularMomentum Croute R (s j) p k := by
    intro p k j
    ext ν
    rw [rectangularMomentum_apply]
    change e k j ν + R p (s j) ν = _
    rw [selected_routing_apply (Croute.submatrix s id) e he]
    rfl
  have h := global_uv_graph (fun j => ρ (s j)) (fun j => hneg (s j))
    (fun j => E (s j)) (fun j => a (s j)) (fun j => α0 (s j)) (fun j => K (s j))
    (fun j => hmE (s j)) (fun j => hE (s j)) (fun j => hpos (s j))
    (fun j => hα0 (s j)) (fun j => hK (s j)) (fun j => ha (s j)) hB hC hD
    (fun j => hcontrol (s j)) (fun u : U => ρ u.val) (fun u => hneg u.val)
    (fun u => (hcontrol u.val).no_atom) (fun u => E u.val) (fun u => a u.val)
    (fun u => hmE u.val) (fun u => hE u.val) (fun u => hpos u.val) qu
    (fun u p => rectangularMomentum_measurable Croute R u.val p) e b hb N hmN hN
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A, hA, ?_⟩
  intro p
  have hprod (k : Fin L → LoopMomentum) :
      (∏ i, schwingerLine (ρ i) (E i) (a i) (rectangularMomentum Croute R i p k)) =
      ∏ v : Fin L ⊕ U, schwingerLine
        (Sum.elim (fun j => ρ (s j)) (fun u : U => ρ u.val) v)
        (Sum.elim (fun j => E (s j)) (fun u : U => E u.val) v)
        (Sum.elim (fun j => a (s j)) (fun u : U => a u.val) v)
        (assembledMomentum e b qu p v k) := by
    calc
      _ = ∏ v : Fin L ⊕ U, schwingerLine (ρ (rowPartition s v))
          (E (rowPartition s v)) (a (rowPartition s v))
          (rectangularMomentum Croute R (rowPartition s v) p k) :=
        ((rowPartition s).prod_comp _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v _
        cases v with
        | inl j =>
          change schwingerLine (ρ (s j)) (E (s j)) (a (s j))
            (rectangularMomentum Croute R (s j) p k) =
            schwingerLine (ρ (s j)) (E (s j)) (a (s j)) ((e k + b p) j)
          rw [hselected]
        | inr u => rfl
  have hi : Integrable (fun k => (∏ i, schwingerLine (ρ i) (E i) (a i)
      (rectangularMomentum Croute R i p k)) • N p k)
      (Measure.pi fun _ : Fin L => volume) := by
    simpa only [hprod] using (h p).1
  refine ⟨hi, ?_, ?_⟩
  · simpa only [hprod] using (h p).2.1
  · exact jointAbsolute_integrable_of_graph _ ρ hneg (fun i => (hcontrol i).no_atom)
      E a (fun i => rectangularMomentum Croute R i p) (N p) hmE hE hpos
      (fun i => rectangularMomentum_measurable Croute R i p) (hmN p) hi

/-- The damped-basis corollary in original rectangular routing coordinates.
Finite line labels are enumerated as selected and remaining lines. The
selected minor is invertible; all other multipliers are merely bounded and
measurable. Identity multipliers require no representing measure or moment. -/
theorem damped_basis_rectangular
    {κ P F : Type*} [Fintype κ] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Croute : Matrix (Fin L ⊕ κ) (Fin L) ℝ)
    (hminor : Matrix.det (Croute.submatrix Sum.inl id) ≠ 0)
    (R : P → (Fin L ⊕ κ) → LoopMomentum) {B C D : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : ∀ p, ‖R p‖ ≤ B)
    (ρ : Fin L → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hcontrol : ∀ j, GapOrEndpoint (ρ j) D)
    (E : Fin L → ℝ → ℝ) (a α0 K : Fin L → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j)
    (Φ Eu : κ → ℝ → ℝ) (M : κ → ℝ)
    (hmΦ : ∀ u, Measurable (Φ u)) (hΦ : ∀ u z, 0 ≤ z → ‖Φ u z‖ ≤ M u)
    (hmEu : ∀ u, Measurable (Eu u)) (hEu : ∀ u, IntegrableOn (Eu u) (Ioi 0))
    (hposu : ∀ u α, 0 < α → 0 ≤ Eu u α)
    (N : P → (Fin L → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k =>
        ((∏ j, schwingerLine (ρ j) (E j) (a j)
          (rectangularMomentum Croute R (Sum.inl j) p k)) *
          (∏ u, boundedCovariance (Φ u) (Eu u)
            (rectangularMomentum Croute R (Sum.inr u) p k))) • N p k)
          (Measure.pi fun _ : Fin L => volume) ∧
      (∫ k, ‖((∏ j, schwingerLine (ρ j) (E j) (a j)
          (rectangularMomentum Croute R (Sum.inl j) p k)) *
          (∏ u, boundedCovariance (Φ u) (Eu u)
            (rectangularMomentum Croute R (Sum.inr u) p k))) • N p k‖
          ∂(Measure.pi fun _ : Fin L => volume)) ≤ A := by
  classical
  obtain ⟨e, he⟩ := exists_selected_routing (Croute.submatrix Sum.inl id) hminor
  let b : P → (Fin L → LoopMomentum) := fun p j => R p (Sum.inl j)
  let qu : κ → P → (Fin L → LoopMomentum) → LoopMomentum :=
    fun u => rectangularMomentum Croute R (Sum.inr u)
  have hb : ∀ p, ‖b p‖ ≤ B := by
    intro p
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    exact (norm_le_pi_norm (R p) (Sum.inl j)).trans (hR p)
  have hselected : ∀ p k j, (e k + b p) j =
      rectangularMomentum Croute R (Sum.inl j) p k := by
    intro p k j
    ext ν
    rw [rectangularMomentum_apply]
    change e k j ν + R p (Sum.inl j) ν = _
    rw [selected_routing_apply (Croute.submatrix Sum.inl id) e he]
    rfl
  obtain ⟨A, hA, h⟩ := damped_basis_graph ρ hneg E a α0 K hmE hE hpos hα0 hK ha
    hB hC hD hcontrol Φ Eu M hmΦ hΦ hmEu hEu hposu qu
    (fun u p => rectangularMomentum_measurable Croute R (Sum.inr u) p) e b hb N hmN hN
  refine ⟨A, hA, ?_⟩
  intro p
  simpa only [hselected, qu] using h p

/-- Absolute Fubini identifies the actual joint majorant integral with the
original graph comparison integral, so the same bound is uniform in both. -/
theorem jointAbsolute_norm_integral_eq_graph
    {I X F : Type*} [Fintype I] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) [SigmaFinite μ]
    (ρ : I → Measure ℝ) [∀ i, IsFiniteMeasure (ρ i)]
    (E : I → ℝ → ℝ) (a : I → ℝ) (q : I → X → LoopMomentum) (N : X → F)
    (hpos : ∀ i α, 0 < α → 0 ≤ E i α)
    (hj : Integrable (jointAbsolute E a q N)
      (μ.prod (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0)))))) :
    (∫ z, ‖jointAbsolute E a q N z‖
      ∂(μ.prod (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0)))))) =
      ∫ k, ‖(∏ i, schwingerLine (ρ i) (E i) (a i) (q i k)) • N k‖ ∂μ := by
  rw [integral_prod _ hj.norm]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  change (∫ t : I → ℝ × ℝ, ‖‖N k‖ * ∏ i,
    exp (-(t i).1 * ((a i) ^ 2 * ‖q i k‖ ^ 2)) *
      (E i (t i).2 * exp (-(t i).2 * ‖q i k‖ ^ 2))‖
      ∂Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0)))) = _
  have hi := joint_parameter_norm_integral
    (fun i => (ρ i).prod (volume.restrict (Ioi 0)))
    (fun i (t : ℝ × ℝ) => exp (-t.1 * ((a i) ^ 2 * ‖q i k‖ ^ 2)) *
      (E i t.2 * exp (-t.2 * ‖q i k‖ ^ 2))) ‖N k‖
  rw [hi]
  simp_rw [schwinger_laplace_parameter_norm_integral _ (hpos _)]
  rw [norm_smul, norm_norm, Real.norm_of_nonneg
    (Finset.prod_nonneg fun i _ => schwingerLine_nonneg (ρ i) (hpos i) (a i) (q i k))]
  simp only [schwingerLine]
  ring

/-- Source-format global theorem with a common positive representing measure
and a fixed positive damping scale. Fourier normalization is included in both
the graph and the joint absolute integral. The rectangular rank premise and
both source gap/endpoint alternatives are discharged in the preceding proof. -/
theorem global_uv
    {I P F : Type*} [Fintype I] {L : ℕ}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Croute : Matrix I (Fin L) ℝ) (hrank : Croute.rank = L)
    (R : P → I → LoopMomentum) {B C D a : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 < a)
    (hR : ∀ p, ‖R p‖ ≤ B)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hcontrol : GapOrEndpoint ρ D)
    (E : I → ℝ → ℝ) (α0 K : I → ℝ)
    (hmE : ∀ i, Measurable (E i)) (hE : ∀ i, IntegrableOn (E i) (Ioi 0))
    (hpos : ∀ i α, 0 < α → 0 ≤ E i α)
    (hα0 : ∀ i, 0 < α0 i) (hK : ∀ i, ∀ α ∈ Ioc 0 (α0 i), E i α ≤ K i)
    (N : P → (Fin L → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p,
      Integrable (fun k => (∏ i, schwingerLine ρ (E i) a
        (rectangularMomentum Croute R i p k)) • N p k)
        (Measure.pi fun _ : Fin L => volume) ∧
      (∫ k, ‖(∏ i, schwingerLine ρ (E i) a
        (rectangularMomentum Croute R i p k)) • N p k‖ / (2 * π) ^ (4 * L)
        ∂(Measure.pi fun _ : Fin L => volume)) ≤ A ∧
      Integrable (jointAbsolute E (fun _ => a)
        (fun i => rectangularMomentum Croute R i p) (N p))
        ((Measure.pi fun _ : Fin L => volume).prod
          (Measure.pi (fun _ : I => ρ.prod (volume.restrict (Ioi 0))))) ∧
      (∫ z, ‖jointAbsolute E (fun _ => a)
        (fun i => rectangularMomentum Croute R i p) (N p) z‖ / (2 * π) ^ (4 * L)
        ∂((Measure.pi fun _ : Fin L => volume).prod
          (Measure.pi (fun _ : I => ρ.prod (volume.restrict (Ioi 0)))))) ≤ A := by
  obtain ⟨A, hA, h⟩ := global_uv_rectangular Croute hrank R hB hC hD hR
    (fun _ : I => ρ) (fun _ => hneg) (fun _ => hcontrol) E (fun _ => a) α0 K
    hmE hE hpos hα0 hK (fun _ => ha) N hmN hN
  refine ⟨A / (2 * π) ^ (4 * L), div_nonneg hA (by positivity), ?_⟩
  intro p
  refine ⟨(h p).1, ?_, (h p).2.2, ?_⟩
  · rw [integral_div]
    exact div_le_div_of_nonneg_right (h p).2.1 (by positivity)
  · rw [integral_div, jointAbsolute_norm_integral_eq_graph _ (fun _ : I => ρ)
      E (fun _ => a) (fun i => rectangularMomentum Croute R i p) (N p) hpos (h p).2.2]
    exact div_le_div_of_nonneg_right (h p).2.1 (by positivity)

end UV
