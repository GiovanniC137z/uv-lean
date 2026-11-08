import UV.ContourExchange
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Sharp mixed Cauchy estimates by successive coordinate blocks. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators

namespace UV

theorem analytic_iteratedFDeriv_comp_linear_at
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : G →L[ℂ] E) {f : E → F} {x : G} (hf : AnalyticAt ℂ f (L x)) (n : ℕ) :
    iteratedFDeriv ℂ n (f ∘ L) x =
      (iteratedFDeriv ℂ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨r, hr, ha⟩ := hf.exists_ball_analyticOnNhd
  have hpre : IsOpen (L ⁻¹' ball (L x) r) := isOpen_ball.preimage L.continuous
  have hx : L x ∈ ball (L x) r := mem_ball_self hr
  have hc : ContDiffOn ℂ n f (ball (L x) r) := ha.contDiffOn_of_completeSpace
  have hw := L.iteratedFDerivWithin_comp_right hc isOpen_ball.uniqueDiffOn hpre.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
    ((hf.comp (L.analyticAt x)).contDiffAt) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ball.uniqueDiffOn
      hf.contDiffAt hx] at hw
  exact hw

/-- The derivative along an affine complex line is the actual repeated
directional Fréchet derivative, at every analytic base point. -/
theorem analytic_iteratedDeriv_affine_slice
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {f : H → ℂ} (b v : H) (c : ℂ) (hf : AnalyticAt ℂ f (b + c • v)) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => f (b + z • v)) c =
      (iteratedFDeriv ℂ n f (b + c • v)) (fun _ => v) := by
  let L : ℂ →L[ℂ] H := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hshift : AnalyticAt ℂ (fun y : H => f (b + y)) (L c) := by
    apply hf.comp_of_eq (analyticAt_const.add analyticAt_id)
    rfl
  have h := analytic_iteratedFDeriv_comp_linear_at L hshift n
  have he := congrArg (fun D => D (fun _ => (1 : ℂ))) h
  simpa only [iteratedDeriv_eq_iteratedFDeriv, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, L] using he

/-- Evaluation of an iterated Fréchet derivative at fixed directions is a
continuous complex linear operation. -/
def multilinearEvaluation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (n : ℕ) (v : Fin n → H) : (H [×n]→L[ℂ] ℂ) →L[ℂ] ℂ where
  toFun D := D v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const v

/-- The literal closed product of complex disks, with individual radii. -/
def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, dist (z j) (c j) ≤ r j}

theorem analyticAt_fin_cons_tail {n : ℕ} (c : ℂ) (u : Fin n → ℂ) :
    AnalyticAt ℂ (fun v : Fin n → ℂ => (Fin.cons c v : Fin (n + 1) → ℂ)) u := by
  apply AnalyticAt.pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin n → ℂ => c) u)
  · simpa only [Fin.cons_succ] using
      (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt u

theorem analyticAt_fin_cons_head {n : ℕ} (u : Fin n → ℂ) (c : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (Fin.cons z u : Fin (n + 1) → ℂ)) c := by
  apply AnalyticAt.pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) c)
  · simpa only [Fin.cons_succ] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => u i) c)

theorem continuous_fin_cons_pair (n : ℕ) :
    Continuous (fun p : ℂ × (Fin n → ℂ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact continuous_fst
  · exact (continuous_apply i).comp continuous_snd

/-- The remaining-coordinate domain where an entire first-coordinate closed
disk is inside the admitted complex domain. -/
def tailDiscDomain {n : ℕ} (Ω : Set (Fin (n + 1) → ℂ)) (c : ℂ) (r : ℝ) : Set (Fin n → ℂ) :=
  {u | ∀ z ∈ closedBall c r, Fin.cons z u ∈ Ω}

theorem isOpen_tailDiscDomain {n : ℕ} {Ω : Set (Fin (n + 1) → ℂ)}
    (hΩ : IsOpen Ω) (c : ℂ) (r : ℝ) : IsOpen (tailDiscDomain Ω c r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro u hu
  have hcont : Continuous (fun p : (Fin n → ℂ) × ℂ =>
      (Fin.cons p.2 p.1 : Fin (n + 1) → ℂ)) :=
    (continuous_fin_cons_pair n).comp continuous_swap
  exact (isCompact_closedBall c r).eventually_forall_of_forall_eventually
    (fun z hz => (hΩ.preimage hcont).mem_nhds (hu z hz))

/-- Holomorphy of an actual coordinate-derivative block from a Cauchy
integral. This only assumes joint complex differentiability of `f`; no
multivariable power-series conclusion is inserted as a premise. -/
theorem scalar_headPartial_differentiableOn {n : ℕ} {Ω : Set (Fin (n + 1) → ℂ)}
    (hΩ : IsOpen Ω) {f : (Fin (n + 1) → ℂ) → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (m : ℕ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ (fun u : Fin n → ℂ => iteratedDeriv m (fun z => f (Fin.cons z u)) c)
      (tailDiscDomain Ω c r) := by
  let ν := volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))
  let W : ℝ → ℂ := fun t => deriv (circleMap c r) t *
    ((circleMap c r t - c)⁻¹ ^ m * (circleMap c r t - c)⁻¹)
  let G : (Fin n → ℂ) → ℝ → ℂ := fun u t => W t * f (Fin.cons (circleMap c r t) u)
  have hU := isOpen_tailDiscDomain hΩ c r
  have hγ : ∀ t, circleMap c r t ∈ closedBall c r :=
    fun t => sphere_subset_closedBall (circleMap_mem_sphere c hr.le t)
  have hne : ∀ t : ℝ, circleMap c r t - c ≠ 0 := by
    intro t
    have hdist : dist (circleMap c r t) c = r := circleMap_mem_sphere c hr.le t
    exact sub_ne_zero.mpr (dist_pos.mp (by simpa only [hdist] using hr))
  have hW : Continuous W := by
    have hd : Continuous (fun t : ℝ => deriv (circleMap c r) t) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    have hk := ((continuous_circleMap c r).sub continuous_const).inv₀ hne
    exact hd.mul ((hk.pow m).mul hk)
  have hiW : Integrable W ν :=
    (show IntervalIntegrable W volume 0 (2 * Real.pi) from hW.intervalIntegrable _ _).def'
  have hmG : ∀ u ∈ tailDiscDomain Ω c r, AEStronglyMeasurable (G u) ν := by
    intro u hu
    have hcurve : Continuous (fun t : ℝ => (Fin.cons (circleMap c r t) u : Fin (n + 1) → ℂ)) :=
      (continuous_fin_cons_pair n).comp ((continuous_circleMap c r).prodMk continuous_const)
    exact (hW.mul (hf.continuousOn.comp_continuous hcurve (fun t => hu _ (hγ t)))).aestronglyMeasurable
  have hdG : ∀ᵐ t ∂ν, DifferentiableOn ℂ (fun u => G u t) (tailDiscDomain Ω c r) := by
    apply Eventually.of_forall
    intro t u hu
    have hpoint := hu _ (hγ t)
    have ht := (hf.differentiableAt (hΩ.mem_nhds hpoint)).comp u
      (analyticAt_fin_cons_tail (circleMap c r t) u).differentiableAt
    exact ((differentiableAt_const (W t)).mul ht).differentiableWithinAt
  have hbG : ∀ u ∈ tailDiscDomain Ω c r, ∃ ε > 0,
      ball u ε ⊆ tailDiscDomain Ω c r ∧ ∃ M : ℝ → ℝ,
        Integrable M ν ∧ ∀ᵐ t ∂ν, ∀ v ∈ ball u ε, ‖G v t‖ ≤ M t := by
    intro u hu
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU u hu
    have hclosed : closedBall u (δ / 2) ⊆ tailDiscDomain Ω c r :=
      (closedBall_subset_ball (by linarith)).trans hδU
    let S : Set (Fin (n + 1) → ℂ) :=
      (fun p : ℂ × (Fin n → ℂ) => Fin.cons p.1 p.2) ''
        (closedBall c r ×ˢ closedBall u (δ / 2))
    have hScompact : IsCompact S :=
      ((isCompact_closedBall c r).prod (isCompact_closedBall u (δ / 2))).image (continuous_fin_cons_pair n)
    have hSΩ : S ⊆ Ω := by
      rintro _ ⟨⟨z, v⟩, ⟨hz, hv⟩, rfl⟩
      exact hclosed hv z hz
    obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn (hf.continuousOn.mono hSΩ)
    refine ⟨δ / 2, by linarith, ball_subset_closedBall.trans hclosed,
      (fun t => ‖W t‖ * C), hiW.norm.mul_const C, Eventually.of_forall ?_⟩
    intro t v hv
    change ‖W t * f (Fin.cons (circleMap c r t) v)‖ ≤ ‖W t‖ * C
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply hC (Fin.cons (circleMap c r t) v)
    exact ⟨(circleMap c r t, v), ⟨hγ t, ball_subset_closedBall hv⟩, rfl⟩
  have hg := holomorphy_from_local_graph_majorants hU hmG hdG hbG
  have hnormalized := (differentiableOn_const ((m.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹)).mul hg
  apply hnormalized.congr
  intro u hu
  have hslice : DifferentiableOn ℂ (fun z => f (Fin.cons z u)) (closedBall c r) := by
    intro z hz
    exact ((hf.differentiableAt (hΩ.mem_nhds (hu z hz))).comp z
      (analyticAt_fin_cons_head u z).differentiableAt).differentiableWithinAt
  have hformula := one_variable_cauchy_derivative_formula hr hslice m
  simpa only [circleIntegral, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ν, G, W, uIoc_of_le Real.two_pi_pos.le, Pi.mul_apply, mul_assoc] using hformula

/-- A block of partial derivatives in the first coordinate, evaluated at
its center, while the remaining coordinates stay free. -/
def headPartial {n : ℕ} (m : ℕ) (f : (Fin (n + 1) → ℂ) → ℂ) (c : ℂ)
    (u : Fin n → ℂ) : ℂ :=
  (iteratedFDeriv ℂ m f (Fin.cons c u)) (fun _ => Fin.cons 1 (fun _ => 0))

/-- The block definition is the actual iterated scalar coordinate derivative,
not a Cauchy integral postulated to equal that derivative. -/
theorem headPartial_eq_iteratedDeriv {n : ℕ} (m : ℕ) {f : (Fin (n + 1) → ℂ) → ℂ}
    (c : ℂ) (u : Fin n → ℂ) (hf : AnalyticAt ℂ f (Fin.cons c u)) :
    headPartial m f c u = iteratedDeriv m (fun z => f (Fin.cons z u)) c := by
  let b : Fin (n + 1) → ℂ := Fin.cons 0 u
  let v : Fin (n + 1) → ℂ := Fin.cons 1 (fun _ => 0)
  have he : ∀ z : ℂ, b + z • v = Fin.cons z u := by
    intro z
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [b, v]
  have hs := analytic_iteratedDeriv_affine_slice b v c (by simpa only [he] using hf) m
  simp_rw [he] at hs
  exact hs.symm

/-- Coordinate-block derivatives remain jointly holomorphic in every
remaining coordinate, by analyticity of the actual Fréchet derivative. -/
theorem headPartial_analyticAt {n : ℕ} (m : ℕ) {f : (Fin (n + 1) → ℂ) → ℂ}
    (c : ℂ) (u : Fin n → ℂ) (hf : AnalyticAt ℂ f (Fin.cons c u)) :
    AnalyticAt ℂ (headPartial m f c) u := by
  let ev := multilinearEvaluation m
    (fun _ : Fin m => (Fin.cons 1 (fun _ : Fin n => (0 : ℂ)) : Fin (n + 1) → ℂ))
  have hd : AnalyticAt ℂ (iteratedFDeriv ℂ m f) (Fin.cons c u) := by
    obtain ⟨r, hr, ha⟩ := hf.exists_ball_analyticOnNhd
    exact (ha.iteratedFDeriv m) _ (mem_ball_self hr)
  exact ((ev.analyticAt _).comp hd).comp (analyticAt_fin_cons_tail c u)

theorem closedPolydisc_cons_iff {n : ℕ} (c : Fin (n + 1) → ℂ) (r : Fin (n + 1) → ℝ)
    (z : ℂ) (u : Fin n → ℂ) :
    Fin.cons z u ∈ closedPolydisc c r ↔
      dist z (c 0) ≤ r 0 ∧ u ∈ closedPolydisc (Fin.tail c) (Fin.tail r) := by
  constructor
  · intro h
    exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨hz, hu⟩ j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hz
    · exact hu i

/-- A first-coordinate derivative block costs precisely its own factorial
and its own radius power, uniformly on all remaining closed disks. -/
theorem headPartial_cauchy_budget {n : ℕ} (m : ℕ)
    {f : (Fin (n + 1) → ℂ) → ℂ} {c : Fin (n + 1) → ℂ} {r : Fin (n + 1) → ℝ} {C : ℝ}
    (hr : ∀ j, 0 < r j) (hf : AnalyticOnNhd ℂ f (closedPolydisc c r))
    (hb : ∀ z ∈ closedPolydisc c r, ‖f z‖ ≤ C)
    {u : Fin n → ℂ} (hu : u ∈ closedPolydisc (Fin.tail c) (Fin.tail r)) :
    ‖headPartial m f (c 0) u‖ ≤ (m.factorial : ℝ) * (r 0)⁻¹ ^ m * C := by
  have hc : Fin.cons (c 0) u ∈ closedPolydisc c r :=
    (closedPolydisc_cons_iff c r _ _).mpr ⟨by simpa only [dist_self] using (hr 0).le, hu⟩
  rw [headPartial_eq_iteratedDeriv m (c 0) u (hf _ hc)]
  have hslice : DifferentiableOn ℂ (fun z => f (Fin.cons z u)) (closedBall (c 0) (r 0)) := by
    intro z hz
    have hz' := (closedPolydisc_cons_iff c r z u).mpr ⟨hz, hu⟩
    exact ((hf _ hz').differentiableAt.comp z
      (analyticAt_fin_cons_head u z).differentiableAt).differentiableWithinAt
  apply one_variable_cauchy_derivative_budget (hr 0) hslice
  intro z hz
  exact hb _ ((closedPolydisc_cons_iff c r z u).mpr ⟨sphere_subset_closedBall hz, hu⟩)

theorem headPartial_analyticOnNhd {n : ℕ} (m : ℕ)
    {f : (Fin (n + 1) → ℂ) → ℂ} {c : Fin (n + 1) → ℂ} {r : Fin (n + 1) → ℝ}
    (hr : ∀ j, 0 < r j) (hf : AnalyticOnNhd ℂ f (closedPolydisc c r)) :
    AnalyticOnNhd ℂ (headPartial m f (c 0)) (closedPolydisc (Fin.tail c) (Fin.tail r)) := by
  intro u hu
  apply headPartial_analyticAt
  apply hf
  exact (closedPolydisc_cons_iff c r _ _).mpr
    ⟨by simpa only [dist_self] using (hr 0).le, hu⟩

/-- The actual ordered mixed derivative: first take `α 0` derivatives in
coordinate zero at its center, and then apply the same construction to the
remaining coordinates. `headPartial_eq_iteratedDeriv` identifies each block
with ordinary repeated complex coordinate differentiation. -/
def mixedPartial : {n : ℕ} → (Fin n → ℕ) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ
  | 0, _, f, c => f c
  | _n + 1, α, f, c =>
      mixedPartial (Fin.tail α) (headPartial (α 0) f (c 0)) (Fin.tail c)

/-- Ordinary scalar coordinate differentiation, in the explicit coordinate
order zero, one, and so on, with each multiplicity given by the multi-index. -/
def orderedMixedDeriv : {n : ℕ} → (Fin n → ℕ) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ
  | 0, _, f, c => f c
  | _n + 1, α, f, c => orderedMixedDeriv (Fin.tail α)
      (fun u => iteratedDeriv (α 0) (fun z => f (Fin.cons z u)) (c 0)) (Fin.tail c)

theorem orderedMixedDeriv_congr {n : ℕ} (α : Fin n → ℕ)
    {f g : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} (heq : f =ᶠ[𝓝 c] g) :
    orderedMixedDeriv α f c = orderedMixedDeriv α g c := by
  induction n with
  | zero => exact heq.self_of_nhds
  | succ n IH =>
    apply IH
    have hemb : Tendsto (fun u : Fin n → ℂ => (Fin.cons (c 0) u : Fin (n + 1) → ℂ))
        (𝓝 (Fin.tail c)) (𝓝 c) := by
      simpa only [Fin.cons_self_tail] using
        (analyticAt_fin_cons_tail (c 0) (Fin.tail c)).continuousAt.tendsto
    filter_upwards [hemb.eventually heq.eventuallyEq_nhds] with u hu
    have hslice := hu.comp_tendsto (analyticAt_fin_cons_head u (c 0)).continuousAt.tendsto
    exact Filter.EventuallyEq.iteratedDeriv_eq (α 0) hslice

/-- The Fréchet-block definition is exactly the ordinary iterated scalar
mixed partial in the stated coordinate order. -/
theorem mixedPartial_eq_orderedMixedDeriv {n : ℕ} (α : Fin n → ℕ)
    {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} (hf : AnalyticAt ℂ f c) :
    mixedPartial α f c = orderedMixedDeriv α f c := by
  induction n with
  | zero => rfl
  | succ n IH =>
    have hcons : AnalyticAt ℂ f (Fin.cons (c 0) (Fin.tail c)) := by
      simpa only [Fin.cons_self_tail] using hf
    have hhead := headPartial_analyticAt (α 0) (c 0) (Fin.tail c) hcons
    change mixedPartial (Fin.tail α) (headPartial (α 0) f (c 0)) (Fin.tail c) = _
    rw [IH (Fin.tail α) hhead]
    apply orderedMixedDeriv_congr
    have hemb : Tendsto (fun u : Fin n → ℂ => (Fin.cons (c 0) u : Fin (n + 1) → ℂ))
        (𝓝 (Fin.tail c)) (𝓝 c) := by
      simpa only [Fin.cons_self_tail] using
        (analyticAt_fin_cons_tail (c 0) (Fin.tail c)).continuousAt.tendsto
    filter_upwards [hemb.eventually hf.eventually_analyticAt] with u hu
    exact headPartial_eq_iteratedDeriv (α 0) (c 0) u hu

/-- Sharp multivariable Cauchy estimate. The factor is `α!`, the product of
the coordinate factorials, rather than the factorial of total order. -/
theorem mixed_cauchy_derivative_budget {n : ℕ} (α : Fin n → ℕ)
    {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : Fin n → ℝ} {C : ℝ}
    (hr : ∀ j, 0 < r j) (hf : AnalyticOnNhd ℂ f (closedPolydisc c r))
    (hb : ∀ z ∈ closedPolydisc c r, ‖f z‖ ≤ C) :
    ‖mixedPartial α f c‖ ≤
      (∏ j, (α j).factorial : ℝ) * (∏ j, (r j)⁻¹ ^ (α j)) * C := by
  induction n generalizing C with
  | zero =>
    have hc : c ∈ closedPolydisc c r := fun j => Fin.elim0 j
    simpa only [mixedPartial, Fin.prod_univ_zero, mul_one, one_mul] using hb c hc
  | succ n IH =>
    have htail : ∀ j, 0 < Fin.tail r j := fun j => hr j.succ
    have hhead := headPartial_analyticOnNhd (α 0) hr hf
    have hbhead : ∀ u ∈ closedPolydisc (Fin.tail c) (Fin.tail r),
        ‖headPartial (α 0) f (c 0) u‖ ≤ ((α 0).factorial : ℝ) * (r 0)⁻¹ ^ (α 0) * C :=
      fun _ hu => headPartial_cauchy_budget (α 0) hr hf hb hu
    have h := IH (Fin.tail α) htail hhead hbhead
    change ‖mixedPartial (Fin.tail α) (headPartial (α 0) f (c 0)) (Fin.tail c)‖ ≤ _
    calc
      _ ≤ _ := h
      _ = _ := by simp only [Fin.prod_univ_succ, Fin.tail]; ring

/-- The sharp estimate stated entirely with actual repeated scalar partial
derivatives, with no assumed Cauchy representation or derivative bound. -/
theorem ordered_mixed_cauchy_budget {n : ℕ} (α : Fin n → ℕ)
    {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : Fin n → ℝ} {C : ℝ}
    (hr : ∀ j, 0 < r j) (hf : AnalyticOnNhd ℂ f (closedPolydisc c r))
    (hb : ∀ z ∈ closedPolydisc c r, ‖f z‖ ≤ C) :
    ‖orderedMixedDeriv α f c‖ ≤
      (∏ j, (α j).factorial : ℝ) * (∏ j, (r j)⁻¹ ^ (α j)) * C := by
  have hc : c ∈ closedPolydisc c r := fun j => by simpa only [dist_self] using (hr j).le
  rw [← mixedPartial_eq_orderedMixedDeriv α (hf c hc)]
  exact mixed_cauchy_derivative_budget α hr hf hb

/-- The sharp mixed derivative estimate directly from joint complex
differentiability. Analyticity of every successive coordinate block is
derived by actual Cauchy integration, so no analytic power-series premise
on the integrated function is required. -/
theorem ordered_mixed_cauchy_budget_of_differentiable {n : ℕ} (α : Fin n → ℕ)
    {f : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) {c : Fin n → ℂ} {r : Fin n → ℝ} {C : ℝ}
    (hr : ∀ j, 0 < r j) (hclosed : closedPolydisc c r ⊆ Ω)
    (hb : ∀ z ∈ closedPolydisc c r, ‖f z‖ ≤ C) :
    ‖orderedMixedDeriv α f c‖ ≤
      (∏ j, (α j).factorial : ℝ) * (∏ j, (r j)⁻¹ ^ (α j)) * C := by
  induction n generalizing C with
  | zero =>
    have hc : c ∈ closedPolydisc c r := fun j => Fin.elim0 j
    simpa only [orderedMixedDeriv, Fin.prod_univ_zero, mul_one, one_mul] using hb c hc
  | succ n IH =>
    have hU := isOpen_tailDiscDomain hΩ (c 0) (r 0)
    have hg := scalar_headPartial_differentiableOn hΩ hf (α 0) (c 0) (hr 0)
    have htail : closedPolydisc (Fin.tail c) (Fin.tail r) ⊆ tailDiscDomain Ω (c 0) (r 0) := by
      intro u hu z hz
      exact hclosed ((closedPolydisc_cons_iff c r z u).mpr ⟨hz, hu⟩)
    have hbhead : ∀ u ∈ closedPolydisc (Fin.tail c) (Fin.tail r),
        ‖iteratedDeriv (α 0) (fun z => f (Fin.cons z u)) (c 0)‖ ≤
          ((α 0).factorial : ℝ) * (r 0)⁻¹ ^ (α 0) * C := by
      intro u hu
      have hs : DifferentiableOn ℂ (fun z => f (Fin.cons z u)) (closedBall (c 0) (r 0)) := by
        intro z hz
        have hzΩ := hclosed ((closedPolydisc_cons_iff c r z u).mpr ⟨hz, hu⟩)
        exact ((hf.differentiableAt (hΩ.mem_nhds hzΩ)).comp z
          (analyticAt_fin_cons_head u z).differentiableAt).differentiableWithinAt
      apply one_variable_cauchy_derivative_budget (hr 0) hs
      intro z hz
      exact hb _ ((closedPolydisc_cons_iff c r z u).mpr ⟨sphere_subset_closedBall hz, hu⟩)
    have h := IH (Fin.tail α) hU hg (fun j => hr j.succ) htail hbhead
    change ‖orderedMixedDeriv (Fin.tail α)
      (fun u => iteratedDeriv (α 0) (fun z => f (Fin.cons z u)) (c 0)) (Fin.tail c)‖ ≤ _
    calc
      _ ≤ _ := h
      _ = _ := by simp only [Fin.prod_univ_succ, Fin.tail]; ring

/-- Source cor:complex-derivative-budget for the actual integrated graph.
The derivative is the ordinary ordered scalar mixed partial, and its exact
factorial/radius constant follows from the complete complex majorant. -/
theorem graph_mixed_cauchy_budget
    {n : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : (Fin n → ℂ) → X → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hclosed : closedPolydisc c r ⊆ Ω) {M : X → ℝ} (hM : Integrable M μ)
    (hbound : ∀ᵐ ξ ∂μ, ∀ z ∈ closedPolydisc c r, ‖F z ξ‖ ≤ M ξ)
    (α : Fin n → ℕ) :
    ‖orderedMixedDeriv α (fun z => ∫ ξ, F z ξ ∂μ) c‖ ≤
      (∏ j, (α j).factorial : ℝ) * (∏ j, (r j)⁻¹ ^ (α j)) * ∫ ξ, M ξ ∂μ := by
  apply ordered_mixed_cauchy_budget_of_differentiable α hΩ
    (holomorphy_from_compact_graph_majorants hΩ hm hd hb) hr hclosed
  intro z hz
  apply MeasureTheory.norm_integral_le_of_norm_le hM
  filter_upwards [hbound] with ξ hξ
  exact hξ z hz

/-- Actual scalar coordinate-block differentiation commutes with the
representation integral, on every fiber containing the whole head disk. -/
theorem graph_scalar_headPartial_commutes
    {n : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : (Fin (n + 1) → ℂ) → X → ℂ} {Ω : Set (Fin (n + 1) → ℂ)} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set (Fin (n + 1) → ℂ), IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    (m : ℕ) (c : ℂ) {r : ℝ} (hr : 0 < r) {u : Fin n → ℂ}
    (hu : u ∈ tailDiscDomain Ω c r) :
    Integrable (fun ξ => iteratedDeriv m (fun z => F (Fin.cons z u) ξ) c) μ ∧
      iteratedDeriv m (fun z => ∫ ξ, F (Fin.cons z u) ξ ∂μ) c =
        ∫ ξ, iteratedDeriv m (fun z => F (Fin.cons z u) ξ) c ∂μ := by
  let e : ℂ → (Fin (n + 1) → ℂ) := fun z => Fin.cons z u
  have he : Continuous e := (continuous_fin_cons_pair n).comp (continuous_id.prodMk continuous_const)
  let U := e ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage he
  have hdS : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F (e z) ξ) U := by
    filter_upwards [hd] with ξ hξ
    intro z hz
    exact ((hξ.differentiableAt (hΩ.mem_nhds hz)).comp z
      (analyticAt_fin_cons_head u z).differentiableAt).differentiableWithinAt
  have hbS : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F (e z) ξ‖ ≤ M ξ := by
    intro K hK hKU
    have himage : e '' K ⊆ Ω := by
      rintro _ ⟨z, hz, rfl⟩
      exact hKU hz
    obtain ⟨M, hM, hbM⟩ := hb (e '' K) (hK.image he) himage
    refine ⟨M, hM, ?_⟩
    filter_upwards [hbM] with ξ hξ
    exact fun z hz => hξ _ ⟨z, hz, rfl⟩
  have hclosed : closedBall c r ⊆ U := hu
  obtain ⟨M, hM, hbM⟩ := hbS (closedBall c r) (isCompact_closedBall c r) hclosed
  exact graph_iteratedDeriv_commutes_of_ae_samples μ hU
    (fun z hz => hm _ hz) hdS hbS hr hclosed hM hbM m

/-- All finite ordered mixed coordinate derivatives commute with the graph
representation integral. Both measurability and integrable common bounds for
the successive derivative families are derived in the induction. -/
theorem graph_orderedMixedDeriv_commutes
    {n : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : (Fin n → ℂ) → X → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hclosed : closedPolydisc c r ⊆ Ω) (α : Fin n → ℕ) :
    Integrable (fun ξ => orderedMixedDeriv α (fun z => F z ξ) c) μ ∧
      orderedMixedDeriv α (fun z => ∫ ξ, F z ξ ∂μ) c =
        ∫ ξ, orderedMixedDeriv α (fun z => F z ξ) c ∂μ := by
  induction n with
  | zero =>
    have hc : c ∈ closedPolydisc c r := fun j => Fin.elim0 j
    have hcΩ := hclosed hc
    obtain ⟨M, hM, hbM⟩ := hb {c} isCompact_singleton (singleton_subset_iff.mpr hcΩ)
    have hi : Integrable (F c) μ := by
      apply hM.mono' (hm c hcΩ)
      filter_upwards [hbM] with ξ hξ
      exact hξ c (mem_singleton c)
    exact ⟨hi, rfl⟩
  | succ n IH =>
    let U := tailDiscDomain Ω (c 0) (r 0)
    have hU : IsOpen U := isOpen_tailDiscDomain hΩ (c 0) (r 0)
    let Q : (Fin n → ℂ) → X → ℂ := fun u ξ =>
      iteratedDeriv (α 0) (fun z => F (Fin.cons z u) ξ) (c 0)
    have hmQ : ∀ u ∈ U, AEStronglyMeasurable (Q u) μ := fun u hu =>
      (graph_scalar_headPartial_commutes μ hΩ hm hd hb (α 0) (c 0) (hr 0) hu).1.aestronglyMeasurable
    have hdQ : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun u => Q u ξ) U := by
      filter_upwards [hd] with ξ hξ
      exact scalar_headPartial_differentiableOn hΩ hξ (α 0) (c 0) (hr 0)
    have hbQ : ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ U → ∃ M : X → ℝ,
        Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ u ∈ K, ‖Q u ξ‖ ≤ M ξ := by
      intro K hK hKU
      let S : Set (Fin (n + 1) → ℂ) :=
        (fun p : ℂ × (Fin n → ℂ) => Fin.cons p.1 p.2) '' (closedBall (c 0) (r 0) ×ˢ K)
      have hScompact : IsCompact S :=
        ((isCompact_closedBall (c 0) (r 0)).prod hK).image (continuous_fin_cons_pair n)
      have hSΩ : S ⊆ Ω := by
        rintro _ ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
        exact hKU hu z hz
      obtain ⟨M, hM, hbM⟩ := hb S hScompact hSΩ
      let C : ℝ := ((α 0).factorial : ℝ) * (r 0)⁻¹ ^ (α 0)
      refine ⟨(fun ξ => C * M ξ), hM.const_mul C, ?_⟩
      filter_upwards [hd, hbM] with ξ hξ hξbound
      intro u hu
      have hs : DifferentiableOn ℂ (fun z => F (Fin.cons z u) ξ) (closedBall (c 0) (r 0)) := by
        intro z hz
        exact ((hξ.differentiableAt (hΩ.mem_nhds (hKU hu z hz))).comp z
          (analyticAt_fin_cons_head u z).differentiableAt).differentiableWithinAt
      apply one_variable_cauchy_derivative_budget (hr 0) hs
      intro z hz
      exact hξbound _ ⟨(z, u), ⟨sphere_subset_closedBall hz, hu⟩, rfl⟩
    have htail : closedPolydisc (Fin.tail c) (Fin.tail r) ⊆ U := by
      intro u hu z hz
      exact hclosed ((closedPolydisc_cons_iff c r z u).mpr ⟨hz, hu⟩)
    have hi := IH hU hmQ hdQ hbQ (fun j => hr j.succ) htail (Fin.tail α)
    refine ⟨hi.1, ?_⟩
    have hcTail : Fin.tail c ∈ U := htail (fun j => by simpa only [dist_self] using (hr j.succ).le)
    have heq : (fun u => iteratedDeriv (α 0) (fun z => ∫ ξ, F (Fin.cons z u) ξ ∂μ) (c 0))
        =ᶠ[𝓝 (Fin.tail c)] (fun u => ∫ ξ, Q u ξ ∂μ) := by
      filter_upwards [hU.mem_nhds hcTail] with u hu
      exact (graph_scalar_headPartial_commutes μ hΩ hm hd hb (α 0) (c 0) (hr 0) hu).2
    exact (orderedMixedDeriv_congr (Fin.tail α) heq).trans hi.2

/-- The local derivative exchange holds at every admitted point: a small
positive closed polydisc is constructed from openness of the domain. -/
theorem graph_orderedMixedDeriv_commutes_at
    {n : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : (Fin n → ℂ) → X → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : Fin n → ℂ} (hc : c ∈ Ω) (α : Fin n → ℕ) :
    Integrable (fun ξ => orderedMixedDeriv α (fun z => F z ξ) c) μ ∧
      orderedMixedDeriv α (fun z => ∫ ξ, F z ξ ∂μ) c =
        ∫ ξ, orderedMixedDeriv α (fun z => F z ξ) c ∂μ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ c hc
  have hpoly : closedPolydisc c (fun _ => ε / 2) ⊆ Ω := by
    intro z hz
    apply hball
    have hdist : dist z c ≤ ε / 2 := (dist_pi_le_iff (by linarith)).mpr hz
    exact lt_of_le_of_lt hdist (by linarith)
  exact graph_orderedMixedDeriv_commutes μ hΩ hm hd hb (fun _ => by linarith) hpoly α

/-- The main joint-holomorphy and all finite coordinate-derivative exchange
conclusions of thm:holomorphy, on its actual finite complex momentum domain. -/
theorem holomorphy_and_all_order_graph_derivatives
    {n : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : (Fin n → ℂ) → X → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ) :
    DifferentiableOn ℂ (fun z => ∫ ξ, F z ξ ∂μ) Ω ∧
      ∀ c ∈ Ω, ∀ α : Fin n → ℕ,
        Integrable (fun ξ => orderedMixedDeriv α (fun z => F z ξ) c) μ ∧
          orderedMixedDeriv α (fun z => ∫ ξ, F z ξ ∂μ) c =
            ∫ ξ, orderedMixedDeriv α (fun z => F z ξ) c ∂μ := by
  refine ⟨holomorphy_from_compact_graph_majorants hΩ hm hd hb, ?_⟩
  intro c hc α
  exact graph_orderedMixedDeriv_commutes_at μ hΩ hm hd hb hc α

end UV
