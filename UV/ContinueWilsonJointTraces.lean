import UV.ContinueWilsonHopSum
import Mathlib.MeasureTheory.Integral.Pi

/-! Fubini bounds for simultaneous closed charged circulations with
shared photon transfers and straight-link parameters. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {ι Z V : Type*} [Fintype ι] [MeasurableSpace Z] [Fintype V]

local instance : MeasurableSpace DiracMatrix := borel _
local instance : BorelSpace DiracMatrix := ⟨rfl⟩

theorem wilson_spin_hop_measurable (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) : Measurable (wilsonSpinHopMatrix L T us) := by
  have hw : Continuous (fun t : OSFourSpace × OSFourSpace => thinPlaneWave t.1 t.2) := by unfold thinPlaneWave; fun_prop
  have h := (hw.mul ((wilson_direction_weight_continuous us).comp continuous_snd)).smul
    ((wilson_spin_weight_continuous L).comp continuous_snd)
  exact (h.stronglyMeasurable.integral_prod_right' (ν := wilsonDisplacementMeasure L T)).measurable

theorem wilson_word_measurable {J : Type*} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (marks : J → WilsonDirections) {shift : J → Z → OSFourSpace} (hs : ∀ j, Measurable (shift j))
    {p : Z → OSFourSpace} (hp : Measurable p) (xs : List J) :
    Measurable (fun z => wilsonCirculationWord L T (xs.map (fun j => ⟨marks j,shift j z⟩)) (p z)) := by
  induction xs with
  | nil => exact measurable_const
  | cons j xs ih => exact ((wilson_spin_hop_measurable L T (marks j)).comp (hp.add (hs j))).mul ih

def wilsonAllocatedTrace {a n : ℕ} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace) (p : OSFourSpace) : ℂ :=
  (wilsonCirculationWord L T (wilsonAssignedHop u f q 0 :: wilsonAssignedTail u f q) p).trace

theorem wilson_allocated_word_measurable {a n : ℕ} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) {q : Z → Fin (n+1) → OSFourSpace}
    (hq : ∀ j, Measurable (q · j)) {p : Z → OSFourSpace} (hp : Measurable p) :
    Measurable (fun z => wilsonCirculationWord L T (wilsonAssignedHop u f (q z) 0 :: wilsonAssignedTail u f (q z)) (p z)) := by
  let marks := fun j => (wilsonAssignedHop u f (fun _ => 0) j).marks
  have hm := wilson_word_measurable L T marks (shift := fun j z => q z j) hq hp
    ((0 : Fin (n+1)) :: List.ofFn (fun i : Fin n => i.succ))
  simpa only [wilsonAssignedTail,List.map_cons,List.map_ofFn,Function.comp_def,wilsonAssignedHop,marks] using hm

theorem wilson_allocated_trace_measurable {a n : ℕ} (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) {q : Z → Fin (n+1) → OSFourSpace}
    (hq : ∀ j, Measurable (q · j)) {p : Z → OSFourSpace} (hp : Measurable p) :
    Measurable (fun z => wilsonAllocatedTrace L T u f (q z) (p z)) := by
  exact (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp
    (wilson_allocated_word_measurable L T u f hq hp)

variable {X : V → Type*}

def wilsonJointFactors (w : Z → ℂ) (F : (v : V) → Z → X v → ℂ) (z : Z × ((v : V) → X v)) : ℂ :=
  w z.1 * ∏ v, F v z.1 (z.2 v)

theorem wilson_factors_measurable [∀ v, MeasurableSpace (X v)] {w : Z → ℂ} (hmw : Measurable w) {F : (v : V) → Z → X v → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × X v => F v t.1 t.2)) : Measurable (wilsonJointFactors w F) :=
  (hmw.comp measurable_fst).mul (Finset.measurable_prod _ (fun v _ => (hm v).comp
    (measurable_fst.prodMk ((measurable_pi_apply v).comp measurable_snd))))

/-- The shared outer variables may shift all components. Each component
can have its own finite-dimensional integration space. -/
theorem wilson_joint_factors_measure [∀ v, MeasurableSpace (X v)] (νv : (v : V) → Measure (X v)) [∀ v, SigmaFinite (νv v)] (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w)
    (hw : Integrable w μ) {F : (v : V) → Z → X v → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × X v => F v t.1 t.2)) (hi : ∀ v z, Integrable (F v z) (νv v))
    (M : V → ℝ) (hM : ∀ v z, (∫ p, ‖F v z p‖ ∂νv v) ≤ M v) :
    let ν := Measure.pi νv
    Integrable (wilsonJointFactors w F) (μ.prod ν) ∧
      (∫ t, ‖wilsonJointFactors w F t‖ ∂μ.prod ν) ≤ (∫ z, ‖w z‖ ∂μ) * ∏ v, M v := by
  let ν := Measure.pi νv
  have hJoint := wilson_factors_measurable hmw hm
  have heq (z : Z) : (∫ p, ‖wilsonJointFactors w F (z,p)‖ ∂ν) = ‖w z‖ * ∏ v, ∫ q, ‖F v z q‖ ∂νv v := by
    simp only [wilsonJointFactors,norm_mul,norm_prod,integral_const_mul]
    rw [integral_fintype_prod_eq_prod (fun v p => ‖F v z p‖)]
  have hle (z : Z) : (∫ p, ‖wilsonJointFactors w F (z,p)‖ ∂ν) ≤ ‖w z‖ * ∏ v, M v := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun v _ => hM v z)) (norm_nonneg _)
  have hout := hw.norm.mul_const (∏ v, M v)
  have hInt : Integrable (wilsonJointFactors w F) (μ.prod ν) := by
    apply (integrable_prod_iff hJoint.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun z => (Integrable.fintype_prod_dep (fun v => hi v z)).const_mul (w z)),?_⟩
    apply hout.mono' hJoint.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle z
  refine ⟨hInt,?_⟩
  rw [integral_prod _ hInt.norm,←integral_mul_const]
  exact integral_mono hInt.integral_norm_prod_left hout hle

theorem wilson_joint_factors_bound [∀ v, MeasureSpace (X v)] [∀ v, SigmaFinite (volume : Measure (X v))] (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w)
    (hw : Integrable w μ) {F : (v : V) → Z → X v → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × X v => F v t.1 t.2)) (hi : ∀ v z, Integrable (F v z))
    (M : V → ℝ) (hM : ∀ v z, (∫ p, ‖F v z p‖) ≤ M v) :
    let ν := Measure.pi (fun v : V => (volume : Measure (X v)))
    Integrable (wilsonJointFactors w F) (μ.prod ν) ∧
      (∫ t, ‖wilsonJointFactors w F t‖ ∂μ.prod ν) ≤ (∫ z, ‖w z‖ ∂μ) * ∏ v, M v :=
  wilson_joint_factors_measure (fun v => (volume : Measure (X v))) μ hmw hw hm hi M hM

def wilsonJointTraces (w : Z → ℂ) (F : V → Z → OSFourSpace → ℂ) : Z × (V → OSFourSpace) → ℂ :=
  wilsonJointFactors w F

theorem wilson_joint_measurable {w : Z → ℂ} (hmw : Measurable w) {F : V → Z → OSFourSpace → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × OSFourSpace => F v t.1 t.2)) : Measurable (wilsonJointTraces w F) :=
  wilson_factors_measurable hmw hm

theorem wilson_joint_traces_bound (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w)
    (hw : Integrable w μ) {F : V → Z → OSFourSpace → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × OSFourSpace => F v t.1 t.2)) (hi : ∀ v z, Integrable (F v z))
    (M : V → ℝ) (hM : ∀ v z, (∫ p, ‖F v z p‖) ≤ M v) :
    let ν := Measure.pi (fun _ : V => (volume : Measure OSFourSpace))
    Integrable (wilsonJointTraces w F) (μ.prod ν) ∧
      (∫ t, ‖wilsonJointTraces w F t‖ ∂μ.prod ν) ≤ (∫ z, ‖w z‖ ∂μ) * ∏ v, M v :=
  wilson_joint_factors_bound μ hmw hw hm hi M hM

end UV
