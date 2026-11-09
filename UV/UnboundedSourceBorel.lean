import UV.UnboundedSourcePVM
import UV.UnboundedSourceSpectral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Operational real bounded Borel spectral calculus on an actual PVM.
The fields are the standard algebra/normality laws of the supplied spectral
calculus. Spectral moment limits refer to actual finite projection sums.
No cut-domain, common-core, intertwining or covariance identity is a field. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace UV

def sourceBoundedBorel (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |f u| ≤ C

theorem sourceBoundedBorel_zero : sourceBoundedBorel (fun _ => 0) :=
  ⟨measurable_const,0,le_rfl,fun _ => by simp⟩

theorem sourceBoundedBorel_one : sourceBoundedBorel (fun _ => 1) :=
  ⟨measurable_const,1,zero_le_one,fun _ => by simp⟩

theorem sourceBoundedBorel_indicator {s : Set ℝ} (hs : MeasurableSet s) :
    sourceBoundedBorel (s.indicator (fun _ => (1 : ℝ))) := by
  refine ⟨measurable_const.indicator hs,1,zero_le_one,fun u => ?_⟩
  by_cases hu : u ∈ s <;> simp [hu]

theorem sourceBoundedBorel_add {f g : ℝ → ℝ} (hf : sourceBoundedBorel f)
    (hg : sourceBoundedBorel g) : sourceBoundedBorel (fun u => f u+g u) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  obtain ⟨D,hD,hgD⟩ := hg.2
  exact ⟨hf.1.add hg.1,C+D,add_nonneg hC hD,fun u =>
    (abs_add_le _ _).trans (add_le_add (hfC u) (hgD u))⟩

theorem sourceBoundedBorel_smul (a : ℝ) {f : ℝ → ℝ} (hf : sourceBoundedBorel f) :
    sourceBoundedBorel (fun u => a*f u) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  refine ⟨measurable_const.mul hf.1,|a| * C,mul_nonneg (abs_nonneg _) hC,fun u => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hfC u) (abs_nonneg _)

theorem sourceBoundedBorel_mul {f g : ℝ → ℝ} (hf : sourceBoundedBorel f)
    (hg : sourceBoundedBorel g) : sourceBoundedBorel (fun u => f u*g u) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  obtain ⟨D,hD,hgD⟩ := hg.2
  refine ⟨hf.1.mul hg.1,C*D,mul_nonneg hC hD,fun u => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hfC u) (hgD u) (abs_nonneg _) hC

theorem sourceBoundedBorel_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, sourceBoundedBorel (f i)) :
    sourceBoundedBorel (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sourceBoundedBorel_zero
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using sourceBoundedBorel_add
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem sourceBoundedBorel_simple (f : SimpleFunc ℝ ℝ) : sourceBoundedBorel f := by
  obtain ⟨C,hC⟩ := (f.map abs).exists_forall_le
  refine ⟨f.measurable,max C 0,le_max_right _ _,fun u => ?_⟩
  exact (hC u).trans (le_max_left _ _)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The standard real bounded Borel calculus of the supplied spectral PVM.
Generic bounded-pointwise normality is not specialized to the desired core. -/
structure SourceBorelCalculus (P : SourcePVM H) where
  operator : (ℝ → ℝ) → H →L[ℂ] H
  indicator : ∀ s, MeasurableSet s → operator (s.indicator (fun _ => 1)) = P.projection s
  add : ∀ f g, sourceBoundedBorel f → sourceBoundedBorel g →
    operator (fun u => f u+g u) = operator f+operator g
  smul : ∀ a f, sourceBoundedBorel f → operator (fun u => a*f u) = (a : ℂ) • operator f
  mul : ∀ f g, sourceBoundedBorel f → sourceBoundedBorel g →
    operator (fun u => f u*g u) = operator f*operator g
  selfAdjoint : ∀ f, sourceBoundedBorel f → IsSelfAdjoint (operator f)
  norm_le : ∀ f C, Measurable f → 0 ≤ C → (∀ u, |f u| ≤ C) → ‖operator f‖ ≤ C
  strong_limit : ∀ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (C : ℝ),
    (∀ n, Measurable (f n)) → Measurable g → 0 ≤ C →
    (∀ n u, |f n u| ≤ C) → (∀ u, Tendsto (fun n => f n u) atTop (𝓝 (g u))) →
    ∀ x : H, Tendsto (fun n => operator (f n) x) atTop (𝓝 (operator g x))

def sourceSimpleSpectralIntegral (P : SourcePVM H) (f : SimpleFunc ℝ ℝ) : H →L[ℂ] H :=
  ∑ v ∈ f.range, (v : ℂ) • P.projection (f ⁻¹' {v})

theorem sourceBorel_zero {P : SourcePVM H} (C : SourceBorelCalculus P) :
    C.operator (fun _ => 0) = 0 := by
  simpa only [indicator_empty',P.empty] using C.indicator ∅ MeasurableSet.empty

theorem sourceBorel_sum {P : SourcePVM H} (C : SourceBorelCalculus P) {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, sourceBoundedBorel (f i)) :
    C.operator (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, C.operator (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sourceBorel_zero C
  | @insert i s hi ih =>
    rw [show (fun u => ∑ j ∈ insert i s, f j u) = fun u => f i u+∑ j ∈ s, f j u by
      funext u; simp only [Finset.sum_insert hi]]
    rw [C.add _ _ (hf i (Finset.mem_insert_self _ _))
      (sourceBoundedBorel_sum s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)),Finset.sum_insert hi]

/-- Finite simple integrals are the actual PVM projection sums, derived from
linearity and agreement on indicators. -/
theorem sourceBorel_simple {P : SourcePVM H} (C : SourceBorelCalculus P) (f : SimpleFunc ℝ ℝ) :
    C.operator f = sourceSimpleSpectralIntegral P f := by
  have he : (f : ℝ → ℝ) = fun u => ∑ v ∈ f.range,
      v*(f ⁻¹' {v}).indicator (fun _ => (1 : ℝ)) u := by
    funext u
    classical
    rw [Finset.sum_eq_single (f u)]
    · simp
    · intro v hv hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (f.mem_range_self u)).elim
  rw [he,sourceBorel_sum C]
  · unfold sourceSimpleSpectralIntegral
    apply Finset.sum_congr rfl
    intro v hv
    rw [C.smul _ _ (sourceBoundedBorel_indicator (f.measurableSet_fiber v)),
      C.indicator _ (f.measurableSet_fiber v)]
  · intro v hv
    exact sourceBoundedBorel_smul v (sourceBoundedBorel_indicator (f.measurableSet_fiber v))

def sourceCoordinateApprox (n : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id univ 0 (mem_univ _) n

theorem sourceCoordinateApprox_tendsto (u : ℝ) :
    Tendsto (fun n => sourceCoordinateApprox n u) atTop (𝓝 u) :=
  SimpleFunc.tendsto_approxOn measurable_id (mem_univ (0 : ℝ)) (by simp)

theorem sourceCoordinateApprox_bound (n : ℕ) (u : ℝ) :
    |sourceCoordinateApprox n u| ≤ 2*|u| := by
  simpa only [sourceCoordinateApprox, Real.norm_eq_abs, id_eq, two_mul] using
    SimpleFunc.norm_approxOn_zero_le measurable_id (mem_univ (0 : ℝ)) u n

/-- The actual separate spectral resolution of an unbounded operator.
The graph is its coordinate-moment operator, using explicitly constructed
simple approximants. No source covariance or common-core result is assumed. -/
structure SourceSpectralResolution (K : H →ₗ.[ℂ] H) where
  measure : SourcePVM H
  calculus : SourceBorelCalculus measure
  moment : ∀ x y : H, (x,y) ∈ K.graph ↔
    Tendsto (fun n => sourceSimpleSpectralIntegral measure (sourceCoordinateApprox n) x)
      atTop (𝓝 y)

end UV
