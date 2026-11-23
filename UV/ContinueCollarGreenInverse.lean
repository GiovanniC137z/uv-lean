import UV.ContinueCollarGreenSmoothing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! On smooth tests compactly supported in the radial interval the
Green operator inverts the displayed differential expression. Its kernel
therefore vanishes on all of L². -/

noncomputable section

open MeasureTheory Set Real Filter
open UV.ContinueCollarHSIdentity (radialMeasure radial_measure_eq_open)
open scoped InnerProductSpace Topology ContDiff

namespace UV.CollarEigenmode

private instance : IsFiniteMeasure radialMeasure := ⟨by simp [radialMeasure,Real.volume_Ioc]⟩

private theorem regularMem (u : ℝ → ℝ) (h : Continuous u) : MemLp u 2 radialMeasure :=
  (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mpr ((h.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)

def regularRadial (u : ℝ → ℝ) (h : Continuous u) : RealRadialL2 := (regularMem u h).toLp _

theorem regularRadial_coe (u : ℝ → ℝ) (h : Continuous u) : ∀ᵐ r ∂radialMeasure,regularRadial u h r=u r :=
  (regularMem u h).coeFn_toLp

def dirichletExpression (c : ℝ) (u : ℝ → ℝ) (r : ℝ) := potential (3*c) r*u r-deriv (deriv u) r

theorem testExpression_continuous (c : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hsupp : tsupport u ⊆ Ioo 0 1) :
    Continuous (dirichletExpression c u) := by
  apply Continuous.sub _ ((contDiff_infty_iff_deriv.mp hu).2.continuous_deriv (by simp))
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have hs : (0:ℝ) ∉ tsupport u := fun h => (lt_irrefl 0 (hsupp h).1)
    have h := notMem_tsupport_iff_eventuallyEq.mp hs
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [h] with y hy
    change u y=0 at hy
    simp [hy]
  · have hp : ContinuousAt (potential (3*c)) x := by unfold potential; fun_prop (disch := positivity)
    exact hp.mul hu.continuous.continuousAt

theorem green_inverse_on_test {c : ℝ} (hc : 0<c) (u : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hsupp : tsupport u ⊆ Ioo 0 1) :
    greenOperator hc (regularRadial _ (testExpression_continuous c u hu hsupp)) = regularRadial u hu.continuous := by
  let q := dirichletExpression c u
  have hq : Continuous q := testExpression_continuous c u hu hsupp
  let f := regularRadial q hq
  let w := greenResponse c f
  let G := greenGradient c q
  have hW (x : ℝ) (hx : x ∈ Ioo 0 1) : w x=greenApplied c q x :=
    greenResponse_at_continuous hc f q hq (regularRadial_coe q hq) hx
  have hu' := (contDiff_infty_iff_deriv.mp hu).2
  have hfirst (x : ℝ) (hx : x ∈ Ioo 0 1) : HasDerivAt w (G x) x := by
    apply (green_solves hc q hq hx).1.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hW y hy
  have hsol := dirichlet_homogeneous_unique (c := c) hc (u := fun x => w x-u x) (g := fun x => G x-deriv u x)
    ((greenResponse_continuous hc f).sub hu.continuous).continuousOn
    (by change greenResponse c f 0 - u 0 = 0; rw [(greenResponse_dirichlet c f).1,image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl 0 (hsupp h).1),sub_self])
    (by change greenResponse c f 1 - u 1 = 0; rw [(greenResponse_dirichlet c f).2,image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl 1 (hsupp h).2),sub_self])
    (fun x hx => (hfirst x hx).sub ((hu.differentiable (by simp)).differentiableAt.hasDerivAt))
    (fun x hx => by
      convert (green_solves hc q hq hx).2.sub ((hu'.differentiable (by simp)).differentiableAt.hasDerivAt) using 1
      rw [← hW x hx]; dsimp [q,dirichletExpression]; ring)
  apply Lp.ext
  filter_upwards [greenOperator_coe hc f,regularRadial_coe u hu.continuous,ae_restrict_mem (s := Ioc (0:ℝ) 1) measurableSet_Ioc] with r hr ht hR
  exact hr.trans ((sub_eq_zero.mp (hsol r ⟨hR.1.le,hR.2⟩)).trans ht.symm)

theorem greenOperator_injective {c : ℝ} (hc : 0<c) : Function.Injective (greenOperator hc) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hL1 : Integrable (fun r => f r) radialMeasure := (Lp.memLp f).integrable (by norm_num)
  have htest := (isOpen_Ioo (a := (0:ℝ)) (b := 1)).ae_eq_zero_of_integral_contDiff_smul_eq_zero (hL1.locallyIntegrable.locallyIntegrableOn _) (fun u hu _ hU => by
    let ftest := regularRadial _ (testExpression_continuous c u hu hU)
    have hsym := greenOperator_symmetric hc ftest f
    change ⟪greenOperator hc ftest,f⟫_ℝ=⟪ftest,greenOperator hc f⟫_ℝ at hsym
    rw [green_inverse_on_test hc u hu hU,hf,inner_zero_right,L2.inner_def] at hsym
    refine (integral_congr_ae ?_).trans hsym
    filter_upwards [regularRadial_coe u hu.continuous] with r hr
    simp [hr,mul_comm])
  have hmem : ∀ᵐ r ∂radialMeasure,r ∈ Ioo (0:ℝ) 1 := by rw [radial_measure_eq_open]; exact ae_restrict_mem measurableSet_Ioo
  apply Lp.ext
  filter_upwards [htest,hmem,Lp.coeFn_zero ℝ 2 radialMeasure] with r hr hs hz
  exact (hr hs).trans hz.symm

end UV.CollarEigenmode
