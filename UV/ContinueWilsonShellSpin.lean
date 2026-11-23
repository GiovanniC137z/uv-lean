import UV.ContinueWilsonShellLaw
import UV.ContinueWilsonChargedPole
import UV.ContinueOSResolvent
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The isometric four-coordinate readout of both shell marks. Reflection
in the unit time axis eliminates all spatial spin moments at rest. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

def wilsonReadoutUnit (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (j : Fin 4) :
    SectorPlane.UnitVector (WilsonBallSpace ι) :=
  ⟨T (osAxis j).val, (T.norm_map _).trans (osAxis j).property⟩

theorem wilson_readout_orthogonal (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {j : Fin 4} (hj : j ≠ 0) :
    ⟪(wilsonReadoutUnit T 0).val,(wilsonReadoutUnit T j).val⟫ = 0 := by
  simp [wilsonReadoutUnit,osAxis,T.inner_map_map,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply,Ne.symm hj]

theorem wilson_spatial_spin_zero (L : ℝ) (u v : SectorPlane.UnitVector (WilsonBallSpace ι))
    (ho : ⟪u.val,v.val⟫ = 0) (z : ℂ) :
    ∫ y, (wilsonTimeDisplacement L v y : ℂ)*Complex.exp (-z*(wilsonTimeDisplacement L u y : ℂ))
      ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)) = 0 := by
  let K := Submodule.span ℝ {u.val}
  let e := K.reflection
  have hu : e u.val = u.val := Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _)
  have hv : e v.val = -v.val := Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho)
  have hup (x : WilsonBallSpace ι) : ⟪u.val,e x⟫ = ⟪u.val,x⟫ := by
    simpa only [hu] using e.inner_map_map u.val x
  have hvp (x : WilsonBallSpace ι) : ⟪v.val,e x⟫ = -⟪v.val,x⟫ := by
    have he := e.inner_map_map v.val x
    rw [hv,inner_neg_left] at he
    exact neg_eq_iff_eq_neg.mp he
  let f := fun y => (wilsonTimeDisplacement L v y:ℂ)*Complex.exp (-z*(wilsonTimeDisplacement L u y:ℂ))
  have hp := (wilson_ball_isometry e).prod (wilson_ball_isometry e)
  have he := hp.integral_comp (e.toMeasurableEquiv.prodCongr e.toMeasurableEquiv).measurableEmbedding f
  have hf (y : WilsonBallSpace ι × WilsonBallSpace ι) : f (Prod.map e e y) = -f y := by
    change (((L*⟪v.val,e y.1+e y.2⟫:ℝ):ℂ) * Complex.exp (-z*((L*⟪u.val,e y.1+e y.2⟫:ℝ):ℂ))) = _
    rw [← e.map_add,hup,hvp]
    simp only [f,wilsonTimeDisplacement,mul_neg,Complex.ofReal_neg,neg_mul]
  simp only [hf,integral_neg] at he
  change (∫ y, f y ∂_) = 0
  linear_combination (-1/2:ℂ)*he

theorem WilsonRestLaw.complex_moment_reflect {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (z : ℂ) :
    D.complexMoment n (-z) = (-1:ℂ)^n * D.complexMoment n z := by
  unfold WilsonRestLaw.complexMoment
  rw [← D.symmetric.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
    (fun s : ℝ => (s:ℂ)^n*Complex.exp (-z*(s:ℂ))),←integral_const_mul]
  congr 1
  funext s
  simp only [Complex.ofReal_neg,neg_mul_neg,neg_one_mul,← mul_assoc,←mul_pow]

theorem wilson_shell_complex_moment {L : ℝ} (hL : 0 < L) (u : SectorPlane.UnitVector (WilsonBallSpace ι))
    (n : ℕ) (z : ℂ) :
    (∫ y, (wilsonTimeDisplacement L u y : ℂ)^n*Complex.exp (-z*(wilsonTimeDisplacement L u y : ℂ))
      ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι))) =
      (-1:ℂ)^n*(wilsonShellRestLaw hL u).complexMoment n z := by
  rw [← (wilsonShellRestLaw hL u).complex_moment_reflect]
  unfold WilsonRestLaw.complexMoment
  change _ = ∫ s, (s:ℂ)^n * Complex.exp (-z*(s:ℂ)) ∂wilsonTimeMarginal L u
  rw [wilsonTimeMarginal,integral_map (wilsonTimeDisplacement_continuous L u).measurable.aemeasurable (by fun_prop)]

end UV
