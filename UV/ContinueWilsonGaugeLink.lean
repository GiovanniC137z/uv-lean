import UV.ContinueWilsonShellEndpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The straight Abelian link on the actual two-mark carrier displacement.
Its endpoint phases give gauge covariance before the source trace. -/

noncomputable section

open MeasureTheory Set Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace Matrix

namespace UV

abbrev WilsonConnection := OSFourSpace → OSFourSpace →L[ℝ] ℝ
abbrev WilsonSpinor := Fin 4 → ℂ

def wilsonLineIntegral (B : WilsonConnection) (x d : OSFourSpace) : ℝ :=
  ∫ t in (0:ℝ)..1, B (x+t • d) d

def wilsonLinkPhase (B : WilsonConnection) (x d : OSFourSpace) : ℂ :=
  Complex.exp (Complex.I*(wilsonLineIntegral B x d:ℂ))

theorem wilson_link_unit_modulus (B : WilsonConnection) (x d : OSFourSpace) :
    ‖wilsonLinkPhase B x d‖ = 1 := by simp [wilsonLinkPhase,Complex.norm_exp,Complex.mul_re]

theorem wilson_line_gauge_shift {B : WilsonConnection} (hB : Continuous B) {α : OSFourSpace → ℝ}
    (hα : ContDiff ℝ 1 α) (x d : OSFourSpace) :
    wilsonLineIntegral (fun y => B y+fderiv ℝ α y) x d =
      wilsonLineIntegral B x d + (α (x+d)-α x) := by
  have hp : Continuous (fun t : ℝ => x + t • d) := continuous_const.add (continuous_id.smul continuous_const)
  have hB' := ((hB.comp hp).clm_apply (continuous_const (y := d))).intervalIntegrable (μ := volume) 0 1
  have ha' := (((hα.continuous_fderiv le_rfl).comp hp).clm_apply (continuous_const (y := d))).intervalIntegrable (μ := volume) 0 1
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => α (x+s • d)) (fderiv ℝ α (x+t • d) d) t := by
    have hpath : HasDerivAt (fun s : ℝ => x+s • d) d t := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const d).const_add x
    exact ((hα.differentiable le_rfl (x+t • d)).hasFDerivAt).comp_hasDerivAt t hpath
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ha'
  calc
    _ = wilsonLineIntegral B x d + ∫ t in (0:ℝ)..1, fderiv ℝ α (x+t • d) d := intervalIntegral.integral_add hB' ha'
    _ = _ := by simp only [he,one_smul,zero_smul,add_zero]

def wilsonGaugePhase (α : OSFourSpace → ℝ) (x : OSFourSpace) : ℂ := Complex.exp (Complex.I*(α x:ℂ))

theorem wilson_link_gauge_covariant {B : WilsonConnection} (hB : Continuous B) {α : OSFourSpace → ℝ}
    (hα : ContDiff ℝ 1 α) (x d : OSFourSpace) :
    wilsonLinkPhase (fun y => B y+fderiv ℝ α y) x d =
      (wilsonGaugePhase α x)⁻¹ * wilsonLinkPhase B x d * wilsonGaugePhase α (x+d) := by
  unfold wilsonLinkPhase wilsonGaugePhase
  rw [wilson_line_gauge_shift hB hα,←Complex.exp_neg,←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

variable {ι : Type*} [Fintype ι]

def wilsonPairDisplacement (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (y : WilsonBallSpace ι × WilsonBallSpace ι) : OSFourSpace :=
  L • T.toContinuousLinearMap.adjoint (y.1+y.2)

theorem wilson_pair_displacement_coordinate (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (y : WilsonBallSpace ι × WilsonBallSpace ι) (j : Fin 4) :
    wilsonPairDisplacement L T y j = wilsonTimeDisplacement L (wilsonReadoutUnit T j) y := by
  have he := T.toContinuousLinearMap.adjoint_inner_right (osAxis j).val (y.1+y.2)
  simp only [osAxis,EuclideanSpace.inner_single_left,one_mul,map_one] at he
  change L*(T.toContinuousLinearMap.adjoint (y.1+y.2)) j = L*⟪T (osAxis j).val,y.1+y.2⟫
  rw [he]
  rfl

def wilsonSpinWeight (L : ℝ) (d : OSFourSpace) : DiracMatrix := 1 - (1/(2*(L:ℂ))) • diracSlash d

def wilsonGaugedHop (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (B : WilsonConnection) (ψ : OSFourSpace → WilsonSpinor) (x : OSFourSpace) (i : Fin 4) : ℂ :=
  ∫ y, let d := wilsonPairDisplacement L T y
    wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i
    ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι))

def wilsonChargedSource (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (B : WilsonConnection) (ψ : OSFourSpace → WilsonSpinor) (x : OSFourSpace) (i : Fin 4) : ℂ :=
  (L:ℂ)⁻¹ * (ψ x i - (lam:ℂ)*wilsonGaugedHop L T B ψ x i)

theorem wilson_gauged_hop_covariant (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {B : WilsonConnection} (hB : Continuous B) {α : OSFourSpace → ℝ} (hα : ContDiff ℝ 1 α)
    (ψ : OSFourSpace → WilsonSpinor) (x : OSFourSpace) (i : Fin 4) :
    wilsonGaugedHop L T (fun y => B y + fderiv ℝ α y) ψ x i =
      (wilsonGaugePhase α x)⁻¹ * wilsonGaugedHop L T B (fun y => wilsonGaugePhase α y • ψ y) x i := by
  unfold wilsonGaugedHop
  rw [←integral_const_mul]
  congr 1
  funext y
  simp only [wilson_link_gauge_covariant hB hα,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem wilson_charged_source_gauge_covariant (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {B : WilsonConnection} (hB : Continuous B) {α : OSFourSpace → ℝ} (hα : ContDiff ℝ 1 α)
    (ψ : OSFourSpace → WilsonSpinor) (x : OSFourSpace) (i : Fin 4) :
    wilsonChargedSource L lam T (fun y => B y + fderiv ℝ α y) ψ x i =
      (wilsonGaugePhase α x)⁻¹ * wilsonChargedSource L lam T B (fun y => wilsonGaugePhase α y • ψ y) x i := by
  unfold wilsonChargedSource
  rw [wilson_gauged_hop_covariant L T hB hα]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp [show wilsonGaugePhase α x ≠ 0 from Complex.exp_ne_zero _]

/-- Evaluating the general gauge link at zero background on an axial
exponential and a basis spinor recovers the integrated rest matrix. -/
theorem wilson_zero_background_matches_shell (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (z : ℂ) (i j : Fin 4) :
    wilsonGaugedHop L T 0 (fun x => Complex.exp (-z*(x 0:ℂ)) • (Pi.single j (1:ℂ) : WilsonSpinor)) 0 i = wilsonShellHop L T z i j := by
  unfold wilsonGaugedHop wilsonShellHop
  congr 1
  funext y
  simp [wilsonLinkPhase,wilsonLineIntegral,wilsonSpinWeight,diracSlash,Matrix.mulVec_smul,
    Matrix.col,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,wilson_pair_displacement_coordinate]
  by_cases h : i = j
  · rw [h]
  · simp [h,Ne.symm h]

end UV
