import UV.ContinueFiveBallPortalSpin
import UV.ScalarGaussian

/-! Momentum-resolved Euclidean Dirac spin, orbital and direct terms
for the two-connection portal. Translation of the charged momentum is
valid before the ultraviolet proper-time limit is taken. -/

noncomputable section

open MeasureTheory Set UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

def portalHeatLeg (t v : ℝ) (Q k : ScalarMomentum) :=
  Real.exp (-(t*(1-v))*‖k‖^2-(t*v)*‖k+Q‖^2)

theorem portal_gaussian_spin {t : ℝ} (ht : 0 < t) (v : ℝ) (Q : ScalarMomentum) :
    (∫ k, portalHeatLeg t v Q k) = Real.pi^2/t^2*Real.exp (-(t*‖Q‖^2)*(v*(1-v))) := by
  have hsum : t*(1-v)+t*v=t := by ring
  unfold portalHeatLeg
  rw [two_line_gaussian_integral (by rw [hsum]; exact ht),hsum]
  congr 2
  field_simp

private theorem portal_axis_second {t : ℝ} (ht : 0 < t) (j : Fin 4) :
    (∫ k : ScalarMomentum, (k j)^2*Real.exp (-t*‖k‖^2)) = Real.pi^2/(2*t^3) := by
  let f := fun a:ℝ => Real.exp (-t*a)
  have hI : Integrable (fun k:ScalarMomentum => ‖k‖^2*f (‖k‖^2)) := by
    have h := massless_gaussian_integrable (d := 4) (by norm_num) ht
    norm_num at h
    simpa only [f,neg_mul] using h
  have h := radial_coordinate_diagonal_integral (g := f) (by dsimp [f]; fun_prop) hI j
  have hv := massless_gaussian_integral (d := 4) (by norm_num) ht
  norm_num [Real.Gamma_nat_eq_factorial] at hv
  simp_rw [←pow_two] at h
  change (∫ q:ScalarMomentum, (q j)^2*f (‖q‖^2)) = _
  rw [h]
  dsimp only [f]
  simp only [neg_mul] at hv ⊢
  rw [hv]
  field_simp
  ring

private theorem portal_unit_second {t : ℝ} (ht : 0 < t) (u : UnitVector ScalarMomentum) :
    (∫ k : ScalarMomentum, ⟪u.val,k⟫^2*Real.exp (-t*‖k‖^2)) = Real.pi^2/(2*t^3) := by
  let a := osAxis 0
  let e := (ℝ ∙ (u.val-a.val))ᗮ.reflection
  have he : e u.val = a.val := Submodule.reflection_sub (u.property.trans a.property.symm)
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun k:ScalarMomentum => ⟪a.val,k⟫^2*Real.exp (-t*‖k‖^2))
  rw [←he] at h
  simp only [e.inner_map_map,e.norm_map] at h
  rw [h,he]
  simpa [a,osAxis,EuclideanSpace.inner_single_left] using portal_axis_second ht 0

theorem portal_gaussian_orbital {t : ℝ} (ht : 0 < t) (v : ℝ) (Q : ScalarMomentum) (u : UnitVector ScalarMomentum)
    (hQ : ⟪u.val,Q⟫=0) :
    (∫ k, (2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k) = (2/t)*(∫ k, portalHeatLeg t v Q k) := by
  let c := Real.exp (-(t*‖Q‖^2)*(v*(1-v)))
  have hsum : t*(1-v)+t*v=t := by ring
  have hmove (k:ScalarMomentum) : (2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k =
      (4*c)*(⟪u.val,k+v • Q⟫^2*Real.exp (-t*‖k+v • Q‖^2)) := by
    have hcoef : (t*(1-v)*(t*v))/t = t*v*(1-v) := by field_simp
    simp only [portalHeatLeg,two_line_gaussian_factor (hsum.trans_ne ht.ne') Q k,hsum,hcoef,
      mul_div_cancel_left₀ v ht.ne',inner_add_right,inner_smul_right,hQ,mul_zero,add_zero]
    dsimp only [c]
    rw [show -(t*v*(1-v))*‖Q‖^2 = -(t*‖Q‖^2)*(v*(1-v)) by ring]
    ring
  simp_rw [hmove]
  rw [integral_const_mul,show (∫ k, ⟪u.val,k+v • Q⟫^2*Real.exp (-t*‖k+v • Q‖^2)) = ∫ k, ⟪u.val,k⟫^2*Real.exp (-t*‖k‖^2)
    from integral_add_right_eq_self (μ := volume) (fun k => ⟪u.val,k⟫^2*Real.exp (-t*‖k‖^2)) (v • Q),
    portal_unit_second ht,portal_gaussian_spin ht]
  dsimp only [c]
  field_simp
  ring

/-- The two transverse spin-curvature insertions on the massive Dirac
heat trace give four times the invariant. -/
theorem portal_heat_spin_trace (Q : ScalarMomentum) (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    ((Complex.I • (diracSlash Q*diracSlash u.val))*(Complex.I • (diracSlash Q*diracSlash u.val))).trace = (4*‖Q‖^2:ℝ) := by
  let V := diracSlash Q
  let U := diracSlash u.val
  have hU : U*U=1 := by simpa only [U,u.property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq u.val
  have hg := wilson_slash_anticommutator u.val Q
  rw [hQ,mul_zero,Complex.ofReal_zero,zero_smul] at hg
  have hanti : U*V= -(V*U) := eq_neg_of_add_eq_zero_left hg
  have hs : (V*U)*(V*U) = -((‖Q‖^2:ℝ):ℂ) • (1:DiracMatrix) := by
    calc _ = (V*(U*V))*U := by noncomm_ring
         _ = -((V*V)*(U*U)) := by rw [hanti]; noncomm_ring
         _ = _ := by rw [hU,mul_one,diracSlash_sq]; simp
  change ((Complex.I • (V*U))*(Complex.I • (V*U))).trace = _
  rw [smul_mul_smul,Complex.I_mul_I,hs,smul_smul,Matrix.trace_smul,Matrix.trace_one]
  norm_num
  ring

/-- Transverse proper-time scalar from spin, the two linear orbital
vertices, and the direct quadratic contact. Fourier normalization and
the two external mediator factors are included. -/
def portalResolvedHeat (m b t : ℝ) (Q : ScalarMomentum) (u : UnitVector ScalarMomentum) :=
  let X := ‖Q‖^2
  2*t*Real.exp (-t*m^2)*(portalEuclidean b X)^2/(2*Real.pi)^4 *
    ∫ v in (0:ℝ)..1,
      (∫ k, portalHeatLeg t v Q k) +
      ((∫ k, (2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k) -
        2/t*(∫ k:ScalarMomentum, Real.exp (-t*‖k‖^2))) / X

theorem portal_resolved_proper_time (m b : ℝ) {t : ℝ} (ht : 0 < t) (Q : ScalarMomentum) (hq : Q≠0)
    (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    portalResolvedHeat m b t Q u = portalBare m b (‖Q‖^2) t := by
  let X := ‖Q‖^2
  let A := Real.pi^2/t^2
  let f := fun v:ℝ => Real.exp (-(t*X)*(v*(1-v)))
  have hX : 0 < X := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have h : (∫ v in (0:ℝ)..1, A*f v+((2/t)*(A*f v)-(2/t)*A)/X) = A*(portalSpinMark (t*X)+2*(portalSpinMark (t*X)-1)/(t*X)) := by
    have hsplit (v:ℝ) : A*f v+((2/t)*(A*f v)-(2/t)*A)/X = A*(f v + (2/(t*X))*(f v-1)) := by ring
    simp_rw [hsplit]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hf.intervalIntegrable ..)
      ((continuous_const.mul (hf.sub continuous_const)).intervalIntegrable ..),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hf.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),intervalIntegral.integral_const]
    change A*(portalSpinMark (t*X)+(2/(t*X))*(portalSpinMark (t*X)-(1-0) • (1:ℝ)))=_
    simp only [sub_zero,one_smul]
    ring
  unfold portalResolvedHeat
  simp_rw [portal_gaussian_orbital ht _ Q u hQ,portal_gaussian_spin ht,scalar_gaussian_integral ht]
  change _ * (∫ v in (0:ℝ)..1, A*f v+((2/t)*(A*f v)-(2/t)*A)/X) = _
  rw [h,portal_mark_contact (mul_ne_zero ht.ne' hX.ne')]
  dsimp only [A,X,portalBare]
  field_simp [ht.ne',Real.pi_ne_zero]
  ring

/-- The divergence is already present in the sum of the momentum-resolved
three contributions for every transverse unit polarization at Q ≠ 0. -/
theorem portal_resolved_uv_obstruction (m : ℝ) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (Q : ScalarMomentum) (hq : Q≠0) (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    ¬ IntegrableOn (fun t => portalResolvedHeat m b t Q u) (Ioo 0 δ) := by
  intro hi
  exact portal_bare_nonintegrable m hb (sq_pos_of_pos (norm_pos_iff.mpr hq)) hδ
    (hi.congr_fun (fun t ht => portal_resolved_proper_time m b ht.1 Q hq u hQ) measurableSet_Ioo)

end UV
