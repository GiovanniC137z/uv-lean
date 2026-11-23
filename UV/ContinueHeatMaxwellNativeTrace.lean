import UV.ContinueHeatMaxwellChordMarks
import UV.ContinueWilsonSpinRotation
import UV.FurtherOpticalProjector

/-! The sign and spin multiplicity of the unintegrated straight-link
determinant Hessian from four-component Euclidean Dirac matrices. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane
open scoped RealInnerProductSpace

private theorem heat_slash_pair (p q : DiracMomentum) :
    (diracSlash p * diracSlash q).trace = ((4*⟪p,q⟫:ℝ):ℂ) := by
  have h := congrArg Matrix.trace (wilson_slash_anticommutator p q)
  rw [Matrix.trace_add,Matrix.trace_mul_comm (diracSlash q),Matrix.trace_smul,Matrix.trace_one] at h
  push_cast at h ⊢
  norm_num at h
  linear_combination (1/2:ℂ)*h

private theorem heat_slash_quad (p q v : DiracMomentum) :
    ((diracSlash p*diracSlash v)*(diracSlash q*diracSlash v)).trace =
    ((4*(2*⟪p,v⟫*⟪q,v⟫-⟪p,q⟫*‖v‖^2):ℝ):ℂ) := by
  let P := diracSlash p
  let Q := diracSlash q
  let V := diracSlash v
  have ha : V*Q = ((2*⟪q,v⟫:ℝ):ℂ) • 1-Q*V := by
    have h := wilson_slash_anticommutator v q
    rw [real_inner_comm q v] at h
    exact eq_sub_of_add_eq h
  have he : (P*V)*(Q*V) = ((2*⟪q,v⟫:ℝ):ℂ) • (P*V) - ((‖v‖^2:ℝ):ℂ) • (P*Q) := by
    calc _ = (P*(V*Q))*V := by noncomm_ring
         _ = _ := by rw [ha,mul_sub,sub_mul,mul_smul_comm,mul_one,smul_mul_assoc,
                       ←mul_assoc P Q V,mul_assoc (P*Q) V V,diracSlash_sq,mul_smul_comm,mul_one]
  change ((P*V)*(Q*V)).trace=_
  rw [he,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_smul,heat_slash_pair p v,heat_slash_pair p q,smul_eq_mul,smul_eq_mul]
  push_cast
  ring

private theorem heat_marked_propagator (m : ℝ) (p v : DiracMomentum) :
    freeDiracPropagator m p*(Complex.I • diracSlash v) =
    (((‖p‖^2+m^2:ℝ):ℂ)⁻¹) • ((Complex.I*(m:ℂ)) • diracSlash v + diracSlash p*diracSlash v) := by
  change (_ • ((-Complex.I) • _ + (m:ℂ) • (1 : DiracMatrix)))*_=_
  rw [smul_mul_assoc,add_mul,smul_mul_smul,smul_mul_smul,one_mul,neg_mul,Complex.I_mul_I,
    neg_neg,one_smul,mul_comm (m:ℂ),add_comm (diracSlash p*diracSlash v)]

theorem heat_native_bubble (m : ℝ) (p q v : DiracMomentum) :
    ((freeDiracPropagator m p*(Complex.I • diracSlash v))*
      (freeDiracPropagator m q*(Complex.I • diracSlash v))).trace =
    ((4*(2*⟪p,v⟫*⟪q,v⟫-(m^2+⟪p,q⟫)*‖v‖^2)/((‖p‖^2+m^2)*(‖q‖^2+m^2)):ℝ):ℂ) := by
  have h3 (u : DiracMomentum) : ((diracSlash u*diracSlash v)*diracSlash v).trace=0 := by
    rw [mul_assoc,diracSlash_sq,mul_smul_comm,mul_one,Matrix.trace_smul,FurtherOptical.slash_trace_zero,smul_zero]
  have h3' : (diracSlash v*(diracSlash q*diracSlash v)).trace=0 :=
    (Matrix.trace_mul_comm _ _).trans (h3 q)
  rw [heat_marked_propagator,heat_marked_propagator,smul_mul_smul,Matrix.trace_smul]
  simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,Matrix.trace_add,Matrix.trace_smul,h3,h3',
    add_zero,diracSlash_sq,Matrix.trace_one,heat_slash_quad,smul_eq_mul]
  push_cast
  simp only [Fintype.card_fin,Nat.cast_ofNat,div_eq_mul_inv]
  rw [show (↑‖p‖^2*↑‖q‖^2+(m:ℂ)^2*↑‖q‖^2+(↑‖p‖^2*(m:ℂ)^2+(m:ℂ)^2*(m:ℂ)^2)) = (↑‖p‖^2+(m:ℂ)^2)*(↑‖q‖^2+(m:ℂ)^2) by ring,mul_inv_rev]
  linear_combination (↑‖p‖^2+(m:ℂ)^2)⁻¹*(↑‖q‖^2+(m:ℂ)^2)⁻¹*(m:ℂ)^2*(↑‖v‖^2*4)*Complex.I_mul_I

theorem heat_native_contact (m : ℝ) (p w : DiracMomentum) :
    (freeDiracPropagator m p*(Complex.I • diracSlash w)).trace =
    ((4*⟪p,w⟫/(‖p‖^2+m^2):ℝ):ℂ) := by
  rw [heat_marked_propagator,Matrix.trace_smul,Matrix.trace_add,Matrix.trace_smul,FurtherOptical.slash_trace_zero,
    smul_zero,zero_add,heat_slash_pair]
  push_cast
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- The full two-mark kernel before the four-momentum integral. The
minus sign on the direct contact is that of the negative logarithm. -/
def heatNativeResponse (m : ℝ) (k : EuclideanPlaneMomentum) (t : ℝ) : ℝ :=
  let p := heatSymbol (k+(-t/2) • softLongitudinal.val)
  let q := heatSymbol (k+(t/2) • softLongitudinal.val)
  let h := heatSymbol k
  let v := heatFirstChord k t
  let w := heatContactChord k t
  (2*⟪p,v⟫*⟪q,v⟫-(m^2+⟪p,q⟫)*‖v‖^2)/((‖p‖^2+m^2)*(‖q‖^2+m^2))-⟪h,w⟫/(‖h‖^2+m^2)

theorem heat_native_response_trace (U : EuclideanPlaneMomentum ≃ₗᵢ[ℝ] DiracMomentum)
    (m : ℝ) (k : EuclideanPlaneMomentum) (t : ℝ) :
    let p := U (heatSymbol (k+(-t/2) • softLongitudinal.val))
    let q := U (heatSymbol (k+(t/2) • softLongitudinal.val))
    let h := U (heatSymbol k)
    let v := Complex.I • diracSlash (U (heatFirstChord k t))
    let w := Complex.I • diracSlash (U (heatContactChord k t))
    (((freeDiracPropagator m p*v)*(freeDiracPropagator m q*v)).trace-(freeDiracPropagator m h*w).trace).re =
    4*heatNativeResponse m k t := by
  dsimp only
  rw [heat_native_bubble,heat_native_contact]
  simp only [←Complex.ofReal_sub,Complex.ofReal_re,U.inner_map_map,U.norm_map,heatNativeResponse]
  ring

end UV.HeatMaxwell
