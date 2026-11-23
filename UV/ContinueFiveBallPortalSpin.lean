import UV.ContinueFiveBallPortal
import UV.ContinueNormalAllLegsSpin

/-! The normalized Dirac pair cut in the rest frame of its total
momentum. There are three physical spatial current components here.
The spin trace uses the actual occupied and empty energy projectors. -/

noncomputable section

open UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

def portalPairTrace (v : DiracMomentum) (i : Fin 3) : ℂ :=
  let U := diracSlash (osAxis i.succ).val
  (((1-FurtherOptical.projector v)*U)*(FurtherOptical.projector v*U)).trace

theorem portal_projector_trace {v : DiracMomentum} (hv : ‖v‖^2=1) (i : Fin 3) :
    portalPairTrace v i = ((2*(1-(v i.succ)^2):ℝ):ℂ) := by
  let P := diracSlash v
  let u := osAxis i.succ
  let U := diracSlash u.val
  have hu : U*U=1 := by simpa only [U,u.property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq u.val
  have hN : normalFiveDenom 0 v 0 = 1 := by simp [normalFiveDenom,hv]
  have hI : normalDiracFrequency 0 v 0 = (-Complex.I) • P := by simp [normalDiracFrequency,hN,freeDiracNumerator,P]
  have h := normal_zero_transfer_spin 0 v 0 u
  rw [hI,hN] at h
  have he : ⟪u.val,v⟫=v i.succ := by simp [u,osAxis,EuclideanSpace.inner_single_left]
  rw [he] at h
  rw [smul_mul_assoc (-Complex.I) P (diracSlash u.val),smul_mul_smul,neg_mul_neg,Complex.I_mul_I,neg_one_smul,Matrix.trace_neg,one_pow,div_one] at h
  change -((P*U)*(P*U)).trace = _ at h
  let Y := FurtherOptical.projector v
  have hY : Y*U = (1/2:ℂ) • (U-P*U) := by dsimp only [Y,FurtherOptical.projector,P]; rw [smul_mul_assoc,sub_mul,one_mul]
  have hV : (1-Y)*U = (1/2:ℂ) • (U+P*U) := by rw [sub_mul,one_mul,hY]; module
  have hZ : (U*(P*U)).trace = ((P*U)*U).trace := Matrix.trace_mul_comm _ _
  change (((1-Y)*U)*(Y*U)).trace = _
  rw [hV,hY,smul_mul_smul,Matrix.trace_smul]
  simp only [mul_sub,add_mul,Matrix.trace_sub,Matrix.trace_add,hZ,hu,Matrix.trace_one,Fintype.card_fin,smul_eq_mul]
  push_cast at h ⊢
  linear_combination (1/4:ℂ)*h

/-- Polarization-averaged spin trace at invariant s=4E². The phase-space
factor sqrt(1−4m²/s)/(16π²) converts this trace into the normalized
Dirac spectral density in the manuscript. -/
theorem portal_spin_average {m : ℝ} (hm : 0 < m) (k : ChargeSpatialMomentum) :
    (∑ i:Fin 3, (portalPairTrace (FurtherOptical.coefficients m 0 k) i).re)/3 =
      (4/3)*(1+2*m^2/(4*FurtherOptical.energy m k^2)) := by
  let E := FurtherOptical.energy m k
  have hE : 0 < E := FurtherOptical.energy_pos hm _
  have he : E^2=m^2+‖k‖^2 := FurtherOptical.energy_sq m k
  have hv := FurtherOptical.coefficients_norm_sq hm (le_refl (0:ℝ)) k
  have h (i:Fin 3) : FurtherOptical.coefficients m 0 k i.succ = k i/E := by
    change FurtherOptical.attenuation 0 k*k i/E = _
    simp [FurtherOptical.attenuation]
  simp only [portal_projector_trace hv,Complex.ofReal_re,h,div_pow]
  change (∑ i:Fin 3, 2*(1-(k i)^2/E^2))/3=(4/3)*(1+2*m^2/(4*E^2))
  rw [←Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,←Finset.sum_div]
  have hk := EuclideanSpace.norm_sq_eq k
  simp only [Real.norm_eq_abs,sq_abs] at hk
  rw [←hk]
  norm_num
  field_simp [hE.ne']
  nlinarith

/-- Conversion from the total pair energy y to its radial momentum in
the rest chart, at positive relative momentum. -/
theorem portal_radial_jacobian {m y : ℝ} (hm : 0 < m) (hy : 2*m < y) :
    HasDerivAt (fun t:ℝ => Real.sqrt ((t/2)^2-m^2))
      (y/(4*Real.sqrt ((y/2)^2-m^2))) y := by
  have hpos : 0 < (y/2)^2-m^2 := by nlinarith [mul_pos (by linarith : 0 < y/2-m) (by linarith : 0 < y/2+m)]
  convert ((((hasDerivAt_id y).div_const 2).pow 2).sub_const (m^2)).sqrt hpos.ne' using 1
  dsimp
  ring

/-- Direct reconstruction from the spin trace, the angular factor 4π,
the (2π)⁻³ spatial normalization and the radial energy Jacobian.
The external timelike transfer appears once on each side of the cut. -/
theorem portal_cut_from_spin {m b : ℝ} (hm : 0 < m) (k : ChargeSpatialMomentum) (hk : k≠0) :
    let y := 2*FurtherOptical.energy m k
    let spin := (∑ i:Fin 3, (portalPairTrace (FurtherOptical.coefficients m 0 k) i).re)/3
    (4*Real.pi/(2*Real.pi)^3)*‖k‖^2*(y/(4*‖k‖))*spin/y^2*(b^2/(y^2-b)^2) = portalPairCut m b (y^2) := by
  let E := FurtherOptical.energy m k
  have hE : 0 < E := FurtherOptical.energy_pos hm _
  have hs : E^2=m^2+‖k‖^2 := FurtherOptical.energy_sq m k
  have hk0 := norm_pos_iff.mpr hk
  have hy : 4*m^2 ≤ (2*E)^2 := by nlinarith [sq_nonneg ‖k‖]
  have hβ : Real.sqrt (1-4*m^2/(2*E)^2) = ‖k‖/E := by
    rw [Real.sqrt_eq_iff_eq_sq (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hy)) (div_nonneg (norm_nonneg _) hE.le)]
    field_simp
    nlinarith
  dsimp only
  rw [portal_spin_average hm k]
  change _ = portalPairCut m b ((2*E)^2)
  rw [portalPairCut,if_pos hy,openingWeight_eq_of_nonneg (by positivity),hβ]
  change (4*Real.pi/(2*Real.pi)^3)*‖k‖^2*(2*E/(4*‖k‖))*(4/3*(1+2*m^2/(4*E^2)))/(2*E)^2*(b^2/((2*E)^2-b)^2) = _
  ring_nf
  field_simp [hE.ne',hk0.ne',Real.pi_ne_zero]

end UV
