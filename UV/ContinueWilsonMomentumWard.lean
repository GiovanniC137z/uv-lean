import UV.ContinueWilsonDisplacementDensity
import UV.ContinueWilsonPolygonCurrent
import UV.ContinueOSOrientedProbe

/-! Plane-wave tests of the actual untraced Wilson source, its contracted
one-photon insertion, and transport of the same link on a sector chart. -/

noncomputable section

open MeasureTheory Set UV.SectorPlane
open scoped Topology RealInnerProductSpace Matrix

namespace UV

variable {ι : Type*} [Fintype ι]

def wilsonMomentumProbe (p : OSFourSpace) (v : WilsonSpinor) (y : OSFourSpace) : WilsonSpinor :=
  thinPlaneWave p y • v

def wilsonMomentumSymbol (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace)
    (v : WilsonSpinor) (i : Fin 4) : ℂ :=
  wilsonChargedSource L lam T 0 (wilsonMomentumProbe p v) 0 i

theorem wilson_wave_add (a p d : OSFourSpace) :
    thinPlaneWave a d * thinPlaneWave p d = thinPlaneWave (p+a) d := by
  simp only [thinPlaneWave,←Complex.exp_add,inner_add_left,Complex.ofReal_add]
  congr 1
  ring

theorem wilson_constant_connection_link (a x d : OSFourSpace) :
    wilsonLinkPhase (fun _ => innerSL ℝ a) x d = thinPlaneWave a d := by
  simp [wilsonLinkPhase,wilsonLineIntegral,innerSL_apply,thinPlaneWave]

theorem wilson_constant_connection_shift (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (p a : OSFourSpace) (v : WilsonSpinor) (i : Fin 4) :
    wilsonChargedSource L lam T (fun _ => innerSL ℝ a) (wilsonMomentumProbe p v) 0 i =
      wilsonMomentumSymbol L lam T (p+a) v i := by
  unfold wilsonMomentumSymbol wilsonChargedSource wilsonGaugedHop
  simp only [wilsonMomentumProbe,zero_add,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,
    wilson_constant_connection_link,←mul_assoc,wilson_wave_add]
  simp [wilsonLinkPhase,wilsonLineIntegral,thinPlaneWave]

def wilsonHopMomentumDensity (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace)
    (v : WilsonSpinor) (i : Fin 4) (d : OSFourSpace) : ℂ :=
  ((wilsonDisplacementDensity L T d).toReal:ℂ) * (thinPlaneWave p d * (wilsonSpinWeight L d *ᵥ v) i)

theorem wilson_hop_momentum_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (p : OSFourSpace) (v : WilsonSpinor) (i : Fin 4) : Integrable (wilsonHopMomentumDensity L T p v i) := by
  have hc : Continuous (wilsonMomentumProbe p v) := by unfold wilsonMomentumProbe thinPlaneWave; fun_prop
  simpa [wilsonHopMomentumDensity,wilsonMomentumProbe,wilsonLinkPhase,wilsonLineIntegral,
    Matrix.mulVec_smul] using wilson_density_hop_integrable hL T (B := 0) continuous_zero hc 0 i

theorem wilson_momentum_symbol_integral {L : ℝ} (hL : 0 < L) (lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) (v : WilsonSpinor) (i : Fin 4) :
    wilsonMomentumSymbol L lam T p v i = (L:ℂ)⁻¹*(v i-(lam:ℂ)*∫ d, wilsonHopMomentumDensity L T p v i d) := by
  have hc : Continuous (wilsonMomentumProbe p v) := by unfold wilsonMomentumProbe thinPlaneWave; fun_prop
  unfold wilsonMomentumSymbol wilsonChargedSource
  rw [wilson_density_hop_for_fields hL T (B := 0) continuous_zero hc.measurable]
  simp [wilsonHopMomentumDensity,wilsonMomentumProbe,wilsonLinkPhase,wilsonLineIntegral,
    Matrix.mulVec_smul,thinPlaneWave]

/-- Contracting the plane-wave photon on the straight link with its transfer
gives precisely the finite difference of the full free inverse on every
basis or test spinor, including its shell profile and spin matrix. -/
theorem wilson_source_ward_contracted {L : ℝ} (hL : 0 < L) (lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p q : OSFourSpace) (v : WilsonSpinor) (i : Fin 4) :
    wilsonMomentumSymbol L lam T (p+q) v i - wilsonMomentumSymbol L lam T p v i =
      -((L:ℂ)⁻¹*(lam:ℂ)) * ∫ d, wilsonHopMomentumDensity L T p v i d *
        (Complex.I*(⟪q,d⟫:ℂ)*wilsonEdgeWave q 0 d) := by
  have h (d : OSFourSpace) : wilsonHopMomentumDensity L T p v i d *
      (Complex.I*(⟪q,d⟫:ℂ)*wilsonEdgeWave q 0 d) =
      wilsonHopMomentumDensity L T (p+q) v i d - wilsonHopMomentumDensity L T p v i d := by
    rw [wilson_edge_contraction,zero_add]
    simp only [wilsonHopMomentumDensity,←wilson_wave_add q p d,
      show thinPlaneWave q 0 = 1 by simp [thinPlaneWave]]
    ring
  simp_rw [h]
  rw [integral_sub (wilson_hop_momentum_integrable hL T (p+q) v i) (wilson_hop_momentum_integrable hL T p v i),
    wilson_momentum_symbol_integral hL,wilson_momentum_symbol_integral hL]
  ring

variable {E : Type*} [NormedAddCommGroup E]

/-- A one-form pulls back with its tangent, including the sign of the
centred GT coordinate on the opposite sector. -/
theorem SectorPlane.Plane.wilson_link_chart (diamond : Plane E) (B : WilsonConnection) (x d : OSFourSpace) :
    wilsonLinkPhase (fun y => (B (diamond.osOrientedChart y)).comp diamond.osOrientedChart.toContinuousLinearEquiv.toContinuousLinearMap) x d =
      wilsonLinkPhase B (diamond.osOrientedChart x) (diamond.osOrientedChart d) := by
  simp [wilsonLinkPhase,wilsonLineIntegral]

theorem SectorPlane.Plane.wilson_wave_unit_chart (diamond : Plane E) (u : UnitVector OSFourSpace) (p : OSFourSpace) :
    ‖diamond.osOrientedChart u.val‖ = 1 ∧
      thinPlaneWave (diamond.osOrientedChart p) (diamond.osOrientedChart u.val) = thinPlaneWave p u.val :=
  ⟨(diamond.osOrientedChart.norm_map _).trans u.property, by simp [thinPlaneWave]⟩

end UV
