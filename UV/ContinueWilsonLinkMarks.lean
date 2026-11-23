import UV.ContinueWilsonGaugeLink

/-! Repeated field variations of the same straight link. Insertions on a
single hop include all contact terms with their relative phases. -/

noncomputable section

open MeasureTheory Set Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace ContinuousMap

namespace UV

abbrev WilsonContinuousConnection := C(OSFourSpace,OSFourSpace →L[ℝ] ℝ)

theorem wilson_line_variation (B A : WilsonContinuousConnection) (t : ℝ) (x d : OSFourSpace) :
    wilsonLineIntegral (B+t • A : WilsonContinuousConnection) x d = wilsonLineIntegral B x d + t*wilsonLineIntegral A x d := by
  let path := fun s : ℝ => x+s • d
  have hp : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  have hB := ((B.continuous.comp hp).clm_apply (continuous_const (y := d))).intervalIntegrable (μ := volume) 0 1
  have hA := ((A.continuous.comp hp).clm_apply (continuous_const (y := d))).intervalIntegrable (μ := volume) 0 1
  calc
    _ = (∫ s in (0:ℝ)..1, B (path s) d) + ∫ s in (0:ℝ)..1, t*A (path s) d :=
      intervalIntegral.integral_add hB (hA.const_mul t)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

theorem wilson_link_field_derivative (B A : WilsonContinuousConnection) (x d : OSFourSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => wilsonLinkPhase (B+s • A : WilsonContinuousConnection) x d)
      ((Complex.I*(wilsonLineIntegral A x d:ℂ))*wilsonLinkPhase (B+t • A : WilsonContinuousConnection) x d) t := by
  let c := Complex.I*(wilsonLineIntegral B x d:ℂ)
  let k := Complex.I*(wilsonLineIntegral A x d:ℂ)
  have he (s : ℝ) : wilsonLinkPhase (B+s • A : WilsonContinuousConnection) x d = Complex.exp (c+(s:ℂ)*k) := by
    unfold wilsonLinkPhase
    rw [wilson_line_variation]
    push_cast
    congr 1
    dsimp [c,k]
    ring
  rw [funext he,he t]
  change HasDerivAt (fun s : ℝ => Complex.exp (c+(s:ℂ)*k)) (k*Complex.exp (c+(t:ℂ)*k)) t
  rw [mul_comm k]
  simpa only [one_mul] using ((((hasDerivAt_id (t:ℂ)).mul_const k).const_add c).cexp).comp_ofReal

def wilsonMixedLink (x d : OSFourSpace) : List WilsonContinuousConnection → WilsonContinuousConnection → ℂ
  | [], B => wilsonLinkPhase B x d
  | A :: rest, B => deriv (fun t : ℝ => wilsonMixedLink x d rest (B+t • A)) 0

theorem wilson_mixed_link_all_orders (x d : OSFourSpace) (As : List WilsonContinuousConnection)
    (B : WilsonContinuousConnection) :
    wilsonMixedLink x d As B =
      (As.map (fun A : WilsonContinuousConnection => Complex.I*(wilsonLineIntegral A x d:ℂ))).prod * wilsonLinkPhase B x d := by
  induction As generalizing B with
  | nil => simp [wilsonMixedLink]
  | cons A As ih =>
    let c := (As.map (fun C : WilsonContinuousConnection => Complex.I*(wilsonLineIntegral C x d:ℂ))).prod
    have he := (wilson_link_field_derivative B A x d 0).const_mul c
    simp only [wilsonMixedLink,ih,List.map_cons,List.prod_cons]
    rw [he.deriv]
    have hzero : B + (0:ℝ) • A = B := by
      ext y v
      change B y v + (0:ℝ)*(A y v) = B y v
      simp
    rw [hzero]
    dsimp [c]
    ring

theorem wilson_mixed_link_norm (x d : OSFourSpace) (As : List WilsonContinuousConnection) (B : WilsonContinuousConnection) :
    ‖wilsonMixedLink x d As B‖ = (As.map (fun A : WilsonContinuousConnection => |wilsonLineIntegral A x d|)).prod := by
  rw [wilson_mixed_link_all_orders,norm_mul,wilson_link_unit_modulus,mul_one]
  induction As with
  | nil => simp
  | cons A As ih =>
    simp only [List.map_cons,List.prod_cons,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,ih]

theorem wilson_pair_displacement_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (y : WilsonBallSpace ι × WilsonBallSpace ι)
    (hy : ‖y.1‖ ≤ 1) (hy' : ‖y.2‖ ≤ 1) : ‖wilsonPairDisplacement L T y‖ ≤ 2*L := by
  rw [wilsonPairDisplacement,norm_smul,Real.norm_eq_abs,abs_of_nonneg hL]
  have he := T.toContinuousLinearMap.adjoint.le_opNorm (y.1+y.2)
  rw [LinearIsometryEquiv.norm_map,T.norm_toContinuousLinearMap,one_mul] at he
  nlinarith [he.trans (norm_add_le y.1 y.2)]

end UV
