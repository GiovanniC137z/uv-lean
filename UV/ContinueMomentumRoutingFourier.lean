import UV.ContinueMomentumRoutingPhysical
import UV.ContinueNormalConstrainedTransform
import UV.ContinueNormalOpenCoordinates

/-! The Fourier coefficient of an open propagator chain with fixed
normal endpoints, including its unmarked terminal propagator. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology

namespace UV

local instance momentumFourierMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance momentumFourierMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

variable {r : ℕ} {m L : ℝ}

def momentumOpenCover (m : ℝ) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) (D : ℝ) : DiracMatrix :=
  ∫ x, normalOpenDiracWord normalCoverGamma5 m D u p x

private theorem momentum_open_joint_measurable (m : ℝ) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    Measurable (fun z : ℝ × (Fin r → ℝ) => normalOpenDiracWord normalCoverGamma5 m z.1 u p z.2) := by
  apply normal_ordered_measurable
  intro i
  apply Measurable.mul_const
  apply normal_cover_args_measurable _ _ measurable_const
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst.sub (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd)
  · exact (measurable_pi_apply j).comp measurable_snd

private theorem momentum_open_joint_integrable (hm : 0 < m) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    Integrable (fun z : ℝ × (Fin r → ℝ) => normalOpenDiracWord normalCoverGamma5 m z.1 u p z.2) := by
  have he := (normal_open_laplace_mass hm).1
  have h := (he.const_mul ((2:ℝ)^(r+1))).mul_prod (Integrable.fintype_prod (fun _ : Fin r => he))
  exact h.mono' (momentum_open_joint_measurable _ _ _).aestronglyMeasurable
    (Eventually.of_forall fun z => normal_open_dirac_majorant _ normal_cover_gamma_norm hm z.1 u p z.2)

private theorem momentum_open_mark_transform (hm : 0 < m) (p : OSFourSpace) (V : DiracMatrix) (ξ : ℝ) :
    let F := fun d => normalAngularPhase ξ d • (normalDiracCover normalCoverGamma5 m p d * V)
    Integrable F ∧ (∫ d, F d) = normalDiracFrequency m p ξ * V := by
  let g := fun d => normalAngularPhase ξ d • normalDiracCover normalCoverGamma5 m p d
  have hg : Integrable g := (normal_cover_angular_fourier normalCoverGamma5 hm p ξ).1
  dsimp only
  simp_rw [←smul_mul_assoc]
  exact ⟨((ContinuousLinearMap.mul ℝ DiracMatrix).flip V).integrable_comp hg,
    (integral_mul_const_of_integrable hg).trans (congrArg (·*V) (normal_frequency_is_cover_transform hm p ξ))⟩

theorem momentum_open_cover_transform (hm : 0 < m) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) (ξ : ℝ) :
    (∫ D, normalAngularPhase ξ D • momentumOpenCover m u p D) =
      normalOrderedWord (fun i => normalDiracFrequency m (p i) ξ * normalOpenVertex u i) := by
  let A := fun i d => normalDiracCover normalCoverGamma5 m (p i) d * normalOpenVertex u i
  let B := fun i d => normalAngularPhase ξ d • A i d
  let tail := fun x : Fin r → ℝ => normalOrderedWord (fun i => A i.succ (x i))
  let btail := fun x : Fin r → ℝ => normalOrderedWord (fun i => B i.succ (x i))
  have hB (i) := momentum_open_mark_transform hm (p i) (normalOpenVertex u i) ξ
  have hmB (i) : Measurable (B i) :=
    (show Continuous (normalAngularPhase ξ) by unfold normalAngularPhase; fun_prop).measurable.smul
      ((normal_cover_args_measurable normalCoverGamma5 m (p := fun _ : ℝ => p i) measurable_const measurable_id).mul_const _)
  have hbI : Integrable btail := normal_ordered_integrable _ (fun i => hmB i.succ) (fun i => (hB i.succ).1)
  have hBt (x : Fin r → ℝ) : btail x = normalAngularPhase ξ (∑ j, x j) • tail x := by
    dsimp only [btail,B,tail]
    rw [normal_ordered_word_smul,normal_angular_phase_sum]
  let F := fun (D : ℝ) (x : Fin r → ℝ) => normalAngularPhase ξ D • normalOpenDiracWord normalCoverGamma5 m D u p x
  have hFI : Integrable (Function.uncurry F) (volume.prod volume) := by
    apply (momentum_open_joint_integrable hm u p).norm.mono'
    · exact (((show Continuous (normalAngularPhase ξ) by unfold normalAngularPhase; fun_prop).measurable.comp measurable_fst).smul
        (momentum_open_joint_measurable m u p)).aestronglyMeasurable
    · exact Eventually.of_forall fun z => by simp only [Function.uncurry,F,norm_smul,normal_angular_phase_norm,one_mul,le_refl]
  have hinner (x : Fin r → ℝ) : (∫ D, F D x) = (∫ d, B 0 d)*btail x := by
    let S := ∑ i, x i
    rw [←integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun D => F D x) S]
    have he (d : ℝ) : F (d+S) x = B 0 d * btail x := by
      rw [hBt]
      dsimp only [F,normalOpenDiracWord]
      rw [List.ofFn_succ,List.prod_cons]
      change normalAngularPhase ξ (d+S) • (A 0 (d+S-S)*tail x) = (normalAngularPhase ξ d • A 0 d)*(normalAngularPhase ξ S • tail x)
      rw [add_sub_cancel_right,normal_angular_phase_add,smul_mul_smul]
    simp_rw [he]
    exact integral_mul_const_of_integrable (hB 0).1
  change (∫ D, normalAngularPhase ξ D • ∫ x, normalOpenDiracWord normalCoverGamma5 m D u p x) = _
  simp_rw [←integral_smul]
  change (∫ D, ∫ x, F D x) = _
  rw [integral_integral_swap hFI]
  simp_rw [hinner]
  rw [integral_const_mul_of_integrable hbI]
  change (∫ d, B 0 d)*(∫ x : Fin r → ℝ, normalOrderedWord (fun i => B i.succ (x i))) = _
  rw [normal_ordered_integral _ (fun i => hmB i.succ) (fun i => (hB i.succ).1)]
  have hv (i) : (∫ d, B i d) = normalDiracFrequency m (p i) ξ*normalOpenVertex u i := (hB i).2
  simp_rw [hv]
  conv_rhs => rw [normalOrderedWord,List.ofFn_succ,List.prod_cons]
  rfl

theorem momentum_periodic_open_fourier (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin (r+1) → OSFourSpace) (n : ℤ) :
    L • (∫ t in Ioc (0:ℝ) 1, normalAngularPhase (2*Real.pi*(n:ℝ)) t •
        (L^r • ∫ x, normalOpenPositionWord m L θ 0 (t:UnitAddCircle) u p x)) =
      normalOrderedWord (fun i => normalDiracFrequency m (p i) ((2*Real.pi*(n:ℝ)+θ)/L) * normalOpenVertex u i) := by
  let ξ := (2*Real.pi*(n:ℝ)+θ)/L
  let F := fun d => normalAngularPhase ξ d • momentumOpenCover m u p d
  have hg : Integrable (momentumOpenCover m u p) := (momentum_open_joint_integrable hm u p).integral_prod_left
  have hF : Integrable F := hg.norm.mono'
    ((show Continuous (normalAngularPhase ξ) by unfold normalAngularPhase; fun_prop).aestronglyMeasurable.smul hg.aestronglyMeasurable)
    (Eventually.of_forall fun _ => by simp only [F,norm_smul,normal_angular_phase_norm,one_mul,le_refl])
  have he (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      normalAngularPhase (2*Real.pi*(n:ℝ)) t • (L^r • ∫ x, normalOpenPositionWord m L θ 0 (t:UnitAddCircle) u p x) =
        ∑' j : ℤ,F (L*(t+(j:ℝ))) := by
    have h0 : (0:ℝ) ∈ Icc 0 L := ⟨le_rfl,hL.le⟩
    have ht' : L*t ∈ Icc 0 L := ⟨mul_nonneg hL.le ht.1.le,mul_le_of_le_one_right hL.le ht.2⟩
    have hv := normal_open_position_integral hm hL θ 0 (L*t) h0 ht' u p
    simp only [zero_div,AddCircle.coe_zero,sub_zero,mul_div_cancel_left₀ t hL.ne'] at hv
    rw [hv,←tsum_const_smul'']
    apply tsum_congr fun j => ?_
    rw [smul_smul,normal_circle_mode_phase hL]
    congr 1
    dsimp [momentumOpenCover]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc he]
  rw [normal_cell_integral_tsum (hF.comp_mul_left' hL.ne'),Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hL),
    smul_smul,mul_inv_cancel₀ hL.ne',one_smul]
  exact momentum_open_cover_transform hm u p ξ

end UV
