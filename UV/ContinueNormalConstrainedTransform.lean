import UV.ContinueNormalCoverConvolution
import UV.ContinueNormalCircleCells

/-! The angular Fourier transform of an ordered Dirac convolution
with one eliminated increment. Each polarization is a unit vector. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology FourierTransform

namespace UV

local instance normalTransformMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalTransformMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

def normalCoverMark (m : ℝ) (p : OSFourSpace) (u : UnitVector OSFourSpace) (d : ℝ) : DiracMatrix :=
  normalDiracCover normalCoverGamma5 m p d * diracSlash u.val

theorem normal_mark_bound {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (u : UnitVector OSFourSpace) (d : ℝ) :
    ‖normalCoverMark m p u d‖ ≤ 2*Real.exp (-m*|d|) := by
  apply (norm_mul_le _ _).trans
  rw [wilson_slash_opnorm,u.property,mul_one]
  apply (normal_dirac_cover_bound _ normal_cover_gamma_norm hm _ _).trans
  have h := mul_le_mul_of_nonneg_right (normal_cover_energy_bounds hm p).1 (abs_nonneg d)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem normal_mark_measurable (m : ℝ) (p : OSFourSpace) (u : UnitVector OSFourSpace) : Measurable (normalCoverMark m p u) :=
  (normal_cover_args_measurable normalCoverGamma5 m (p := fun _ : ℝ => p) measurable_const measurable_id).mul_const _

theorem normal_mark_transform {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (u : UnitVector OSFourSpace) (ξ : ℝ) :
    let F := fun d => normalAngularPhase ξ d • normalCoverMark m p u d
    Integrable F ∧ (∫ d, F d) = normalDiracFrequency m p ξ * diracSlash u.val := by
  let g := fun d => normalAngularPhase ξ d • normalDiracCover normalCoverGamma5 m p d
  have hg : Integrable g := (normal_cover_angular_fourier normalCoverGamma5 hm p ξ).1
  have he (d) : normalAngularPhase ξ d • normalCoverMark m p u d = g d * diracSlash u.val := (smul_mul_assoc _ _ _).symm
  dsimp only
  simp_rw [he]
  refine ⟨?_,?_⟩
  · exact ((ContinuousLinearMap.mul ℝ DiracMatrix).flip (diracSlash u.val)).integrable_comp hg
  · rw [integral_mul_const_of_integrable hg]
    exact congrArg (·*diracSlash u.val) (normal_frequency_is_cover_transform hm p ξ)

def normalConstrainedWord {n : ℕ} (m : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (D : ℝ) (x : Fin n → ℝ) : DiracMatrix :=
  normalOrderedWord (fun j => normalCoverMark m (p j) (u j) (normalOpenIncrements D x j))

theorem normal_constrained_measurable {n : ℕ} (m : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) : Measurable (fun z : ℝ × (Fin n → ℝ) => normalConstrainedWord m u p z.1 z.2) := by
  apply normal_ordered_measurable
  intro j
  apply (normal_mark_measurable _ _ _).comp
  refine Fin.cases ?_ (fun i => ?_) j
  · exact measurable_fst.sub (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd))
  · exact (measurable_pi_apply i).comp measurable_snd

theorem normal_constrained_bound {n : ℕ} {m : ℝ} (hm : 0 < m) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (D : ℝ) (x : Fin n → ℝ) :
    ‖normalConstrainedWord m u p D x‖ ≤ (2^(n+1)*Real.exp (-(m/2)*|D|))*∏ i, Real.exp (-(m/2)*|x i|) := by
  let A := fun j => normalCoverMark m (p j) (u j) (normalOpenIncrements D x j)
  change ‖(List.ofFn A).prod‖ ≤ _
  apply (List.norm_prod_le _).trans
  rw [List.map_ofFn,List.prod_ofFn]
  apply (Finset.prod_le_prod (fun j _ => norm_nonneg (A j)) (fun j _ => normal_mark_bound hm _ _ _)).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_sum,←Finset.mul_sum,mul_assoc]
  exact mul_le_mul_of_nonneg_left (normal_open_increment_envelope hm D x) (by positivity)

theorem normal_constrained_integrable {n : ℕ} {m : ℝ} (hm : 0 < m) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => normalConstrainedWord m u p z.1 z.2) := by
  have he := (normal_open_laplace_mass hm).1
  have h := (he.const_mul ((2:ℝ)^(n+1))).mul_prod (Integrable.fintype_prod (fun _ : Fin n => he))
  exact h.mono' (normal_constrained_measurable m u p).aestronglyMeasurable (Eventually.of_forall fun z => normal_constrained_bound hm u p z.1 z.2)

theorem normal_angular_phase_add (ξ d t : ℝ) : normalAngularPhase ξ (d+t) = normalAngularPhase ξ d * normalAngularPhase ξ t := by
  unfold normalAngularPhase
  rw [Complex.ofReal_add,mul_add,Complex.exp_add]

theorem normal_angular_phase_sum {n : ℕ} (ξ : ℝ) (x : Fin n → ℝ) :
    normalAngularPhase ξ (∑ j, x j) = ∏ j, normalAngularPhase ξ (x j) := by
  simp only [normalAngularPhase,Complex.ofReal_sum,Finset.mul_sum,Complex.exp_sum]

def normalCoverConvolution {n : ℕ} (m : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (D : ℝ) : DiracMatrix := ∫ x, normalConstrainedWord m u p D x

theorem normal_cover_convolution_transform {n : ℕ} {m : ℝ} (hm : 0 < m) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (ξ : ℝ) :
    (∫ D, normalAngularPhase ξ D • normalCoverConvolution m u p D) =
      normalOrderedWord (fun i => normalDiracFrequency m (p i) ξ * diracSlash (u i).val) := by
  let A := fun i => normalCoverMark m (p i) (u i)
  let B := fun i d => normalAngularPhase ξ d • A i d
  let tail := fun x : Fin n → ℝ => normalOrderedWord (fun i => A i.succ (x i))
  let btail := fun x : Fin n → ℝ => normalOrderedWord (fun i => B i.succ (x i))
  have hB (i) := normal_mark_transform hm (p i) (u i) ξ
  have hmB (i) : Measurable (B i) :=
    (show Continuous (normalAngularPhase ξ) by unfold normalAngularPhase; fun_prop).measurable.smul (normal_mark_measurable _ _ _)
  have hbI : Integrable btail := normal_ordered_integrable _ (fun i => hmB i.succ) (fun i => (hB i.succ).1)
  have hBt (x : Fin n → ℝ) : btail x = normalAngularPhase ξ (∑ j, x j) • tail x := by
    dsimp only [btail,B,tail]
    rw [normal_ordered_word_smul,normal_angular_phase_sum]
  let F := fun (D : ℝ) (x : Fin n → ℝ) => normalAngularPhase ξ D • normalConstrainedWord m u p D x
  have hFI : Integrable (Function.uncurry F) (volume.prod volume) := by
    apply (normal_constrained_integrable hm u p).norm.mono'
    · exact (((show Continuous (normalAngularPhase ξ) by unfold normalAngularPhase; fun_prop).measurable.comp measurable_fst).smul
        (normal_constrained_measurable m u p)).aestronglyMeasurable
    · exact Eventually.of_forall fun z => by simp only [Function.uncurry,F,norm_smul,normal_angular_phase_norm,one_mul,le_refl]
  have hinner (x : Fin n → ℝ) : (∫ D, F D x) = (∫ d, B 0 d)*btail x := by
    let S := ∑ i, x i
    rw [←integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun D => F D x) S]
    have he (d : ℝ) : F (d+S) x = B 0 d * btail x := by
      rw [hBt]
      dsimp only [F,normalConstrainedWord,normalOrderedWord]
      rw [List.ofFn_succ,List.prod_cons]
      change normalAngularPhase ξ (d+S) • (A 0 (d+S-S)*tail x) = (normalAngularPhase ξ d • A 0 d)*(normalAngularPhase ξ S • tail x)
      rw [add_sub_cancel_right,normal_angular_phase_add,smul_mul_smul]
    simp_rw [he]
    exact integral_mul_const_of_integrable (hB 0).1
  change (∫ D, normalAngularPhase ξ D • ∫ x, normalConstrainedWord m u p D x) = _
  simp_rw [←integral_smul]
  change (∫ D, ∫ x, F D x) = _
  rw [integral_integral_swap hFI]
  simp_rw [hinner]
  rw [integral_const_mul_of_integrable hbI]
  change (∫ d, B 0 d)*(∫ x : Fin n → ℝ, normalOrderedWord (fun i => B i.succ (x i))) = _
  rw [normal_ordered_integral _ (fun i => hmB i.succ) (fun i => (hB i.succ).1)]
  have hval (i) : (∫ d, B i d) = normalDiracFrequency m (p i) ξ*diracSlash (u i).val := (hB i).2
  simp_rw [hval]
  conv_rhs => rw [normalOrderedWord,List.ofFn_succ,List.prod_cons]
  rfl

end UV
