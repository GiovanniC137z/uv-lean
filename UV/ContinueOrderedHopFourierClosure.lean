import UV.ContinueOrderedHopVolume
import UV.ContinueTwoBandFourierLink
import Mathlib.Analysis.Fourier.Inversion

/-! Angular-frequency Fourier inversion of the closed displacement
convolution. Only its first factor needs the indicated almost-everywhere
continuity on the return slice. This allows genuinely one-sided onsite
kernels with a jump at zero. -/

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology FourierTransform

namespace UV.SectorPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] {n : ℕ}

def orderedHopWave (p x : V) : ℂ := Complex.exp ((⟪x,p⟫:ℝ)*Complex.I)
def orderedHopFourier (f : V → ℂ) (p : V) : ℂ := ∫ x, orderedHopWave p x * f x

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem orderedHop_wave_norm (p x : V) : ‖orderedHopWave p x‖ = 1 := by
  simp [orderedHopWave,Complex.norm_exp]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
private theorem wave_add (p x y : V) : orderedHopWave p (x+y) = orderedHopWave p x * orderedHopWave p y := by
  simp [orderedHopWave,inner_add_left,add_mul,Complex.exp_add]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
private theorem wave_sum (p : V) (d : Fin n → V) : orderedHopWave p (∑ j, d j) = ∏ j, orderedHopWave p (d j) := by
  classical
  generalize (Finset.univ : Finset (Fin n)) = s
  induction s using Finset.induction_on with
  | empty => simp [orderedHopWave]
  | insert j s hj ih => simp only [Finset.prod_insert hj,Finset.sum_insert hj,wave_add,ih]

def orderedHopClosure (head : V → ℂ) (tail : Fin n → V → ℂ) (D : V) : ℂ :=
  ∫ z : Fin n → V, head (D-∑ j, z j) * ∏ j, tail j (z j)

private theorem closure_measurable {f : V → ℂ} {h : Fin n → V → ℂ}
    (hf : Measurable f) (hh : ∀ j, Measurable (h j)) :
    Measurable (fun Dz : V × (Fin n → V) => f (Dz.1-∑ j, Dz.2 j) * ∏ j, h j (Dz.2 j)) := by
  exact (hf.comp (measurable_fst.sub (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd))).mul
    (Finset.measurable_prod _ fun j _ => (hh j).comp ((measurable_pi_apply j).comp measurable_snd))

private theorem closure_joint_integrable {f : V → ℂ} {h : Fin n → V → ℂ}
    (hf : Measurable f) (hh : ∀ j, Measurable (h j)) (hI : Integrable f) (ht : ∀ j, Integrable (h j)) :
    Integrable (fun Dz : V × (Fin n → V) => f (Dz.1-∑ j, Dz.2 j) * ∏ j, h j (Dz.2 j)) (volume.prod volume) := by
  apply (integrable_prod_iff' (closure_measurable hf hh).aestronglyMeasurable).mpr
  have htr (z : Fin n → V) : Integrable (fun D => f (D-∑ j, z j)) := by
    simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-(∑ j, z j))).integrable_comp_of_integrable hI
  refine ⟨Eventually.of_forall (fun z => (htr z).mul_const (∏ j, h j (z j))),?_⟩
  have he (z : Fin n → V) : (∫ D, ‖f (D - ∑ j, z j) * ∏ j, h j (z j)‖) = (∫ D, ‖f D‖)* ∏ j, ‖h j (z j)‖ := by
    simp_rw [norm_mul,norm_prod,sub_eq_add_neg]
    rw [integral_mul_const,integral_add_right_eq_self (μ := (volume : Measure V)) (fun x => ‖f x‖) (-(∑ j, z j))]
  simp_rw [he]
  exact (Integrable.fintype_prod (fun j => (ht j).norm)).const_mul _

theorem orderedHop_closure_transform {f : V → ℂ} {h : Fin n → V → ℂ}
    (hf : Measurable f) (hh : ∀ j, Measurable (h j)) (hI : Integrable f) (ht : ∀ j, Integrable (h j)) (p : V) :
    orderedHopFourier (orderedHopClosure f h) p = orderedHopFourier f p * ∏ j, orderedHopFourier (h j) p := by
  let X := fun (D : V) (z : Fin n → V) => orderedHopWave p D * (f (D-∑ j, z j)*∏ j, h j (z j))
  have hJ := closure_joint_integrable hf hh hI ht
  have hXI : Integrable (Function.uncurry X) (volume.prod volume) := by
    apply hJ.norm.mono' (((show Continuous (orderedHopWave p) by unfold orderedHopWave; fun_prop).comp continuous_fst).aestronglyMeasurable.mul hJ.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖orderedHopWave p x.1 * _‖ ≤ _
      rw [norm_mul,orderedHop_wave_norm,one_mul]
  have hrow (z : Fin n → V) : (∫ D, X D z) = orderedHopFourier f p * ∏ j, (orderedHopWave p (z j)*h j (z j)) := by
    let s := ∑ j, z j
    rw [← integral_add_right_eq_self (μ := (volume : Measure V)) (fun D => X D z) s]
    have he (x : V) : X (x+s) z = (orderedHopWave p x*f x) * ∏ j, (orderedHopWave p (z j)*h j (z j)) := by
      dsimp only [X,s]
      rw [add_sub_cancel_right,wave_add,wave_sum,Finset.prod_mul_distrib]; ring
    simp_rw [he]
    exact integral_mul_const _ _
  change (∫ D, orderedHopWave p D*(∫ z : Fin n → V, f (D-∑ j, z j)*∏ j, h j (z j))) = _
  simp_rw [← integral_const_mul]
  change (∫ D, ∫ z, X D z) = _
  rw [integral_integral_swap hXI]; simp_rw [hrow]
  rw [integral_const_mul,integral_fintype_prod_volume_eq_prod (fun j x => orderedHopWave p x*h j x)]
  rfl

theorem orderedHop_closure_continuousAt {f : V → ℂ} {h : Fin n → V → ℂ}
    (hf : Measurable f) (hh : ∀ j, Measurable (h j)) (ht : ∀ j, Integrable (h j))
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (D : V) (hc : ∀ᵐ z : Fin n → V, ContinuousAt f (D-∑ j, z j)) :
    ContinuousAt (orderedHopClosure f h) D := by
  have hBound (z : Fin n → V) (s : V) :
      ‖f (s-∑ j, z j)*∏ j, h j (z j)‖ ≤ B * ∏ j, ‖h j (z j)‖ := by
    rw [norm_mul,norm_prod]; exact mul_le_mul_of_nonneg_right (hB _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  let X := fun (s : V) (z : Fin n → V) => f (s-∑ j, z j) * ∏ j, h j (z j)
  have hm (s : V) : Measurable (X s) :=
    (hf.comp (measurable_const.sub (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))).mul
      (Finset.measurable_prod _ fun j _ => (hh j).comp (measurable_pi_apply j))
  have hi : Integrable (fun z : Fin n → V => B * ∏ j, ‖h j (z j)‖) :=
    (Integrable.fintype_prod (fun j => (ht j).norm)).const_mul B
  change Tendsto (fun s => ∫ z, X s z) (𝓝 D) (𝓝 (∫ z, X D z))
  apply tendsto_integral_filter_of_dominated_convergence (F := X) (f := X D) _
    (Eventually.of_forall fun s => (hm s).aestronglyMeasurable)
    (Eventually.of_forall fun s => Eventually.of_forall fun z => hBound z s) hi
  filter_upwards [hc] with z hz
  have hsub : ContinuousAt (fun s : V => s-∑ j, z j) D := continuousAt_id.sub continuousAt_const
  exact (hz.tendsto.comp hsub.tendsto).mul_const _

/-- If the product of the transformed factors is integrable, invert the
actual constrained convolution at zero with the (2π)^(-dim V) normalization. -/
theorem orderedHop_fourier_return {f : V → ℂ} {h : Fin n → V → ℂ}
    (hf : Measurable f) (hh : ∀ j, Measurable (h j)) (hI : Integrable f) (ht : ∀ j, Integrable (h j))
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (hc : ∀ᵐ z : Fin n → V, ContinuousAt f (-(∑ j, z j)))
    (hF : Integrable (fun p => orderedHopFourier f p * ∏ j, orderedHopFourier (h j) p)) :
    ((2*Real.pi)^(Module.finrank ℝ V))⁻¹ • (∫ p, orderedHopFourier f p * ∏ j, orderedHopFourier (h j) p) =
      orderedHopClosure f h 0 := by
  let C := orderedHopClosure f h
  let F := fun p => orderedHopFourier f p * ∏ j, orderedHopFourier (h j) p
  have hπ : (-(2*Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have he (p : V) : 𝓕 C p = F ((-(2*Real.pi)) • p) := by
    dsimp only [F,C]
    rw [←orderedHop_closure_transform hf hh hI ht,Real.fourierIntegral_eq',orderedHopFourier]
    congr 1
    funext x
    simp only [orderedHopWave,real_inner_smul_right,real_inner_comm p x,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_neg]
    congr 2
    ring
  have hiC : Integrable C := (closure_joint_integrable hf hh hI ht).integral_prod_left
  have hcC : ContinuousAt C 0 := orderedHop_closure_continuousAt hf hh ht hB _ (by simpa only [zero_sub] using hc)
  have hiF : Integrable (𝓕 C) := by
    rw [show 𝓕 C = _ from funext he]
    exact (integrable_comp_smul_iff volume F hπ).mpr hF
  have h := hiC.fourier_inversion hiF hcC
  rw [Real.fourierIntegralInv_eq'] at h
  simp only [inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul,he] at h
  rw [Measure.integral_comp_smul volume F (-(2*Real.pi))] at h
  simpa only [abs_inv,abs_pow,abs_neg,abs_of_pos (show 0 < 2*Real.pi by positivity)] using h

end UV.SectorPlane
