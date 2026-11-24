import UV.ContinueTwoBandFourier

/-! A fully marked spatial hop. Each photon has a polarized plane wave and
its own straight-segment integral. The Gaussian hop integral is absolutely
convergent before Fubini interchanges displacement and segment parameters. -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

namespace UV.SectorPlane

private theorem wave_add (k l z : Spatial) :
    twoBandDisplacementWave (k+l) z = twoBandDisplacementWave k z * twoBandDisplacementWave l z := by
  simp [twoBandDisplacementWave,inner_add_right,add_mul,Complex.exp_add]

private theorem wave_sum {ι : Type*} (s : Finset ι) (q : ι → Spatial) (z : Spatial) :
    twoBandDisplacementWave (∑ j ∈ s, q j) z = ∏ j ∈ s, twoBandDisplacementWave (q j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twoBandDisplacementWave]
  | insert i s hi ih => simp [hi,wave_add,ih]

/-- The linearized charged phase of one polarized spatial Fourier mode
on the segment from the origin to `z`, with common charge removed. -/
def twoBandLineMode (u : UnitVector Spatial) (q z : Spatial) : ℂ :=
  ∫ s : ℝ in Icc 0 1, Complex.I * (⟪z,u.val⟫ : ℝ) * twoBandDisplacementWave q (s • z)

/-- Repeated real source derivatives of the exponential link phase.
The directions are complexified Fourier modes, including the factor `I`
from the Wilson exponent. -/
def twoBandLinkVariations (A : List ℂ) (B : ℂ) : ℂ :=
  match A with
  | [] => Complex.exp B
  | a :: As => deriv (fun t : ℝ => twoBandLinkVariations As (B+(t:ℂ)*a)) 0

theorem twoBand_link_variations_eval (A : List ℂ) (B : ℂ) :
    twoBandLinkVariations A B = A.prod * Complex.exp B := by
  induction A generalizing B with
  | nil => simp [twoBandLinkVariations]
  | cons a As ih =>
    simp only [twoBandLinkVariations,ih,List.prod_cons]
    have hd := (((hasDerivAt_id (0:ℂ)).mul_const a).const_add B).cexp.comp_ofReal
    simpa [mul_comm,mul_left_comm,mul_assoc] using (hd.const_mul As.prod).deriv

def twoBandFourierLinkKernel (g σ : ℝ) {n : ℕ} (u : Fin n → UnitVector Spatial)
    (b : Spatial) (q : Fin n → Spatial) (k z : Spatial) : ℂ :=
  twoBandDisplacementWave (k+b) z * (g * twoBandDisplacementDensity σ z : ℂ) *
    twoBandLinkVariations (List.ofFn (fun j => twoBandLineMode (u j) (q j) z)) 0

private def fractionIntegrand (g σ : ℝ) {n : ℕ} (u : Fin n → UnitVector Spatial)
    (b : Spatial) (q : Fin n → Spatial) (k z : Spatial) (s : Fin n → ℝ) : ℂ :=
  twoBandDisplacementWave (k+(b+∑ j, s j • q j)) z *
    ((∏ j, Complex.I * (⟪z,(u j).val⟫ : ℝ)) * (g * twoBandDisplacementDensity σ z : ℂ))

private theorem line_mode_product (g σ : ℝ) {n : ℕ} (u : Fin n → UnitVector Spatial)
    (b : Spatial) (q : Fin n → Spatial) (k z : Spatial) :
    twoBandFourierLinkKernel g σ u b q k z =
      ∫ s, fractionIntegrand g σ u b q k z s ∂(twoBandPathFractions n) := by
  classical
  let A := fun (j : Fin n) (s : ℝ) =>
    Complex.I * (⟪z,(u j).val⟫ : ℝ) * twoBandDisplacementWave (q j) (s • z)
  have hA (j : Fin n) : twoBandLineMode (u j) (q j) z = ∫ s in Icc 0 1, A j s := rfl
  rw [twoBandFourierLinkKernel,twoBand_link_variations_eval,Complex.exp_zero,mul_one,List.prod_ofFn]
  simp_rw [hA]
  rw [← integral_fintype_prod_eq_prod,← integral_const_mul]
  congr 1
  funext s
  unfold fractionIntegrand
  rw [← add_assoc,wave_add (k+b) (∑ j, s j • q j) z,wave_sum]
  have hsym (j : Fin n) :
      twoBandDisplacementWave (q j) (s j • z) = twoBandDisplacementWave (s j • q j) z := by
    simp [twoBandDisplacementWave,real_inner_smul_left,real_inner_smul_right]
  simp only [A,Finset.prod_mul_distrib,hsym]
  ring

private theorem fraction_integrable (g : ℝ) {σ : ℝ} (hσ : 0 < σ) {n : ℕ}
    (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial) (k : Spatial) :
    Integrable (fun p : Spatial × (Fin n → ℝ) => fractionIntegrand g σ u b q k p.1 p.2)
      (volume.prod (twoBandPathFractions n)) := by
  have h := (twoBand_displacement_density_moment g hσ n).comp_fst (twoBandPathFractions n)
  refine h.mono' ?_ (ae_of_all _ fun p => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold fractionIntegrand twoBandDisplacementWave twoBandDisplacementDensity
    fun_prop
  · unfold fractionIntegrand
    rw [norm_mul,twoBand_displacement_wave_norm,one_mul,norm_mul,norm_prod]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∏ _ : Fin n, ‖p.1‖ := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => ?_)
        rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
        simpa [(u j).property] using abs_real_inner_le_norm p.1 (u j).val
      _ = _ := by simp

/-- The Fourier kernel of the actual mixed straight-link variation is
absolutely integrable in the displacement, at every external shift. -/
theorem twoBand_fourier_link_kernel_integrable (g : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {n : ℕ} (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial) (k : Spatial) :
    Integrable (twoBandFourierLinkKernel g σ u b q k) := by
  have h := (fraction_integrable g hσ u b q k).integral_prod_left
  exact h.congr (ae_of_all _ fun z => (line_mode_product g σ u b q k z).symm)

/-- The exact Fourier multiplier of all marks on one Wilson hop, with
common charge and translation phases removed. Each labeled mode retains
its own parameter and unit polarization. -/
theorem twoBand_fourier_link_eq_gaussian_wilson_mark (g : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {n : ℕ} (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial) (k : Spatial) :
    (∫ z, twoBandFourierLinkKernel g σ u b q k z) = (twoBandGaussianWilsonMark g σ u b q k : ℂ) := by
  simp_rw [line_mode_product g σ u b q k]
  rw [integral_integral_swap (f := fractionIntegrand g σ u b q k) (fraction_integrable g hσ u b q k)]
  unfold fractionIntegrand twoBandGaussianWilsonMark twoBandGaussianMarkAverage
  simp_rw [twoBand_displacement_fourier_derivative g hσ u]
  exact integral_ofReal

end UV.SectorPlane
