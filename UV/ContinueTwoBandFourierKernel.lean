import UV.ContinueTwoBandFourier
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-! Integral operators for the two actual gauged slab kernels.
Bessel's inequality proves square summability of the columns in any
Hilbert basis of the complex slab L² space. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ComplexInnerProductSpace

namespace UV.SectorPlane.SlabKernel

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

structure Bounded (X : Type*) [MeasurableSpace X] where
  val : X → X → ℂ
  measurable : Measurable (fun p : X × X => val p.1 p.2)
  bound : ℝ
  nonneg : 0 ≤ bound
  bounded : ∀ x y, ‖val x y‖ ≤ bound

variable (K : Bounded X)

private def one : Lp ℂ 2 μ := (memLp_const (μ := μ) (p := 2) (1:ℂ)).toLp _

private theorem one_coe : ∀ᵐ y ∂μ, one μ y = 1 := MemLp.coeFn_toLp _

private theorem row_mem (x : X) : MemLp (fun y => conj (K.val x y)) 2 μ :=
  MemLp.of_bound (Complex.continuous_conj.measurable.comp
    (K.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable K.bound
    (ae_of_all _ fun y => by simpa using K.bounded x y)

def row (x : X) : Lp ℂ 2 μ := (row_mem μ K x).toLp _

theorem row_coe (x : X) : ∀ᵐ y ∂μ, row μ K x y = conj (K.val x y) := (row_mem μ K x).coeFn_toLp

private theorem row_bound (x : X) : ‖row μ K x‖ ≤ K.bound * ‖one μ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [row_coe μ K x,one_coe μ] with y hy h1
  simpa [hy,h1] using K.bounded x y

theorem row_pair (x : X) (f : Lp ℂ 2 μ) :
    ⟪row μ K x,f⟫ = ∫ y, K.val x y * f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [row_coe μ K x] with y hy
  simp [hy,RCLike.inner_apply,mul_comm]

private theorem output_mem (f : Lp ℂ 2 μ) :
    MemLp (fun x => ⟪row μ K x,f⟫) 2 μ := by
  refine MemLp.of_bound ?_ (K.bound*‖one μ‖*‖f‖) ?_
  · simp_rw [row_pair]
    exact (K.measurable.mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · exact ae_of_all _ fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (row_bound μ K x) (norm_nonneg _))

private def linear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (output_mem μ K f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(output_mem μ K (f+g)).coeFn_toLp,Lp.coeFn_add ((output_mem μ K f).toLp _) ((output_mem μ K g).toLp _),
      (output_mem μ K f).coeFn_toLp,(output_mem μ K g).coeFn_toLp] with x hx ha hf hg
    rw [hx,ha,Pi.add_apply,hf,hg,inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(output_mem μ K (c • f)).coeFn_toLp,Lp.coeFn_smul c ((output_mem μ K f).toLp _),
      (output_mem μ K f).coeFn_toLp] with x hx ha hf
    rw [RingHom.id_apply,hx,ha,Pi.smul_apply,hf,inner_smul_right,smul_eq_mul]

def operator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linear μ K).mkContinuous (K.bound*‖one μ‖^2) (fun f => by
    have h : ‖linear μ K f‖ ≤ (K.bound*‖one μ‖*‖f‖)*‖one μ‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(output_mem μ K f).coeFn_toLp,one_coe μ] with x hx h1
      change ‖((output_mem μ K f).toLp _) x‖ ≤ _
      rw [hx,h1,norm_one,mul_one]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (row_bound μ K x) (norm_nonneg _))
    convert h using 1; ring)

theorem operator_coe (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, operator μ K f x = ∫ y, K.val x y * f y ∂μ :=
  (output_mem μ K f).coeFn_toLp.mono fun x hx => hx.trans (row_pair μ K x f)

theorem operator_pair_ae (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, operator μ K f x = ⟪row μ K x,f⟫ := (output_mem μ K f).coeFn_toLp

theorem operator_square_columns {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    Summable (fun i => ‖operator μ K (b i)‖^2) := by
  let G := fun i => operator μ K (b i)
  have hnorm (i : ι) : ‖G i‖^2 = ∫ x, ‖G i x‖^2 ∂μ := by
    have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) (G i) (G i))
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)] at h
    simpa only [← norm_sq_eq_re_inner] using h
  apply summable_of_sum_le (c := ∫ _ : X,(K.bound*‖one μ‖)^2 ∂μ) (fun _ => sq_nonneg _)
  intro S
  simp_rw [show ∀ i, ‖operator μ K (b i)‖^2 = ∫ x, ‖G i x‖^2 ∂μ from hnorm]
  rw [← integral_finset_sum _ fun i _ => (Lp.memLp (G i)).integrable_norm_pow (p := 2) (by norm_num)]
  apply integral_mono_ae (integrable_finset_sum _ (fun i _ => (Lp.memLp (G i)).integrable_norm_pow (p := 2) (by norm_num))) (integrable_const _)
  have hform : ∀ᵐ x ∂μ, ∀ i ∈ S, G i x = ⟪row μ K x,b i⟫ := by
    apply (eventually_all_finset S).mpr
    intro i _
    exact (output_mem μ K (b i)).coeFn_toLp
  filter_upwards [hform] with x hx
  have he (i : ι) (hi : i ∈ S) : ‖G i x‖^2 = ‖⟪b i,row μ K x⟫‖^2 := by rw [hx i hi,norm_inner_symm]
  rw [Finset.sum_congr rfl he]
  exact (b.orthonormal.sum_inner_products_le (s := S) (row μ K x)).trans
    (pow_le_pow_left₀ (norm_nonneg _) (row_bound μ K x) 2)

end UV.SectorPlane.SlabKernel
