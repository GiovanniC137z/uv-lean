import UV.ContinueTwoBandFourierKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Diagonal operator trace in terms of a genuinely closed position-space
path. All kernel pairings are ordinary product-measure integrals. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ComplexInnerProductSpace

namespace UV.SectorPlane.SlabKernel

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def transposeConj (K : Bounded X) : Bounded X where
  val x y := conj (K.val y x)
  measurable := Complex.continuous_conj.measurable.comp (K.measurable.comp measurable_swap)
  bound := K.bound
  nonneg := K.nonneg
  bounded x y := by simpa using K.bounded y x

private theorem form_integrable (K : Bounded X) (f g : Lp ℂ 2 μ) :
    Integrable (fun p : X × X => (K.val p.1 p.2 * g p.2) * conj (f p.1)) (μ.prod μ) := by
  have hf := ((Lp.memLp f).integrable (by norm_num)).norm
  have hg := ((Lp.memLp g).integrable (by norm_num)).norm
  apply ((hf.mul_prod hg).const_mul K.bound).mono'
  · exact ((K.measurable.mul ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable f).measurable.comp measurable_fst))).aestronglyMeasurable
  · exact ae_of_all _ fun p => by
      simp only [norm_mul,Complex.norm_conj]
      change (‖K.val p.1 p.2‖*‖g p.2‖)*‖f p.1‖ ≤ K.bound*(‖f p.1‖*‖g p.2‖)
      calc
        _ ≤ (K.bound*‖g p.2‖)*‖f p.1‖ := by gcongr; exact K.bounded _ _
        _ = _ := by ring

theorem operator_transpose_pair (K : Bounded X) (f g : Lp ℂ 2 μ) :
    ⟪f,operator μ K g⟫ = ⟪operator μ (transposeConj K) f,g⟫ := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ x, ∫ y, (K.val x y * g y) * conj (f x) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [operator_coe μ K g] with x hx
      rw [RCLike.inner_apply,hx,integral_mul_const]
    _ = ∫ y, ∫ x, (K.val x y * g y) * conj (f x) ∂μ ∂μ := integral_integral_swap (form_integrable μ K f g)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [operator_coe μ (transposeConj K) f] with y hy
      rw [RCLike.inner_apply,hy,←integral_conj,←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [transposeConj,mul_assoc,mul_left_comm]

omit [IsFiniteMeasure μ] in
private theorem norm_sq_as_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [← norm_sq_eq_re_inner] using h

/-- No projection is identified with a delta: the two kernels are sewn
through a complete orthonormal basis using Parseval and absolute integral
summability. -/
theorem trace_pair {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (K L : Bounded X) :
    HasSum (fun i => ⟪b i,operator μ K (operator μ L (b i))⟫)
      (∫ x, ∫ y, L.val x y * K.val y x ∂μ ∂μ) := by
  let F := fun i => operator μ (transposeConj K) (b i)
  let G := fun i => operator μ L (b i)
  let φ := fun i x => inner ℂ (F i x) (G i x)
  have hI (i : ι) : Integrable (φ i) μ := L2.integrable_inner (𝕜 := ℂ) (F i) (G i)
  have hF := operator_square_columns μ (transposeConj K) b
  have hG := operator_square_columns μ L b
  have hs : Summable (fun i => ∫ x, ‖φ i x‖ ∂μ) := by
    apply ((hF.add hG).mul_left (1/2:ℝ)).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    change _ ≤ (1/2)*(‖F i‖^2+‖G i‖^2)
    rw [norm_sq_as_integral μ (F i),norm_sq_as_integral μ (G i),←integral_add
      ((Lp.memLp _).integrable_norm_pow (p := 2) (by norm_num)) ((Lp.memLp _).integrable_norm_pow (p := 2) (by norm_num)),
      ← integral_const_mul]
    apply integral_mono (hI i).norm ((((Lp.memLp (F i)).integrable_norm_pow (p := 2) (by norm_num)).add
      ((Lp.memLp (G i)).integrable_norm_pow (p := 2) (by norm_num))).const_mul _)
    intro x
    simp only [φ,RCLike.inner_apply,norm_mul,Complex.norm_conj,Pi.add_apply]
    nlinarith only [sq_nonneg (‖F i x‖-‖G i x‖)]
  have hp := hasSum_integral_of_summable_integral_norm hI hs
  have hPoint : ∀ᵐ x ∂μ, ∀ i, F i x = ⟪row μ (transposeConj K) x,b i⟫ ∧
      G i x = ⟪row μ L x,b i⟫ := ae_all_iff.mpr (fun i =>
    (operator_pair_ae μ (transposeConj K) (b i)).and (operator_pair_ae μ L (b i)))
  have he : (∫ x, ∑' i, φ i x ∂μ) = ∫ x, ∫ y, L.val x y * K.val y x ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hPoint] with x hx
    have hφ (i) : φ i x = ⟪row μ L x,b i⟫ * ⟪b i,row μ (transposeConj K) x⟫ := by
      dsimp [φ]
      rw [(hx i).1,(hx i).2]
      exact congrArg (_ * ·) (inner_conj_symm (𝕜 := ℂ) (b i) (row μ (transposeConj K) x))
    simp only [hφ]
    rw [b.tsum_inner_mul_inner,row_pair]
    apply integral_congr_ae
    filter_upwards [row_coe μ (transposeConj K) x] with y hy
    rw [hy]
    simp [transposeConj]
  rw [← he]
  apply hp.congr_fun
  intro i
  rw [operator_transpose_pair μ K]
  exact L2.inner_def (𝕜 := ℂ) (F i) (G i)

end UV.SectorPlane.SlabKernel
