import UV.ContinueTwoBandFourierTrace
import UV.ContinueTwoBandFourierOperator

/-! Every power of the two-band Schur product traces to the closed chain
of its actual time-directed, spatially periodized kernels. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexInnerProductSpace

namespace UV.SectorPlane.SlabKernel

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Integrate out the intermediate position and carrier time. -/
def sew (K L : Bounded X) : Bounded X where
  val x y := ∫ z, K.val x z * L.val z y ∂μ
  measurable := ((K.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
    (L.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable.integral_prod_right'.measurable
  bound := (K.bound*L.bound)*μ.real Set.univ
  nonneg := mul_nonneg (mul_nonneg K.nonneg L.nonneg) (measureReal_nonneg)
  bounded x y := by
    apply norm_integral_le_of_norm_le_const
    exact ae_of_all _ fun z => (norm_mul_le _ _).trans (mul_le_mul (K.bounded x z) (L.bounded z y) (norm_nonneg _) K.nonneg)

theorem sew_operator (K L : Bounded X) :
    operator μ (sew μ K L) = operator μ K * operator μ L := by
  ext f : 1
  apply Lp.ext
  filter_upwards [operator_coe μ (sew μ K L) f, operator_coe μ K (operator μ L f)] with x hx hright
  change operator μ (sew μ K L) f x = operator μ K (operator μ L f) x
  rw [hx,hright]
  have hi : Integrable (fun p : X × X => (K.val x p.2 * L.val p.2 p.1) * f p.1) (μ.prod μ) := by
    have hf := (((Lp.memLp f).integrable (by norm_num)).norm.comp_fst μ).const_mul (K.bound*L.bound)
    apply hf.mono'
    · exact (((K.measurable.comp (measurable_const.prodMk measurable_snd)).mul (L.measurable.comp measurable_swap)).mul
          ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)).aestronglyMeasurable
    · exact ae_of_all _ fun p => by
        rw [norm_mul,norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (K.bounded _ _) (L.bounded _ _) (norm_nonneg _) K.nonneg) (norm_nonneg _)
  calc
    _ = ∫ y, ∫ z, (K.val x z * L.val z y) * f y ∂μ ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => (integral_mul_const _ _).symm
    _ = ∫ z, ∫ y, (K.val x z * L.val z y) * f y ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [operator_coe μ L f] with z hz
      rw [hz,←integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun _ => mul_assoc _ _ _)

/-- An alternating open chain with one more upper than lower block. -/
def oddChain (P N : Bounded X) : ℕ → Bounded X
  | 0 => P
  | n+1 => sew μ P (sew μ N (oddChain P N n))

theorem odd_chain_operator (P N : Bounded X) (n : ℕ) :
    operator μ (oddChain μ P N n) = operator μ P*(operator μ N*operator μ P)^n := by
  induction n with
  | zero => simp [oddChain]
  | succ n ih => simp [oddChain,sew_operator,ih,pow_succ',mul_assoc]

theorem trace_alternating_cycles {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (P N : Bounded X) (n : ℕ) :
    HasSum (fun i => ⟪b i,((operator μ N*operator μ P)^(n+1)) (b i)⟫)
      (∫ x, ∫ y, (oddChain μ P N n).val x y * N.val y x ∂μ ∂μ) := by
  have h := trace_pair μ b N (oddChain μ P N n)
  apply h.congr_fun
  intro i
  rw [odd_chain_operator,pow_succ']
  rfl

end UV.SectorPlane.SlabKernel
