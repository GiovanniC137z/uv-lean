import UV.ContinueTwoBandFourierCycles
import UV.ContinueTwoBandSlabFredholm
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! The finite-section determinant has an absolutely convergent logarithm in
the closed, signed position-space cycles of the periodized Wilson kernels. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexInnerProductSpace Matrix.Norms.L2Operator

namespace UV.SectorPlane

private theorem basis_countable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] {I : Type*} (b : HilbertBasis I ℂ H) : Countable I := by
  classical
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1/3:ℝ)) (Metric.ball (b j) (1/3:ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have h := norm_inner_le_norm (𝕜 := ℂ) (b i) (b i-b j)
    simp [inner_sub_right, orthonormal_iff_ite.mp b.orthonormal, hij, b.orthonormal.norm_eq_one] at h
    linarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.mpr (by norm_num))

theorem schur_cycle_position {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {I : Type*} [Countable I] (b : HilbertBasis I ℂ (Lp ℂ 2 μ)) (P N : SlabKernel.Bounded X) (n : ℕ) :
    schurCycleTrace b (SlabKernel.operator μ N) (SlabKernel.operator μ P) n =
      ∫ x, ∫ y, (SlabKernel.oddChain μ P N n).val x y * N.val y x ∂μ ∂μ := by
  let A := SlabKernel.operator μ N
  let B := SlabKernel.operator μ P
  have hcomm (k : ℕ) : (B*A)^k*B = B*(A*B)^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',pow_succ',mul_assoc,ih]; simp only [mul_assoc]
  have e : A*((B*A)^n*B) = (A*B)^(n+1) := by rw [hcomm,pow_succ',mul_assoc]
  change (∑' i, inner ℂ (A.adjoint (b i)) (((B*A)^n) (B (b i)))) = _
  rw [← (SlabKernel.trace_alternating_cycles μ b P N n).tsum_eq]
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact congrArg (fun F : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => inner ℂ (b i) (F (b i))) e

/-- A trace word with n+1 upper and n+1 lower propagations on the true slab. -/
def twoBandSlabClosedCycle (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) (n : ℕ) : ℂ :=
  let μ := twoBandSlabMeasure T L₁ L₂ L₃
  let P := twoBandBoundedSlabHop true hA hφ hm q g hσ h₁ h₂ h₃
  let N := twoBandBoundedSlabHop false hA hφ hm q g hσ h₁ h₂ h₃
  ∫ x, ∫ y, (SlabKernel.oddChain μ P N n).val x y * N.val y x ∂μ ∂μ

theorem twoBand_slab_determinant_position_cycles (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m g : ℝ} (hg : |g| < m) (q : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    {I : Type*} [DecidableEq I] (b : HilbertBasis I ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃))) :
    let hm := (abs_nonneg g).trans hg.le
    let U := twoBandSlabOperator true T hA hφ hm q g hσ h₁ h₂ h₃
    let V := twoBandSlabOperator false T hA hφ hm q g hσ h₁ h₂ h₃
    let C := fun n : ℕ => twoBandSlabClosedCycle T hA hφ hm q g hσ h₁ h₂ h₃ n / (n+1)
    Summable (fun n => ‖C n‖) ∧
      Tendsto (fun s : Finset I => (1-schurSection b s V * schurSection b s U).det)
        atTop (𝓝 (Complex.exp (-(∑' n, C n)))) := by
  intro hm U V C
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : MeasurableSpace.CountablyGenerated TwoBandPoint := by infer_instance
  letI : IsSeparable (twoBandSlabMeasure T L₁ L₂ L₃) := isSeparable_of_sigmaFinite _
  letI := basis_countable b
  have h (n : ℕ) : schurCycleTrace b V U n = twoBandSlabClosedCycle T hA hφ hm q g hσ h₁ h₂ h₃ n :=
    schur_cycle_position _ b _ _ n
  have he := twoBand_slab_determinant_trace_series T hA hφ hg q hσ h₁ h₂ h₃ b
  change Summable (fun n : ℕ => ‖schurCycleTrace b V U n / (n+1)‖) ∧
    Tendsto (fun s : Finset I => (1-schurSection b s V * schurSection b s U).det)
      atTop (𝓝 (Complex.exp (-(∑' n : ℕ, schurCycleTrace b V U n / (n+1))))) at he
  simpa only [C,h] using he

end UV.SectorPlane
