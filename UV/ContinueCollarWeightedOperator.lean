import UV.ContinueCollarEigenTrace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Construct the bounded, Hilbert–Schmidt weighted collar from its
columns and identify multiplication by the unbounded determinant on
every input using closedness of the L² multiplication graph. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace UV.CollarEigenmode

variable {ι H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem bounded_operator_of_sq_columns (b : HilbertBasis ι ℂ H) (col : ι → G) (hs : Summable (fun i => ‖col i‖^2)) :
    ∃ A : H →L[ℂ] G,(∀ i,A (b i) = col i) ∧ ‖A‖^2 ≤ ∑' i,‖col i‖^2 := by
  classical
  let g : ℓ²(ι,ℂ) := ⟨fun i => (‖col i‖:ℂ),memℓp_gen (by simpa [Complex.norm_real,Real.norm_of_nonneg] using hs)⟩
  have hg (i) : ‖g i‖ = ‖col i‖ := by simp [g]
  have hhold (x : H) := lp.tsum_mul_le_mul_norm (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num) (b.repr x) g
  have hN (x : H) : Summable (fun i => ‖b.repr x i • col i‖) := by simpa only [norm_smul,hg] using (hhold x).1
  have h (x : H) := (hN x).of_norm
  let L : H →ₗ[ℂ] G := {
    toFun := fun x => ∑' i,b.repr x i • col i
    map_add' := fun x y => by simpa only [map_add,lp.coeFn_add,Pi.add_apply,add_smul] using (h x).tsum_add (h y)
    map_smul' := fun c x => by simpa only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul,RingHom.id_apply] using (h x).tsum_const_smul c }
  have hbound (x : H) : ‖L x‖ ≤ ‖g‖*‖x‖ := by
    apply (norm_tsum_le_tsum_norm (hN x)).trans
    simpa only [norm_smul,hg,b.repr.norm_map,mul_comm ‖g‖] using (hhold x).2
  let A := L.mkContinuous ‖g‖ hbound
  refine ⟨A,fun i => ?_,?_⟩
  · change ∑' j,b.repr (b i) j • col j = col i
    rw [b.repr_self,tsum_eq_single i]
    · simp [lp.single_apply]
    · intro j hji; simp [lp.single_apply,Pi.single_eq_of_ne hji]
  · have hA : ‖A‖ ≤ ‖g‖ := L.mkContinuous_norm_le (norm_nonneg g) hbound
    have hsum := (lp.hasSum_norm (p := 2) (by norm_num) g).tsum_eq
    norm_num [hg] at hsum
    exact (pow_le_pow_left₀ (norm_nonneg A) hA 2).trans_eq hsum.symm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_graph_closed (A T : H →L[ℂ] Lp ℂ 2 μ) (f : X → ℂ) :
    IsClosed {x : H | ∀ᵐ r ∂μ,A x r = f r*T x r} := by
  apply IsSeqClosed.isClosed
  intro u x hu hx
  obtain ⟨s,hs,hA⟩ := (tendstoInMeasure_of_tendsto_Lp (A.continuous.continuousAt.tendsto.comp hx)).exists_seq_tendsto_ae
  obtain ⟨j,hj,hT⟩ := (tendstoInMeasure_of_tendsto_Lp (T.continuous.continuousAt.tendsto.comp (hx.comp hs.tendsto_atTop))).exists_seq_tendsto_ae
  have he : ∀ᵐ r ∂μ, ∀ n : ℕ,A (u (s (j n))) r = f r*T (u (s (j n))) r := ae_all_iff.mpr fun n => hu (s (j n))
  filter_upwards [hA,hT,he] with r h₁ h₂ h₃
  exact tendsto_nhds_unique (h₁.comp hj.tendsto_atTop) ((h₂.const_mul (f r)).congr' (Eventually.of_forall fun n => (h₃ n).symm))

theorem weighted_operator_from_columns (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] Lp ℂ 2 μ) (f : X → ℂ) (col : ι → Lp ℂ 2 μ)
    (hm : ∀ i,∀ᵐ r ∂μ,col i r = f r*T (b i) r) (hs : Summable (fun i => ‖col i‖^2)) :
    ∃ A : H →L[ℂ] Lp ℂ 2 μ,(∀ x,∀ᵐ r ∂μ,A x r = f r*T x r) ∧
      (∀ i,A (b i)=col i) ∧ ‖A‖^2 ≤ ∑' i,‖col i‖^2 := by
  obtain ⟨A,hA,hN⟩ := bounded_operator_of_sq_columns b col hs
  let M : Submodule ℂ H := {
    carrier := {x : H | ∀ᵐ r ∂μ,A x r = f r*T x r}
    zero_mem' := by change ∀ᵐ r ∂μ,A 0 r = f r*T 0 r; simp only [map_zero]; filter_upwards [Lp.coeFn_zero ℂ 2 μ] with r hr; rw [hr]; simp
    add_mem' := fun {x y} hx hy => by
      change ∀ᵐ r ∂μ,A (x+y) r = f r*T (x+y) r
      simp only [map_add]
      filter_upwards [Lp.coeFn_add (A _) (A _),Lp.coeFn_add (T _) (T _),hx,hy] with r ha ht h₁ h₂
      rw [ha,ht,Pi.add_apply,Pi.add_apply,h₁,h₂,mul_add]
    smul_mem' := fun c x hx => by
      change ∀ᵐ r ∂μ,A (c • x) r = f r*T (c • x) r
      simp only [map_smul]
      filter_upwards [Lp.coeFn_smul c (A x),Lp.coeFn_smul c (T x),hx] with r ha ht h₁
      rw [ha,ht,Pi.smul_apply,Pi.smul_apply,h₁,smul_eq_mul,smul_eq_mul]; ring }
  have hin : Submodule.span ℂ (range b) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change ∀ᵐ r ∂μ,A (b i) r = f r*T (b i) r
    rw [hA]; exact hm i
  have hM : IsClosed (M : Set H) := weighted_graph_closed A T f
  have hall := (Submodule.span ℂ (range b)).topologicalClosure_minimal hin hM
  rw [b.dense_span] at hall
  exact ⟨A,fun x => hall (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H)),hA,hN⟩

end UV.CollarEigenmode
