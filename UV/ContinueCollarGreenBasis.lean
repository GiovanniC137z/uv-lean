import UV.ContinueCollarGreenOperator
import UV.ContinueCollarHilbertSchmidtCompact

/-! The integral operator of the singular radial Green kernel is
Hilbert–Schmidt, compact, and diagonalizable in a real Hilbert basis. -/

noncomputable section

open MeasureTheory Real
open UV.ContinueCollarHSIdentity (radialMeasure)
open scoped InnerProductSpace

namespace UV.CollarEigenmode

private instance : IsFiniteMeasure radialMeasure := ⟨by simp [radialMeasure,Real.volume_Ioc]⟩

theorem greenOperator_square_columns {ι : Type*} (b : HilbertBasis ι ℝ RealRadialL2)
    {c : ℝ} (hc : 0<c) : Summable (fun i => ‖greenOperator hc (b i)‖^2) := by
  obtain ⟨B,hB,hbound⟩ := greenRow_uniform hc
  let g (i : ι) := greenOperator hc (b i)
  have hnorm (i : ι) : ‖g i‖^2=∫ r,‖g i r‖^2 ∂radialMeasure := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  apply summable_of_sum_le (c := ∫ _ : ℝ,B^2 ∂radialMeasure) (fun _ => sq_nonneg _)
  intro s
  simp_rw [show ∀ i,‖greenOperator hc (b i)‖^2 = ∫ r,‖g i r‖^2 ∂radialMeasure from hnorm]
  rw [← integral_finset_sum _ (fun i _ => (Lp.memLp (g i)).integrable_norm_pow (p := 2) (by norm_num))]
  apply integral_mono_ae (integrable_finset_sum s fun i _ => (Lp.memLp (g i)).integrable_norm_pow (p := 2) (by norm_num)) (integrable_const _)
  have hform : ∀ᵐ r ∂radialMeasure,∀ i ∈ s,g i r=⟪b i,greenRow hc r⟫_ℝ := by
    apply (Filter.eventually_all_finset s).mpr
    intro i _
    filter_upwards [greenOperator_coe hc (b i)] with r hr
    exact hr.trans ((greenRow_pair hc r (b i)).symm.trans (real_inner_comm _ _))
  filter_upwards [hform] with r hr
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun z : ℝ => ‖z‖^2) (hr i hi))]
  exact (b.orthonormal.sum_inner_products_le (s := s) (greenRow hc r)).trans (pow_le_pow_left₀ (norm_nonneg _) (hbound r) 2)

theorem greenOperator_compact {c : ℝ} (hc : 0<c) : IsCompactOperator (greenOperator hc) := by
  obtain ⟨_,b,_⟩ := exists_hilbertBasis ℝ RealRadialL2
  exact compact_of_square_columns b _ (greenOperator_square_columns b hc)

theorem greenOperator_eigenbasis {c : ℝ} (hc : 0<c) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ RealRadialL2) (e : ι → ℝ),
      ∀ i,greenOperator hc (b i)=e i • b i :=
  compact_symmetric_eigenbasis _ (greenOperator_compact hc) (greenOperator_symmetric hc)

end UV.CollarEigenmode
