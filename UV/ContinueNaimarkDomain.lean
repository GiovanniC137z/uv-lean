import UV.ContinueNaimarkTrace
import UV.ContinueNaimarkLift

/-! The trace second moment places every constant slot in the domain of
the maximal self-adjoint signed energy multiplier. -/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal InnerProductSpace
namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def closingNaimarkEnergy (M : Matrix ι ι (ComplexMeasure ℝ)) :=
  sourceL2Multiplier (closingNaimarkMeasure M) (fun p => (p.2 : ℂ))

omit [DecidableEq ι] [MeasurableSingletonClass ι] in
theorem closing_naimark_energy_selfAdjoint (M : Matrix ι ι (ComplexMeasure ℝ)) :
    IsSelfAdjoint (closingNaimarkEnergy M) :=
  sourceL2Multiplier_real_selfAdjoint _ Prod.snd measurable_snd

theorem closing_column_energy_domain (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (h₂ : Integrable (fun x : ℝ => x^2) (closingTraceLaw M)) (j : ι) :
    closingNaimarkColumn M hM j ∈ (closingNaimarkEnergy M).domain := by
  let C := closingNaimarkFactor M
  let f (p : ι × ℝ) : ℂ := (p.2 : ℂ) * closingColumnValue M j p
  have hm : Measurable f := measurable_snd.complex_ofReal.mul (closing_column_measurable M j)
  have hslice (k : ι) : Integrable (fun x : ℝ => ‖f (k,x)‖^2) (closingControlMeasure M) := by
    apply (closing_density_second_integrable M hM h₂ j).mono'
      ((hm.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [closing_factor_column_norm M hM j] with x hx
    change ‖‖(x : ℂ) * C x k j‖^2‖ ≤ x^2 * (closingMatrixDensity M x j j).re
    rw [Real.norm_of_nonneg (sq_nonneg _),norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,←hx]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun t => ‖C x t j‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)) (sq_nonneg _)
  have hI : Integrable (fun p => ‖f p‖ ^ 2) (closingNaimarkMeasure M) :=
    (integrable_prod_iff (hm.norm.pow_const 2).aestronglyMeasurable).mpr
      ⟨ae_of_all _ hslice, Integrable.of_finite⟩
  have hL := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hI
  apply MemLp.ae_eq _ hL
  filter_upwards [closing_naimark_column_ae M hM j] with p h
  exact congrArg ((p.2 : ℂ) * ·) h.symm

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]

theorem closing_naimark_slot_domain (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (hn : ClosingNormalizedMatrixMeasure M) (b : OrthonormalBasis ι ℂ S)
    (h₂ : Integrable (fun x : ℝ => x^2) (closingTraceLaw M)) (v : S) :
    closingNaimarkLift M hM hn b v ∈ (closingNaimarkEnergy M).domain := by
  rw [← b.sum_repr v,map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul,closing_naimark_lift_basis]
  exact Submodule.smul_mem _ _ (closing_column_energy_domain M hM h₂ j)

end UV.SectorPlane
