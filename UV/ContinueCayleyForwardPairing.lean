import UV.ContinueNaimarkSchur
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Identification of the repository's Radon–Nikodym entry integral
from the setwise polarized quadratic laws of a finite matrix measure. -/

noncomputable section
namespace UV.SectorPlane
open MeasureTheory Set Filter Matrix
open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def closingFiniteForm (A : Matrix ι ι ℂ) (y : ι→ℂ) : ℂ :=
  ∑ i, ∑ j, (conj (y i)*y j)*A i j

omit [DecidableEq ι] in
theorem closing_finite_form_dot (A : Matrix ι ι ℂ) (y : ι→ℂ) :
    closingFiniteForm A y = star y ⬝ᵥ (A *ᵥ y) := by
  simp only [closingFiniteForm,dotProduct,mulVec,Pi.star_apply,Finset.mul_sum,Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem closing_finite_form_ext {A B : Matrix ι ι ℂ} (he : ∀ y, closingFiniteForm A y=closingFiniteForm B y) :
    A=B := by
  have hi (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
      ⟪v,Matrix.toEuclideanLin M v⟫_ℂ=closingFiniteForm M (WithLp.ofLp v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toEuclideanLin_apply,dotProduct_comm,closing_finite_form_dot]
  have hz := (inner_map_self_eq_zero (Matrix.toEuclideanLin A-Matrix.toEuclideanLin B)).mp (fun v => by
    rw [←inner_conj_symm]
    simp only [LinearMap.sub_apply,inner_sub_right,hi,he,sub_self,map_zero])
  exact Matrix.toEuclideanLin.injective (sub_eq_zero.mp hz)

omit [DecidableEq ι] in
theorem closing_finite_form_gram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ι→H) (R : H →L[ℂ] H) (y : ι→ℂ) :
    closingFiniteForm (fun i j => ⟪v i,R (v j)⟫_ℂ) y =
    ⟪∑ i, y i • v i,R (∑ j, y j • v j)⟫_ℂ := by
  simp only [closingFiniteForm,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
theorem closing_forward_form_test (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (y : ι→ℂ)
    (hν : ∀ s, MeasurableSet s → closingFiniteForm (fun i j => M i j s) y=(ν.real s:ℂ))
    (f : ℝ→ℂ) (hw : ∀ i j, Integrable (fun x => f x*closingMatrixDensity M x i j) (closingControlMeasure M)) :
    closingFiniteForm (closingMeasureEntryIntegral M f) y = ∫ x, f x ∂ν := by
  let μ := closingControlMeasure M
  let D := closingMatrixDensity M
  let Q := fun x => closingFiniteForm (D x) y
  have hI (i j : ι) : Integrable (fun x => D x i j) μ := closing_density_entry_integrable M i j
  have hQ : Integrable Q μ := integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (hI i j).const_mul (conj (y i)*y j)
  have hpos : ∀ᵐ x ∂μ, 0≤Q x := (closing_matrix_density_positive M hM).mono fun x hx => by
    rw [show Q x = star y ⬝ᵥ (D x *ᵥ y) from closing_finite_form_dot _ _]
    exact hx.2 y
  have hsQ (s : Set ℝ) (hs : MeasurableSet s) : (∫ x in s,Q x ∂μ)=(ν.real s:ℂ) := by
    rw [←hν s hs]
    dsimp only [Q,closingFiniteForm]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul,closing_density_entry_integral M i j hs]
      · exact fun j _ => ((hI i j).const_mul _).integrableOn
    · exact fun i _ => integrable_finset_sum _ fun j _ => ((hI i j).const_mul _).integrableOn
  have hμ : μ.withDensity (fun x => ENNReal.ofReal (Q x).re)=ν := by
    ext s hs
    have hR : IntegrableOn (fun x => (Q x).re) s μ := hQ.re.integrableOn
    have hreal : (∫ x in s,(Q x).re ∂μ)=(∫ x in s,Q x ∂μ).re := integral_re hQ.integrableOn
    rw [withDensity_apply _ hs,←ofReal_integral_eq_lintegral_ofReal hR
      (ae_restrict_of_ae (hpos.mono fun x hx => (Complex.nonneg_iff.mp hx).1)),hreal,hsQ s hs,
      Complex.ofReal_re,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hRm : AEMeasurable (fun x => (Q x).re) μ := hQ.re.aemeasurable
  rw [←hμ,integral_withDensity_eq_integral_toReal_smul₀ hRm.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc _ = ∫ x, ∑ i,∑ j,(conj (y i)*y j)*(f x*D x i j) ∂μ := by
            unfold closingFiniteForm
            rw [integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro i _
              rw [integral_finset_sum]
              · apply Finset.sum_congr rfl
                intro j _
                rw [integral_const_mul]
                rfl
              · exact fun j _ => (hw i j).const_mul _
            · exact fun i _ => integrable_finset_sum _ fun j _ => (hw i j).const_mul _
       _ = _ := by
            apply integral_congr_ae
            filter_upwards [hpos] with x hx
            obtain ⟨hr,hi⟩ := Complex.nonneg_iff.mp hx
            have hcx : ((Q x).re:ℂ)=Q x := Complex.ext rfl hi
            rw [ENNReal.toReal_ofReal hr,Complex.real_smul,hcx]
            dsimp only [Q,closingFiniteForm]
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring

end UV.SectorPlane
