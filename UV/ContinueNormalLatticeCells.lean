import UV.ContinueNormalZeroLoop
import UV.ContinueNormalWindingIntegral
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Countable

/-! Counting every point of a reciprocal four-lattice. Integrable
continuum majorants with a uniform comparison on each fundamental cell
give absolute lattice sums, also with a continuous normal frequency. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace UV

abbrev NormalReciprocalBasis := Module.Basis (Fin 4) ℝ OSFourSpace
abbrev NormalReciprocalLattice (b : NormalReciprocalBasis) := Submodule.span ℤ (Set.range b)

def normalLatticeMeasure (b : NormalReciprocalBasis) : Measure OSFourSpace :=
  Measure.map (fun k : NormalReciprocalLattice b => (k : OSFourSpace)) Measure.count

instance (b : NormalReciprocalBasis) : SigmaFinite (normalLatticeMeasure b) := by
  haveI : Countable (NormalReciprocalLattice b) := inferInstanceAs (Countable (Submodule.span ℤ (Set.range (fun i : Fin 4 => b i))))
  have h : (NormalReciprocalLattice b : Set OSFourSpace).Countable := Set.countable_coe_iff.mp (show Countable (NormalReciprocalLattice b) from inferInstance)
  have he : MeasurableEmbedding (fun k : NormalReciprocalLattice b => (k : OSFourSpace)) := MeasurableEmbedding.subtype_coe h.measurableSet
  exact he.sigmaFinite_map

def normalCellFactor (b : NormalReciprocalBasis) (C : ℝ) : ℝ≥0∞ :=
  (volume (ZSpan.fundamentalDomain b))⁻¹ * ENNReal.ofReal C

theorem normal_cell_factor_finite (b : NormalReciprocalBasis) (C : ℝ) : normalCellFactor b C ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ZSpan.measure_fundamentalDomain_ne_zero b)) ENNReal.ofReal_ne_top

theorem normal_lattice_cell_lintegral (b : NormalReciprocalBasis) (C : ℝ) (f : OSFourSpace → ℝ≥0∞)
    (hf : Measurable f)
    (hc : ∀ (k : NormalReciprocalLattice b), ∀ x ∈ ZSpan.fundamentalDomain b,
      f k ≤ ENNReal.ofReal C * f ((k:OSFourSpace)+x)) :
    (∫⁻ k, f k ∂normalLatticeMeasure b) ≤ normalCellFactor b C * ∫⁻ k, f k := by
  let S := ZSpan.fundamentalDomain b
  let A := volume S
  have hA : A ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero b
  have hAt : A ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  letI : MeasurableVAdd (NormalReciprocalLattice b) OSFourSpace :=
    inferInstanceAs (MeasurableVAdd (NormalReciprocalLattice b).toAddSubgroup OSFourSpace)
  letI : VAddInvariantMeasure (NormalReciprocalLattice b) OSFourSpace volume :=
    inferInstanceAs (VAddInvariantMeasure (NormalReciprocalLattice b).toAddSubgroup OSFourSpace volume)
  have hd := (ZSpan.isAddFundamentalDomain b volume).lintegral_eq_tsum'' f
  have h (k : NormalReciprocalLattice b) : A * f k ≤ ENNReal.ofReal C * ∫⁻ x in S, f ((k:OSFourSpace)+x) := by
    calc A * f k = ∫⁻ _ : OSFourSpace in S, f k := by simp [A,mul_comm]
         _ ≤ ∫⁻ x in S, ENNReal.ofReal C * f ((k:OSFourSpace)+x) := lintegral_mono_ae
           ((ae_restrict_mem (ZSpan.fundamentalDomain_measurableSet b)).mono fun x hx => hc k x hx)
         _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hh : A * (∑' k : NormalReciprocalLattice b, f k) ≤ ENNReal.ofReal C * ∫⁻ k, f k := by
    rw [hd,←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum h
  rw [normalLatticeMeasure,lintegral_map hf measurable_subtype_coe,lintegral_count]
  calc _ = A⁻¹ * (A * ∑' k : NormalReciprocalLattice b, f k) := by rw [←mul_assoc,ENNReal.inv_mul_cancel hA hAt,one_mul]
       _ ≤ A⁻¹ * (ENNReal.ofReal C * ∫⁻ k, f k) := mul_le_mul_left' hh _
       _ = _ := (mul_assoc _ _ _).symm

/-- Tonelli leaves the extra normal-circle Fourier variable continuous,
even when every carrier four-momentum is summed on the torus. -/
theorem normal_lattice_frequency_lintegral (b : NormalReciprocalBasis) (C : ℝ) (f : NormalLoopFrequency → ℝ≥0∞)
    (hf : Measurable f) (hc : ∀ (k : NormalReciprocalLattice b), ∀ x ∈ ZSpan.fundamentalDomain b, ∀ ξ,
      f (k,ξ) ≤ ENNReal.ofReal C * f ((k:OSFourSpace)+x,ξ)) :
    (∫⁻ t, f t ∂(normalLatticeMeasure b).prod volume) ≤ normalCellFactor b C * ∫⁻ t, f t := by
  rw [Measure.volume_eq_prod OSFourSpace ℝ,lintegral_prod_symm _ hf.aemeasurable,lintegral_prod_symm _ hf.aemeasurable,
    ←lintegral_const_mul' _ _ (normal_cell_factor_finite b C)]
  exact lintegral_mono fun ξ => normal_lattice_cell_lintegral b C (fun k => f (k,ξ))
    (hf.comp (measurable_id.prodMk measurable_const)) (fun k x hx => hc k x hx ξ)

theorem normal_integral_from_cell_bound {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    {g : X → ℝ} (hg : Measurable g) (hn : ∀ x, 0 ≤ g x) (hi : Integrable g ν) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hb : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ C * ∫⁻ x, ENNReal.ofReal (g x) ∂ν) :
    Integrable g μ ∧ (∫ x, g x ∂μ) ≤ C.toReal*(∫ x, g x ∂ν) := by
  have hnμ : 0 ≤ᵐ[μ] g := Eventually.of_forall hn
  have hnν : 0 ≤ᵐ[ν] g := Eventually.of_forall hn
  rw [←ofReal_integral_eq_lintegral_ofReal hi hnν] at hb
  have hfin := ENNReal.mul_ne_top hC (ENNReal.ofReal_ne_top : ENNReal.ofReal (∫ x, g x ∂ν) ≠ ⊤)
  have hμ : Integrable g μ := ⟨hg.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hnμ).mpr (hb.trans_lt hfin.lt_top)⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hμ hnμ] at hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),ENNReal.toReal_mul] using
    And.intro hμ (ENNReal.toReal_mono hfin hb)

end UV
