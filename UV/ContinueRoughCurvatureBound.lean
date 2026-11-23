import UV.ContinueRoughCurvatureGreen
import UV.ContinueNetworkTonelli
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Absolute angular summation and radial integration of the actual
Green comparison with essentially bounded L² angular profiles. -/

noncomputable section
open Real MeasureTheory Filter Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius Topology
namespace UV.RoughCurvature

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem collar_cycle_sum_finite {n : ℕ} (s : Finset ℤ)
    (z : Fin (n+2) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (b : Fin (n+2) → AngularProfile) (hb : ∀ i, fourierCoeff (b i) 0 = 0) :
    ∑ k : Fin (n+2) → s, collarCyclicWeight z (fun i => fourierCoeff (b i)) (fun i => (k i:ℤ)) ≤
      ∏ i, collarVertexMajorant (z i) * (sqrt (1+Real.pi^2/12) * ‖b i‖) := by
  classical
  let A := fun i => angularMatrix s (fourierCoeff (b i))
  have hV (i : Fin (n+2)) : 0 ≤ collarVertexMajorant (z i) :=
    rpow_nonneg (by linarith [hz i]) _
  calc
    _ ≤ ∑ k : Fin (n+2) → s, ∏ i, collarVertexMajorant (z i) * A i (k i) (k (i+1)) := by
      apply Finset.sum_le_sum
      exact fun k _ => collar_cyclic_route_bound z hz _ hb (fun i => (k i:ℤ))
    _ = (∏ i, collarVertexMajorant (z i)) * (List.ofFn A).prod.trace := by
      simp only [Finset.prod_mul_distrib, ← Finset.mul_sum, cycle_trace_formula]
    _ ≤ (∏ i, collarVertexMajorant (z i)) * ∏ i, ‖A i‖ := by
      apply mul_le_mul_of_nonneg_left ((le_abs_self _).trans (frobenius_cycle_le A))
      exact Finset.prod_nonneg fun i _ => hV i
    _ ≤ _ := by
      rw [Finset.prod_mul_distrib]
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hV i)
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => angularMatrix_parseval s (b i))

/-- The full countable angular sum is bounded before radial integration.
A finite family of paths fits in one genuine finite matrix compression. -/
theorem collar_cycle_sum {n : ℕ} (z : Fin (n+2) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (b : Fin (n+2) → AngularProfile) (hb : ∀ i, fourierCoeff (b i) 0 = 0) :
    ∑' k : Fin (n+2) → ℤ, ENNReal.ofReal (collarCyclicWeight z (fun i => fourierCoeff (b i)) k) ≤
      ENNReal.ofReal (∏ i, collarVertexMajorant (z i) * (sqrt (1+Real.pi^2/12) * ‖b i‖)) := by
  classical
  let f := collarCyclicWeight z (fun i => fourierCoeff (b i))
  have hf (k : Fin (n+2) → ℤ) : 0 ≤ f k := collarCyclicWeight_nonneg hz _ k
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let s : Finset ℤ := S.biUnion (fun k => Finset.univ.image k)
  let lift (k : S) (i : Fin (n+2)) : s :=
    ⟨k.val i, Finset.mem_biUnion.mpr ⟨k.val,k.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩
  let e : S ↪ (Fin (n+2) → s) := ⟨lift, by
    intro p q hpq
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hpq i)⟩
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hf k)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ∑ k ∈ S, f k = ∑ k ∈ Finset.univ.map e, f (fun i => (k i : ℤ)) := by
      rw [Finset.sum_map]
      exact Finset.sum_subtype S (fun _ => Iff.rfl) f
    _ ≤ ∑ k : Fin (n+2) → s, f (fun i => (k i : ℤ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hf _)
    _ ≤ _ := collar_cycle_sum_finite s z hz b hb

private theorem collarVertexMajorant_measurable : Measurable collarVertexMajorant := by
  unfold collarVertexMajorant
  fun_prop

theorem collarVertexMajorant_integral :
    (∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal (collarVertexMajorant z)) = ENNReal.ofReal (2/3) := by
  let F (z : ℝ) := -(2/3:ℝ) * (1+3*z)^(-1/2:ℝ)
  have hD (z : ℝ) (hz : z ∈ Ici (0:ℝ)) : HasDerivAt F (collarVertexMajorant z) z := by
    have hz' : 0 < 1+3*z := by linarith [mem_Ici.mp hz]
    have hlin : HasDerivAt (fun t : ℝ => 1+3*t) 3 z := by
      convert ((hasDerivAt_id z).const_mul 3).const_add 1 using 1
      ring
    have hpow := (Real.hasDerivAt_rpow_const (p := (-1/2:ℝ))
      (Or.inl hz'.ne')).comp z hlin
    convert hpow.const_mul (-(2/3:ℝ)) using 1
    simp only [collarVertexMajorant]
    rw [show (-1/2:ℝ)-1=-3/2 by ring]
    ring
  have hP (z : ℝ) (hz : z ∈ Ioi (0:ℝ)) : 0 ≤ collarVertexMajorant z :=
    rpow_nonneg (by linarith [mem_Ioi.mp hz]) _
  have hL : Tendsto (fun z : ℝ => 1+3*z) atTop atTop := by
    apply tendsto_atTop.2
    intro x
    filter_upwards [eventually_ge_atTop (x/3)] with z hz
    linarith
  have hT : Tendsto F atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < (1/2:ℝ) by norm_num)).comp hL
    simpa only [F, mul_zero, Function.comp_apply, neg_div] using h.const_mul (-(2/3:ℝ))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hD hP hT)
    ((ae_restrict_mem measurableSet_Ioi).mono hP),
    integral_Ioi_of_hasDerivAt_of_nonneg' hD hP hT]
  norm_num [F]

abbrev collarPositiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

def roughCurvatureCost {n : ℕ} (b : Fin (n+1) → ℝ → AngularProfile) : ℝ≥0∞ :=
  ∫⁻ z : Fin (n+1) → ℝ,
    ∑' k : Fin (n+1) → ℤ, ENNReal.ofReal
      (collarCyclicWeight z (fun i => fourierCoeff (b i (z i))) k)
    ∂Measure.pi (fun _ => collarPositiveMeasure)

/-- The stated exact rough-profile constant for the absolute Green word.
The hypotheses on the profiles and the norm bound hold almost everywhere
in the radial integral. -/
theorem rough_curvature_green_bound {n : ℕ} (b : Fin (n+2) → ℝ → AngularProfile)
    (M : Fin (n+2) → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hb : ∀ i, ∀ᵐ z ∂collarPositiveMeasure, fourierCoeff (b i z) 0 = 0 ∧ ‖b i z‖ ≤ M i) :
    roughCurvatureCost b ≤
      ENNReal.ofReal (((2/3)*sqrt (1+Real.pi^2/12))^(n+2) * ∏ i, M i) := by
  have hpos : ∀ᵐ z : Fin (n+2) → ℝ ∂Measure.pi (fun _ => collarPositiveMeasure), ∀ i, 0 < z i := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n+2) => collarPositiveMeasure) (i := i)
      (ae_restrict_mem measurableSet_Ioi)
  have hp : ∀ᵐ z : Fin (n+2) → ℝ ∂Measure.pi (fun _ => collarPositiveMeasure),
      ∀ i, fourierCoeff (b i (z i)) 0 = 0 ∧ ‖b i (z i)‖ ≤ M i := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n+2) => collarPositiveMeasure) (i := i) (hb i)
  let C := sqrt (1+Real.pi^2/12)
  have hC : 0 ≤ C := sqrt_nonneg _
  calc
    roughCurvatureCost b ≤ ∫⁻ z : Fin (n+2) → ℝ,
        ∏ i, ENNReal.ofReal (collarVertexMajorant (z i) * (C*M i))
        ∂Measure.pi (fun _ => collarPositiveMeasure) := by
      apply lintegral_mono_ae
      filter_upwards [hpos, hp] with z hz hbz
      have hW (i : Fin (n+2)) : 0 ≤ collarVertexMajorant (z i) := rpow_nonneg (by linarith [hz i]) _
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (hW i) (mul_nonneg hC (hM i)))]
      exact (collar_cycle_sum z (fun i => (hz i).le) (fun i => b i (z i)) (fun i => (hbz i).1)).trans
        (ENNReal.ofReal_le_ofReal (Finset.prod_le_prod
          (fun i _ => mul_nonneg (hW i) (mul_nonneg hC (norm_nonneg _)))
          (fun i _ => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbz i).2 hC) (hW i))))
    _ = _ := by
      rw [network_lintegral_fintype_prod (fun _ : Fin (n+2) => collarPositiveMeasure)
        (fun i x => ENNReal.ofReal (collarVertexMajorant x * (C*M i)))
        (fun i => ENNReal.measurable_ofReal.comp (collarVertexMajorant_measurable.mul_const _))]
      have hI (i : Fin (n+2)) :
          (∫⁻ z, ENNReal.ofReal (collarVertexMajorant z * (C*M i)) ∂collarPositiveMeasure) =
          ENNReal.ofReal ((2/3)*C*M i) := by
        have he (x : ℝ) : ENNReal.ofReal (collarVertexMajorant x * (C*M i)) =
            ENNReal.ofReal (C*M i) * ENNReal.ofReal (collarVertexMajorant x) := by
          rw [mul_comm, ENNReal.ofReal_mul (mul_nonneg hC (hM i))]
        simp_rw [he]
        rw [lintegral_const_mul _ (show Measurable (fun z => ENNReal.ofReal (collarVertexMajorant z)) from
          ENNReal.measurable_ofReal.comp collarVertexMajorant_measurable),
          collarPositiveMeasure, collarVertexMajorant_integral, ← ENNReal.ofReal_mul (mul_nonneg hC (hM i))]
        congr 1
        ring
      simp_rw [hI]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (by norm_num) hC) (hM i)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

theorem rough_curvature_one_insertion (z : Fin 1 → ℝ) (a : Fin 1 → ℤ → ℂ)
    (h : a 0 0 = 0) (k : Fin 1 → ℤ) : collarCyclicWeight z a k = 0 := by
  simp [collarCyclicWeight, h]

end UV.RoughCurvature
