import UV.ContinueTwoBandFourierTorus
import Mathlib.MeasureTheory.Function.Floor

/-! Exact mass of the periodized spatial heat envelope. The half-open cells
tile the cover in the three independent physical periods. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.SectorPlane

private def windingIndex (L₁ L₂ L₃ : ℝ) (x : Spatial) : ℤ × ℤ × ℤ :=
  (⌊x 0 / L₁⌋,⌊x 1 / L₂⌋,⌊x 2 / L₃⌋)

private theorem winding_index_measurable (L₁ L₂ L₃ : ℝ) : Measurable (windingIndex L₁ L₂ L₃) := by
  unfold windingIndex
  have h (i : Fin 3) (L : ℝ) : Measurable (fun x : Spatial => ⌊x i / L⌋) :=
    Int.measurable_floor.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.div_const L)
  exact (h 0 L₁).prodMk ((h 1 L₂).prodMk (h 2 L₃))

private theorem winding_index_shift {L : ℝ} (hL : 0 < L) (x : ℝ) (j : ℤ) :
    ⌊(x+L*(j:ℝ))/L⌋ = j ↔ x ∈ Ico 0 L := by
  have he : (x+L*(j:ℝ))/L = x/L+(j:ℝ) := by field_simp
  rw [he,Int.floor_add_intCast,add_eq_right,Int.floor_eq_zero_iff]
  simp [mem_Ico,le_div_iff₀ hL,div_lt_one hL]

theorem twoBand_torus_cell_integrals_hasSum
    {L₁ L₂ L₃ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) {f : Spatial → ℝ} (hf : Integrable f) :
    HasSum (fun n => ∫ x in twoBandTorusCell L₁ L₂ L₃, f (x+repairTorusMomentum L₁ L₂ L₃ n)) (∫ x, f x) := by
  classical
  let D := fun n : ℤ × ℤ × ℤ => windingIndex L₁ L₂ L₃ ⁻¹' {n}
  have hD (n) : MeasurableSet (D n) := (winding_index_measurable L₁ L₂ L₃) (measurableSet_singleton n)
  have hall : ⋃ n, D n = univ := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨windingIndex L₁ L₂ L₃ x,rfl⟩
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) :=
    fun _ _ hne => Set.disjoint_left.mpr fun _ hi hj => hne (hi.symm.trans hj)
  have hpre (n) : (fun x : Spatial => x+repairTorusMomentum L₁ L₂ L₃ n) ⁻¹' (D n) = twoBandTorusCell L₁ L₂ L₃ := by
    ext x
    change windingIndex _ _ _ (x + repairTorusMomentum L₁ L₂ L₃ n) = n ↔ _
    rcases n with ⟨n₁,n₂,n₃⟩
    change (⌊(x 0+L₁*(n₁:ℝ))/L₁⌋,⌊(x 1+L₂*(n₂:ℝ))/L₂⌋,⌊(x 2+L₃*(n₃:ℝ))/L₃⌋) =
      (n₁,n₂,n₃) ↔ _
    rw [Prod.mk.injEq,Prod.mk.injEq,winding_index_shift h₁,winding_index_shift h₂,winding_index_shift h₃]
    rfl
  have hs := hasSum_integral_iUnion hD hdis hf.integrableOn
  rw [hall,setIntegral_univ] at hs
  apply hs.congr_fun
  intro n
  have he := (measurePreserving_add_right volume (repairTorusMomentum L₁ L₂ L₃ n)).setIntegral_preimage_emb
    (Homeomorph.addRight _).measurableEmbedding f (D n)
  rwa [hpre n] at he

theorem twoBand_torus_cell_unfold
    {L₁ L₂ L₃ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) {f : Spatial → ℝ} (hf : Integrable f) :
    (∫ x in twoBandTorusCell L₁ L₂ L₃, ∑' n, f (x+repairTorusMomentum L₁ L₂ L₃ n)) = ∫ x, f x := by
  have hi (n) : IntegrableOn (fun x : Spatial => f (x+repairTorusMomentum L₁ L₂ L₃ n)) (twoBandTorusCell L₁ L₂ L₃) :=
    ((measurePreserving_add_right volume _).integrable_comp_of_integrable hf).integrableOn
  exact (hasSum_integral_of_summable_integral_norm hi (twoBand_torus_cell_integrals_hasSum h₁ h₂ h₃ hf.norm).summable).unique (twoBand_torus_cell_integrals_hasSum h₁ h₂ h₃ hf)

private theorem heat_nonneg (σ : ℝ) (z : Spatial) : 0 ≤ twoBandDisplacementDensity σ z := by
  unfold twoBandDisplacementDensity
  positivity

private theorem heat_integrable {σ : ℝ} (hσ : 0 < σ) : Integrable (twoBandDisplacementDensity σ) := by
  have h := twoBand_displacement_density_moment 1 hσ 0
  simpa [Real.norm_of_nonneg (heat_nonneg _ _)] using h

def twoBandHeatEnvelope (σ L₁ L₂ L₃ : ℝ) (x y : Spatial) : ℝ :=
  ∑' n, twoBandDisplacementDensity σ (y-x+repairTorusMomentum L₁ L₂ L₃ n)

theorem twoBand_heat_envelope_nonneg (σ L₁ L₂ L₃ : ℝ) (x y : Spatial) :
    0 ≤ twoBandHeatEnvelope σ L₁ L₂ L₃ x y := tsum_nonneg (fun _ => heat_nonneg _ _)

theorem twoBand_heat_envelope_mass {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁)
    (h₂ : 0 < L₂) (h₃ : 0 < L₃) (x : Spatial) :
    (∫ y in twoBandTorusCell L₁ L₂ L₃, twoBandHeatEnvelope σ L₁ L₂ L₃ x y) = 1 := by
  have he (y : Spatial) (n) : y-x+repairTorusMomentum L₁ L₂ L₃ n =
      (y+repairTorusMomentum L₁ L₂ L₃ n)+(-x) := by abel
  unfold twoBandHeatEnvelope
  simp_rw [he]
  rw [twoBand_torus_cell_unfold h₁ h₂ h₃ (f := fun y => twoBandDisplacementDensity σ (y+-x))
    ((measurePreserving_add_right volume (-x)).integrable_comp_of_integrable (heat_integrable hσ)),
    integral_add_right_eq_self,twoBand_displacement_density_mass hσ]

theorem twoBand_heat_envelope_symm (σ L₁ L₂ L₃ : ℝ) (x y : Spatial) :
    twoBandHeatEnvelope σ L₁ L₂ L₃ y x = twoBandHeatEnvelope σ L₁ L₂ L₃ x y := by
  unfold twoBandHeatEnvelope
  rw [← (Equiv.neg (ℤ × ℤ × ℤ)).tsum_eq (fun n =>
    twoBandDisplacementDensity σ (x-y+repairTorusMomentum L₁ L₂ L₃ n))]
  apply tsum_congr
  intro n
  have hv : repairTorusMomentum L₁ L₂ L₃ (-n) = -repairTorusMomentum L₁ L₂ L₃ n := by
    ext i
    fin_cases i <;> simp [repairTorusMomentum]
  have he : x-y+repairTorusMomentum L₁ L₂ L₃ (Equiv.neg _ n) =
      -(y-x+repairTorusMomentum L₁ L₂ L₃ n) := by change x-y+repairTorusMomentum L₁ L₂ L₃ (-n) = _; rw [hv]; abel
  simp only [he,twoBandDisplacementDensity,norm_neg]

private theorem winding_norm (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (q g σ L₁ L₂ L₃ t : ℝ)
    (x y : Spatial) (n : ℤ × ℤ × ℤ) :
    ‖twoBandWindingHop A q g σ L₁ L₂ L₃ t x y n‖ =
      |g| * twoBandDisplacementDensity σ (y-x+repairTorusMomentum L₁ L₂ L₃ n) := by
  unfold twoBandWindingHop
  rw [norm_mul,twoBand_spatial_wilson_unit,mul_one,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_of_nonneg (heat_nonneg _ _)]

theorem twoBand_periodized_hop_envelope (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) (t : ℝ) (x y : Spatial) :
    ‖twoBandPeriodizedHop A q g σ L₁ L₂ L₃ t x y‖ ≤ |g| * twoBandHeatEnvelope σ L₁ L₂ L₃ x y := by
  obtain ⟨F,hF,hB⟩ := twoBand_winding_gaussian_bound A q g hσ h₁ h₂ h₃ ‖y-x‖
  apply (norm_tsum_le_tsum_norm (hF.of_nonneg_of_le (fun _ => norm_nonneg _) (hB t x y le_rfl))).trans_eq
  simp_rw [winding_norm]
  rw [tsum_mul_left]
  rfl

theorem twoBand_heat_envelope_measurable {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ)
    (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    Measurable (fun p : Spatial × Spatial => twoBandHeatEnvelope σ L₁ L₂ L₃ p.1 p.2) := by
  apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset (ℤ × ℤ × ℤ)))
    (fun S => Finset.measurable_sum S (fun n _ => (show Measurable (fun p : Spatial × Spatial =>
      twoBandDisplacementDensity σ (p.2-p.1+repairTorusMomentum L₁ L₂ L₃ n)) by unfold twoBandDisplacementDensity; fun_prop)))
  apply tendsto_pi_nhds.mpr
  intro p
  obtain ⟨F,hF,hB⟩ := twoBand_winding_gaussian_bound (fun _ => 0) 0 1 hσ h₁ h₂ h₃ ‖p.2-p.1‖
  have h := hF.of_nonneg_of_le (fun _ => norm_nonneg _) (hB 0 p.1 p.2 le_rfl)
  simpa only [winding_norm,abs_one,one_mul] using h.hasSum

end UV.SectorPlane
