import UV.ContinueCayleyCauchy
import UV.ContinueCayleyAtom

/-! A finite scalar spectral law on the real signed-energy axis for a vector
in the domain of an arbitrary self-adjoint generator. The compact vector
state is taken at the graph vector `K x + i x`. Its Cayley weight realizes
the original vector `x` and its Cauchy transform is the actual resolvent. -/

noncomputable section
open MeasureTheory Set ContinuousLinearMap Filter
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private abbrev slotRep (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :=
  cfcHom (R:=ℂ) (closing_cayley_normal K hK)

private abbrev graphVector (K : H →ₗ.[ℂ] H) (x : K.domain) : H := K x + Complex.I • (x:H)

private abbrev slotState (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :=
  closingCompactState (slotRep K hK) (graphVector K x)

private def slotMultiplier (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    C(spectrum ℂ (closingCayley K hK),ℂ) :=
  ((2:ℂ)*Complex.I)⁻¹ • (1-(ContinuousMap.id ℂ).restrict _)

private theorem multiplier_on_graph (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    slotRep K hK (slotMultiplier K hK) (graphVector K x) = (x:H) := by
  rw [slotMultiplier,map_smul,map_sub,map_one,cfcHom_id,smul_apply,
    (closing_cayley_graph_pair K hK x).1, smul_smul]
  rw [inv_mul_cancel₀ (by norm_num : (2:ℂ)*Complex.I ≠ 0),one_smul]

private theorem multiplier_weight (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (y : spectrum ℂ (closingCayley K hK)) :
    (closingCayleyWeight y : ℂ) = conj (slotMultiplier K hK y) * (slotMultiplier K hK y) := by
  rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  apply congrArg Complex.ofReal
  change ‖1-(y:ℂ)‖^2/4 = ‖((2:ℂ)*Complex.I)⁻¹ * (1-(y:ℂ))‖^2
  simp
  ring

theorem closing_domain_weighted_compact_test (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain)
    (g : C(spectrum ℂ (closingCayley K hK),ℂ)) :
    (∫ y, (closingCayleyWeight y : ℂ) * g y ∂slotState K hK x) = ⟪(x:H),slotRep K hK g (x:H)⟫_ℂ := by
  let L := slotMultiplier K hK
  have he (y : spectrum ℂ (closingCayley K hK)) :
      (closingCayleyWeight y : ℂ)*g y = (star L * (g*L)) y := by
    rw [multiplier_weight K hK y]
    change (conj (L y)*L y)*g y = conj (L y)*(g y*L y)
    ring
  simp_rw [he]
  rw [closing_compact_state_integral,map_mul,map_star,map_mul]
  change ⟪graphVector K x, (slotRep K hK L).adjoint (slotRep K hK g (slotRep K hK L (graphVector K x)))⟫_ℂ=_
  rw [adjoint_inner_right,multiplier_on_graph]

def closingDomainSlotLaw (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) : Measure ℝ :=
  closingCayleyLaw (slotState K hK x) Subtype.val

instance (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    IsFiniteMeasure (closingDomainSlotLaw K hK x) := by
  let μ := slotState K hK x
  let w (y : spectrum ℂ (closingCayley K hK)) := ENNReal.ofReal (closingCayleyWeight y)
  have hw (y : spectrum ℂ (closingCayley K hK)) : w y ≤ 1 := by
    have hu := norm_sub_le (1:ℂ) (y:ℂ)
    rw [norm_one,closing_cayley_spectral_norm K hK y] at hu
    change ENNReal.ofReal (‖1-(y:ℂ)‖^2/4) ≤ 1
    rw [ENNReal.ofReal_le_one]
    nlinarith [norm_nonneg (1-(y:ℂ))]
  haveI : IsFiniteMeasure (μ.withDensity w) := isFiniteMeasure_withDensity <|
    ne_top_of_le_ne_top (by simp : (∫⁻ _ : spectrum ℂ (closingCayley K hK), (1:ℝ≥0∞) ∂μ) ≠ ⊤)
      (lintegral_mono hw)
  change IsFiniteMeasure ((μ.withDensity w).map _)
  infer_instance

theorem closing_domain_slot_mass (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    (closingDomainSlotLaw K hK x).real univ = ‖(x:H)‖^2 := by
  rw [closingDomainSlotLaw,closing_cayley_law_mass _ _ measurable_subtype_coe]
  have h := closing_domain_weighted_compact_test K hK x 1
  simp only [ContinuousMap.one_apply,mul_one,map_one,one_apply,inner_self_eq_norm_sq_to_K] at h
  have hc := integral_complex_ofReal (μ:=slotState K hK x) (f:=fun y : spectrum ℂ (closingCayley K hK) => closingCayleyWeight y)
  exact Complex.ofReal_injective ((hc.symm.trans h).trans (Complex.ofReal_pow ..).symm)

theorem closing_domain_slot_second_moment (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    Integrable (fun t : ℝ => t^2) (closingDomainSlotLaw K hK x) :=
  closing_cayley_law_second_moment _ _ measurable_subtype_coe (closing_cayley_spectral_norm K hK)

theorem closing_domain_slot_cauchy (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain)
    (z : ℂ) (hz : z.im ≠ 0) :
    (∫ t : ℝ, (z + (t:ℂ))⁻¹ ∂closingDomainSlotLaw K hK x) =
      ⟪(x:H),(closingNonrealResolvent K hK z hz).map (x:H)⟫_ℂ := by
  rw [closingDomainSlotLaw,closing_cayley_law_cauchy _ _ measurable_subtype_coe (closing_cayley_spectral_norm K hK)]
  exact (closing_domain_weighted_compact_test K hK x (closingCayleySpectralCauchy K hK z hz)).trans
    (congrArg (fun A : H →L[ℂ] H => ⟪(x:H), A (x:H)⟫_ℂ) (closing_cayley_cfc_resolvent K hK z hz))

private def slotEnergyMultiplier (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    C(spectrum ℂ (closingCayley K hK),ℂ) :=
  (2:ℂ)⁻¹ • (1+(ContinuousMap.id ℂ).restrict _)

private theorem energy_multiplier_on_graph (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    slotRep K hK (slotEnergyMultiplier K hK) (graphVector K x) = K x := by
  rw [slotEnergyMultiplier,map_smul,map_add (slotRep K hK),map_one,cfcHom_id,smul_apply,
    (closing_cayley_graph_pair K hK x).2, smul_smul]
  simp

private theorem slot_mixed_test (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain)
    (f g : C(spectrum ℂ (closingCayley K hK),ℂ)) :
    (∫ y, conj (f y) * g y ∂slotState K hK x) =
      ⟪slotRep K hK f (graphVector K x),slotRep K hK g (graphVector K x)⟫_ℂ := by
  change (∫ y, (star f*g) y ∂slotState K hK x)=_
  rw [closing_compact_state_integral,map_mul,map_star]
  exact adjoint_inner_right (slotRep K hK f) (graphVector K x) (slotRep K hK g (graphVector K x))

private theorem slot_energy_product (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (y : spectrum ℂ (closingCayley K hK)) :
    ((closingCayleyWeight y * closingCayleyEnergy y : ℝ) : ℂ) =
      conj (slotMultiplier K hK y) * slotEnergyMultiplier K hK y := by
  by_cases hy : (y:ℂ)=1
  · change _ = conj (((2:ℂ)*Complex.I)⁻¹ * (1-(y:ℂ))) * ((2:ℂ)⁻¹*(1+(y:ℂ)))
    simp [hy,closingCayleyWeight]
  have hne : 1-(y:ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  rw [Complex.ofReal_mul,multiplier_weight K hK y,mul_assoc]
  congr 1
  rw [closing_cayley_energy_real (closing_cayley_spectral_norm K hK y)]
  change (((2:ℂ)*Complex.I)⁻¹ * (1-(y:ℂ))) * (Complex.I*(1+(y:ℂ))/(1-(y:ℂ))) = (2:ℂ)⁻¹*(1+(y:ℂ))
  field_simp

theorem closing_domain_slot_first_exact (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    (∫ t : ℝ, t ∂closingDomainSlotLaw K hK x) = (⟪(x:H),K x⟫_ℂ).re := by
  rw [closingDomainSlotLaw,closing_cayley_law_integral _ _ measurable_subtype_coe (fun t : ℝ => t) (by fun_prop)]
  let w (y : spectrum ℂ (closingCayley K hK)) := closingCayleyWeight y * closingCayleyEnergy y
  have h : ((∫ y, w y ∂slotState K hK x : ℝ) : ℂ) = ⟪(x:H),K x⟫_ℂ := by
    calc
      _ = ∫ y, (w y : ℂ) ∂slotState K hK x := integral_complex_ofReal.symm
      _ = ∫ y, conj (slotMultiplier K hK y) * slotEnergyMultiplier K hK y ∂slotState K hK x := by
        apply integral_congr_ae
        exact Eventually.of_forall (slot_energy_product K hK)
      _ = _ := by rw [slot_mixed_test,multiplier_on_graph,energy_multiplier_on_graph]
  exact congrArg Complex.re h

private theorem slot_energy_square (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (y : spectrum ℂ (closingCayley K hK)) :
    ((‖1+(y:ℂ)‖^2/4 : ℝ) : ℂ) =
      conj (slotEnergyMultiplier K hK y) * slotEnergyMultiplier K hK y := by
  rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  apply congrArg Complex.ofReal
  change ‖1+(y:ℂ)‖^2/4 = ‖(2:ℂ)⁻¹ * (1+(y:ℂ))‖^2
  simp
  ring

theorem closing_domain_slot_second_exact (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    (∫ t : ℝ, t^2 ∂closingDomainSlotLaw K hK x) = ‖K x‖^2 := by
  have hy : ∀ᵐ y : spectrum ℂ (closingCayley K hK) ∂slotState K hK x, (y:ℂ) ≠ 1 := by
    simpa only [ae_iff,not_not] using closing_cayley_state_no_atom K hK (graphVector K x)
  rw [closingDomainSlotLaw,closing_cayley_law_energy_square _ _ measurable_subtype_coe
    (closing_cayley_spectral_norm K hK)]
  let w (y : spectrum ℂ (closingCayley K hK)) := if (y:ℂ)=1 then 0 else ‖1+(y:ℂ)‖^2/4
  apply Complex.ofReal_injective
  calc
    ((∫ y, w y ∂slotState K hK x : ℝ) : ℂ) = ∫ y, (w y : ℂ) ∂slotState K hK x := integral_complex_ofReal.symm
    _ = ∫ y, conj (slotEnergyMultiplier K hK y) * slotEnergyMultiplier K hK y ∂slotState K hK x := by
      apply integral_congr_ae
      filter_upwards [hy] with y h
      simpa only [w,if_neg h] using slot_energy_square K hK y
    _ = ⟪K x,K x⟫_ℂ := by rw [slot_mixed_test,energy_multiplier_on_graph]
    _ = _ := (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (K x)).trans (Complex.ofReal_pow ..).symm

end UV.SectorPlane
