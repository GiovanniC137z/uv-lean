import UV.ContinueCayleyForwardFamily

/-! Polarization of the exact real-axis domain moments, including
the off-diagonal first and second energy entries. -/

noncomputable section
namespace UV.SectorPlane
open MeasureTheory Set Matrix
open scoped InnerProductSpace ComplexConjugate

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq ι] [CompleteSpace H] in
private theorem forward_cross_form (u v : ι→H) (y : ι→ℂ) :
    closingFiniteForm (fun i j => ⟪u i,v j⟫_ℂ) y=⟪∑ i,y i • u i,∑ j,y j • v j⟫_ℂ := by
  simp only [closingFiniteForm,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem forward_density_moments (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (h₂ : Integrable (fun t : ℝ => t^2) (closingTraceLaw M)) (i j : ι) :
    Integrable (fun t : ℝ => (t:ℂ)*closingMatrixDensity M t i j) (closingControlMeasure M) ∧
    Integrable (fun t : ℝ => (t:ℂ)^2*closingMatrixDensity M t i j) (closingControlMeasure M) := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let μ := closingNaimarkMeasure M
  let V := closingNaimarkColumn M hM
  let L := fun n => closingNaimarkEnergy M ⟨V n,closing_column_energy_domain M hM h₂ n⟩
  have hV (n : ι) : (⇑(V n))=ᵐ[μ] fun p => (1:ℂ)*closingColumnValue M n p := by
    simpa only [one_mul] using closing_naimark_column_ae M hM n
  have hL (n : ι) : (⇑(L n))=ᵐ[μ] fun p => (p.2:ℂ)*closingColumnValue M n p := by
    have hl := sourceL2Multiplier_coe μ (fun p : ι×ℝ => (p.2:ℂ)) ⟨V n,closing_column_energy_domain M hM h₂ n⟩
    filter_upwards [hl,closing_naimark_column_ae M hM n] with p h hp
    exact h.trans (congrArg ((p.2:ℂ)* ·) hp)
  constructor
  · simpa only [star_one,one_mul] using
      (closing_weighted_columns_integrable_pairing M hM i j (fun _ => 1) (fun t => (t:ℂ)) (V i) (L j) (hV i) (hL j)).1
  · simpa only [Complex.star_def,Complex.conj_ofReal,←pow_two] using
      (closing_weighted_columns_integrable_pairing M hM i j (fun t => (t:ℂ)) (fun t => (t:ℂ)) (L i) (L j) (hL i) (hL j)).1

theorem closing_forward_family_moments (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : ι→K.domain)
    (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (h₂ : Integrable (fun t : ℝ => t^2) (closingTraceLaw M))
    (hquad : ∀ y : ι→ℂ, ∀ s, MeasurableSet s → closingFiniteForm (fun i j => M i j s) y =
      ((closingDomainSlotLaw K hK (∑ i,y i • x i)).real s:ℂ)) :
    (∀ i j, closingMeasureEntryIntegral M (fun t : ℝ => (t:ℂ)) i j = ⟪(x i:H),K (x j)⟫_ℂ) ∧
    (∀ i j, closingMeasureEntryIntegral M (fun t : ℝ => (t:ℂ)^2) i j = ⟪K (x i),K (x j)⟫_ℂ) := by
  have hsum (y : ι→ℂ) : (↑(∑ i,y i • x i) : H)=∑ i,y i • (x i:H) := by simp
  have hk (y : ι→ℂ) : K (∑ i,y i • x i)=∑ i,y i • K (x i) := by change K.toFun _=_;simp
  have hi (v : K.domain) : ((⟪(v:H),K v⟫_ℂ).re : ℂ)=⟪(v:H),K v⟫_ℂ := by
    have hh := closing_symmetric_of_selfAdjoint K hK v v
    have hconj := inner_conj_symm (𝕜:=ℂ) (K v) (v:H)
    rw [hh] at hconj
    exact Complex.conj_eq_iff_re.mp hconj
  constructor
  · have H : closingMeasureEntryIntegral M (fun t : ℝ => (t:ℂ))=(fun i j => ⟪(x i:H),K (x j)⟫_ℂ) := by
      apply closing_finite_form_ext
      intro y
      rw [closing_forward_form_test M hM _ y (hquad y) _ (fun i j => (forward_density_moments M hM h₂ i j).1),
        integral_complex_ofReal,closing_domain_slot_first_exact,hi,hsum,hk,forward_cross_form]
    exact fun i j => congrFun (congrFun H i) j
  · have H : closingMeasureEntryIntegral M (fun t : ℝ => (t:ℂ)^2)=(fun i j => ⟪K (x i),K (x j)⟫_ℂ) := by
      apply closing_finite_form_ext
      intro y
      rw [closing_forward_form_test M hM _ y (hquad y) _ (fun i j => (forward_density_moments M hM h₂ i j).2)]
      simp_rw [←Complex.ofReal_pow]
      rw [integral_complex_ofReal,closing_domain_slot_second_exact,hk,forward_cross_form,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    exact fun i j => congrFun (congrFun H i) j

end UV.SectorPlane
