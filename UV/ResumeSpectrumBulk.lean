import UV.RevisionSpectrumBulk

/-! Exact boundary Stieltjes representation of the positive normal comparison.
All integrals are evaluated from the displayed atom and continuum density;
no spectral representation is assumed. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

theorem resumeCauchy_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun k : ℝ => (k^2+c^2)⁻¹) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun k : ℝ => (1+k^2)⁻¹) 0 (inv_pos.mpr hc)).mpr (by simpa using
    (integrable_inv_one_add_sq.integrableOn (s := Ioi 0)))
  have hh : IntegrableOn (fun x : ℝ => (c^2)⁻¹ * (1+(c⁻¹*x)^2)⁻¹) (Ioi 0) := h.const_mul _
  refine hh.congr_fun ?_ measurableSet_Ioi
  intro k _
  change (c^2)⁻¹ * (1+(c⁻¹*k)^2)⁻¹ = (k^2+c^2)⁻¹
  have hne : 1+(c⁻¹*k)^2 ≠ 0 := by positivity
  have hneq : k^2+c^2 ≠ 0 := by positivity
  field_simp
  ring

theorem resumeCauchy_integral (c : ℝ) (hc : 0 < c) :
    (∫ k : ℝ in Ioi 0, (k^2+c^2)⁻¹) = Real.pi/(2*c) := by
  have hne (k : ℝ) : k^2+c^2 ≠ 0 := by positivity
  calc
    _ = ∫ k : ℝ in Ioi 0, (c^2)⁻¹ * (1+(c⁻¹*k)^2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro k _
      have hnes : 1+(c⁻¹*k)^2 ≠ 0 := by positivity
      field_simp
      ring
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi
        (fun k : ℝ => (1+k^2)⁻¹) 0 (inv_pos.mpr hc)]
      simp only [mul_zero, inv_inv, smul_eq_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
      field_simp


theorem resumeCauchyPair_integrable {c w : ℝ} (hc : 0<c) (hw : 0<w) :
    IntegrableOn (fun k : ℝ => (k^2+c^2)⁻¹ * (k^2+w^2)⁻¹) (Ioi 0) := by
  apply ((resumeCauchy_integrable c hc).const_mul ((w^2)⁻¹)).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => (k^2+c^2)⁻¹ * (k^2+w^2)⁻¹)).aestronglyMeasurable
  · filter_upwards with k
    rw [Real.norm_of_nonneg (by positivity)]
    have hi : (k^2+w^2)⁻¹ ≤ (w^2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith [sq_nonneg k])
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (k^2+c^2)⁻¹)

theorem resumeCauchyPair_integral {c w : ℝ} (hc : 0<c) (hw : 0<w) (hcw : c≠w) :
    (∫ k : ℝ in Ioi 0, (k^2+c^2)⁻¹ * (k^2+w^2)⁻¹) =
      Real.pi/(2*c*w*(c+w)) := by
  have hdiff : w^2-c^2 ≠ 0 := by
    intro h
    have he := (sq_eq_sq₀ hw.le hc.le).mp (sub_eq_zero.mp h)
    exact hcw he.symm
  have he (k : ℝ) : (k^2+c^2)⁻¹ * (k^2+w^2)⁻¹ =
      (w^2-c^2)⁻¹ * ((k^2+c^2)⁻¹ - (k^2+w^2)⁻¹) := by
    have h₁ : k^2+c^2≠0 := by positivity
    have h₂ : k^2+w^2≠0 := by positivity
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub (resumeCauchy_integrable c hc) (resumeCauchy_integrable w hw),
    resumeCauchy_integral c hc, resumeCauchy_integral w hw]
  field_simp
  ring

theorem resumeCauchyTriple_integrable {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) :
    IntegrableOn (fun k : ℝ => k^2 / ((k^2+u^2)*(k^2+v^2)*(k^2+w^2))) (Ioi 0) := by
  apply (resumeCauchyPair_integrable hv hw).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => k^2 / ((k^2+u^2)*(k^2+v^2)*(k^2+w^2)))).aestronglyMeasurable
  · filter_upwards with k
    rw [Real.norm_of_nonneg (by positivity)]
    have h₁ : 0 < k^2+u^2 := by positivity
    have h₂ : 0 < (k^2+v^2)*(k^2+w^2) := by positivity
    rw [← mul_inv, ← one_div]
    rw [mul_assoc]
    apply (div_le_div_iff₀ (mul_pos h₁ h₂) h₂).mpr
    nlinarith [mul_nonneg (sq_nonneg u) h₂.le]

theorem resumeCauchyTriple_integral {u v w : ℝ}
    (hu : 0<u) (hv : 0<v) (hw : 0<w) (huv : u<v) (huw : u≠w) (hvw : v≠w) :
    (∫ k : ℝ in Ioi 0, k^2 / ((k^2+u^2)*(k^2+v^2)*(k^2+w^2))) =
      Real.pi/(2*(u+v)*(u+w)*(v+w)) := by
  have hdiff : v^2-u^2≠0 := ne_of_gt (sub_pos.mpr ((sq_lt_sq₀ hu.le hv.le).mpr huv))
  have he (k : ℝ) : k^2 / ((k^2+u^2)*(k^2+v^2)*(k^2+w^2)) =
      (v^2-u^2)⁻¹ *
        (v^2*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹) -
          u^2*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) := by
    have h₁ : k^2+u^2≠0 := by positivity
    have h₂ : k^2+v^2≠0 := by positivity
    have h₃ : k^2+w^2≠0 := by positivity
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub
    ((resumeCauchyPair_integrable hv hw).const_mul (v^2))
    ((resumeCauchyPair_integrable hu hw).const_mul (u^2)),
    integral_const_mul, integral_const_mul,
    resumeCauchyPair_integral hv hw hvw, resumeCauchyPair_integral hu hw huw]
  field_simp
  ring

theorem resume_bulk_spectral_substitution (M₂ : ℝ) (f : ℝ → ℝ) :
    (∫ s : ℝ in Ioi M₂, f s) = ∫ k : ℝ in Ioi 0, (2*k)*f (k^2+M₂) := by
  have hder : ∀ k ∈ Ioi (0:ℝ), HasDerivWithinAt (fun k : ℝ => k^2+M₂) (2*k) (Ioi 0) k := by
    intro k _
    exact (by simpa using (((hasDerivAt_id k).pow 2).add_const M₂).hasDerivWithinAt)
  have hinj : InjOn (fun k : ℝ => k^2+M₂) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro r hr k hk h
    exact add_lt_add_right ((sq_lt_sq₀ hr.le hk.le).mpr h) M₂
  have himage : (fun k : ℝ => k^2+M₂) '' Ioi 0 = Ioi M₂ := by
    ext s
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact (show M₂<k^2+M₂ by linarith [sq_pos_of_pos (mem_Ioi.mp hk)])
    · intro hs
      have h : 0<s-M₂ := sub_pos.mpr hs
      exact ⟨Real.sqrt (s-M₂),Real.sqrt_pos.mpr h, by
        change Real.sqrt (s-M₂)^2+M₂=s
        rw [Real.sq_sqrt h.le]
        ring⟩
  have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj f
  rw [himage] at hc
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro k hk
  change 0<k at hk
  dsimp only
  rw [abs_of_pos (by positivity : 0<2*k), smul_eq_mul]

theorem resume_bulk_boundary_stieltjes_integrable {β b M₂ x : ℝ}
    (hβ : 0<β) (hb : b<M₂) (hM : 0≤M₂) (hx : 0<x) :
    IntegrableOn (fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s)) (Ioi M₂) := by
  apply ((bulkBoundary_mass hβ hb).1.div_const x).mono'
  · exact (by unfold bulkBoundaryDensity; fun_prop :
      Measurable (fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0≤s := hM.trans hs.le
    have hd₀ : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by
      unfold bulkBoundaryDensity
      positivity
    rw [Real.norm_of_nonneg (div_nonneg hd₀ (by positivity))]
    exact div_le_div_of_nonneg_left hd₀ hx (by linarith)

/-- The actual weighted continuum integral, evaluated away from a temporary
coincident partial-fraction factor. The final theorem removes this condition
by dominated convergence. -/
theorem resume_bulk_boundary_continuum_noncoincident {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x)
    (hvw : bulkKappa β b M₂ + β ≠ Real.sqrt (x+M₂)) :
    (∫ s : ℝ in Ioi M₂,
      bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s)) =
      β/((2*bulkKappa β b M₂+β)*
        (bulkKappa β b M₂+Real.sqrt (x+M₂))*
        (bulkKappa β b M₂+β+Real.sqrt (x+M₂))) := by
  let u := bulkKappa β b M₂
  let v := u+β
  let w := Real.sqrt (x+M₂)
  have hu : 0<u := bulkKappa_pos hβ hb
  have hv : 0<v := by dsimp [v]; positivity
  have hM : 0<M₂ := hb₀.trans hb
  have hw : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by positivity)
  have huv : u<v := by dsimp [v]; linarith
  have huv' : u*v=M₂-b := by
    dsimp [v,u]
    nlinarith [bulkKappa_sq_add (β:=β) hb]
  have hup : u^2<M₂ := by
    have hp := (bulkPole_unique hβ hb).1
    unfold bulkPole at hp
    change b < M₂-u^2 at hp
    linarith
  have huw : u≠w := by intro h; rw [h] at hup; linarith
  have hsplit (k : ℝ) : (b-(k^2+M₂))^2+(β*k)^2 = (k^2+u^2)*(k^2+v^2) := by
    have hh : b-(k^2+M₂)=-(k^2+u*v) := by linarith
    rw [hh]
    dsimp [v]
    ring
  rw [resume_bulk_spectral_substitution M₂]
  have he : (∫ k : ℝ in Ioi 0,
      (2*k)*(bulkBoundaryDensity β (Real.sqrt (k^2+M₂-M₂)) (b-(k^2+M₂))/(x+(k^2+M₂)))) =
      (2*β/Real.pi) * ∫ k : ℝ in Ioi 0,
        k^2/((k^2+u^2)*(k^2+v^2)*(k^2+w^2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro k hk
    change 0<k at hk
    dsimp only
    rw [show k^2+M₂-M₂=k^2 by ring, Real.sqrt_sq hk.le]
    unfold bulkBoundaryDensity
    rw [hsplit, show x+(k^2+M₂)=k^2+w^2 by linarith]
    have h₁ : k^2+u^2≠0 := by positivity
    have h₂ : k^2+v^2≠0 := by positivity
    have h₃ : k^2+w^2≠0 := by positivity
    field_simp
  rw [he, resumeCauchyTriple_integral hu hv hw huv huw hvw]
  change (2*β/Real.pi) * (Real.pi/(2*(u+v)*(u+w)*(v+w))) = _
  have h₁ : u+v≠0 := by positivity
  have h₂ : u+w≠0 := by positivity
  have h₃ : v+w≠0 := by positivity
  dsimp [v,u,w] at *
  field_simp
  ring

theorem resume_bulk_boundary_representation_noncoincident {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x)
    (hvw : bulkKappa β b M₂+β≠Real.sqrt (x+M₂)) :
    bulkResidue β b M₂/(x+bulkPole β b M₂) +
      (∫ s : ℝ in Ioi M₂,
        bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s)) =
      (x+b+β*Real.sqrt (x+M₂))⁻¹ := by
  let u := bulkKappa β b M₂
  let w := Real.sqrt (x+M₂)
  have hu : 0<u := bulkKappa_pos hβ hb
  have hM : 0<M₂ := hb₀.trans hb
  have hw : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by positivity)
  have hq : u^2+β*u=M₂-b := bulkKappa_sq_add hb
  have hup : u<w := by
    have hp := (bulkPole_unique hβ hb).1
    unfold bulkPole at hp
    change b<M₂-u^2 at hp
    nlinarith
  have hZ : bulkResidue β b M₂=2*u/(2*u+β) := by
    unfold bulkResidue
    change (1+β/(2*u))⁻¹=2*u/(2*u+β)
    have hd : 1+β/(2*u)≠0 := by positivity
    field_simp
  have hpole : x+bulkPole β b M₂=(w-u)*(w+u) := by
    unfold bulkPole
    change x+(M₂-u^2)=_
    nlinarith
  have hden : x+b+β*w=(w-u)*(w+u+β) := by nlinarith
  rw [resume_bulk_boundary_continuum_noncoincident hβ hb₀ hb hx hvw, hZ, hpole]
  change (2*u/(2*u+β))/((w-u)*(w+u)) +
    β/((2*u+β)*(u+w)*(u+β+w))=(x+b+β*w)⁻¹
  rw [hden]
  have h₁ : 2*u+β≠0 := by positivity
  have h₂ : w-u≠0 := sub_ne_zero.mpr hup.ne'
  have h₃ : w+u≠0 := by positivity
  have h₄ : u+w≠0 := by positivity
  have h₅ : u+β+w≠0 := by positivity
  have h₆ : w+u+β≠0 := by positivity
  field_simp
  ring

/-- The boundary continuum converges at every positive Euclidean sampling
point along the actual positive shifts used to remove coincident factors. -/
theorem resume_bulk_boundary_shift_limit {β b M₂ x : ℝ}
    (hβ : 0<β) (hb : b<M₂) (hM : 0≤M₂) (hx : 0<x) :
    Tendsto (fun n : ℕ => ∫ s : ℝ in Ioi M₂,
      bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+1/((n:ℝ)+1)+s))
      atTop (𝓝 (∫ s : ℝ in Ioi M₂,
        bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s))) := by
  let ρ := fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)
  have hm : IntegrableOn (fun s => ρ s/x) (Ioi M₂) := (bulkBoundary_mass hβ hb).1.div_const x
  apply tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Ioi M₂)) (fun s => ρ s/x)
  · intro n
    exact (by dsimp [ρ]; unfold bulkBoundaryDensity; fun_prop :
      Measurable (fun s => ρ s/(x+1/((n:ℝ)+1)+s))).aestronglyMeasurable
  · exact hm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0≤s := hM.trans hs.le
    have hρ : 0≤ρ s := by dsimp [ρ]; unfold bulkBoundaryDensity; positivity
    rw [Real.norm_of_nonneg (div_nonneg hρ (by positivity))]
    exact div_le_div_of_nonneg_left hρ hx (by
      have hh : 0≤1/((n:ℝ)+1) := by positivity
      linarith)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0≤s := hM.trans hs.le
    have ht : Tendsto (fun n : ℕ => x+1/((n:ℝ)+1)+s) atTop (𝓝 (x+s)) := by
      simpa using (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).add_const s
    exact tendsto_const_nhds.div ht (by positivity)

/-- Exact boundary block of the positive bulk spectral representation,
including the degenerate partial-fraction parameter by dominated convergence. -/
theorem resume_bulk_boundary_stieltjes {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) :
    IntegrableOn (fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s)) (Ioi M₂) ∧
    bulkResidue β b M₂/(x+bulkPole β b M₂) +
      (∫ s : ℝ in Ioi M₂,
        bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)/(x+s)) =
      (x+b+β*Real.sqrt (x+M₂))⁻¹ := by
  have hM : 0<M₂ := hb₀.trans hb
  refine ⟨resume_bulk_boundary_stieltjes_integrable hβ hb hM.le hx,?_⟩
  by_cases hco : bulkKappa β b M₂+β=Real.sqrt (x+M₂)
  · let xn := fun n : ℕ => x+1/((n:ℝ)+1)
    have hxn : Tendsto xn atTop (𝓝 x) := by
      simpa [xn] using tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hxp (n : ℕ) : 0<xn n := by dsimp [xn]; positivity
    have hne (n : ℕ) : bulkKappa β b M₂+β≠Real.sqrt (xn n+M₂) := by
      intro heq
      have hs := Real.sq_sqrt (show 0≤xn n+M₂ by positivity)
      have hs' := Real.sq_sqrt (show 0≤x+M₂ by positivity)
      rw [← heq] at hs
      rw [← hco] at hs'
      have he : xn n=x := by linarith
      have hh : 0<1/((n:ℝ)+1) := by positivity
      dsimp [xn] at he
      linarith
    have hZ : Tendsto (fun _ : ℕ => bulkResidue β b M₂) atTop
        (𝓝 (bulkResidue β b M₂)) := tendsto_const_nhds
    have hL := (hZ.div (hxn.add_const (bulkPole β b M₂))
      (show x+bulkPole β b M₂≠0 by
        have hp := (bulkPole_unique hβ hb).1
        exact (add_pos hx (hb₀.trans hp)).ne' )).add (resume_bulk_boundary_shift_limit hβ hb hM.le hx)
    have hR : Tendsto (fun n => (xn n+b+β*Real.sqrt (xn n+M₂))⁻¹) atTop
        (𝓝 ((x+b+β*Real.sqrt (x+M₂))⁻¹)) := by
      apply Tendsto.inv₀ _ (by positivity)
      exact (hxn.add_const b).add (tendsto_const_nhds.mul
        (Real.continuous_sqrt.continuousAt.tendsto.comp (hxn.add_const M₂)))
    apply tendsto_nhds_unique hL
    apply hR.congr'
    exact Eventually.of_forall fun n =>
      (resume_bulk_boundary_representation_noncoincident hβ hb₀ hb (hxp n) (hne n)).symm
  · exact resume_bulk_boundary_representation_noncoincident hβ hb₀ hb hx hco

end UV.RevisionSpectrum
