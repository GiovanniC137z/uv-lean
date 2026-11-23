import UV.ContinueTemporalMinimizer

/-! Ray-only material coefficients and complex transverse Fourier amplitudes.
Both real quadratures have the same normal energy at every squared frequency. -/

noncomputable section

namespace UV.TemporalRay

open Real MeasureTheory Set Filter

/-- Coefficients only specified on the normal ray extend constantly through
the boundary; they are evaluated on the original ray in every energy. -/
def normalChannelOfRay {k aMin aMax spMin spMax parMax : ℝ}
    (a spatial temporal : Ici (0:ℝ) → ℝ) (hk : 0 < k) (haMin : 0 < aMin) (hspMin : 0 < spMin)
    (ha : Continuous a) (hsp : Continuous spatial) (ht : Continuous temporal)
    (ab : ∀ r, a r ∈ Icc aMin aMax) (sb : ∀ r, spatial r ∈ Icc spMin spMax)
    (tb : ∀ r, temporal r ∈ Icc 0 parMax) : NormalChannel where
  k := k
  a r := a ⟨max r 0,le_max_right r (0:ℝ)⟩
  spatial r := spatial ⟨max r 0,le_max_right r (0:ℝ)⟩
  temporal r := temporal ⟨max r 0,le_max_right r (0:ℝ)⟩
  aMin := aMin
  aMax := aMax
  spMin := spMin
  spMax := spMax
  parMax := parMax
  k_pos := hk
  aMin_pos := haMin
  spMin_pos := hspMin
  continuous_a := ha.comp ((continuous_id.max continuous_const).subtype_mk _)
  continuous_spatial := hsp.comp ((continuous_id.max continuous_const).subtype_mk _)
  continuous_temporal := ht.comp ((continuous_id.max continuous_const).subtype_mk _)
  a_bound r _ := ab ⟨max r 0,le_max_right r (0:ℝ)⟩
  spatial_bound r _ := sb ⟨max r 0,le_max_right r (0:ℝ)⟩
  temporal_bound r _ := tb ⟨max r 0,le_max_right r (0:ℝ)⟩

theorem normalChannelOfRay_coefficients {k aMin aMax spMin spMax parMax : ℝ}
    (a spatial temporal : Ici (0:ℝ) → ℝ) (hk : 0 < k) (haMin : 0 < aMin) (hspMin : 0 < spMin)
    (ha : Continuous a) (hsp : Continuous spatial) (ht : Continuous temporal)
    (ab : ∀ r, a r ∈ Icc aMin aMax) (sb : ∀ r, spatial r ∈ Icc spMin spMax)
    (tb : ∀ r, temporal r ∈ Icc 0 parMax) (r : Ici (0:ℝ)) :
    let D := normalChannelOfRay a spatial temporal hk haMin hspMin ha hsp ht ab sb tb
    D.a r = a r ∧ D.spatial r = spatial r ∧ D.temporal r = temporal r := by
  have he : (⟨max r.val 0,le_max_right r.val (0:ℝ)⟩ : Ici (0:ℝ)) = r :=
    Subtype.ext (max_eq_left (show (0:ℝ) ≤ r.val from r.property))
  exact ⟨congrArg a he,congrArg spatial he,congrArg temporal he⟩

structure ComplexNormalProfile where
  value : ℝ → ℂ
  slope : ℝ → ℂ
  value_L2 : MemLp value 2 normalRayMeasure
  slope_L2 : MemLp slope 2 normalRayMeasure
  primitive : ∀ r ≥ 0, value r = value 0 + ∫ t in (0:ℝ)..r, slope t

def ComplexNormalProfile.component (v : ComplexNormalProfile) (L : ℂ →L[ℝ] ℝ) : NormalEnergyProfile where
  value r := L (v.value r)
  slope r := L (v.slope r)
  value_L2 := L.comp_memLp' v.value_L2
  slope_L2 := L.comp_memLp' v.slope_L2
  primitive r hr := by
    rw [v.primitive r hr,map_add,L.intervalIntegral_comp_comm (normal_ray_interval_integrable v.slope_L2 le_rfl hr)]

def complexNormalFormEnergy (D : NormalChannel) (y : ℝ) (v : ComplexNormalProfile) : ℝ :=
  (∫ r in Ioi (0:ℝ), D.a r*‖v.slope r‖^2 + D.potential y r*‖v.value r‖^2)/2

theorem normal_complex_energy_split (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y) (v : ComplexNormalProfile) :
    complexNormalFormEnergy D y v =
      normalFormEnergy D y (v.component Complex.reCLM) + normalFormEnergy D y (v.component Complex.imCLM) := by
  let vr := v.component Complex.reCLM
  let vi := v.component Complex.imCLM
  have he : (fun r => D.a r*‖v.slope r‖^2 + D.potential y r*‖v.value r‖^2) =
      fun r => normalEnergyDensity D y vr r + normalEnergyDensity D y vi r := by
    funext r
    simp only [Complex.sq_norm,Complex.normSq_apply,normalEnergyDensity,vr,vi,
      ComplexNormalProfile.component,Complex.reCLM_apply,Complex.imCLM_apply]
    ring
  unfold complexNormalFormEnergy normalFormEnergy
  rw [he]
  change (∫ t, normalEnergyDensity D y vr t + normalEnergyDensity D y vi t ∂normalRayMeasure)/2 =
    (∫ t, normalEnergyDensity D y vr t ∂normalRayMeasure)/2 +
      (∫ t, normalEnergyDensity D y vi t ∂normalRayMeasure)/2
  rw [integral_add (normal_energy_density_integrable D hy vr) (normal_energy_density_integrable D hy vi)]
  ring

def NormalEnergyProfile.toComplex (v : NormalEnergyProfile) : ComplexNormalProfile where
  value r := (v.value r : ℂ)
  slope r := (v.slope r : ℂ)
  value_L2 := Complex.ofRealCLM.comp_memLp' v.value_L2
  slope_L2 := Complex.ofRealCLM.comp_memLp' v.slope_L2
  primitive r hr := by
    change Complex.ofRealCLM (v.value r) = Complex.ofRealCLM (v.value 0) +
      ∫ t in (0:ℝ)..r, Complex.ofRealCLM (v.slope t)
    rw [v.primitive r hr,map_add,Complex.ofRealCLM.intervalIntegral_comp_comm
      (normal_ray_interval_integrable v.slope_L2 le_rfl hr)]

theorem normal_complex_energy_attained (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y) :
    let u := (normalMinimizingTransfer D y hy).toNormalProfile.toEnergyProfile
    u.toComplex.value 0 = 1 ∧ complexNormalFormEnergy D y u.toComplex = normalFormEnergy D y u := by
  intro u
  refine ⟨by simp [u,NormalEnergyProfile.toComplex,NormalProfile.toEnergyProfile,
    (normalMinimizingTransfer D y hy).boundary_one],?_⟩
  simp only [complexNormalFormEnergy,normalFormEnergy,normalEnergyDensity,NormalEnergyProfile.toComplex,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Minimization against every complex weak profile with boundary value one.
Equality determines the complex values everywhere and their slopes almost everywhere. -/
theorem normal_complex_minimum_unique (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (v : ComplexNormalProfile) (hv : v.value 0 = 1) :
    let u := normalMinimizingTransfer D y hy
    let E := normalFormEnergy D y u.toNormalProfile.toEnergyProfile
    E ≤ complexNormalFormEnergy D y v ∧
    (complexNormalFormEnergy D y v = E → (∀ r ≥ 0, v.value r = (u.amplitude r : ℂ)) ∧
      v.slope =ᵐ[normalRayMeasure] fun r => (u.gradient r : ℂ)) := by
  let vr := v.component Complex.reCLM
  let vi := v.component Complex.imCLM
  have h0 : vr.value 0 = 1 := by simp [vr,ComplexNormalProfile.component,hv]
  have h0i : vi.value 0 = 0 := by simp [vi,ComplexNormalProfile.component,hv]
  have hR := normal_minimizes_full_form D hy vr h0
  have hI := normal_form_energy_nonneg D hy vi
  have hs := normal_complex_energy_split D hy v
  intro u E
  change E ≤ normalFormEnergy D y vr at hR
  change complexNormalFormEnergy D y v = normalFormEnergy D y vr + normalFormEnergy D y vi at hs
  refine ⟨by linarith only [hR,hI,hs],fun he => ?_⟩
  have hre : normalFormEnergy D y vr = E := by linarith only [hR,hI,hs,he]
  have hze : normalFormEnergy D y vi = 0 := by linarith only [hre,hs,he]
  obtain ⟨hgr,hvr⟩ := normal_minimizer_unique D hy u vr h0 hre
  have hgi := normal_zero_energy_slope D hy vi hze
  refine ⟨fun r hr => Complex.ext (hvr r hr) ?_,hgr.and hgi |>.mono fun t h => Complex.ext h.1 h.2⟩
  change vi.value r = 0
  rw [vi.primitive r hr,h0i,zero_add,intervalIntegral.integral_of_le hr]
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hgi)]
  simp

end UV.TemporalRay
