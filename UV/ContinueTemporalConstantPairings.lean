import UV.ContinueTemporalMinimizer

/-! Exact normal readout and boundary flux of the two fixed curvature
pairings on one transverse sector channel. -/

noncomputable section

namespace UV.TemporalRay

open Real MeasureTheory

def constantCurvatureChannel (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) : NormalChannel where
  k := k
  a := fun _ => 1
  spatial := fun _ => 1
  temporal := fun _ => c
  aMin := 1
  aMax := 1
  spMin := 1
  spMax := 1
  parMax := c
  k_pos := hk
  aMin_pos := zero_lt_one
  spMin_pos := zero_lt_one
  continuous_a := continuous_const
  continuous_spatial := continuous_const
  continuous_temporal := continuous_const
  a_bound _ _ := ⟨le_rfl,le_rfl⟩
  spatial_bound _ _ := ⟨le_rfl,le_rfl⟩
  temporal_bound _ _ := ⟨hc,le_rfl⟩

private def constantCurvatureTransfer {k c y : ℝ} (hk : 0 < k) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    let D := constantCurvatureChannel k c hk hc
    NormalTransfer D.a (D.potential y) := by
  let γ := √(k^2+c*y)
  have hp : 0 < k^2+c*y := add_pos_of_pos_of_nonneg (sq_pos_of_pos hk) (mul_nonneg hc hy)
  have hγ : 0 < γ := sqrt_pos.mpr hp
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => exp (-γ*s)) (-γ*exp (-γ*r)) r := by
    simpa only [id_eq,mul_one,one_mul,mul_comm] using ((hasDerivAt_id r).const_mul (-γ)).exp
  have hgg : -γ * -γ = k^2+c*y := by rw [neg_mul_neg,← sq,sq_sqrt hp.le]
  exact {
    amplitude := fun r => exp (-γ*r)
    gradient := fun r => -γ*exp (-γ*r)
    amplitude_L2 := normal_ray_exp_decay_memLp hγ
    gradient_L2 := (normal_ray_exp_decay_memLp hγ).const_mul (-γ)
    has_gradient := fun r _ => hd r
    boundary_one := by simp
    flux_derivative := fun r _ => by
      simpa only [constantCurvatureChannel,NormalChannel.potential,modePotential,one_mul,
        ← mul_assoc (-γ) (-γ),hgg] using (hd r).const_mul (-γ) }

theorem constant_curvature_readout_flux {k c y : ℝ} (hk : 0 < k) (hc : 0 ≤ c) (hy : 0 ≤ y)
    {r : ℝ} (hr : 0 ≤ r) :
    let D := constantCurvatureChannel k c hk hc
    let u := normalMinimizingTransfer D y hy
    u.amplitude r = exp (-r*√(k^2+c*y)) ∧ boundaryFlux D.a u = √(k^2+c*y) := by
  let D := constantCurvatureChannel k c hk hc
  let u := normalMinimizingTransfer D y hy
  let v := constantCurvatureTransfer hk hc hy
  have he := transverse_amplitude_exact_difference D v u (fun s hs => normal_transfer_positive D hy v hs) hr
  have hf := transverse_flux_difference D hy hy v u
  simp only [sub_self,neg_zero,zero_mul,sub_eq_zero] at he hf
  refine ⟨he.trans ?_,hf.trans ?_⟩
  · change exp (-√(k^2+c*y)*r) = exp (-r*√(k^2+c*y))
    congr 1
    ring
  · simp [v,constantCurvatureTransfer,boundaryFlux,constantCurvatureChannel,D]

/-- At nonzero carrier frequency the temporal pairing is strictly more
attenuating. Both branches have identical static extension and flux. -/
theorem temporal_spatial_pairings_compare {k r : ℝ} (hk : 0 < k) (hr : 0 < r) (ω : ℝ) :
    let full := constantCurvatureChannel k 1 hk zero_le_one
    let spatial := constantCurvatureChannel k 0 hk le_rfl
    let U := fun D => normalMinimizingTransfer D (ω^2) (sq_nonneg _)
    (U full).amplitude r = exp (-r*√(k^2+ω^2)) ∧
    (U spatial).amplitude r = exp (-r*k) ∧
    boundaryFlux full.a (U full) = √(k^2+ω^2) ∧ boundaryFlux spatial.a (U spatial) = k ∧
    (ω ≠ 0 → (U full).amplitude r < (U spatial).amplitude r) ∧
    (ω = 0 → (U full).amplitude r = (U spatial).amplitude r ∧
      boundaryFlux full.a (U full) = boundaryFlux spatial.a (U spatial)) := by
  have hf := constant_curvature_readout_flux hk (c := 1) zero_le_one (sq_nonneg ω) hr.le
  have hs := constant_curvature_readout_flux hk (c := 0) le_rfl (sq_nonneg ω) hr.le
  simp only [one_mul] at hf
  simp only [zero_mul,add_zero,sqrt_sq hk.le] at hs
  refine ⟨hf.1,hs.1,hf.2,hs.2,fun hω => ?_,fun hω => ?_⟩
  · rw [hf.1,hs.1]
    apply exp_lt_exp.mpr
    apply mul_lt_mul_of_neg_left _ (neg_neg_of_pos hr)
    have h : k^2 < k^2+ω^2 := lt_add_of_pos_right _ (sq_pos_of_ne_zero hω)
    simpa only [sqrt_sq hk.le] using Real.sqrt_lt_sqrt (sq_nonneg k) h
  · rw [hf.1,hs.1,hf.2,hs.2,hω]
    simp [sqrt_sq hk.le]

end UV.TemporalRay
