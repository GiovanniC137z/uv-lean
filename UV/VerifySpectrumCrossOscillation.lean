import UV.ContinueSpectrumOscillatory

/-! Exact absolutely convergent transforms for embedded real resonances.
A compact time integral resolves the apparent singularity before exchange
with the Cauchy cosine transform. The same formula covers the threshold. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

private theorem verify_cosine_pair_primitive (k q a t : ℝ) :
    HasDerivAt (fun u : ℝ =>
      k*Real.sin (k*u)*Real.cos (q*(a-u))+
      q*Real.cos (k*u)*Real.sin (q*(a-u)))
      ((k^2-q^2)*(Real.cos (k*t)*Real.cos (q*(a-t)))) t := by
  have hk := (hasDerivAt_id t).const_mul k
  have hq := ((hasDerivAt_id t).const_sub a).const_mul q
  have h := (((hk.sin.const_mul k).mul hq.cos).add
    ((hk.cos.const_mul q).mul hq.sin))
  convert h using 1
  simp only [id_eq, mul_one]
  ring

theorem verify_cosine_pair_resonance {k q a : ℝ} (hq : 0 ≤ q) (hk : 0 < k)
    (hne : k ≠ q) (hsin : Real.sin (a*q) = 0) :
    k*Real.sin (a*k)*(k^2-q^2)⁻¹ =
      ∫ t in (0 : ℝ)..a, Real.cos (t*k)*Real.cos (q*(a-t)) := by
  have hI : IntervalIntegrable (fun t : ℝ =>
    (k^2-q^2)*(Real.cos (k*t)*Real.cos (q*(a-t)))) volume 0 a :=
    (by fun_prop : Continuous (fun t : ℝ =>
      (k^2-q^2)*(Real.cos (k*t)*Real.cos (q*(a-t))))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => verify_cosine_pair_primitive k q a t) hI
  have hz : k^2-q^2 ≠ 0 := by
    intro hz
    exact hne ((sq_eq_sq₀ hk.le hq).1 (sub_eq_zero.1 hz))
  rw [intervalIntegral.integral_const_mul] at h
  have hs' : Real.sin (q*a) = 0 := by rwa [mul_comm]
  simp only [sub_self, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, zero_mul,
    add_zero, sub_zero, hs'] at h
  have hN : k*Real.sin (a*k) =
      (k^2-q^2) * ∫ t in (0 : ℝ)..a, Real.cos (t*k)*Real.cos (q*(a-t)) := by
    rw [mul_comm a k, ← h]
    congr 1
    exact intervalIntegral.integral_congr (fun t _ => by rw [mul_comm k t])
  rw [hN, mul_right_comm, mul_inv_cancel₀ hz, one_mul]

private theorem verify_laplace_cosine_primitive (w q a t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-w*u) *
      (-w*Real.cos (q*(a-u))-q*Real.sin (q*(a-u))))
      ((w^2+q^2)*(Real.exp (-w*t)*Real.cos (q*(a-t)))) t := by
  have hw := ((hasDerivAt_id t).const_mul (-w)).exp
  have hq := ((hasDerivAt_id t).const_sub a).const_mul q
  have h := hw.mul ((hq.cos.const_mul (-w)).sub (hq.sin.const_mul q))
  convert h using 1
  simp only [Pi.sub_apply, id_eq, mul_one]
  ring

theorem verify_laplace_cosine_resonance {w q a : ℝ} (hw : 0 < w)
    (hsin : Real.sin (a*q) = 0) :
    (∫ t in (0 : ℝ)..a, Real.exp (-w*t)*Real.cos (q*(a-t))) =
      w*(Real.cos (a*q)-Real.exp (-w*a))/(w^2+q^2) := by
  have hI : IntervalIntegrable (fun t : ℝ =>
    (w^2+q^2)*(Real.exp (-w*t)*Real.cos (q*(a-t)))) volume 0 a :=
    (by fun_prop : Continuous (fun t : ℝ =>
      (w^2+q^2)*(Real.exp (-w*t)*Real.cos (q*(a-t))))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => verify_laplace_cosine_primitive w q a t) hI
  have hz : 0 < w^2+q^2 := by positivity
  rw [intervalIntegral.integral_const_mul] at h
  have hs' : Real.sin (q*a) = 0 := by rwa [mul_comm]
  simp only [sub_self, mul_zero, Real.cos_zero, Real.sin_zero, mul_one,
    sub_zero, Real.exp_zero, one_mul, hs'] at h
  apply (eq_div_iff hz.ne').2
  rw [mul_comm _ (w^2+q^2), h, mul_comm a q]
  ring

def verifyResonanceJoint (w q a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1^2+w^2)⁻¹ * Real.cos (p.2*p.1) * Real.cos (q*(a-p.2))

private theorem verify_resonance_joint_integrable {w : ℝ} (hw : 0 < w) (q a : ℝ) :
    Integrable (verifyResonanceJoint w q a)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) a))) := by
  have hk := resumeCauchy_integrable w hw
  have ha : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc 0 a) := integrable_const _
  apply (hk.mul_prod ha).mono'
  · exact (by unfold verifyResonanceJoint; fun_prop :
      Measurable (verifyResonanceJoint w q a)).aestronglyMeasurable
  · filter_upwards with p
    dsimp only [verifyResonanceJoint]
    simp only [norm_mul, mul_one, Real.norm_of_nonneg (by positivity : 0 ≤ (p.1^2+w^2)⁻¹)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _) |>.trans
      (by rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))

private theorem verify_resonance_pair_ae {w q a : ℝ} (ha : 0<a) (hq : 0≤q)
    (hsin : Real.sin (a*q) = 0) :
    (fun k : ℝ => k*Real.sin (a*k)*((k^2-q^2)⁻¹*(k^2+w^2)⁻¹)) =ᵐ[volume.restrict (Ioi 0)]
      fun k => ∫ t in Ioc 0 a, verifyResonanceJoint w q a (k,t) := by
  have hne : ∀ᵐ k : ℝ, k ≠ q := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using measure_singleton q
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hne] with k hk hneq
  change k*Real.sin (a*k)*((k^2-q^2)⁻¹*(k^2+w^2)⁻¹) =
    ∫ t in Ioc 0 a, (k^2+w^2)⁻¹*Real.cos (t*k)*Real.cos (q*(a-t))
  rw [← mul_assoc, verify_cosine_pair_resonance hq hk hneq hsin,
    intervalIntegral.integral_of_le ha.le]
  simp_rw [mul_assoc, integral_const_mul]
  ring

/-- At a sine-zero embedded pole, including the threshold, the apparent
pole cancels on a full-measure set and the actual integral is absolutely
convergent. -/
theorem verify_resonance_pair_integrable {w q a : ℝ} (hw : 0<w) (hq : 0≤q) (ha : 0<a)
    (hsin : Real.sin (a*q) = 0) :
    IntegrableOn (fun k : ℝ => k*Real.sin (a*k)*((k^2-q^2)⁻¹*(k^2+w^2)⁻¹)) (Ioi 0) := by
  have hinner : Integrable (fun k : ℝ => ∫ t in Ioc 0 a, verifyResonanceJoint w q a (k,t))
      (volume.restrict (Ioi 0)) :=
    (verify_resonance_joint_integrable hw q a).integral_prod_left
  exact hinner.congr (verify_resonance_pair_ae ha hq hsin).symm

theorem verify_resonance_pair_integral {w q a : ℝ} (hw : 0<w) (hq : 0≤q) (ha : 0<a)
    (hsin : Real.sin (a*q) = 0) :
    (∫ k : ℝ in Ioi 0, k*Real.sin (a*k)*((k^2-q^2)⁻¹*(k^2+w^2)⁻¹)) =
      (Real.pi/2)*(Real.cos (a*q)-Real.exp (-w*a))/(w^2+q^2) := by
  rw [integral_congr_ae (verify_resonance_pair_ae ha hq hsin)]
  have hi := verify_resonance_joint_integrable hw q a
  rw [integral_integral_swap (f:=fun k t => verifyResonanceJoint w q a (k,t)) hi]
  have hcos (t : ℝ) :
      (∫ k : ℝ in Ioi 0, verifyResonanceJoint w q a (k,t)) =
        (Real.pi/(2*w)*Real.exp (-w*|t|))*Real.cos (q*(a-t)) := by
    simp only [verifyResonanceJoint]
    rw [integral_mul_const]
    congr 1
    calc
      _ = ∫ k : ℝ in Ioi 0, Real.cos (k*t)/(k^2+w^2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro k _
        dsimp only
        rw [mul_comm t k, div_eq_mul_inv, mul_comm]
      _ = _ := continueCauchyCos_integral hw t
  simp_rw [hcos]
  have hpos :
      (∫ t in Ioc 0 a, (Real.pi/(2*w)*Real.exp (-w*|t|))*Real.cos (q*(a-t))) =
        (Real.pi/(2*w))*∫ t in Ioc 0 a, Real.exp (-w*t)*Real.cos (q*(a-t)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [abs_of_nonneg ht.1.le, mul_assoc]
  rw [hpos, ← intervalIntegral.integral_of_le ha.le, verify_laplace_cosine_resonance hw hsin]
  field_simp [hw.ne']

end UV.RevisionSpectrum
