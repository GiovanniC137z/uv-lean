import UV.ContinueOSPositiveWick
import UV.ContinueOSMassiveForm
import UV.ContinueOSGaussianModification
import UV.ContinueOSWickRealization

/-! The normalized Wick quartic and all boundary covariance-form domain
smearings are defined together on a single probability space. -/

noncomputable section
open MeasureTheory Matrix Set Filter
open scoped InnerProductSpace Topology

namespace UV

abbrev OSMassiveSamples := OSMassiveFormSpace → ℝ

/-- Full form-domain isonormal Gaussian and a jointly measurable
representative of its point transfers on the same probability space. -/
theorem osMassiveWick_joint_law {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃ (ν : Measure OSMassiveSamples) (F : OSQuarticSlot → OSMassiveSamples → ℝ),
      IsProbabilityMeasure ν ∧
      OSWickMoments ν (fun (h : OSMassiveFormSpace) (z : OSMassiveSamples) => z h) osMassiveHilbertCovariance.entry ∧
      OSWickMoments ν F (osQuarticCovariance m r) ∧
      (∀ i, F i =ᵐ[ν] (fun z => z (osQuarticFormSlot hm hr i))) ∧
      Measurable (fun p : OSFourSpace × OSMassiveSamples => F (.inr p.1) p.2) := by
  classical
  letI : Inhabited OSMassiveFormSpace := ⟨0⟩
  let Q := osMassiveHilbertCovariance
  obtain ⟨ν,hν,_⟩ := osPositiveGaussianProcess Q
  have hW := osPositiveProcess_wick Q ν hν
  haveI (I : Finset OSMassiveFormSpace) : IsProbabilityMeasure (Q.family I) :=
    @OSPositiveCovariance.law_probability _ Q I _ (Classical.decEq _) Subtype.val
  haveI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  let s := osQuarticFormSlot hm hr
  let p (z : OSMassiveSamples) := z ∘ s
  have hp : Measurable p := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  let μ := ν.map p
  have hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr) := by
    intro I
    rw [show μ.map I.restrict = ν.map (fun z => z ∘ (fun j : I => s j.val)) from
      Measure.map_map (Finset.measurable_restrict I) hp]
    letI : DecidableEq I := Classical.decEq _
    rw [osPositiveGaussian_projection Q ν hν]
    have hk : (fun i j : I => Q.entry (s i.val) (s j.val)) = fun i j => osQuarticCovariance m r i.val j.val :=
      funext₂ (fun i j => osQuarticFormSlot_inner hm hr i.val j.val)
    unfold OSPositiveCovariance.law osGaussianFamily osQuarticFiniteLaw
    congr 1
  obtain ⟨Z,hZ,hmod⟩ := osQuarticGaussian_joint_modification hm hr μ hμ
  let F : OSQuarticSlot → OSMassiveSamples → ℝ := Sum.elim (fun a z => z (s (.inl a))) (fun x z => Z x (p z))
  have he (i : OSQuarticSlot) : F i =ᵐ[ν] (fun z => z (s i)) := by
    cases i with
    | inl i => exact EventuallyEq.rfl
    | inr x => exact ae_of_ae_map hp.aemeasurable (hmod x)
  have hmom (l : List OSQuarticSlot) :
      osMonomial F l =ᵐ[ν] osMonomial (fun i (z : OSMassiveSamples) => z (s i)) l := by
    induction l with
    | nil => exact EventuallyEq.rfl
    | cons i l ih => exact (he i).mul ih
  have hrestricted := hW.reindex s
  have hKR : (fun i j => Q.entry (s i) (s j)) = osQuarticCovariance m r := funext₂ (osQuarticFormSlot_inner hm hr)
  rw [hKR] at hrestricted
  refine ⟨ν,F,inferInstance,hW,⟨fun l => (hrestricted.integrable l).congr (hmom l).symm,
    fun n l h => (integral_congr_ae (hmom l)).trans (hrestricted.moment n l h)⟩,he,?_⟩
  exact hZ.comp (measurable_fst.prodMk (hp.comp measurable_snd))

/-- A linear relation in the covariance-form domain holds almost surely
for the corresponding smeared boundary random variables. -/
theorem osMassiveField_linear_relation {ν : Measure OSMassiveSamples}
    (hW : OSWickMoments ν (fun h z => z h) osMassiveHilbertCovariance.entry)
    {ι : Type*} [Fintype ι] (s : ι → OSMassiveFormSpace) (t : ι → ℝ) (hlin : ∑ i, t i • s i = 0) :
    ∀ᵐ z ∂ν, ∑ i, t i * z (s i) = 0 := by
  let G (z : OSMassiveSamples) := ∑ i, t i * z (s i)
  let P (i j : ι) (z : OSMassiveSamples) := z (s i)*z (s j)
  have hi (i j : ι) : Integrable (P i j) ν := by
    exact (hW.integrable [s i,s j]).congr (Eventually.of_forall fun z => by simp [osMonomial,P])
  have hp (i j : ι) : (∫ z, P i j z ∂ν) = ⟪s i,s j⟫_ℝ := by
    simpa [P,osMonomial,osWickMoment,List.zipIdx,List.eraseIdx,osMassiveHilbertCovariance] using
      hW.moment 1 [s i,s j] (by simp)
  have he (z : OSMassiveSamples) : G z ^2 = ∑ i, ∑ j, (t i*t j)*P i j z := by
    simp only [G,sq,Finset.sum_mul,Finset.mul_sum,P]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have ha (i j : ι) := (hi i j).const_mul (t i*t j)
  have hb (i : ι) : Integrable (fun z => ∑ j, t i*t j*P i j z) ν := integrable_finset_sum _ (fun j _ => ha i j)
  have hG : Integrable (fun z => G z ^2) ν := by
    simp_rw [he]
    exact integrable_finset_sum _ (fun i _ => hb i)
  have hz : (∫ z, G z^2 ∂ν) = 0 := by
    simp_rw [he,integral_finset_sum Finset.univ (fun i _ => hb i)]
    have hstep (i : ι) : (∫ z, ∑ j, t i*t j*P i j z ∂ν) = ∑ j, t i*t j*⟪s i,s j⟫_ℝ := by
      rw [integral_finset_sum _ (fun j _ => ha i j)]
      simp only [integral_const_mul,hp]
    simp only [hstep]
    have hin : ⟪∑ i, t i • s i,∑ i, t i • s i⟫_ℝ = 0 := by rw [hlin]; simp
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,←mul_assoc] at hin
    simpa only [real_inner_comm (s _) (s _)] using hin
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (G z)) hG).mp hz] with z h
  exact sq_eq_zero_iff.mp h

private theorem osWick_form_moment {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {ζ : OSFourSpace → ℝ} (hc : Continuous ζ) (hk : HasCompactSupport ζ) (hn : 0 ≤ ζ)
    (v : ℝ) (Z : OSFourSpace → Ω → ℝ) (hZ : Measurable (fun p : OSFourSpace × Ω => Z p.1 p.2))
    (A : Ω → ℝ) (hA : Integrable A ν) {g : ℝ} (hg : 0 ≤ g) :
    let W := osSpatialPotential volume (fun x ω => ζ x * osWickQuartic v (Z x ω))
    Integrable A (osGibbsMeasure ν W g) := by
  intro W
  have hζ : Integrable ζ := hc.integrable_of_hasCompactSupport hk
  let D (x : OSFourSpace) (z : Ω) := ζ x * osWickQuartic v (Z x z)
  have hmeas : Measurable W := by
    have hD : Measurable (Function.uncurry D) := (hc.measurable.comp measurable_fst).mul
      ((by unfold osWickQuartic; fun_prop : Continuous (osWickQuartic v)).measurable.comp hZ)
    exact hD.stronglyMeasurable.integral_prod_left.measurable
  apply osGibbsMeasure_integrable (L := v^2/4 * ∫ x, ζ x) hmeas hA _ hg
  filter_upwards with z
  by_cases hi : Integrable (fun x => D x z)
  · have h := integral_mono (hζ.const_mul (-(v^2/4))) hi (fun x => by
      have he := osWick_quartic_density_lower (hn x) v (Z x z)
      dsimp [D,osWickQuartic]
      linarith)
    rw [integral_const_mul] at h
    simpa only [W,osSpatialPotential,D,neg_mul] using h
  · change _ ≤ ∫ x, D x z
    rw [integral_undef hi]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) (integral_nonneg hn))

/-- Integrability of every finite mixed moment implies integrability of
every polynomial, even on an infinite set of boundary smearings. -/
theorem osPolynomial_of_mixed_moments {ι : Type*} {μ : Measure (ι → ℝ)}
    (h : ∀ l : List ι, Integrable (osMonomial (fun i z => z i) l) μ) (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) μ := by
  have aux (q : MvPolynomial ι ℝ) : ∀ l : List ι,
      Integrable (fun z => osMonomial (fun i z => z i) l z * MvPolynomial.eval z q) μ := by
    induction q using MvPolynomial.induction_on with
    | C a =>
      intro l
      simp only [MvPolynomial.eval_C]
      exact (h l).mul_const a
    | add p q hp hq =>
      intro l
      simp only [map_add,mul_add]
      exact (hp l).add (hq l)
    | mul_X p i hp =>
      intro l
      apply (hp (i::l)).congr
      filter_upwards with z
      simp only [osMonomial,List.map_cons,List.prod_cons,map_mul,MvPolynomial.eval_X]
      ring
  simpa [osMonomial] using aux p []

/-- The fixed-depth Wick-ordered measure has all mixed polynomial
moments of covariance-form domain boundary smearings at every
nonnegative coupling, and the centered reflected boundary observable
has the strictly negative right slope at zero. -/
theorem osWickQuartic_fixed_depth {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {ζ : OSFourSpace → ℝ} (hc : Continuous ζ) (hk : HasCompactSupport ζ) (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x) :
    ∃ (ν : Measure OSMassiveSamples) (F : OSQuarticSlot → OSMassiveSamples → ℝ),
      IsProbabilityMeasure ν ∧ OSWickMoments ν F (osQuarticCovariance m r) ∧
      (∀ i, F i =ᵐ[ν] fun z => z (osQuarticFormSlot hm hr i)) ∧
      let K := osQuarticCovariance m r
      let v := osCoincidence m r
      let a : OSQuarticSlot := .inl .reflectedLocal
      let b : OSQuarticSlot := .inl .reflectedBump
      let c : OSQuarticSlot := .inl .localProbe
      let d : OSQuarticSlot := .inl .bump
      let A := fun z => (F a z*F b z-K a b)*(F c z*F d z-K c d)
      let W := osSpatialPotential volume (fun x z => ζ x*osWickQuartic v (F (.inr x) z))
      (∀ g : ℝ, 0 ≤ g → IsProbabilityMeasure (osGibbsMeasure ν W g) ∧
        1 ≤ osGibbsPartition ν W g ∧ osGibbsPartition ν W g ≤ Real.exp (g*(v^2/4*∫ x, ζ x)) ∧
        (∀ l : List OSMassiveFormSpace, Integrable (osMonomial (fun h z => z h) l) (osGibbsMeasure ν W g)) ∧
        ∀ p : MvPolynomial OSMassiveFormSpace ℝ, Integrable (fun z => MvPolynomial.eval z p) (osGibbsMeasure ν W g)) ∧
      HasDerivWithinAt (osGibbsExpectation ν W A) (osWickQuarticSlope m r ζ) (Ioi 0) 0 ∧
        ∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation ν W A g < 0 := by
  obtain ⟨ν,F,hν,hform,hW,hslot,hZ⟩ := osMassiveWick_joint_law hm hr
  refine ⟨ν,F,hν,hW,hslot,?_⟩
  obtain ⟨hprob,hslope,hneg⟩ := osWickQuartic_realization hm hr hc hk hn hz F hW hZ
  refine ⟨fun g hg => ?_,hslope,hneg⟩
  have hmix (l : List OSMassiveFormSpace) := osWick_form_moment hc hk hn (osCoincidence m r)
    (fun x ω => F (.inr x) ω) hZ _ (hform.integrable l) hg
  exact ⟨(hprob g hg).1,(hprob g hg).2.1,(hprob g hg).2.2,hmix,osPolynomial_of_mixed_moments hmix⟩

end UV
