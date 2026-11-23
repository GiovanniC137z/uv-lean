import UV.ContinueOSQuarticLaw

/-! Product moments, partition function, and the exact derivative for
the Wick-ordered boundary insertion in the specified Gaussian realization. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace UV

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private def centeredPairProduct (F : ι → Ω → ℝ) (ps : List (ι × ι × ℝ)) (ω : Ω) : ℝ :=
  (ps.map (fun p => F p.1 ω * F p.2.1 ω - p.2.2)).prod

private theorem osMonomial_centeredPairProduct {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (ps : List (ι × ι × ℝ)) (xs : List ι) :
    Integrable (fun ω => osMonomial F xs ω * centeredPairProduct F ps ω) μ := by
  induction ps generalizing xs with
  | nil => simpa [centeredPairProduct] using hW.integrable xs
  | cons p ps ih =>
    apply ((ih (p.1 :: p.2.1 :: xs)).sub ((ih xs).const_mul p.2.2)).congr
    filter_upwards with ω
    simp [centeredPairProduct, osMonomial]
    ring

theorem osWickQuadratic_L2 {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (a b c d : ι) :
    let A := fun ω => (F a ω * F b ω - K a b) * (F c ω * F d ω - K c d)
    Integrable A μ ∧ Integrable (fun ω => A ω^2) μ := by
  let p : ι × ι × ℝ := (a,b,K a b)
  let q : ι × ι × ℝ := (c,d,K c d)
  refine ⟨(osMonomial_centeredPairProduct hW [p,q] []).congr
    (Eventually.of_forall fun ω => by simp [osMonomial,centeredPairProduct,p,q]),
    (osMonomial_centeredPairProduct hW [p,q,p,q] []).congr
    (Eventually.of_forall fun ω => by simp [osMonomial,centeredPairProduct,p,q]; ring)⟩

/-- Exact point variance of the Wick polynomial with the 1/4! convention. -/
theorem osWickQuartic_square_mean {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (y : ι) :
    let W := fun ω => osWickQuartic (K y y) (F y ω)
    Integrable (fun ω => W ω ^ 2) μ ∧ (∫ ω, W ω ^ 2 ∂μ) = K y y ^ 4 / 24 := by
  let W := fun ω => osWickQuartic (K y y) (F y ω)
  let M := fun (xs : List ι) (ω : Ω) => osMonomial F xs ω * W ω
  have hi (xs : List ι) : Integrable (M xs) μ := osWickQuartic_insert_integrable hW _ _
  have h4 : (∫ ω, M [y,y,y,y] ω ∂μ) = K y y ^ 4 := by
    rw [show (∫ ω, M [y,y,y,y] ω ∂μ) = _ from osWickQuartic_insert_mean hW _ y (n := 2) (by simp)]
    simp [osWickMoment, List.zipIdx, List.eraseIdx]
    ring
  have h2 : (∫ ω, M [y,y] ω ∂μ) = 0 := by
    rw [show (∫ ω, M [y,y] ω ∂μ) = _ from osWickQuartic_insert_mean hW _ y (n := 1) (by simp)]
    simp [osWickMoment, List.zipIdx, List.eraseIdx]
    ring
  have h0 : (∫ ω, M [] ω ∂μ) = 0 := by simpa [M,W,osMonomial] using osWickQuartic_centered_mean hW y
  let v := K y y
  have he (ω : Ω) : W ω ^ 2 =
      (M [y,y,y,y] ω - (6*v) * M [y,y] ω + (3*v^2) * M [] ω)/24 := by
    simp [M,W,v,osMonomial,osWickQuartic]
    ring
  have hsub : Integrable (fun ω => M [y,y,y,y] ω - (6*v) * M [y,y] ω) μ :=
    (hi [y,y,y,y]).sub ((hi [y,y]).const_mul (6*v))
  have hall := hsub.add ((hi []).const_mul (3*v^2))
  refine ⟨(hall.div_const _).congr (Eventually.of_forall fun ω => (he ω).symm), ?_⟩
  change (∫ ω, W ω^2 ∂μ) = _
  simp only [he, integral_div]
  rw [integral_add hsub ((hi []).const_mul (3*v^2)), integral_sub (hi [y,y,y,y]) ((hi [y,y]).const_mul (6*v)),
    integral_const_mul, integral_const_mul, h4, h2, h0, mul_zero, sub_zero, mul_zero, add_zero]

variable [IsProbabilityMeasure μ]

/-- With the fixed-depth Wick law and a jointly measurable point field,
the full normalized measure exists at every nonnegative coupling. Its
quadratic boundary observable has the stated negative right slope. -/
theorem osWickQuartic_realization {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {ζ : OSFourSpace → ℝ} (hc : Continuous ζ) (hk : HasCompactSupport ζ)
    (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x)
    (F : OSQuarticSlot → Ω → ℝ) (hW : OSWickMoments μ F (osQuarticCovariance m r))
    (hZ : Measurable (fun p : OSFourSpace × Ω => F (.inr p.1) p.2)) :
    let K := osQuarticCovariance m r
    let v := osCoincidence m r
    let a : OSQuarticSlot := .inl .reflectedLocal
    let b : OSQuarticSlot := .inl .reflectedBump
    let c : OSQuarticSlot := .inl .localProbe
    let d : OSQuarticSlot := .inl .bump
    let A := fun ω => (F a ω * F b ω - K a b) * (F c ω * F d ω - K c d)
    let W := osSpatialPotential volume (fun x ω => ζ x * osWickQuartic v (F (.inr x) ω))
    (∀ g : ℝ, 0 ≤ g → IsProbabilityMeasure (osGibbsMeasure μ W g) ∧
      1 ≤ osGibbsPartition μ W g ∧ osGibbsPartition μ W g ≤ Real.exp (g * (v^2/4 * ∫ x, ζ x))) ∧
    HasDerivWithinAt (osGibbsExpectation μ W A) (osWickQuarticSlope m r ζ) (Ioi 0) 0 ∧
      ∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation μ W A g < 0 := by
  intro K v a b c d A W
  let D := fun (x : OSFourSpace) ω => ζ x * osWickQuartic v (F (.inr x) ω)
  let S := fun x => ζ x * (osPoissonTransfer r osReflectedBump x * osPoissonTransfer r osPositiveBump x *
    osGreenPoissonTransfer m r osReflectedBump x * osGreenPoissonTransfer m r osPositiveBump x)
  let L := v^2/4 * ∫ x, ζ x
  have hL₀ : 0 ≤ L := mul_nonneg (by positivity) (integral_nonneg hn)
  have hiζ : Integrable ζ := hc.integrable_of_hasCompactSupport hk
  have hv (x : OSFourSpace) : osQuarticCovariance m r (.inr x) (.inr x) = v := by
    simp [osQuarticCovariance, osCoincidence, v]
  have hmW : Measurable (Function.uncurry fun (x : OSFourSpace) ω => osWickQuartic v (F (.inr x) ω)) := by
    change Measurable (fun p : OSFourSpace × Ω => osWickQuartic v (F (.inr p.1) p.2))
    have hp : Continuous (osWickQuartic v) := by unfold osWickQuartic; fun_prop
    exact hp.measurable.comp hZ
  have hI (x : OSFourSpace) : Integrable (fun ω => (osWickQuartic v (F (.inr x) ω))^2) μ ∧
      (∫ ω, (osWickQuartic v (F (.inr x) ω))^2 ∂μ) = v^4/24 := by
    simpa only [hv] using osWickQuartic_square_mean hW (.inr x)
  have hD : Integrable (Function.uncurry D) (volume.prod μ) := by
    have h := osSpatialProduct_second_moments (A := fun _ : Ω => (1:ℝ)) (ζ := ζ)
      (C := v^4/24) hmW aestronglyMeasurable_const (by simp) hiζ
      (fun x => (hI x).1) (fun x => (hI x).2.le)
    simpa only [one_mul] using h
  have hA := osWickQuadratic_L2 hW a b c d
  have hDA := osSpatialProduct_second_moments (A := A) (C := v^4/24) hmW hA.1.1 hA.2 hiζ
    (fun x => (hI x).1) (fun x => (hI x).2.le)
  have hcenter : (∫ ω, W ω ∂μ) = 0 := by
    apply osSpatialPotential_center hD
    filter_upwards with x
    change (∫ ω, ζ x * osWickQuartic v (F (.inr x) ω) ∂μ) = 0
    rw [integral_const_mul, ← hv x, osWickQuartic_centered_mean hW, mul_zero]
  have hlower : ∀ᵐ ω ∂μ, -L ≤ W ω := by
    have hb := osSpatialPotential_lower (D := D) (B := fun x => -(v^2/4) * ζ x)
      hD (hiζ.const_mul _) (fun ω x => by
        have h := osWick_quartic_density_lower (hn x) v (F (.inr x) ω)
        dsimp [D,osWickQuartic]
        linarith)
    rw [integral_const_mul] at hb
    simpa only [L, neg_mul] using hb
  have hnull := osWick_centeredQuadratic_free_norm hW a b c d
    (osQuarticCovariance_raw_null hm r) (osQuarticCovariance_cross_null hm r)
  have hS (x : OSFourSpace) : (∫ ω, A ω * D x ω ∂μ) = S x := by
    obtain ⟨hc',ha',hd',hb'⟩ := osPointSource_four_pairings hm hr x
    calc
      _ = ζ x * (∫ ω, A ω * osWickQuartic v (F (.inr x) ω) ∂μ) := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        dsimp only [D]
        ring
      _ = _ := by
        rw [← hv x, show (∫ ω, A ω * osWickQuartic (osQuarticCovariance m r (.inr x) (.inr x))
          (F (.inr x) ω) ∂μ) = _ from osWickQuartic_centeredQuadratic_mean hW a b c d (.inr x)]
        simp only [a,b,c,d,osQuarticCovariance,osBoundaryTestProbe,ha',hb',hc',hd',Complex.ofReal_re,S]
        ring
  have hpos : 0 < ∫ x, S x := neg_lt_zero.mp (osWickQuarticSlope_neg hm hr hc hk hn hz)
  refine ⟨fun g hg => ⟨osGibbsMeasure_probability hD.integral_prod_right.1.aemeasurable hlower hg,
    osGibbsPartition_ge_one_of_centered hD.integral_prod_right hlower hg hcenter,
    osGibbsPartition_le hD.integral_prod_right.1.aemeasurable hlower hg⟩, ?_⟩
  exact osSpatialPotential_negative_reflection hD hA.1 hDA hlower hL₀ hnull (Eventually.of_forall hS) hpos

end UV
