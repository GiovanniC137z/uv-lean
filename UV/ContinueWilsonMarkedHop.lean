import UV.ContinueWilsonActualShell

/-! Every finite Cartesian moment of the full two-mark density has an
absolutely integrable Fourier transform. The displacement polynomial
expands into products of two square-integrable single-mark transforms. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric UV.SectorPlane
open scoped Topology RealInnerProductSpace ENNReal Matrix

namespace UV

abbrev WilsonDirections := List (UnitVector OSFourSpace)

def wilsonDirectionWeight : WilsonDirections → OSFourSpace → ℂ
  | [], _ => 1
  | u :: us, x => (⟪u.val,x⟫:ℝ) * wilsonDirectionWeight us x

theorem wilson_direction_weight_continuous (us : WilsonDirections) : Continuous (wilsonDirectionWeight us) := by
  induction us with
  | nil => exact continuous_const
  | cons u us ih => exact (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).mul ih

variable {ι : Type*} [Fintype ι]

private theorem wilson_continuous_pair_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {f : OSFourSpace × OSFourSpace → ℂ} (hf : Continuous f) :
    Integrable f ((wilsonSingleLaw L T).prod (wilsonSingleLaw L T)) := by
  let K := closedBall (0:OSFourSpace) L
  have hx := (quasiMeasurePreserving_fst (ν := wilsonSingleLaw L T)).ae (wilson_single_support hL T)
  have hy := (quasiMeasurePreserving_snd (μ := wilsonSingleLaw L T)).ae (wilson_single_support hL T)
  have hs : ∀ᵐ z ∂(wilsonSingleLaw L T).prod (wilsonSingleLaw L T), z ∈ K ×ˢ K := hx.and hy
  have h := hf.continuousOn.integrableOn_compact (μ := (wilsonSingleLaw L T).prod (wilsonSingleLaw L T))
    ((isCompact_closedBall (0:OSFourSpace) L).prod (isCompact_closedBall 0 L))
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hs] at h

def wilsonPairPolynomial (a b rest : WilsonDirections) (p : OSFourSpace) (z : OSFourSpace × OSFourSpace) : ℂ :=
  (thinPlaneWave p z.1 * wilsonDirectionWeight a z.1) *
    (thinPlaneWave p z.2 * wilsonDirectionWeight b z.2) * wilsonDirectionWeight rest (z.1+z.2)

theorem wilson_pair_polynomial_continuous (a b rest : WilsonDirections) (p : OSFourSpace) :
    Continuous (wilsonPairPolynomial a b rest p) := by
  have h : Continuous (thinPlaneWave p) := by unfold thinPlaneWave; fun_prop
  exact (((h.mul (wilson_direction_weight_continuous a)).comp continuous_fst).mul
    ((h.mul (wilson_direction_weight_continuous b)).comp continuous_snd)).mul
      ((wilson_direction_weight_continuous rest).comp (continuous_fst.add continuous_snd))

private theorem wilson_pair_polynomial_split (u : UnitVector OSFourSpace) (a b rest : WilsonDirections)
    (p : OSFourSpace) (z : OSFourSpace × OSFourSpace) :
    wilsonPairPolynomial a b (u::rest) p z =
      wilsonPairPolynomial (u::a) b rest p z + wilsonPairPolynomial a (u::b) rest p z := by
  simp only [wilsonPairPolynomial,wilsonDirectionWeight,inner_add_right,Complex.ofReal_add]
  ring

theorem wilson_mixed_marked_pair_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (a b rest : WilsonDirections) :
    Integrable (fun p => ∫ z, wilsonPairPolynomial a b rest p z ∂(wilsonSingleLaw L T).prod (wilsonSingleLaw L T)) := by
  induction rest generalizing a b with
  | nil =>
    have he (p : OSFourSpace) : (∫ z, wilsonPairPolynomial a b [] p z ∂(wilsonSingleLaw L T).prod (wilsonSingleLaw L T)) =
        wilsonMarkedTransform (wilsonSingleLaw L T) (wilsonDirectionWeight a) p *
          wilsonMarkedTransform (wilsonSingleLaw L T) (wilsonDirectionWeight b) p := by
      simp only [wilsonPairPolynomial,wilsonDirectionWeight,mul_one]
      exact integral_prod_mul (fun x => thinPlaneWave p x*wilsonDirectionWeight a x)
        (fun x => thinPlaneWave p x*wilsonDirectionWeight b x)
    simp_rw [he]
    exact (wilson_continuous_single_L2 hL T (wilson_direction_weight_continuous a)).integrable_mul
      (wilson_continuous_single_L2 hL T (wilson_direction_weight_continuous b))
  | cons u rest ih =>
    have h (p : OSFourSpace) := wilson_continuous_pair_integrable hL T (wilson_pair_polynomial_continuous (u::a) b rest p)
    have h' (p : OSFourSpace) := wilson_continuous_pair_integrable hL T (wilson_pair_polynomial_continuous a (u::b) rest p)
    simp_rw [wilson_pair_polynomial_split,integral_add (h _) (h' _)]
    exact (ih (u::a) b).add (ih a (u::b))

theorem wilson_scalar_marked_hop_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) :
    Integrable (fun p => ∫ d, thinPlaneWave p d * wilsonDirectionWeight us d ∂wilsonDisplacementMeasure L T) := by
  have he (p : OSFourSpace) : (∫ d, thinPlaneWave p d * wilsonDirectionWeight us d ∂wilsonDisplacementMeasure L T) =
      ∫ z, wilsonPairPolynomial [] [] us p z ∂(wilsonSingleLaw L T).prod (wilsonSingleLaw L T) := by
    have h : Continuous (thinPlaneWave p) := by unfold thinPlaneWave; fun_prop
    rw [wilson_pair_sum_law,integral_map (measurable_fst.add measurable_snd).aemeasurable
      (h.mul (wilson_direction_weight_continuous us)).aestronglyMeasurable]
    congr 1
    funext z
    simp [wilsonPairPolynomial,wilsonDirectionWeight,thinPlaneWave,inner_add_right,mul_add,Complex.exp_add]
  simp_rw [he]
  exact wilson_mixed_marked_pair_integrable hL T [] [] us

private theorem wilson_continuous_displacement_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {f : OSFourSpace → ℂ} (hf : Continuous f) : Integrable f (wilsonDisplacementMeasure L T) := by
  have hs : ∀ᵐ d ∂wilsonDisplacementMeasure L T, d ∈ closedBall 0 (2*L) := by
    simpa only [mem_closedBall,dist_zero_right] using wilson_displacement_band hL.le T
  have hi := hf.continuousOn.integrableOn_compact (μ := wilsonDisplacementMeasure L T) (isCompact_closedBall 0 (2*L))
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hs] at hi

def wilsonMarkedSpinHop (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (us : WilsonDirections)
    (i j : Fin 4) (p : OSFourSpace) : ℂ :=
  ∫ d, thinPlaneWave p d * wilsonDirectionWeight us d * wilsonSpinWeight L d i j ∂wilsonDisplacementMeasure L T

/-- Fourier transform of the complete spin-weighted density with arbitrary
finitely many displacement insertions, in each of the sixteen matrix entries. -/
theorem wilson_marked_spin_hop_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) : Integrable (wilsonMarkedSpinHop L T us i j) := by
  let M := fun vs p => ∫ d, thinPlaneWave p d * wilsonDirectionWeight vs d ∂wilsonDisplacementMeasure L T
  let c := fun k : Fin 4 => (1/(2*(L:ℂ)))*euclideanGamma k i j
  have H (p : OSFourSpace) (vs : WilsonDirections) : Integrable
      (fun d => thinPlaneWave p d*wilsonDirectionWeight vs d) (wilsonDisplacementMeasure L T) :=
    wilson_continuous_displacement_integrable hL T
      ((show Continuous (thinPlaneWave p) by unfold thinPlaneWave; fun_prop).mul (wilson_direction_weight_continuous vs))
  have he (p : OSFourSpace) : wilsonMarkedSpinHop L T us i j p =
      M us p*(1:DiracMatrix) i j - ∑ k : Fin 4, M (osAxis k::us) p*c k := by
    have hpoint (d : OSFourSpace) : thinPlaneWave p d*wilsonDirectionWeight us d*wilsonSpinWeight L d i j =
        thinPlaneWave p d*wilsonDirectionWeight us d*(1:DiracMatrix) i j -
        ∑ k : Fin 4, (thinPlaneWave p d*wilsonDirectionWeight (osAxis k::us) d)*c k := by
      simp only [wilsonSpinWeight,diracSlash,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,
        smul_eq_mul,mul_sub,Finset.mul_sum,wilsonDirectionWeight,osAxis,
        EuclideanSpace.inner_single_left,map_one,one_mul,c]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    unfold wilsonMarkedSpinHop
    simp_rw [hpoint]
    rw [integral_sub ((H p us).mul_const _) (integrable_finset_sum _ (fun k _ => (H p (osAxis k::us)).mul_const _)),
      integral_finset_sum _ (fun k _ => (H p (osAxis k::us)).mul_const _),integral_mul_const]
    simp only [M,integral_mul_const]
  change Integrable (fun p => wilsonMarkedSpinHop L T us i j p)
  simp_rw [he]
  exact ((wilson_scalar_marked_hop_integrable hL T us).mul_const _).sub
    (integrable_finset_sum _ (fun k _ => (wilson_scalar_marked_hop_integrable hL T (osAxis k::us)).mul_const _))

/-- A circulating carrier momentum can be shifted by arbitrary transfers
and path fractions with exactly the same absolute integral. -/
theorem wilson_marked_spin_hop_shift {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) (q : OSFourSpace) :
    Integrable (fun p => wilsonMarkedSpinHop L T us i j (p+q)) ∧
      (∫ p, ‖wilsonMarkedSpinHop L T us i j (p+q)‖) = ∫ p, ‖wilsonMarkedSpinHop L T us i j p‖ := by
  have hm := measurePreserving_add_right (volume : Measure OSFourSpace) q
  exact ⟨(hm.integrable_comp_emb (Homeomorph.addRight q).measurableEmbedding).mpr (wilson_marked_spin_hop_integrable hL T us i j),
    hm.integral_comp (Homeomorph.addRight q).measurableEmbedding (fun p => ‖wilsonMarkedSpinHop L T us i j p‖)⟩

end UV
