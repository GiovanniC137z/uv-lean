import UV.ContinueRepairResultRadial

/-! A compact timelike band is invariant under the axial boosts of the
locked frame. A putative positive tensor measure restricted to that band
has the actual particle-hole pair marginal. Sublinear upper growth of
this marginal forces the integrated boost tensor to vanish. -/

noncomputable section
open Filter Set MeasureTheory Metric Matrix
open scoped ENNReal Matrix ComplexOrder

namespace UV.ContinuationBoostSpectrum

private theorem boostBox_norm (i : Fin 3) {R L : ℝ} (hR : 0 ≤ R) (hRL : R ≤ L)
    {k : ChargeSpatialMomentum} (hk : k ∈ boostBox i R L) : ‖k‖ ≤ 3*L := by
  have h (j : Fin 3) : |k j| ≤ L := by
    have hm := abs_le.mpr ⟨hk.1 j,hk.2 j⟩
    exact hm.trans (by change (if j=i then L else R) ≤ L; split_ifs <;> first | exact le_rfl | exact hRL)
  have hsq (j) := (sq_le_sq₀ (abs_nonneg _) (hR.trans hRL)).mpr (h j)
  simp only [sq_abs] at hsq
  have hn := EuclideanSpace.norm_sq_eq k
  rw [Fin.sum_univ_three] at hn
  simp only [Real.norm_eq_abs,sq_abs] at hn
  nlinarith [hsq 0,hsq 1,hsq 2,norm_nonneg k,sq_nonneg L]

private theorem sublinear_marginal_kills_diagonals (i : Fin 3) (μ : Measure CurrentMomentum)
    {R : ℝ} (hR : 0 < R) (K : Set CurrentMomentum)
    (hK : ∀ k ∈ K, |k.1| ≤ R ∧ ∀ j, |k.2 j| ≤ R)
    (F : ChargeSpatialMomentum → ℝ) (hMarg : Measure.map Prod.snd μ ≤ volume.withDensity (fun p => ENNReal.ofReal (F p)))
    (hF : ∀ ε > 0, ∃ D : ℝ, 0 ≤ D ∧ ∀ p, F p ≤ D+ε*‖p‖)
    (a t z : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hCov : ∀ b : ℝ, μ.real (currentBoost i b '' K) = boostGamma b^2*a+b^2*t+boostGamma b*b*z) :
    a=0 ∧ t=0 := by
  by_contra! h
  have hs : 0 < a+t := by by_contra! h'; exact (h (by linarith)) (by linarith)
  let ε := (a+t)/(432*R^4)
  have hε : 0 < ε := div_pos hs (by positivity)
  obtain ⟨D,hD,hU⟩ := hF ε hε
  have upper (b : ℝ) (hb : 1 ≤ |b|) :
      μ.real (currentBoost i b '' K) ≤ (D+9*ε*R*|b|)*(24*R^3*|b|) := by
    let L := (1+2*|b|)*R
    have hRL : R ≤ L := by dsimp [L]; nlinarith [mul_nonneg (abs_nonneg b) hR.le]
    have hL := hR.le.trans hRL
    have hbox := boostBox_measurable i R L
    have hm : μ (currentBoost i b '' K) ≤ ENNReal.ofReal ((D+3*ε*L)*(8*R^2*L)) := by
      calc
        _ ≤ μ (Prod.snd ⁻¹' boostBox i R L) := measure_mono (currentBoost_spatial_containment i b K hK)
        _ = Measure.map Prod.snd μ (boostBox i R L) := (Measure.map_apply measurable_snd hbox).symm
        _ ≤ volume.withDensity (fun p => ENNReal.ofReal (F p)) (boostBox i R L) := hMarg _
        _ ≤ ∫⁻ _ in boostBox i R L, ENNReal.ofReal (D+3*ε*L) := by
          rw [withDensity_apply _ hbox]
          apply setLIntegral_mono' hbox
          intro p hp
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_left (boostBox_norm i hR.le hRL hp) hε.le
          linarith [hU p]
        _ = _ := by rw [setLIntegral_const,boostBox_volume i hR.le hL,ENNReal.ofReal_mul (by positivity : 0 ≤ D+3*ε*L)]
    have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
      ENNReal.ofReal_ne_top).mpr hm
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    have h3 : L ≤ 3*R*|b| := by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_right hb hR.le]
    apply hreal.trans
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · nlinarith [mul_le_mul_of_nonneg_left h3 hε.le]
    · nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg R)]
  let b := max 1 (48*D*R^3/(a+t))+1
  have hb : 1 ≤ b := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hb₀ : 0 < b := by linarith
  have hlarge : 48*D*R^3/(a+t) < b := (le_max_right _ _).trans_lt (lt_add_one _)
  have hl := mul_lt_mul_of_pos_left ((div_lt_iff₀ hs).mp hlarge) hb₀
  have hp := upper b (by rwa [abs_of_pos hb₀])
  have hn := upper (-b) (by rwa [abs_neg,abs_of_pos hb₀])
  rw [hCov,abs_of_pos hb₀] at hp
  rw [hCov,show boostGamma (-b) = boostGamma b by simp [boostGamma],abs_neg,abs_of_pos hb₀] at hn
  have he : 432*R^4*ε = a+t := by dsimp [ε]; field_simp
  have hg : boostGamma b^2 = 1+b^2 := Real.sq_sqrt (by positivity)
  rw [hg] at hp hn
  nlinarith [congrArg (· * b^2) he]

/-- A positive Lorentz-vector spectral tensor restricted to a band, and
whose spatial time marginal has sublinear growth, vanishes on every
compact set. The covariance hypotheses are the integrated 00 component
of the ordinary tensor law; no scalar mass-shell representation is
assumed. -/
theorem compact_sublinear_lorentz_tensor_vanishes (μ : Measure CurrentMomentum)
    (F : ChargeSpatialMomentum → ℝ)
    (hMarg : Measure.map Prod.snd μ ≤ volume.withDensity (fun p => ENNReal.ofReal (F p)))
    (hF : ∀ ε > 0, ∃ D : ℝ, 0 ≤ D ∧ ∀ p, F p ≤ D+ε*‖p‖)
    {K : Set CurrentMomentum} (hK : IsCompact K) (T : DiracMatrix) (hT : T.PosSemidef)
    (hCov : ∀ i b, μ.real (currentBoost i b '' K) = (boostTimeRow i b ⬝ᵥ (T *ᵥ boostTimeRow i b)).re) :
    T=0 := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  have hBound (k : CurrentMomentum) (hk : k ∈ K) : |k.1| ≤ max R 1 ∧ ∀ j, |k.2 j| ≤ max R 1 := by
    have h := (hR k hk).trans (le_max_left R 1)
    exact ⟨(norm_fst_le k).trans h,fun j => (PiLp.norm_apply_le k.2 j).trans ((norm_snd_le k).trans h)⟩
  have hdiag (j : Fin 4) : 0 ≤ T j j := by
    simpa only [Matrix.mulVec_single_one,←Pi.single_star,star_one,single_dotProduct,one_mul,Matrix.col_apply] using
      hT.2 (Pi.single j (1:ℂ))
  have hz (i : Fin 3) := sublinear_marginal_kills_diagonals i μ (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) K
    hBound F hMarg hF _ _ _ (Complex.nonneg_iff.mp (hdiag 0)).1 (Complex.nonneg_iff.mp (hdiag i.succ)).1
    (fun b => (hCov i b).trans (boostTimeRow_congruence T i b))
  apply hT.trace_eq_zero_iff.mp
  change ∑ j, T j j = 0
  apply Finset.sum_eq_zero
  intro j _
  apply Complex.ext
  · refine Fin.cases (hz 0).1 (fun i => (hz i).2) j
  · exact (Complex.nonneg_iff.mp (hdiag j)).2.symm

end UV.ContinuationBoostSpectrum
