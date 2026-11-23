import UV.ContinueNormalLegTransfer
import UV.ContinueNormalCoverConvolution

/-! Charged lines with a separate constant-shell compression at each end.
The physical circle modes are retained in frequency space. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator ENNReal

namespace UV

local instance compressedMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance compressedMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

variable {ι : Type*} [Fintype ι]

/-- The two adjacent marked vertices compress the same internal charged momentum twice.
The transverse photon profile is accounted for separately on photon incidences. -/
def compressedMarkedLine (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : UnitVector OSFourSpace) (p : OSFourSpace) : DiracMatrix :=
  (Complex.I*(normalLegForm L T ξ p : ℂ)^2) • (normalDiracFrequency m p ξ*diracSlash u.val)

def compressedLoopTrace {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) : ℂ :=
  (normalOrderedWord (fun j => compressedMarkedLine m L T ξ (u j) (p j))).trace

theorem compressed_line_continuous {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) : Continuous (compressedMarkedLine m L T ξ u) :=
  (continuous_const.mul ((Complex.continuous_ofReal.comp (normal_leg_form_continuous L T ξ)).pow 2)).smul
    ((normal_frequency_continuous hm ξ).mul continuous_const)

theorem compressed_line_norm_le (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) (p : OSFourSpace) :
    ‖compressedMarkedLine m L T ξ u p‖ ≤ |normalLegForm L T ξ p|^2 * ‖normalDiracFrequency m p ξ‖ := by
  simp only [compressedMarkedLine,norm_smul,norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [wilson_slash_opnorm,u.property,mul_one] using norm_mul_le (normalDiracFrequency m p ξ) (diracSlash u.val)

theorem compressed_line_uniform {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) (p : OSFourSpace) : ‖compressedMarkedLine m L T ξ u p‖ ≤ m⁻¹ := by
  have hf : |normalLegForm L T ξ p| ≤ 1 := (Complex.abs_re_le_norm _).trans (normal_shell_characteristic_le_one _)
  apply (compressed_line_norm_le m L T ξ u p).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) (by simpa using pow_le_pow_left₀ (abs_nonneg _) hf 2)).trans
  exact normal_frequency_mass_bound hm p ξ

theorem compressed_frequency_radial_bound {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (ξ : ℝ) (p : OSFourSpace) :
    ‖normalDiracFrequency m p ξ‖ ≤ (m⁻¹+L)/(1+L*‖normalBallJoin ξ p‖) := by
  let P := normalBallJoin ξ p
  let X := 1+L*‖P‖
  let E := Real.sqrt (normalFiveDenom m p ξ)
  have hE : 0 < E := by dsimp [E,normalFiveDenom]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have he : E^2 = m^2 + ‖P‖^2 := by
    rw [show E^2 = normalFiveDenom m p ξ from Real.sq_sqrt (by dsimp [normalFiveDenom]; positivity),normal_ball_join_norm]
    dsimp [normalFiveDenom]; ring
  have h1 : m ≤ E := by nlinarith [sq_nonneg ‖P‖]
  have h2 : ‖P‖ ≤ E := by nlinarith [sq_nonneg m,norm_nonneg P]
  have hA : X ≤ (m⁻¹+L)*E := by
    have h := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hm.le)
    rw [inv_mul_cancel₀ hm.ne'] at h
    dsimp [X]; nlinarith [mul_le_mul_of_nonneg_left h2 hL.le]
  rw [normal_dirac_frequency_norm hm]
  change E⁻¹ ≤ (m⁻¹+L)/X
  rw [←one_div]
  rw [div_le_div_iff₀ hE hX,one_mul]
  exact hA

/-- With cubic shell decay the two compressions contribute six powers and
the Dirac inverse one more. This is sufficient in all shell dimensions at least five. -/
theorem compressed_line_radial_bound {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) {B : ℝ} (hB : 0 < B)
    (hshell : ∀ a : WilsonBallSpace ι, ‖normalShellCharacteristic a‖ ≤ B/(1+‖a‖)^3) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ (u : UnitVector OSFourSpace) p,
      ‖compressedMarkedLine m L T ξ u p‖ ≤ C/(1+L*‖normalBallJoin ξ p‖)^7 := by
  refine ⟨B^2*(m⁻¹+L),by positivity,fun ξ u p => ?_⟩
  let P := normalBallJoin ξ p
  let X := 1+L*‖P‖
  have hX : 0 < X := by dsimp [X]; positivity
  have hD := compressed_frequency_radial_bound hm hL ξ p
  have hf : |normalLegForm L T ξ p| ≤ B/X^3 := (Complex.abs_re_le_norm _).trans
    (by simpa only [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le] using hshell (L • T P))
  apply (compressed_line_norm_le m L T ξ u p).trans
  apply (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hf 2) hD (norm_nonneg _) (sq_nonneg _)).trans_eq
  change (B/X^3)^2*((m⁻¹+L)/X) = B^2*(m⁻¹+L)/X^7
  field_simp [hX.ne']

theorem compressed_line_separate_bound {m L : ℝ} (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) {C : ℝ} (hC : 0 < C)
    (h : ∀ ξ (u : UnitVector OSFourSpace) p, ‖compressedMarkedLine m L T ξ u p‖ ≤ C/(1+L*‖normalBallJoin ξ p‖)^7) :
    ∃ K : ℝ, 0 < K ∧ ∀ ξ (u : UnitVector OSFourSpace) p,
      ‖compressedMarkedLine m L T ξ u p‖ ≤ K*normalPhotonWeight 2 ξ*normalPhotonWeight 5 p := by
  let D := 1+L⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D^7,by positivity,fun ξ u p => ?_⟩
  let P := normalBallJoin ξ p
  let X := 1+L*‖P‖
  have hX : 0 < X := by dsimp [X]; positivity
  have he := normal_ball_join_norm ξ p
  have hp : ‖p‖ ≤ ‖P‖ := by dsimp [P]; nlinarith [norm_nonneg p,norm_nonneg (normalBallJoin ξ p),sq_nonneg ξ]
  have hξ : |ξ| ≤ ‖P‖ := by dsimp [P]; nlinarith [sq_abs ξ,abs_nonneg ξ,norm_nonneg (normalBallJoin ξ p),sq_nonneg ‖p‖]
  have hscale : 1+‖P‖ ≤ D*X := by
    dsimp [D,X]
    have hh : L⁻¹*(L*‖P‖) = ‖P‖ := by rw [←mul_assoc,inv_mul_cancel₀ hL.ne',one_mul]
    nlinarith [inv_nonneg.mpr hL.le,mul_nonneg hL.le (norm_nonneg P)]
  have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖p‖) ((add_le_add_left hp 1).trans hscale) 5
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|ξ|) ((add_le_add_left hξ 1).trans hscale) 2
  have hS : (1+|ξ|)^2*(1+‖p‖)^5 ≤ D^7*X^7 := (mul_le_mul h2 h1 (by positivity) (by positivity)).trans_eq (by ring)
  apply (h ξ u p).trans
  change C/X^7 ≤ C*D^7*((1+|ξ|)^2)⁻¹*((1+‖p‖)^5)⁻¹
  rw [mul_assoc,←mul_inv,←div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hS hC.le

theorem compressed_loop_measurable {n : ℕ} {Z : Type*} [MeasurableSpace Z] {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    {p : Z → Fin (n+1) → OSFourSpace} (hp : ∀ i, Measurable (fun z => p z i)) :
    Measurable (fun z => compressedLoopTrace m L T ξ u (p z)) := by
  apply (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp
  exact normal_ordered_measurable _ (fun i => (compressed_line_continuous hm L T ξ (u i)).measurable.comp (hp i))

/-- One selected segment suffices to bind the unrestricted carrier and normal circulation.
The other factors only use the mass gap, with their order and unit polarizations retained. -/
theorem compressed_loop_le_first {n : ℕ} {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    ‖compressedLoopTrace m L T ξ u p‖ ≤ (4*m⁻¹^n)*‖compressedMarkedLine m L T ξ (u 0) (p 0)‖ := by
  let A := fun i => compressedMarkedLine m L T ξ (u i) (p i)
  have htail : ‖normalOrderedWord (fun i : Fin n => A i.succ)‖ ≤ m⁻¹^n := by
    apply (List.norm_prod_le _).trans
    rw [List.map_ofFn,List.prod_ofFn]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun (i : Fin n) _ => norm_nonneg (A i.succ))
        (fun i _ => compressed_line_uniform hm L T ξ (u i.succ) (p i.succ))
  apply (wilson_trace_le_opnorm _).trans
  change 4*‖(List.ofFn A).prod‖ ≤ _
  rw [List.ofFn_succ,List.prod_cons]
  exact (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left htail (norm_nonneg _)))
    (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by change 4*(‖A 0‖*m⁻¹^n) = (4*m⁻¹^n)*‖A 0‖; ring)

def CompressedCarrierBound (σ : Measure OSFourSpace) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s : OSFourSpace, let g := fun k => normalPhotonWeight 5 (k+s)
    Integrable g σ ∧ (∫ k, g k ∂σ) ≤ B

theorem compressed_volume_carrier_bound : CompressedCarrierBound volume := by
  let w := normalPhotonWeight (E := OSFourSpace) 5
  have hi : Integrable w := normal_photon_weight_integrable volume (by rw [finrank_euclideanSpace_fin]; decide)
  exact ⟨∫ k, w k,integral_nonneg (fun k => by dsimp [w,normalPhotonWeight]; positivity),fun s =>
    ⟨(measurePreserving_add_right volume s).integrable_comp_of_integrable hi,(integral_add_right_eq_self w s).le⟩⟩

theorem compressed_lattice_carrier_bound (b : NormalReciprocalBasis) : CompressedCarrierBound (normalLatticeMeasure b) := by
  obtain ⟨R,hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  let C := (1+max R 0)^5
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let A := normalCellFactor b C
  obtain ⟨B,hB,hsh⟩ := compressed_volume_carrier_bound
  refine ⟨A.toReal*B,mul_nonneg ENNReal.toReal_nonneg hB,fun s => ?_⟩
  let g := fun k : OSFourSpace => normalPhotonWeight 5 (k+s)
  have hg : Measurable g := by dsimp [g,normalPhotonWeight]; fun_prop
  have hn (k) : 0 ≤ g k := by dsimp [g,normalPhotonWeight]; positivity
  have hc (k : NormalReciprocalLattice b) (x) (hx : x ∈ ZSpan.fundamentalDomain b) :
      g k ≤ C * g ((k:OSFourSpace)+x) := by
    simpa only [g,C,add_right_comm (k:OSFourSpace) x s] using normal_photon_weight_cell (le_max_right R 0)
      ((k:OSFourSpace)+s) x ((hR x hx).trans (le_max_left _ _)) 5
  have h := normal_integral_from_cell_bound (normalLatticeMeasure b) volume hg hn (hsh s).1 A (normal_cell_factor_finite b C)
    (normal_lattice_cell_lintegral b C _ (ENNReal.measurable_ofReal.comp hg) (fun k x hx => by
      rw [←ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal (hc k x hx)))
  exact ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left (hsh s).2 ENNReal.toReal_nonneg)⟩

theorem compressed_loop_budget_of_decay {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin (n+1) → UnitVector OSFourSpace)
    (σ : Measure OSFourSpace) (hσ : CompressedCarrierBound σ)
    (hdec : ∃ B : ℝ, 0 < B ∧ ∀ a : WilsonBallSpace ι, ‖normalShellCharacteristic a‖ ≤ B/(1+‖a‖)^3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ξ : ℝ) (s : Fin (n+1) → OSFourSpace),
      let F := fun k => compressedLoopTrace m L T ξ u (fun i => k+s i)
      Integrable F σ ∧ (∫ k, ‖F k‖ ∂σ) ≤ B*normalPhotonWeight 2 ξ := by
  obtain ⟨B,hB,h⟩ := hdec
  obtain ⟨C,hC,h1⟩ := compressed_line_radial_bound hm hL T hB h
  obtain ⟨K,hK,h2⟩ := compressed_line_separate_bound hL T hC h1
  obtain ⟨M,hM,h3⟩ := hσ
  let D := (4*m⁻¹^n)*K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D*M,mul_nonneg hD hM,fun ξ s => ?_⟩
  let F := fun k => compressedLoopTrace m L T ξ u (fun i => k+s i)
  let w := normalPhotonWeight 2 ξ
  have hw : 0 ≤ w := by dsimp [w,normalPhotonWeight]; positivity
  have hle (k) : ‖F k‖ ≤ (D*w)*normalPhotonWeight 5 (k+s 0) := by
    apply (compressed_loop_le_first hm L T ξ u (fun i => k+s i)).trans
    apply (mul_le_mul_of_nonneg_left (h2 ξ (u 0) (k+s 0)) (by positivity : 0 ≤ 4*m⁻¹^n)).trans_eq
    dsimp [D,w]; ring
  have hI := (h3 (s 0)).1.const_mul (D*w)
  have hF := hI.mono' (compressed_loop_measurable hm L T ξ u (fun i => measurable_id.add_const (s i))).aestronglyMeasurable
    (Eventually.of_forall hle)
  refine ⟨hF,(integral_mono hF.norm hI hle).trans ?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (h3 (s 0)).2 (mul_nonneg hD hw)).trans_eq (by dsimp [w]; ring)

end UV
