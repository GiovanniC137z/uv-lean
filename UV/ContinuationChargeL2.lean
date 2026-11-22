import UV.ContinuationChargeRigidity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! From equality of the spatially shifted bounded operators on actual L²
slots to equality of their continuous matrix representatives. -/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Matrix InnerProductSpace

namespace UV

abbrev ChargeSlots (d : ℕ) := EuclideanSpace ℂ (Fin d)
abbrev ChargeL2 (d : ℕ) := Lp (ChargeSlots d) 2 (volume : Measure ChargeSpatialMomentum)

variable {Sector : Type*} {d : ℕ}

/-- Spatial translation covariance in sector `plane`, stated for the actual
representatives of bounded charge maps on the Hilbert slots. -/
def chargeModeRep (T : ChargeSpatialMomentum → ChargeL2 d →L[ℂ] ChargeL2 d)
    (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
      Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector) : Prop :=
  ∀ p (f : ChargeL2 d), ∀ᵐ k ∂(volume : Measure ChargeSpatialMomentum),
    (T p f (k + p) : Fin d → ℂ) = K plane p k *ᵥ (f k : Fin d → ℂ)

private theorem shift_ae_eq {A : Type*} {f g : ChargeSpatialMomentum → A}
    (h : f =ᵐ[(volume : Measure ChargeSpatialMomentum)] g) (p : ChargeSpatialMomentum) :
    (fun k => f (k + p)) =ᵐ[(volume : Measure ChargeSpatialMomentum)] (fun k => g (k + p)) :=
  (measurePreserving_add_right volume p).quasiMeasurePreserving.ae_eq_comp h

private theorem continuous_matrix_eq_of_slot_actions
    (A B : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (h : ∀ f : ChargeL2 d, ∀ᵐ k ∂(volume : Measure ChargeSpatialMomentum),
      A k *ᵥ (f k : Fin d → ℂ) = B k *ᵥ (f k : Fin d → ℂ)) : A = B := by
  funext k
  ext i j
  let s := Metric.ball k 1
  let v : ChargeSlots d := EuclideanSpace.single j 1
  let f₀ := s.indicator (fun _ => v)
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hfin : volume s ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  let hf : MemLp f₀ 2 (volume : Measure ChargeSpatialMomentum) :=
    memLp_indicator_const 2 hs v (Or.inr hfin)
  let f := hf.toLp f₀
  have h' : (fun k' => A k' i j) =ᵐ[volume.restrict s] (fun k' => B k' i j) := by
    filter_upwards [ae_restrict_of_ae (h f), ae_restrict_of_ae hf.coeFn_toLp,
      ae_restrict_mem hs] with k' hk hk' hks
    change f k' = f₀ k' at hk'
    simp only [f₀, indicator_of_mem hks] at hk'
    rw [hk'] at hk
    have hv : (v : Fin d → ℂ) = Pi.single j (1 : ℂ) := by
      funext j'
      simp only [v, EuclideanSpace.single_apply, Pi.single_apply]
    rw [hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hk
    exact congrFun hk i
  have he := Measure.eqOn_of_ae_eq h'
    (((continuous_apply j).comp ((continuous_apply i).comp hA)).continuousOn)
    (((continuous_apply j).comp ((continuous_apply i).comp hB)).continuousOn)
    (by rw [Metric.isOpen_ball.interior_eq]; exact subset_closure)
  exact he (Metric.mem_ball_self (by norm_num))

/-- Derive the shifted matrix product from actual operator commutation. -/
theorem chargeModeRep_matrix_commute (T : ChargeSpatialMomentum → ChargeL2 d →L[ℂ] ChargeL2 d)
    (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
      Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (hcont : Continuous (Function.uncurry (K plane))) (hrep : chargeModeRep T K plane)
    (hcomm : ∀ p h, Commute (T h) (T p)) (p h k : ChargeSpatialMomentum) :
    K plane h (k + p) * K plane p k = K plane p (k + h) * K plane h k := by
  let A := fun k => K plane h (k + p) * K plane p k
  let B := fun k => K plane p (k + h) * K plane h k
  have hk (p' : ChargeSpatialMomentum) : Continuous (K plane p') :=
    hcont.comp (continuous_const.prodMk continuous_id)
  have hA : Continuous A := ((hk h).comp (continuous_id.add continuous_const)).mul (hk p)
  have hB : Continuous B := ((hk p).comp (continuous_id.add continuous_const)).mul (hk h)
  apply congrFun (continuous_matrix_eq_of_slot_actions A B hA hB ?_) k
  intro f
  filter_upwards [hrep p f, hrep h f, shift_ae_eq (hrep h (T p f)) p,
    shift_ae_eq (hrep p (T h f)) h] with k' hp hh hph hhp
  have hc : T h (T p f) = T p (T h f) := congrArg (fun M : ChargeL2 d →L[ℂ] ChargeL2 d => M f)
    (hcomm p h).eq
  change (T h (T p f) (k' + p + h) : Fin d → ℂ) =
    K plane h (k' + p) *ᵥ (T p f (k' + p) : Fin d → ℂ) at hph
  change (T p (T h f) (k' + h + p) : Fin d → ℂ) =
    K plane p (k' + h) *ᵥ (T h f (k' + h) : Fin d → ℂ) at hhp
  rw [hc, add_right_comm k' p h, hp] at hph
  rw [hh] at hhp
  change (K plane h (k' + p) * K plane p k') *ᵥ (f k' : Fin d → ℂ) =
    (K plane p (k' + h) * K plane h k') *ᵥ (f k' : Fin d → ℂ)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hph.symm.trans hhp

private theorem chargeModeRep_adjoint_entries_integral
    (T : ChargeSpatialMomentum → ChargeL2 d →L[ℂ] ChargeL2 d)
    (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
      Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector) (hrep : chargeModeRep T K plane)
    (hadj : ∀ p, T (-p) = (T p).adjoint) (p : ChargeSpatialMomentum) (i j : Fin d)
    (s : Set ChargeSpatialMomentum) (hs : MeasurableSet s)
    (hfin : (volume : Measure ChargeSpatialMomentum) s < ⊤) :
    (∫ k in s, K plane p k i j) = ∫ k in s, star (K plane (-p) (k + p) j i) := by
  let μ := (volume : Measure ChargeSpatialMomentum)
  let sp := (fun k : ChargeSpatialMomentum => k + (-p)) ⁻¹' s
  have hp : MeasurePreserving (fun k : ChargeSpatialMomentum => k + p) μ μ :=
    measurePreserving_add_right μ p
  have hn : MeasurePreserving (fun k : ChargeSpatialMomentum => k + (-p)) μ μ :=
    measurePreserving_add_right μ (-p)
  have hsp : MeasurableSet sp := hn.measurable hs
  have hspfin : μ sp < ⊤ := by
    change μ ((fun k => k + (-p)) ⁻¹' s) < ⊤
    rw [← Measure.map_apply hn.measurable hs, hn.map_eq]
    exact hfin
  let a : ChargeSlots d := EuclideanSpace.single i 1
  let b : ChargeSlots d := EuclideanSpace.single j 1
  let f₀ := s.indicator (fun _ => b)
  let g₀ := sp.indicator (fun _ => a)
  let hf : MemLp f₀ 2 μ := memLp_indicator_const 2 hs b (Or.inr hfin.ne)
  let hg : MemLp g₀ 2 μ := memLp_indicator_const 2 hsp a (Or.inr hspfin.ne)
  let f := hf.toLp f₀
  let g := hg.toLp g₀
  have ha : (a : Fin d → ℂ) = Pi.single i (1 : ℂ) := by
    funext j'
    simp only [a, EuclideanSpace.single_apply, Pi.single_apply]
  have hb : (b : Fin d → ℂ) = Pi.single j (1 : ℂ) := by
    funext j'
    simp only [b, EuclideanSpace.single_apply, Pi.single_apply]
  have hLeft : inner ℂ g (T p f) = ∫ k in s, K plane p k i j := by
    rw [MeasureTheory.L2.inner_def, ← hp.integral_comp (Homeomorph.addRight p).isClosedEmbedding.measurableEmbedding,
      ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [hrep p f, hf.coeFn_toLp, shift_ae_eq hg.coeFn_toLp p] with k hk hkf hkg
    change f k = f₀ k at hkf
    change g (k + p) = g₀ (k + p) at hkg
    change inner ℂ (g (k + p)) (T p f (k + p)) = s.indicator (fun k => K plane p k i j) k
    have hspk : (k + p) ∈ sp ↔ k ∈ s := by simp [sp]
    by_cases hks : k ∈ s
    · simp only [g₀, indicator_of_mem (hspk.mpr hks)] at hkg
      simp only [f₀, indicator_of_mem hks] at hkf
      rw [hkg, indicator_of_mem hks, EuclideanSpace.inner_single_left, map_one, one_mul]
      rw [hkf, hb, Matrix.mulVec_single_one] at hk
      exact congrFun hk i
    · simp only [g₀, indicator_of_notMem (mt hspk.mp hks)] at hkg
      rw [hkg, inner_zero_left, indicator_of_notMem hks]
  have hRight : inner ℂ (T (-p) g) f = ∫ k in s, star (K plane (-p) (k + p) j i) := by
    rw [MeasureTheory.L2.inner_def, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [shift_ae_eq (hrep (-p) g) p, hf.coeFn_toLp, shift_ae_eq hg.coeFn_toLp p]
      with k hk hkf hkg
    change f k = f₀ k at hkf
    change g (k + p) = g₀ (k + p) at hkg
    change (T (-p) g (k + p + (-p)) : Fin d → ℂ) =
      K plane (-p) (k + p) *ᵥ (g (k + p) : Fin d → ℂ) at hk
    simp only [add_neg_cancel_right] at hk
    have hspk : (k + p) ∈ sp ↔ k ∈ s := by simp [sp]
    by_cases hks : k ∈ s
    · simp only [g₀, indicator_of_mem (hspk.mpr hks)] at hkg
      simp only [f₀, indicator_of_mem hks] at hkf
      rw [hkf, indicator_of_mem hks, EuclideanSpace.inner_single_right, one_mul]
      rw [hkg, ha, Matrix.mulVec_single_one] at hk
      exact congrArg star (congrFun hk j)
    · simp only [f₀, indicator_of_notMem hks] at hkf
      rw [hkf, inner_zero_right, indicator_of_notMem hks]
  rw [← hLeft, ← hRight, hadj]
  exact ((T p).adjoint_inner_left f g).symm

/-- The reverse spatial mode's continuous representative is the physical
adjoint matrix with the momentum slots exchanged. -/
theorem chargeModeRep_matrix_adjoint (T : ChargeSpatialMomentum → ChargeL2 d →L[ℂ] ChargeL2 d)
    (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
      Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (hcont : Continuous (Function.uncurry (K plane))) (hrep : chargeModeRep T K plane)
    (hadj : ∀ p, T (-p) = (T p).adjoint) (p k : ChargeSpatialMomentum) :
    K plane (-p) (k + p) = (K plane p k)ᴴ := by
  ext i j
  let f := fun u => K plane p u j i
  let g := fun u => star (K plane (-p) (u + p) i j)
  have hk (p' : ChargeSpatialMomentum) : Continuous (K plane p') :=
    hcont.comp (continuous_const.prodMk continuous_id)
  have hf : Continuous f := (continuous_apply i).comp ((continuous_apply j).comp (hk p))
  have hg : Continuous g := continuous_star.comp ((continuous_apply j).comp
    ((continuous_apply i).comp ((hk (-p)).comp (continuous_id.add continuous_const))))
  let s := Metric.ball k 1
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hfin : (volume : Measure ChargeSpatialMomentum) s < ⊤ := Metric.isBounded_ball.measure_lt_top
  have hfi : IntegrableOn f s := (hf.continuousOn.integrableOn_compact (isCompact_closedBall k 1)).mono_set
    Metric.ball_subset_closedBall
  have hgi : IntegrableOn g s := (hg.continuousOn.integrableOn_compact (isCompact_closedBall k 1)).mono_set
    Metric.ball_subset_closedBall
  have he : f =ᵐ[volume.restrict s] g := by
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    · intro u hu hμ
      exact hfi.integrableOn
    · intro u hu hμ
      exact hgi.integrableOn
    · intro u hu hμ
      rw [Measure.restrict_restrict hu]
      exact chargeModeRep_adjoint_entries_integral T K plane hrep hadj p j i (u ∩ s) (hu.inter hs)
        ((measure_mono inter_subset_right).trans_lt hfin)
  have heq := Measure.eqOn_of_ae_eq he hf.continuousOn hg.continuousOn
    (by rw [Metric.isOpen_ball.interior_eq]; exact subset_closure) (Metric.mem_ball_self (by norm_num))
  exact star_injective (by simpa only [Matrix.conjTranspose_apply, star_star, f, g] using heq.symm)

/-- The named local-charge result for actual bounded operators on L².
Each spatial translation and adjoint comparison stays on `plane`. -/
theorem local_charge_rigidity_L2 (T : ChargeSpatialMomentum → ChargeL2 d →L[ℂ] ChargeL2 d)
    (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
      Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector) (hd : 0 < d)
    (hcont : Continuous (Function.uncurry (K plane))) {q : ℝ} (hq : q ≠ 0)
    (hzero : ∀ k, K plane 0 k = (q : ℂ) • 1) (hrep : chargeModeRep T K plane)
    (hadj : ∀ p, T (-p) = (T p).adjoint) (hcomm : ∀ p h, Commute (T h) (T p)) :
    (∀ p k k', (chargeGram_hermitian K plane p k).eigenvalues =
      (chargeGram_hermitian K plane p k').eigenvalues) ∧
    (∀ p k, chargeInclusiveSquare (K plane p k) = chargeInclusiveSquare (K plane p 0)) ∧
    (∀ᶠ p in 𝓝 (0 : ChargeSpatialMomentum), ∀ k, 0 < chargeInclusiveSquare (K plane p k)) := by
  have hm := chargeModeRep_matrix_commute T K plane hcont hrep hcomm
  have hA := chargeModeRep_matrix_adjoint T K plane hcont hrep hadj
  exact ⟨commuting_local_charge_eigenvalues K plane hcont hq hzero hA hm,
    commuting_local_charge_inclusive_square K plane hd hcont hq hzero hA hm⟩

end UV
