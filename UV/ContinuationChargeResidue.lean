import UV.ContinuationChargeRigidity
import Mathlib.Analysis.Normed.Field.Basic

/-! The complete limiting contact coefficient on one locked plane has a
noncancellable double pole when an equal-energy charge block survives.
Energies are the actual slots of a fixed orthonormal eigenbasis, with
multiplicities retained. -/

noncomputable section
open Complex Filter Matrix Set
open scoped Topology Matrix

namespace UV

variable {Sector : Type*} {d : ℕ}

/-- Both vectorial pole characters are retained for the external frequency. -/
def temporalCarrierFrequency (u : ℝ) : Carrier.Algebra :=
  (I * (u : ℂ), -(I * (u : ℂ)))

/-- In the locked-plane eigenbasis the spectral projection selects every
slot with the specified energy, including degenerate slots. -/
def temporalEnergyProjection (ε : Fin d → ℝ) (E : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun i => if ε i = E then 1 else 0

/-- The actual diagonal resolvent `(z I + H)⁻¹` on the locked plane. -/
def temporalDiagonalResolvent (ε : Fin d → ℝ) (z : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun i => (z + (ε i : ℂ))⁻¹

theorem temporalDiagonalResolvent_inverse (ε : Fin d → ℝ) (z : ℂ)
    (hz : ∀ i, z + (ε i : ℂ) ≠ 0) :
    temporalDiagonalResolvent ε z = (diagonal fun i => z + (ε i : ℂ))⁻¹ := by
  symm
  rw [Matrix.inv_eq_left_inv]
  unfold temporalDiagonalResolvent
  rw [diagonal_mul_diagonal']
  simpa only [inv_mul_cancel₀ (hz _)] using (Matrix.diagonal_one :
    (diagonal fun _ : Fin d => (1 : ℂ)) = 1)

/-- Complete contact-minus-bubble coefficient in one spectral chart. -/
def temporalContactCoefficient (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (z : ℂ) : ℂ :=
  let R := temporalDiagonalResolvent (ε plane) z
  (R * C plane).trace - (R * (Q plane)ᴴ * R * Q plane).trace

private def temporalScaledInv (E e : ℝ) (t : ℂ) : ℂ :=
  if e = E then 1 else t / (t + ((e - E : ℝ) : ℂ))

private theorem temporalScaledInv_continuousAt (E e : ℝ) :
    ContinuousAt (temporalScaledInv E e) 0 := by
  by_cases h : e = E
  · have he : temporalScaledInv E e = (fun _ : ℂ => (1 : ℂ)) := by
      funext u
      simp [temporalScaledInv, h]
    rw [he]
    exact continuousAt_const
  · have he : temporalScaledInv E e = (fun t : ℂ => t / (t + ((e - E : ℝ) : ℂ))) := by
      funext u
      simp only [temporalScaledInv, if_neg h]
    rw [he]
    apply continuousAt_id.div (continuousAt_id.add continuousAt_const)
    simpa only [id_eq, zero_add, ofReal_ne_zero] using sub_ne_zero.mpr h

private theorem temporalScaledInv_eq (E e : ℝ) (t : ℂ) (ht : t ≠ 0) :
    temporalScaledInv E e t = t * ((t - (E : ℂ)) + (e : ℂ))⁻¹ := by
  by_cases h : e = E
  · subst e
    simp [temporalScaledInv, ht]
  · simp only [temporalScaledInv, if_neg h, ofReal_sub, div_eq_mul_inv]
    congr 2
    ring

private theorem temporalScaledInv_zero (E e : ℝ) :
    temporalScaledInv E e 0 = (if e = E then 1 else 0) := by
  by_cases h : e = E <;> simp [temporalScaledInv, h]

/-- The scaled coefficient tends to minus the squared Hilbert--Schmidt
norm of the actual double-pole block. Contact terms have only simple poles. -/
theorem temporal_contact_double_pole (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (E : ℝ) :
    Tendsto (fun t : ℂ => t ^ 2 * temporalContactCoefficient ε C Q plane (t - (E : ℂ)))
      (𝓝[≠] 0) (𝓝 (-(chargeInclusiveSquare
        (temporalEnergyProjection (ε plane) E * Q plane * temporalEnergyProjection (ε plane) E) : ℂ))) := by
  let P := temporalEnergyProjection (ε plane) E
  let D := fun t => diagonal (fun i => temporalScaledInv E (ε plane i) t)
  let F := fun t => (t • (D t * C plane)).trace - (D t * (Q plane)ᴴ * D t * Q plane).trace
  have hD : ContinuousAt D 0 := by
    exact (continuous_id.matrix_diagonal.continuousAt).comp
      (continuousAt_pi.mpr (fun i => temporalScaledInv_continuousAt E (ε plane i)))
  have htrace : Continuous (Matrix.trace : Matrix (Fin d) (Fin d) ℂ → ℂ) :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  have hF : ContinuousAt F 0 :=
    (htrace.continuousAt.comp (continuousAt_id.smul (hD.mul continuousAt_const))).sub
      (htrace.continuousAt.comp (((hD.mul continuousAt_const).mul hD).mul continuousAt_const))
  have hD₀ : D 0 = P := by
    unfold D P temporalEnergyProjection
    simp only [temporalScaledInv_zero]
  have hPId : P * P = P := by
    unfold P temporalEnergyProjection
    rw [Matrix.diagonal_mul_diagonal']
    congr 1
    funext i
    by_cases h : ε plane i = E <;> simp [h]
  have hPH : Pᴴ = P := by
    unfold P temporalEnergyProjection
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : ε plane i = E <;> simp [h]
  have ht : (P * (Q plane)ᴴ * P * Q plane).trace =
      ((P * Q plane * P)ᴴ * (P * Q plane * P)).trace := by
    calc
      _ = (P * ((Q plane)ᴴ * P * Q plane)).trace := by simp only [mul_assoc]
      _ = ((P * ((Q plane)ᴴ * P * Q plane)) * P).trace := by
        rw [Matrix.trace_mul_comm (P * ((Q plane)ᴴ * P * Q plane)) P,
          ← mul_assoc P P, hPId]
      _ = _ := by
        simp only [conjTranspose_mul, hPH, mul_assoc]
        rw [← mul_assoc P P, hPId]
  have hF₀ : F 0 = -(chargeInclusiveSquare (P * Q plane * P) : ℂ) := by
    unfold F
    simp only [zero_smul, Matrix.trace_zero, zero_sub, hD₀, ht]
    rw [chargeInclusiveSquare_eq_trace]
    congr 1
    let G := chargeGram (fun _ _ _ => P * Q plane * P) plane 0 0
    change G.trace = (G.trace.re : ℂ)
    have hH : G.IsHermitian := chargeGram_hermitian (fun _ _ _ => P * Q plane * P) plane 0 0
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hH]
    simp
  have he : F =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun t => t ^ 2 * temporalContactCoefficient ε C Q plane (t - (E : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    have hDt : D t = t • temporalDiagonalResolvent (ε plane) (t - (E : ℂ)) := by
      unfold D temporalDiagonalResolvent
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      exact temporalScaledInv_eq E (ε plane i) t ht'
    change (t • (D t * C plane)).trace - (D t * (Q plane)ᴴ * D t * Q plane).trace = _
    rw [hDt]
    simp [temporalContactCoefficient, smul_smul, pow_two, mul_sub]
  rw [← hF₀]
  exact hF.continuousWithinAt.congr' he

/-- The double pole is nonzero for a surviving equal-energy matrix block.
This statement uses the full coefficient before the frequency integration. -/
theorem temporal_contact_not_eventually_zero (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (E : ℝ) (h : temporalEnergyProjection (ε plane) E * Q plane *
      temporalEnergyProjection (ε plane) E ≠ 0) :
    ¬ ∀ᶠ t : ℂ in 𝓝[≠] 0, temporalContactCoefficient ε C Q plane (t - (E : ℂ)) = 0 := by
  let A := temporalEnergyProjection (ε plane) E * Q plane * temporalEnergyProjection (ε plane) E
  have hpos : 0 < chargeInclusiveSquare A := by
    have hne : ∃ i j, A i j ≠ 0 := by
      by_contra! hn
      apply h
      ext i j
      exact hn i j
    obtain ⟨i, j, hij⟩ := hne
    unfold chargeInclusiveSquare
    apply Finset.sum_pos' (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg (A i' j'))
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun j' _ => Complex.normSq_nonneg (A i j'))
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hij⟩
  intro hz
  have ht := temporal_contact_double_pole ε C Q plane E
  have he : (fun t => t ^ 2 * temporalContactCoefficient ε C Q plane (t - (E : ℂ)))
      =ᶠ[𝓝[≠] 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [hz] with t ht'
    rw [ht', mul_zero]
  have hh := tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds
  exact (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne')) hh

end UV
