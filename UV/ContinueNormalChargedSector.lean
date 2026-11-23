import UV.ContinueNormalWindingIntegral
import UV.ContinueNormalZeroLoop
import UV.ContinueNormalPacketGraph

/-! The three charged components of the compressed normal-circle comparison.
The winding of a closed loop selects its displacement or frequency integral.
An open line retains both external spinor packets and its normal endpoints. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane

namespace UV

inductive NormalChargedSector (L : ℝ)
  | winding (n : ℕ) (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
  | zero (r : ℕ) (hr : 5 < r) (u : Fin r → UnitVector OSFourSpace)
  | line (r : ℕ) (u : Fin r → UnitVector OSFourSpace) (φ ψ : WilsonPacket) (z z' : Icc 0 L)

open NormalChargedSector

variable {L : ℝ}

def NormalChargedSector.segments : NormalChargedSector L → ℕ
  | .winding n _ _ => n+1
  | .zero r _ _ => r
  | .line r .. => r+1

def NormalChargedSector.Variables : NormalChargedSector L → Type
  | .winding n _ _ => (Fin n → ℝ) × OSFourSpace
  | .zero .. => NormalLoopFrequency
  | .line r .. => NormalOpenVariables r

instance (P : NormalChargedSector L) : MeasureSpace P.Variables := by
  cases P with
  | winding n => exact inferInstanceAs (MeasureSpace ((Fin n → ℝ) × OSFourSpace))
  | zero => exact inferInstanceAs (MeasureSpace NormalLoopFrequency)
  | line r => exact inferInstanceAs (MeasureSpace (NormalOpenVariables r))

instance (P : NormalChargedSector L) : SigmaFinite (volume : Measure P.Variables) := by
  cases P with
  | winding n => exact inferInstanceAs (SigmaFinite (volume : Measure ((Fin n → ℝ) × OSFourSpace)))
  | zero => exact inferInstanceAs (SigmaFinite (volume : Measure NormalLoopFrequency))
  | line r => exact inferInstanceAs (SigmaFinite (volume : Measure (NormalOpenVariables r)))

def NormalChargedSector.amplitude (m : ℝ) (w : ℤ) (Δ : OSFourSpace) (P : NormalChargedSector L) :
    (Fin P.segments → OSFourSpace) → P.Variables → ℂ :=
  match P with
  | .winding _ θ u => fun s t => if w = 0 then 0 else normalWindingTrace m L θ w u (fun j => t.2+s j) t.1
  | .zero _ _ u => fun s t => if w = 0 then normalZeroTrace m L u (fun j => t.1+s j) t.2 else 0
  | .line _ u φ ψ z z' => fun s => normalPacketWord m (z'.val-z.val+(w:ℝ)*L) u φ ψ Δ (fun t j => t.2+s j)

theorem NormalChargedSector.amplitude_measurable {Z : Type*} [MeasurableSpace Z] (m : ℝ) (w : ℤ) (P : NormalChargedSector L)
    {s : Z → Fin P.segments → OSFourSpace} (hs : ∀ j, Measurable (s · j))
    {Δ : Z → OSFourSpace} (hΔ : Measurable Δ) :
    Measurable (fun t : Z × P.Variables => P.amplitude m w (Δ t.1) (s t.1) t.2) := by
  cases P with
  | winding n θ u =>
    dsimp only [amplitude]
    split_ifs
    · exact measurable_const
    · exact normal_winding_trace_measurable m L θ w u
        (fun j => (measurable_snd.comp measurable_snd).add ((hs j).comp measurable_fst))
        (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
  | zero r hr u =>
    dsimp only [amplitude]
    split_ifs
    · exact normal_zero_trace_measurable m L u
        (fun j => (measurable_fst.comp measurable_snd).add ((hs j).comp measurable_fst))
        (measurable_snd.comp measurable_snd)
    · exact measurable_const
  | line r u φ ψ z z' =>
    exact wilson_packet_pair_measurable φ ψ (measurable_snd.comp measurable_snd) (hΔ.comp measurable_fst)
      (normal_open_word_args_measurable normalCoverGamma5 m _ u
        (fun j => (measurable_snd.comp measurable_snd).add ((hs j).comp measurable_fst))
        (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)))

/-- Each component has a summable absolute allowance, uniform in all photon
transfers, including transfers shared with other charged components. -/
theorem NormalChargedSector.amplitude_budget {m : ℝ} (hm : 0 < m) (hL : 0 < L) (P : NormalChargedSector L) :
    ∃ g : ℤ → ℝ, (∀ w, 0 ≤ g w) ∧ Summable g ∧ ∀ w Δ s,
      Integrable (P.amplitude m w Δ s) ∧ (∫ t, ‖P.amplitude m w Δ s t‖) ≤ g w := by
  cases P with
  | winding n θ u =>
    obtain ⟨B,hB,hsh⟩ := normal_volume_exponential_shifts (a := L/(2*((n:ℝ)+1))) (by positivity)
    let K := normalWindingBudget n m L B
    have hK : 0 ≤ K := by dsimp [K,normalWindingBudget]; positivity
    refine ⟨fun w => K * normalWindingRate m L w,fun w => mul_nonneg hK (Real.exp_pos _).le,
      (normal_winding_rate_summable hm hL).mul_left K,?_⟩
    intro w Δ s
    by_cases hw : w = 0
    · simpa only [amplitude,if_pos hw,norm_zero,integral_zero,integrable_zero,true_and] using
        mul_nonneg hK (Real.exp_pos (-(m/4)*|(w:ℝ)*L|)).le
    · simpa only [amplitude,if_neg hw] using normal_winding_trace_integral hm hL θ w hw u s volume B hsh
  | zero r hr u =>
    let K := (L/(2*Real.pi)*4)*(∫ x : NormalLoopFrequency, normalLoopWeight m x^r)
    have hK : 0 ≤ K := by
      exact mul_nonneg (by positivity) (integral_nonneg fun x => pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) r)
    refine ⟨fun w => if w = 0 then K else 0,fun w => by dsimp only; split_ifs <;> first | exact hK | exact le_rfl,
      summable_of_ne_finset_zero (s := {0}) (fun w hw => if_neg (by simpa using hw)),?_⟩
    intro w Δ s
    by_cases hw : w = 0
    · simpa only [amplitude,if_pos hw] using normal_zero_winding_six hm hL hr u s
    · simp only [amplitude,if_neg hw,norm_zero,integrable_zero,integral_zero,le_refl,and_self]
  | line r u φ ψ z z' =>
    let K := ((2:ℝ)^(r+1)*(4/m)^r)*((φ.cost+ψ.cost)/2)
    have hK : 0 ≤ K := by dsimp [K]; have := φ.cost_nonneg; have := ψ.cost_nonneg; positivity
    obtain ⟨hg,hw⟩ := normal_winding_majorant hm hL
    refine ⟨fun w => K*(Real.exp (m*L/2)*Real.exp (-(m*L/2)*|(w:ℝ)|)),fun w => by positivity,hg.mul_left K,?_⟩
    intro w Δ s
    have h := normal_packet_word_bound hm (z'.val-z.val+(w:ℝ)*L) u φ ψ Δ (fun t j => t.2+s j)
      (fun j => measurable_snd.add_const (s j))
    have hd : |z'.val-z.val| ≤ L := abs_le.mpr ⟨by linarith [z.property.2,z'.property.1],
      by linarith [z.property.1,z'.property.2]⟩
    refine ⟨h.1,h.2.trans ?_⟩
    calc _ = K * Real.exp (-(m/2)*|z'.val-z.val+(w:ℝ)*L|) := by dsimp [K]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (hw _ hd w) hK

end UV
