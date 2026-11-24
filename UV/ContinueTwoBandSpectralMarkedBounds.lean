import UV.ContinueTwoBandSpectralExpansion
import UV.ContinueTwoBandSpatialWord

/-! Absolute frequency bounds on complete temporal vertices. Two different
intervals in a loop may carry arbitrarily many scalar marks, simultaneous hard
transfers, cancelling partial sums, or exact zero transfers. The other
intervals have uniform supremum bounds. -/

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology

namespace UV.SectorPlane

theorem hopping_interval_norm (a s : ℝ) :
    ‖hoppingInterval a s‖ = twoBandFrequencyBound |a| s := by
  have h : Complex.normSq ((a:ℂ)-I*s) = s^2+a^2 := by
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  simp only [hoppingInterval,norm_inv,Complex.norm_def,h,twoBandFrequencyBound,sq_abs]

private def amplitudeScale (m : ℝ) := max 1 m⁻¹

private theorem scale_one (m : ℝ) : 1 ≤ amplitudeScale m := le_max_left _ _
private theorem scale_nonneg (m : ℝ) : 0 ≤ amplitudeScale m := zero_le_one.trans (scale_one _)

private theorem word_sup {m a : ℝ} (hm : 0 < m) (ha : |a|=m) (B : List ℝ) (s : ℝ) :
    ‖hoppingWord a B s‖ ≤ (amplitudeScale m)^B.length := by
  induction B with
  | nil => simp [hoppingWord]
  | cons b B ih =>
    change ‖hoppingInterval a (s+b)*hoppingWord a B s‖ ≤ _
    rw [norm_mul,hopping_interval_norm,ha,List.length_cons,pow_succ']
    exact mul_le_mul ((twoBand_resolvent_bound hm 0 _).2.trans (le_max_right _ _))
      ih (norm_nonneg _) (scale_nonneg _)

private def termShape (m : ℝ) (t : HoppingTerm) (s : ℝ) :=
  ‖t.1‖ * twoBandFrequencyBound m (s+t.2.headD 0)

private def envelope (m : ℝ) (P : List HoppingTerm) (s : ℝ) :=
  (P.map (fun t => termShape m t s)).sum

private theorem shape_nonneg (m : ℝ) (t : HoppingTerm) (s : ℝ) : 0 ≤ termShape m t s := by
  unfold termShape twoBandFrequencyBound
  positivity

private theorem envelope_nonneg (m : ℝ) (P : List HoppingTerm) (s : ℝ) : 0 ≤ envelope m P s := by
  induction P with
  | nil => exact le_refl _
  | cons t ts ih => exact add_nonneg (shape_nonneg _ _ _) ih

private theorem eval_continuous {a : ℝ} (ha : a ≠ 0) (P : List HoppingTerm) :
    Continuous (hoppingEval a P) := by
  induction P with
  | nil => exact continuous_const
  | cons t ts ih => exact (continuous_const.mul (hopping_word_differentiable ha _).continuous).add ih

private theorem eval_bound {m a : ℝ} (hm : 0<m) (ha : |a|=m) {K : ℕ}
    {P : List HoppingTerm} (hP : HoppingDegree K P) (s : ℝ) :
    ‖hoppingEval a P s‖ ≤ (amplitudeScale m)^K * envelope m P s := by
  induction P with
  | nil => simp [hoppingEval,envelope]
  | cons t ts ih =>
    have h := hP t List.mem_cons_self
    have hi := ih (fun p hp => hP p (List.mem_cons_of_mem _ hp))
    have ht : ‖t.1*hoppingWord a t.2 s‖ ≤ (amplitudeScale m)^K * termShape m t s := by
      obtain ⟨c,B⟩ := t
      cases B with
      | nil => simp at h
      | cons b B =>
        have hlen : B.length ≤ K := by simpa using (Nat.le_succ _).trans h.2
        change ‖c*(hoppingInterval a (s+b)*hoppingWord a B s)‖ ≤
          (amplitudeScale m)^K * (‖c‖*twoBandFrequencyBound m (s+b))
        rw [norm_mul,norm_mul,←mul_assoc,hopping_interval_norm,ha,mul_comm ((amplitudeScale m)^K)]
        exact mul_le_mul_of_nonneg_left ((word_sup hm ha B s).trans (pow_le_pow_right₀ (scale_one _) hlen))
          (by unfold twoBandFrequencyBound; positivity)
    change ‖t.1*hoppingWord a t.2 s + hoppingEval a ts s‖ ≤ (amplitudeScale m)^K *
      (termShape m t s + envelope m ts s)
    rw [mul_add]
    exact (norm_add_le _ _).trans (add_le_add ht hi)

private theorem envelope_sup {m : ℝ} (hm : 0 < m) (P : List HoppingTerm) (s : ℝ) :
    envelope m P s ≤ m⁻¹ * hoppingCost P := by
  induction P with
  | nil => simp [envelope,hoppingCost]
  | cons t P ih =>
    change ‖t.1‖*twoBandFrequencyBound m _ + envelope m P s ≤ m⁻¹*(‖t.1‖+hoppingCost P)
    rw [mul_add,mul_comm m⁻¹ ‖t.1‖]
    exact add_le_add (mul_le_mul_of_nonneg_left (twoBand_resolvent_bound hm 0 _).2 (norm_nonneg _)) ih

private theorem shape_pair {m : ℝ} (hm : 0 < m) (t u : HoppingTerm) :
    Integrable (fun s => termShape m t s * termShape m u s) ∧
    (∫ s, termShape m t s * termShape m u s) ≤ ‖t.1‖*‖u.1‖*(Real.pi/m) := by
  have h := twoBand_frequency_product hm (t.2.headD 0) (u.2.headD 0)
  have he (s : ℝ) : termShape m t s * termShape m u s =
      (‖t.1‖*‖u.1‖)*(twoBandFrequencyBound m (s+t.2.headD 0)*twoBandFrequencyBound m (s+u.2.headD 0)) := by
    unfold termShape
    ring
  simp_rw [he]
  rw [integral_const_mul]
  exact ⟨h.1.const_mul _, mul_le_mul_of_nonneg_left h.2 (by positivity)⟩

private theorem shape_env {m : ℝ} (hm : 0 < m) (t : HoppingTerm) (Q : List HoppingTerm) :
    Integrable (fun s => termShape m t s * envelope m Q s) ∧
    (∫ s, termShape m t s * envelope m Q s) ≤ ‖t.1‖*hoppingCost Q*(Real.pi/m) := by
  induction Q with
  | nil => simp [envelope,hoppingCost]
  | cons u Q ih =>
    have he (s : ℝ) : termShape m t s*envelope m (u::Q) s =
      termShape m t s*termShape m u s + termShape m t s*envelope m Q s := mul_add _ _ _
    simp_rw [he]
    have h := shape_pair hm t u
    rw [integral_add h.1 ih.1]
    refine ⟨h.1.add ih.1,(add_le_add h.2 ih.2).trans_eq ?_⟩
    simp only [hoppingCost,List.map_cons,List.sum_cons]
    ring

private theorem env_pair {m : ℝ} (hm : 0 < m) (P Q : List HoppingTerm) :
    Integrable (fun s => envelope m P s*envelope m Q s) ∧
    (∫ s, envelope m P s*envelope m Q s) ≤ hoppingCost P*hoppingCost Q*(Real.pi/m) := by
  induction P with
  | nil => simp [envelope,hoppingCost]
  | cons t P ih =>
    have he (s : ℝ) : envelope m (t::P) s*envelope m Q s =
      termShape m t s*envelope m Q s+envelope m P s*envelope m Q s := add_mul _ _ _
    simp_rw [he]
    have h := shape_env hm t Q
    rw [integral_add h.1 ih.1]
    refine ⟨h.1.add ih.1,(add_le_add h.2 ih.2).trans_eq ?_⟩
    simp only [hoppingCost,List.map_cons,List.sum_cons]
    ring

/-- Mark-count constant independent of every frequency and translation. -/
def hoppingIntervalConstant (m : ℝ) (d : ℕ) : ℝ :=
  (amplitudeScale m)^(1+d)*hoppingCountFactor 1 d

theorem hopping_interval_constant_nonneg (m : ℝ) (n : ℕ) : 0 ≤ hoppingIntervalConstant m n :=
  mul_nonneg (pow_nonneg (scale_nonneg m) _) (hopping_count_nonneg _ _)

private theorem singleton_expansion {m a : ℝ} (hm : 0<m) (ha : |a|=m) (b : ℝ) (V : List ℝ) :
    ∃ P : List HoppingTerm, hoppingMarks V (fun s => hoppingInterval a (s+b)) = hoppingEval a P ∧
      HoppingDegree (1+V.length) P ∧ hoppingCost P ≤ hoppingCountFactor 1 V.length * hoppingWeight V := by
  have han : a ≠ 0 := abs_pos.mp (ha.symm ▸ hm)
  let Q : List HoppingTerm := [(1,[b])]
  have he : hoppingEval a Q = fun s => hoppingInterval a (s+b) := by funext; simp [Q,hoppingEval,hoppingWord]
  have hQ : HoppingDegree 1 Q := by
    intro t ht
    have ht' : t = (1,[b]) := by simpa [Q] using ht
    simp [ht']
  have h := hopping_expansion_cost hQ V
  exact ⟨_,he ▸ hopping_expansion_exact han V Q,h.1,by simpa [Q,hoppingCost] using h.2⟩

/-- Uniform supremum bound supplying an independent factor `1/(1+|ν|)` for
every scalar end on this interval. -/
theorem hopping_marked_interval_sup {m a : ℝ} (hm : 0 < m) (ha : |a|=m) (b : ℝ) (V : List ℝ) (s : ℝ) :
    ‖hoppingMarks V (fun x => hoppingInterval a (x+b)) s‖ ≤
      m⁻¹*hoppingIntervalConstant m V.length*hoppingWeight V := by
  obtain ⟨P,he,hd,hc⟩ := singleton_expansion hm ha b V
  rw [he]
  calc
    _ ≤ _ := eval_bound hm ha hd s
    _ ≤ _ := mul_le_mul_of_nonneg_left (envelope_sup hm P s) (pow_nonneg (scale_nonneg m) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (by positivity)) (pow_nonneg (scale_nonneg m) _)
    _ = _ := by unfold hoppingIntervalConstant; ring

/-- Two distinct interval factors have an absolute charged-frequency integral
uniform in every external frequency and every real routing shift. Taking the
same factor twice gives its squared L² bound. -/
theorem hopping_marked_interval_pair {m a c : ℝ} (hm : 0 < m) (ha : |a|=m) (hc : |c|=m)
    (b d : ℝ) (V W : List ℝ) :
    let F := hoppingMarks V (fun x => hoppingInterval a (x+b))
    let G := hoppingMarks W (fun x => hoppingInterval c (x+d))
    Integrable (fun s => F s*G s) ∧
      (∫ s, ‖F s*G s‖) ≤ (Real.pi/m)*
        (hoppingIntervalConstant m V.length*hoppingWeight V)*
        (hoppingIntervalConstant m W.length*hoppingWeight W) := by
  dsimp only
  obtain ⟨P,hP,hPd,hPc⟩ := singleton_expansion hm ha b V
  obtain ⟨Q,hQ,hQd,hQc⟩ := singleton_expansion hm hc d W
  rw [hP,hQ]
  have hi := env_pair hm P Q
  let H := (amplitudeScale m)^(1+V.length)*(amplitudeScale m)^(1+W.length)
  have hH : 0 ≤ H := mul_nonneg (pow_nonneg (scale_nonneg m) _) (pow_nonneg (scale_nonneg m) _)
  have hle (s : ℝ) : ‖hoppingEval a P s*hoppingEval c Q s‖ ≤ H*(envelope m P s*envelope m Q s) := by
    rw [norm_mul]
    calc
      _ ≤ _ := mul_le_mul (eval_bound hm ha hPd s) (eval_bound hm hc hQd s) (norm_nonneg _)
        (mul_nonneg (pow_nonneg (scale_nonneg m) _) (envelope_nonneg _ _ _))
      _ = _ := by unfold H; ring
  have hi' := hi.1.const_mul H
  have hf : Integrable (fun s => hoppingEval a P s*hoppingEval c Q s) :=
    hi'.mono' (((eval_continuous (abs_pos.mp (ha.symm ▸ hm)) _).mul
      (eval_continuous (abs_pos.mp (hc.symm ▸ hm)) _)).aestronglyMeasurable) (ae_of_all _ hle)
  have hcost : 0 ≤ hoppingCost Q := by
    clear * - Q
    induction Q with
    | nil => exact le_refl _
    | cons t Q ih => exact add_nonneg (norm_nonneg _) ih
  refine ⟨hf,(integral_mono hf.norm hi' hle).trans ?_⟩
  rw [integral_const_mul]
  have hx := mul_le_mul hPc hQc hcost (mul_nonneg (hopping_count_nonneg _ _) (hopping_weight_nonneg _))
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.2 hH
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ Real.pi/m)) hH
    _ = _ := by unfold H hoppingIntervalConstant; ring

end UV.SectorPlane
