import UV.ContinueWilsonGraphHopSum
import UV.ContinueWilsonGraphTwoPoint
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! A photon inserted at fraction s of a link is evaluated at the
polygon start plus s times its displacement. Regrouping these phases
gives the shifts in the Fourier transforms of the marked hops. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
open scoped BigOperators RealInnerProductSpace unitInterval

namespace UV

def wilsonVisitFraction {a n : ℕ} (f : Fin a → Fin (n+1)) (s : Fin a → I) (i : Fin a) (j : Fin (n+1)) : ℝ :=
  if j < f i then 1 else if j = f i then (s i : ℝ) else 0

def wilsonVisitPosition {a n : ℕ} (f : Fin a → Fin (n+1)) (s : Fin a → I)
    (d : Fin (n+1) → OSFourSpace) (i : Fin a) : OSFourSpace :=
  (∑ j, if j < f i then d j else 0) + (s i : ℝ) • d (f i)

def wilsonVisitShift {a n : ℕ} (f : Fin a → Fin (n+1)) (s : Fin a → I)
    (k : Fin a → OSFourSpace) (j : Fin (n+1)) : OSFourSpace :=
  ∑ i, wilsonVisitFraction f s i j • k i

theorem wilson_visit_position {a n : ℕ} (f : Fin a → Fin (n+1)) (s : Fin a → I)
    (d : Fin (n+1) → OSFourSpace) (i : Fin a) :
    wilsonVisitPosition f s d i = ∑ j, wilsonVisitFraction f s i j • d j := by
  classical
  have h (j) : wilsonVisitFraction f s i j • d j =
      (if j < f i then d j else 0) + (if j = f i then (s i : ℝ) • d j else 0) := by
    by_cases h₁ : j < f i
    · simp [wilsonVisitFraction,h₁,h₁.ne]
    · by_cases h₂ : j = f i <;> simp [wilsonVisitFraction,h₁,h₂]
  simp only [h,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,wilsonVisitPosition]

theorem wilson_visit_phase {a n : ℕ} (f : Fin a → Fin (n+1)) (s : Fin a → I)
    (d : Fin (n+1) → OSFourSpace) (k : Fin a → OSFourSpace) :
    (∑ i, ⟪k i,wilsonVisitPosition f s d i⟫) = ∑ j, ⟪wilsonVisitShift f s k j,d j⟫ := by
  simp only [wilson_visit_position,wilsonVisitShift,inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right]
  exact Finset.sum_comm

theorem wilson_visit_shift_measurable {Z : Type*} [MeasurableSpace Z] {a n : ℕ}
    (f : Fin a → Fin (n+1)) {s : Z → Fin a → I} (hs : ∀ i, Measurable (s · i))
    {k : Z → Fin a → OSFourSpace} (hk : ∀ i, Measurable (k · i)) (j : Fin (n+1)) :
    Measurable (fun z => wilsonVisitShift f (s z) (k z) j) := by
  apply Finset.measurable_sum
  intro i _
  apply Measurable.smul _ (hk i)
  by_cases h₁ : j < f i
  · simpa only [wilsonVisitFraction,if_pos h₁] using (measurable_const (a := (1:ℝ)) : Measurable (fun _ : Z => (1:ℝ)))
  · by_cases h₂ : j = f i
    · simpa only [wilsonVisitFraction,if_neg h₁,if_pos h₂] using measurable_subtype_coe.comp (hs i)
    · simpa only [wilsonVisitFraction,if_neg h₁,if_neg h₂] using (measurable_const (a := (0:ℝ)) : Measurable (fun _ : Z => (0:ℝ)))

variable {V C D ι : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype D] [Fintype ι]

abbrev WilsonPathFractions (a : V → ℕ) := (j : Sigma (fun v => Fin (a v))) → I

abbrev WilsonPhotonPaths (a : V → ℕ) (C : Type*) := WilsonPathFractions a × (C → OSFourSpace)

def wilsonHardPathWeight (a : V → ℕ) (L ρ : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (z : WilsonPhotonPaths a C) : ℂ :=
  (wilsonHardPhotonProduct ρ (wilsonShellPhotonForm L T) chord tree route z.2 : ℂ)

omit [DecidableEq V] in
theorem wilson_hard_path_weight (a : V → ℕ) {L ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (chord : C → WilsonPhotonPolarizations)
    (tree : D → WilsonPhotonPolarizations) (route : (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ e, Measurable (route · e)) :
    let w := wilsonHardPathWeight a L ρ T chord tree route
    Measurable w ∧ Integrable w ((volume : Measure (WilsonPathFractions a)).prod (Measure.pi (fun _ : C => volume))) :=
  ⟨Complex.continuous_ofReal.measurable.comp ((wilson_hard_product_measurable ρ
     (wilson_shell_form_continuous L T) chord tree hr).comp (measurable_snd (α := WilsonPathFractions a))),
   ((wilson_hard_product_integrable hL hρ T chord tree hr).ofReal (𝕜 := ℂ)).comp_snd
     (ν := Measure.pi (fun _ : C => (volume : Measure OSFourSpace))) (volume : Measure (WilsonPathFractions a))⟩

omit [Fintype V] [DecidableEq V] [Fintype C] in
theorem wilson_path_shifts_measurable {a : V → ℕ} (k : (v : V) → (C → OSFourSpace) → Fin (a v) → OSFourSpace)
    (hk : ∀ v i, Measurable (k v · i)) (n : V → ℕ) (f : WilsonMarkAllocation a n) (v : V) (j : Fin (n v+1)) :
    Measurable (fun z : WilsonPhotonPaths a C => wilsonVisitShift (f v) (fun i => z.1 ⟨v,i⟩) (k v z.2) j) :=
  wilson_visit_shift_measurable _ (fun i => (measurable_pi_apply (⟨v,i⟩ : Sigma (fun x => Fin (a x)))).comp measurable_fst)
    (fun i => (hk v i).comp measurable_snd) _

/-- A complete fixed-order closed-circulation hard integral. The external
momenta and every path fraction shift the charged words according to the
straight links. Tree transfers are measurable functions of the same chord
momenta. The bound sums every independent length and every allocation. -/
theorem wilson_hard_closed_graph_sum {L lam ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {a : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ e, Measurable (route · e))
    (k : (v : V) → (C → OSFourSpace) → Fin (a v) → OSFourSpace) (hk : ∀ v i, Measurable (k v · i)) :
    let μ := (volume : Measure (WilsonPathFractions a)).prod (Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
    let w := fun z : WilsonPathFractions a × (C → OSFourSpace) =>
      (wilsonHardPhotonProduct ρ (wilsonShellPhotonForm L T) chord tree route z.2 : ℂ)
    let q := fun (n : V → ℕ) (f : WilsonMarkAllocation a n) v (z : WilsonPathFractions a × (C → OSFourSpace)) =>
      wilsonVisitShift (f v) (fun i => z.1 ⟨v,i⟩) (k v z.2)
    (∀ n f, Integrable (wilsonGraphWord w L T u f (q n f)) (μ.prod (Measure.pi (fun _ : V => volume)))) ∧
      Summable (fun n : V → ℕ => (∏ v, lam^(n v+1)) * ∑ f : WilsonMarkAllocation a n,
        ∫ t, ‖wilsonGraphWord w L T u f (q n f) t‖ ∂μ.prod (Measure.pi (fun _ : V => volume))) := by
  dsimp only
  obtain ⟨hmw,hw⟩ := wilson_hard_path_weight a hL hρ T chord tree route hr
  have hq := wilson_path_shifts_measurable k hk
  let μ := (volume : Measure (WilsonPathFractions a)).prod (Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
  haveI : SFinite μ := Measure.prod.instSFinite (μ := (volume : Measure (WilsonPathFractions a)))
    (ν := Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
  exact ⟨fun n f => (wilson_graph_words_bound hL T u f (hq n f) μ hmw hw).1,
    wilson_graph_all_lengths_summable hL hlam hl T u _ hq μ hmw hw⟩

end UV
