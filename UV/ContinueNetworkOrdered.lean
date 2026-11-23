import UV.ContinueNetworkSchwinger
import UV.ContinueNetworkTonelli
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact ordered Schwinger-sector costs. Successive integration of
the least time is the triangular ratio substitution for these monomials. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace UV

private def directionalOrderedCap : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 1
  | _ + 1, t => t 0

private theorem directionalOrderedCap_continuous (n : ℕ) :
    Continuous (directionalOrderedCap (n := n)) := by
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply 0

/-- The open part of the ordered sector; boundary hyperplanes can be
handled separately from the Schwinger endpoint. -/
def directionalOrderedSet : (n : ℕ) → Set (Fin n → ℝ)
  | 0 => univ
  | n + 1 => {t | t 0 ∈ Ioo 0 (directionalOrderedCap (fun i : Fin n => t i.succ)) ∧
      (fun i : Fin n => t i.succ) ∈ directionalOrderedSet n}

theorem directionalOrderedSet_open (n : ℕ) : IsOpen (directionalOrderedSet n) := by
  induction n with
  | zero => exact isOpen_univ
  | succ n ih =>
      let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun t i => t i.succ
      have ht : Continuous tail := continuous_pi fun i => continuous_apply i.succ
      change IsOpen ({t | 0 < t 0} ∩
        {t | t 0 < directionalOrderedCap (tail t)} ∩ tail ⁻¹' directionalOrderedSet n)
      exact ((isOpen_lt continuous_const (continuous_apply 0)).inter
        (isOpen_lt (continuous_apply 0) ((directionalOrderedCap_continuous n).comp ht))).inter
        (ih.preimage ht)

/-- The recursive set is the literal open simplex of increasing times. -/
theorem directionalOrderedSet_mem_iff {n : ℕ} (t : Fin n → ℝ) :
    t ∈ directionalOrderedSet n ↔ StrictMono t ∧ ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
  induction n with
  | zero => simp [directionalOrderedSet, StrictMono]
  | succ n ih =>
      let q : Fin n → ℝ := fun i => t i.succ
      cases n with
      | zero =>
          change t 0 ∈ Ioo 0 1 ∧ q ∈ directionalOrderedSet 0 ↔ _
          rw [ih q]
          constructor
          · rintro ⟨h0, -, -⟩
            have hz (i : Fin (0 + 1)) : i = 0 := Fin.ext (by omega)
            refine ⟨?_, fun i => ?_⟩
            · intro i j hij
              rw [hz i, hz j] at hij
              exact (lt_irrefl _ hij).elim
            · rw [hz i]
              exact h0
          · intro h
            exact ⟨h.2 0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
      | succ n =>
          change t 0 ∈ Ioo 0 (q 0) ∧ q ∈ directionalOrderedSet (n + 1) ↔ _
          rw [ih q]
          constructor
          · rintro ⟨h0, hm, hq⟩
            refine ⟨?_, fun i => ?_⟩
            · intro i j hij
              revert hij
              refine Fin.cases ?_ (fun i => ?_) i
              · refine Fin.cases ?_ (fun j _ => ?_) j
                · intro hj
                  exact (lt_irrefl _ hj).elim
                · exact h0.2.trans_le (hm.monotone (Fin.zero_le j))
              · refine Fin.cases ?_ (fun j hij => ?_) j
                · intro hj
                  exact (not_lt_of_ge (Fin.zero_le _) hj).elim
                · exact hm (Fin.strictMono_succ.lt_iff_lt.mp hij)
            · refine Fin.cases ?_ (fun j => ?_) i
              · exact ⟨h0.1, h0.2.trans (hq 0).2⟩
              · exact hq j
          · intro h
            refine ⟨⟨(h.2 0).1, h.1 (Fin.succ_pos 0)⟩, ?_, fun j => h.2 j.succ⟩
            intro i j hij
            exact h.1 (Fin.strictMono_succ hij)

private theorem directionalOrderedCap_pos {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ directionalOrderedSet n) : 0 < directionalOrderedCap t := by
  cases n with
  | zero => exact zero_lt_one
  | succ n => exact ht.1.1

private theorem directionalOrderedSet_cons_mem {n : ℕ} (s : ℝ) (t : Fin n → ℝ) :
    (@Fin.cons n (fun _ => ℝ) s t) ∈ directionalOrderedSet (n + 1) ↔
      s ∈ Ioo 0 (directionalOrderedCap t) ∧ t ∈ directionalOrderedSet n := by
  let y : Fin (n + 1) → ℝ := Fin.cons s t
  change y 0 ∈ Ioo 0 (directionalOrderedCap (fun i : Fin n => y i.succ)) ∧
    (fun i : Fin n => y i.succ) ∈ directionalOrderedSet n ↔ _
  simp only [y, Fin.cons_zero, Fin.cons_succ]

private theorem directionalEndpointMass_scale {a T : ℝ} (hT : 0 < T) :
    directionalEndpointMass a T = directionalEndpointMass a 1 * ENNReal.ofReal (T ^ a) := by
  rw [directionalEndpointMass_eq hT, directionalEndpointMass_eq zero_lt_one]
  by_cases ha : 0 < a
  · rw [if_pos ha, if_pos ha, Real.one_rpow, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · rw [if_neg ha, if_neg ha, ENNReal.top_mul
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hT a))]

def directionalOrderedDensity {n : ℕ} (a t : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (t i ^ (a i - 1))

theorem directionalOrderedDensity_measurable {n : ℕ} (a : Fin n → ℝ) :
    Measurable (directionalOrderedDensity a) := by
  apply Finset.measurable_prod
  intro i _
  exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).pow_const _)

def directionalOrderedCost {n : ℕ} (a : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in directionalOrderedSet n, directionalOrderedDensity a t

private def directionalOrderedMerge {n : ℕ} (a : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  a i.succ + if i.val = 0 then a 0 else 0

private theorem directionalOrderedDensity_merge {n : ℕ} (a : Fin (n + 1) → ℝ)
    (t : Fin n → ℝ) (ht : t ∈ directionalOrderedSet n) :
    ENNReal.ofReal (directionalOrderedCap t ^ a 0) *
      directionalOrderedDensity (fun i => a i.succ) t =
        directionalOrderedDensity (directionalOrderedMerge a) t := by
  cases n with
  | zero => simp [directionalOrderedDensity, directionalOrderedCap]
  | succ n =>
      have ht0 : 0 < t 0 := ht.1.1
      simp only [directionalOrderedDensity, Fin.prod_univ_succ, directionalOrderedMerge,
        Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false, add_zero,
        directionalOrderedCap, ← mul_assoc]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_add ht0]
      have he : a 0 + (a (Fin.succ 0) - 1) = a (Fin.succ 0) + a 0 - 1 := by ring
      rw [he]

/-- Exact recursive sector integration, with no strict endpoint
hypothesis and with a divergent factor retained as infinity. -/
theorem directionalOrderedCost_succ {n : ℕ} (a : Fin (n + 1) → ℝ) :
    directionalOrderedCost a =
      directionalEndpointMass (a 0) 1 * directionalOrderedCost (directionalOrderedMerge a) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f := (directionalOrderedSet (n + 1)).indicator (directionalOrderedDensity a)
  have hf : Measurable f := (directionalOrderedDensity_measurable a).indicator
    (directionalOrderedSet_open _).measurableSet
  have hcoord (s : ℝ) (t : Fin n → ℝ) : e.symm (s, t) = @Fin.cons n (fun _ => ℝ) s t := by
    change (0 : Fin (n + 1)).insertNth s t = @Fin.cons n (fun _ => ℝ) s t
    rw [Fin.insertNth_zero']
  have hmain : directionalOrderedCost a =
      ∫⁻ t : Fin n → ℝ, ∫⁻ s : ℝ, f (Fin.cons s t) := by
    unfold directionalOrderedCost
    rw [← lintegral_indicator (directionalOrderedSet_open _).measurableSet]
    change (∫⁻ t, f t) = _
    rw [← (he.symm e).lintegral_comp_emb e.symm.measurableEmbedding]
    change (∫⁻ q, (f ∘ e.symm) q ∂((volume : Measure ℝ).prod
      (volume : Measure (Fin n → ℝ)))) = _
    rw [lintegral_prod_symm' _ (hf.comp e.symm.measurable)]
    simp only [Function.comp_apply, hcoord]
  let F := (directionalOrderedSet n).indicator
    (directionalOrderedDensity (directionalOrderedMerge a))
  have hF : Measurable F := (directionalOrderedDensity_measurable _).indicator
    (directionalOrderedSet_open _).measurableSet
  rw [hmain]
  unfold directionalOrderedCost
  rw [← lintegral_indicator (directionalOrderedSet_open _).measurableSet,
    ← lintegral_const_mul _ hF]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ directionalOrderedSet n
  · have hcap := directionalOrderedCap_pos ht
    have hfun (s : ℝ) :
        f (Fin.cons s t) = (Ioo 0 (directionalOrderedCap t)).indicator
          (fun s => ENNReal.ofReal (s ^ (a 0 - 1)) *
            directionalOrderedDensity (fun i => a i.succ) t) s := by
      by_cases hs : s ∈ Ioo 0 (directionalOrderedCap t)
      · have hm := (directionalOrderedSet_cons_mem s t).mpr ⟨hs, ht⟩
        dsimp only [f]
        rw [indicator_of_mem hm, indicator_of_mem hs]
        simp only [directionalOrderedDensity, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      · have hm : @Fin.cons n (fun _ => ℝ) s t ∉ directionalOrderedSet (n + 1) :=
          fun hc => hs ((directionalOrderedSet_cons_mem s t).mp hc).1
        dsimp only [f]
        rw [indicator_of_notMem hm, indicator_of_notMem hs]
    have hm : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (a 0 - 1))) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
    simp only [hfun]
    rw [lintegral_indicator measurableSet_Ioo, lintegral_mul_const _ hm,
      ← directionalEndpointMass, directionalEndpointMass_scale hcap,
      mul_assoc, directionalOrderedDensity_merge a t ht]
    simp [F, ht]
  · have hzero (s : ℝ) : f (Fin.cons s t) = 0 := by
      have hm : @Fin.cons n (fun _ => ℝ) s t ∉ directionalOrderedSet (n + 1) :=
        fun hc => ht ((directionalOrderedSet_cons_mem s t).mp hc).2
      exact indicator_of_notMem hm _
    simp [hzero, F, ht]

/-- Cumulative exponent in the source's shortest-to-longest order. -/
def directionalOrderedPrefix {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin n, if i ≤ j then a i else 0

private theorem directionalOrderedPrefix_zero {n : ℕ} (a : Fin (n + 1) → ℝ) :
    directionalOrderedPrefix a 0 = a 0 := by
  simp [directionalOrderedPrefix, Fin.le_zero_iff]

private theorem directionalOrderedPrefix_succ {n : ℕ} (a : Fin (n + 1) → ℝ) (j : Fin n) :
    directionalOrderedPrefix a j.succ =
      directionalOrderedPrefix (directionalOrderedMerge a) j := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      simp only [directionalOrderedPrefix, Fin.sum_univ_succ, Fin.zero_le, if_true,
        Fin.succ_le_succ_iff, directionalOrderedMerge, Fin.val_zero, Fin.val_succ, Nat.succ_ne_zero,
        if_false, add_zero]
      ring

/-- Exact ordered monomial integral as a product of cumulative
endpoint factors. Thus the formula covers both convergence and failure. -/
theorem directionalOrderedCost_eq_prefix_product {n : ℕ} (a : Fin n → ℝ) :
    directionalOrderedCost a =
      ∏ j, directionalEndpointMass (directionalOrderedPrefix a j) 1 := by
  induction n with
  | zero =>
      simp [directionalOrderedCost, directionalOrderedDensity, directionalOrderedSet, volume_pi,
        Measure.pi_empty_univ]
  | succ n ih =>
      rw [directionalOrderedCost_succ, ih, Fin.prod_univ_succ, directionalOrderedPrefix_zero]
      simp_rw [directionalOrderedPrefix_succ]

theorem directionalOrderedCost_finite_iff {n : ℕ} (a : Fin n → ℝ) :
    directionalOrderedCost a < ⊤ ↔ ∀ j, 0 < directionalOrderedPrefix a j := by
  classical
  rw [directionalOrderedCost_eq_prefix_product]
  constructor
  · intro h j
    by_contra hnonpos
    have hj : directionalEndpointMass (directionalOrderedPrefix a j) 1 = ⊤ := by
      rw [directionalEndpointMass_eq zero_lt_one, if_neg hnonpos]
    have hrest : (∏ i ∈ Finset.univ.erase j,
        directionalEndpointMass (directionalOrderedPrefix a i) 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => directionalEndpointMass_ne_zero _ zero_lt_one
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hj, ENNReal.top_mul hrest] at h
    exact (lt_irrefl _ h)
  · intro h
    exact ENNReal.prod_lt_top fun j _ => (directionalEndpointMass_lt_top_iff zero_lt_one).2 (h j)

/-- Successive ratios of the ordered times, with the last time divided
by the upper endpoint one. -/
def directionalOrderedRatios : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _ => Fin.elim0
  | n + 1, t => Fin.cons (t 0 / directionalOrderedCap (fun i : Fin n => t i.succ))
      (directionalOrderedRatios (fun i : Fin n => t i.succ))

theorem directionalOrderedRatios_measurable {n : ℕ} :
    Measurable (directionalOrderedRatios (n := n)) := by
  induction n with
  | zero => exact measurable_pi_iff.mpr (fun i => Fin.elim0 i)
  | succ n ih =>
      have htail : Measurable (fun (t : Fin (n + 1) → ℝ) (i : Fin n) => t i.succ) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply i.succ)
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [directionalOrderedRatios,Fin.cons_zero] using (measurable_pi_apply 0).div
          ((directionalOrderedCap_continuous n).measurable.comp htail)
      · simpa only [directionalOrderedRatios,Fin.cons_succ] using (measurable_pi_apply j).comp (ih.comp htail)

theorem directionalOrderedRatios_ge_time {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ directionalOrderedSet n) (i : Fin n) : t i ≤ directionalOrderedRatios t i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      let q : Fin n → ℝ := fun j => t j.succ
      have ht' : t 0 ∈ Ioo 0 (directionalOrderedCap q) ∧ q ∈ directionalOrderedSet n := ht
      refine Fin.cases ?_ (fun j => ?_) i
      · have hcap := directionalOrderedCap_pos ht'.2
        have hcap₁ : directionalOrderedCap q ≤ 1 := by
          cases n with
          | zero => exact le_rfl
          | succ n => exact ((directionalOrderedSet_mem_iff q).1 ht'.2).2 0 |>.2.le
        change t 0 ≤ t 0/directionalOrderedCap q
        rw [le_div_iff₀ hcap]
        exact mul_le_of_le_one_right ht'.1.1.le hcap₁
      · exact ih ht'.2 j

private theorem directional_ratio_scale (a : ℝ) {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ s in Ioo 0 T, ENNReal.ofReal (s ^ (a-1)) * g (s/T)) =
      ENNReal.ofReal (T^a) * ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (r ^ (a-1)) * g r := by
  let u := fun r : ℝ => T*r
  have himage : u '' Ioo 0 1 = Ioo 0 T := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨mul_pos hT hr.1, by simpa [u] using mul_lt_mul_of_pos_left hr.2 hT⟩
    · intro hx
      refine ⟨x/T,⟨div_pos hx.1 hT, (div_lt_one hT).mpr hx.2⟩,?_⟩
      dsimp [u]
      field_simp
  have hd (x : ℝ) (_hx : x ∈ Ioo (0:ℝ) 1) : HasDerivWithinAt u T (Ioo 0 1) x := by
    simpa [u] using ((hasDerivAt_id x).const_mul T).hasDerivWithinAt (s := Ioo 0 1)
  have hi : Set.InjOn u (Ioo 0 1) := (mul_right_injective₀ hT.ne').injOn
  have hG : Measurable (fun r : ℝ => ENNReal.ofReal (r^(a-1))*g r) :=
    (measurable_id.pow_const _).ennreal_ofReal.mul hg
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hi,
    ← lintegral_const_mul _ hG]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  change ENNReal.ofReal |T| * (ENNReal.ofReal ((T*r) ^ (a-1)) * g (T*r/T)) =
    ENNReal.ofReal (T^a) * (ENNReal.ofReal (r ^ (a-1)) * g r)
  have harg : T*r/T = r := by field_simp
  have hpow : T*(T*r)^(a-1) = T^a*r^(a-1) := by
    calc _ = T^((1:ℝ)+(a-1))*r^(a-1) := by
          rw [Real.mul_rpow hT.le hr.1.le,Real.rpow_add hT,Real.rpow_one,mul_assoc]
    _ = _ := by rw [show (1:ℝ)+(a-1)=a by ring]
  rw [harg,abs_of_pos hT,← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul hT.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _),hpow]

def directionalWeightedSector {n : ℕ} (a : Fin n → ℝ) (g : Fin n → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in directionalOrderedSet n, directionalOrderedDensity a t *
    ∏ i, g i (directionalOrderedRatios t i)

private theorem directionalWeightedSector_succ {n : ℕ} (a : Fin (n+1) → ℝ)
    (g : Fin (n+1) → ℝ → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    directionalWeightedSector a g =
      (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (r ^ (a 0-1)) * g 0 r) *
        directionalWeightedSector (directionalOrderedMerge a) (fun j => g j.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
  let J := fun t => directionalOrderedDensity a t * ∏ i, g i (directionalOrderedRatios t i)
  have hJ : Measurable J := (directionalOrderedDensity_measurable a).mul
    (Finset.measurable_prod _ fun i _ => (hg i).comp ((measurable_pi_apply i).comp directionalOrderedRatios_measurable))
  let f := (directionalOrderedSet (n+1)).indicator J
  have hf : Measurable f := hJ.indicator (directionalOrderedSet_open _).measurableSet
  let K := fun t => directionalOrderedDensity (directionalOrderedMerge a) t *
    ∏ i : Fin n, g i.succ (directionalOrderedRatios t i)
  have hK : Measurable K := (directionalOrderedDensity_measurable _).mul
    (Finset.measurable_prod _ fun i _ => (hg i.succ).comp
      ((measurable_pi_apply i).comp directionalOrderedRatios_measurable))
  let c := ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (r ^ (a 0-1)) * g 0 r
  unfold directionalWeightedSector
  rw [← lintegral_indicator (directionalOrderedSet_open _).measurableSet,
    ← lintegral_const_mul _ hK, ← lintegral_indicator (directionalOrderedSet_open _).measurableSet]
  change (∫⁻ t, f t) = ∫⁻ t, (directionalOrderedSet n).indicator (fun t => c*K t) t
  rw [← (he.symm e).lintegral_comp_emb e.symm.measurableEmbedding]
  change (∫⁻ q, (f ∘ e.symm) q ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))) = _
  rw [lintegral_prod_symm' _ (hf.comp e.symm.measurable)]
  apply lintegral_congr
  intro t
  have hcoord (s : ℝ) : e.symm (s,t) = @Fin.cons n (fun _ => ℝ) s t := by
    change (0 : Fin (n+1)).insertNth (α := fun _ => ℝ) s t = _
    rw [Fin.insertNth_zero']
  simp only [Function.comp_apply,hcoord]
  by_cases ht : t ∈ directionalOrderedSet n
  · let T := directionalOrderedCap t
    let K' := directionalOrderedDensity (fun i => a i.succ) t *
      ∏ i : Fin n, g i.succ (directionalOrderedRatios t i)
    have hf' (s : ℝ) : f (Fin.cons s t) = (Ioo 0 T).indicator
        (fun s => (ENNReal.ofReal (s^(a 0-1)) * g 0 (s/T)) * K') s := by
      by_cases hs : s ∈ Ioo 0 T
      · dsimp only [f]
        rw [indicator_of_mem ((directionalOrderedSet_cons_mem s t).2 ⟨hs,ht⟩),indicator_of_mem hs]
        simp only [J,directionalOrderedDensity,directionalOrderedRatios,Fin.prod_univ_succ,
          Fin.cons_zero,Fin.cons_succ,T,K']
        ac_rfl
      · dsimp only [f]
        rw [indicator_of_notMem (fun h => hs ((directionalOrderedSet_cons_mem s t).1 h).1),
          indicator_of_notMem hs]
    simp only [hf']
    have hG : Measurable (fun s : ℝ => ENNReal.ofReal (s^(a 0-1)) * g 0 (s/T)) :=
      (measurable_id.pow_const _).ennreal_ofReal.mul ((hg 0).comp (measurable_id.div_const T))
    rw [lintegral_indicator measurableSet_Ioo,lintegral_mul_const _ hG,
      directional_ratio_scale (a 0) (directionalOrderedCap_pos ht) _ (hg 0),indicator_of_mem ht]
    change (ENNReal.ofReal (T^a 0)*c)*K' = c*K t
    rw [mul_comm (ENNReal.ofReal (T^a 0)),mul_assoc]
    congr 1
    unfold K'
    rw [← mul_assoc,directionalOrderedDensity_merge a t ht]
  · have hf' (s : ℝ) : f (Fin.cons s t)=0 := by
      exact indicator_of_notMem (fun h => ht ((directionalOrderedSet_cons_mem s t).1 h).2) _
    simp [hf',ht]

/-- The exact triangular ratio change of variables with an arbitrary
nonnegative measurable factor on each ratio. All cumulative powers,
including logarithmically divergent endpoints, are retained. -/
theorem directionalWeightedSector_eq_prefix_product {n : ℕ} (a : Fin n → ℝ)
    (g : Fin n → ℝ → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    directionalWeightedSector a g =
      ∏ j, ∫⁻ r in Ioo (0:ℝ) 1,
        ENNReal.ofReal (r ^ (directionalOrderedPrefix a j-1))*g j r := by
  induction n with
  | zero =>
    simp [directionalWeightedSector,directionalOrderedDensity,directionalOrderedSet,volume_pi,
      Measure.pi_empty_univ]
  | succ n ih =>
    rw [directionalWeightedSector_succ a g hg,ih _ _ (fun i => hg i.succ),Fin.prod_univ_succ,
      directionalOrderedPrefix_zero]
    simp_rw [directionalOrderedPrefix_succ]

end UV
