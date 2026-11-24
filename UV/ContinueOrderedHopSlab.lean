import UV.ContinueOrderedHopTrace
import Mathlib.Analysis.Normed.Group.Tannery
import UV.ContinueOrderedCurrentReturn

/-! Per-unit-time normalization on the symmetric vacuum slab. Integrating
the base time of a translated path clips the slab by the time span of its
vertices. This boundary factor disappears both inside the path integrals
and after summing the absolute hopping expansion. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace UV.SectorPlane

private def slabHigh {ι : Type*} (v : ι → ℝ) : List ι → ℝ
  | [] => 0
  | j::L => max (v j) (slabHigh v L)

private theorem slab_high_nonneg {ι : Type*} (v : ι → ℝ) (L : List ι) : 0 ≤ slabHigh v L := by
  induction L with
  | nil => exact le_rfl
  | cons j L ih => exact ih.trans (le_max_right _ _)

private theorem slab_high_le_iff {ι : Type*} (v : ι → ℝ) (L : List ι) (r : ℝ) :
    slabHigh v L ≤ r ↔ 0 ≤ r ∧ ∀ j ∈ L, v j ≤ r := by
  induction L with
  | nil => simp [slabHigh]
  | cons j L ih => simp only [slabHigh,max_le_iff,ih,List.mem_cons,forall_eq_or_imp]; tauto

private theorem slab_high_continuous {ι X : Type*} [TopologicalSpace X] (v : ι → X → ℝ)
    (h : ∀ j, Continuous (v j)) (L : List ι) : Continuous (fun x => slabHigh (fun j => v j x) L) := by
  induction L with
  | nil => exact continuous_const
  | cons j L ih => exact (h j).max ih

def orderedHopTimeSpan {n : ℕ} (v : Fin (n+1) → ℝ) : ℝ :=
  slabHigh v (List.ofFn id) + slabHigh (fun j => -v j) (List.ofFn id)

def orderedHopSlabOrigins {n : ℕ} (T : ℝ) (v : Fin (n+1) → ℝ) : Set ℝ :=
  {t | t ∈ Icc (-T/2) (T/2) ∧ ∀ j, t+v j ∈ Icc (-T/2) (T/2)}

def orderedHopSlabFraction {n : ℕ} (T : ℝ) (v : Fin (n+1) → ℝ) : ℝ :=
  max (T-orderedHopTimeSpan v) 0 / T

theorem orderedHop_time_span_nonneg {n : ℕ} (v : Fin (n+1) → ℝ) : 0 ≤ orderedHopTimeSpan v :=
  add_nonneg (slab_high_nonneg _ _) (slab_high_nonneg _ _)

theorem orderedHop_slab_origins_eq {n : ℕ} (T : ℝ) (v : Fin (n+1) → ℝ) :
    orderedHopSlabOrigins T v = Icc (-T/2+slabHigh (fun j => -v j) (List.ofFn id))
      (T/2-slabHigh v (List.ofFn id)) := by
  ext t
  change (_ ∧ ∀ j, _ ∈ Icc _ _) ↔ _ ≤ t ∧ t ≤ _
  rw [show -T/2+slabHigh (fun j => -v j) (List.ofFn id) ≤ t ↔
        slabHigh (fun j => -v j) (List.ofFn id) ≤ t+T/2 by constructor <;> intro H <;> linarith,
    show t ≤ T/2-slabHigh v (List.ofFn id) ↔ slabHigh v (List.ofFn id) ≤ T/2-t by
      constructor <;> intro H <;> linarith, slab_high_le_iff,slab_high_le_iff]
  simp only [List.mem_ofFn,exists_eq,forall_const,Function.id_def,mem_Icc]
  constructor
  · rintro ⟨⟨ha,hb⟩,hv⟩
    exact ⟨⟨by linarith,fun j => by linarith [(hv j).1]⟩,⟨by linarith,fun j => by linarith [(hv j).2]⟩⟩
  · rintro ⟨⟨ha,hv⟩,⟨hb,hw⟩⟩
    refine ⟨⟨by linarith,by linarith⟩,fun j => ⟨?_,?_⟩⟩
    · linarith [hv j]
    · linarith [hw j]

/-- Exact base-time integral divided by the slab width, including paths
which cannot fit inside that slab at any translate. -/
theorem orderedHop_slab_fraction_eq_volume {n : ℕ} (T : ℝ) (v : Fin (n+1) → ℝ) :
    (volume.real (orderedHopSlabOrigins T v))/T = orderedHopSlabFraction T v := by
  rw [orderedHop_slab_origins_eq,Real.volume_real_Icc]
  unfold orderedHopSlabFraction orderedHopTimeSpan
  congr 2
  ring

theorem orderedHop_slab_fraction_unit {n : ℕ} {T : ℝ} (hT : 0 < T) (v : Fin (n+1) → ℝ) :
    0 ≤ orderedHopSlabFraction T v ∧ orderedHopSlabFraction T v ≤ 1 := by
  have hs := orderedHop_time_span_nonneg v
  unfold orderedHopSlabFraction
  refine ⟨div_nonneg (le_max_right _ _) hT.le, (div_le_one hT).mpr (max_le (by linarith) hT.le)⟩

theorem orderedHop_slab_fraction_tendsto {n : ℕ} (v : Fin (n+1) → ℝ) :
    Tendsto (fun T : ℝ => orderedHopSlabFraction T v) atTop (𝓝 1) := by
  have h : Tendsto (fun T : ℝ => 1-orderedHopTimeSpan v*T⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_inv_atTop_zero.const_mul (orderedHopTimeSpan v))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (orderedHopTimeSpan v),eventually_gt_atTop (0:ℝ)] with T hs hT
  unfold orderedHopSlabFraction
  rw [max_eq_left (sub_nonneg.mpr hs)]
  field_simp

def orderedHopReturnSlabFraction {n : ℕ} (T : ℝ) (d : Fin n → OrderedHopStep) : ℝ :=
  orderedHopSlabFraction T (fun j : Fin (n+1) => (OrderedTwoBandPath.returnPath d).time j)

theorem orderedHop_return_slab_continuous (T : ℝ) (n : ℕ) :
    Continuous (orderedHopReturnSlabFraction (n := n) T) := by
  let v := fun (j : Fin (n+1)) (d : Fin n → OrderedHopStep) => (OrderedTwoBandPath.returnPath d).time j
  have h (j) : Continuous (v j) := OrderedTwoBandPath.continuous_return_time _
  exact ((continuous_const.sub ((slab_high_continuous v h _).add
    (slab_high_continuous (fun j x => -v j x) (fun j => (h j).neg) _))).max continuous_const).div_const _

/-- Remove the actual base-time cutoff in every closed relative integral
and simultaneously in the infinite hop series, using its absolute cost. -/
theorem orderedHop_slab_remove (F : (n : ℕ) → (Fin n → OrderedHopStep) → ℂ)
    (hI : ∀ n, Integrable (F n)) (hS : Summable (fun n => ∫ d, ‖F n d‖)) :
    Tendsto (fun T : ℝ => ∑' n, ∫ d, (orderedHopReturnSlabFraction T d : ℂ) * F n d)
      atTop (𝓝 (∑' n, ∫ d, F n d)) := by
  have hb {T : ℝ} (hT : 0 < T) (n : ℕ) (d : Fin n → OrderedHopStep) :
      ‖(orderedHopReturnSlabFraction T d : ℂ)*F n d‖ ≤ ‖F n d‖ := by
    have h := orderedHop_slab_fraction_unit hT (fun j : Fin (n+1) => (OrderedTwoBandPath.returnPath d).time j)
    rw [norm_mul,Complex.norm_real,orderedHopReturnSlabFraction,Real.norm_of_nonneg h.1]
    exact mul_le_of_le_one_left (norm_nonneg _) h.2
  apply tendsto_tsum_of_dominated_convergence hS
  · intro n
    apply tendsto_integral_filter_of_dominated_convergence (fun d => ‖F n d‖)
      (Eventually.of_forall fun T => (Complex.continuous_ofReal.comp
        (orderedHop_return_slab_continuous T n)).aestronglyMeasurable.mul (hI n).aestronglyMeasurable)
      ((eventually_gt_atTop (0:ℝ)).mono fun T hT => Eventually.of_forall (hb hT n)) (hI n).norm
    apply Eventually.of_forall
    intro d
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (orderedHop_slab_fraction_tendsto (fun j : Fin (n+1) => (OrderedTwoBandPath.returnPath d).time j))
    simpa only [Complex.ofReal_one,one_mul] using h.mul_const (F n d)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT n
    exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      (hI n).norm (ae_of_all _ (hb hT n)))

theorem orderedHop_slab_marked_log_limit {m σ g C : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m)
    (hC : 0 ≤ C) (a b : ℕ) (φ : (n : ℕ) → OrderedHopPhases n)
    (hφ : ∀ n j s, Measurable (φ n j s)) (M : (n : ℕ) → (Fin n → OrderedHopStep) → ℂ)
    (hM : ∀ n, Measurable (M n))
    (hBound : ∀ n d, ‖M n d‖ ≤ C*(1+(n:ℝ))^a*(1+orderedHopPathLength d)^b) :
    let F := fun n d => M n d * orderedHopLogWord m σ g (φ n) d
    Tendsto (fun T : ℝ => ∑' n, ∫ d, (orderedHopReturnSlabFraction T d : ℂ) * F n d)
      atTop (𝓝 (∑' n, ∫ d, F n d)) := by
  obtain ⟨hI,hS⟩ := orderedHop_marked_log_words_summable hσ hg hC a b φ hφ M hM hBound
  exact orderedHop_slab_remove _ hI hS

end UV.SectorPlane
