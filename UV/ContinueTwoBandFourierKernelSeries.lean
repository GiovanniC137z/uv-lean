import UV.ContinueTwoBandFourierCycles

/-! Absolutely convergent families of bounded integral kernels can be
multiplied in position space, retaining every index on both edges. -/

noncomputable section
open MeasureTheory

namespace UV.SectorPlane.SlabKernel

variable {X ι κ : Type*} [MeasurableSpace X] [Countable ι] [Countable κ]

/-- An indexed expansion with summable uniform bounds on its terms. -/
structure Expansion (ι : Type*) (K : Bounded X) where
  term : ι → Bounded X
  summable_bound : Summable (fun i => (term i).bound)
  hasSum : ∀ x y, HasSum (fun i => (term i).val x y) (K.val x y)

private theorem expanded_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {f : ι → Y → ℂ} {g : Y → ℂ} {c : ι → ℝ} (hc : Summable c)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hb : ∀ i x, ‖f i x‖ ≤ c i)
    (hs : ∀ x, HasSum (fun i => f i x) (g x)) :
    HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, g x ∂μ) := by
  have hi (i) : Integrable (f i) μ := (integrable_const (c i)).mono' (hf i) (ae_of_all _ (hb i))
  have hN : Summable (fun i => ∫ x, ‖f i x‖ ∂μ) := by
    apply (hc.mul_right (μ.real Set.univ)).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    simpa only [integral_const,smul_eq_mul,mul_comm] using
      integral_mono (hi i).norm (integrable_const (c i)) (hb i)
  simpa only [fun x => (hs x).tsum_eq] using hasSum_integral_of_summable_integral_norm hi hN

variable (μ : Measure X) [IsFiniteMeasure μ]

def Expansion.sew {K L : Bounded X} (p : Expansion ι K) (q : Expansion κ L) :
    Expansion (ι × κ) (SlabKernel.sew μ K L) where
  term w := SlabKernel.sew μ (p.term w.1) (q.term w.2)
  summable_bound := (p.summable_bound.mul_of_nonneg q.summable_bound
    (fun i => (p.term i).nonneg) (fun j => (q.term j).nonneg)).mul_right (μ.real Set.univ)
  hasSum x y := by
    apply expanded_integral μ (p.summable_bound.mul_of_nonneg q.summable_bound
      (fun i => (p.term i).nonneg) (fun j => (q.term j).nonneg))
    · intro w
      exact (((p.term w.1).measurable.comp (measurable_const.prodMk measurable_id)).mul
        ((q.term w.2).measurable.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    · intro w z
      exact (norm_mul_le _ _).trans (mul_le_mul ((p.term w.1).bounded x z)
        ((q.term w.2).bounded z y) (norm_nonneg _) (p.term w.1).nonneg)
    · intro z
      have hp := p.summable_bound.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (p.term i).bounded x z)
      have hq := q.summable_bound.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (q.term i).bounded z y)
      rw [← (p.hasSum x z).tsum_eq, ← (q.hasSum z y).tsum_eq, tsum_mul_tsum_of_summable_norm hp hq]
      exact (summable_mul_of_summable_norm hp hq).hasSum

/-- Close one kernel at its diagonal and integrate, keeping its winding indices. -/
theorem Expansion.diagonal {K : Bounded X} (p : Expansion ι K) :
    HasSum (fun i => ∫ x, (p.term i).val x x ∂μ) (∫ x, K.val x x ∂μ) :=
  expanded_integral μ p.summable_bound (fun i => ((p.term i).measurable.comp
      (measurable_id.prodMk measurable_id)).aestronglyMeasurable)
    (fun i x => (p.term i).bounded x x) (fun x => p.hasSum x x)

/-- One independent lift for each of the 2n+1 open-chain hops. -/
def OddIndices (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n+1 => ι × ι × OddIndices ι n

instance (n : ℕ) : Countable (OddIndices ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable ι)
  | succ n ih => exact inferInstanceAs (Countable (ι × ι × OddIndices ι n))

def Expansion.odd {K L : Bounded X} (p : Expansion ι K) (q : Expansion ι L) :
    (n : ℕ) → Expansion (OddIndices ι n) (oddChain μ K L n)
  | 0 => p
  | n+1 => p.sew μ (q.sew μ (p.odd q n))

theorem Expansion.closed_word {K L : Bounded X} (p : Expansion ι K) (q : Expansion ι L) (n : ℕ) :
    HasSum (fun w : OddIndices ι n × ι =>
      ∫ x, ∫ y, ((p.odd μ q n).term w.1).val x y * (q.term w.2).val y x ∂μ ∂μ)
      (∫ x, ∫ y, (oddChain μ K L n).val x y * L.val y x ∂μ ∂μ) :=
  (((p.odd μ q n).sew μ q).diagonal μ)

end UV.SectorPlane.SlabKernel
