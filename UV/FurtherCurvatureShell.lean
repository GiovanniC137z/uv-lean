import UV.RevisionCurvatureDeterminant
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

/-! Actual centered cube shells of the nonzero four-torus modes on the fixed
sector plane. The auxiliary cube height only estimates the Euclidean
frequency used in the source covariance and spherical cutoff. -/

noncomputable section

open Set Real
open scoped BigOperators

namespace UV.FurtherCurvatureShell

open UV.RevisionCurvatureDeterminant (latticeFrequency)

abbrev TorusMode := Fin 4 → ℤ

def modeBox (N : ℕ) : Finset TorusMode :=
  Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem mem_modeBox (N : ℕ) (k : TorusMode) :
    k ∈ modeBox N ↔ ∀ i, (k i).natAbs ≤ N := by
  rw [modeBox, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]
  constructor
  · intro h i
    obtain ⟨hl, hu⟩ := h i
    omega
  · intro h i
    have hi := h i
    constructor <;> omega

theorem modeBox_mono {M N : ℕ} (h : M ≤ N) : modeBox M ⊆ modeBox N := by
  intro k hk
  simpa only [mem_modeBox] using fun i => ((mem_modeBox M k).mp hk i).trans h

theorem modeBox_card (N : ℕ) : (modeBox N).card = (2*N+1)^4 := by
  have hf : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card) = 2*N+1 := by rw [Int.card_Icc]; omega
  rw [modeBox, Fintype.card_piFinset]
  simp [hf, Finset.prod_const]

def latticeHeight (k : TorusMode) : ℕ := Finset.univ.sup fun i => (k i).natAbs

theorem latticeHeight_le (k : TorusMode) (N : ℕ) :
    latticeHeight k ≤ N ↔ k ∈ modeBox N := by
  rw [latticeHeight, Finset.sup_le_iff, mem_modeBox]
  simp

theorem latticeHeight_ne_zero {k : TorusMode} (hk : k ≠ 0) :
    latticeHeight k ≠ 0 := by
  intro he
  apply hk
  funext i
  have hc := (mem_modeBox 0 k).mp ((latticeHeight_le k 0).mp he.le) i
  change k i = 0
  omega

theorem latticeHeight_le_latticeFrequency (k : TorusMode) :
    (latticeHeight k : ℝ) ≤ latticeFrequency k := by
  let x := latticeFrequency k
  have hx : 0 ≤ x := sqrt_nonneg _
  have hc (i : Fin 4) : ((k i).natAbs : ℝ) ≤ x := by
    have hsq : ((k i : ℝ) ^ 2) ≤ ∑ j : Fin 4, (k j : ℝ)^2 :=
      Finset.single_le_sum (f := fun j : Fin 4 => (k j : ℝ)^2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hn : ((k i).natAbs : ℝ)^2 = (k i : ℝ)^2 := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
    apply (sq_le_sq₀ (Nat.cast_nonneg _) hx).mp
    change ((k i).natAbs : ℝ)^2 ≤ (latticeFrequency k)^2
    rw [hn, latticeFrequency, Real.sq_sqrt (by positivity)]
    exact hsq
  unfold latticeHeight
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin 4)))
    (f := fun i => (k i).natAbs) Finset.univ_nonempty
  simpa only [← hi] using hc i

theorem latticeFrequency_le_twice_height (k : TorusMode) :
    latticeFrequency k ≤ 2 * (latticeHeight k : ℝ) := by
  have hc := (mem_modeBox (latticeHeight k) k).mp ((latticeHeight_le k _).mp le_rfl)
  have hsq (i : Fin 4) : (k i : ℝ)^2 ≤ (latticeHeight k : ℝ)^2 := by
    have h2 := pow_le_pow_left₀ (show 0 ≤ ((k i).natAbs : ℝ) from Nat.cast_nonneg _)
      (show ((k i).natAbs : ℝ) ≤ latticeHeight k by exact_mod_cast hc i) 2
    rwa [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs] at h2
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 4, (latticeHeight k : ℝ)^2 := Finset.sum_le_sum (fun i _ => hsq i)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Exact shell indexed by the positive cube height (j+1). -/
def modeShell (j : ℕ) : Finset TorusMode := modeBox (j+1) \ modeBox j

theorem mem_modeShell {j : ℕ} {k : TorusMode} :
    k ∈ modeShell j ↔ latticeHeight k = j+1 := by
  rw [modeShell, Finset.mem_sdiff, ← latticeHeight_le, ← latticeHeight_le]
  omega

theorem modeShell_card (j : ℕ) : ((modeShell j).card : ℝ) ≤ 80 * ((j+1 : ℕ) : ℝ) ^ 3 := by
  have h := Finset.card_sdiff_add_card_eq_card (modeBox_mono (by omega : j ≤ j+1))
  change (modeShell j).card + (modeBox j).card = (modeBox (j+1)).card at h
  rw [modeBox_card, modeBox_card] at h
  have hc := congrArg (fun x : ℕ => (x : ℝ)) h
  push_cast at hc ⊢
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hj3 : 0 ≤ (j : ℝ)^3 := by positivity
  nlinarith [sq_nonneg (j : ℝ)]

/-- Literal spherical restrictions built from the bounding integer box. -/
def sphericalModes (Λ : ℝ) : Finset TorusMode :=
  (modeBox ⌊Λ⌋₊).filter fun k => k ≠ 0 ∧ latticeFrequency k ≤ Λ

theorem mem_sphericalModes {Λ : ℝ} {k : TorusMode} :
    k ∈ sphericalModes Λ ↔ k ≠ 0 ∧ latticeFrequency k ≤ Λ := by
  rw [sphericalModes, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_,h⟩⟩
  exact (latticeHeight_le k _).mp (Nat.le_floor ((latticeHeight_le_latticeFrequency k).trans h.2))

theorem sphericalModes_mono {Λ Λ' : ℝ} (hΛ : Λ ≤ Λ') : sphericalModes Λ ⊆ sphericalModes Λ' :=
  fun _ hk => mem_sphericalModes.mpr ⟨(mem_sphericalModes.mp hk).1, (mem_sphericalModes.mp hk).2.trans hΛ⟩

end UV.FurtherCurvatureShell
