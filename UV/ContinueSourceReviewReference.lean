import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Filled reference sea in the energy eigenbasis. States are occupation sets.
The signs count occupied orbitals preceding the annihilated (or created)
orbital. Scalar normal ordering subtracts the occupied diagonal. -/

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexConjugate Matrix

namespace UV

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def seaSign (X : Finset ι) (i : ι) : ℝ := (-1)^((X.filter (· < i)).card)

omit [Fintype ι] in
private theorem seaSign_sq (X : Finset ι) (i : ι) : seaSign X i * seaSign X i = 1 := by
  unfold seaSign
  rw [←mul_pow]
  simp

omit [Fintype ι] in
private theorem seaSign_ne (X : Finset ι) (i : ι) : seaSign X i ≠ 0 := by
  unfold seaSign
  positivity

def seaCurrentEntry (Q : Matrix ι ι ℂ) (X Y : Finset ι) (a b : ι) : ℂ :=
  if a ∈ X ∧ b ∈ Y ∧ X.erase a = Y.erase b then (seaSign X a : ℂ)*(seaSign Y b : ℂ)*Q a b else 0

def seaCurrent (A : Finset ι) (Q : Matrix ι ι ℂ) : Matrix (Finset ι) (Finset ι) ℂ :=
  fun X Y => (∑ a, ∑ b, seaCurrentEntry Q X Y a b) - (if X = Y then ∑ i ∈ A, Q i i else 0)

def seaProjection (A : Finset ι) : Matrix ι ι ℂ := Matrix.diagonal (fun i => if i ∈ A then 1 else 0)

theorem sea_offblock (A : Finset ι) (Q : Matrix ι ι ℂ) :
    (1-seaProjection A)*Q*seaProjection A = 0 ↔ ∀ i ∉ A, ∀ j ∈ A, Q i j = 0 := by
  have he (i j : ι) : ((1-seaProjection A)*Q*seaProjection A) i j =
      (if i ∉ A ∧ j ∈ A then Q i j else 0) := by
    rw [sub_mul,one_mul]
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [seaProjection,Matrix.mul_diagonal,Matrix.diagonal_mul,hi,hj]
  constructor
  · intro h i hi j hj
    simpa [he,hi,hj] using congrFun (congrFun h i) j
  · intro h
    ext i j
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [he,hi,hj,h]

theorem sea_commutes_iff_block (A : Finset ι) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) :
    seaProjection A*Q = Q*seaProjection A ↔ (1-seaProjection A)*Q*seaProjection A = 0 := by
  rw [sea_offblock]
  constructor
  · intro h i hi j hj
    simpa [seaProjection,Matrix.diagonal_mul,Matrix.mul_diagonal,hi,hj] using (congrFun (congrFun h i) j).symm
  · intro h
    ext i j
    have ht : i ∈ A → j ∉ A → Q i j = 0 := by
      intro hi hj
      have hrel := hQ.apply i j
      simpa [h j hj i hi] using hrel.symm
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [seaProjection,Matrix.diagonal_mul,Matrix.mul_diagonal,hi,hj,h,ht]

omit [Fintype ι] in
private theorem sea_entry_diag (Q : Matrix ι ι ℂ) (A : Finset ι) (a b : ι) :
    seaCurrentEntry Q A A a b = if a ∈ A ∧ b = a then Q a a else 0 := by
  by_cases ha : a ∈ A
  · by_cases he : b = a
    · subst b
      simp only [seaCurrentEntry,ha,and_self,if_true]
      rw [←Complex.ofReal_mul,seaSign_sq]; simp
    · have hn : A.erase a ≠ A.erase b := by
        intro hh
        have hx : a ∈ A.erase b := Finset.mem_erase.mpr ⟨Ne.symm he,ha⟩
        rw [←hh] at hx
        exact Finset.notMem_erase _ _ hx
      simp [seaCurrentEntry,ha,hn,he]
  · simp [seaCurrentEntry,ha]

theorem sea_current_vacuum_expectation (Q : Matrix ι ι ℂ) (A : Finset ι) : seaCurrent A Q A A = 0 := by
  simp only [seaCurrent,sea_entry_diag]
  have hh (a : ι) : (∑ b, if a ∈ A ∧ b = a then Q a a else 0) = if a ∈ A then Q a a else 0 := by
    by_cases h : a ∈ A <;> simp [h]
  simp [hh]

omit [Fintype ι] in
private theorem sea_target_ne {A : Finset ι} {i j : ι} (hi : i ∉ A) :
    insert i (A.erase j) ≠ A := by
  intro h
  exact hi (h ▸ Finset.mem_insert_self i (A.erase j))

theorem sea_current_particle_hole (A : Finset ι) (Q : Matrix ι ι ℂ) {i j : ι} (hi : i ∉ A) (hj : j ∈ A) :
    let X := insert i (A.erase j)
    seaCurrent A Q X A = (seaSign X i : ℂ)*(seaSign A j : ℂ)*Q i j := by
  let X := insert i (A.erase j)
  have hij : i ≠ j := by rintro rfl; exact hi hj
  have hX : i ∈ X := Finset.mem_insert_self ..
  have hJ : j ∉ X := by simp [X,Ne.symm hij]
  have he : X.erase i = A.erase j := Finset.erase_insert (by simp [hi])
  have hdiag : X ≠ A := sea_target_ne hi
  change (∑ a, ∑ b, seaCurrentEntry Q X A a b) - (if X = A then _ else 0) = _
  rw [if_neg hdiag,sub_zero,Finset.sum_eq_single i,Finset.sum_eq_single j]
  · simp only [seaCurrentEntry,hX,hj,he,and_self,if_true]; rfl
  · intro b _ hb
    have hn : X.erase i ≠ A.erase b := by
      intro hh
      exact hJ (Finset.mem_of_mem_erase (hh ▸ Finset.mem_erase.mpr ⟨Ne.symm hb,hj⟩))
    simp [seaCurrentEntry,hn]
  · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    have hn : X.erase a ≠ A.erase b := by
      intro hh
      have hx : i ∈ X.erase a := Finset.mem_erase.mpr ⟨Ne.symm ha,hX⟩
      exact hi (Finset.mem_of_mem_erase (hh ▸ hx))
    simp [seaCurrentEntry,hn]
  · simp

theorem sea_current_annihilates_iff (A : Finset ι) (Q : Matrix ι ι ℂ) :
    (∀ X, seaCurrent A Q X A = 0) ↔ (1-seaProjection A)*Q*seaProjection A = 0 := by
  rw [sea_offblock]
  constructor
  · intro h i hi j hj
    have hv := h (insert i (A.erase j))
    rw [sea_current_particle_hole A Q hi hj] at hv
    exact (mul_eq_zero.mp hv).resolve_left (mul_ne_zero (Complex.ofReal_ne_zero.mpr (seaSign_ne _ _)) (Complex.ofReal_ne_zero.mpr (seaSign_ne _ _)))
  · intro h X
    by_cases hX : X = A
    · subst X; exact sea_current_vacuum_expectation Q A
    simp only [seaCurrent,if_neg hX,sub_zero]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    unfold seaCurrentEntry
    split_ifs with hc
    · obtain ⟨ha,hb,he⟩ := hc
      have hn : a ∉ A := by
        intro hA
        by_cases heq : a = b
        · subst b
          exact hX (by rw [←Finset.insert_erase ha,he,Finset.insert_erase hb])
        · have hx : a ∈ A.erase b := Finset.mem_erase.mpr ⟨heq,hA⟩
          rw [←he] at hx
          exact Finset.notMem_erase _ _ hx
      rw [h a hn b hb,mul_zero]
    · rfl

/-- Occupation-basis annihilation operator in a fixed ordering of the orbitals. -/
def seaAnnihilate (i : ι) : Matrix (Finset ι) (Finset ι) ℂ :=
  fun X Y => if i ∈ Y ∧ X = Y.erase i then (seaSign Y i : ℂ) else 0

private theorem sea_hop_entry (a b : ι) (X Y : Finset ι) :
    ((seaAnnihilate a)ᴴ * seaAnnihilate b) X Y =
    if a ∈ X ∧ b ∈ Y ∧ X.erase a = Y.erase b then (seaSign X a : ℂ)*(seaSign Y b : ℂ) else 0 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (X.erase a)]
  · by_cases ha : a ∈ X <;> by_cases hb : b ∈ Y <;> by_cases h : X.erase a = Y.erase b <;>
      simp [Matrix.conjTranspose_apply,seaAnnihilate,ha,hb,h]
  · intro Z _ hZ
    simp [seaAnnihilate,Matrix.conjTranspose_apply,hZ]
  · simp

theorem sea_current_second_quantization (A : Finset ι) (Q : Matrix ι ι ℂ) :
    seaCurrent A Q = (∑ a, ∑ b, (Q a b) • ((seaAnnihilate a)ᴴ * seaAnnihilate b)) -
      (∑ a ∈ A, Q a a) • (1 : Matrix (Finset ι) (Finset ι) ℂ) := by
  ext X Y
  simp only [seaCurrent,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,sea_hop_entry]
  congr 1
  · apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold seaCurrentEntry; split_ifs <;> ring
  · by_cases h : X = Y <;> simp [h,Matrix.one_apply]

theorem sea_current_hermitian (A : Finset ι) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) : (seaCurrent A Q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro X Y
  change conj (seaCurrent A Q Y X) = seaCurrent A Q X Y
  simp only [seaCurrent,map_sub,map_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have hh := hQ.apply a b
    change conj (Q b a) = Q a b at hh
    unfold seaCurrentEntry
    by_cases h : a ∈ X ∧ b ∈ Y ∧ X.erase a = Y.erase b
    · obtain ⟨ha,hb,he⟩ := h
      simp [ha,hb,he,hh,mul_comm]
    · have hn : ¬(b ∈ Y ∧ a ∈ X ∧ Y.erase b = X.erase a) := fun ⟨hb,ha,he⟩ => h ⟨ha,hb,he.symm⟩
      simp [hn,h]
  · by_cases h : X = Y
    · subst Y; simp only [if_true,map_sum]
      exact Finset.sum_congr rfl fun a _ => hQ.apply a a
    · simp [h,Ne.symm h]

/-- Vacuum-energy-subtracted free transfer in an orbital energy basis. -/
def seaFreeTransfer (A : Finset ι) (ε : ι → ℝ) (t : ℝ) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.diagonal fun X => (Real.exp (-t*((∑ i ∈ X, ε i)-(∑ i ∈ A, ε i))) : ℂ)

omit [Fintype ι] in
theorem sea_free_vacuum (A : Finset ι) (ε : ι → ℝ) (t : ℝ) : seaFreeTransfer A ε t A A = 1 := by
  simp [seaFreeTransfer]

theorem sea_two_current (A : Finset ι) (ε : ι → ℝ) (t : ℝ) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) :
    ((seaCurrent A Q * seaFreeTransfer A ε t * seaCurrent A Q) A A).re =
      ∑ X, Real.exp (-t*((∑ i ∈ X, ε i)-(∑ i ∈ A, ε i)))*Complex.normSq (seaCurrent A Q X A) := by
  rw [Matrix.mul_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [seaFreeTransfer,Matrix.mul_diagonal]
  have he := (sea_current_hermitian A hQ).apply A X
  change conj (seaCurrent A Q X A) = seaCurrent A Q A X at he
  rw [←he]
  set z := seaCurrent A Q X A
  set c := Real.exp _
  have hh : conj z * (c:ℂ) * z = (c:ℂ)*(z*conj z) := by ring
  rw [hh,Complex.mul_conj,←Complex.ofReal_mul,Complex.ofReal_re]

theorem sea_two_current_zero_iff (A : Finset ι) (ε : ι → ℝ) (t : ℝ) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) :
    ((seaCurrent A Q * seaFreeTransfer A ε t * seaCurrent A Q) A A).re = 0 ↔
      (1-seaProjection A)*Q*seaProjection A = 0 := by
  rw [sea_two_current A ε t hQ,←sea_current_annihilates_iff,Finset.sum_eq_zero_iff_of_nonneg (fun X _ => mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _))]
  simp [Real.exp_ne_zero]

/-- Each nonempty time-ordered product has a rightmost insertion. Factors
on its left can comprise arbitrary additional transfers and insertions. -/
theorem sea_ordered_word (A : Finset ι) (ε : ι → ℝ) (t : ℝ) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian)
    (hc : seaProjection A*Q = Q*seaProjection A) (B : Matrix (Finset ι) (Finset ι) ℂ) (X : Finset ι) :
    (B * seaCurrent A Q * seaFreeTransfer A ε t) X A = 0 := by
  have hz := (sea_current_annihilates_iff A Q).2 ((sea_commutes_iff_block A hQ).1 hc)
  rw [seaFreeTransfer,Matrix.mul_diagonal,Matrix.mul_apply]; simp [hz]

/-- In a continuum spectral window the response is the weighted squared
norm of the particle-hole amplitude. Strict positivity of the spectral
multiplier gives the converse even without a uniform lower bound. -/
theorem sea_spectral_window_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (energy : Ω → ℝ)
    (amplitude : Ω → ℂ) (t : ℝ) (h : Integrable (fun ω => Real.exp (-t*energy ω)*‖amplitude ω‖^2) μ) :
    (∫ ω, Real.exp (-t*energy ω)*‖amplitude ω‖^2 ∂μ) = 0 ↔ ∀ᵐ ω ∂μ, amplitude ω = 0 := by
  rw [integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) h]
  constructor
  · intro he
    filter_upwards [he] with ω hω
    exact norm_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp ((mul_eq_zero.mp hω).resolve_left (Real.exp_ne_zero _)))
  · intro he
    filter_upwards [he] with ω hω; simp [hω]

/-- Every nonzero positive spectral measure contributes a strictly positive
smeared heat response whenever its transform exists. This applies to measures
with atoms and to singular continuous measures as well. -/
theorem sea_window_measure_detects {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (energy : Ω → ℝ) (t : ℝ) (hi : Integrable (fun x => Real.exp (-t * energy x)) μ) :
    (0 < ∫ x, Real.exp (-t * energy x) ∂μ) ↔ μ ≠ 0 := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi]
  have hs : Function.support (fun x => Real.exp (-t * energy x)) = Set.univ :=
    Set.eq_univ_of_forall fun _ => Real.exp_ne_zero _
  rw [hs, Measure.measure_univ_pos]

end UV
