import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Nodup
import UV.BRST

/-! The four distinct labelled marks in the formal relative trace logarithm. -/

noncomputable section

namespace UV.RelativeSoft

open scoped BigOperators

private abbrev Mark := Fin 4
private abbrev MarkBlock := Finset Mark
private abbrev MarkExponent := Mark →₀ ℕ

private def blockExponent (s : MarkBlock) : MarkExponent :=
  ∑ i ∈ s, Finsupp.single i 1

/-- The monomial containing each of the four labels once. -/
def fourMarkExponent : Fin 4 →₀ ℕ := blockExponent Finset.univ

private def markBlocks : List MarkBlock :=
  (Finset.univ.filter Finset.Nonempty).toList

private def markedWords : ℕ → List (List MarkBlock)
  | 0 => [[]]
  | n + 1 => markBlocks.flatMap fun s => (markedWords n).map (s :: ·)

private def wordExponent : List MarkBlock → MarkExponent
  | [] => 0
  | s :: w => blockExponent s + wordExponent w

private theorem block_exponent_apply (s : MarkBlock) (i : Mark) :
    blockExponent s i = if i ∈ s then 1 else 0 := by
  classical
  simp [blockExponent, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem word_exponent_apply (w : List MarkBlock) (i : Mark) :
    wordExponent w i = (w.filter fun s => decide (i ∈ s)).length := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    by_cases hi : i ∈ s
    · simp [wordExponent, Finsupp.add_apply, block_exponent_apply, hi, ih, Nat.add_comm]
    · simp [wordExponent, Finsupp.add_apply, block_exponent_apply, hi, ih]

private theorem mem_markedWords {n : ℕ} {w : List MarkBlock} :
    w ∈ markedWords n ↔ w.length = n ∧ ∀ s ∈ w, s.Nonempty := by
  induction n generalizing w with
  | zero =>
    cases w <;> simp [markedWords]
  | succ n ih =>
    cases w with
    | nil => simp [markedWords, List.mem_flatMap]
    | cons s w =>
      simp [markedWords, markBlocks, List.mem_flatMap, ih, and_comm, and_left_comm]

private theorem markedWords_nodup (n : ℕ) : (markedWords n).Nodup := by
  induction n with
  | zero => simp [markedWords]
  | succ n ih =>
    rw [markedWords, List.nodup_flatMap]
    refine ⟨fun s _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    have hb : markBlocks.Nodup := Finset.nodup_toList _
    refine hb.imp (fun {a b} hn => List.disjoint_left.mpr ?_)
    intro w hwa hwb
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hwa
    obtain ⟨l', _, h⟩ := List.mem_map.mp hwb
    exact hn (List.cons.inj h).1.symm

private def chordWord {A : Type*} [Monoid A] (Y : MarkBlock → A) (R₀ : A) :
    List MarkBlock → A
  | [] => 1
  | s :: w => (Y s * R₀) * chordWord Y R₀ w

/-- The multivariate marked perturbation with the constant term omitted. -/
def markedChordPolynomial {A : Type*} [Semiring A] (Y : Finset (Fin 4) → A) (R₀ : A) :
    AddMonoidAlgebra A (Fin 4 →₀ ℕ) :=
  (markBlocks.map fun s => AddMonoidAlgebra.single (blockExponent s) (Y s * R₀)).sum

private theorem list_map_sum_mul {A B : Type*} [Semiring A] (l : List B) (f : B → A) (x : A) :
    (l.map f).sum * x = (l.map fun b => f b * x).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [add_mul, ih]

private theorem mul_list_map_sum {A B : Type*} [Semiring A] (l : List B) (f : B → A) (x : A) :
    x * (l.map f).sum = (l.map fun b => x * f b).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [mul_add, ih]

private theorem list_map_sum_flatMap {A B C : Type*} [AddMonoid A]
    (l : List B) (f : B → List C) (g : C → A) :
    ((l.flatMap f).map g).sum = (l.map fun b => ((f b).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih]

private theorem markedChordPolynomial_pow {A : Type*} [Semiring A]
    (Y : MarkBlock → A) (R₀ : A) (n : ℕ) :
    markedChordPolynomial Y R₀ ^ n =
      ((markedWords n).map fun w => AddMonoidAlgebra.single (wordExponent w)
        (chordWord Y R₀ w)).sum := by
  induction n with
  | zero => simp [markedWords, wordExponent, chordWord, AddMonoidAlgebra.one_def]
  | succ n ih =>
    rw [pow_succ', ih, markedChordPolynomial, list_map_sum_mul, markedWords,
      list_map_sum_flatMap]
    congr 1
    apply List.map_congr_left
    intro s _
    rw [mul_list_map_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [Function.comp_apply, wordExponent, chordWord, AddMonoidAlgebra.single_mul_single]

/-- A listed word counts as an ordered partition when it has the desired
number of nonempty blocks and every labelled mark occurs in one block. -/
def OrderedMarkedPartition (n : ℕ) (w : List (Finset (Fin 4))) : Prop :=
  w.length = n ∧ (∀ s ∈ w, s.Nonempty) ∧
    ∀ i : Fin 4, (w.filter fun s => decide (i ∈ s)).length = 1

/-- The ordered list of block arrangements selected by the four-mark coefficient. -/
def orderedMarkedPartitions (n : ℕ) : List (List (Finset (Fin 4))) :=
  (markedWords n).filter fun w => decide (wordExponent w = fourMarkExponent)

theorem orderedMarkedPartitions_nodup (n : ℕ) : (orderedMarkedPartitions n).Nodup :=
  List.Nodup.filter _ (markedWords_nodup n)

theorem orderedMarkedPartitions_iff (n : ℕ) (w : List (Finset (Fin 4))) :
    w ∈ orderedMarkedPartitions n ↔ OrderedMarkedPartition n w := by
  simp only [orderedMarkedPartitions, List.mem_filter, decide_eq_true_eq, mem_markedWords,
    OrderedMarkedPartition, and_assoc]
  constructor
  · rintro ⟨hlen, hb, he⟩
    refine ⟨hlen, hb, fun i => ?_⟩
    rw [← word_exponent_apply, he]
    simp [fourMarkExponent, block_exponent_apply]
  · rintro ⟨hlen, hb, he⟩
    refine ⟨hlen, hb, ?_⟩
    ext i
    rw [word_exponent_apply, he]
    simp [fourMarkExponent, block_exponent_apply]

private theorem markedWord_length_le (w : List MarkBlock) (hn : ∀ s ∈ w, s.Nonempty) :
    w.length ≤ ∑ i : Mark, wordExponent w i := by
  induction w with
  | nil => simp [wordExponent]
  | cons s w ih =>
    have hw := ih fun t ht => hn t (List.mem_cons_of_mem _ ht)
    obtain ⟨i, hi⟩ := hn s (List.mem_cons_self)
    have h := Finset.single_le_sum (f := blockExponent s)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [block_exponent_apply, if_pos hi] at h
    simp only [List.length_cons, wordExponent, Finsupp.add_apply, Finset.sum_add_distrib]
    omega

/-- The single-block partition is precisely the direct four-mark contact. -/
theorem markedFourth_single_block (s : Finset (Fin 4)) :
    OrderedMarkedPartition 1 [s] ↔ s = Finset.univ := by
  constructor
  · intro h
    ext i
    have hi := h.2.2 i
    by_cases hm : i ∈ s
    · simp [hm]
    · simp [hm] at hi
  · rintro rfl
    simp [OrderedMarkedPartition]

private theorem selected_word_sum {A B : Type*} [AddMonoid A] (f : B → A)
    (p : B → Prop) [DecidablePred p] (l : List B) :
    (l.map fun x => if p x then f x else 0).sum =
      ((l.filter fun x => decide (p x)).map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases hx : p x <;> simp [hx, ih]

private theorem markedChordPolynomial_coefficient {A : Type*} [Semiring A]
    (Y : MarkBlock → A) (R₀ : A) (n : ℕ) :
    (markedChordPolynomial Y R₀ ^ n) fourMarkExponent =
      ((orderedMarkedPartitions n).map (chordWord Y R₀)).sum := by
  classical
  rw [markedChordPolynomial_pow]
  let coeff : AddMonoidAlgebra A MarkExponent →+ A :=
    { toFun := fun z => z fourMarkExponent
      map_zero' := rfl
      map_add' := fun z w => Finsupp.add_apply z w fourMarkExponent }
  change coeff _ = _
  rw [map_list_sum, List.map_map, orderedMarkedPartitions]
  change ((markedWords n).map fun w =>
    (Finsupp.single (wordExponent w) (chordWord Y R₀ w)) fourMarkExponent).sum = _
  simp only [Finsupp.single_apply]
  exact selected_word_sum _ _ _

/-- Powers above four cannot contribute to the coefficient with one of each
of the four labels. Every block uses at least one label. -/
theorem markedChordPolynomial_higher_coeff_zero {A : Type*} [Semiring A]
    (Y : Finset (Fin 4) → A) (R₀ : A) {n : ℕ} (hn : 4 < n) :
    (markedChordPolynomial Y R₀ ^ n) fourMarkExponent = 0 := by
  rw [markedChordPolynomial_coefficient]
  suffices h : orderedMarkedPartitions n = [] by simp [h]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro w hw
  have hp := (orderedMarkedPartitions_iff n w).mp hw
  have hlen := markedWord_length_le w hp.2.1
  rw [hp.1] at hlen
  simp_rw [word_exponent_apply, hp.2.2] at hlen
  simp at hlen
  omega

/-- The coefficient with one of each label in the first four powers of the
formal relative trace logarithm, divided by the torus volume. -/
def markedFourthTraceLog {A : Type*} [Semiring A] [Module ℚ A]
    (trace : A →ₗ[ℚ] ℝ) (Y : Finset (Fin 4) → A) (R₀ : A) (V : ℝ) : ℝ :=
  V⁻¹ * ∑ a : Fin 4, (-1 : ℝ) ^ a.val / (a.val + 1) *
    trace ((markedChordPolynomial Y R₀ ^ (a.val + 1)) fourMarkExponent)

/-- The four-mark coefficient agrees with the repository's finite logarithm
at every truncation containing all four relevant powers. -/
theorem markedFourthTraceLog_eq_finiteLog {A : Type*} [Ring A] [Algebra ℚ A]
    (trace : A →ₗ[ℚ] ℝ) (Y : Finset (Fin 4) → A) (R₀ : A) (V : ℝ)
    {N : ℕ} (hN : 4 ≤ N) :
    markedFourthTraceLog trace Y R₀ V =
      V⁻¹ * trace ((UV.finiteLogPolynomial (1 + markedChordPolynomial Y R₀) N) fourMarkExponent) := by
  let Z := markedChordPolynomial Y R₀
  have hterm (n : ℕ) :
      trace ((((-1 : ℚ) ^ n / (n + 1 : ℚ)) • Z ^ (n + 1)) fourMarkExponent) =
        (-1 : ℝ) ^ n / (n + 1 : ℝ) * trace ((Z ^ (n + 1)) fourMarkExponent) := by
    rw [Finsupp.smul_apply, map_smul, Rat.smul_def]
    push_cast
    ring
  have hsum : (∑ n ∈ Finset.range 4, (-1 : ℝ) ^ n / (n + 1 : ℝ) *
        trace ((Z ^ (n + 1)) fourMarkExponent)) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (n + 1 : ℝ) *
        trace ((Z ^ (n + 1)) fourMarkExponent) := by
    refine Finset.sum_subset (Finset.range_mono hN) ?_
    intro n _ hn
    have hn' : 4 < n + 1 := by
      rw [Finset.mem_range] at hn
      omega
    rw [markedChordPolynomial_higher_coeff_zero Y R₀ hn', map_zero, mul_zero]
  unfold markedFourthTraceLog UV.finiteLogPolynomial
  rw [Finsupp.finset_sum_apply, map_sum]
  simp only [add_sub_cancel_left]
  let f (n : ℕ) := (-1 : ℝ) ^ n / (n + 1 : ℝ) * trace ((Z ^ (n + 1)) fourMarkExponent)
  have hf : (∑ a : Fin 4, f a.val) = ∑ n ∈ Finset.range 4, f n :=
    Fin.sum_univ_eq_sum_range f 4
  congr 1
  exact hf.trans hsum |>.trans (Finset.sum_congr rfl fun n _ => (hterm n).symm)

/-- The four-mark coefficient includes all ordered partitions and preserves
the operator order in every block product. -/
theorem markedFourthTraceLog_ordered_partitions {A : Type*} [Semiring A] [Module ℚ A]
    (trace : A →ₗ[ℚ] ℝ) (Y : Finset (Fin 4) → A) (R₀ : A) (V : ℝ) :
    markedFourthTraceLog trace Y R₀ V =
      V⁻¹ * ∑ a : Fin 4, (-1 : ℝ) ^ a.val / (a.val + 1) *
        (((orderedMarkedPartitions (a.val + 1)).map fun w => trace (chordWord Y R₀ w)).sum) := by
  unfold markedFourthTraceLog
  simp_rw [markedChordPolynomial_coefficient, map_list_sum, List.map_map]
  rfl

end UV.RelativeSoft
