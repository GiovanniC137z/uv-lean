import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.RealVectorSpace

/-! A represented weak (Pettis) integral in arbitrary real topological
vector spaces. All scalar tests are genuine integrable real functions.
The representing vector is required to exist; dual separation proves its
uniqueness and all functorial and linear identities. No algebraic identity
or differentiation-under-the-integral rule is inserted as trusted data. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

section Topological

variable {X A B : Type*} [MeasurableSpace X]
  [AddCommGroup A] [TopologicalSpace A] [Module ℝ A]
  [AddCommGroup B] [TopologicalSpace B] [Module ℝ B]
  {μ : Measure X} {f g : X → A}

/-- Scalar absolute integrability and representation by an actual vector.
There is no normability or boundedness assumption on the vector space. -/
def WeakIntegrable (μ : Measure X) (f : X → A) : Prop :=
  (∀ ℓ : A →L[ℝ] ℝ, Integrable (fun x => ℓ (f x)) μ) ∧
    ∃ a : A, ∀ ℓ : A →L[ℝ] ℝ, ℓ a = ∫ x, ℓ (f x) ∂μ

/-- The actual weak integral is the representing vector when it exists. -/
def weakIntegral (μ : Measure X) (f : X → A) : A := by
  classical
  exact if h : WeakIntegrable μ f then Classical.choose h.2 else 0

theorem weakIntegral_apply (hf : WeakIntegrable μ f) (ℓ : A →L[ℝ] ℝ) :
    ℓ (weakIntegral μ f) = ∫ x, ℓ (f x) ∂μ := by
  rw [weakIntegral, dif_pos hf]
  exact Classical.choose_spec hf.2 ℓ

/-- Continuous real dual tests determine vectors even in a nonnormable
locally convex space. -/
theorem weakDual_ext [SeparatingDual ℝ A] {a b : A}
    (h : ∀ ℓ : A →L[ℝ] ℝ, ℓ a = ℓ b) : a = b := by
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
  exact hℓ (h ℓ)

theorem weakIntegral_eq [SeparatingDual ℝ A] (hf : WeakIntegrable μ f) {a : A}
    (ha : ∀ ℓ : A →L[ℝ] ℝ, ℓ a = ∫ x, ℓ (f x) ∂μ) :
    weakIntegral μ f = a :=
  weakDual_ext (fun ℓ => (weakIntegral_apply hf ℓ).trans (ha ℓ).symm)

theorem weakIntegrable_zero (μ : Measure X) : WeakIntegrable μ (fun _ : X => (0 : A)) := by
  refine ⟨?_, 0, ?_⟩ <;> simp

@[simp] theorem weakIntegral_zero [SeparatingDual ℝ A] (μ : Measure X) :
    weakIntegral μ (fun _ : X => (0 : A)) = 0 := by
  apply weakIntegral_eq (weakIntegrable_zero μ)
  simp

theorem WeakIntegrable.add (hf : WeakIntegrable μ f) (hg : WeakIntegrable μ g) :
    WeakIntegrable μ (fun x => f x + g x) := by
  obtain ⟨a, ha⟩ := hf.2
  obtain ⟨b, hb⟩ := hg.2
  refine ⟨fun ℓ => ?_, a+b, fun ℓ => ?_⟩
  · simpa only [map_add] using (hf.1 ℓ).add (hg.1 ℓ)
  · simp only [map_add]
    rw [ha ℓ, hb ℓ, integral_add (hf.1 ℓ) (hg.1 ℓ)]

theorem weakIntegral_add [SeparatingDual ℝ A]
    (hf : WeakIntegrable μ f) (hg : WeakIntegrable μ g) :
    weakIntegral μ (fun x => f x + g x) = weakIntegral μ f + weakIntegral μ g := by
  apply weakIntegral_eq (hf.add hg)
  intro ℓ
  simp only [map_add]
  rw [weakIntegral_apply hf, weakIntegral_apply hg, integral_add (hf.1 ℓ) (hg.1 ℓ)]

theorem WeakIntegrable.neg (hf : WeakIntegrable μ f) :
    WeakIntegrable μ (fun x => -f x) := by
  obtain ⟨a, ha⟩ := hf.2
  refine ⟨fun ℓ => ?_, -a, fun ℓ => ?_⟩
  · simpa only [map_neg] using (hf.1 ℓ).neg
  · simpa only [map_neg, integral_neg] using congrArg Neg.neg (ha ℓ)

theorem weakIntegral_neg [SeparatingDual ℝ A] (hf : WeakIntegrable μ f) :
    weakIntegral μ (fun x => -f x) = -weakIntegral μ f := by
  apply weakIntegral_eq hf.neg
  intro ℓ
  simp only [map_neg, integral_neg]
  rw [weakIntegral_apply hf]

theorem WeakIntegrable.sub (hf : WeakIntegrable μ f) (hg : WeakIntegrable μ g) :
    WeakIntegrable μ (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem weakIntegral_sub [SeparatingDual ℝ A]
    (hf : WeakIntegrable μ f) (hg : WeakIntegrable μ g) :
    weakIntegral μ (fun x => f x - g x) = weakIntegral μ f - weakIntegral μ g := by
  simpa only [sub_eq_add_neg, weakIntegral_neg hg] using weakIntegral_add hf hg.neg

theorem WeakIntegrable.smul (r : ℝ) (hf : WeakIntegrable μ f) :
    WeakIntegrable μ (fun x => r • f x) := by
  obtain ⟨a, ha⟩ := hf.2
  refine ⟨fun ℓ => ?_, r • a, fun ℓ => ?_⟩
  · simpa only [map_smul, smul_eq_mul] using (hf.1 ℓ).const_mul r
  · simp only [map_smul, smul_eq_mul]
    rw [ha ℓ, integral_const_mul]

theorem weakIntegral_smul [SeparatingDual ℝ A] (r : ℝ) (hf : WeakIntegrable μ f) :
    weakIntegral μ (fun x => r • f x) = r • weakIntegral μ f := by
  apply weakIntegral_eq (WeakIntegrable.smul r hf)
  intro ℓ
  simp only [map_smul, smul_eq_mul]
  rw [weakIntegral_apply hf, integral_const_mul]

theorem WeakIntegrable.congr_ae (hf : WeakIntegrable μ f) (hfg : f =ᵐ[μ] g) :
    WeakIntegrable μ g := by
  obtain ⟨a, ha⟩ := hf.2
  exact ⟨fun ℓ => (hf.1 ℓ).congr (hfg.fun_comp ℓ), a,
    fun ℓ => (ha ℓ).trans (integral_congr_ae (hfg.fun_comp ℓ))⟩

theorem weakIntegral_congr_ae [SeparatingDual ℝ A]
    (hf : WeakIntegrable μ f) (hfg : f =ᵐ[μ] g) :
    weakIntegral μ f = weakIntegral μ g := by
  apply weakDual_ext
  intro ℓ
  rw [weakIntegral_apply hf, weakIntegral_apply (hf.congr_ae hfg)]
  exact integral_congr_ae (hfg.fun_comp ℓ)

theorem weakIntegral_congr (hfg : ∀ x, f x = g x) :
    weakIntegral μ f = weakIntegral μ g := by
  rw [funext hfg]

/-- Continuous linear images are weakly integrable because their dual tests
are precisely tests composed with the continuous linear map. -/
theorem WeakIntegrable.map (hf : WeakIntegrable μ f) (L : A →L[ℝ] B) :
    WeakIntegrable μ (fun x => L (f x)) := by
  obtain ⟨a, ha⟩ := hf.2
  exact ⟨fun ℓ => hf.1 (ℓ.comp L), L a, fun ℓ => ha (ℓ.comp L)⟩

theorem weakIntegral_map [SeparatingDual ℝ B] (L : A →L[ℝ] B)
    (hf : WeakIntegrable μ f) :
    weakIntegral μ (fun x => L (f x)) = L (weakIntegral μ f) := by
  apply weakDual_ext
  intro ℓ
  rw [weakIntegral_apply (hf.map L)]
  exact (weakIntegral_apply hf (ℓ.comp L)).symm

theorem weakIntegrable_const (μ : Measure X) [IsFiniteMeasure μ] (a : A) :
    WeakIntegrable μ (fun _ : X => a) := by
  refine ⟨fun _ => integrable_const _, μ.real Set.univ • a, fun ℓ => ?_⟩
  simp only [map_smul, integral_const]

theorem weakIntegral_const [SeparatingDual ℝ A] (μ : Measure X) [IsFiniteMeasure μ] (a : A) :
    weakIntegral μ (fun _ : X => a) = μ.real Set.univ • a := by
  apply weakIntegral_eq (weakIntegrable_const μ a)
  intro ℓ
  simp only [map_smul, integral_const]

theorem WeakIntegrable.finset_sum {ι : Type*} (s : Finset ι) (F : ι → X → A)
    (hF : ∀ i ∈ s, WeakIntegrable μ (F i)) :
    WeakIntegrable μ (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weakIntegrable_zero (A := A) μ
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, WeakIntegrable μ (F j) :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self _ _)).add (ih hs)

theorem weakIntegral_finset_sum [SeparatingDual ℝ A] {ι : Type*}
    (s : Finset ι) (F : ι → X → A) (hF : ∀ i ∈ s, WeakIntegrable μ (F i)) :
    weakIntegral μ (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, weakIntegral μ (F i) := by
  apply weakDual_ext
  intro ℓ
  rw [weakIntegral_apply (WeakIntegrable.finset_sum s F hF)]
  simp only [map_sum]
  rw [integral_finset_sum s (fun i hi => (hF i hi).1 ℓ)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (weakIntegral_apply (hF i hi) ℓ).symm

end Topological

section Bochner

variable {X A : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A] {f : X → A}

/-- The weak construction agrees with the actual Bochner integral wherever
the latter exists. The weak theory therefore extends ordinary integration. -/
theorem bochner_weakIntegrable (hf : Integrable f μ) : WeakIntegrable μ f :=
  ⟨fun ℓ => ℓ.integrable_comp hf, ∫ x, f x ∂μ,
    fun ℓ => (ℓ.integral_comp_comm hf).symm⟩

theorem weakIntegral_eq_bochner (hf : Integrable f μ) :
    weakIntegral μ f = ∫ x, f x ∂μ :=
  weakIntegral_eq (bochner_weakIntegrable hf) (fun ℓ => (ℓ.integral_comp_comm hf).symm)

end Bochner

end UV
