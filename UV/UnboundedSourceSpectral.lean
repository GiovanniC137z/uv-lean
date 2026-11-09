import UV.UnboundedSourceAbstract

/-! Separate spectral simple integrals imply strong domain commutation.
Only finite sums of the actual spectral projections and their moment limits
are used; no joint scalar spectral representation is required. -/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite Borel simple function, represented by its actual cells and real
coefficients, before integrating it against a projection-valued measure. -/
structure SourceSpectralSimple where
  index : Finset ℕ
  coefficient : ℕ → ℝ
  cell : ℕ → Set ℝ
  measurable : ∀ i ∈ index, MeasurableSet (cell i)

def SourceSpectralSimple.operator (s : SourceSpectralSimple)
    (P : Set ℝ → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i ∈ s.index, (s.coefficient i : ℂ) • P (s.cell i)

/-- Pairwise spectral projection commutation gives commutation of the
actual finite simple spectral integrals. -/
theorem source_simple_spectral_commute (s t : SourceSpectralSimple)
    (P Q : Set ℝ → H →L[ℂ] H)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B → Commute (P A) (Q B)) :
    Commute (s.operator P) (t.operator Q) := by
  unfold SourceSpectralSimple.operator
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  exact ((hPQ _ _ (s.measurable i hi) (t.measurable j hj)).smul_left _).smul_right _

omit [CompleteSpace H] in
/-- Strong limits preserve commutation with each fixed bounded operator. -/
theorem source_strongLimit_commute {A : ℕ → H →L[ℂ] H} {F B : H →L[ℂ] H}
    (hlim : ∀ x : H, Tendsto (fun n => A n x) atTop (𝓝 (F x)))
    (hcomm : ∀ n, Commute (A n) B) : Commute F B := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft := hlim (B x)
  have hright := B.continuous.continuousAt.tendsto.comp (hlim x)
  have he : ∀ n, A n (B x) = B (A n x) :=
    fun n => congrArg (fun C : H →L[ℂ] H => C x) (hcomm n).eq
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (he n).symm))

omit [CompleteSpace H] in
/-- A bounded operator commuting with the approximating spectral moments
preserves the maximal moment domain and intertwines its unbounded value. -/
theorem source_graph_commutes_of_moment_limits (K : H →ₗ.[ℂ] H)
    (A : ℕ → H →L[ℂ] H) (F : H →L[ℂ] H)
    (hMoment : ∀ x y : H, (x,y) ∈ K.graph ↔ Tendsto (fun n => A n x) atTop (𝓝 y))
    (hcomm : ∀ n, Commute (A n) F) : sourceGraphCommutes K F := by
  intro x
  apply (hMoment _ _).mpr
  have hx := (hMoment _ _).mp (K.mem_graph x)
  have hlim := F.continuous.continuousAt.tendsto.comp hx
  apply hlim.congr
  intro n
  exact (congrArg (fun C : H →L[ℂ] H => C (x : H)) (hcomm n).eq).symm

/-- The exact separate-resolution bridge used by the source: pairwise
spectral-projection commutation yields actual F/K domain commutation via
the two spectral moment limits, without a joint realization assumption. -/
theorem source_graph_commutes_of_spectral_resolutions (K : H →ₗ.[ℂ] H)
    (F : H →L[ℂ] H) (P Q : Set ℝ → H →L[ℂ] H)
    (s t : ℕ → SourceSpectralSimple)
    (hP : ∀ x : H, Tendsto (fun n => (s n).operator P x) atTop (𝓝 (F x)))
    (hQ : ∀ x y : H, (x,y) ∈ K.graph ↔
      Tendsto (fun n => (t n).operator Q x) atTop (𝓝 y))
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B → Commute (P A) (Q B)) :
    sourceGraphCommutes K F := by
  apply source_graph_commutes_of_moment_limits K (fun n => (t n).operator Q) F hQ
  intro m
  exact (source_strongLimit_commute hP
    (fun n => source_simple_spectral_commute (s n) (t m) P Q hPQ)).symm

end UV
