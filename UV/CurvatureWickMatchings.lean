import UV.VerifyCurvatureReindex

/-! Resolve Wick partners by occurrence position before assigning Fourier
labels. The recursive lists retain every multiplicity when labels coincide. -/

noncomputable section

namespace UV.CurvatureWick

open UV.VerifyCurvatureExpansion UV.VerifyCurvatureRouting
open UV.AdvanceCurvatureWick UV.NextCurvatureLaw

/-- Ordered enumeration used by the Wick recurrence. The first remaining
position is paired with each possible partner in turn. -/
def matchings {α : Type*} : ℕ → List α → List (List (α × α))
  | 0, [] => [[]]
  | 0, _ :: _ => []
  | _+1, [] => [[]]
  | k+1, a::l => l.zipIdx.flatMap fun q =>
      ((matchings k (l.eraseIdx q.2)).map (List.cons (a,q.1)))

def matchingWeight {α : Type*} (C : α → α → ℝ) (P : List (α × α)) : ℝ :=
  (P.map fun e => C e.1 e.2).prod

private theorem sum_flatMap {α β : Type*} (l : List α) (F : α → List β) (w : β → ℝ) :
    ((l.flatMap F).map w).sum = (l.map fun x => ((F x).map w).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem wick_sum_over_matchings {α β : Type*} (C : β → β → ℝ) (slot : α → β)
    (k : ℕ) (l : List α) :
    osWickMoment C k (l.map slot) =
      ((matchings k l).map (matchingWeight (fun i j => C (slot i) (slot j)))).sum := by
  induction k generalizing l with
  | zero => cases l <;> simp [osWickMoment,matchings,matchingWeight]
  | succ k ih =>
    cases l with
    | nil => simp [osWickMoment,matchings,matchingWeight]
    | cons a l =>
      simp only [List.map_cons,osWickMoment,matchings,List.zipIdx_map,List.map_map,sum_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,j⟩ _
      change C (slot a) (slot b) * osWickMoment C k ((l.map slot).eraseIdx j) = _
      rw [List.eraseIdx_map,ih,← List.sum_map_mul_left]
      simp [Function.comp_def,matchingWeight]

def endpoints {α : Type*} (P : List (α × α)) : List α :=
  P.flatMap fun e => [e.1,e.2]

theorem matching_endpoints_perm {α : Type*} {k : ℕ} {l : List α} {P : List (α × α)}
    (h : P ∈ matchings k l) : (endpoints P).Perm l := by
  induction k generalizing l P with
  | zero =>
    cases l with
    | nil => simp only [matchings,List.mem_singleton] at h; subst P; rfl
    | cons a l => simp [matchings] at h
  | succ k ih =>
    cases l with
    | nil => simp only [matchings,List.mem_singleton] at h; subst P; rfl
    | cons a l =>
      obtain ⟨⟨b,j⟩,hj,hrest⟩ := List.mem_flatMap.mp h
      obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hrest
      obtain ⟨_,hk,he⟩ := List.mem_zipIdx hj
      have hj' : j < l.length := by simpa using hk
      have hjb : l[j] = b := by simpa using he.symm
      have hperm := List.getElem_cons_eraseIdx_perm hj'
      rw [hjb] at hperm
      exact ((ih hQ).cons b |>.trans hperm).cons a

theorem endpoints_length {α : Type*} (P : List (α × α)) : (endpoints P).length = P.length*2 := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [endpoints] at ih ⊢; omega

def vertexPositions {r p : ℕ} (v : Fin r) : List (EndPosition r p) :=
  [.inl (v,0,0),.inl (v,1,0),.inl (v,0,1),.inl (v,1,1)]

def sourcePositions (r p : ℕ) : List (EndPosition r p) :=
  (List.ofFn (fun z : Fin r => z)).flatMap vertexPositions ++ List.ofFn (fun j : Fin p => .inr j)

def assignedOccurrence {n r p : ℕ} (v : Fin r → VertexChoice n) (probes : Fin p → ModeSlot n)
    (x : EndPosition r p) : Occurrence n := (isInteraction x, configuredSlot v probes x)

theorem source_positions_all {r p : ℕ} (x : EndPosition r p) : x ∈ sourcePositions r p := by
  rcases x with ⟨z,a,b⟩ | j
  · apply List.mem_append_left _ (List.mem_flatMap.mpr ⟨z, List.mem_ofFn.mpr ⟨z,rfl⟩, ?_⟩)
    fin_cases a <;> fin_cases b <;> simp [vertexPositions]
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem source_positions_length (r p : ℕ) :
    (sourcePositions r p).length = Fintype.card (EndPosition r p) := by
  have len (l : List (Fin r)) : (l.flatMap (vertexPositions (p := p))).length = l.length * 4 := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons,vertexPositions,ih]; omega
  simp [sourcePositions,len,EndPosition]

theorem source_positions_assigned {n r p : ℕ} (v : Fin r → VertexChoice n) (probes : Fin p → ModeSlot n) :
    (sourcePositions r p).map (assignedOccurrence v probes) = sourceOccurrences v (List.ofFn probes) := by
  have hv (z : Fin r) : ((vertexPositions z).map (assignedOccurrence v probes)) = vertexOccurrences (v z) := by
    simp [vertexPositions,assignedOccurrence,isInteraction,configuredSlot,vertexOccurrences]
  simp only [sourcePositions,sourceOccurrences,List.map_append,List.map_flatMap,List.map_ofFn,hv]
  congr 1
  have he : List.ofFn v = (List.ofFn (fun z : Fin r => z)).map v := by rw [List.map_ofFn]; rfl
  rw [he, List.flatMap_map]

theorem positional_wick_expansion {n r p : ℕ} (v : Fin r → VertexChoice n) (probes : Fin p → ModeSlot n)
    (ℓ : ℝ) :
    let w := sourceOccurrences v (List.ofFn probes)
    osWickMoment (occurrenceCovariance ℓ) w.length w =
      ((matchings (sourcePositions r p).length (sourcePositions r p)).map
        (matchingWeight (fun x y => occurrenceCovariance ℓ (assignedOccurrence v probes x) (assignedOccurrence v probes y)))).sum := by
  dsimp only
  rw [← source_positions_assigned v probes,List.length_map,wick_sum_over_matchings]

end UV.CurvatureWick
