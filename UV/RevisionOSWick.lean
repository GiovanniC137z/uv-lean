import Mathlib.Tactic

/-! Isserlis contractions at the two boundary observables in the scalar
reflection tests. The matrix entries are arbitrary pairwise covariances;
these identities check all multiplicities before any spacetime integration. -/

noncomputable section

namespace UV

/-- In a nonempty list pair the first index with each possible partner.
The depth parameter bounds the number of pairs in the recurrence. -/
def osWickMoment {ι : Type*} (c : ι → ι → ℝ) : ℕ → List ι → ℝ
  | 0, xs => if xs.isEmpty then 1 else 0
  | _ + 1, [] => 1
  | n + 1, i :: xs => ((xs.zipIdx 0).map fun (j, k) ↦ c i j *
      osWickMoment c n (xs.eraseIdx k)).sum

/-- The contractions at the unsubtracted quartic. The null free boundary
pair kills the terms in which the two probes contract with each other. -/
theorem osWick_unsubtracted_quartic_contractions {ι : Type*} (c : ι → ι → ℝ)
    (a b y : ι) (h : c a b = 0) :
    osWickMoment c 3 [a, b, y, y, y, y] / 24 =
      c y y * (c a y * c b y) / 2 := by
  simp [osWickMoment, List.zipIdx, List.eraseIdx, h]
  ring

/-- The free norm of two centered quadratic probes is the sum of the
cross-contractions. The `a` and `c` probes are the local inverse witnesses. -/
theorem osWick_centered_boundary_norm {ι : Type*} (K : ι → ι → ℝ)
    (a b c d : ι) (hac : K a c = 0) (had : K a d = 0) :
    osWickMoment K 2 [a, b, c, d] - K a b * osWickMoment K 1 [c, d] -
      K c d * osWickMoment K 1 [a, b] + K a b * K c d = 0 := by
  simp [osWickMoment, List.zipIdx, List.eraseIdx, hac, had]
  ring

/-- Insertion of the Wick-ordered quartic against four boundary factors.
The two correction terms cancel precisely the internal contractions. -/
theorem osWick_ordered_quartic_contractions {ι : Type*} (K : ι → ι → ℝ)
    (a b c d y : ι) :
    (osWickMoment K 4 [a, b, c, d, y, y, y, y] -
      6 * K y y * osWickMoment K 3 [a, b, c, d, y, y] +
      3 * K y y ^ 2 * osWickMoment K 2 [a, b, c, d]) / 24 =
      K a y * K b y * K c y * K d y := by
  simp [osWickMoment, List.zipIdx, List.eraseIdx]
  ring

/-- Fewer than four boundary factors give zero after Wick ordering. -/
theorem osWick_ordered_quartic_two_probes {ι : Type*} (K : ι → ι → ℝ)
    (a b y : ι) :
    osWickMoment K 3 [a, b, y, y, y, y] -
      6 * K y y * osWickMoment K 2 [a, b, y, y] +
      3 * K y y ^ 2 * osWickMoment K 1 [a, b] = 0 := by
  simp [osWickMoment, List.zipIdx, List.eraseIdx]
  ring

theorem osWick_ordered_quartic_no_probes {ι : Type*} (K : ι → ι → ℝ) (y : ι) :
    osWickMoment K 2 [y, y, y, y] - 6 * K y y * osWickMoment K 1 [y, y] +
      3 * K y y ^ 2 = 0 := by
  simp [osWickMoment, List.zipIdx, List.eraseIdx]
  ring

/-- Pointwise lower envelope for the quartic interaction density, including
its factor `1/4!` and a nonnegative switching function. -/
theorem osWick_quartic_density_lower {ζ : ℝ} (hζ : 0 ≤ ζ) (v y : ℝ) :
    -(v ^ 2 * ζ / 4) ≤ ζ * (y ^ 4 - 6 * v * y ^ 2 + 3 * v ^ 2) / 24 := by
  nlinarith [mul_nonneg hζ (sq_nonneg (y ^ 2 - 3 * v))]

end UV
