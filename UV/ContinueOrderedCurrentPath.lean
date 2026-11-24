import UV.ContinuationSectorPlane

/-! Closed ordered paths in the sector-plane carrier chart. -/

namespace UV.SectorPlane

/-- Vertices in the real carrier chart of a fixed sector plane. -/
structure OrderedTwoBandPath where
  hops : ℕ
  time : ℕ → ℝ
  position : ℕ → Spatial
  time_closed : time hops = time 0
  space_closed : position hops = position 0

end UV.SectorPlane
