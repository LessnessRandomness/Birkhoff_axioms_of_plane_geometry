import Mathlib

-- this should contain all necessary things (axioms) for Euclidean plane geometry, I hope
structure Birkhoff_geometry where
  point : Type
  line : ∀ {p1 p2 : point}, p1 ≠ p2 → Set point

  point_A : point
  point_B : point
  point_C : point
  A_ne_B : point_A ≠ point_B
  C_not_on_AB : point_C ∉ line A_ne_B

  get_coordinate : ∀ {p1 p2 p : point} {H : p1 ≠ p2}, p ∈ line H → ℝ
  get_point : ∀ {p1 p2 : point}, p1 ≠ p2 → ℝ → point

  get_point_property : ∀ {p1 p2 : point} (H : p1 ≠ p2) (x : ℝ), get_point H x ∈ line H
  coordinate_function_property_1 :
    ∀ {p1 p2 p : point} {H : p1 ≠ p2} (H0 : p ∈ line H), get_point H (get_coordinate H0) = p
  coordinate_function_property_2 :
    ∀ {p1 p2 : point} (H : p1 ≠ p2) (x : ℝ), get_coordinate (get_point_property H x) = x

  two_points_belong_to_line_through_them :
    ∀ {p1 p2 : point} (H : p1 ≠ p2), p1 ∈ line H ∧ p2 ∈ line H

  halfline : ∀ {start p : point}, start ≠ p → Set point
  halfline_def : ∀ {start p : point} (H : start ≠ p),
    let L := line H
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    if x1 < x2
    then halfline H = setOf (fun a => ∃ (h : a ∈ L), x1 ≤ get_coordinate h)
    else halfline H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ≤ x1)

  segment : ∀ {p1 p2 : point}, p1 ≠ p2 → Set point
  segment_def : ∀ {p1 p2 : point} (H : p1 ≠ p2),
    let L := line H
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    if x1 < x2
    then segment H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x1 x2)
    else segment H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x2 x1)

  distance : point → point → ℝ
  distance_distinct_def : ∀ {p1 p2 : point} (H : p1 ≠ p2),
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    distance p1 p2 = abs (x1 - x2)
  distance_same_def : ∀ (p : point), distance p p = 0

  get_direction : ∀ {start p : point}, start ≠ p → Real.Angle
  get_point_of_direction : point → Real.Angle → point

  get_point_of_direction_property :
    ∀ (start : point) (x : Real.Angle), start ≠ get_point_of_direction start x
  direction_function_property_1 :
    ∀ {start p : point} (H : start ≠ p),
    get_point_of_direction start (get_direction H) ∈ halfline H
  direction_function_property_2 :
    ∀ (start : point) (x : Real.Angle),
    get_direction (get_point_of_direction_property start x) = x

  angle : ∀ {p1 start p2 : point}, start ≠ p1 → start ≠ p2 → Real.Angle
  angle_def : ∀ {p1 start p2 : point} (H1 : start ≠ p1) (H2 : start ≠ p2),
    let d1 := get_direction H1
    let d2 := get_direction H2
    let delta := if d1.toReal < d2.toReal then d2 - d1 else d1 - d2
    angle H1 H2 = if delta.toReal ≤ Real.pi then delta else - delta

  continuity_axiom_1 : ∀ {start p1 p2 p : point}
    (H1 : start ≠ p1) (H2 : start ≠ p2) (H12 : p1 ≠ p2) (H : start ≠ p),
    p ∈ segment H12 → angle H1 H + angle H H2 = angle H1 H2
  continuity_axiom_2 : ∀ {start p1 p2 p : point}
    (H1 : start ≠ p1) (H2 : start ≠ p2) (H12 : p1 ≠ p2) (H : start ≠ p),
    angle H1 H + angle H H2 = angle H1 H2 →
    ∃ (a : point) (Ha : start ≠ p), a ∈ halfline Ha ∧ a ∈ segment H12

  similarity_axiom : ∀ {a b c a0 b0 c0 : point} {k : ℝ}
    (Hba : b ≠ a) (Hbc : b ≠ c) (Hba0 : b0 ≠ a0) (Hbc0 : b0 ≠ c0),
    0 < k →
    distance a0 b0 = k * distance a b →
    distance b0 c0 = k * distance b c →
    angle Hba0 Hbc0 = angle Hba Hbc →
    distance a0 c0 = k * distance a c
