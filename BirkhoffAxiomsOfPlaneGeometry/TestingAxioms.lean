import BirkhoffAxiomsOfPlaneGeometry.Axioms

namespace Test

def point : Type := EuclideanSpace ℝ (Fin 2)

def line {p1 p2 : point} : p1 ≠ p2 → Set point :=
  fun _ => setOf (fun x =>
    (p2 0 - p1 0) * (x 1 - p1 1) = (p2 1 - p1 1) * (x 0 - p1 0))

def point_A : point := !₂[0, 0]
def point_B : point := !₂[1, 0]
def point_C : point := !₂[0, 1]

theorem A_ne_B : point_A ≠ point_B := by
  intro H
  unfold point_A point_B at H
  have H0: (!₂[(0: ℝ), 0]) 0 = (!₂[1, 0]) 0 := congrFun H 0
  simp at H0

theorem C_not_on_AB : point_C ∉ line A_ne_B := by
  intro H
  unfold line at H
  simp at H
  unfold point_A point_B point_C at H
  simp at H

noncomputable def get_coordinate {p1 p2 p : point} {H : p1 ≠ p2} (_ : p ∈ line H) : ℝ :=
  let d := Real.sqrt ((p 0 - p1 0) ^ 2 + (p 1 - p1 1) ^ 2)
  if 0 < (p2 0 - p1 0) * (p 0 - p1 0) + (p2 1 - p1 1) * (p 1 - p1 1)
  then d
  else - d

noncomputable def get_point {p1 p2 : point} (_ : p1 ≠ p2) (x : ℝ) : point :=
  let d := Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2)
  !₂[p1 0 + (x / d) * (p2 0 - p1 0), p1 1 + (x / d) * (p2 1 - p1 1)]

theorem aux00 (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 := by nlinarith

theorem distance_pos {p1 p2 : point} (H : p1 ≠ p2) :
    0 < Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) := by
  have H : Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) ≠ 0 := by
    intro H0; apply H; clear H
    have H1 : 0 ≤ (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 := by nlinarith
    have H2 : (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 = 0 := (Real.sqrt_eq_zero H1).mp H0
    have H3 : p2 0 - p1 0 = 0 := by nlinarith
    have H4 : p2 1 - p1 1 = 0 := by nlinarith
    unfold point at *
    ext i; fin_cases i <;> simp <;> grind
  have H0 := Real.sqrt_nonneg ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2)
  grind

theorem squared_distance_pos {p1 p2 : point} (H : p1 ≠ p2) :
    0 < (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 := by
  have H := distance_pos H
  exact Real.sqrt_pos.mp H

theorem get_point_property {p1 p2 : point} (H : p1 ≠ p2) (x : ℝ) : get_point H x ∈ line H := by
  unfold get_point line
  simp
  have H0 := distance_pos H
  field_simp

set_option maxHeartbeats 1000000 in
--- needed to increase hearbeats for this proof
theorem coordinate_function_property_1 {p1 p2 p : point} {H : p1 ≠ p2} (H0 : p ∈ line H) :
    get_point H (get_coordinate H0) = p := by
  unfold get_point get_coordinate line point at *
  have H1 := distance_pos H
  have H2 := squared_distance_pos H
  simp
  set d := Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2)
  set d' := Real.sqrt ((p 0 - p1 0) ^ 2 + (p 1 - p1 1) ^ 2)
  have d'_nonneg : 0 ≤ d' := by
    unfold d'; apply Real.sqrt_nonneg
  have sq_d : d ^ 2 = (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 := by
    have H2 := aux00 (p2 0 - p1 0) (p2 1 - p1 1)
    exact Real.sq_sqrt H2
  have sq_d' : d' ^ 2 = (p 0 - p1 0) ^ 2 + (p 1 - p1 1) ^ 2 := by
    have H2 := aux00 (p 0 - p1 0) (p 1 - p1 1)
    exact Real.sq_sqrt H2
  simp at *
  obtain H3 | H3 := eq_or_ne (p2 0) (p1 0)
  · rw [H3] at H0 sq_d ⊢
    simp_all
    obtain H0 | H0 := H0
    · rw [sub_eq_zero] at H0
      exfalso; apply H; ext i; fin_cases i <;> simp <;> grind
    · ext i; fin_cases i <;> simp
      · grind
      · rw [sub_eq_zero] at H0
        simp [H0] at sq_d'
        rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg d'_nonneg] at sq_d'
        rw [sq_eq_sq_iff_abs_eq_abs, abs_of_pos H1] at sq_d
        split_ifs <;> rename_i H4
        · field_simp
          rw [mul_pos_iff] at H4
          obtain ⟨H4, H5⟩ | ⟨H4, H5⟩ := H4
          · rw [abs_of_pos H5] at sq_d'
            rw [abs_of_pos H4] at sq_d
            grind
          · rw [abs_of_neg H5] at sq_d'
            rw [abs_of_neg H4] at sq_d
            grind
        · field_simp
          simp at H4
          rw [mul_nonpos_iff] at H4
          obtain ⟨H4, H5⟩ | ⟨H4, H5⟩ := H4
          · rw [abs_of_nonpos H5] at sq_d'
            rw [abs_of_nonneg H4] at sq_d
            grind
          · rw [abs_of_nonneg H5] at sq_d'
            rw [abs_of_nonpos H4] at sq_d
            grind
  · have H4 : p2 0 - p1 0 ≠ 0 := sub_ne_zero_of_ne H3
    have H5 : p 1 - p1 1 = (p2 1 - p1 1) / (p2 0 - p1 0) * (p 0 - p1 0) := by grind
    rw [H5] at sq_d'
    field_simp at sq_d'
    rw [show (p 0 - p1 0) ^ 2 * ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) =
             (d * (p 0 - p1 0)) ^ 2 by grind] at sq_d'
    rw [show d' ^ 2 * (p2 0 - p1 0) ^ 2 = (d' * (p2 0 - p1 0)) ^ 2 by grind] at sq_d'
    rw [sq_eq_sq_iff_abs_eq_abs, abs_mul, abs_mul] at sq_d'
    rw [abs_of_pos H1, abs_of_nonneg d'_nonneg] at sq_d'
    have H7 : (p 0 - p1 0) * ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) =
              (p 0 - p1 0) * d ^ 2 := by grind
    split_ifs <;> rename_i H6
    · rw [H5] at H6
      field_simp at H6
      rw [H7] at H6
      obtain H8 | H8 := lt_or_gt_of_ne H3
      · rw [div_pos_iff] at H6
        obtain ⟨H9, H10⟩ | ⟨H9, H10⟩ := H6 <;> try linarith
        rw [mul_neg_iff] at H9
        obtain ⟨H11, H12⟩ | ⟨H11, H12⟩ := H9 <;> try grind
        rw [abs_of_neg H10, abs_of_neg H11] at sq_d'
        have H10 : d' = (p 0 - p1 0) / (p2 0 - p1 0) * d := by grind
        rw [show p1 0 + d' / d * (p2 0 - p1 0) = p 0 by grind]
        rw [show p1 1 + d' / d * (p2 1 - p1 1) = p 1 by grind]
        ext i; fin_cases i <;> simp
      · field_simp at H5
        rw [div_pos_iff] at H6
        obtain ⟨H9, H10⟩ | ⟨H9, H10⟩ := H6 <;> try linarith
        rw [mul_pos_iff] at H9
        obtain ⟨H11, H12⟩ | ⟨H11, H12⟩ := H9 <;> try grind
        rw [abs_of_pos H10, abs_of_pos H11] at sq_d'
        have H10 : d' = (p 0 - p1 0) / (p2 0 - p1 0) * d := by grind
        rw [show p1 0 + d' / d * (p2 0 - p1 0) = p 0 by grind]
        rw [show p1 1 + d' / d * (p2 1 - p1 1) = p 1 by grind]
        ext i; fin_cases i <;> simp
    · simp at H6
      rw [H5] at H6
      field_simp at H6
      rw [H7] at H6
      obtain H8 | H8 := lt_or_gt_of_ne H3
      · rw [div_nonpos_iff] at H6
        obtain ⟨H9, H10⟩ | ⟨H9, H10⟩ := H6 <;> try linarith
        rw [mul_nonneg_iff] at H9
        obtain ⟨H11, H12⟩ | ⟨H11, H12⟩ := H9 <;> try grind
        rw [abs_of_neg (by linarith), abs_of_nonneg H11] at sq_d'
        have H10 : d' = (p 0 - p1 0) / (p1 0 - p2 0) * d := by grind
        rw [show p1 0 + -d' / d * (p2 0 - p1 0) = p 0 by grind]
        rw [show p1 1 + -d' / d * (p2 1 - p1 1) = p 1 by grind]
        ext i; fin_cases i <;> simp
      · rw [div_nonpos_iff] at H6
        obtain ⟨H9, H10⟩ | ⟨H9, H10⟩ := H6 <;> try linarith
        rw [mul_nonpos_iff] at H9
        obtain ⟨H11, H12⟩ | ⟨H11, H12⟩ := H9 <;> try grind
        rw [abs_of_pos (by linarith), abs_of_nonpos H11] at sq_d'
        have H10 : d' = (p 0 - p1 0) / (p1 0 - p2 0) * d := by grind
        rw [show p1 0 + -d' / d * (p2 0 - p1 0) = p 0 by grind]
        rw [show p1 1 + -d' / d * (p2 1 - p1 1) = p 1 by grind]
        ext i; fin_cases i <;> simp

theorem coordinate_function_property_2 {p1 p2 : point} (H : p1 ≠ p2) (x : ℝ) :
    get_coordinate (get_point_property H x) = x := by
  unfold get_point get_coordinate point at *
  simp
  set d := Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2)
  have d_pos : 0 < d := by
    unfold d; apply distance_pos H
  have sq_d : d ^ 2 = (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 := by
    have H2 := aux00 (p2 0 - p1 0) (p2 1 - p1 1)
    exact Real.sq_sqrt H2
  split_ifs <;> rename_i H0
  · field_simp at *
    rw [show x ^ 2 * ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) = (x * d) ^ 2 by grind]
    field_simp at *
    rw [← sq_d] at H0
    field_simp at H0
    rw [mul_pos_iff_of_pos_right d_pos] at H0
    have H1 : Real.sqrt (x ^ 2) = abs x := Real.sqrt_sq_eq_abs x
    rw [H1, abs_of_pos H0]
  · field_simp at *
    rw [← sq_d] at H0
    field_simp at H0
    simp at H0
    rw [mul_nonpos_iff] at H0
    obtain ⟨H0, H1⟩ | ⟨H0, H1⟩ := H0
    · linarith
    · rw [← sq_d]
      field_simp
      have H2 : Real.sqrt (x ^ 2) = abs x := Real.sqrt_sq_eq_abs x
      rw [H2, abs_of_nonpos H0]
      simp

theorem two_points_belong_to_line_through_them {p1 p2 : point} (H : p1 ≠ p2) :
    p1 ∈ line H ∧ p2 ∈ line H := by
  unfold line; simp
  ring

def halfline {start p : point} (H : start ≠ p) : Set point :=
  let L := line H
  let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
  let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
  if x1 < x2
  then setOf (fun a => ∃ (h : a ∈ L), x1 ≤ get_coordinate h)
  else setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ≤ x1)

theorem halfline_def {start p : point} (H : start ≠ p) :
    let L := line H
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    if x1 < x2
    then halfline H = setOf (fun a => ∃ (h : a ∈ L), x1 ≤ get_coordinate h)
    else halfline H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ≤ x1) := by
  unfold halfline; simp; grind

def segment {p1 p2 : point} (H : p1 ≠ p2) : Set point :=
  let L := line H
  let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
  let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
  if x1 < x2
  then setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x1 x2)
  else setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x2 x1)

def segment_def : ∀ {p1 p2 : point} (H : p1 ≠ p2),
    let L := line H
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    if x1 < x2
    then segment H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x1 x2)
    else segment H = setOf (fun a => ∃ (h : a ∈ L), get_coordinate h ∈ Set.Icc x2 x1) := by
  unfold segment; simp; grind

noncomputable def distance (p1 p2 : point) : ℝ :=
  Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2)

theorem distance_distinct_def {p1 p2 : point} (H : p1 ≠ p2) :
    let x1 := get_coordinate (two_points_belong_to_line_through_them H).1
    let x2 := get_coordinate (two_points_belong_to_line_through_them H).2
    distance p1 p2 = abs (x1 - x2) := by
  unfold distance get_coordinate
  simp; split_ifs <;> rename_i H0
  · have H1 : 0 ≤ Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) := by
      apply Real.sqrt_nonneg
    rw [abs_of_nonneg H1]
  · have H2 : 0 < (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2 := squared_distance_pos H
    linarith

theorem distance_same_def (p : point) : distance p p = 0 := by
  unfold distance; simp

noncomputable def get_direction {start p : point} (_ : start ≠ p) : Real.Angle :=
  let d := Real.sqrt ((p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2)
  let x := (p 0 - start 0) / d
  if 0 ≤ p 1 - start 1 then Real.arccos x else (- Real.arccos x)

noncomputable def get_point_of_direction (start : point) (a : Real.Angle) : point :=
  !₂[start 0 + a.cos, start 1 + a.sin]

theorem get_point_of_direction_property (start : point) (a : Real.Angle) :
    start ≠ get_point_of_direction start a := by
  unfold get_point_of_direction; simp
  intros H
  unfold point at *
  have H0 : start 0 = start 0 + a.cos := by
    nth_rw 1 [H]
    simp
  have H1 : start 1 = start 1 + a.sin := by
    nth_rw 1 [H]
    simp
  have H2 : a.cos = 0 := by linarith
  have H3 : a.sin = 0 := by linarith
  have H4 : a.cos ^ 2 + a.sin ^ 2 = 0 := by grind
  have H5 : a.cos ^ 2 + a.sin ^ 2 = 1 := by simp
  linarith

lemma aux_x {p1 p2 : point} (H : p1 ≠ p2) :
    (p2 0 - p1 0) / Real.sqrt ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) ∈ Set.Icc (- 1) 1 := by
  have H0 := distance_pos H
  have H0' := squared_distance_pos H
  set d2 := (p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2
  have H1 : 0 ≤ d2 - (p2 0 - p1 0) ^ 2 := by
    unfold d2
    nlinarith
  have H2 : ((p2 0 - p1 0) / Real.sqrt d2) ^ 2 ≤ 1 ^ 2 := by
    field_simp
    rw [show 1 = d2 / d2 by field_simp]
    rw [← sub_nonneg]
    field_simp
    have H3 : 0 / d2 ≤ (d2 - (p2 0 - p1 0) ^ 2) / d2 := by
      exact (div_le_div_iff_of_pos_right H0').mpr H1
    have H4 : (Real.sqrt d2) ^ 2 = d2 := by
      refine Real.sq_sqrt (by linarith)
    rw [H4]; simp at H3; exact H3
  rw [sq_le_sq] at H2
  simp at H1 H2
  obtain ⟨H2, H3⟩ | ⟨H2, H3⟩ := abs_cases ((p2 0 - p1 0) / Real.sqrt d2) <;> grind


set_option maxHeartbeats 400000 in
-- out of necessity
theorem direction_function_property_1 {start p : point} (H : start ≠ p) :
    get_point_of_direction start (get_direction H) ∈ halfline H := by
  unfold get_direction get_point_of_direction halfline at *
  simp
  have Hd := distance_pos H
  have Hd' := squared_distance_pos H
  set d := Real.sqrt ((p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2)
  split_ifs <;> rename_i H0 H1 <;> simp at *
  · rw [Real.cos_arccos, Real.sin_arccos]
    · have H2 : 1 - ((p 0 - start 0) / d) ^ 2 = ((p 1 - start 1) / d) ^ 2 := by
        rw [show 1 = d ^ 2 / d ^ 2 by field_simp]
        field_simp
        unfold d
        rw [Real.sq_sqrt]
        · ring
        · linarith
      rw [H2, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos Hd, abs_of_nonneg (by linarith)]
      have h : !₂[start 0 + (p 0 - start 0) / d,
                  start 1 + (p 1 - start 1) / d] ∈ line H := by
        unfold line
        refine Set.mem_setOf.mpr ?_; simp
        field_simp
      use h
      unfold get_coordinate; simp; split_ifs <;> rename_i H4
      · field_simp
        rw [show d ^ 2 = (p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2 by grind]
        field_simp; simp
      · field_simp at H4; simp at H4
        rw [show (p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2 = d ^ 2 by grind] at H4
        field_simp at H4
        linarith
    · exact (aux_x H).1
    · exact (aux_x H).2
  · rw [Real.cos_arccos, Real.sin_arccos]
    · have H2 : 1 - ((p 0 - start 0) / d) ^ 2 = ((p 1 - start 1) / d) ^ 2 := by
        rw [show 1 = d ^ 2 / d ^ 2 by field_simp]
        field_simp
        have H3 : d ^ 2 = (p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2 := by
          unfold d
          rw [Real.sq_sqrt]
          linarith
        rw [H3]; ring
      rw [H2, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos Hd, abs_of_neg (by linarith)]
      have h : !₂[start 0 + (p 0 - start 0) / d,
                  start 1 + (p 1 - start 1) / d] ∈ line H := by
        unfold line
        refine Set.mem_setOf.mpr ?_; simp
        field_simp
      rw [show - (- (p 1 - start 1) / d) = (p 1 - start 1) / d by ring]
      use h
      unfold get_coordinate; simp; split_ifs <;> rename_i H4
      · field_simp
        rw [show d ^ 2 = (p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2 by grind]
        field_simp; simp
      · field_simp at H4; simp at H4
        rw [show (p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2 = d ^ 2 by grind] at H4
        field_simp at H4
        linarith
    · exact (aux_x H).1
    · exact (aux_x H).2
  · exfalso
    unfold get_coordinate at H0; simp at H0; split_ifs at * <;> rename_i H4 <;> grind
  · exfalso
    unfold get_coordinate at H0; simp at H0; split_ifs at * <;> rename_i H4 <;> grind

theorem direction_function_property_2 (start : point) (x : Real.Angle) :
    get_direction (get_point_of_direction_property start x) = x := by
  unfold get_direction get_point_of_direction
  have H : x.toReal ≤ Real.pi := Real.Angle.toReal_le_pi x
  have H0 : - Real.pi < x.toReal := Real.Angle.neg_pi_lt_toReal x
  simp; split_ifs <;> rename_i H1
  · nth_rw 2 [← Real.Angle.coe_toReal x]
    congr
    rw [← Real.Angle.sin_toReal] at H1
    rw [← Real.Angle.cos_toReal, Real.arccos_cos]
    · by_contra H2; simp at H2
      have H3 := Real.sin_neg_of_neg_of_neg_pi_lt H2 H0
      linarith
    · exact H
  · have H2 (t: ℝ): - Real.arccos t = Real.arccos (- t) - Real.pi := by
      rw [Real.arccos_neg]; ring
    nth_rw 2 [← Real.Angle.coe_toReal x]
    simp at H1
    rw [← Real.Angle.sin_toReal] at H1
    rw [← Real.Angle.coe_neg, ← Real.Angle.cos_toReal]
    congr
    rw [H2, ← Real.cos_add_pi, Real.arccos_cos]
    · ring
    · linarith
    · simp
      by_contra H3; simp at H3
      have H3 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) H
      linarith

noncomputable def angle {p1 start p2 : point} (_ : start ≠ p1) (_ : start ≠ p2) :=
  let d1 := distance start p1
  let d2 := distance start p2
  let dot_product := (p1 0 - start 0) * (p2 0 - start 0) + (p1 1 - start 1) * (p2 1 - start 1)
  Real.arccos (dot_product / d1 / d2)

lemma aux01 {x y : ℝ} (H : x ^ 2 + y ^ 2 = 1) (H0 : 0 ≤ y) : y = Real.sin (Real.arccos x) := by
  have H1 : y ^ 2 = 1 - Real.cos (Real.arccos x) ^ 2 := by
    rw [Real.cos_arccos (by nlinarith) (by nlinarith)]
    exact (sub_eq_of_eq_add' H.symm).symm
  rw [← Real.sin_sq] at H1
  have H2 : 0 ≤ Real.sin (Real.arccos x) := Real.sin_nonneg_of_mem_Icc
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg H0, abs_of_nonneg H2] at H1
  exact H1

lemma aux02 {x y : ℝ} (H : x ^ 2 + y ^ 2 = 1) (H0 : y ≤ 0) : y = - Real.sin (Real.arccos x) := by
  have H1 : y ^ 2 = 1 - Real.cos (Real.arccos x) ^ 2 := by
    rw [Real.cos_arccos (by nlinarith) (by nlinarith)]
    exact (sub_eq_of_eq_add' H.symm).symm
  rw [← Real.sin_sq] at H1
  have H2 : 0 ≤ Real.sin (Real.arccos x) := Real.sin_nonneg_of_mem_Icc
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonpos H0, abs_of_nonneg H2] at H1
  rw [<- H1]; simp


lemma angle_def_aux01 {x : ℝ} (H : x ∈ Set.Icc (-Real.pi) Real.pi)
    (H0 : 0 ≤ (Real.Angle.coe x).toReal) :
    x = - Real.pi ∨ x ∈ Set.Icc 0 Real.pi := by
  have H1 : x = - Real.pi ∨ x ∈ Set.Ioc (- Real.pi) Real.pi := by grind
  obtain H1 | H1 := H1
  · left; exact H1
  · right
    contrapose! H0
    simp at *
    obtain ⟨H2, H3⟩ := H1
    apply eq_or_lt_of_le at H3
    obtain H3 | H3 := H3
    · rw [H3] at H0
      linarith [H0 Real.pi_nonneg]
    · obtain H4 | H4 := lt_or_ge x 0
      · rw [Real.Angle.toReal_coe,
           (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith, by linarith⟩]
        exact H4
      · linarith [H0 H4]

lemma angle_def_aux02 {x : ℝ} (H : x ∈ Set.Icc (-Real.pi) Real.pi)
    (H0 : (Real.Angle.coe x).toReal < 0) :
    x ∈ Set.Ioo (-Real.pi) 0 := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  apply eq_or_lt_of_le at H1
  obtain H1 | H1 := H1
  · rw [← H1]; simp; linarith [Real.pi_pos]
  · have H3 := H0 H1
    rw [Real.Angle.toReal_coe,
        (toIocMod_eq_self Real.two_pi_pos).mpr ⟨H1, by linarith⟩]
    exact H3

lemma angle_def_aux03 {x : ℝ} (H : x ∈ Set.Icc 0 (2 * Real.pi))
    (H0 : 0 ≤ (Real.Angle.coe x).toReal) :
    x = 2 * Real.pi ∨ x ∈ Set.Icc 0 Real.pi := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  obtain ⟨H3, H4⟩ := H0
  have H5 := H4 H1
  have H6 : x < 2 * Real.pi := by grind
  rw [Real.Angle.toReal_coe, ← toIocMod_sub,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith, by linarith⟩]
  linarith

lemma angle_def_aux04 {x : ℝ} (H : x ∈ Set.Icc 0 (2 * Real.pi))
    (H0 : (Real.Angle.coe x).toReal < 0) :
    x ∈ Set.Ioo Real.pi (2 * Real.pi) := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  obtain H3 | H3 := lt_or_ge Real.pi x
  · have H4 : x = 2 * Real.pi := by linarith [H0 H3]
    rw [H4]; simp
  · rw [Real.Angle.toReal_coe,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith [Real.pi_pos], by linarith⟩]
    exact H1

lemma angle_def_aux05 {x : ℝ} (H : x ∈ Set.Icc 0 (2 * Real.pi))
    (H0 : 0 ≤ (Real.Angle.coe (-x)).toReal) :
    x = 0 ∨ x ∈ Set.Icc Real.pi (2 * Real.pi) := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  obtain ⟨H3, H4⟩ := H0
  obtain H5 | H5 := le_or_gt Real.pi x
  · linarith [H4 H5]
  · rw [← Real.Angle.coe_neg, Real.Angle.toReal_coe,
          (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith [Real.pi_pos], by linarith⟩]
    grind

-- by https://leanprover.zulipchat.com/#narrow/dm/816344-Aaron-Liu
lemma angle_def_aux06 {x : ℝ} (H : x ∈ Set.Icc 0 (2 * Real.pi))
    (H0 : (Real.Angle.coe (-x)).toReal < 0) :
    x ∈ Set.Ioo 0 Real.pi := by
  contrapose! H0
  obtain ⟨hl, hr⟩ := H
  apply eq_or_lt_of_le at hl
  obtain rfl | hx := hl
  · simp
  simp only [Set.mem_Ioo, not_and, not_lt, hx, true_imp_iff] at H0
  rw [Real.Angle.toReal_coe, ← toIocMod_add_left, ← sub_eq_add_neg,
    (toIocMod_eq_self Real.two_pi_pos).2 ⟨by linarith, by linarith⟩]
  linarith

lemma angle_def_aux07 {x : ℝ} (H : x ∈ Set.Icc (-Real.pi) Real.pi)
    (H0 : 0 ≤ (Real.Angle.coe x).toReal) :
    x = -Real.pi ∨ x ∈ Set.Icc 0 Real.pi := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  obtain ⟨H3, H4⟩ := H0
  apply eq_or_lt_of_le at H2
  obtain H5 | H5 := H2
  · rw [H5] at H4
    linarith [H4 Real.pi_nonneg]
  · obtain H6 | H6 := le_or_gt 0 x
    · linarith [H4 H6]
    · rw [Real.Angle.toReal_coe,
          (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by grind, by linarith⟩]
      exact H6

lemma angle_def_aux08 {x : ℝ} (H : x ∈ Set.Icc (-Real.pi) Real.pi)
    (H0 : (Real.Angle.coe x).toReal < 0) :
    x ∈ Set.Ioo (-Real.pi) 0 := by
  contrapose! H0
  simp at *
  obtain ⟨H1, H2⟩ := H
  apply eq_or_lt_of_le at H1
  obtain H1 | H1 := H1
  · rw [← H1]; simp
    exact Real.pi_nonneg
  · have H3 := H0 H1
    rw [Real.Angle.toReal_coe,
        (toIocMod_eq_self Real.two_pi_pos).mpr ⟨H1, by linarith⟩]
    exact H3

set_option maxHeartbeats 1000000 in
-- need more heartbeats
theorem angle_def {p1 start p2 : point} (H1 : start ≠ p1) (H2 : start ≠ p2) :
    let d1 := get_direction H1
    let d2 := get_direction H2
    let delta := d2 - d1
    angle H1 H2 = if 0 ≤ delta.sign then delta else - delta := by
  unfold angle get_direction distance
  simp
  set d1 := Real.sqrt ((p1 0 - start 0) ^ 2 + (p1 1 - start 1) ^ 2)
  set d2 := Real.sqrt ((p2 0 - start 0) ^ 2 + (p2 1 - start 1) ^ 2)
  set x1 := (p1 0 - start 0) / d1
  set y1 := (p1 1 - start 1) / d1
  set x2 := (p2 0 - start 0) / d2
  set y2 := (p2 1 - start 1) / d2
  have Hxy1 : x1 ^ 2 + y1 ^ 2 = 1 := by
    unfold x1 y1 d1
    have H5 := distance_pos H1
    field_simp
    rw [Real.sq_sqrt]
    linarith [squared_distance_pos H1]
  have Hxy2 : x2 ^ 2 + y2 ^ 2 = 1 := by
    unfold x2 y2 d2
    have H5 := distance_pos H2
    field_simp
    rw [Real.sq_sqrt]
    linarith [squared_distance_pos H2]
  have H9 : ((p1 0 - start 0) * (p2 0 - start 0) + (p1 1 - start 1) * (p2 1 - start 1))
                / d1 / d2 = x1 * x2 + y1 * y2 := by
        unfold x1 x2 y1 y2 d1 d2
        field_simp
  split_ifs <;> rename_i H5 H6 H7 <;> simp at *
  · rw [← Real.Angle.coe_sub, ← Real.Angle.toReal_nonneg_iff_sign_nonneg] at H7
    apply angle_def_aux01
          ⟨by linarith [Real.pi_pos, Real.arccos_nonneg x2, Real.arccos_le_pi x1],
           by linarith [Real.pi_pos, Real.arccos_nonneg x1, Real.arccos_le_pi x2]⟩ at H7
    obtain H7 | ⟨H7, H8⟩ := H7
    · have H8 : Real.arccos x2 = 0 := by linarith [Real.arccos_le_pi x1, Real.arccos_nonneg x2]
      have H10 : Real.arccos x1 = Real.pi := by linarith [Real.arccos_le_pi x1]
      simp at H8 H10
      have H11 : x1 = -1 := by nlinarith
      have H12 : x2 = 1 := by nlinarith
      rw [H11] at Hxy1; simp at Hxy1
      rw [H12] at Hxy2; simp at Hxy2
      rw [H9, H11, H12, Hxy1, Hxy2]; simp
    · rw [H9]
      have H10 : 0 ≤ y1 := by
        unfold y1 d1
        have H11 := distance_pos H1
        rw [div_nonneg_iff]
        left; exact ⟨by linarith, by linarith⟩
      have H11 : 0 ≤ y2 := by
        unfold y2 d2
        have H12 := distance_pos H2
        rw [div_nonneg_iff]
        left; exact ⟨by linarith, by linarith⟩
      have H12 := aux01 Hxy1 H10
      have H13 := aux01 Hxy2 H11
      have H14 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
      have H15 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
      rw [H12, H13]
      nth_rw 1 [← H14, ← H15]
      rw [← Real.cos_sub, ← Real.cos_neg, Real.arccos_cos (by linarith) (by linarith)]; simp
  · rw [← Real.Angle.coe_sub, ← Real.Angle.toReal_neg_iff_sign_neg] at H7
    apply angle_def_aux02
          ⟨by linarith [Real.pi_pos, Real.arccos_nonneg x2, Real.arccos_le_pi x1],
           by linarith [Real.pi_pos, Real.arccos_nonneg x1, Real.arccos_le_pi x2]⟩ at H7
    obtain ⟨H7, H8⟩ := H7
    rw [H9]; congr
    have H10 : 0 ≤ y1 := by
      unfold y1 d1
      have H11 := distance_pos H1
      rw [div_nonneg_iff]
      left; exact ⟨by linarith, by linarith⟩
    have H11 : 0 ≤ y2 := by
      unfold y2 d2
      have H12 := distance_pos H2
      rw [div_nonneg_iff]
      left; exact ⟨by linarith, by linarith⟩
    have H12 := aux01 Hxy1 H10
    have H13 := aux01 Hxy2 H11
    have H14 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
    have H15 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
    rw [H12, H13]
    nth_rw 1 [← H14, ← H15]
    rw [← Real.cos_sub, Real.arccos_cos (by linarith) (by linarith)]
  · rw [← Real.Angle.coe_add, ← Real.Angle.toReal_nonneg_iff_sign_nonneg] at H7
    apply angle_def_aux03
          ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2],
           by linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]⟩ at H7
    obtain H7 | ⟨H7, H8⟩ := H7
    · have H10 : Real.arccos x2 = Real.pi := by
        linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]
      have H11 : Real.arccos x1 = Real.pi := by
        linarith [Real.arccos_le_pi x1]
      simp at H10 H11
      have H12 : x1 = -1 := by nlinarith
      have H13 : x2 = -1 := by nlinarith
      rw [H12] at Hxy1; simp at Hxy1
      rw [H13] at Hxy2; simp at Hxy2
      rw [H9, H12, H13, Hxy1, Hxy2]; simp
    · rw [H9]; congr
      have H10 : y1 ≤ 0 := by
        unfold y1 d1
        have H11 := distance_pos H1
        rw [div_nonpos_iff]
        right; exact ⟨by linarith, by linarith⟩
      have H11 : 0 ≤ y2 := by
        unfold y2 d2
        have H12 := distance_pos H2
        rw [div_nonneg_iff]
        left; exact ⟨by linarith, by linarith⟩
      have H12 := aux02 Hxy1 H10
      have H13 := aux01 Hxy2 H11
      have H14 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
      have H15 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
      rw [H12, H13]
      nth_rw 1 [← H14, ← H15]
      rw [← Real.sin_neg, ← Real.cos_neg (Real.arccos x1), ← Real.cos_sub, ← Real.cos_neg]
      rw [Real.arccos_cos (by linarith) (by linarith)]; simp
  · rw [← Real.Angle.coe_add, ← Real.Angle.toReal_neg_iff_sign_neg] at H7
    apply angle_def_aux04
          ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2],
           by linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]⟩ at H7
    obtain ⟨H7, H8⟩ := H7
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    use 1; simp
    rw [H9]
    have H10 : y1 ≤ 0 := by
      unfold y1 d1
      have H11 := distance_pos H1
      rw [div_nonpos_iff]
      right; exact ⟨by linarith, by linarith⟩
    have H11 : 0 ≤ y2 := by
      unfold y2 d2
      have H12 := distance_pos H2
      rw [div_nonneg_iff]
      left; exact ⟨by linarith, by linarith⟩
    have H12 := aux02 Hxy1 H10
    have H13 := aux01 Hxy2 H11
    have H14 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
    have H15 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
    rw [H12, H13]
    nth_rw 1 [← H14, ← H15]
    rw [← Real.sin_neg, ← Real.cos_neg (Real.arccos x1), ← Real.cos_sub]
    rw [show -Real.arccos x1 - Real.arccos x2 = - (Real.arccos x1 + Real.arccos x2) by ring]
    rw [← Real.cos_neg]; simp
    rw [show Real.arccos x1 + Real.arccos x2 =
             Real.arccos x1 + Real.arccos x2 - Real.pi + Real.pi by ring]
    rw [Real.cos_add_pi, Real.arccos_neg]
    rw [Real.arccos_cos (by linarith) (by linarith)]; ring
  · rw [← Real.Angle.toReal_nonneg_iff_sign_nonneg] at H7
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_sub] at H7
    rw [show -Real.arccos x2 - Real.arccos x1 = - (Real.arccos x1 + Real.arccos x2) by ring] at H7
    apply angle_def_aux05
          ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2],
           by linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]⟩  at H7
    obtain H7 | ⟨H7, H8⟩ := H7
    · have H10 : Real.arccos x1 = 0 := by linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2]
      have H11 : Real.arccos x2 = 0 := by linarith [Real.arccos_nonneg x2]
      simp at H10 H11
      have H12 : x1 = 1 := by nlinarith
      have H13 : x2 = 1 := by nlinarith
      rw [H12] at Hxy1; simp at Hxy1
      rw [H13] at Hxy2; simp at Hxy2
      rw [H9, H12, H13, Hxy1, Hxy2]
      simp
    · rw [H9, ← Real.Angle.coe_neg, ← Real.Angle.coe_sub]
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      use 1; simp
      have H12 : 0 ≤ y1 := by
        unfold y1 d1
        have H13 := distance_pos H1
        rw [div_nonneg_iff]
        left; exact ⟨by linarith, by linarith⟩
      have H13 : y2 ≤ 0 := by
        unfold y2 d2
        have H14 := distance_pos H2
        rw [div_nonpos_iff]
        right; exact ⟨by linarith, by linarith⟩
      have H14 := aux01 Hxy1 H12
      have H15 := aux02 Hxy2 H13
      have H16 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
      have H17 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
      rw [H14, H15]
      nth_rw 1 [← H16, ← H17]
      rw [← Real.sin_neg, ← Real.cos_neg (Real.arccos x2), ← Real.cos_sub]
      simp
      rw [show Real.arccos x1 + Real.arccos x2 =
               Real.arccos x1 + Real.arccos x2 - Real.pi + Real.pi by ring]
      rw [Real.cos_add_pi, Real.arccos_neg]
      rw [Real.arccos_cos (by linarith) (by linarith)]; ring
  · rw [← Real.Angle.toReal_neg_iff_sign_neg] at H7
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_sub] at H7
    rw [show -Real.arccos x2 - Real.arccos x1 = - (Real.arccos x1 + Real.arccos x2) by ring] at H7
    have H10 := angle_def_aux06
      ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2],
       by linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]⟩ H7
    simp only [Set.mem_Ioo] at H10
    obtain ⟨H10, H11⟩ := H10
    rw [H9]
    have H12 : 0 ≤ y1 := by
      unfold y1 d1
      have H13 := distance_pos H1
      rw [div_nonneg_iff]
      left; exact ⟨by linarith, by linarith⟩
    have H13 : y2 ≤ 0 := by
      unfold y2 d2
      have H14 := distance_pos H2
      rw [div_nonpos_iff]
      right; exact ⟨by linarith, by linarith⟩
    have H14 := aux01 Hxy1 H12
    have H15 := aux02 Hxy2 H13
    have H16 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
    have H17 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
    rw [H14, H15]
    nth_rw 1 [← H16, ← H17]
    rw [← Real.sin_neg, ← Real.cos_neg (Real.arccos x2), ← Real.cos_sub]
    rw [← Real.Angle.coe_add, Real.arccos_cos]
    · congr; ring
    · linarith [Real.arccos_nonneg x1, Real.arccos_nonneg x2]
    · linarith
  · rw [← Real.Angle.toReal_nonneg_iff_sign_nonneg] at H7
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add] at H7
    apply angle_def_aux07
      ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_le_pi x2],
       by linarith [Real.arccos_le_pi x1, Real.arccos_nonneg x2]⟩ at H7
    obtain H7 | ⟨H7, H8⟩ := H7
    · have H10 : Real.arccos x2 = Real.pi := by
        linarith [Real.arccos_nonneg x1, Real.arccos_le_pi x2]
      have H11 : Real.arccos x1 = 0 := by
        linarith [Real.arccos_le_pi x1, Real.arccos_nonneg x2]
      simp at H10 H11
      have H12 : x1 = 1 := by nlinarith
      have H13 : x2 = - 1 := by nlinarith
      rw [H12] at Hxy1; simp at Hxy1
      rw [H13] at Hxy2; simp at Hxy2
      rw [H9, H12, H13, Hxy1, Hxy2]; simp
    · rw [H9]
      have H14 : y1 ≤ 0 := by
        unfold y1 d1
        have H15 := distance_pos H1
        rw [div_nonpos_iff]
        right; exact ⟨by linarith, by linarith⟩
      have H15 : y2 ≤ 0 := by
        unfold y2 d2
        have H16 := distance_pos H2
        rw [div_nonpos_iff]
        right; exact ⟨by linarith, by linarith⟩
      have H16 := aux02 Hxy1 H14
      have H17 := aux02 Hxy2 H15
      have H18 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
      have H19 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
      rw [H16, H17]
      nth_rw 1 [← H18, ← H19]
      rw [← Real.sin_neg, ← Real.sin_neg, ← Real.cos_neg (Real.arccos x1),
          ← Real.cos_neg (Real.arccos x2), ← Real.cos_sub]
      rw [show -Real.arccos x1 - -Real.arccos x2 = -(- Real.arccos x2 + Real.arccos x1) by ring]
      rw [Real.cos_neg]
      rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add, Real.arccos_cos (by linarith) (by linarith)]
  · rw [← Real.Angle.toReal_neg_iff_sign_neg] at H7
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add] at H7
    apply angle_def_aux08
      ⟨by linarith [Real.arccos_nonneg x1, Real.arccos_le_pi x2],
       by linarith [Real.arccos_le_pi x1, Real.arccos_nonneg x2]⟩ at H7
    obtain ⟨H7, H8⟩ := H7
    rw [H9]
    have H11 : y1 ≤ 0 := by
      unfold y1 d1
      have H12 := distance_pos H1
      rw [div_nonpos_iff]
      right; exact ⟨by linarith, by linarith⟩
    have H12 : y2 ≤ 0 := by
      unfold y2 d2
      have H13 := distance_pos H2
      rw [div_nonpos_iff]
      right; exact ⟨by linarith, by linarith⟩
    have H13 := aux02 Hxy1 H11
    have H14 := aux02 Hxy2 H12
    have H15 := @Real.cos_arccos x1 (by nlinarith) (by nlinarith)
    have H16 := @Real.cos_arccos x2 (by nlinarith) (by nlinarith)
    rw [H13, H14]
    nth_rw 1 [← H15, ← H16]
    rw [← Real.sin_neg, ← Real.sin_neg, ← Real.cos_neg (Real.arccos x1),
        ← Real.cos_neg (Real.arccos x2), ← Real.cos_sub]
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add]
    congr
    rw [Real.arccos_cos (by linarith) (by linarith)]
    ring


lemma aux00_for_continuity_axiom_1 {x : ℝ} (Hx : x ∈ Set.Ico 0 (2 * Real.pi)) :
    0 ≤ Real.sin x → x ∈ Set.Icc 0 Real.pi := by
  intro H
  refine ⟨Hx.1, ?_⟩
  contrapose! H
  have H0 := @Real.sin_neg_of_neg_of_neg_pi_lt (x - 2 * Real.pi) (by grind) (by grind)
  simp at H0
  exact H0

lemma aux01_for_continuity_axiom_1 {a b : ℝ} (Ha : a ∈ Set.Icc (-1) 1) (Hb : b ∈ Set.Icc (-1) 1) :
    Real.sin (Real.arccos a + Real.arccos b) =
    a * Real.sqrt (1 - b ^ 2) + b * Real.sqrt (1 - a ^ 2) := by
  rw [Real.sin_add, Real.sin_arccos, Real.sin_arccos,
     Real.cos_arccos Hb.1 Hb.2, Real.cos_arccos Ha.1 Ha.2]
  ring

lemma aux02_for_continuity_axiom_1 {a b : ℝ} (Ha : a ∈ Set.Icc (-1) 1) (Hb : b ∈ Set.Icc (-1) 1) :
    Real.cos (Real.arccos a + Real.arccos b) =
    a * b - Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) := by
  rw [Real.cos_add, Real.sin_arccos, Real.sin_arccos,
     Real.cos_arccos Hb.1 Hb.2, Real.cos_arccos Ha.1 Ha.2]

lemma aux03_for_continuity_axiom_1 {x1 x2 : ℝ}
    (Hx1 : x1 ∈ Set.Icc (-1) 1) (Hx2 : x2 ∈ Set.Icc (-1) 1) (Hx12 : x1 ≠ -1 ∨ x2 ≠ -1) :
    Real.arccos x1 + Real.arccos x2 ∈ Set.Icc 0 Real.pi ↔
    0 ≤ x1 * Real.sqrt (1 - x2 ^ 2) + x2 * Real.sqrt (1 - x1 ^ 2) := by
  have H1 : Real.arccos x1 ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg x1, Real.arccos_le_pi x1⟩
  have H2 : Real.arccos x2 ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg x2, Real.arccos_le_pi x2⟩
  constructor <;> intro H
  · have H3 : 0 ≤ Real.sin (Real.arccos x1 + Real.arccos x2) :=
      Real.sin_nonneg_of_mem_Icc H
    rw [aux01_for_continuity_axiom_1 Hx1 Hx2] at H3
    exact H3
  · have H3 := Real.cos_arccos Hx1.1 Hx1.2
    have H4 := Real.cos_arccos Hx2.1 Hx2.2
    rw [← H3, ← H4] at H
    repeat rw [← Real.abs_sin_eq_sqrt_one_sub_cos_sq] at H
    rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc H1),
        abs_of_nonneg (Real.sin_nonneg_of_mem_Icc H2)] at H
    nth_rw 1 2 [mul_comm] at H
    rw [← Real.sin_add, add_comm] at H
    obtain H6 | H6 := eq_or_ne (Real.arccos x1 + Real.arccos x2) (2 * Real.pi)
    · have H7 : Real.arccos x1 = Real.pi := by
        linarith [Real.arccos_le_pi x1, Real.arccos_le_pi x2]
      have H8 : Real.arccos x2 = Real.pi := by
        linarith [Real.arccos_le_pi x2]
      simp at H7 H8; grind
    · exact aux00_for_continuity_axiom_1 (by grind) H

lemma aux04_for_continuity_axiom_1 {x1 x2 : ℝ}
    (Hx1 : x1 ∈ Set.Icc 0 Real.pi) (Hx2 : x2 ∈ Set.Icc 0 Real.pi) :
    Real.cos x1 = Real.cos x2 ↔ x1 = x2 := by
  constructor <;> intro H
  · apply Real.injOn_cos at H
    · exact H
    · exact Hx1
    · exact Hx2
  · grind



set_option maxHeartbeats 1000000 in
--- need more hearbeats
theorem continuity_axiom_1 {start p1 p2 p : point}
    (H1 : start ≠ p1) (H2 : start ≠ p2) (H12 : p1 ≠ p2) (H : start ≠ p) :
    p ∈ segment H12 → angle H1 H + angle H H2 = angle H1 H2 := by
  intros Hp
  unfold segment angle line at *; simp at *
  unfold get_coordinate distance at *; simp at *
  set d := Real.sqrt ((p 0 - start 0) ^ 2 + (p 1 - start 1) ^ 2)
  set d1 := Real.sqrt ((p1 0 - start 0) ^ 2 + (p1 1 - start 1) ^ 2)
  set d2 := Real.sqrt ((p2 0 - start 0) ^ 2 + (p2 1 - start 1) ^ 2)
  set x := (p 0 - start 0) / d
  set y := (p 1 - start 1) / d
  set x1 := (p1 0 - start 0) / d1
  set y1 := (p1 1 - start 1) / d1
  set x2 := (p2 0 - start 0) / d2
  set y2 := (p2 1 - start 1) / d2
/-
  have Hxy : x ^ 2 + y ^ 2 = 1 := by
    unfold x y d
    have H5 := distance_pos H
    field_simp
    rw [Real.sq_sqrt]
    linarith [squared_distance_pos H]
  have Hxy1 : x1 ^ 2 + y1 ^ 2 = 1 := by
    unfold x1 y1 d1
    have H5 := distance_pos H1
    field_simp
    rw [Real.sq_sqrt]
    linarith [squared_distance_pos H1]
  have Hxy2 : x2 ^ 2 + y2 ^ 2 = 1 := by
    unfold x2 y2 d2
    have H5 := distance_pos H2
    field_simp
    rw [Real.sq_sqrt]
    linarith [squared_distance_pos H2] -/
  have H3 : ((p1 0 - start 0) * (p 0 - start 0) + (p1 1 - start 1) * (p 1 - start 1)) /d1 / d =
            x * x1 + y * y1 := by
    unfold x x1 y y1 d d1
    field_simp
  have H4 : ((p 0 - start 0) * (p2 0 - start 0) + (p 1 - start 1) * (p2 1 - start 1)) / d / d2 =
            x * x2 + y * y2 := by
    unfold x x2 y y2 d d2
    field_simp
  have H5 : ((p1 0 - start 0) * (p2 0 - start 0) + (p1 1 - start 1) * (p2 1 - start 1)) / d1 / d2 =
            x1 * x2 + y1 * y2 := by
    unfold x1 x2 y1 y2 d1 d2
    field_simp
  simp at *; split_ifs at * <;> rename_i H6 H7 <;> simp at Hp <;> split_ifs at * <;> rename_i H8
  · rw [H3, H4, H5]
    rw [← aux04_for_continuity_axiom_1]
    · rw [Real.cos_arccos, aux02_for_continuity_axiom_1]
      · field_simp
        obtain ⟨Hp1, Hp2, Hp3⟩ := Hp
        have H9 : (p2 0 - p1 0) * (p 1 - p1 1) / d = (p2 1 - p1 1) * (p 0 - p1 0) / d := by
          have H10 : 0 < d := by unfold d; apply distance_pos H
          field_simp
          exact Hp2
        have H10 := distance_pos H12
        set d12 := Real.sqrt ((p1 0 - p2 0) ^ 2 + (p1 1 - p2 1) ^ 2)

        sorry
      · sorry
      · sorry
      · sorry
      · sorry
    · rw [aux03_for_continuity_axiom_1]
      · sorry
      · sorry
      · sorry
      · sorry
    · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

/-

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
    distance a0 c0 = k * distance a c -/

end Test
