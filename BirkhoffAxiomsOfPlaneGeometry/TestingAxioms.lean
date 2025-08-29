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

/- lemma aux05 (x1 y1 x2 y2 : ℝ) (H1 : x1 ^ 2 + y1 ^ 2 = 1) (H2 : x2 ^ 2 + y2 ^ 2 = 1) :
    Real.arccos (x1 * x2 + y1 * y2) = Real.arccos x1 - Real.arccos x2 := by
  have H : x1 = Real.cos (Real.arccos x1) := by
    rw [Real.cos_arccos (by nlinarith) (by nlinarith)]
  have H3 : y1 ^ 2 = 1 - Real.cos (Real.arccos x1) ^ 2 := by grind
  have H4 : y1 ^ 2 = Real.sin (Real.arccos x1) ^ 2 := by
    rw [← Real.sin_sq] at H3; exact H3
  rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at H4
  have H5 : x2 = Real.cos (Real.arccos x2) := by
    rw [Real.cos_arccos (by nlinarith) (by nlinarith)]
  have H6 : y2 ^ 2 = 1 - Real.cos (Real.arccos x2) ^ 2 := by grind
  have H7 : y2 ^ 2 = Real.sin (Real.arccos x2) ^ 2 := by
    rw [← Real.sin_sq] at H6; exact H6
  rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at H7
  obtain H4 | H4 := H4 <;> obtain H7 | H7 := H7
  · rw [H, H5, H4, H7]
    rw [← Real.cos_sub]
    rw [Real.arccos_cos (Real.arccos_nonneg x1) (Real.arccos_le_pi x1)]
    rw [Real.arccos_cos (Real.arccos_nonneg x2) (Real.arccos_le_pi x2)]
    obtain H8 | H8 := lt_or_ge (Real.arccos x1) (Real.arccos x2)
    · simp at H8
      sorry
    · sorry
  · sorry
  · sorry
  · sorry

 -/

set_option maxHeartbeats 1000000 in
-- need more heartbeats
theorem angle_def {p1 start p2 : point} (H1 : start ≠ p1) (H2 : start ≠ p2) :
    let d1 := get_direction H1
    let d2 := get_direction H2
    let delta := if d1.toReal < d2.toReal then d2 - d1 else d1 - d2
    angle H1 H2 = if delta.toReal ≤ Real.pi then delta else - delta := by
  unfold angle get_direction distance
  simp; split_ifs <;> rename_i H3 H4 H5 H6 <;> simp at *
  · rw [← Real.Angle.coe_sub] at H6 ⊢
    congr
    have H7 : (Real.Angle.coe (Real.arccos ((p2 0 - start 0) /
               √((p2 0 - start 0) ^ 2 + (p2 1 - start 1) ^ 2)) -
        Real.arccos ((p1 0 - start 0) / √((p1 0 - start 0) ^ 2 + (p1 1 - start 1) ^ 2)))).toReal =
        Real.arccos ((p2 0 - start 0) / √((p2 0 - start 0) ^ 2 + (p2 1 - start 1) ^ 2)) -
        Real.arccos ((p1 0 - start 0) / √((p1 0 - start 0) ^ 2 + (p1 1 - start 1) ^ 2)) := by
      rw [Real.Angle.toReal_coe_eq_self_iff]
      simp; constructor
      ·
        sorry
      · sorry

    sorry
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
  · sorry
  · sorry
  · sorry


/-
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
    distance a0 c0 = k * distance a c -/

end Test
