import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27491

open PEqualNP.CircuitLowerBounds

private def reads (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

private def run (n : Nat) (w : Nat → Bool) (gs : List Gate) : Nat → Bool :=
  match gs with
  | [] => w
  | g :: rest => run (n+1) (Function.update w n (g.op.eval (g.inputs.map w))) rest

private theorem run_getD (gs : List Gate) (w : List Bool) (i : Nat) :
    run w.length (fun j => w.getD j false) gs i =
      (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) w).getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, List.foldl_cons]
    let value := g.op.eval (g.inputs.map fun j => w.getD j false)
    have hw : Function.update (fun j => w.getD j false) w.length value =
        fun j => (w ++ [value]).getD j false := by
      funext j
      by_cases hj : j < w.length
      · rw [Function.update_of_ne (Nat.ne_of_lt hj)]
        rw [List.getD_append]
        simp [hj]
      · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hj) with rfl | hgt
        · simp
        · rw [Function.update_of_ne (Nat.ne_of_gt hgt)]
          have hne : j - w.length ≠ 0 := by omega
          rw [List.getD_append_right _ _ _ _ (Nat.le_of_lt hgt)]
          cases he : j - w.length with
          | zero => exact False.elim (hne he)
          | succ k => simp [List.getElem?_eq_none (by omega : w.length ≤ j)]
    rw [hw]
    simpa only [List.length_append, List.length_singleton, value] using ih (w ++ [value])

private theorem run_rel (R : Bool → Bool → Prop) (gs : List Gate)
    (hs : ∀ g ∈ gs, ∀ a b : Nat → Bool,
      (∀ i ∈ g.inputs, R (a i) (b i)) →
      R (g.op.eval (g.inputs.map a)) (g.op.eval (g.inputs.map b)))
    (n out : Nat) (a b : Nat → Bool)
    (hr : ∀ i, (i = out ∨ i ∈ reads gs) → R (a i) (b i)) :
    R (run n a gs out) (run n b gs out) := by
  induction gs generalizing n a b with
  | nil => exact hr out (Or.inl rfl)
  | cons g gs ih =>
    simp only [run]
    apply ih (fun q hq => hs q (List.mem_cons_of_mem g hq))
    intro i hi
    by_cases h : i = n
    · subst i
      simp only [Function.update_self]
      apply hs g List.mem_cons_self a b
      exact fun j hj => hr j (Or.inr (by simp [reads, hj]))
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact hr i (hi.imp_right fun hm => by simp [reads, reads] at hm ⊢; exact Or.inr hm)

private theorem run_eq (gs : List Gate) (n out : Nat) (a b : Nat → Bool)
    (hr : ∀ i, (i = out ∨ i ∈ reads gs) → a i = b i) :
    run n a gs out = run n b gs out :=
  run_rel Eq gs (fun g _ _ _ h => congrArg g.op.eval (List.map_congr_left h)) n out a b hr

private def binary (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ g.inputs = [a,b]

private theorem run_le (gs : List Gate) (hb : ∀ g ∈ gs, binary g)
    (n out : Nat) (a b : Nat → Bool)
    (hr : ∀ i, (i = out ∨ i ∈ reads gs) → a i ≤ b i) :
    run n a gs out ≤ run n b gs out := by
  apply run_rel (· ≤ ·) gs _ n out a b hr
  intro g hg p q h
  obtain ⟨hop, u, v, _, hin⟩ := hb g hg
  have hu := h u (by simp [hin])
  have hv := h v (by simp [hin])
  rcases hop with ho | ho <;> simp [hin, ho, GateOp.eval]
  · exact (show ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) by decide) _ _ _ _ hu hv
  · exact (show ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) by decide) _ _ _ _ hu hv

private theorem reads_length_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (reads gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [reads]
  | cons g gs ih =>
    have h1 := h g List.mem_cons_self
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem g hq))
    change (g.inputs ++ reads gs).length ≤ 2 * (gs.length + 1)
    rw [List.length_append]
    omega

private theorem reads_saturated (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hs : 2 * gs.length ≤ (reads gs).length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have hh : ∀ q ∈ gs, q.inputs.length ≤ 2 := fun q hq => h q (List.mem_cons_of_mem g hq)
    have hd := reads_length_bound gs hh
    change 2 * (gs.length + 1) ≤ (g.inputs ++ reads gs).length at hs
    rw [List.length_append] at hs
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    · exact ih hh (by omega) q hq


private def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def raw (r : Nat) (i : Fin 9) : Bool := r.testBit i.val

private def augmented (x : Fin 9 → Bool) (i : Nat) : Bool :=
  if hi : i < 9 then x ⟨i, hi⟩ else if i = 9 then (!x 0 || x 4) else false

private def valid (r : Nat) : Bool := r.testBit 9 == (!r.testBit 0 || r.testBit 4)

private def verify (m : Nat) (on : Bool) (w : Nat × Nat × Nat) : Bool :=
  valid w.1 && valid w.2.1 && valid w.2.2 &&
    (matching (raw w.1) == !on) && (matching (raw w.2.1) == on) &&
    (matching (raw w.2.2) == on) &&
    ((m &&& w.1) == (m &&& w.2.1)) &&
    (((1023 ^^^ m) &&& w.1) == ((1023 ^^^ m) &&& w.2.2))

-- The masks put raw wire 0 on the left. Each triple is a bad row followed by two
-- forcing rows that agree with it on the left and right, respectively.
-- Mask 511 leaves only the output of the fixed OR on the right and is handled separately.
set_option maxRecDepth 4096 in
private def certificates : List (Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat)) := [
  (1, (689, 457, 688), (688, 1022, 689)),
  (3, (610, 978, 608), (608, 1020, 610)),
  (5, (596, 996, 593), (592, 1018, 597)),
  (7, (596, 996, 595), (593, 1017, 599)),
  (9, (652, 1016, 644), (644, 1014, 652)),
  (11, (610, 978, 616), (608, 1012, 618)),
  (13, (596, 996, 601), (592, 1010, 605)),
  (15, (596, 996, 603), (593, 1009, 607)),
  (17, (596, 1016, 580), (580, 1006, 597)),
  (19, (596, 1016, 582), (580, 1004, 599)),
  (21, (596, 950, 593), (576, 1002, 597)),
  (23, (596, 948, 595), (578, 1002, 599)),
  (25, (596, 1008, 588), (580, 998, 605)),
  (27, (596, 1008, 590), (582, 998, 607)),
  (29, (596, 950, 601), (576, 994, 605)),
  (31, (596, 948, 603), (578, 994, 607)),
  (33, (610, 1016, 578), (578, 990, 610)),
  (35, (610, 950, 608), (576, 988, 610)),
  (37, (596, 966, 625), (578, 986, 614)),
  (39, (596, 964, 625), (65, 985, 103)),
  (41, (610, 1008, 586), (578, 982, 618)),
  (43, (610, 950, 616), (576, 980, 618)),
  (45, (596, 966, 633), (67, 979, 111)),
  (47, (596, 964, 633), (65, 977, 111)),
  (49, (596, 984, 612), (578, 974, 627)),
  (51, (596, 984, 612), (576, 972, 627)),
  (53, (596, 918, 625), (576, 970, 629)),
  (55, (596, 916, 625), (578, 970, 631)),
  (57, (596, 978, 620), (586, 974, 635)),
  (59, (596, 976, 620), (584, 972, 635)),
  (61, (596, 918, 633), (584, 970, 637)),
  (63, (596, 916, 633), (586, 970, 639)),
  (65, (596, 1016, 533), (532, 958, 597)),
  (67, (596, 1016, 535), (532, 956, 599)),
  (69, (596, 996, 593), (528, 954, 597)),
  (71, (596, 996, 595), (529, 953, 599)),
  (73, (596, 1008, 541), (533, 951, 605)),
  (75, (596, 1008, 543), (533, 949, 607)),
  (77, (596, 996, 601), (529, 947, 605)),
  (79, (596, 996, 603), (529, 945, 607)),
  (81, (596, 1016, 580), (516, 942, 597)),
  (83, (596, 1016, 582), (516, 940, 599)),
  (85, (610, 1000, 567), (512, 938, 597)),
  (87, (610, 962, 625), (514, 938, 599)),
  (89, (596, 1008, 588), (524, 942, 605)),
  (91, (596, 1008, 590), (524, 940, 607)),
  (93, (610, 992, 575), (520, 938, 605)),
  (95, (610, 962, 633), (522, 938, 607)),
  (97, (596, 984, 565), (514, 926, 610)),
  (99, (596, 984, 567), (512, 924, 610)),
  (101, (596, 966, 625), (514, 922, 614)),
  (103, (596, 964, 625), (1, 921, 103)),
  (105, (596, 978, 573), (3, 919, 107)),
  (107, (596, 976, 575), (1, 917, 107)),
  (109, (596, 966, 633), (3, 915, 111)),
  (111, (596, 964, 633), (1, 913, 111)),
  (113, (596, 984, 612), (514, 910, 627)),
  (115, (596, 984, 612), (512, 908, 627)),
  (117, (610, 1000, 595), (512, 906, 629)),
  (119, (652, 900, 760), (514, 906, 631)),
  (121, (596, 978, 620), (522, 910, 635)),
  (123, (596, 976, 620), (520, 908, 635)),
  (125, (610, 992, 603), (520, 906, 637)),
  (127, (652, 780, 760), (522, 906, 639)),
  (129, (652, 1016, 524), (524, 894, 652)),
  (131, (610, 850, 736), (524, 892, 654)),
  (133, (596, 876, 721), (520, 890, 652)),
  (135, (596, 876, 723), (9, 889, 143)),
  (137, (652, 1016, 644), (516, 886, 652)),
  (139, (610, 850, 744), (516, 884, 654)),
  (141, (596, 868, 729), (512, 882, 652)),
  (143, (596, 868, 731), (1, 881, 143)),
  (145, (596, 888, 708), (524, 878, 669)),
  (147, (596, 888, 710), (526, 878, 671)),
  (149, (596, 828, 721), (520, 874, 669)),
  (151, (596, 828, 723), (522, 874, 671)),
  (153, (596, 880, 708), (516, 870, 669)),
  (155, (596, 880, 710), (518, 870, 671)),
  (157, (596, 822, 729), (512, 866, 669)),
  (159, (596, 820, 731), (514, 866, 671)),
  (161, (610, 888, 706), (1, 863, 161)),
  (163, (610, 822, 736), (1, 861, 163)),
  (165, (596, 844, 752), (1, 859, 165)),
  (167, (596, 844, 752), (1, 857, 167)),
  (169, (610, 880, 714), (1, 855, 169)),
  (171, (610, 822, 744), (1, 853, 171)),
  (173, (596, 838, 760), (1, 851, 173)),
  (175, (596, 836, 760), (1, 849, 175)),
  (177, (596, 856, 740), (512, 846, 689)),
  (179, (596, 856, 740), (514, 846, 691)),
  (181, (596, 796, 752), (512, 842, 693)),
  (183, (596, 796, 752), (514, 842, 695)),
  (185, (596, 850, 740), (520, 846, 697)),
  (187, (596, 848, 740), (522, 846, 699)),
  (189, (596, 790, 760), (520, 842, 701)),
  (191, (596, 788, 760), (522, 842, 703)),
  (193, (596, 888, 661), (524, 830, 716)),
  (195, (596, 888, 663), (13, 829, 207)),
  (197, (596, 876, 721), (520, 826, 716)),
  (199, (596, 876, 723), (9, 825, 207)),
  (201, (596, 880, 661), (5, 823, 205)),
  (203, (596, 880, 663), (5, 821, 207)),
  (205, (596, 868, 729), (1, 819, 205)),
  (207, (596, 868, 731), (1, 817, 207)),
  (209, (596, 888, 708), (516, 814, 725)),
  (211, (596, 888, 710), (518, 814, 727)),
  (213, (610, 872, 694), (512, 810, 725)),
  (215, (610, 834, 752), (514, 810, 727)),
  (217, (596, 880, 708), (524, 814, 733)),
  (219, (596, 880, 710), (526, 814, 735)),
  (221, (610, 864, 698), (520, 810, 733)),
  (223, (610, 834, 760), (522, 810, 735)),
  (225, (596, 856, 692), (1, 799, 225)),
  (227, (596, 856, 694), (1, 797, 227)),
  (229, (596, 844, 752), (1, 795, 229)),
  (231, (596, 844, 752), (1, 793, 231)),
  (233, (596, 850, 692), (1, 791, 233)),
  (235, (596, 848, 694), (1, 789, 235)),
  (237, (596, 838, 760), (1, 787, 237)),
  (239, (596, 836, 760), (1, 785, 239)),
  (241, (596, 856, 740), (512, 782, 753)),
  (243, (596, 856, 740), (514, 782, 755)),
  (245, (610, 872, 723), (512, 778, 757)),
  (247, (652, 900, 760), (514, 778, 759)),
  (249, (596, 850, 740), (520, 782, 761)),
  (251, (596, 848, 740), (522, 782, 763)),
  (253, (610, 864, 731), (520, 778, 765)),
  (255, (778, 522, 1016), (522, 778, 767)),
  (257, (689, 731, 944), (522, 766, 778)),
  (259, (610, 730, 864), (520, 764, 778)),
  (261, (596, 740, 848), (522, 762, 782)),
  (263, (596, 740, 850), (9, 761, 271)),
  (265, (652, 760, 900), (514, 758, 778)),
  (267, (610, 722, 872), (512, 756, 778)),
  (269, (596, 740, 856), (514, 754, 782)),
  (271, (596, 740, 856), (1, 753, 271)),
  (273, (596, 760, 836), (512, 750, 785)),
  (275, (596, 760, 838), (512, 748, 787)),
  (277, (596, 694, 848), (512, 746, 789)),
  (279, (596, 692, 850), (514, 746, 791)),
  (281, (596, 752, 844), (512, 742, 793)),
  (283, (596, 752, 844), (1, 229, 267)),
  (285, (596, 694, 856), (512, 738, 797)),
  (287, (596, 692, 856), (1, 225, 271)),
  (289, (610, 760, 834), (522, 734, 810)),
  (291, (610, 698, 864), (520, 732, 810)),
  (293, (596, 710, 880), (526, 734, 814)),
  (295, (596, 708, 880), (524, 732, 814)),
  (297, (610, 752, 834), (514, 726, 810)),
  (299, (610, 694, 872), (512, 724, 810)),
  (301, (596, 710, 888), (518, 726, 814)),
  (303, (596, 708, 888), (516, 724, 814)),
  (305, (596, 730, 868), (512, 718, 817)),
  (307, (596, 728, 868), (512, 716, 819)),
  (309, (596, 662, 880), (516, 718, 821)),
  (311, (596, 660, 880), (516, 716, 823)),
  (313, (596, 722, 876), (520, 718, 825)),
  (315, (596, 720, 876), (520, 716, 827)),
  (317, (596, 662, 888), (524, 718, 829)),
  (319, (596, 660, 888), (524, 716, 831)),
  (321, (596, 760, 788), (522, 702, 842)),
  (323, (596, 760, 790), (520, 700, 842)),
  (325, (596, 740, 848), (11, 699, 335)),
  (327, (596, 740, 850), (9, 697, 335)),
  (329, (596, 752, 796), (3, 695, 331)),
  (331, (596, 752, 796), (1, 693, 331)),
  (333, (596, 740, 856), (3, 691, 335)),
  (335, (596, 740, 856), (1, 689, 335)),
  (337, (596, 760, 836), (512, 686, 849)),
  (339, (596, 760, 838), (512, 684, 851)),
  (341, (610, 744, 822), (516, 686, 853)),
  (343, (610, 714, 880), (516, 684, 855)),
  (345, (596, 752, 844), (3, 167, 331)),
  (347, (596, 752, 844), (1, 165, 331)),
  (349, (610, 736, 822), (3, 163, 335)),
  (351, (610, 706, 888), (1, 161, 335)),
  (353, (596, 730, 820), (514, 670, 866)),
  (355, (596, 728, 822), (512, 668, 866)),
  (357, (596, 710, 880), (518, 670, 870)),
  (359, (596, 708, 880), (516, 668, 870)),
  (361, (596, 722, 828), (522, 670, 874)),
  (363, (596, 720, 828), (520, 668, 874)),
  (365, (596, 710, 888), (526, 670, 878)),
  (367, (596, 708, 888), (524, 668, 878)),
  (369, (596, 730, 868), (512, 654, 881)),
  (371, (596, 728, 868), (512, 652, 883)),
  (373, (610, 744, 850), (516, 654, 885)),
  (375, (652, 644, 1016), (516, 652, 887)),
  (377, (596, 722, 876), (520, 654, 889)),
  (379, (596, 720, 876), (520, 652, 891)),
  (381, (610, 736, 850), (524, 654, 893)),
  (383, (652, 524, 1016), (524, 652, 895)),
  (385, (652, 760, 780), (522, 638, 906)),
  (387, (610, 602, 992), (520, 636, 906)),
  (389, (596, 620, 976), (520, 634, 908)),
  (391, (596, 620, 978), (522, 634, 910)),
  (393, (652, 760, 900), (514, 630, 906)),
  (395, (610, 594, 1000), (512, 628, 906)),
  (397, (596, 612, 984), (512, 626, 908)),
  (399, (596, 612, 984), (514, 626, 910)),
  (401, (596, 632, 964), (512, 622, 913)),
  (403, (596, 632, 966), (514, 622, 915)),
  (405, (596, 574, 976), (512, 618, 917)),
  (407, (596, 572, 978), (514, 618, 919)),
  (409, (596, 624, 964), (512, 614, 921)),
  (411, (596, 624, 966), (514, 614, 923)),
  (413, (596, 566, 984), (512, 610, 925)),
  (415, (596, 564, 984), (514, 610, 927)),
  (417, (610, 632, 962), (1, 607, 417)),
  (419, (610, 574, 992), (1, 605, 419)),
  (421, (596, 590, 1008), (5, 607, 421)),
  (423, (596, 588, 1008), (5, 605, 423)),
  (425, (610, 624, 962), (1, 599, 425)),
  (427, (610, 566, 1000), (512, 596, 938)),
  (429, (596, 582, 1016), (516, 598, 940)),
  (431, (596, 580, 1016), (516, 596, 942)),
  (433, (596, 602, 996), (528, 606, 945)),
  (435, (596, 600, 996), (528, 604, 947)),
  (437, (596, 542, 1008), (532, 606, 949)),
  (439, (596, 540, 1008), (532, 604, 951)),
  (441, (596, 594, 996), (528, 598, 953)),
  (443, (596, 592, 996), (528, 596, 955)),
  (445, (596, 534, 1016), (532, 598, 957)),
  (447, (596, 532, 1016), (532, 596, 959)),
  (449, (596, 632, 916), (586, 638, 970)),
  (451, (596, 632, 918), (584, 636, 970)),
  (453, (596, 620, 976), (584, 634, 972)),
  (455, (596, 620, 978), (586, 634, 974)),
  (457, (596, 624, 916), (578, 630, 970)),
  (459, (596, 624, 918), (576, 628, 970)),
  (461, (596, 612, 984), (576, 626, 972)),
  (463, (596, 612, 984), (578, 626, 974)),
  (465, (596, 632, 964), (576, 622, 977)),
  (467, (596, 632, 966), (578, 622, 979)),
  (469, (610, 616, 950), (576, 618, 981)),
  (471, (610, 586, 1008), (578, 618, 983)),
  (473, (596, 624, 964), (576, 614, 985)),
  (475, (596, 624, 966), (578, 614, 987)),
  (477, (610, 608, 950), (576, 610, 989)),
  (479, (610, 578, 1016), (578, 610, 991)),
  (481, (596, 602, 948), (65, 607, 481)),
  (483, (596, 600, 950), (576, 604, 994)),
  (485, (596, 590, 1008), (69, 607, 485)),
  (487, (596, 588, 1008), (580, 604, 998)),
  (489, (596, 594, 948), (65, 599, 489)),
  (491, (596, 592, 950), (576, 596, 1002)),
  (493, (596, 582, 1016), (580, 598, 1004)),
  (495, (596, 580, 1016), (580, 596, 1006)),
  (497, (596, 602, 996), (592, 606, 1009)),
  (499, (596, 600, 996), (592, 604, 1011)),
  (501, (610, 616, 978), (608, 618, 1013)),
  (503, (652, 644, 1016), (644, 652, 1015)),
  (505, (596, 594, 996), (592, 598, 1017)),
  (507, (596, 592, 996), (592, 596, 1019)),
  (509, (610, 608, 978), (608, 610, 1021)),
  (513, (161, 457, 672), (672, 1022, 161)),
  (515, (610, 978, 97), (608, 1020, 99)),
  (517, (596, 996, 593), (592, 1018, 597)),
  (519, (596, 996, 595), (593, 1017, 599)),
  (521, (652, 1016, 133), (644, 1014, 141)),
  (523, (610, 978, 105), (608, 1012, 107)),
  (525, (596, 996, 601), (592, 1010, 605)),
  (527, (596, 996, 603), (593, 1009, 607)),
  (529, (596, 1016, 69), (580, 1006, 597)),
  (531, (596, 1016, 71), (580, 1004, 599)),
  (533, (596, 950, 593), (576, 1002, 597)),
  (535, (596, 948, 595), (65, 489, 599)),
  (537, (596, 1008, 77), (580, 998, 605)),
  (539, (596, 1008, 79), (69, 485, 607)),
  (541, (596, 950, 601), (576, 994, 605)),
  (543, (596, 948, 603), (65, 481, 607)),
  (545, (610, 1016, 67), (578, 990, 99)),
  (547, (610, 950, 97), (576, 988, 99)),
  (549, (596, 966, 625), (578, 986, 103)),
  (551, (596, 964, 625), (578, 986, 103)),
  (553, (610, 1008, 75), (578, 982, 107)),
  (555, (610, 950, 105), (576, 980, 107)),
  (557, (596, 966, 633), (582, 982, 111)),
  (559, (596, 964, 633), (580, 980, 111)),
  (561, (596, 984, 101), (578, 974, 627)),
  (563, (596, 984, 101), (576, 972, 627)),
  (565, (596, 918, 625), (576, 970, 629)),
  (567, (596, 916, 625), (578, 970, 631)),
  (569, (596, 978, 109), (586, 974, 635)),
  (571, (596, 976, 109), (584, 972, 635)),
  (573, (596, 918, 633), (584, 970, 637)),
  (575, (596, 916, 633), (586, 970, 639)),
  (577, (596, 1016, 533), (532, 958, 597)),
  (579, (596, 1016, 535), (532, 956, 599)),
  (581, (596, 996, 593), (528, 954, 597)),
  (583, (596, 996, 595), (529, 953, 599)),
  (585, (596, 1008, 541), (533, 951, 605)),
  (587, (596, 1008, 543), (533, 949, 607)),
  (589, (596, 996, 601), (529, 947, 605)),
  (591, (596, 996, 603), (529, 945, 607)),
  (593, (596, 1016, 69), (516, 942, 597)),
  (595, (596, 1016, 71), (516, 940, 599)),
  (597, (610, 1000, 567), (512, 938, 597)),
  (599, (610, 962, 625), (1, 425, 599)),
  (601, (596, 1008, 77), (5, 423, 605)),
  (603, (596, 1008, 79), (5, 421, 607)),
  (605, (610, 992, 575), (1, 419, 605)),
  (607, (610, 962, 633), (1, 417, 607)),
  (609, (596, 984, 565), (514, 926, 99)),
  (611, (596, 984, 567), (512, 924, 99)),
  (613, (596, 966, 625), (514, 922, 103)),
  (615, (596, 964, 625), (514, 922, 103)),
  (617, (596, 978, 573), (522, 926, 107)),
  (619, (596, 976, 575), (520, 924, 107)),
  (621, (596, 966, 633), (522, 922, 111)),
  (623, (596, 964, 633), (522, 922, 111)),
  (625, (596, 984, 101), (514, 910, 627)),
  (627, (596, 984, 101), (512, 908, 627)),
  (629, (610, 1000, 595), (512, 906, 629)),
  (631, (652, 900, 760), (514, 906, 631)),
  (633, (596, 978, 109), (522, 910, 635)),
  (635, (596, 976, 109), (520, 908, 635)),
  (637, (610, 992, 603), (520, 906, 637)),
  (639, (652, 780, 760), (522, 906, 639)),
  (641, (652, 1016, 13), (524, 894, 141)),
  (643, (610, 850, 736), (524, 892, 143)),
  (645, (596, 876, 721), (520, 890, 141)),
  (647, (596, 876, 723), (522, 890, 143)),
  (649, (652, 1016, 133), (516, 886, 141)),
  (651, (610, 850, 744), (516, 884, 143)),
  (653, (596, 868, 729), (512, 882, 141)),
  (655, (596, 868, 731), (514, 882, 143)),
  (657, (596, 888, 197), (524, 878, 669)),
  (659, (596, 888, 199), (526, 878, 671)),
  (661, (596, 828, 721), (520, 874, 669)),
  (663, (596, 828, 723), (522, 874, 671)),
  (665, (596, 880, 197), (516, 870, 669)),
  (667, (596, 880, 199), (518, 870, 671)),
  (669, (596, 822, 729), (512, 866, 669)),
  (671, (596, 820, 731), (514, 866, 671)),
  (673, (610, 888, 195), (512, 862, 161)),
  (675, (610, 822, 736), (512, 860, 163)),
  (677, (596, 844, 752), (512, 858, 165)),
  (679, (596, 844, 752), (514, 858, 167)),
  (681, (610, 880, 203), (512, 854, 169)),
  (683, (610, 822, 744), (512, 852, 171)),
  (685, (596, 838, 760), (516, 854, 173)),
  (687, (596, 836, 760), (516, 852, 175)),
  (689, (596, 856, 740), (512, 846, 689)),
  (691, (596, 856, 740), (514, 846, 691)),
  (693, (596, 796, 752), (512, 842, 693)),
  (695, (596, 796, 752), (514, 842, 695)),
  (697, (596, 850, 740), (520, 846, 697)),
  (699, (596, 848, 740), (522, 846, 699)),
  (701, (596, 790, 760), (520, 842, 701)),
  (703, (596, 788, 760), (522, 842, 703)),
  (705, (596, 888, 661), (524, 830, 205)),
  (707, (596, 888, 663), (526, 830, 207)),
  (709, (596, 876, 721), (520, 826, 205)),
  (711, (596, 876, 723), (522, 826, 207)),
  (713, (596, 880, 661), (524, 830, 205)),
  (715, (596, 880, 663), (526, 830, 207)),
  (717, (596, 868, 729), (520, 826, 205)),
  (719, (596, 868, 731), (522, 826, 207)),
  (721, (596, 888, 197), (516, 814, 725)),
  (723, (596, 888, 199), (518, 814, 727)),
  (725, (610, 872, 694), (512, 810, 725)),
  (727, (610, 834, 752), (514, 810, 727)),
  (729, (596, 880, 197), (524, 814, 733)),
  (731, (596, 880, 199), (526, 814, 735)),
  (733, (610, 864, 698), (520, 810, 733)),
  (735, (610, 834, 760), (522, 810, 735)),
  (737, (596, 856, 692), (512, 798, 225)),
  (739, (596, 856, 694), (514, 798, 227)),
  (741, (596, 844, 752), (512, 794, 229)),
  (743, (596, 844, 752), (514, 794, 231)),
  (745, (596, 850, 692), (520, 798, 233)),
  (747, (596, 848, 694), (522, 798, 235)),
  (749, (596, 838, 760), (520, 794, 237)),
  (751, (596, 836, 760), (522, 794, 239)),
  (753, (596, 856, 740), (512, 782, 753)),
  (755, (596, 856, 740), (514, 782, 755)),
  (757, (610, 872, 723), (512, 778, 757)),
  (759, (652, 900, 760), (514, 778, 759)),
  (761, (596, 850, 740), (520, 782, 761)),
  (763, (596, 848, 740), (522, 782, 763)),
  (765, (610, 864, 731), (520, 778, 765)),
  (767, (778, 522, 1016), (522, 778, 767)),
  (769, (161, 203, 928), (522, 766, 267)),
  (771, (610, 730, 353), (520, 764, 267)),
  (773, (596, 740, 848), (522, 762, 271)),
  (775, (596, 740, 850), (9, 233, 271)),
  (777, (652, 760, 389), (514, 758, 267)),
  (779, (610, 722, 361), (512, 756, 267)),
  (781, (596, 740, 856), (514, 754, 271)),
  (783, (596, 740, 856), (1, 225, 271)),
  (785, (596, 760, 325), (512, 750, 785)),
  (787, (596, 760, 327), (512, 748, 787)),
  (789, (596, 694, 848), (512, 746, 789)),
  (791, (596, 692, 850), (1, 233, 791)),
  (793, (596, 752, 333), (512, 742, 793)),
  (795, (596, 752, 333), (1, 229, 795)),
  (797, (596, 694, 856), (512, 738, 797)),
  (799, (596, 692, 856), (1, 225, 799)),
  (801, (610, 760, 323), (522, 734, 299)),
  (803, (610, 698, 353), (520, 732, 299)),
  (805, (596, 710, 880), (526, 734, 303)),
  (807, (596, 708, 880), (524, 732, 303)),
  (809, (610, 752, 323), (514, 726, 299)),
  (811, (610, 694, 361), (512, 724, 299)),
  (813, (596, 710, 888), (518, 726, 303)),
  (815, (596, 708, 888), (516, 724, 303)),
  (817, (596, 730, 357), (512, 718, 817)),
  (819, (596, 728, 357), (512, 716, 819)),
  (821, (596, 662, 880), (516, 718, 821)),
  (823, (596, 660, 880), (516, 716, 823)),
  (825, (596, 722, 365), (520, 718, 825)),
  (827, (596, 720, 365), (520, 716, 827)),
  (829, (596, 662, 888), (524, 718, 829)),
  (831, (596, 660, 888), (524, 716, 831)),
  (833, (596, 760, 788), (522, 702, 331)),
  (835, (596, 760, 790), (520, 700, 331)),
  (837, (596, 740, 848), (11, 171, 335)),
  (839, (596, 740, 850), (9, 169, 335)),
  (841, (596, 752, 796), (3, 167, 331)),
  (843, (596, 752, 796), (1, 165, 331)),
  (845, (596, 740, 856), (3, 163, 335)),
  (847, (596, 740, 856), (1, 161, 335)),
  (849, (596, 760, 325), (512, 686, 849)),
  (851, (596, 760, 327), (512, 684, 851)),
  (853, (610, 744, 822), (1, 171, 853)),
  (855, (610, 714, 880), (1, 169, 855)),
  (857, (596, 752, 333), (1, 167, 857)),
  (859, (596, 752, 333), (1, 165, 859)),
  (861, (610, 736, 822), (1, 163, 861)),
  (863, (610, 706, 888), (1, 161, 863)),
  (865, (596, 730, 820), (514, 670, 355)),
  (867, (596, 728, 822), (512, 668, 355)),
  (869, (596, 710, 880), (518, 670, 359)),
  (871, (596, 708, 880), (516, 668, 359)),
  (873, (596, 722, 828), (522, 670, 363)),
  (875, (596, 720, 828), (520, 668, 363)),
  (877, (596, 710, 888), (526, 670, 367)),
  (879, (596, 708, 888), (524, 668, 367)),
  (881, (596, 730, 357), (512, 654, 881)),
  (883, (596, 728, 357), (512, 652, 883)),
  (885, (610, 744, 850), (516, 654, 885)),
  (887, (652, 644, 1016), (516, 652, 887)),
  (889, (596, 722, 365), (520, 654, 889)),
  (891, (596, 720, 365), (520, 652, 891)),
  (893, (610, 736, 850), (524, 654, 893)),
  (895, (652, 524, 1016), (524, 652, 895)),
  (897, (652, 760, 269), (522, 638, 395)),
  (899, (610, 602, 992), (520, 636, 395)),
  (901, (596, 620, 976), (520, 634, 397)),
  (903, (596, 620, 978), (522, 634, 399)),
  (905, (652, 760, 389), (514, 630, 395)),
  (907, (610, 594, 1000), (512, 628, 395)),
  (909, (596, 612, 984), (512, 626, 397)),
  (911, (596, 612, 984), (514, 626, 399)),
  (913, (596, 632, 453), (512, 622, 913)),
  (915, (596, 632, 455), (514, 622, 915)),
  (917, (596, 574, 976), (512, 618, 917)),
  (919, (596, 572, 978), (514, 618, 919)),
  (921, (596, 624, 453), (512, 614, 921)),
  (923, (596, 624, 455), (514, 614, 923)),
  (925, (596, 566, 984), (512, 610, 925)),
  (927, (596, 564, 984), (514, 610, 927)),
  (929, (610, 632, 451), (512, 606, 417)),
  (931, (610, 574, 992), (512, 604, 419)),
  (933, (596, 590, 1008), (516, 606, 421)),
  (935, (596, 588, 1008), (516, 604, 423)),
  (937, (610, 624, 451), (512, 598, 425)),
  (939, (610, 566, 1000), (512, 596, 427)),
  (941, (596, 582, 1016), (516, 598, 429)),
  (943, (596, 580, 1016), (516, 596, 431)),
  (945, (596, 602, 996), (528, 606, 945)),
  (947, (596, 600, 996), (528, 604, 947)),
  (949, (596, 542, 1008), (532, 606, 949)),
  (951, (596, 540, 1008), (532, 604, 951)),
  (953, (596, 594, 996), (528, 598, 953)),
  (955, (596, 592, 996), (528, 596, 955)),
  (957, (596, 534, 1016), (532, 598, 957)),
  (959, (596, 532, 1016), (532, 596, 959)),
  (961, (596, 632, 916), (586, 638, 459)),
  (963, (596, 632, 918), (584, 636, 459)),
  (965, (596, 620, 976), (584, 634, 461)),
  (967, (596, 620, 978), (586, 634, 463)),
  (969, (596, 624, 916), (578, 630, 459)),
  (971, (596, 624, 918), (576, 628, 459)),
  (973, (596, 612, 984), (576, 626, 461)),
  (975, (596, 612, 984), (578, 626, 463)),
  (977, (596, 632, 453), (576, 622, 977)),
  (979, (596, 632, 455), (578, 622, 979)),
  (981, (610, 616, 950), (576, 618, 981)),
  (983, (610, 586, 1008), (578, 618, 983)),
  (985, (596, 624, 453), (576, 614, 985)),
  (987, (596, 624, 455), (578, 614, 987)),
  (989, (610, 608, 950), (576, 610, 989)),
  (991, (610, 578, 1016), (578, 610, 991)),
  (993, (596, 602, 948), (576, 606, 481)),
  (995, (596, 600, 950), (576, 604, 483)),
  (997, (596, 590, 1008), (580, 606, 485)),
  (999, (596, 588, 1008), (580, 604, 487)),
  (1001, (596, 594, 948), (576, 598, 489)),
  (1003, (596, 592, 950), (576, 596, 491)),
  (1005, (596, 582, 1016), (580, 598, 493)),
  (1007, (596, 580, 1016), (580, 596, 495)),
  (1009, (596, 602, 996), (592, 606, 1009)),
  (1011, (596, 600, 996), (592, 604, 1011)),
  (1013, (610, 616, 978), (608, 618, 1013)),
  (1015, (652, 644, 1016), (644, 652, 1015)),
  (1017, (596, 594, 996), (592, 598, 1017)),
  (1019, (596, 592, 996), (592, 596, 1019)),
  (1021, (610, 608, 978), (608, 610, 1021))
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem certificates_valid :
    (certificates.all (fun ⟨m, o, a⟩ => verify m false o && verify m true a)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem certificate_masks :
    certificates.map Prod.fst = ((List.range 511).map (fun i => 2*i+1)).erase 511 := by
  decide +kernel

private theorem valid_bit {r : Nat} (h : valid r = true) :
    r.testBit 9 = (!r.testBit 0 || r.testBit 4) := by
  simpa [valid] using h

private theorem augmented_raw {r i : Nat} (hr : valid r = true) (hi : i < 10) :
    augmented (raw r) i = r.testBit i := by
  by_cases h : i < 9
  · simp [augmented, raw, h]
  · have eq : i = 9 := by omega
    subst i
    simpa [augmented, raw] using (valid_bit hr).symm

private theorem agree_of_and_eq {m x y : Nat} (hx : valid x = true) (hy : valid y = true)
    (he : m &&& x = m &&& y) {i : Nat} (hi : i < 10) (hm : m.testBit i = true) :
    augmented (raw x) i = augmented (raw y) i := by
  rw [augmented_raw hx hi, augmented_raw hy hi]
  simpa [hm] using congrArg (fun n : Nat => n.testBit i) he

private def depends (m : Nat) (f : (Fin 9 → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, i < 10 → m.testBit i = true → augmented x i = augmented y i) → f x = f y

private theorem no_general_split {m : Nat} (hm : m < 1023)
    (hodd : m % 2 = 1) (hy : m ≠ 511)
    {f g : (Fin 9 → Bool) → Bool} (hf : depends m f) (hg : depends (1023 ^^^ m) g)
    (on : Bool) :
    ¬ ∀ x, matching x = (if on then f x && g x else f x || g x) := by
  intro h
  have hm_mem : m ∈ certificates.map Prod.fst := by
    rw [certificate_masks, List.mem_erase_of_ne hy, List.mem_map]
    exact ⟨m / 2, List.mem_range.mpr (by omega), by omega⟩
  obtain ⟨⟨m', o, a⟩, hmem, heq⟩ := List.mem_map.mp hm_mem
  change m' = m at heq
  subst m'
  have hv := List.all_eq_true.mp certificates_valid (m, o, a) hmem
  have obs : ∃ w, verify m on w = true := by
    cases on
    · exact ⟨o, (Bool.and_eq_true_iff.mp hv).1⟩
    · exact ⟨a, (Bool.and_eq_true_iff.mp hv).2⟩
  obtain ⟨⟨bad, left, right⟩, hw⟩ := obs
  simp only [verify, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hl⟩, hr⟩, hbad⟩, hleft⟩, hright⟩, hal⟩, har⟩ := hw
  have hfl := hf (raw bad) (raw left) (fun _ hi hb' => agree_of_and_eq hb hl hal hi hb')
  have hgr := hg (raw bad) (raw right) (fun _ hi hb' => agree_of_and_eq hb hr har hi hb')
  have e0 := h (raw bad)
  have e1 := h (raw left)
  have e2 := h (raw right)
  rw [hbad] at e0
  rw [hleft] at e1
  rw [hright] at e2
  rw [← hfl] at e1
  rw [← hgr] at e2
  cases on <;> simp at e0 e1 e2 <;> simp [e1.1, e2.2] at e0


private def Comb (on a b : Bool) : Bool := if on then a && b else a || b

private theorem comb_cases (g : Gate) (hb : binary g) :
    ∃ on a b, a < b ∧ g.inputs = [a,b] ∧
      ∀ w : Nat → Bool, g.op.eval (g.inputs.map w) = Comb on (w a) (w b) := by
  obtain ⟨hop, a, b, hab, hin⟩ := hb
  rcases hop with hop | hop
  · exact ⟨true, a, b, hab, hin, fun _ => by simp [Comb, hin, hop, GateOp.eval]⟩
  · exact ⟨false, a, b, hab, hin, fun _ => by simp [Comb, hin, hop, GateOp.eval]⟩

private def Support (s : Finset Nat) (f : (Fin 9 → Bool) → Bool) : Prop :=
  s.Nonempty ∧ (∀ i ∈ s, i < 10) ∧
    (∀ x y, (∀ i ∈ s, augmented x i = augmented y i) → f x = f y) ∧
    ∀ x b, (∀ i ∈ s, augmented x i = b) → f x = b

private theorem Support.nonempty {s f} (h : Support s f) : s.Nonempty := h.1

private theorem Support.bound {s f} (h : Support s f) : ∀ i ∈ s, i < 10 := h.2.1

private theorem Support.ag {s f} (h : Support s f) :
    ∀ x y, (∀ i ∈ s, augmented x i = augmented y i) → f x = f y :=
  h.2.2.1

private theorem Support.uniform {s f} (h : Support s f) :
    ∀ x b, (∀ i ∈ s, augmented x i = b) → f x = b :=
  h.2.2.2

private theorem merge_support {s t : Finset Nat} {f g : (Fin 9 → Bool) → Bool}
    (hs : Support s f) (ht : Support t g) (on : Bool) :
    Support (s ∪ t) (fun x => Comb on (f x) (g x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hs.nonempty.mono Finset.subset_union_left
  · intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact hs.bound i h
    · exact ht.bound i h
  · intro x y h
    change Comb on (f x) (g x) = Comb on (f y) (g y)
    rw [hs.ag x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      ht.ag x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · intro x b h
    change Comb on (f x) (g x) = b
    rw [hs.uniform x b (fun i hi => h i (Finset.mem_union_left _ hi)),
      ht.uniform x b (fun i hi => h i (Finset.mem_union_right _ hi))]
    cases on <;> simp [Comb]

private def Earlier (n : Nat) (gs : List Gate) : Prop :=
  ∀ (j : Nat) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

-- Among already constructed wires that a later gate will read, the supports
-- are disjoint. Each step consumes two such wires and introduces their union.
private theorem find_root (gs : List Gate) (hn : gs ≠ [])
    (hb : ∀ g ∈ gs, binary g) (hd : (reads gs).Nodup)
    (n : Nat) (he : Earlier n gs) (w : (Fin 9 → Bool) → Nat → Bool)
    (parts : Nat → Finset Nat)
    (hp : ∀ i ∈ reads gs, i < n → Support (parts i) (fun x => w x i))
    (hdis : ∀ i ∈ reads gs, ∀ j ∈ reads gs, i < n → j < n → i ≠ j →
      Disjoint (parts i) (parts j)) :
    ∃ (on : Bool) (s t : Finset Nat) (f g : (Fin 9 → Bool) → Bool),
      Support s f ∧ Support t g ∧ Disjoint s t ∧
      ∀ x, run n (w x) gs (n + gs.length - 1) = Comb on (f x) (g x) := by
  induction gs generalizing n w parts with
  | nil => exact False.elim (hn rfl)
  | cons g gs ih =>
    obtain ⟨on, a, b, hab, hinputs, hg⟩ := comb_cases g (hb g List.mem_cons_self)
    have ha : a ∈ reads (g :: gs) := by simp [reads, hinputs]
    have hbr : b ∈ reads (g :: gs) := by simp [reads, hinputs]
    have ha' : a < n := by simpa using he 0 (by simp) a (by simp [hinputs])
    have hb' : b < n := by simpa using he 0 (by simp) b (by simp [hinputs])
    have rootdis := hdis a ha b hbr ha' hb' (Nat.ne_of_lt hab)
    have asup := hp a ha ha'
    have bsup := hp b hbr hb'
    by_cases hg0 : gs = []
    · subst gs
      refine ⟨on, parts a, parts b, fun x => w x a, fun x => w x b,
        asup, bsup, rootdis, ?_⟩
      intro x
      simpa [run] using hg (w x)
    have hd' : (a :: b :: reads gs).Nodup := by
      simpa [reads, hinputs] using hd
    have haa : a ∉ reads gs := fun h => (List.nodup_cons.mp hd').1 (by simp [h])
    have hbb : b ∉ reads gs := (List.nodup_cons.mp (List.nodup_cons.mp hd').2).1
    have rest_mem : ∀ i ∈ reads gs, i ∈ reads (g :: gs) := by
      intro i hi
      simp only [reads, List.flatMap_cons, List.mem_append]
      exact Or.inr hi
    let w' := fun x => Function.update (w x) n (g.op.eval (g.inputs.map (w x)))
    let parts' := Function.update parts n (parts a ∪ parts b)
    have hpn : ∀ i ∈ reads gs, i < n+1 → Support (parts' i) (fun x => w' x i) := by
      intro i hi hi'
      by_cases hen : i = n
      · subst i
        simp only [parts', w', Function.update_self, hg]
        exact merge_support asup bsup on
      · simp only [parts', w', Function.update_of_ne hen]
        exact hp i (rest_mem i hi) (by omega)
    have prior : ∀ i ∈ reads gs, i < n → Disjoint (parts a ∪ parts b) (parts i) := by
      intro i hi hin
      have hia : a ≠ i := fun e => haa (e ▸ hi)
      have hib : b ≠ i := fun e => hbb (e ▸ hi)
      exact Finset.disjoint_union_left.mpr
        ⟨hdis a ha i (rest_mem i hi) ha' hin hia, hdis b hbr i (rest_mem i hi) hb' hin hib⟩
    have hdn : ∀ i ∈ reads gs, ∀ j ∈ reads gs, i < n+1 → j < n+1 → i ≠ j →
        Disjoint (parts' i) (parts' j) := by
      intro i hi j hj il jl ij
      by_cases ein : i = n
      · subst i
        have ejn : j ≠ n := Ne.symm ij
        simpa [parts', Function.update_of_ne ejn] using prior j hj (by omega)
      · by_cases ejn : j = n
        · subst j
          simpa [parts', Function.update_of_ne ein] using (prior i hi (by omega)).symm
        · simp only [parts', Function.update_of_ne ein, Function.update_of_ne ejn]
          exact hdis i (rest_mem i hi) j (rest_mem j hj) (by omega) (by omega) ij
    have hen : Earlier (n+1) gs := by
      intro j hj i hi
      have hh := he (j+1) (by simpa using hj) i hi
      omega
    obtain ⟨r, s, t, f, k, hsf, htk, hst, hval⟩ :=
      ih hg0 (fun q hq => hb q (List.mem_cons_of_mem g hq))
        (List.nodup_cons.mp (List.nodup_cons.mp hd').2).2 (n+1) hen w' parts' hpn hdn
    refine ⟨r, s, t, f, k, hsf, htk, hst, fun x => ?_⟩
    simp only [run]
    convert hval x using 2
    simp

private def first : Gate := ⟨.not, [0]⟩
private def second : Gate := ⟨.or, [4,9]⟩

private def initial (x : Fin 9 → Bool) (i : Nat) : Bool :=
  if hi : i < 9 then x ⟨i, hi⟩
  else if i = 9 then !x 0
  else if i = 10 then (!x 0 || x 4) else false

private theorem initial_high (x : Fin 9 → Bool) {i : Nat} (hi : 11 ≤ i) :
    initial x i = false := by
  simp [initial, show ¬ i < 9 by omega, show i ≠ 9 by omega, show i ≠ 10 by omega]

private theorem prefixed_eval (gs : List Gate) (out : Nat) (x : Fin 9 → Bool) :
    Circuit.eval ⟨first :: second :: gs, out⟩ (List.ofFn x) =
      run 11 (initial x) gs out := by
  rw [Circuit.eval, Circuit.wires, ← run_getD]
  set z := List.ofFn x
  have zlen : z.length = 9 := List.length_ofFn
  have getbit (i : Nat) (h : i < 9) : z.getD i false = x ⟨i, h⟩ := by
    have hz : i < z.length := by omega
    rw [List.getD_eq_getElem z false hz]
    exact List.getElem_ofFn hz
  have above (i : Nat) (h : 9 ≤ i) : z.getD i false = false := by
    apply List.getD_eq_default
    omega
  rw [zlen]
  simp only [run, first, second, List.map_cons, List.map_nil, GateOp.eval,
    List.headD_cons, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [getbit 0 (by decide), Function.update_of_ne (by decide : (4 : Nat) ≠ 9),
    Function.update_self, getbit 4 (by decide)]
  congr 2
  funext i
  by_cases hlt : i < 9
  · have i9 : i ≠ 9 := by omega
    have i10 : i ≠ 10 := by omega
    simp only [Function.update_of_ne i9, Function.update_of_ne i10, initial, dite_eq_left hlt]
    exact getbit i hlt
  by_cases h9 : i = 9
  · subst i
    simp [initial, Function.update_of_ne]
  by_cases h10 : i = 10
  · subst i
    simp [initial, Bool.or_comm]
  simp only [Function.update_of_ne h9, Function.update_of_ne h10, initial, dite_eq_right hlt,
    ite_eq_right h9, ite_eq_right h10]
  exact above i (by omega)

private theorem positive_raw_inputs (i : Fin 9) (hi : i ≠ 0) :
    ∃ x y : Fin 9 → Bool, matching x ≠ matching y ∧
      ∀ j : Fin 11, j.val ≠ i.val → initial x j.val = initial y j.val := by
  fin_cases i
  · exact False.elim (hi rfl)
  · exact ⟨raw 266, raw 264, by decide, by decide⟩
  · exact ⟨raw 140, raw 136, by decide, by decide⟩
  · exact ⟨raw 266, raw 258, by decide, by decide⟩
  · exact ⟨raw 84, raw 68, by decide, by decide⟩
  · exact ⟨raw 98, raw 66, by decide, by decide⟩
  · exact ⟨raw 98, raw 34, by decide, by decide⟩
  · exact ⟨raw 140, raw 12, by decide, by decide⟩
  · exact ⟨raw 266, raw 10, by decide, by decide⟩

private theorem counted_tail (gs : List Gate) (hmax : gs.length ≤ 9)
    (hsize : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hgood : ∀ g ∈ gs, binary g ∨ g.inputs.length = 1)
    (hused : ∀ j, 10 ≤ j → j < 10 + gs.length → j ∈ reads gs)
    (heval : ∀ x : Fin 9 → Bool, run 11 (initial x) gs (10+gs.length) = matching x) :
    gs.length = 9 ∧ (reads gs).Nodup ∧ (∀ g ∈ gs, binary g) ∧ 9 ∉ reads gs := by
  have raw_used (i : Nat) (hi : i < 9) (hpos : i ≠ 0) : i ∈ reads gs := by
    obtain ⟨x, y, h, agree⟩ :=
      positive_raw_inputs ⟨i, hi⟩ (fun e => hpos (congrArg Fin.val e))
    by_contra nh
    apply h
    rw [← heval x, ← heval y]
    apply run_eq
    intro j hj
    by_cases hlt : j < 11
    · exact agree ⟨j, hlt⟩ (fun e => by
        change j = i at e
        subst j
        exact hj.elim (fun he => by omega) nh)
    · rw [initial_high x (by omega), initial_high y (by omega)]
  have either_used : 0 ∈ reads gs ∨ 9 ∈ reads gs := by
    by_contra hh
    have h : matching (raw 273) ≠ matching (raw 272) := by decide
    apply h
    rw [← heval (raw 273), ← heval (raw 272)]
    apply run_eq
    intro j hj
    by_cases hlt : j < 11
    · have agree : ∀ i : Fin 11, i.val ≠ 0 → i.val ≠ 9 →
          initial (raw 273) i.val = initial (raw 272) i.val := by decide
      exact agree ⟨j, hlt⟩
        (fun e => by change j = 0 at e; subst j; exact hj.elim (fun he => by omega) (fun hj' => hh (Or.inl hj')))
        (fun e => by change j = 9 at e; subst j; exact hj.elim (fun he => by omega) (fun hj' => hh (Or.inr hj')))
    · rw [initial_high (raw 273) (by omega), initial_high (raw 272) (by omega)]
  -- The tail reads all raw wires 1 through 8, at least one of 0 and 9,
  -- and each nonfinal output starting with wire 10.
  classical
  let skip : Nat := if 0 ∈ reads gs then 9 else 0
  let needed := (Finset.range (10 + gs.length)).erase skip
  have cover : needed ⊆ (reads gs).toFinset := by
    intro j hj
    obtain ⟨hne, hj'⟩ := Finset.mem_erase.mp hj
    have hjb := Finset.mem_range.mp hj'
    apply List.mem_toFinset.mpr
    by_cases h0 : j = 0
    · subst j
      by_contra hn
      exact hne (by simp [skip, hn])
    by_cases h9 : j = 9
    · subst j
      rcases either_used with hh | hh
      · exact False.elim (hne (by simp [skip, hh]))
      · exact hh
    by_cases hl : j < 9
    · exact raw_used j hl h0
    · exact hused j (by omega) hjb
  have needed_card : needed.card = 9 + gs.length := by
    have hs : skip < 10 + gs.length := by unfold skip; split <;> omega
    simp [needed, Finset.card_erase_of_mem (Finset.mem_range.mpr hs)]
  have lower := Finset.card_le_card cover
  rw [needed_card] at lower
  have upper := reads_length_bound gs hsize
  have fin_upper := List.toFinset_card_le (reads gs)
  have hn : gs.length = 9 := by omega
  have hsat : 2 * gs.length ≤ (reads gs).length := by omega
  have card_eq : needed = (reads gs).toFinset :=
    Finset.eq_of_subset_of_card_le cover (by rw [needed_card]; omega)
  have hnod : (reads gs).Nodup := by
    apply List.nodup_iff_length_dedup_eq.mpr
    rw [← List.card_toFinset]
    rw [← card_eq, needed_card]
    omega
  have hbin : ∀ g ∈ gs, binary g := by
    intro g hg
    rcases hgood g hg with hb | ha
    · exact hb
    · have h2 := reads_saturated gs hsize hsat g hg
      omega
  -- With the tail entirely positive, using only wire 9 would give the wrong
  -- direction of monotonicity on the two rows with raw wire 4 set to true.
  have useZero : 0 ∈ reads gs := by
    by_contra nh
    have h := run_le gs hbin 11 (10+gs.length) (initial (raw 273)) (initial (raw 272)) (by
      intro j hj
      by_cases hj' : j < 11
      · have m : ∀ i : Fin 11, i.val ≠ 0 →
            initial (raw 273) i.val ≤ initial (raw 272) i.val := by decide
        exact m ⟨j, hj'⟩ (fun e => by
          change j = 0 at e
          subst j
          exact hj.elim (fun he => by omega) nh)
      · rw [initial_high _ (by omega), initial_high _ (by omega)])
    rw [heval, heval] at h
    exact (by decide : ¬ matching (raw 273) ≤ matching (raw 272)) h
  refine ⟨hn, hnod, hbin, ?_⟩
  intro hh
  have hmem : 9 ∈ needed := card_eq ▸ List.mem_toFinset.mpr hh
  exact (Finset.mem_erase.mp hmem).1 (by simp [skip, useZero])

private def mask (t : Finset Nat) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 10 => decide (i.val ∉ t)))).toNat

private theorem mask_bit (t : Finset Nat) {i : Nat} (hi : i < 10) :
    (mask t).testBit i = decide (i ∉ t) := by
  rw [mask, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  have h : i < (List.ofFn (fun j : Fin 10 => decide (j.val ∉ t))).length := by simpa
  rw [List.getD_eq_getElem _ false h, List.getElem_ofFn]

private theorem no_disjoint_zero {s t : Finset Nat} {f g : (Fin 9 → Bool) → Bool}
    (hs : Support s f) (ht : Support t g) (hdis : Disjoint s t) (hz : 0 ∉ t)
    (on : Bool) : ¬ ∀ x, matching x = Comb on (f x) (g x) := by
  intro h
  let m := mask t
  have mrange : m < 1024 := by
    have hlt := (BitVec.ofBoolListLE
      (List.ofFn (fun i : Fin 10 => decide (i.val ∉ t)))).isLt
    simpa [m, mask] using hlt
  have full_bit {i : Nat} (hi : i < 10) : (1023 : Nat).testBit i = true := by
    rw [show (1023 : Nat) = 2^10-1 by decide, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  have mbound : m < 1023 := by
    by_contra! hbound
    have meq : m = 1023 := by omega
    obtain ⟨i, hi⟩ := ht.nonempty
    have q : m.testBit i = decide (i ∉ t) := mask_bit t (ht.bound i hi)
    rw [meq, full_bit (ht.bound i hi)] at q
    simp [hi] at q
  have modd : m % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr (by
    rw [show m = mask t from rfl, mask_bit t (by decide : 0 < 10)]
    simp [hz])
  by_cases meq : m = 511
  · have only : ∀ i ∈ t, i = 9 := by
      intro i hi
      have hb := ht.bound i hi
      have q : m.testBit i = decide (i ∉ t) := mask_bit t hb
      rw [meq, show (511 : Nat) = 2^9-1 by decide, Nat.testBit_two_pow_sub_one] at q
      have h9 : ¬ i < 9 := by simpa [hi] using q
      omega
    have gid (x : Fin 9 → Bool) : g x = augmented x 9 :=
      ht.uniform x _ (fun i hi => by rw [only i hi])
    cases on
    · have e := h (raw 0)
      rw [gid, show augmented (raw 0) 9 = true by decide,
        show matching (raw 0) = false by decide] at e
      simp [Comb] at e
    · have e := h (raw 99)
      rw [gid, show augmented (raw 99) 9 = false by decide,
        show matching (raw 99) = true by decide] at e
      simp [Comb] at e
  · have hf : depends m f := by
      intro x y hxy
      apply hs.ag x y
      intro i hi
      have hb := hs.bound i hi
      have hin : i ∉ t := fun hit => Finset.disjoint_left.mp hdis hi hit
      apply hxy i hb
      rw [show m = mask t from rfl, mask_bit t hb]
      simp [hin]
    have hg : depends (1023 ^^^ m) g := by
      intro x y hxy
      apply ht.ag x y
      intro i hi
      have hb := ht.bound i hi
      apply hxy i hb
      rw [Nat.testBit_xor, full_bit hb, show m = mask t from rfl, mask_bit t hb]
      simp [hi]
    exact no_general_split mbound modd meq hf hg on h

private theorem no_disjoint {s t : Finset Nat} {f g : (Fin 9 → Bool) → Bool}
    (hs : Support s f) (ht : Support t g) (hdis : Disjoint s t)
    (on : Bool) : ¬ ∀ x, matching x = Comb on (f x) (g x) := by
  intro h
  by_cases h0 : 0 ∈ t
  · have hs0 : 0 ∉ s := fun h1 => Finset.disjoint_left.mp hdis h1 h0
    apply no_disjoint_zero ht hs hdis.symm hs0 on
    intro x
    rw [h x]
    cases on <;> simp [Comb, Bool.and_comm, Bool.or_comm]
  · exact no_disjoint_zero hs ht hdis h0 on h

private def supportIndex (i : Nat) : Nat := if i = 10 then 9 else i

private theorem initial_augmented (x : Fin 9 → Bool) {i : Nat} (hi : i < 11) (hne : i ≠ 9) :
    initial x i = augmented x (supportIndex i) := by
  by_cases h10 : i = 10
  · subst i
    rfl
  · have h9 : i < 9 := by omega
    simp [initial, augmented, supportIndex, h10, h9]

private theorem counted_matching (gs : List Gate) (hn : gs.length = 9)
    (hd : (reads gs).Nodup) (hb : ∀ g ∈ gs, binary g) (h9 : 9 ∉ reads gs)
    (he : Earlier 11 gs) :
    ¬ ∀ x : Fin 9 → Bool, run 11 (initial x) gs (10+gs.length) = matching x := by
  intro h
  let parts : Nat → Finset Nat := fun i => {supportIndex i}
  have hp : ∀ i ∈ reads gs, i < 11 → Support (parts i) (fun x => initial x i) := by
    intro i hr hi
    have hne : i ≠ 9 := fun e => h9 (e ▸ hr)
    have hbound : supportIndex i < 10 := by unfold supportIndex; split <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨_, Finset.mem_singleton_self _⟩
    · intro j hj
      have hj' : j = supportIndex i := Finset.mem_singleton.mp hj
      omega
    · intro x y hxy
      change initial x i = initial y i
      rw [initial_augmented x hi hne, initial_augmented y hi hne]
      exact hxy _ (Finset.mem_singleton_self _)
    · intro x b hxb
      change initial x i = b
      rw [initial_augmented x hi hne]
      exact hxb _ (Finset.mem_singleton_self _)
  have hdis : ∀ i ∈ reads gs, ∀ j ∈ reads gs, i < 11 → j < 11 → i ≠ j →
      Disjoint (parts i) (parts j) := by
    intro i hr j hs hi hj hne
    have hi9 : i ≠ 9 := fun e => h9 (e ▸ hr)
    have hj9 : j ≠ 9 := fun e => h9 (e ▸ hs)
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have e1 : k = supportIndex i := Finset.mem_singleton.mp hk
    have e2 : k = supportIndex j := Finset.mem_singleton.mp hk'
    unfold supportIndex at e1 e2
    split at e1 <;> split at e2 <;> omega
  have hnon : gs ≠ [] := fun e => by simp [e] at hn
  obtain ⟨on, s, t, f, g, hsf, htg, hst, root⟩ :=
    find_root gs hnon hb hd 11 he initial parts hp hdis
  apply no_disjoint hsf htg hst on
  intro x
  have r := root x
  rw [show 11 + gs.length - 1 = 10 + gs.length by omega, h] at r
  exact r

end PEqualNP.Outside.L_meta_27491

open PEqualNP.Outside.L_meta_27491 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_27491 :
  ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩) := by
  rintro ⟨⟨gates, out⟩, fan, size, eval, last, shape, _, used, opens, follows⟩
  cases gates with
  | nil => simp at opens
  | cons g gates =>
    have g0 : g = first := Option.some.inj opens
    subst g
    cases gates with
    | nil => simp at follows
    | cons g gs =>
      have g1 : g = second := Option.some.inj follows
      subst g
      have limit : gs.length ≤ 9 := by
        change gs.length + 1 + 1 ≤ 11 at size
        omega
      have output : out = 10 + gs.length := by
        change out + 1 = 9 + (gs.length + 1 + 1) at last
        omega
      have match_run : ∀ x : Fin 9 → Bool,
          run 11 (initial x) gs (10+gs.length) = matching x := by
        intro x
        rw [← prefixed_eval, ← output]
        exact eval x
      have gateShapes (j : Nat) (hj : j < gs.length) :
          ((gs[j]).op = .not ∧ ∃ a, a < 11 + j ∧ (gs[j]).inputs = [a]) ∨
          (((gs[j]).op = .and ∨ (gs[j]).op = .or) ∧
            ∃ a b, a < b ∧ b < 11 + j ∧ (gs[j]).inputs = [a,b]) := by
        let p : Fin ((first :: second :: gs).length) := ⟨j+2, by simp; omega⟩
        simpa [p, List.get_eq_getElem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using shape p
      have hsize : ∀ g ∈ gs, g.inputs.length ≤ 2 := by
        intro g hg
        exact (fan g (by simp [hg])).2
      have hgood : ∀ g ∈ gs, binary g ∨ g.inputs.length = 1 := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        rcases gateShapes j hj with ⟨_, a, _, ha⟩ | ⟨hop, a, b, hab, _, hrs⟩
        · exact Or.inr (by simp [ha])
        · exact Or.inl ⟨hop, a, b, hab, hrs⟩
      have hused : ∀ j, 10 ≤ j → j < 10 + gs.length → j ∈ reads gs := by
        intro j hj hj'
        let p : Fin ((first :: second :: gs).length) := ⟨j-9, by simp; omega⟩
        obtain ⟨k, hpk, hmem⟩ := used p (by change j - 9 + 1 < (first :: second :: gs).length; simp; omega)
        change j - 9 < k.val at hpk
        have hk : k.val - 2 < gs.length := by
          have h := k.isLt
          simp at h
          omega
        have hke : k.val = (k.val - 2) + 2 := by omega
        have e : (first :: second :: gs).get k = gs[k.val - 2] := by
          let k' : Fin ((first :: second :: gs).length) := ⟨k.val - 2 + 2, by simp; omega⟩
          calc
            _ = (first :: second :: gs).get k' := congrArg _ (Fin.ext hke)
            _ = _ := rfl
        change 9 + (j - 9) ∈ ((first :: second :: gs).get k).inputs at hmem
        rw [e, show 9 + (j - 9) = j by omega] at hmem
        exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hk, hmem⟩
      have earlier : Earlier 11 gs := by
        intro j hj i hi
        rcases gateShapes j hj with ⟨_, a, ha, hr⟩ | ⟨_, a, b, hab, hb, hr⟩
        · simp [hr] at hi
          omega
        · simp [hr] at hi
          rcases hi with ha' | hb' <;> omega
      obtain ⟨n, nodup, bin, reject⟩ := counted_tail gs limit hsize hgood hused match_run
      exact counted_matching gs n nodup bin reject earlier match_run
