import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27651

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_length : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => rfl
  | g :: gs, w => by
      show (run gs (step w g)).length = _
      rw [run_length gs]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

theorem getD_app (wx wy t : List Bool) (h : wx.length = wy.length) (k : Nat)
    (hk : wx.getD k false = wy.getD k false) :
    (wx ++ t).getD k false = (wy ++ t).getD k false := by
  by_cases hlt : k < wx.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (h ▸ hlt), hk]
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp hlt),
      List.getD_append_right _ _ _ _ (h ▸ not_lt.mp hlt), h]

theorem loc : ∀ (post : List Gate) (wx wy : List Bool), wx.length = wy.length →
    (∀ g ∈ post, ∀ k ∈ g.inputs, wx.getD k false = wy.getD k false) →
    ∃ t, run post wx = wx ++ t ∧ run post wy = wy ++ t
  | [], wx, wy, _, _ => ⟨[], (List.append_nil wx).symm, (List.append_nil wy).symm⟩
  | g :: post, wx, wy, hl, h => by
      have hv : (g.inputs.map fun i => wx.getD i false) = (g.inputs.map fun i => wy.getD i false) :=
        List.map_congr_left (fun k hk => h g List.mem_cons_self k hk)
      have hs : step wy g = wy ++ [g.op.eval (g.inputs.map fun i => wx.getD i false)] := by
        rw [hv]; rfl
      obtain ⟨t, h1, h2⟩ := loc post (step wx g) (step wy g)
        (by rw [hs]; simp only [step, List.length_append, hl])
        (by
          intro g' hg' k hk
          rw [hs]
          exact getD_app wx wy _ hl k (h g' (List.mem_cons_of_mem _ hg') k hk))
      refine ⟨g.op.eval (g.inputs.map fun i => wx.getD i false) :: t, ?_, ?_⟩
      · show run post (step wx g) = _
        rw [h1]
        simp only [step, List.append_assoc, List.singleton_append]
      · show run post (step wy g) = _
        rw [h2, hs]
        simp only [List.append_assoc, List.singleton_append]

theorem sep_core (gs pre post : List Gate) (o : Nat) (hg : gs = pre ++ post) (x y : List Bool)
    (hxy : x.length = y.length)
    (ho : (run pre x).getD o false = (run pre y).getD o false)
    (hag : ∀ g ∈ post, ∀ k ∈ g.inputs, (run pre x).getD k false = (run pre y).getD k false) :
    (Circuit.mk gs o).eval x = (Circuit.mk gs o).eval y := by
  have hl : (run pre x).length = (run pre y).length := by rw [run_length, run_length, hxy]
  obtain ⟨t, h1, h2⟩ := loc post (run pre x) (run pre y) hl hag
  have hx : ∀ z, (Circuit.mk gs o).wires z = run post (run pre z) := by
    intro z
    subst hg
    exact List.foldl_append ..
  show ((Circuit.mk gs o).wires x).getD o false = ((Circuit.mk gs o).wires y).getD o false
  rw [hx, hx, h1, h2]
  exact getD_app _ _ _ hl _ ho

def bits (n : Nat) : Fin 9 → Bool := fun i => n.testBit i.val

def tgt (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def agreeB (wx wy : List Bool) (excl : List Nat) : Bool :=
  wx.length == wy.length &&
    (List.range wx.length).all (fun k => excl.contains k || wx.getD k false == wy.getD k false)

theorem agreeB_spec (wx wy : List Bool) (excl : List Nat) (h : agreeB wx wy excl = true) (k : Nat)
    (hk : k ∉ excl) : wx.getD k false = wy.getD k false := by
  simp only [agreeB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_iff_mem] at h
  obtain ⟨hl, ha⟩ := h
  by_cases hlt : k < wx.length
  · rcases ha k hlt with h1 | h1
    · exact absurd h1 hk
    · exact h1
  · rw [List.getD_eq_default _ _ (not_lt.mp hlt), List.getD_eq_default _ _ (hl ▸ not_lt.mp hlt)]

def good (pre : List Gate) (excl : List Nat) (p : Nat × Nat) : Bool :=
  (tgt (bits p.1) != tgt (bits p.2)) &&
    agreeB (run pre (List.ofFn (bits p.1))) (run pre (List.ofFn (bits p.2))) excl

theorem sep_use (gs pre post : List Gate) (o : Nat) (hg : gs = pre ++ post)
    (hf : ∀ x : Fin 9 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = tgt x)
    (excl : List Nat) (p : Nat × Nat) (hgood : good pre excl p = true)
    (ho : o ∉ excl) (hpost : ∀ g ∈ post, ∀ k ∈ g.inputs, k ∉ excl) : False := by
  simp only [good, Bool.and_eq_true, bne_iff_ne, ne_eq] at hgood
  obtain ⟨hne, hag⟩ := hgood
  apply hne
  rw [← hf, ← hf]
  exact sep_core gs pre post o hg _ _ (by simp only [List.length_ofFn])
    (agreeB_spec _ _ _ hag o ho) (fun g hg' k hk => agreeB_spec _ _ _ hag k (hpost g hg' k hk))

def w1 : List (Nat × Nat) :=
  [(176, 177), (96, 98), (80, 84), (132, 140), (69, 85), (66, 98), (20, 84), (12, 140), (10, 266)]

theorem chk1 : ∀ i < 9, good [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩] [i] (w1.getD i (0, 0)) = true := by
  decide +kernel

def w3 : List (Nat × Nat) :=
  [(466, 470), (316, 317), (262, 270), (43, 171), (97, 99), (218, 474), (29, 93), (78, 110),
   (393, 409), (162, 226), (338, 370), (456, 458), (133, 141), (202, 458), (46, 174), (168, 172),
   (327, 342), (418, 419), (284, 286), (76, 92)]

def chkA (a b : Nat) : Bool :=
  w3.any (good [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [a, b]⟩] [a, b, 9])

def chkO (a b : Nat) : Bool :=
  w3.any (good [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [a, b]⟩] [a, b, 9])

def chk3B (a b : Nat) : Bool :=
  !(decide (a < b)) || (a == 9) || (b == 9) || (chkA a b && chkO a b)

theorem chk3all : (List.range 11).all (fun a => (List.range 11).all (fun b => chk3B a b)) = true := by
  decide +kernel

theorem chk3 (a b : Nat) (hb : b < 11) (hab : a < b) (ha9 : a ≠ 9) (hb9 : b ≠ 9) :
    chkA a b = true ∧ chkO a b = true := by
  have h := chk3all
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr hb)
  simp only [chk3B, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    beq_iff_eq] at h2
  rcases h2 with ((h3 | h3) | h3) | h3
  · exact absurd hab h3
  · exact absurd h3 ha9
  · exact absurd h3 hb9
  · exact h3

def reads (l : List Gate) : List Nat := l.flatMap (fun g => g.inputs)

theorem reads_cons (g : Gate) (l : List Gate) : reads (g :: l) = g.inputs ++ reads l := by
  simp only [reads, List.flatMap_cons]

theorem mem_reads (l : List Gate) (g : Gate) (hg : g ∈ l) (k : Nat) (hk : k ∈ g.inputs) :
    k ∈ reads l := List.mem_flatMap.mpr ⟨g, hg, hk⟩

theorem reads_len : ∀ l : List Gate, (∀ g ∈ l, g.inputs.length ≤ 2) →
    (reads l).length ≤ 2 * l.length
  | [], _ => by simp [reads]
  | g :: l, h => by
      have h1 := h g List.mem_cons_self
      have h2 := reads_len l (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      rw [reads_cons]
      simp only [List.length_append, List.length_cons]
      omega

theorem main_aux (rest : List Gate) (o : Nat)
    (hfan : ∀ g ∈ rest, g.inputs.length ≤ 2)
    (hn : rest.length ≤ 9)
    (hf : ∀ x : Fin 9 → Bool,
      (Circuit.mk (⟨GateOp.or, [0, 4]⟩ :: ⟨GateOp.not, [9]⟩ :: rest) o).eval (List.ofFn x) = tgt x)
    (ho : o = rest.length + 10)
    (hnf2 : ∀ g2 post, rest = g2 :: post →
      (g2.op = GateOp.not ∧ ∃ a, a < 11 ∧ g2.inputs = [a]) ∨
      ((g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < 11 ∧ g2.inputs = [a, b]))
    (hread : ∀ m, 1 ≤ m → m ≤ rest.length → 9 + m ∈ reads rest) : False := by
  have hF1 : ∀ i < 9, i ∈ reads rest := by
    intro i hi
    by_contra hni
    refine sep_use _ [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩] rest o rfl hf [i] (w1.getD i (0, 0))
      (chk1 i hi) ?_ ?_
    · simp only [List.mem_singleton]
      omega
    · intro g hg k hk
      simp only [List.mem_singleton]
      intro hki
      subst hki
      exact hni (mem_reads rest g hg k hk)
  have hsub : List.range 9 ++ List.range' 10 rest.length ⊆ reads rest := by
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · exact hF1 k (List.mem_range.mp h)
    · have h' := List.mem_range'_1.mp h
      have h9 := hread (k - 9) (by omega) (by omega)
      rwa [show 9 + (k - 9) = k by omega] at h9
  have hnd : (List.range 9 ++ List.range' 10 rest.length).Nodup := by
    refine List.Nodup.append List.nodup_range List.nodup_range' ?_
    intro k h1 h2
    have h1' := List.mem_range.mp h1
    have h2' := List.mem_range'_1.mp h2
    omega
  have hsp := List.subperm_of_subset hnd hsub
  have hlen := hsp.length_le
  have hL2 := reads_len rest hfan
  simp only [List.length_append, List.length_range, List.length_range'] at hlen
  have hn9 : rest.length = 9 := by omega
  have hperm := hsp.perm_of_length_le (by
    simp only [List.length_append, List.length_range, List.length_range']
    omega)
  have hLnd : (reads rest).Nodup := hperm.nodup_iff.mp hnd
  have h9 : 9 ∉ reads rest := by
    intro h
    rcases List.mem_append.mp (hperm.mem_iff.mpr h) with h1 | h1
    · have := List.mem_range.mp h1
      omega
    · have := List.mem_range'_1.mp h1
      omega
  obtain ⟨g2, post, hrest⟩ : ∃ g2 post, rest = g2 :: post := by
    cases rest with
    | nil => simp at hn9
    | cons g2 post => exact ⟨g2, post, rfl⟩
  have hnf := hnf2 g2 post hrest
  subst hrest
  rw [reads_cons] at hLnd h9 hlen
  have hpl : post.length = 8 := by
    simp only [List.length_cons] at hn9
    omega
  have hP2 := reads_len post (fun g hg => hfan g (List.mem_cons_of_mem _ hg))
  obtain ⟨op2, in2⟩ := g2
  dsimp only at hnf hLnd h9 hlen
  rcases hnf with ⟨-, a, -, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
  · subst hin
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  · subst hin
    have ha9 : a ≠ 9 := by
      intro h
      exact h9 (by simp [h])
    have hb9 : b ≠ 9 := by
      intro h
      exact h9 (by simp [h])
    have h9p : 9 ∉ reads post := fun h => h9 (by simp [h])
    have hap : a ∉ reads post := by
      intro h
      have := (List.nodup_cons.mp hLnd).1
      exact this (by simp [h])
    have hbp : b ∉ reads post := by
      intro h
      have := (List.nodup_cons.mp (List.nodup_cons.mp hLnd).2).1
      exact this h
    have hc := chk3 a b hb hab ha9 hb9
    have hex : ∀ k, k ∈ reads post → k ∉ [a, b, 9] := by
      intro k hk hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · exact hap (h ▸ hk)
      · exact hbp (h ▸ hk)
      · exact h9p (h ▸ hk)
    have hoex : o ∉ [a, b, 9] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      simp only [List.length_cons] at ho
      omega
    rcases hop with hop | hop
    · subst hop
      have hA : w3.any (good [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [a, b]⟩]
        [a, b, 9]) = true := hc.1
      obtain ⟨p, -, hgood⟩ := List.any_eq_true.mp hA
      exact sep_use _ [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [a, b]⟩] post o rfl hf
        [a, b, 9] p hgood hoex (fun g hg k hk => hex k (mem_reads post g hg k hk))
    · subst hop
      have hO : w3.any (good [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [a, b]⟩]
        [a, b, 9]) = true := hc.2
      obtain ⟨p, -, hgood⟩ := List.any_eq_true.mp hO
      exact sep_use _ [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [a, b]⟩] post o rfl hf
        [a, b, 9] p hgood hoex (fun g hg k hk => hex k (mem_reads post g hg k hk))

end PEqualNP.Outside.L_meta_27651

theorem PEqualNP.Outside.L_meta_27651 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩)) := by
  rintro ⟨⟨gates, output⟩, hfan, hsize, hf, hout, hnf, -, hread, hh0, hh1⟩
  dsimp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hsize hout hnf hread hh0 hh1
  obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.mp hh0
  subst htl
  simp only [List.tail_cons] at hh1
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hh1
  subst hrest
  simp only [List.length_cons] at hsize hout
  refine PEqualNP.Outside.L_meta_27651.main_aux rest output ?_ (by omega) hf (by omega) ?_ ?_
  · intro g hg
    exact (hfan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))).2
  · intro g2 post hrest
    subst hrest
    exact hnf ⟨2, by simp⟩
  · intro m hm1 hm2
    obtain ⟨k, -, hmem⟩ := hread ⟨m, by simp only [List.length_cons]; omega⟩
      (by simp only [List.length_cons]; omega)
    have hin := List.get_mem (_ :: _ :: rest) k
    dsimp only at hmem
    generalize List.get (_ :: _ :: rest) k = g at hmem hin
    rcases List.mem_cons.mp hin with h | h
    · subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      omega
    · rcases List.mem_cons.mp h with h | h
      · subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        omega
      · exact PEqualNP.Outside.L_meta_27651.mem_reads rest g h _ hmem
