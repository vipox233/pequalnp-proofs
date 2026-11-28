import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
namespace PEqualNP.Outside.L_meta_33651_aux
open Sum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0
def z2b (z : ZMod 2) : Bool := decide (z ≠ 0)
lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
 rcases z with ⟨k, hk⟩
 interval_cases k
 · exact Or.inl rfl
 · exact Or.inr rfl
lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
 cases b <;> simp [z2b, b2z, one_ne_zero]
lemma b2z_z2b (z : ZMod 2) : b2z (z2b z) = z := by
 rcases zmod2_cases z with rfl | rfl <;> simp [z2b, b2z, one_ne_zero]
lemma z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
 rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
 · decide
 · decide
 · decide
 · decide
lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
 cases a <;> cases b <;> decide
lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
 cases a <;> cases b <;> decide
lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
 rcases zmod2_cases x with rfl | rfl <;> decide
def stepWires (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
   C.wires x = C.gates.foldl stepWires x := rfl
lemma foldl_stepWires_length (gs : List Gate) (w : List Bool) :
   (gs.foldl stepWires w).length = w.length + gs.length := by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
   simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons, List.length_nil]
   omega
lemma foldl_stepWires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
   (gs.foldl stepWires w).getD i false = w.getD i false := by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
   simp only [List.foldl_cons]
   have hlt : i < (stepWires w g).length := by
     simp only [stepWires, List.length_append, List.length_cons, List.length_nil]; omega
   rw [ih (stepWires w g) hlt]
   simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma foldl_stepWires_getD_eq (w : List Bool) (g : Gate) :
   (stepWires w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
 simp [stepWires, List.getD_eq_getElem?_getD]
def MultiCirc {n L : ℕ} (s : ℕ) (f : (Fin n → Bool) → (Fin L → Bool)) : Prop :=
 ∃ (C : Circuit) (out : Fin L → Fin (n + C.size)),
   FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ s ∧
   ∀ x : Fin n → Bool, ∀ i : Fin L,
     (C.wires (List.ofFn x)).getD (out i).val false = f x i
lemma mc_mono {n L s1 s2 : ℕ} {f : (Fin n → Bool) → (Fin L → Bool)}
   (hs : s1 ≤ s2) (hf : MultiCirc s1 f) : MultiCirc s2 f := by
 obtain ⟨C, out, hF, hB, hS, hE⟩ := hf
 exact ⟨C, out, hF, hB, hS.trans hs, hE⟩
lemma mc_proj {n L : ℕ} (p : Fin L → Fin n) :
   MultiCirc 0 (fun x i => x (p i)) := by
 refine ⟨⟨[], 0⟩, fun i => ⟨(p i).val, by simp [Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg; cases hg
 · intro j hj; cases hj
 · simp [Circuit.size]
 · intro x i
   simp [Circuit.wires, List.getD_eq_getElem?_getD]
lemma mc_const {n L : ℕ} (c : Fin L → Bool) :
   MultiCirc 2 (fun (_ : Fin n → Bool) i => c i) := by
 let gs : List Gate := [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩]
 refine ⟨⟨gs, 0⟩, fun i => ⟨if c i then n + 1 else n, by
     simp only [Circuit.size, gs, List.length_cons, List.length_nil]
     split_ifs <;> omega⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg
   simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
   rcases hg with rfl | rfl <;> simp
 · intro j hj i hi
   simp only [gateAt, gs, List.getD_eq_getElem?_getD] at hi
   rcases j with _ | _ | j <;> simp at hi
 · simp [Circuit.size, gs]
 · intro x i
   have hlen : (List.ofFn x).length = n := List.length_ofFn
   rw [wires_eq_foldl]
   simp only [gs, List.foldl_cons, List.foldl_nil]
   cases hc : c i
   · simp only [Bool.false_eq_true, ↓reduceIte]
     have h1 : (stepWires (stepWires (List.ofFn x) ⟨GateOp.or, []⟩) ⟨GateOp.and, []⟩).getD n false =
         (stepWires (List.ofFn x) ⟨GateOp.or, []⟩).getD n false := by
       simp only [stepWires, List.getD_eq_getElem?_getD]
       rw [List.getElem?_append_left (by simp [hlen])]
     have h2 := foldl_stepWires_getD_eq (List.ofFn x) ⟨GateOp.or, []⟩
     rw [hlen] at h2
     rw [h1, h2]
     rfl
   · simp only [↓reduceIte]
     have hlen1 : (stepWires (List.ofFn x) ⟨GateOp.or, []⟩).length = n + 1 := by
       simp [stepWires, hlen]
     rw [← hlen1, foldl_stepWires_getD_eq]
     rfl
lemma foldl_stepWires_map_remap {n L1 : ℕ} (out1 : Fin L1 → ℕ)
   (w1 : List Bool) (hw1 : w1.length = n) (y : List Bool) (hy : y.length = L1)
   (hagree : ∀ j : Fin L1, w1.getD (out1 j) false = y.getD j.val false)
   (hout1_lt : ∀ j : Fin L1, out1 j < n)
   (gs : List Gate)
   (hBack : ∀ j < gs.length, ∀ a ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, a < L1 + j) :
   let remap : ℕ → ℕ := fun a => if h : a < L1 then out1 ⟨a, h⟩ else n + (a - L1)
   let gs' : List Gate := gs.map (fun g => ⟨g.op, g.inputs.map remap⟩)
   ∀ (k : ℕ) (_hk : k < gs.length),
     (gs'.foldl stepWires w1).getD (n + k) false = (gs.foldl stepWires y).getD (L1 + k) false := by
 intro remap gs'
 have hmain : ∀ (m : ℕ) (hm : m ≤ gs.length),
     ∀ (k : ℕ) (hk : k < m),
       (((gs.take m).map (fun g => ⟨g.op, g.inputs.map remap⟩)).foldl stepWires w1).getD (n + k) false =
       ((gs.take m).foldl stepWires y).getD (L1 + k) false := by
   intro m
   induction m with
   | zero => intro _ k hk; omega
   | succ m ih =>
     intro hm k hk
     have htake : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem (by omega)
     rw [htake, List.map_append, List.map_singleton, List.foldl_append, List.foldl_append,
       List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
     let p1 := ((gs.take m).map (fun g => ⟨g.op, g.inputs.map remap⟩)).foldl stepWires w1
     let p2 := (gs.take m).foldl stepWires y
     have hlen1 : p1.length = n + m := by
       dsimp [p1]
       rw [foldl_stepWires_length, hw1, List.length_map, List.length_take, Nat.min_eq_left (by omega)]
     have hlen2 : p2.length = L1 + m := by
       dsimp [p2]
       rw [foldl_stepWires_length, hy, List.length_take, Nat.min_eq_left (by omega)]
     by_cases hkm : k < m
     · have hlt1 : n + k < p1.length := by omega
       have hlt2 : L1 + k < p2.length := by omega
       change (stepWires p1 _).getD (n + k) false = (stepWires p2 _).getD (L1 + k) false
       simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
         List.getElem?_append_left hlt2]
       exact ih (by omega) k hkm
     · have hkeq : k = m := by omega
       subst hkeq
       change (stepWires p1 _).getD (n + k) false = (stepWires p2 _).getD (L1 + k) false
       rw [← hlen1, foldl_stepWires_getD_eq, ← hlen2, foldl_stepWires_getD_eq]
       congr 1
       rw [List.map_map]
       apply List.map_congr_left
       intro a ha
       have ha_lt : a < L1 + k := by
         have hb := hBack k (by omega) a
         have hget : gs.getD k ⟨GateOp.or, []⟩ = gs[k] := by
           simp [List.getD_eq_getElem?_getD, show k < gs.length by omega]
         rw [hget] at hb
         exact hb ha
       dsimp [Function.comp, remap]
       by_cases haL : a < L1
       · simp only [haL, ↓reduceDIte]
         have h1 : p1.getD (out1 ⟨a, haL⟩) false = w1.getD (out1 ⟨a, haL⟩) false :=
           foldl_stepWires_getD_lt _ w1 _ (by rw [hw1]; exact hout1_lt ⟨a, haL⟩)
         have h2 : p2.getD a false = y.getD a false :=
           foldl_stepWires_getD_lt _ y _ (by rw [hy]; exact haL)
         rw [h1, h2, hagree ⟨a, haL⟩]
       · simp only [haL, ↓reduceDIte]
         have hsub : a - L1 < k := by omega
         have hrec := ih (by omega) (a - L1) hsub
         have hadd : L1 + (a - L1) = a := by omega
         rw [hadd] at hrec
         exact hrec
 intro k hk
 have h := hmain gs.length le_rfl k hk
 rwa [List.take_length] at h
lemma mc_comp {n L1 L2 s1 s2 : ℕ}
   {f : (Fin n → Bool) → (Fin L1 → Bool)}
   {g : (Fin L1 → Bool) → (Fin L2 → Bool)}
   (hf : MultiCirc s1 f) (hg : MultiCirc s2 g) :
   MultiCirc (s1 + s2) (fun x => g (f x)) := by
 obtain ⟨C1, out1, hF1, hB1, hS1, hE1⟩ := hf
 obtain ⟨C2, out2, hF2, hB2, hS2, hE2⟩ := hg
 let m1 := C1.size
 let remap : ℕ → ℕ := fun a => if h : a < L1 then (out1 ⟨a, h⟩).val else n + m1 + (a - L1)
 let gs2' : List Gate := C2.gates.map (fun gt => ⟨gt.op, gt.inputs.map remap⟩)
 let C : Circuit := ⟨C1.gates ++ gs2', 0⟩
 have hCsize : C.size = m1 + C2.size := by
   simp [C, Circuit.size, gs2', m1]
 have hremap_lt : ∀ a j, a < L1 + j → remap a < n + m1 + j := by
   intro a j ha
   dsimp only [remap]
   by_cases h : a < L1
   · simp only [h, ↓reduceDIte]; have := (out1 ⟨a, h⟩).isLt; omega
   · simp only [h, ↓reduceDIte]; omega
 refine ⟨C, fun i => ⟨remap (out2 i).val, by
     rw [hCsize, ← add_assoc]; exact hremap_lt _ _ (out2 i).isLt⟩,
   ?_, ?_, ?_, ?_⟩
 · intro gt hgt
   simp only [C, List.mem_append, gs2', List.mem_map] at hgt
   rcases hgt with h1 | ⟨gt2, hgt2, rfl⟩
   · exact hF1 gt h1
   · obtain ⟨hop, hlen⟩ := hF2 gt2 hgt2
     exact ⟨hop, by simpa using hlen⟩
 · intro j hj a ha
   have hlenC : C.gates.length = m1 + C2.gates.length := by simp [C, gs2', m1, Circuit.size]
   by_cases hj1 : j < m1
   · have hgt : gateAt C j = gateAt C1 j := by
       simp only [gateAt, C, List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
     rw [hgt] at ha
     exact hB1 j hj1 a ha
   · have hj2 : j - m1 < C2.gates.length := by omega
     have hgt : gateAt C j = ⟨(gateAt C2 (j - m1)).op, (gateAt C2 (j - m1)).inputs.map remap⟩ := by
       simp only [gateAt, C, gs2', List.getD_eq_getElem?_getD]
       have hge : C1.gates.length ≤ j := by dsimp [m1, Circuit.size] at hj1; omega
       rw [List.getElem?_append_right hge, show C1.gates.length = m1 from rfl, List.getElem?_map,
         List.getElem?_eq_getElem hj2]
       rfl
     rw [hgt] at ha
     rcases List.mem_map.mp ha with ⟨a0, ha0, rfl⟩
     have ha0_lt := hB2 (j - m1) hj2 a0 ha0
     have hlt := hremap_lt a0 (j - m1) ha0_lt
     omega
 · rw [hCsize]; omega
 · intro x i
   dsimp only
   rw [wires_eq_foldl]
   change ((C1.gates ++ gs2').foldl stepWires (List.ofFn x)).getD (remap (out2 i).val) false =
     g (f x) i
   rw [List.foldl_append]
   let w1 := C1.gates.foldl stepWires (List.ofFn x)
   have hw1 : w1.length = n + m1 := by
     dsimp [w1]; rw [foldl_stepWires_length, List.length_ofFn]; rfl
   have hfx_len : (List.ofFn (f x)).length = L1 := List.length_ofFn
   have hagree : ∀ j : Fin L1, w1.getD (out1 j).val false = (List.ofFn (f x)).getD j.val false := by
     intro j
     have h1 := hE1 x j
     rw [wires_eq_foldl] at h1
     rw [h1]
     simp [List.getD_eq_getElem?_getD]
   have hstep := foldl_stepWires_map_remap (fun j => (out1 j).val) w1 hw1 (List.ofFn (f x))
     hfx_len hagree (fun j => (out1 j).isLt) C2.gates hB2
   have hE2i := hE2 (f x) i
   rw [wires_eq_foldl] at hE2i
   rw [← hE2i]
   by_cases h2 : (out2 i).val < L1
   · dsimp only [remap]
     simp only [h2, ↓reduceDIte]
     have hl1 : (gs2'.foldl stepWires w1).getD (out1 ⟨(out2 i).val, h2⟩).val false =
         w1.getD (out1 ⟨(out2 i).val, h2⟩).val false :=
       foldl_stepWires_getD_lt gs2' w1 _ (by rw [hw1]; exact (out1 _).isLt)
     have hl2 : (C2.gates.foldl stepWires (List.ofFn (f x))).getD (out2 i).val false =
         (List.ofFn (f x)).getD (out2 i).val false :=
       foldl_stepWires_getD_lt C2.gates (List.ofFn (f x)) _ (by rw [hfx_len]; exact h2)
     rw [hl1, hl2, hagree ⟨(out2 i).val, h2⟩]
   · dsimp only [remap]
     simp only [h2, ↓reduceDIte]
     have hk : (out2 i).val - L1 < C2.gates.length := by
       have := (out2 i).isLt; dsimp [Circuit.size] at this; omega
     have hres := hstep ((out2 i).val - L1) hk
     have hadd : L1 + ((out2 i).val - L1) = (out2 i).val := by omega
     rwa [hadd] at hres
lemma mc_pair {n L1 L2 s1 s2 : ℕ}
   {f1 : (Fin n → Bool) → (Fin L1 → Bool)}
   {f2 : (Fin n → Bool) → (Fin L2 → Bool)}
   (h1 : MultiCirc s1 f1) (h2 : MultiCirc s2 f2) :
   MultiCirc (s1 + s2) (fun x (i : Fin (L1 + L2)) =>
     if hi : i.val < L1 then f1 x ⟨i.val, hi⟩ else f2 x ⟨i.val - L1, by omega⟩) := by
 obtain ⟨C1, out1, hF1, hB1, hS1, hE1⟩ := h1
 obtain ⟨C2, out2, hF2, hB2, hS2, hE2⟩ := h2
 let m1 := C1.size
 let remap : ℕ → ℕ := fun a => if a < n then a else a + m1
 let gs2' : List Gate := C2.gates.map (fun gt => ⟨gt.op, gt.inputs.map remap⟩)
 let C : Circuit := ⟨C1.gates ++ gs2', 0⟩
 have hCsize : C.size = m1 + C2.size := by simp [C, Circuit.size, gs2', m1]
 let out : Fin (L1 + L2) → Fin (n + C.size) := fun i =>
   if hi : i.val < L1 then ⟨(out1 ⟨i.val, hi⟩).val, by rw [hCsize]; have := (out1 ⟨i.val, hi⟩).isLt; omega⟩
   else ⟨remap (out2 ⟨i.val - L1, by omega⟩).val, by
     rw [hCsize]; dsimp only [remap]
     have := (out2 ⟨i.val - L1, by omega⟩).isLt
     split_ifs <;> omega⟩
 refine ⟨C, out, ?_, ?_, ?_, ?_⟩
 · intro gt hgt
   simp only [C, List.mem_append, gs2', List.mem_map] at hgt
   rcases hgt with ha | ⟨gt2, hgt2, rfl⟩
   · exact hF1 gt ha
   · obtain ⟨hop, hlen⟩ := hF2 gt2 hgt2
     exact ⟨hop, by simpa using hlen⟩
 · intro j hj a ha
   by_cases hj1 : j < m1
   · have hgt : gateAt C j = gateAt C1 j := by
       simp only [gateAt, C, List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
     rw [hgt] at ha
     exact hB1 j hj1 a ha
   · have hj2 : j - m1 < C2.gates.length := by
       have hlenC : C.gates.length = m1 + C2.gates.length := by simp [C, gs2', m1, Circuit.size]
       omega
     have hgt : gateAt C j = ⟨(gateAt C2 (j - m1)).op, (gateAt C2 (j - m1)).inputs.map remap⟩ := by
       simp only [gateAt, C, gs2', List.getD_eq_getElem?_getD]
       have hge : C1.gates.length ≤ j := by dsimp [m1, Circuit.size] at hj1; omega
       rw [List.getElem?_append_right hge, show C1.gates.length = m1 from rfl, List.getElem?_map,
         List.getElem?_eq_getElem hj2]
       rfl
     rw [hgt] at ha
     rcases List.mem_map.mp ha with ⟨a0, ha0, rfl⟩
     have ha0_lt := hB2 (j - m1) hj2 a0 ha0
     dsimp only [remap]
     split_ifs <;> omega
 · rw [hCsize]; omega
 · intro x i
   dsimp only [out]
   by_cases hi : i.val < L1
   · simp only [hi, ↓reduceDIte]
     rw [wires_eq_foldl]
     change ((C1.gates ++ gs2').foldl stepWires (List.ofFn x)).getD (out1 ⟨i.val, hi⟩).val false =
       f1 x ⟨i.val, hi⟩
     rw [List.foldl_append]
     have hw1 : (C1.gates.foldl stepWires (List.ofFn x)).length = n + m1 := by
       rw [foldl_stepWires_length, List.length_ofFn]; rfl
     rw [foldl_stepWires_getD_lt gs2' _ _ (by rw [hw1]; exact (out1 _).isLt)]
     exact hE1 x ⟨i.val, hi⟩
   · simp only [hi, ↓reduceDIte]
     rw [wires_eq_foldl]
     change ((C1.gates ++ gs2').foldl stepWires (List.ofFn x)).getD
       (remap (out2 ⟨i.val - L1, by omega⟩).val) false = f2 x ⟨i.val - L1, by omega⟩
     rw [List.foldl_append]
     let w1 := C1.gates.foldl stepWires (List.ofFn x)
     have hw1 : w1.length = n + m1 := by
       dsimp [w1]; rw [foldl_stepWires_length, List.length_ofFn]; rfl
     have hlenx : (List.ofFn x).length = n := List.length_ofFn
     have hagree : ∀ j : Fin n, w1.getD j.val false = (List.ofFn x).getD j.val false := fun j =>
       foldl_stepWires_getD_lt C1.gates (List.ofFn x) j.val (by rw [hlenx]; exact j.isLt)
     have hgs2'_eq : gs2' = C2.gates.map (fun gt => ⟨gt.op, gt.inputs.map
         (fun a => if h : a < n then (⟨a, h⟩ : Fin n).val else n + m1 + (a - n))⟩) := by
       dsimp [gs2']
       congr 1; funext gt; congr 1
       apply List.map_congr_left
       intro a _; dsimp [remap]; by_cases h : a < n
       · simp [h]
       · simp [h]; omega
     have hstep := foldl_stepWires_map_remap (fun j : Fin n => j.val) w1 hw1 (List.ofFn x) hlenx
       hagree (fun j => by omega) C2.gates hB2
     have hE2i := hE2 x ⟨i.val - L1, by omega⟩
     rw [wires_eq_foldl] at hE2i
     rw [← hE2i]
     let w := (out2 ⟨i.val - L1, by omega⟩).val
     by_cases hwn : w < n
     · have hrm : remap w = w := by simp [remap, hwn]
       rw [hrm]
       rw [foldl_stepWires_getD_lt gs2' w1 w (by rw [hw1]; omega)]
       rw [foldl_stepWires_getD_lt C2.gates (List.ofFn x) w (by rw [hlenx]; exact hwn)]
       exact hagree ⟨w, hwn⟩
     · have hrm : remap w = n + m1 + (w - n) := by simp [remap, hwn]; omega
       rw [hrm, hgs2'_eq]
       have hk : w - n < C2.gates.length := by
         have := (out2 ⟨i.val - L1, by omega⟩).isLt; dsimp [w, Circuit.size] at *; omega
       have hres := hstep (w - n) hk
       have hadd : n + (w - n) = w := by omega
       rwa [hadd] at hres
lemma mc_not : MultiCirc 1 (fun (x : Fin 1 → Bool) (_ : Fin 1) => !(x 0)) := by
 let C : Circuit := ⟨[⟨GateOp.not, [0]⟩], 0⟩
 refine ⟨C, fun _ => ⟨1, by simp [C, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg; simp [C] at hg; subst hg; simp
 · intro j hj a ha
   have : j = 0 := by simp [C] at hj; omega
   subst this; simp [gateAt, C] at ha; omega
 · simp [C, Circuit.size]
 · intro x i
   have hi : i = 0 := Subsingleton.elim i 0
   subst hi
   simp [C, Circuit.wires, List.getD_eq_getElem?_getD, GateOp.eval]
lemma mc_and : MultiCirc 1 (fun (x : Fin 2 → Bool) (_ : Fin 1) => x 0 && x 1) := by
 let C : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 0⟩
 refine ⟨C, fun _ => ⟨2, by simp [C, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg; simp [C] at hg; subst hg; simp
 · intro j hj a ha
   have : j = 0 := by simp [C] at hj; omega
   subst this; simp [gateAt, C] at ha; omega
 · simp [C, Circuit.size]
 · intro x i
   have hi : i = 0 := Subsingleton.elim i 0
   subst hi
   simp [C, Circuit.wires, List.getD_eq_getElem?_getD, GateOp.eval]
lemma mc_or : MultiCirc 1 (fun (x : Fin 2 → Bool) (_ : Fin 1) => x 0 || x 1) := by
 let C : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩], 0⟩
 refine ⟨C, fun _ => ⟨2, by simp [C, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg; simp [C] at hg; subst hg; simp
 · intro j hj a ha
   have : j = 0 := by simp [C] at hj; omega
   subst this; simp [gateAt, C] at ha; omega
 · simp [C, Circuit.size]
 · intro x i
   have hi : i = 0 := Subsingleton.elim i 0
   subst hi
   simp [C, Circuit.wires, List.getD_eq_getElem?_getD, GateOp.eval]
lemma mc_xor : MultiCirc 5 (fun (x : Fin 2 → Bool) (_ : Fin 1) => xor (x 0) (x 1)) := by
 let gs : List Gate :=
   [⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [4, 5]⟩]
 let C : Circuit := ⟨gs, 0⟩
 refine ⟨C, fun _ => ⟨6, by simp [C, gs, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg
   simp only [C, gs, List.mem_cons, List.not_mem_nil, or_false] at hg
   rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
 · intro j hj a ha
   have hjlt : j < 5 := by simpa [C, gs] using hj
   interval_cases j <;> simp [gateAt, C, gs] at ha <;> omega
 · simp [C, gs, Circuit.size]
 · intro x i
   have hi : i = 0 := Subsingleton.elim i 0
   subst hi
   simp only [C, gs, Circuit.wires, List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
     Fin.succ_zero_eq_one, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
     List.getD_eq_getElem?_getD, GateOp.eval]
   cases x 0 <;> cases x 1 <;> rfl
lemma mc_ite : MultiCirc 4 (fun (x : Fin 3 → Bool) (_ : Fin 1) => if x 0 then x 1 else x 2) := by
 let gs : List Gate :=
   [⟨GateOp.not, [0]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [3, 2]⟩, ⟨GateOp.or, [4, 5]⟩]
 let C : Circuit := ⟨gs, 0⟩
 refine ⟨C, fun _ => ⟨6, by simp [C, gs, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
 · intro g hg
   simp only [C, gs, List.mem_cons, List.not_mem_nil, or_false] at hg
   rcases hg with rfl | rfl | rfl | rfl <;> simp
 · intro j hj a ha
   have hjlt : j < 4 := by simpa [C, gs] using hj
   interval_cases j <;> simp [gateAt, C, gs] at ha <;> omega
 · simp [C, gs, Circuit.size]
 · intro x i
   have hi : i = 0 := Subsingleton.elim i 0
   subst hi
   have hs1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := rfl
   simp only [C, gs, Circuit.wires, List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
     Fin.succ_zero_eq_one, hs1, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
     List.getD_eq_getElem?_getD, GateOp.eval]
   cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl
noncomputable def EC {ι ο : Type} [Fintype ι] [Fintype ο] (s : ℕ)
   (f : (ι → Bool) → (ο → Bool)) : Prop :=
 MultiCirc s (fun x j => f (fun i => x (Fintype.equivFin ι i)) ((Fintype.equivFin ο).symm j))
lemma ec_mono {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 : ℕ}
   {f : (ι → Bool) → (ο → Bool)} (hs : s1 ≤ s2) (hf : EC s1 f) : EC s2 f :=
 mc_mono hs hf
lemma ec_eq {ι ο : Type} [Fintype ι] [Fintype ο] {s : ℕ}
   {f g : (ι → Bool) → (ο → Bool)} (hfg : ∀ x j, f x j = g x j) (hf : EC s f) :
   EC s g := by
 have : f = g := funext (fun x => funext (hfg x))
 rwa [← this]
lemma ec_le {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 : ℕ} {f : (ι → Bool) → (ο → Bool)}
   (hf : EC s1 f) (hle : s1 ≤ s2) : EC s2 f :=
 ec_mono hle hf
lemma ec_proj {ι ο : Type} [Fintype ι] [Fintype ο] (p : ο → ι) :
   EC 0 (fun (x : ι → Bool) j => x (p j)) :=
 mc_proj (fun j : Fin (Fintype.card ο) => Fintype.equivFin ι (p ((Fintype.equivFin ο).symm j)))
lemma ec_id {ι : Type} [Fintype ι] : EC 0 (fun (x : ι → Bool) => x) :=
 ec_proj id
lemma ec_const {ι ο : Type} [Fintype ι] [Fintype ο] (c : ο → Bool) :
   EC 2 (fun (_ : ι → Bool) => c) :=
 mc_const (fun j => c ((Fintype.equivFin ο).symm j))
lemma ec_comp {ι μ ο : Type} [Fintype ι] [Fintype μ] [Fintype ο] {s1 s2 : ℕ}
   {f : (ι → Bool) → (μ → Bool)} {g : (μ → Bool) → (ο → Bool)}
   (hf : EC s1 f) (hg : EC s2 g) :
   EC (s1 + s2) (fun x => g (f x)) := by
 unfold EC at hf hg ⊢
 have h := mc_comp hf hg
 have heq : (fun (x : Fin (Fintype.card ι) → Bool) j =>
     g (fun i => f (fun a => x (Fintype.equivFin ι a))
       ((Fintype.equivFin μ).symm (Fintype.equivFin μ i))) ((Fintype.equivFin ο).symm j)) =
     (fun (x : Fin (Fintype.card ι) → Bool) j =>
       g (f (fun i => x (Fintype.equivFin ι i))) ((Fintype.equivFin ο).symm j)) := by
   funext x j; simp
 rwa [heq] at h
lemma ec_pair {ι ο1 ο2 : Type} [Fintype ι] [Fintype ο1] [Fintype ο2] {s1 s2 : ℕ}
   {f1 : (ι → Bool) → (ο1 → Bool)} {f2 : (ι → Bool) → (ο2 → Bool)}
   (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (s1 + s2) (fun x => Sum.elim (f1 x) (f2 x)) := by
 unfold EC at h1 h2 ⊢
 let L1 := Fintype.card ο1
 let L2 := Fintype.card ο2
 have hp := mc_pair h1 h2
 let idx : Fin (Fintype.card (ο1 ⊕ ο2)) → Fin (L1 + L2) := fun j =>
   match (Fintype.equivFin (ο1 ⊕ ο2)).symm j with
   | inl a => ⟨(Fintype.equivFin ο1 a).val, by have := (Fintype.equivFin ο1 a).isLt; omega⟩
   | inr b => ⟨L1 + (Fintype.equivFin ο2 b).val, by have := (Fintype.equivFin ο2 b).isLt; omega⟩
 have hcomp := mc_comp hp (mc_proj idx)
 rw [add_zero] at hcomp
 have heq : (fun (x : Fin (Fintype.card ι) → Bool) j =>
     (if hi : (idx j).val < L1 then
       f1 (fun i => x (Fintype.equivFin ι i)) ((Fintype.equivFin ο1).symm ⟨(idx j).val, hi⟩)
      else
       f2 (fun i => x (Fintype.equivFin ι i))
         ((Fintype.equivFin ο2).symm ⟨(idx j).val - L1, by omega⟩))) =
     (fun (x : Fin (Fintype.card ι) → Bool) j =>
       Sum.elim (f1 (fun i => x (Fintype.equivFin ι i)))
         (f2 (fun i => x (Fintype.equivFin ι i))) ((Fintype.equivFin (ο1 ⊕ ο2)).symm j)) := by
   funext x j
   rcases hq : (Fintype.equivFin (ο1 ⊕ ο2)).symm j with a | b
   · have hlt : (Fintype.equivFin ο1 a).val < L1 := (Fintype.equivFin ο1 a).isLt
     simp only [idx, hq, hlt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply, Sum.elim_inl]
   · have hnot : ¬ (L1 + (Fintype.equivFin ο2 b).val < L1) := by omega
     simp only [idx, hq, hnot, ↓reduceDIte, Sum.elim_inr]
     congr 1
     have hfin : (⟨L1 + (Fintype.equivFin ο2 b).val - L1, by omega⟩ : Fin L2) =
         Fintype.equivFin ο2 b := Fin.ext (by dsimp; omega)
     rw [hfin, Equiv.symm_apply_apply]
 rwa [heq] at hcomp
lemma ec_let {ι μ ο : Type} [Fintype ι] [Fintype μ] [Fintype ο] {s1 s2 : ℕ}
   {f : (ι → Bool) → (μ → Bool)} {g : (ι ⊕ μ → Bool) → (ο → Bool)}
   (hf : EC s1 f) (hg : EC s2 g) :
   EC (s1 + s2) (fun x => g (Sum.elim x (f x))) := by
 have hp := ec_pair (ec_id (ι := ι)) hf
 rw [zero_add] at hp
 exact ec_comp hp hg
lemma ec_family_fin {ι ο : Type} [Fintype ι] [Fintype ο] {M s : ℕ}
   {f : Fin M → (ι → Bool) → (ο → Bool)}
   (hf : ∀ a : Fin M, EC s (f a)) :
   EC (M * s) (fun x (p : Fin M × ο) => f p.1 x p.2) := by
 induction M with
 | zero =>
   have h0 : EC 0 (fun (x : ι → Bool) (p : Fin 0 × ο) => x (Fin.elim0 p.1)) :=
     ec_proj (fun p => Fin.elim0 p.1)
   rw [zero_mul]
   exact ec_eq (fun x p => Fin.elim0 p.1) h0
 | succ M ih =>
   have hhead : EC s (f 0) := hf 0
   have htail : EC (M * s) (fun x (p : Fin M × ο) => f p.1.succ x p.2) :=
     ih (fun a => hf a.succ)
   have hpair := ec_pair hhead htail
   let sel : Fin (M + 1) × ο → ο ⊕ (Fin M × ο) := fun p =>
     Fin.cases (inl p.2) (fun j => inr (j, p.2)) p.1
   have hres := ec_comp hpair (ec_proj sel)
   rw [add_zero, show s + M * s = (M + 1) * s by ring] at hres
   refine ec_eq ?_ hres
   intro x ⟨a, b⟩
   refine Fin.cases ?_ ?_ a <;> simp [sel]
lemma ec_family {α ι ο : Type} [Fintype α] [Fintype ι] [Fintype ο] {s : ℕ}
   {f : α → (ι → Bool) → (ο → Bool)}
   (hf : ∀ a : α, EC s (f a)) :
   EC (Fintype.card α * s) (fun x (p : α × ο) => f p.1 x p.2) := by
 let e := Fintype.equivFin α
 have hfin := ec_family_fin (fun j : Fin (Fintype.card α) => hf (e.symm j))
 have hres := ec_comp hfin (ec_proj (fun p : α × ο => (e p.1, p.2)))
 rw [add_zero] at hres
 refine ec_eq ?_ hres
 intro x ⟨a, b⟩
 simp [e]
lemma ec_finFold {σ : Type} [Fintype σ] {M s : ℕ}
   {step : Fin M → (σ → Bool) → (σ → Bool)}
   (hstep : ∀ i : Fin M, EC s (step i)) :
   EC (M * s) (fun x => (List.finRange M).foldl (fun st i => step i st) x) := by
 have htake : ∀ m (hm : m ≤ M),
     EC (m * s) (fun x => ((List.finRange M).take m).foldl (fun st i => step i st) x) := by
   intro m
   induction m with
   | zero => intro _; simpa using ec_id (ι := σ)
   | succ m ih =>
     intro hm
     have h1 := ih (by omega)
     have h2 := hstep ⟨m, hm⟩
     have hcomp := ec_comp h1 h2
     rw [show m * s + s = (m + 1) * s by ring] at hcomp
     refine ec_eq ?_ hcomp
     intro x j
     have htk : (List.finRange M).take (m + 1) =
         (List.finRange M).take m ++ [(List.finRange M)[m]'(by simp; omega)] :=
       List.take_succ_eq_append_getElem (by simp; omega)
     rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
     simp
 have h := htake M le_rfl
 rwa [show (List.finRange M).take M = List.finRange M by
   rw [List.take_of_length_le]; simp] at h
lemma ec_not1 : EC 1 (fun (x : Unit → Bool) (_ : Unit) => !(x ())) := by
 unfold EC
 have h := mc_comp (mc_proj (fun (_ : Fin 1) => (0 : Fin (Fintype.card Unit)))) mc_not
 rw [zero_add] at h
 have heq : (fun (x : Fin (Fintype.card Unit) → Bool) (_ : Fin 1) =>
     !(x (0 : Fin (Fintype.card Unit)))) =
     (fun (x : Fin (Fintype.card Unit) → Bool) (_ : Fin (Fintype.card Unit)) =>
       !(x (Fintype.equivFin Unit ()))) := by
   funext x j
   congr 1
   apply congrArg x
   apply Fin.ext
   have hlt := (Fintype.equivFin Unit ()).isLt
   simp only [Fintype.card_unit] at hlt
   change 0 = (Fintype.equivFin Unit ()).val
   omega
 exact heq ▸ h
lemma ec_and1 : EC 1 (fun (x : Bool → Bool) (_ : Unit) => x false && x true) := by
 unfold EC
 let idx : Fin 2 → Fin (Fintype.card Bool) := fun i =>
   if i = 0 then Fintype.equivFin Bool false else Fintype.equivFin Bool true
 have h := mc_comp (mc_proj idx) mc_and
 rw [zero_add] at h
 have heq : (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin 1) =>
     x (idx 0) && x (idx 1)) =
     (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin (Fintype.card Unit)) =>
       x (Fintype.equivFin Bool false) && x (Fintype.equivFin Bool true)) := by
   funext x j; simp [idx]
 exact heq ▸ h
lemma ec_or1 : EC 1 (fun (x : Bool → Bool) (_ : Unit) => x false || x true) := by
 unfold EC
 let idx : Fin 2 → Fin (Fintype.card Bool) := fun i =>
   if i = 0 then Fintype.equivFin Bool false else Fintype.equivFin Bool true
 have h := mc_comp (mc_proj idx) mc_or
 rw [zero_add] at h
 have heq : (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin 1) =>
     x (idx 0) || x (idx 1)) =
     (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin (Fintype.card Unit)) =>
       x (Fintype.equivFin Bool false) || x (Fintype.equivFin Bool true)) := by
   funext x j; simp [idx]
 exact heq ▸ h
lemma ec_xor1 : EC 5 (fun (x : Bool → Bool) (_ : Unit) => xor (x false) (x true)) := by
 unfold EC
 let idx : Fin 2 → Fin (Fintype.card Bool) := fun i =>
   if i = 0 then Fintype.equivFin Bool false else Fintype.equivFin Bool true
 have h := mc_comp (mc_proj idx) mc_xor
 rw [zero_add] at h
 have heq : (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin 1) =>
     xor (x (idx 0)) (x (idx 1))) =
     (fun (x : Fin (Fintype.card Bool) → Bool) (_ : Fin (Fintype.card Unit)) =>
       xor (x (Fintype.equivFin Bool false)) (x (Fintype.equivFin Bool true))) := by
   funext x j; simp [idx]
 exact heq ▸ h
lemma ec_ite1 : EC 4 (fun (x : Fin 3 → Bool) (_ : Unit) => if x 0 then x 1 else x 2) := by
 unfold EC
 let idx : Fin 3 → Fin (Fintype.card (Fin 3)) := fun i => Fintype.equivFin (Fin 3) i
 have h := mc_comp (mc_proj idx) mc_ite
 rw [zero_add] at h
 have heq : (fun (x : Fin (Fintype.card (Fin 3)) → Bool) (_ : Fin 1) =>
     if x (idx 0) then x (idx 1) else x (idx 2)) =
     (fun (x : Fin (Fintype.card (Fin 3)) → Bool) (_ : Fin (Fintype.card Unit)) =>
       if x (Fintype.equivFin (Fin 3) 0) then x (Fintype.equivFin (Fin 3) 1)
       else x (Fintype.equivFin (Fin 3) 2)) := by
   funext x j; rfl
 exact heq ▸ h
lemma ec_not_of {ι ο : Type} [Fintype ι] [Fintype ο] {s : ℕ}
   {f : (ι → Bool) → (ο → Bool)} (hf : EC s f) :
   EC (s + Fintype.card ο) (fun x j => !(f x j)) := by
 have hfam : EC (Fintype.card ο * 1)
     (fun (y : ο → Bool) (p : ο × Unit) => !(y p.1)) :=
   ec_family (f := fun (j : ο) (y : ο → Bool) (_ : Unit) => !(y j))
     (fun j => ec_comp (ec_proj (fun (_ : Unit) => j)) ec_not1)
 have h1 := ec_comp hfam (ec_proj (fun j : ο => (j, ())))
 rw [mul_one, add_zero] at h1
 exact ec_comp hf h1
lemma ec_bin_of {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 sb : ℕ}
   {op : Bool → Bool → Bool}
   (hop : EC sb (fun (x : Bool → Bool) (_ : Unit) => op (x false) (x true)))
   {f1 f2 : (ι → Bool) → (ο → Bool)} (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (s1 + s2 + Fintype.card ο * sb) (fun x j => op (f1 x j) (f2 x j)) := by
 have hpair := ec_pair h1 h2
 have hfam : EC (Fintype.card ο * sb)
     (fun (y : ο ⊕ ο → Bool) (p : ο × Unit) => op (y (inl p.1)) (y (inr p.1))) :=
   ec_family (f := fun (j : ο) (y : ο ⊕ ο → Bool) (_ : Unit) => op (y (inl j)) (y (inr j)))
     (fun j => by
       have hsel : EC 0 (fun (y : ο ⊕ ο → Bool) (b : Bool) =>
           y (if b then inr j else inl j)) := ec_proj _
       have hc := ec_comp hsel hop
       rw [zero_add] at hc
       simpa using hc)
 have hpost := ec_comp hfam (ec_proj (fun j : ο => (j, ())))
 rw [add_zero] at hpost
 have htot := ec_comp hpair hpost
 simpa using htot
lemma ec_and_of {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 : ℕ}
   {f1 f2 : (ι → Bool) → (ο → Bool)} (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (s1 + s2 + Fintype.card ο) (fun x j => f1 x j && f2 x j) := by
 simpa [mul_one] using ec_bin_of ec_and1 h1 h2
lemma ec_or_of {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 : ℕ}
   {f1 f2 : (ι → Bool) → (ο → Bool)} (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (s1 + s2 + Fintype.card ο) (fun x j => f1 x j || f2 x j) := by
 simpa [mul_one] using ec_bin_of ec_or1 h1 h2
lemma ec_xor_of {ι ο : Type} [Fintype ι] [Fintype ο] {s1 s2 : ℕ}
   {f1 f2 : (ι → Bool) → (ο → Bool)} (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (s1 + s2 + Fintype.card ο * 5) (fun x j => xor (f1 x j) (f2 x j)) :=
 ec_bin_of ec_xor1 h1 h2
lemma ec_ite_of {ι ο : Type} [Fintype ι] [Fintype ο] {sc s1 s2 : ℕ}
   {fc f1 f2 : (ι → Bool) → (ο → Bool)}
   (hc : EC sc fc) (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (sc + s1 + s2 + Fintype.card ο * 4)
     (fun x j => if fc x j then f1 x j else f2 x j) := by
 have hp := ec_pair (ec_pair hc h1) h2
 have hfam : EC (Fintype.card ο * 4)
     (fun (y : (ο ⊕ ο) ⊕ ο → Bool) (p : ο × Unit) =>
       if y (inl (inl p.1)) then y (inl (inr p.1)) else y (inr p.1)) :=
   ec_family (f := fun (j : ο) (y : (ο ⊕ ο) ⊕ ο → Bool) (_ : Unit) =>
       if y (inl (inl j)) then y (inl (inr j)) else y (inr j))
     (fun j => by
       let sel : Fin 3 → (ο ⊕ ο) ⊕ ο := fun r =>
         if r = 0 then inl (inl j)
         else if r = 1 then inl (inr j)
         else inr j
       have hcomp := ec_comp (ec_proj sel) ec_ite1
       rw [zero_add] at hcomp
       refine ec_eq ?_ hcomp
       intro y u; rfl)
 have hpost := ec_comp hfam (ec_proj (fun j : ο => (j, ())))
 rw [add_zero] at hpost
 have htot := ec_comp hp hpost
 refine ec_eq ?_ htot
 intro x j; rfl
lemma ec_ite_scalar {ι ο : Type} [Fintype ι] [Fintype ο] {sc s1 s2 : ℕ}
   {fc : (ι → Bool) → (Unit → Bool)} {f1 f2 : (ι → Bool) → (ο → Bool)}
   (hc : EC sc fc) (h1 : EC s1 f1) (h2 : EC s2 f2) :
   EC (sc + s1 + s2 + Fintype.card ο * 4)
     (fun x j => if fc x () then f1 x j else f2 x j) := by
 have hc' : EC sc (fun x (_ : ο) => fc x ()) := by
   simpa using ec_comp hc (ec_proj (fun (_ : ο) => ()))
 exact ec_ite_of hc' h1 h2
lemma ec_all_fin (M : ℕ) :
   EC (M + 2) (fun (x : Fin M → Bool) (_ : Unit) => decide (∀ i : Fin M, x i = true)) := by
 induction M with
 | zero =>
   have h := ec_const (ι := Fin 0) (fun (_ : Unit) => true)
   rw [zero_add]
   exact ec_eq (fun x u => by simp) h
 | succ M ih =>
   have h0 : EC 0 (fun (x : Fin (M + 1) → Bool) (_ : Unit) => x 0) :=
     ec_proj (fun _ => 0)
   have htail : EC (M + 2)
       (fun (x : Fin (M + 1) → Bool) (_ : Unit) => decide (∀ i : Fin M, x i.succ = true)) := by
     simpa using ec_comp (ec_proj Fin.succ) ih
   have hand := ec_and_of h0 htail
   rw [Fintype.card_unit, zero_add, show M + 2 + 1 = M + 1 + 2 by omega] at hand
   refine ec_eq ?_ hand
   intro x u
   cases hx0 : x 0 <;> simp [Fin.forall_fin_succ, hx0]
lemma ec_all {α : Type} [Fintype α] :
   EC (Fintype.card α + 2)
     (fun (x : α → Bool) (_ : Unit) => decide (∀ a : α, x a = true)) := by
 let e := Fintype.equivFin α
 have h := ec_comp (ec_proj e.symm) (ec_all_fin (Fintype.card α))
 rw [zero_add] at h
 refine ec_eq ?_ h
 intro x u
 simp only [decide_eq_decide]
 constructor
 · intro hall a; simpa using hall (e a)
 · intro hall i; exact hall (e.symm i)
lemma ec_any {α : Type} [Fintype α] :
   EC (2 * Fintype.card α + 3)
     (fun (x : α → Bool) (_ : Unit) => decide (∃ a : α, x a = true)) := by
 have h1 : EC (Fintype.card α) (fun (x : α → Bool) a => !(x a)) := by
   simpa using ec_not_of (ec_id (ι := α))
 have h2 := ec_comp h1 (ec_all (α := α))
 have h3 := ec_not_of h2
 rw [Fintype.card_unit] at h3
 have hsz : Fintype.card α + (Fintype.card α + 2) + 1 = 2 * Fintype.card α + 3 := by omega
 rw [hsz] at h3
 refine ec_eq ?_ h3
 intro x u
 by_cases hex : ∃ a : α, x a = true
 · rcases hex with ⟨a, ha⟩
   have hnot : ¬ ∀ b : α, (!(x b)) = true := by
     intro hall; have := hall a; simp [ha] at this
   simp [show ∃ a, x a = true from ⟨a, ha⟩]
 · push Not at hex
   have hall : ∀ b : α, (!(x b)) = true := by
     intro b; cases hb : x b
     · rfl
     · exact absurd hb (hex b)
   have hne : ¬ ∃ a : α, x a = true := fun ⟨a, ha⟩ => hex a ha
   simp [hall, hne]
lemma ec_zmod2Sum_fin (M : ℕ) :
   EC (5 * M + 2)
     (fun (x : Fin M → Bool) (_ : Unit) => z2b (∑ i : Fin M, b2z (x i))) := by
 induction M with
 | zero =>
   have h := ec_const (ι := Fin 0) (fun (_ : Unit) => false)
   rw [mul_zero, zero_add]
   exact ec_eq (fun x u => by simp [z2b]) h
 | succ M ih =>
   have h0 : EC 0 (fun (x : Fin (M + 1) → Bool) (_ : Unit) => x 0) :=
     ec_proj (fun _ => 0)
   have htail : EC (5 * M + 2)
       (fun (x : Fin (M + 1) → Bool) (_ : Unit) => z2b (∑ i : Fin M, b2z (x i.succ))) := by
     simpa using ec_comp (ec_proj Fin.succ) ih
   have hxor := ec_xor_of h0 htail
   rw [Fintype.card_unit, one_mul, zero_add, show 5 * M + 2 + 5 = 5 * (M + 1) + 2 by omega] at hxor
   refine ec_eq ?_ hxor
   intro x u
   rw [Fin.sum_univ_succ, z2b_add, z2b_b2z]
abbrev RIdx (R C : ℕ) := (Fin R × Fin C) ⊕ Fin R ⊕ Fin C
def rrefA {R C : ℕ} (st : RIdx R C → Bool) (i : Fin R) (j : Fin C) : Bool :=
 st (inl (i, j))
def rrefRow {R C : ℕ} (st : RIdx R C → Bool) (i : Fin R) (j : Fin C) : ZMod 2 :=
 b2z (rrefA st i j)
def rrefUsed {R C : ℕ} (st : RIdx R C → Bool) (i : Fin R) : Bool :=
 st (inr (inl i))
def rPC {R C : ℕ} (st : RIdx R C → Bool) (j : Fin C) : Bool :=
 st (inr (inr j))
def rrefInit {R C : ℕ} (A : Fin R × Fin C → Bool) : RIdx R C → Bool :=
 Sum.elim A (Sum.elim (fun _ => false) (fun _ => false))
def rrefStep {R C : ℕ} (c : Fin C) (st : RIdx R C → Bool) : RIdx R C → Bool :=
 let cand : Fin R → Bool := fun i => (!rrefUsed st i) && rrefA st i c
 let first : Fin R → Bool := fun i =>
   cand i && decide (∀ j : Fin R, j.val < i.val → cand j = false)
 let hasPiv : Bool := decide (∃ i : Fin R, cand i = true)
 let pivRow : Fin C → Bool := fun j => decide (∃ i : Fin R, first i = true ∧ rrefA st i j = true)
 Sum.elim
   (fun p => if (!first p.1) && rrefA st p.1 c then xor (rrefA st p.1 p.2) (pivRow p.2) else rrefA st p.1 p.2)
   (Sum.elim
     (fun i => rrefUsed st i || first i)
     (fun j => if j = c then hasPiv else rPC st j))
def rref {R C : ℕ} (A : Fin R × Fin C → Bool) : RIdx R C → Bool :=
 (List.finRange C).foldl (fun st c => rrefStep c st) (rrefInit A)
lemma ec_rrefInit (R C : ℕ) : EC 4 (@rrefInit R C) := by
 have h1 := ec_const (ι := Fin R × Fin C) (fun (_ : Fin R) => false)
 have h2 := ec_const (ι := Fin R × Fin C) (fun (_ : Fin C) => false)
 have hp := ec_pair (ec_id (ι := Fin R × Fin C)) (ec_pair h1 h2)
 exact ec_mono (by omega) hp
lemma ec_rrefStep {R C : ℕ} (c : Fin C) :
   EC (30 * (R + 1) * (R + C + 1)) (@rrefStep R C c) := by
 have hused : EC 0 (fun (st : RIdx R C → Bool) (i : Fin R) => rrefUsed st i) :=
   ec_proj (fun i => inr (inl i))
 have hAc : EC 0 (fun (st : RIdx R C → Bool) (i : Fin R) => rrefA st i c) :=
   ec_proj (fun i => inl (i, c))
 have hcand : EC (2 * R)
     (fun (st : RIdx R C → Bool) (i : Fin R) => (!rrefUsed st i) && rrefA st i c) := by
   have h := ec_and_of (ec_not_of hused) hAc
   rw [Fintype.card_fin] at h
   exact ec_mono (by omega) h
 let S1 := RIdx R C ⊕ Fin R
 have hfirst : EC (R * (3 * R + 6))
     (fun (y : S1 → Bool) (i : Fin R) =>
       y (inr i) && decide (∀ j : Fin R, j.val < i.val → y (inr j) = false)) := by
   have hfam : EC (Fintype.card (Fin R) * (3 * R + 6))
       (fun (y : S1 → Bool) (p : Fin R × Unit) =>
         y (inr p.1) && decide (∀ j : Fin R, j.val < p.1.val → y (inr j) = false)) :=
     ec_family (f := fun (i : Fin R) (y : S1 → Bool) (_ : Unit) =>
         y (inr i) && decide (∀ j : Fin R, j.val < i.val → y (inr j) = false))
       (fun i => by
         have hci : EC 0 (fun (y : S1 → Bool) (_ : Unit) => y (inr i)) :=
           ec_proj (fun _ => inr i)
         have hcond : EC (2 * R + 2)
             (fun (y : S1 → Bool) (j : Fin R) => !(decide (j.val < i.val)) || !(y (inr j))) := by
           have h1 := ec_const (ι := S1) (fun j : Fin R => !(decide (j.val < i.val)))
           have h2 := ec_not_of (ec_proj (fun j : Fin R => (inr j : S1)))
           have h3 := ec_or_of h1 h2
           rw [Fintype.card_fin] at h3
           exact ec_mono (by omega) h3
         have hall := ec_comp hcond (ec_all (α := Fin R))
         rw [Fintype.card_fin] at hall
         have hlt : EC (3 * R + 4)
             (fun (y : S1 → Bool) (_ : Unit) =>
               decide (∀ j : Fin R, j.val < i.val → y (inr j) = false)) := by
           refine ec_mono (by omega) (ec_eq ?_ hall)
           intro y u
           simp only [decide_eq_decide]
           constructor
           · intro h j hji; have := h j; simp [hji] at this; exact this
           · intro h j; by_cases hji : j.val < i.val <;> simp [hji, h]
         have hand := ec_and_of hci hlt
         rw [Fintype.card_unit] at hand
         exact ec_mono (by omega) hand)
   rw [Fintype.card_fin] at hfam
   have hp := ec_comp hfam (ec_proj (fun i : Fin R => (i, ())))
   rw [add_zero] at hp; exact hp
 have hhasPiv : EC (2 * R + 3)
     (fun (y : S1 → Bool) (_ : Unit) => decide (∃ i : Fin R, y (inr i) = true)) := by
   have h := ec_comp (ec_proj (fun i : Fin R => (inr i : S1))) (ec_any (α := Fin R))
   rw [zero_add, Fintype.card_fin] at h
   exact ec_eq (fun y u => by simp [decide_eq_decide]) h
 let S2 := S1 ⊕ (Fin R ⊕ Unit)
 have hstep12 := ec_pair hfirst hhasPiv
 have hpivRow : EC (C * (3 * R + 3))
     (fun (z : S2 → Bool) (j : Fin C) =>
       decide (∃ i : Fin R, z (inr (inl i)) = true ∧
         z (inl (inl (inl (i, j)))) = true)) := by
   have hfam : EC (Fintype.card (Fin C) * (3 * R + 3))
       (fun (z : S2 → Bool) (p : Fin C × Unit) =>
         decide (∃ i : Fin R, z (inr (inl i)) = true ∧
           z (inl (inl (inl (i, p.1)))) = true)) :=
     ec_family (f := fun (j : Fin C) (z : S2 → Bool) (_ : Unit) =>
         decide (∃ i : Fin R, z (inr (inl i)) = true ∧
           z (inl (inl (inl (i, j)))) = true))
       (fun j => by
         have h1 : EC 0 (fun (z : S2 → Bool) (i : Fin R) => z (inr (inl i))) := ec_proj _
         have h2 : EC 0 (fun (z : S2 → Bool) (i : Fin R) =>
             z (inl (inl (inl (i, j))))) := ec_proj _
         have hand := ec_and_of h1 h2
         rw [Fintype.card_fin] at hand
         have hany := ec_comp hand (ec_any (α := Fin R))
         rw [Fintype.card_fin] at hany
         refine ec_mono (by omega) (ec_eq ?_ hany)
         intro z u; simp [Bool.and_eq_true])
   rw [Fintype.card_fin] at hfam
   have hp := ec_comp hfam (ec_proj (fun j : Fin C => (j, ())))
   rw [add_zero] at hp; exact hp
 let S3 := S2 ⊕ Fin C
 have hfinal : EC (12 * R * C + R)
     (fun (w : S3 → Bool) =>
       let A : Fin R → Fin C → Bool := fun i j => w (inl (inl (inl (inl (i, j)))))
       let used : Fin R → Bool := fun i => w (inl (inl (inl (inr (inl i)))))
       let pivCol : Fin C → Bool := fun j => w (inl (inl (inl (inr (inr j)))))
       let first : Fin R → Bool := fun i => w (inl (inr (inl i)))
       let hasPiv : Bool := w (inl (inr (inr ())))
       let pivRow : Fin C → Bool := fun j => w (inr j)
       Sum.elim
         (fun p : Fin R × Fin C => if (!first p.1) && A p.1 c then xor (A p.1 p.2) (pivRow p.2) else A p.1 p.2)
         (Sum.elim
           (fun i => used i || first i)
           (fun j => if j = c then hasPiv else pivCol j))) := by
   have hA' : EC (12 * R * C)
       (fun (w : S3 → Bool) (p : Fin R × Fin C) =>
         if (!(w (inl (inr (inl p.1))))) &&
             w (inl (inl (inl (inl (p.1, c)))))
         then xor (w (inl (inl (inl (inl p))))) (w (inr p.2))
         else w (inl (inl (inl (inl p))))) := by
     have hnf : EC (R * C) (fun (w : S3 → Bool) (p : Fin R × Fin C) =>
         !(w (inl (inr (inl p.1))))) := by
       have h := ec_not_of (ec_proj (fun p : Fin R × Fin C => (inl (inr (inl p.1)) : S3)))
       simpa [Fintype.card_prod] using h
     have hAc' : EC 0 (fun (w : S3 → Bool) (p : Fin R × Fin C) =>
         w (inl (inl (inl (inl (p.1, c)))))) := ec_proj _
     have hcond := ec_and_of hnf hAc'
     have hA0 : EC 0 (fun (w : S3 → Bool) (p : Fin R × Fin C) =>
         w (inl (inl (inl (inl p))))) := ec_proj _
     have hP0 : EC 0 (fun (w : S3 → Bool) (p : Fin R × Fin C) => w (inr p.2)) := ec_proj _
     have hxor := ec_xor_of hA0 hP0
     have hite := ec_ite_of hcond hxor hA0
     simp only [Fintype.card_prod, Fintype.card_fin] at hite
     exact ec_mono (by nlinarith) hite
   have hused' : EC R (fun (w : S3 → Bool) (i : Fin R) =>
       w (inl (inl (inl (inr (inl i))))) || w (inl (inr (inl i)))) := by
     have h := ec_or_of (ec_proj (fun i : Fin R => (inl (inl (inl (inr (inl i)))) : S3)))
       (ec_proj (fun i : Fin R => (inl (inr (inl i)) : S3)))
     simpa using h
   have hpiv' : EC 0 (fun (w : S3 → Bool) (j : Fin C) =>
       if j = c then w (inl (inr (inr ())))
       else w (inl (inl (inl (inr (inr j)))))) := by
     let sel : Fin C → S3 := fun j =>
       if j = c then inl (inr (inr ()))
       else inl (inl (inl (inr (inr j))))
     refine ec_eq ?_ (ec_proj sel)
     intro w j; dsimp only [sel]; split_ifs <;> rfl
   have hp := ec_pair hA' (ec_pair hused' hpiv')
   exact ec_mono (by omega) hp
 have h1 := ec_let hpivRow hfinal
 have h2 := ec_let hstep12 h1
 have h3 := ec_let hcand h2
 exact ec_mono (by nlinarith) h3
lemma ec_rref (R C : ℕ) : EC (4 + 30 * C * (R + 1) * (R + C + 1)) (@rref R C) := by
 have hfold := ec_finFold (fun c : Fin C => ec_rrefStep (R := R) c)
 have hcomp := ec_comp (ec_rrefInit R C) hfold
 exact ec_mono (by nlinarith) hcomp
def rrefInv {R C : ℕ} (A0 : Fin R × Fin C → Bool) (t : ℕ) (st : RIdx R C → Bool) : Prop :=
 Submodule.span (ZMod 2) (Set.range (rrefRow st)) =
   Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j)))) ∧
 (∀ v : Fin C → ZMod 2, (∀ i : Fin R, ∑ j : Fin C, rrefRow st i j * v j = 0) ↔
   (∀ i : Fin R, ∑ j : Fin C, b2z (A0 (i, j)) * v j = 0)) ∧
 (∀ i : Fin R, rrefUsed st i = false → ∀ j : Fin C, j.val < t → rrefRow st i j = 0) ∧
 (∀ j : Fin C, rPC st j = true → j.val < t) ∧
 (∀ j : Fin C, rPC st j = true → ∃ i : Fin R, rrefUsed st i = true ∧ rrefRow st i j = 1 ∧
   ∀ i' : Fin R, i' ≠ i → rrefRow st i' j = 0) ∧
 (∀ i : Fin R, rrefUsed st i = true → ∃ j : Fin C, rPC st j = true ∧ rrefRow st i j = 1 ∧
   ∀ j' : Fin C, rPC st j' = true → j' ≠ j → rrefRow st i j' = 0)
lemma rrefInv_init {R C : ℕ} (A0 : Fin R × Fin C → Bool) :
   rrefInv A0 0 (rrefInit A0) := by
 refine ⟨rfl, fun _ => Iff.rfl, ?_, ?_, ?_, ?_⟩
 · intro i _ j hj; omega
 · intro j hj; simp [rPC, rrefInit] at hj
 · intro j hj; simp [rPC, rrefInit] at hj
 · intro i hi; simp [rrefUsed, rrefInit] at hi
lemma rrefInv_step {R C : ℕ} (A0 : Fin R × Fin C → Bool) (t : ℕ) (ht : t < C)
   (st : RIdx R C → Bool) (hinv : rrefInv A0 t st) :
   rrefInv A0 (t + 1) (rrefStep ⟨t, ht⟩ st) := by
 let c : Fin C := ⟨t, ht⟩
 let st' := rrefStep c st
 let cand : Fin R → Bool := fun i => (!rrefUsed st i) && rrefA st i c
 let first : Fin R → Bool := fun i =>
   cand i && decide (∀ j : Fin R, j.val < i.val → cand j = false)
 let hasPiv : Bool := decide (∃ i : Fin R, cand i = true)
 let pivRow : Fin C → Bool := fun j => decide (∃ i : Fin R, first i = true ∧ rrefA st i j = true)
 obtain ⟨hspan, hker, hunused, hpivlt, hpivcol_ex, hused_ex⟩ := hinv
 by_cases hex : ∃ i : Fin R, cand i = true
 · have hhas : hasPiv = true := decide_eq_true hex
   have hmin_ex : ∃ p : Fin R, first p = true ∧ ∀ i : Fin R, first i = true → i = p := by
     have hne : (Finset.univ.filter (fun i : Fin R => cand i = true)).Nonempty := by
       obtain ⟨i, hi⟩ := hex
       exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
     let p := (Finset.univ.filter (fun i : Fin R => cand i = true)).min' hne
     have hp_mem : cand p = true := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
     have hp_min : ∀ j : Fin R, j.val < p.val → cand j = false := by
       intro j hjp
       by_contra hnot
       have hjc : cand j = true := by cases h : cand j <;> simp_all
       have hle : p ≤ j := Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjc⟩)
       exact absurd hjp (not_lt.mpr hle)
     have hfp : first p = true := by
       simp only [first, hp_mem, Bool.true_and, decide_eq_true_eq]
       exact hp_min
     refine ⟨p, hfp, fun i hi => ?_⟩
     simp only [first, Bool.and_eq_true, decide_eq_true_eq] at hi
     have hle : p ≤ i := Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.1⟩)
     by_contra hne_ip
     have hlt : p.val < i.val := lt_of_le_of_ne hle (fun h => hne_ip (Fin.ext h.symm))
     have := hi.2 p hlt
     rw [hp_mem] at this
     exact Bool.false_ne_true this.symm
   obtain ⟨p, hfp, hfp_uniq⟩ := hmin_ex
   have hp_cand : cand p = true := (Bool.and_eq_true _ _ |>.mp hfp).1
   have hp_unused : rrefUsed st p = false := by
     have h1 := (Bool.and_eq_true _ _ |>.mp hp_cand).1
     cases hu : rrefUsed st p <;> simp_all
   have hp_Ac : rrefA st p c = true := (Bool.and_eq_true _ _ |>.mp hp_cand).2
   have hpivRow_eq : ∀ j : Fin C, pivRow j = rrefA st p j := by
     intro j
     dsimp only [pivRow]
     cases hApj : rrefA st p j
     · simp only [decide_eq_false_iff_not]
       rintro ⟨i, hfi, hAij⟩
       have hip := hfp_uniq i hfi
       subst hip
       rw [hApj] at hAij
       exact Bool.false_ne_true hAij
     · exact decide_eq_true ⟨p, hfp, hApj⟩
   have hrow'_p : rrefRow st' p = rrefRow st p := by
     funext j
     change b2z (if (!first p) && rrefA st p c then xor (rrefA st p j) (pivRow j) else rrefA st p j) =
       b2z (rrefA st p j)
     simp [hfp]
   have hrow'_ne : ∀ i : Fin R, i ≠ p →
       rrefRow st' i = rrefRow st i + b2z (rrefA st i c) • rrefRow st p := by
     intro i hne
     have hfi : first i = false := by
       by_contra hnot
       have : first i = true := by cases h : first i <;> simp_all
       exact hne (hfp_uniq i this)
     funext j
     change b2z (if (!first i) && rrefA st i c then xor (rrefA st i j) (pivRow j) else rrefA st i j) =
       b2z (rrefA st i j) + b2z (rrefA st i c) * b2z (rrefA st p j)
     rw [hfi, hpivRow_eq j]
     cases hAic : rrefA st i c
     · simp [b2z]
     · simp only [Bool.not_false, Bool.true_and, ↓reduceIte, b2z_xor]
       simp [b2z]
   have hrow_of_row' : ∀ i : Fin R, i ≠ p →
       rrefRow st i = rrefRow st' i + b2z (rrefA st i c) • rrefRow st' p := by
     intro i hne
     rw [hrow'_p, hrow'_ne i hne, add_assoc]
     funext j
     simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zmod2_add_self, add_zero]
   have hspan' : Submodule.span (ZMod 2) (Set.range (rrefRow st')) =
       Submodule.span (ZMod 2) (Set.range (rrefRow st)) := by
     apply le_antisymm
     · rw [Submodule.span_le]
       rintro _ ⟨i, rfl⟩
       by_cases hip : i = p
       · rw [hip, hrow'_p]; exact Submodule.subset_span ⟨p, rfl⟩
       · rw [hrow'_ne i hip]
         exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
           (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
     · rw [Submodule.span_le]
       rintro _ ⟨i, rfl⟩
       by_cases hip : i = p
       · rw [hip, ← hrow'_p]; exact Submodule.subset_span ⟨p, rfl⟩
       · rw [hrow_of_row' i hip]
         exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
           (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
   have hker' : ∀ v : Fin C → ZMod 2,
       (∀ i : Fin R, ∑ j : Fin C, rrefRow st' i j * v j = 0) ↔
       (∀ i : Fin R, ∑ j : Fin C, rrefRow st i j * v j = 0) := by
     intro v
     constructor
     · intro h i
       by_cases hip : i = p
       · rw [hip]; simpa [hrow'_p] using h p
       · have h1 := h i
         have h2 := h p
         have heq : ∑ j : Fin C, rrefRow st i j * v j =
             (∑ j : Fin C, rrefRow st' i j * v j) +
             b2z (rrefA st i c) * (∑ j : Fin C, rrefRow st' p j * v j) := by
           rw [Finset.mul_sum, ← Finset.sum_add_distrib]
           apply Finset.sum_congr rfl
           intro j _
           rw [hrow_of_row' i hip]
           simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
           ring
         rw [heq, h1, h2]; ring
     · intro h i
       by_cases hip : i = p
       · rw [hip]; simpa [hrow'_p] using h p
       · have h1 := h i
         have h2 := h p
         have heq : ∑ j : Fin C, rrefRow st' i j * v j =
             (∑ j : Fin C, rrefRow st i j * v j) +
             b2z (rrefA st i c) * (∑ j : Fin C, rrefRow st p j * v j) := by
           rw [Finset.mul_sum, ← Finset.sum_add_distrib]
           apply Finset.sum_congr rfl
           intro j _
           rw [hrow'_ne i hip]
           simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
           ring
         rw [heq, h1, h2]; ring
   have hrow'_lt_t : ∀ i : Fin R, ∀ j : Fin C, j.val < t → rrefRow st' i j = rrefRow st i j := by
     intro i j hjt
     by_cases hip : i = p
     · rw [hip]; exact congrFun hrow'_p j
     · have hpj : rrefRow st p j = 0 := hunused p hp_unused j hjt
       rw [hrow'_ne i hip]
       simp [hpj]
   have hrow'_c_p : rrefRow st' p c = 1 := by
     rw [hrow'_p]; simp [rrefRow, hp_Ac, b2z]
   have hrow'_c_ne : ∀ i : Fin R, i ≠ p → rrefRow st' i c = 0 := by
     intro i hne
     rw [hrow'_ne i hne]
     simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rrefRow, hp_Ac, b2z, ↓reduceIte,
       mul_one, zmod2_add_self]
   have hused'_eq : ∀ i : Fin R, rrefUsed st' i = (rrefUsed st i || decide (i = p)) := by
     intro i
     change (rrefUsed st i || first i) = (rrefUsed st i || decide (i = p))
     by_cases hip : i = p
     · subst hip; simp [hfp]
     · have hfi : first i = false := by
         by_contra hnot
         have : first i = true := by
           cases h : first i
           · exact absurd h hnot
           · rfl
         exact hip (hfp_uniq i this)
       simp [hfi, hip]
   have hpivCol'_eq : ∀ j : Fin C, rPC st' j = (if j = c then true else rPC st j) := by
     intro j
     change (if j = c then hasPiv else rPC st j) = _
     rw [hhas]
   refine ⟨hspan'.trans hspan, fun v => (hker' v).trans (hker v), ?_, ?_, ?_, ?_⟩
   · intro i hui j hjt
     rw [hused'_eq] at hui
     have hui0 : rrefUsed st i = false := by
       cases h : rrefUsed st i
       · rfl
       · rw [h] at hui; simp at hui
     have hip : i ≠ p := by intro heq; subst heq; simp at hui
     by_cases hlt : j.val < t
     · rw [hrow'_lt_t i j hlt]
       exact hunused i hui0 j hlt
     · have hjc : j = c := Fin.ext (by dsimp [c]; omega)
       subst hjc
       exact hrow'_c_ne i hip
   · intro j hj
     rw [hpivCol'_eq] at hj
     by_cases hjc : j = c
     · subst hjc; dsimp [c]; omega
     · simp only [hjc, ↓reduceIte] at hj
       have := hpivlt j hj; omega
   · intro j hj
     rw [hpivCol'_eq] at hj
     by_cases hjc : j = c
     · subst hjc
       refine ⟨p, ?_, hrow'_c_p, hrow'_c_ne⟩
       rw [hused'_eq]; simp
     · simp only [hjc, ↓reduceIte] at hj
       have hjt : j.val < t := hpivlt j hj
       obtain ⟨i, hui, hrij, hzero⟩ := hpivcol_ex j hj
       refine ⟨i, ?_, ?_, ?_⟩
       · rw [hused'_eq, hui]; rfl
       · rw [hrow'_lt_t i j hjt]; exact hrij
       · intro i' hi'
         rw [hrow'_lt_t i' j hjt]
         exact hzero i' hi'
   · intro i hui
     rw [hused'_eq] at hui
     by_cases hip : i = p
     · subst i
       refine ⟨c, ?_, hrow'_c_p, ?_⟩
       · rw [hpivCol'_eq]; simp
       · intro j' hj' hne
         rw [hpivCol'_eq] at hj'
         simp only [hne, ↓reduceIte] at hj'
         have hjt : j'.val < t := hpivlt j' hj'
         rw [hrow'_lt_t p j' hjt]
         exact hunused p hp_unused j' hjt
     · simp only [hip, decide_false, Bool.or_false] at hui
       obtain ⟨j, hj, hrij, hzero⟩ := hused_ex i hui
       have hjt : j.val < t := hpivlt j hj
       have hjc : j ≠ c := by intro heq; subst heq; dsimp [c] at hjt; omega
       refine ⟨j, ?_, ?_, ?_⟩
       · rw [hpivCol'_eq]; simp [hjc, hj]
       · rw [hrow'_lt_t i j hjt]; exact hrij
       · intro j' hj' hne
         rw [hpivCol'_eq] at hj'
         by_cases hj'c : j' = c
         · subst hj'c; exact hrow'_c_ne i hip
         · simp only [hj'c, ↓reduceIte] at hj'
           rw [hrow'_lt_t i j' (hpivlt j' hj')]
           exact hzero j' hj' hne
 · push Not at hex
   have hcand0 : ∀ i : Fin R, cand i = false := by
     intro i; cases h : cand i
     · rfl
     · exact absurd h (hex i)
   have hfirst0 : ∀ i : Fin R, first i = false := fun i => by simp [first, hcand0 i]
   have hhas0 : hasPiv = false := by
     simp only [hasPiv, decide_eq_false_iff_not]
     rintro ⟨i, hi⟩; exact hex i hi
   have hpivRow0 : ∀ j : Fin C, pivRow j = false := by
     intro j
     simp only [pivRow, decide_eq_false_iff_not]
     rintro ⟨i, hfi, _⟩; rw [hfirst0 i] at hfi; exact Bool.false_ne_true hfi
   have hrow'_eq : rrefRow st' = rrefRow st := by
     funext i j
     change b2z (if (!first i) && rrefA st i c then xor (rrefA st i j) (pivRow j) else rrefA st i j) =
       b2z (rrefA st i j)
     rw [hpivRow0 j]
     by_cases hcond : (!first i) && rrefA st i c = true <;> simp
   have hused'_eq : rrefUsed st' = rrefUsed st := by
     funext i; change (rrefUsed st i || first i) = rrefUsed st i; simp [hfirst0 i]
   have hpivCol'_eq : rPC st' = rPC st := by
     funext j
     change (if j = c then hasPiv else rPC st j) = rPC st j
     by_cases hjc : j = c
     · subst hjc
       simp only [↓reduceIte, hhas0]
       by_contra hnot
       have hpc : rPC st c = true := by cases h : rPC st c <;> simp_all
       have := hpivlt c hpc
       dsimp [c] at this; omega
     · simp [hjc]
   refine ⟨by rw [hrow'_eq]; exact hspan, by rw [hrow'_eq]; exact hker, ?_, ?_, ?_, ?_⟩
   · intro i hui j hjt
     rw [hused'_eq] at hui
     rw [hrow'_eq]
     by_cases hlt : j.val < t
     · exact hunused i hui j hlt
     · have hjc : j = c := Fin.ext (by dsimp [c]; omega)
       subst hjc
       have hc0 := hcand0 i
       dsimp only [cand] at hc0
       rw [hui] at hc0
       simp only [Bool.not_false, Bool.true_and] at hc0
       simp [rrefRow, hc0, b2z]
   · intro j hj
     rw [hpivCol'_eq] at hj
     have := hpivlt j hj; omega
   · intro j hj
     rw [hpivCol'_eq] at hj
     rw [hused'_eq, hrow'_eq]
     exact hpivcol_ex j hj
   · intro i hi
     rw [hused'_eq] at hi
     rw [hpivCol'_eq, hrow'_eq]
     exact hused_ex i hi
lemma rrefInv_final {R C : ℕ} (A0 : Fin R × Fin C → Bool) :
   rrefInv A0 C (rref A0) := by
 have htake : ∀ t (ht : t ≤ C),
     rrefInv A0 t (((List.finRange C).take t).foldl (fun st c => rrefStep c st) (rrefInit A0)) := by
   intro t
   induction t with
   | zero => intro _; simpa using rrefInv_init A0
   | succ t ih =>
     intro ht
     have htk : (List.finRange C).take (t + 1) =
         (List.finRange C).take t ++ [(List.finRange C)[t]'(by simp; omega)] :=
       List.take_succ_eq_append_getElem (by simp; omega)
     rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
     have hget : (List.finRange C)[t]'(by simp; omega) = ⟨t, ht⟩ := by simp
     rw [hget]
     exact rrefInv_step A0 t ht _ (ih (by omega))
 have h := htake C le_rfl
 rwa [show (List.finRange C).take C = List.finRange C by rw [List.take_of_length_le]; simp] at h
lemma rref_used_basis {R C : ℕ} (A0 : Fin R × Fin C → Bool) :
   (∀ i : Fin R, rrefUsed (rref A0) i = false → rrefRow (rref A0) i = 0) ∧
   LinearIndependent (ZMod 2)
     (fun i : {i : Fin R // rrefUsed (rref A0) i = true} => rrefRow (rref A0) i.val) ∧
   Submodule.span (ZMod 2)
     (Set.range (fun i : {i : Fin R // rrefUsed (rref A0) i = true} => rrefRow (rref A0) i.val)) =
     Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j)))) ∧
   Module.finrank (ZMod 2)
     ↥(Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j))))) =
     (Finset.univ.filter (fun i : Fin R => rrefUsed (rref A0) i = true)).card ∧
   (Finset.univ.filter (fun i : Fin R => rrefUsed (rref A0) i = true)).card =
     (Finset.univ.filter (fun j : Fin C => rPC (rref A0) j = true)).card := by
 classical
 obtain ⟨hspan, _, hunused, _, hpivcol_ex, hused_ex⟩ := rrefInv_final A0
 have hzero : ∀ i : Fin R, rrefUsed (rref A0) i = false → rrefRow (rref A0) i = 0 := by
   intro i hui
   funext j
   exact hunused i hui j j.isLt
 have hli : LinearIndependent (ZMod 2)
     (fun i : {i : Fin R // rrefUsed (rref A0) i = true} => rrefRow (rref A0) i.val) := by
   rw [Fintype.linearIndependent_iff]
   intro g hg i
   obtain ⟨j, hj, hrij, _⟩ := hused_ex i.val i.property
   obtain ⟨i0, hi0u, hri0j, hi0zero⟩ := hpivcol_ex j hj
   have hii0 : i.val = i0 := by
     by_contra hne
     have := hi0zero i.val hne
     rw [hrij] at this
     exact one_ne_zero this
   have hgj := congrFun hg j
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgj
   rw [Finset.sum_eq_single i] at hgj
   · rw [hrij, mul_one] at hgj; exact hgj
   · intro i' _ hne
     have hne0 : i'.val ≠ i0 := fun h => hne (Subtype.ext (h.trans hii0.symm))
     rw [hi0zero i'.val hne0, mul_zero]
   · intro hi; exact absurd (Finset.mem_univ i) hi
 have hspan_used :
     Submodule.span (ZMod 2)
       (Set.range (fun i : {i : Fin R // rrefUsed (rref A0) i = true} => rrefRow (rref A0) i.val)) =
     Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j)))) := by
   rw [← hspan]
   apply le_antisymm
   · rw [Submodule.span_le]
     rintro _ ⟨i, rfl⟩
     exact Submodule.subset_span ⟨i.val, rfl⟩
   · rw [Submodule.span_le]
     rintro _ ⟨i, rfl⟩
     cases hui : rrefUsed (rref A0) i
     · rw [hzero i hui]; exact Submodule.zero_mem _
     · exact Submodule.subset_span ⟨⟨i, hui⟩, rfl⟩
 have hrank : Module.finrank (ZMod 2)
     ↥(Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j))))) =
     (Finset.univ.filter (fun i : Fin R => rrefUsed (rref A0) i = true)).card := by
   rw [← hspan_used, finrank_span_eq_card hli]
   rw [Fintype.card_subtype]
 have hbij_card : (Finset.univ.filter (fun i : Fin R => rrefUsed (rref A0) i = true)).card =
     (Finset.univ.filter (fun j : Fin C => rPC (rref A0) j = true)).card := by
   choose fP hfP_piv hfP_one hfP_zero using hused_ex
   choose fU hfU_used hfU_one hfU_zero using hpivcol_ex
   let e : {i : Fin R // rrefUsed (rref A0) i = true} ≃
       {j : Fin C // rPC (rref A0) j = true} :=
     { toFun := fun i => ⟨fP i.val i.property, hfP_piv i.val i.property⟩
       invFun := fun j => ⟨fU j.val j.property, hfU_used j.val j.property⟩
       left_inv := fun i => by
         apply Subtype.ext
         by_contra hne
         have h0 := hfU_zero (fP i.val i.property) (hfP_piv i.val i.property) i.val (Ne.symm hne)
         rw [hfP_one i.val i.property] at h0
         exact one_ne_zero h0
       right_inv := fun j => by
         apply Subtype.ext
         by_contra hne
         have h0 := hfP_zero (fU j.val j.property) (hfU_used j.val j.property) j.val j.property
           (Ne.symm hne)
         rw [hfU_one j.val j.property] at h0
         exact one_ne_zero h0 }
   have := Fintype.card_congr e
   rwa [Fintype.card_subtype, Fintype.card_subtype] at this
 exact ⟨hzero, hli, hspan_used, hrank, hbij_card⟩
def rNV {R C : ℕ} (st : RIdx R C → Bool) (f j : Fin C) : Bool :=
 if rPC st f then false
 else if rPC st j then
   decide (∃ i : Fin R, rrefUsed st i = true ∧ rrefA st i j = true ∧ rrefA st i f = true)
 else decide (j = f)
lemma rref_nullVecs_span_ker {R C : ℕ} (A0 : Fin R × Fin C → Bool) :
   (∀ f : Fin C, ∀ i : Fin R, ∑ j : Fin C, b2z (A0 (i, j)) * b2z (rNV (rref A0) f j) = 0) ∧
   (∀ v : Fin C → ZMod 2, (∀ i : Fin R, ∑ j : Fin C, b2z (A0 (i, j)) * v j = 0) →
     v ∈ Submodule.span (ZMod 2) (Set.range (fun f j => b2z (rNV (rref A0) f j)))) := by
 classical
 obtain ⟨_, hker, hunused, _, hpivcol_ex, hused_ex⟩ := rrefInv_final A0
 let st := rref A0
 let nv : Fin C → Fin C → ZMod 2 := fun f j => b2z (rNV st f j)
 have hnv_ker : ∀ f : Fin C, ∀ i : Fin R, ∑ j : Fin C, rrefRow st i j * nv f j = 0 := by
   intro f i
   cases hpf : rPC st f
   · cases hui : rrefUsed st i
     · apply Finset.sum_eq_zero
       intro j _
       rw [hunused i hui j j.isLt, zero_mul]
     · obtain ⟨j0, hj0piv, hrij0, hrij_other⟩ := hused_ex i hui
       obtain ⟨i0, hi0u, hri0j0, hi0zero⟩ := hpivcol_ex j0 hj0piv
       have hii0 : i = i0 := by
         by_contra hne
         have := hi0zero i hne
         rw [hrij0] at this; exact one_ne_zero this
       subst hii0
       have hj0ne : j0 ≠ f := by
         intro heq; subst heq; rw [hpf] at hj0piv; exact Bool.false_ne_true hj0piv
       have hnv_j0 : nv f j0 = rrefRow st i f := by
         change b2z (rNV st f j0) = b2z (rrefA st i f)
         unfold rNV
         rw [hpf, hj0piv]
         simp only [Bool.false_eq_true, ↓reduceIte]
         cases hAif : rrefA st i f
         · have hno : ¬ ∃ i' : Fin R, rrefUsed st i' = true ∧ rrefA st i' j0 = true ∧
               rrefA st i' f = true := by
             rintro ⟨i', hi'u, hAij0, hAif'⟩
             have hi'i : i' = i := by
               by_contra hne
               have := hi0zero i' hne
               simp only [rrefRow, b2z, ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true] at this
               change rrefA st i' j0 = false at this
               rw [this] at hAij0
               exact Bool.false_ne_true hAij0
             subst hi'i; rw [hAif] at hAif'; exact Bool.false_ne_true hAif'
           simp [hno]
         · have hex : ∃ i' : Fin R, rrefUsed st i' = true ∧ rrefA st i' j0 = true ∧
               rrefA st i' f = true :=
             ⟨i, hui, by
               cases h : rrefA st i j0
               · rw [rrefRow, h] at hrij0; exact absurd hrij0 (by decide)
               · rfl, hAif⟩
           simp [hex]
       have hnv_f : nv f f = 1 := by
         change b2z (rNV st f f) = 1
         unfold rNV
         rw [hpf]
         simp [b2z]
       have hother : ∀ j : Fin C, j ≠ j0 → j ≠ f → rrefRow st i j * nv f j = 0 := by
         intro j hnj0 hnf
         cases hpj : rPC st j
         · have hnv0 : nv f j = 0 := by
             change b2z (rNV st f j) = 0
             unfold rNV
             rw [hpf, hpj]
             simp [hnf, b2z]
           rw [hnv0, mul_zero]
         · rw [hrij_other j hpj hnj0, zero_mul]
       have hsum_pair : ∑ j : Fin C, rrefRow st i j * nv f j =
           rrefRow st i j0 * nv f j0 + rrefRow st i f * nv f f := by
         rw [← Finset.sum_subset (s₁ := {j0, f}) (Finset.subset_univ _)]
         · rw [Finset.sum_pair hj0ne]
         · intro j _ hnot
           simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
           exact hother j hnot.1 hnot.2
       rw [hsum_pair, hrij0, hnv_j0, hnv_f, one_mul, mul_one, zmod2_add_self]
   · apply Finset.sum_eq_zero
     intro j _
     have : nv f j = 0 := by
       change b2z (rNV st f j) = 0
       unfold rNV
       rw [hpf]
       simp [b2z]
     rw [this, mul_zero]
 refine ⟨fun f => (hker (nv f)).mp (hnv_ker f), ?_⟩
 intro v hv0
 have hv := (hker v).mpr hv0
 let w : Fin C → ZMod 2 := v - ∑ f : Fin C, (if rPC st f then (0 : ZMod 2) else v f) • nv f
 have hw_ker : ∀ i : Fin R, ∑ j : Fin C, rrefRow st i j * w j = 0 := by
   intro i
   have hlin : ∑ j : Fin C, rrefRow st i j * w j =
       (∑ j : Fin C, rrefRow st i j * v j) -
       ∑ f : Fin C, (if rPC st f then (0 : ZMod 2) else v f) *
         (∑ j : Fin C, rrefRow st i j * nv f j) := by
     simp only [w, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
       Finset.sum_sub_distrib]
     congr 1
     calc ∑ j : Fin C, rrefRow st i j *
           ∑ f : Fin C, (if rPC st f = true then (0 : ZMod 2) else v f) * nv f j
         = ∑ j : Fin C, ∑ f : Fin C,
             rrefRow st i j * ((if rPC st f = true then (0 : ZMod 2) else v f) * nv f j) := by
           apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
       _ = ∑ f : Fin C, ∑ j : Fin C,
             rrefRow st i j * ((if rPC st f = true then (0 : ZMod 2) else v f) * nv f j) :=
           Finset.sum_comm
       _ = ∑ f : Fin C, (if rPC st f = true then (0 : ZMod 2) else v f) *
             ∑ j : Fin C, rrefRow st i j * nv f j := by
           apply Finset.sum_congr rfl; intro f _
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl; intro j _; ring
   rw [hlin, hv i]
   have h0 : ∑ f : Fin C, (if rPC st f then (0 : ZMod 2) else v f) *
       (∑ j : Fin C, rrefRow st i j * nv f j) = 0 :=
     Finset.sum_eq_zero (fun f _ => by rw [hnv_ker f i, mul_zero])
   rw [h0, sub_zero]
 have hw_nonpiv : ∀ j : Fin C, rPC st j = false → w j = 0 := by
   intro j hpj
   simp only [w, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
   rw [Finset.sum_eq_single j]
   · have hnvjj : nv j j = 1 := by
       change b2z (rNV st j j) = 1
       unfold rNV; rw [hpj]; simp [b2z]
     simp [hpj, hnvjj]
   · intro f _ hfj
     cases hpf : rPC st f
     · have hnvfj : nv f j = 0 := by
         change b2z (rNV st f j) = 0
         unfold rNV; rw [hpf, hpj]; simp [Ne.symm hfj, b2z]
       rw [hnvfj, mul_zero]
     · simp
   · intro hj; exact absurd (Finset.mem_univ j) hj
 have hw_zero : w = 0 := by
   funext j
   cases hpj : rPC st j
   · exact hw_nonpiv j hpj
   · obtain ⟨i, hui, hrij, _⟩ := hpivcol_ex j hpj
     obtain ⟨j0, hj0p, hrij0, hrij_other⟩ := hused_ex i hui
     have hjj0 : j = j0 := by
       by_contra hne
       have := hrij_other j hpj hne
       rw [hrij] at this; exact one_ne_zero this
     subst hjj0
     have hwi := hw_ker i
     rw [Finset.sum_eq_single j] at hwi
     · rw [hrij, one_mul] at hwi; exact hwi
     · intro j' _ hne
       cases hpj' : rPC st j'
       · rw [hw_nonpiv j' hpj', mul_zero]
       · rw [hrij_other j' hpj' hne, zero_mul]
     · intro hj; exact absurd (Finset.mem_univ j) hj
 have hv_eq : v = ∑ f : Fin C, (if rPC st f then (0 : ZMod 2) else v f) • nv f :=
   sub_eq_zero.mp hw_zero
 rw [hv_eq]
 exact Submodule.sum_mem _ (fun f _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩))
lemma ec_rNV (R C : ℕ) :
   EC (C * C * (4 * R + 15) + 4)
     (fun (st : RIdx R C → Bool) (p : Fin C × Fin C) => rNV st p.1 p.2) := by
 have hfam : EC (Fintype.card (Fin C × Fin C) * (4 * R + 15))
     (fun (st : RIdx R C → Bool) (p : (Fin C × Fin C) × Unit) => rNV st p.1.1 p.1.2) :=
   ec_family (f := fun (p : Fin C × Fin C) (st : RIdx R C → Bool) (_ : Unit) =>
       rNV st p.1 p.2)
     (fun ⟨f, j⟩ => by
       have hpf : EC 0 (fun (st : RIdx R C → Bool) (_ : Unit) => rPC st f) := ec_proj _
       have hpj : EC 0 (fun (st : RIdx R C → Bool) (_ : Unit) => rPC st j) := ec_proj _
       have hfalse := ec_const (ι := RIdx R C) (fun (_ : Unit) => false)
       have heq := ec_const (ι := RIdx R C) (fun (_ : Unit) => decide (j = f))
       have hex : EC (4 * R + 3)
           (fun (st : RIdx R C → Bool) (_ : Unit) =>
             decide (∃ i : Fin R, rrefUsed st i = true ∧
               rrefA st i j = true ∧ rrefA st i f = true)) := by
         have h1 : EC 0 (fun (st : RIdx R C → Bool) (i : Fin R) => rrefUsed st i) := ec_proj _
         have h2 : EC 0 (fun (st : RIdx R C → Bool) (i : Fin R) => rrefA st i j) := ec_proj _
         have h3 : EC 0 (fun (st : RIdx R C → Bool) (i : Fin R) => rrefA st i f) := ec_proj _
         have ha1 := ec_and_of h2 h3
         have ha2 := ec_and_of h1 ha1
         rw [Fintype.card_fin] at ha1 ha2
         have hany := ec_comp ha2 (ec_any (α := Fin R))
         rw [Fintype.card_fin] at hany
         refine ec_mono (by omega) (ec_eq ?_ hany)
         intro st u; simp [Bool.and_eq_true]
       have hinner := ec_ite_scalar hpj hex heq
       have houter := ec_ite_scalar hpf hfalse hinner
       rw [Fintype.card_unit] at hinner houter
       exact ec_mono (by omega) houter)
 have hp := ec_comp hfam (ec_proj (fun p : Fin C × Fin C => (p, ())))
 simp only [Fintype.card_prod, Fintype.card_fin, add_zero] at hp
 exact ec_mono (by omega) hp
def bNat (L : ℕ) (x : Fin L → Bool) : ℕ :=
 ∑ i : Fin L, if x i then 2 ^ i.val else 0
def bitsVal (L : ℕ) (x : Fin L → Bool) : ZMod (2 ^ L) :=
 (bNat L x : ZMod (2 ^ L))
lemma bitsNat_succ (L : ℕ) (x : Fin (L + 1) → Bool) :
   bNat (L + 1) x = (if x 0 then 1 else 0) + 2 * bNat L (fun i => x i.succ) := by
 unfold bNat
 rw [Fin.sum_univ_succ, Finset.mul_sum]
 simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ']
 congr 1
 apply Finset.sum_congr rfl
 intro i _
 split_ifs <;> simp
lemma bNat_lt (L : ℕ) (x : Fin L → Bool) : bNat L x < 2 ^ L := by
 induction L with
 | zero => simp [bNat]
 | succ L ih =>
   rw [bitsNat_succ, pow_succ']
   have h := ih (fun i => x i.succ)
   cases x 0 <;> simp <;> omega
lemma bNat_tb (L : ℕ) (x : Fin L → Bool) (i : Fin L) :
   (bNat L x).testBit i.val = x i := by
 induction L with
 | zero => exact i.elim0
 | succ L ih =>
   rw [bitsNat_succ]
   refine Fin.cases ?_ ?_ i
   · simp only [Fin.val_zero, Nat.testBit_zero]
     cases x 0 <;> simp
   · intro j
     simp only [Fin.val_succ, Nat.testBit_succ]
     have hdiv : ((if x 0 = true then 1 else 0) + 2 * bNat L (fun r => x r.succ)) / 2 =
         bNat L (fun r => x r.succ) := by
       cases x 0
       · simp
       · simp; omega
     rw [hdiv]
     exact ih (fun r => x r.succ) j
lemma bitsNat_not_add (L : ℕ) (x : Fin L → Bool) :
   bNat L (fun i => !(x i)) + bNat L x = 2 ^ L - 1 := by
 induction L with
 | zero => simp [bNat]
 | succ L ih =>
   rw [bitsNat_succ, bitsNat_succ]
   have h := ih (fun i => x i.succ)
   have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
   rw [pow_succ']
   cases x 0 <;> simp <;> omega
def bAC : (L : ℕ) → (Fin L ⊕ Fin L ⊕ Unit → Bool) → (Fin L ⊕ Unit → Bool)
 | 0, inp => Sum.elim Fin.elim0 (fun _ => inp (inr (inr ())))
 | L + 1, inp =>
   let x0 := inp (inl 0)
   let y0 := inp (inr (inl 0))
   let cin := inp (inr (inr ()))
   let s0 := xor (xor x0 y0) cin
   let c1 := (x0 && y0) || (cin && (x0 || y0))
   let tailInp : Fin L ⊕ Fin L ⊕ Unit → Bool :=
     Sum.elim (fun i => inp (inl i.succ))
       (Sum.elim (fun i => inp (inr (inl i.succ))) (fun _ => c1))
   let tailOut := bAC L tailInp
   Sum.elim (Fin.cases s0 (fun i => tailOut (inl i))) (fun _ => tailOut (inr ()))
lemma bAC_sp (L : ℕ) (x y : Fin L → Bool) (cin : Bool) :
   let out := bAC L (Sum.elim x (Sum.elim y (fun _ => cin)))
   bNat L (fun i => out (inl i)) + 2 ^ L * (if out (inr ()) then 1 else 0) =
     bNat L x + bNat L y + (if cin then 1 else 0) := by
 induction L generalizing cin with
 | zero =>
   dsimp only [bAC]
   simp [bNat]
   rfl
 | succ L ih =>
   dsimp only [bAC]
   set x0 := x 0
   set y0 := y 0
   set s0 := xor (xor x0 y0) cin
   set c1 := (x0 && y0) || (cin && (x0 || y0))
   have hbit_gen : ∀ a b c : Bool,
       (if xor (xor a b) c then 1 else 0) + 2 * (if (a && b) || (c && (a || b)) then 1 else 0) =
         (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
     decide
   have hbit : (if s0 then 1 else 0) + 2 * (if c1 then 1 else 0) =
       (if x0 then 1 else 0) + (if y0 then 1 else 0) + (if cin then 1 else 0) :=
     hbit_gen x0 y0 cin
   have htail := ih (fun i => x i.succ) (fun i => y i.succ) c1
   dsimp only at htail
   rw [bitsNat_succ, bitsNat_succ, bitsNat_succ]
   change ((if s0 then 1 else 0) +
       2 * bNat L (fun i =>
         bAC L (Sum.elim (fun i => x i.succ) (Sum.elim (fun i => y i.succ) (fun _ => c1))) (inl i))) +
       2 ^ (L + 1) * (if bAC L (Sum.elim (fun i => x i.succ) (Sum.elim (fun i => y i.succ) (fun _ => c1))) (inr ()) then 1 else 0) =
     ((if x0 then 1 else 0) + 2 * bNat L (fun i => x i.succ)) +
     ((if y0 then 1 else 0) + 2 * bNat L (fun i => y i.succ)) + (if cin then 1 else 0)
   rw [pow_succ', add_assoc, mul_assoc 2 (2 ^ L), ← mul_add, htail]
   omega
lemma ec_bAC (L : ℕ) : EC (18 * L) (bAC L) := by
 induction L with
 | zero =>
   let sel : Fin 0 ⊕ Unit → Fin 0 ⊕ Fin 0 ⊕ Unit :=
     Sum.elim Fin.elim0 (fun _ => inr (inr ()))
   have h := ec_proj sel
   refine ec_le (ec_eq ?_ h) (by omega)
   intro inp q
   rcases q with i | u
   · exact i.elim0
   · rfl
 | succ L ih =>
   let I := Fin (L + 1) ⊕ Fin (L + 1) ⊕ Unit
   have hbit : EC 18
       (fun (inp : I → Bool) (q : Unit ⊕ Unit) =>
         let x0 := inp (inl 0)
         let y0 := inp (inr (inl 0))
         let cin := inp (inr (inr ()))
         Sum.elim (fun _ => xor (xor x0 y0) cin) (fun _ => (x0 && y0) || (cin && (x0 || y0))) q) := by
     have hx0 : EC 0 (fun (inp : I → Bool) (_ : Unit) => inp (inl 0)) := ec_proj _
     have hy0 : EC 0 (fun (inp : I → Bool) (_ : Unit) => inp (inr (inl 0))) := ec_proj _
     have hcin : EC 0 (fun (inp : I → Bool) (_ : Unit) => inp (inr (inr ()))) := ec_proj _
     have hs0 := ec_xor_of (ec_xor_of hx0 hy0) hcin
     have hc1 := ec_or_of (ec_and_of hx0 hy0) (ec_and_of hcin (ec_or_of hx0 hy0))
     have hp := ec_pair hs0 hc1
     rw [Fintype.card_unit] at hp
     exact ec_le hp (by omega)
   let I1 := I ⊕ (Unit ⊕ Unit)
   let selTail : (Fin L ⊕ Fin L ⊕ Unit) → I1 := fun q =>
     match q with
     | inl i => inl (inl i.succ)
     | inr (inl i) => inl (inr (inl i.succ))
     | inr (inr _) => inr (inr ())
   have htail : EC (18 * L)
       (fun (y : I1 → Bool) => bAC L (fun q => y (selTail q))) := by
     have h := ec_comp (ec_proj selTail) ih
     rwa [zero_add] at h
   let I2 := I1 ⊕ (Fin L ⊕ Unit)
   let selOut : (Fin (L + 1) ⊕ Unit) → I2 := fun q =>
     match q with
     | inl i => Fin.cases (inl (inr (inl ()))) (fun j => inr (inl j)) i
     | inr _ => inr (inr ())
   have hstep := ec_let htail (ec_proj selOut)
   have htot := ec_let hbit hstep
   refine ec_le (ec_eq ?_ htot) (by omega)
   intro inp q
   have htail_inp :
       (fun q => Sum.elim inp (fun q => Sum.elim (fun _ => xor (xor (inp (inl 0)) (inp (inr (inl 0)))) (inp (inr (inr ()))))
           (fun _ => (inp (inl 0) && inp (inr (inl 0))) || (inp (inr (inr ())) && (inp (inl 0) || inp (inr (inl 0))))) q)
         (selTail q)) =
       Sum.elim (fun i : Fin L => inp (inl i.succ))
         (Sum.elim (fun i : Fin L => inp (inr (inl i.succ)))
           (fun _ => (inp (inl 0) && inp (inr (inl 0))) ||
             (inp (inr (inr ())) && (inp (inl 0) || inp (inr (inl 0)))))) := by
     funext r; rcases r with i | i | u <;> rfl
   rcases q with i | u
   · refine Fin.cases ?_ ?_ i
     · rfl
     · intro j
       dsimp only [bAC, selOut, Fin.cases_succ, Sum.elim_inr, Sum.elim_inl]
       rw [htail_inp]
   · dsimp only [bAC, selOut, Sum.elim_inr]
     rw [htail_inp]
def bvAdd (L : ℕ) (xy : Fin L ⊕ Fin L → Bool) (i : Fin L) : Bool :=
 bAC L (Sum.elim (xy ∘ inl) (Sum.elim (xy ∘ inr) (fun _ => false))) (inl i)
lemma bitsVal_bvAdd (L : ℕ) (x y : Fin L → Bool) :
   bitsVal L (bvAdd L (Sum.elim x y)) = bitsVal L x + bitsVal L y := by
 have h := bAC_sp L x y false
 dsimp only at h
 have hcast : ((bNat L (bvAdd L (Sum.elim x y)) +
     2 ^ L * (if bAC L (Sum.elim x (Sum.elim y (fun _ => false))) (inr ()) then 1 else 0) : ℕ) :
     ZMod (2 ^ L)) = ((bNat L x + bNat L y + 0 : ℕ) : ZMod (2 ^ L)) := by
   exact congrArg (Nat.cast (R := ZMod (2 ^ L))) h
 simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hcast
 exact hcast
lemma ec_bvAdd (L : ℕ) : EC (20 * (L + 1)) (bvAdd L) := by
 have hfalse := ec_const (ι := Fin L ⊕ Fin L) (fun (_ : Unit) => false)
 have hprep : EC 2
     (fun (xy : Fin L ⊕ Fin L → Bool) =>
       Sum.elim (xy ∘ inl) (Sum.elim (xy ∘ inr) (fun (_ : Unit) => false))) := by
   have hp := ec_pair (ec_proj (fun i : Fin L => (inl i : Fin L ⊕ Fin L)))
     (ec_pair (ec_proj (fun i : Fin L => (inr i : Fin L ⊕ Fin L))) hfalse)
   exact ec_le hp (by omega)
 have hcomp := ec_comp (ec_comp hprep (ec_bAC L))
   (ec_proj (ι := Fin L ⊕ Unit) (fun i : Fin L => inl i))
 exact ec_le hcomp (by omega)
def bvSumFin (M L : ℕ) (xs : Fin M × Fin L → Bool) : Fin L → Bool :=
 (List.finRange M).foldl (fun acc j => bvAdd L (Sum.elim acc (fun l => xs (j, l)))) (fun _ => false)
lemma bitsVal_bvSumFin (M L : ℕ) (xs : Fin M × Fin L → Bool) :
   bitsVal L (bvSumFin M L xs) = ∑ j : Fin M, bitsVal L (fun l => xs (j, l)) := by
 have hfold : ∀ (n : ℕ) (hn : n ≤ M),
     bitsVal L (((List.finRange M).take n).foldl
       (fun acc j => bvAdd L (Sum.elim acc (fun l => xs (j, l)))) (fun _ => false)) =
     ∑ j ∈ Finset.univ.filter (fun j : Fin M => j.val < n), bitsVal L (fun l => xs (j, l)) := by
   intro n
   induction n with
   | zero => intro _; simp [bitsVal, bNat]
   | succ n ih =>
     intro hn
     let jj : Fin M := ⟨n, hn⟩
     have htk : (List.finRange M).take (n + 1) = (List.finRange M).take n ++ [jj] := by
       have h1 := List.take_succ_eq_append_getElem (l := List.finRange M) (i := n) (by simp; omega)
       simpa [jj] using h1
     rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, bitsVal_bvAdd, ih (by omega)]
     have hfilt : Finset.univ.filter (fun j : Fin M => j.val < n + 1) =
         insert jj (Finset.univ.filter (fun j : Fin M => j.val < n)) := by
       ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
         Fin.ext_iff, jj]; omega
     have hnot : jj ∉ Finset.univ.filter (fun j : Fin M => j.val < n) := by simp [jj]
     rw [hfilt, Finset.sum_insert hnot, add_comm]
 have h := hfold M le_rfl
 rw [show (List.finRange M).take M = List.finRange M by rw [List.take_of_length_le]; simp] at h
 rw [show Finset.univ.filter (fun j : Fin M => j.val < M) = Finset.univ by
   ext j; simp] at h
 exact h
lemma ec_bvSumFin (M L : ℕ) : EC (2 + M * (20 * (L + 1))) (bvSumFin M L) := by
 have htake : ∀ n : ℕ,
     EC (2 + n * (20 * (L + 1)))
       (fun (xs : Fin M × Fin L → Bool) =>
         ((List.finRange M).take n).foldl
           (fun acc j => bvAdd L (Sum.elim acc (fun l => xs (j, l)))) (fun _ => false)) := by
   intro n
   induction n with
   | zero => simpa using ec_const (ι := Fin M × Fin L) (fun (_ : Fin L) => false)
   | succ n ih =>
     by_cases hn : n < M
     · let jj : Fin M := ⟨n, hn⟩
       let sel : Fin L ⊕ Fin L → (Fin M × Fin L) ⊕ Fin L :=
         Sum.elim (fun l => inr l) (fun l => inl (jj, l))
       have hstep := ec_comp (ec_proj sel) (ec_bvAdd L)
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) (by nlinarith)
       intro xs l
       have htk : (List.finRange M).take (n + 1) = (List.finRange M).take n ++ [jj] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange M) (i := n) (by simp; omega)
         simpa [jj] using h1
       simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
       congr 1; funext q; rcases q with r | r <;> rfl
     · have htk : (List.finRange M).take (n + 1) = (List.finRange M).take n := by
         rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
       refine ec_le (ec_eq ?_ ih) (by nlinarith)
       intro xs l; simp only [htk]
 have h := htake M
 rwa [show (List.finRange M).take M = List.finRange M by rw [List.take_of_length_le]; simp] at h
noncomputable def bvSum {α : Type} [Fintype α] (L : ℕ) (xs : α × Fin L → Bool) : Fin L → Bool :=
 bvSumFin (Fintype.card α) L (fun p => xs ((Fintype.equivFin α).symm p.1, p.2))
lemma bitsVal_bvSum {α : Type} [Fintype α] (L : ℕ) (xs : α × Fin L → Bool) :
   bitsVal L (bvSum L xs) = ∑ a : α, bitsVal L (fun l => xs (a, l)) := by
 unfold bvSum
 rw [bitsVal_bvSumFin]
 exact Equiv.sum_comp (Fintype.equivFin α).symm (fun a => bitsVal L (fun l => xs (a, l)))
lemma ec_bvSum {α : Type} [Fintype α] (L : ℕ) :
   EC (2 + Fintype.card α * (20 * (L + 1))) (@bvSum α _ L) := by
 have h := ec_comp (ec_proj (fun p : Fin (Fintype.card α) × Fin L => ((Fintype.equivFin α).symm p.1, p.2)))
   (ec_bvSumFin (Fintype.card α) L)
 rwa [zero_add] at h
lemma ec_to_circuit {n : ℕ} {ο : Type} [Fintype ο] {s : ℕ}
   {f : (Fin n → Bool) → (ο → Bool)} (hf : EC s f) :
   ∃ (C : Circuit) (out : ο → Fin (n + C.size)),
     FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ s ∧
     ∀ (bits : List Bool), bits.length = n →
       ∀ j : ο, (C.wires bits).getD (out j).val false = f (fun i => bits.getD i.val false) j := by
 let eI := Fintype.equivFin (Fin n)
 let eO := Fintype.equivFin ο
 unfold EC at hf
 have hcomp := mc_comp (mc_proj (fun k : Fin (Fintype.card (Fin n)) => eI.symm k)) hf
 rw [zero_add] at hcomp
 obtain ⟨C, outRaw, hF, hB, hS, hE⟩ := hcomp
 refine ⟨C, fun j => outRaw (eO j), hF, hB, hS, ?_⟩
 intro bits hlen j
 have hof : List.ofFn (fun i : Fin n => bits.getD i.val false) = bits := by
   apply List.ext_getElem
   · simp [hlen]
   · intro i hi1 hi2
     simp only [List.getElem_ofFn, List.getD_eq_getElem _ _ hi2]
 have he := hE (fun i : Fin n => bits.getD i.val false) (eO j)
 rw [hof] at he
 rw [he]
 dsimp only
 simp [eI, eO]
lemma gD_al {α : Type*} (l1 l2 : List α) (i : ℕ) (h : i < l1.length) (d : α) :
   (l1 ++ l2).getD i d = l1.getD i d := by
 rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
   List.getElem_append_left h, ← List.getD_eq_getElem _ _ h]
lemma gD_ar {α : Type*} (l1 l2 : List α) (i : ℕ) (h1 : l1.length ≤ i)
   (h2 : i - l1.length < l2.length) (d : α) :
   (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
 rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
   List.getElem_append_right h1, ← List.getD_eq_getElem _ _ h2]
lemma ec_to_eval_circuit {n : ℕ} {s : ℕ}
   {f : (Fin n → Bool) → (Unit → Bool)} (hf : EC s f) :
   ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ s ∧
     ∀ (bits : List Bool), bits.length = n →
       C.eval bits = f (fun i => bits.getD i.val false) () := by
 obtain ⟨C, out, hF, hB, hS, hE⟩ := ec_to_circuit hf
 refine ⟨⟨C.gates, (out ()).val⟩, hF, hB, hS, ?_⟩
 intro bits hlen
 exact hE bits hlen ()
lemma rrefInv_take {R C : ℕ} (A0 : Fin R × Fin C → Bool) (t : ℕ) (ht : t ≤ C) :
   rrefInv A0 t (((List.finRange C).take t).foldl (fun st c => rrefStep c st) (rrefInit A0)) := by
 induction t with
 | zero => simpa using rrefInv_init A0
 | succ t ih =>
   have htk : (List.finRange C).take (t + 1) =
       (List.finRange C).take t ++ [(List.finRange C)[t]'(by simp; omega)] :=
     List.take_succ_eq_append_getElem (by simp; omega)
   rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
   have hget : (List.finRange C)[t]'(by simp; omega) = ⟨t, ht⟩ := by simp
   rw [hget]
   exact rrefInv_step A0 t ht _ (ih (by omega))
lemma rref_in_rowSpace {R C : ℕ} (A0 : Fin R × Fin C → Bool) (v : Fin C → ZMod 2) :
   v ∈ Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j)))) ↔
     ∀ f : Fin C, ∑ j : Fin C, b2z (rNV (rref A0) f j) * v j = 0 := by
 classical
 let st := rref A0
 let Rsp : Submodule (ZMod 2) (Fin C → ZMod 2) :=
   Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j))))
 let T : (Fin C → ZMod 2) →ₗ[ZMod 2] (Fin C → ZMod 2) :=
   { toFun := fun u f => ∑ j : Fin C, b2z (rNV st f j) * u j
     map_add' := fun u w => by
       funext f; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := fun c u => by
       funext f; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
       apply Finset.sum_congr rfl; intro j _; ring }
 have hle : Rsp ≤ LinearMap.ker T := by
   rw [Submodule.span_le]
   rintro _ ⟨i, rfl⟩
   change (fun j => b2z (A0 (i, j))) ∈ LinearMap.ker T
   rw [LinearMap.mem_ker]
   funext f
   change ∑ j : Fin C, b2z (rNV st f j) * b2z (A0 (i, j)) = 0
   have hk := (rref_nullVecs_span_ker A0).1 f i
   simpa [mul_comm] using hk
 let evec : Fin C → (Fin C → ZMod 2) := fun a j => if j = a then 1 else 0
 have hli_range : LinearIndependent (ZMod 2)
     (fun f' : {f : Fin C // rPC st f = false} => T (evec f'.val)) := by
   rw [Fintype.linearIndependent_iff]
   intro g hg f'
   have hval := congrFun hg f'.val
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
   have hTsingle : ∀ a : {f : Fin C // rPC st f = false},
       T (evec a.val) f'.val = if a = f' then 1 else 0 := by
     intro a
     change ∑ j : Fin C, b2z (rNV st f'.val j) * (if j = a.val then 1 else 0) = _
     rw [Finset.sum_eq_single a.val]
     · simp only [↓reduceIte, mul_one]
       unfold rNV
       rw [f'.property, a.property]
       simp only [Bool.false_eq_true, ↓reduceIte]
       by_cases h : a = f'
       · subst h; simp [b2z]
       · have hne : a.val ≠ f'.val := fun he => h (Subtype.ext he)
         simp [h, hne, b2z]
     · intro j _ hne; simp [hne]
     · intro ha; exact absurd (Finset.mem_univ _) ha
   simp_rw [hTsingle] at hval
   simpa using hval
 have hrange_ge : (Finset.univ.filter (fun f : Fin C => rPC st f = false)).card ≤
     Module.finrank (ZMod 2) (LinearMap.range T) := by
   let S : Submodule (ZMod 2) (Fin C → ZMod 2) :=
     Submodule.span (ZMod 2)
       (Set.range (fun f' : {f : Fin C // rPC st f = false} => T (evec f'.val)))
   have hSle : S ≤ LinearMap.range T := by
     rw [Submodule.span_le]; rintro _ ⟨f', rfl⟩; exact ⟨evec f'.val, rfl⟩
   have hSdim : Module.finrank (ZMod 2) S =
       (Finset.univ.filter (fun f : Fin C => rPC st f = false)).card := by
     rw [finrank_span_eq_card hli_range, Fintype.card_subtype]
   rw [← hSdim]
   exact Submodule.finrank_mono hSle
 have hnull := LinearMap.finrank_range_add_finrank_ker T
 rw [Module.finrank_pi, Fintype.card_fin] at hnull
 obtain ⟨_, _, _, hRdim, hcard_eq⟩ := rref_used_basis A0
 have hpart : (Finset.univ.filter (fun f : Fin C => rPC st f = true)).card +
     (Finset.univ.filter (fun f : Fin C => rPC st f = false)).card = C := by
   have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C)))
     (p := fun f => rPC st f = true)
   have heq : Finset.univ.filter (fun f : Fin C => ¬ rPC st f = true) =
       Finset.univ.filter (fun f : Fin C => rPC st f = false) := by
     ext f; simp
   rw [heq, Finset.card_fin] at h1
   exact h1
 have hker_le : Module.finrank (ZMod 2) (LinearMap.ker T) ≤ Module.finrank (ZMod 2) Rsp := by
   change Module.finrank (ZMod 2) (LinearMap.ker T) ≤ Module.finrank (ZMod 2)
     (Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin C => b2z (A0 (i, j)))))
   rw [hRdim, hcard_eq]
   change Module.finrank (ZMod 2) (LinearMap.ker T) ≤
     (Finset.univ.filter (fun j : Fin C => rPC st j = true)).card
   omega
 have heq_sub : Rsp = LinearMap.ker T := Submodule.eq_of_le_of_finrank_le hle hker_le
 change v ∈ Rsp ↔ ∀ f : Fin C, T v f = 0
 rw [heq_sub, LinearMap.mem_ker, funext_iff]
 rfl
def aMt {M Q : ℕ} (cols : Fin Q → Fin M → Bool) (rhs : Fin M → Bool) :
   Fin M × Fin (Q + 1) → Bool :=
 fun p => Fin.lastCases (rhs p.1) (fun q => cols q p.1) p.2
lemma rref_solve_spec {M Q : ℕ} (cols : Fin Q → Fin M → Bool) (rhs : Fin M → Bool) :
   let st := rref (aMt cols rhs)
   (rPC st (Fin.last Q) = false ↔
     ∃ α : Fin Q → ZMod 2, ∑ q : Fin Q, α q • (fun i : Fin M => b2z (cols q i)) =
       fun i : Fin M => b2z (rhs i)) ∧
   (rPC st (Fin.last Q) = false →
     ∑ q : Fin Q, b2z (rNV st (Fin.last Q) q.castSucc) •
         (fun i : Fin M => b2z (cols q i)) =
       fun i : Fin M => b2z (rhs i)) := by
 dsimp only
 set A0 := aMt cols rhs
 set st := rref A0
 have hsol : rPC st (Fin.last Q) = false →
     ∑ q : Fin Q, b2z (rNV st (Fin.last Q) q.castSucc) •
         (fun i : Fin M => b2z (cols q i)) =
       fun i : Fin M => b2z (rhs i) := by
   intro hnp
   funext i
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
   have hker := (rref_nullVecs_span_ker A0).1 (Fin.last Q) i
   rw [Fin.sum_univ_castSucc] at hker
   have hlast : rNV st (Fin.last Q) (Fin.last Q) = true := by
     unfold rNV
     rw [hnp]
     simp
   have hA_last : A0 (i, Fin.last Q) = rhs i := by
     simp [A0, aMt]
   have hA_cast : ∀ q : Fin Q, A0 (i, q.castSucc) = cols q i := by
     intro q; simp [A0, aMt]
   simp_rw [hA_cast] at hker
   rw [hA_last, hlast] at hker
   have hb1 : b2z true = 1 := rfl
   rw [hb1, mul_one] at hker
   have hsum : (∑ q : Fin Q, b2z (rNV st (Fin.last Q) q.castSucc) * b2z (cols q i)) +
       b2z (rhs i) = 0 := by
     simpa [mul_comm] using hker
   have hadd := congrArg (fun x => x + b2z (rhs i)) hsum
   rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
   exact hadd
 refine ⟨⟨fun hnp => ⟨fun q => b2z (rNV st (Fin.last Q) q.castSucc), hsol hnp⟩, ?_⟩, hsol⟩
 rintro ⟨α, hα⟩
 by_contra hne
 have hpiv : rPC st (Fin.last Q) = true := by
   cases h : rPC st (Fin.last Q)
   · exact absurd h hne
   · rfl
 let stQ := ((List.finRange (Q + 1)).take Q).foldl (fun s c => rrefStep c s) (rrefInit A0)
 have hst_eq : st = rrefStep (Fin.last Q) stQ := by
   change rref A0 = _
   unfold rref
   have hlen : (List.finRange (Q + 1)).length = Q + 1 := List.length_finRange
   have htk : List.finRange (Q + 1) = (List.finRange (Q + 1)).take Q ++ [Fin.last Q] := by
     have h1 := List.take_succ_eq_append_getElem (l := List.finRange (Q + 1)) (i := Q) (by omega)
     rw [List.take_of_length_le (by omega)] at h1
     simpa [Fin.last] using h1
   rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
 rw [hst_eq] at hpiv
 dsimp only [rrefStep, rPC, Sum.elim_inr] at hpiv
 simp only [↓reduceIte, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at hpiv
 obtain ⟨i0, hi0u, hi0a⟩ := hpiv
 obtain ⟨_, hkerQ, hunusedQ, _, _, _⟩ := rrefInv_take A0 Q (by omega)
 let v : Fin (Q + 1) → ZMod 2 := Fin.lastCases 1 α
 have hv_A0 : ∀ i : Fin M, ∑ j : Fin (Q + 1), b2z (A0 (i, j)) * v j = 0 := by
   intro i
   rw [Fin.sum_univ_castSucc]
   have hA_cast : ∀ q : Fin Q, A0 (i, q.castSucc) = cols q i := fun q => by simp [A0, aMt]
   have hA_last : A0 (i, Fin.last Q) = rhs i := by simp [A0, aMt]
   have hv_cast : ∀ q : Fin Q, v q.castSucc = α q := fun q => by simp [v]
   have hv_last : v (Fin.last Q) = 1 := by simp [v]
   simp_rw [hA_cast, hv_cast]
   rw [hA_last, hv_last, mul_one]
   have hi := congrFun hα i
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
   rw [show ∑ q : Fin Q, b2z (cols q i) * α q = ∑ q : Fin Q, α q * b2z (cols q i) by
     apply Finset.sum_congr rfl; intro q _; ring]
   rw [hi, zmod2_add_self]
 have hv_stQ := (hkerQ v).mpr hv_A0 i0
 rw [Fin.sum_univ_castSucc] at hv_stQ
 have hfirst0 : ∑ q : Fin Q, rrefRow stQ i0 q.castSucc * v q.castSucc = 0 :=
   Finset.sum_eq_zero (fun q _ => by rw [hunusedQ i0 hi0u q.castSucc q.isLt, zero_mul])
 rw [hfirst0, zero_add] at hv_stQ
 have h1 : rrefRow stQ i0 (Fin.last Q) = 1 := by simp [rrefRow, hi0a, b2z]
 have hv1 : v (Fin.last Q) = 1 := by simp [v]
 rw [h1, hv1, mul_one] at hv_stQ
 exact one_ne_zero hv_stQ
def bSC (L : ℕ) (xy : Fin L ⊕ Fin L → Bool) : Fin L ⊕ Unit → Bool :=
 bAC L (Sum.elim (xy ∘ inl) (Sum.elim (fun j => !(xy (inr j))) (fun _ => true)))
lemma bSC_sp (L : ℕ) (x y : Fin L → Bool) :
   let out := bSC L (Sum.elim x y)
   (out (inr ()) = true ↔ bNat L y ≤ bNat L x) ∧
   (bNat L y ≤ bNat L x → bNat L (fun i => out (inl i)) = bNat L x - bNat L y) := by
 have hinp : Sum.elim (Sum.elim x y ∘ inl)
     (Sum.elim (fun j => !(Sum.elim x y (inr j))) (fun (_ : Unit) => true)) =
     Sum.elim x (Sum.elim (fun j => !(y j)) (fun (_ : Unit) => true)) := by
   funext q; rcases q with _ | _ | _ <;> rfl
 have h := bAC_sp L x (fun j => !(y j)) true
 dsimp only at h
 have hnot := bitsNat_not_add L y
 have hxlt := bNat_lt L x
 have hylt := bNat_lt L y
 have hsumlt := bNat_lt L (fun i => bAC L (Sum.elim x (Sum.elim (fun j => !(y j)) (fun _ => true))) (inl i))
 have htrue : (if (true : Bool) = true then 1 else 0) = 1 := rfl
 rw [htrue] at h
 have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
 change (bAC L _ (inr ()) = true ↔ _) ∧
   (bNat L y ≤ bNat L x → bNat L (fun i => bAC L _ (inl i)) = _)
 rw [hinp]
 cases hc : bAC L (Sum.elim x (Sum.elim (fun j => !(y j)) (fun _ => true))) (inr ())
 · rw [hc] at h
   simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at h
   constructor
   · simp only [Bool.false_eq_true, false_iff, not_le]; omega
   · intro hle; omega
 · rw [hc] at h
   simp only [↓reduceIte, mul_one] at h
   constructor
   · simp only [true_iff]; omega
   · intro _; omega
lemma ec_bSC (L : ℕ) : EC (20 * (L + 1)) (bSC L) := by
 have htrue := ec_const (ι := Fin L ⊕ Fin L) (fun (_ : Unit) => true)
 have hny : EC L (fun (xy : Fin L ⊕ Fin L → Bool) (j : Fin L) => !(xy (inr j))) := by
   have h := ec_not_of (ec_proj (fun j : Fin L => (inr j : Fin L ⊕ Fin L)))
   simpa [Fintype.card_fin] using h
 have hprep : EC (L + 2)
     (fun (xy : Fin L ⊕ Fin L → Bool) =>
       Sum.elim (xy ∘ inl) (Sum.elim (fun j => !(xy (inr j))) (fun (_ : Unit) => true))) := by
   have hp := ec_pair (ec_proj (fun i : Fin L => (inl i : Fin L ⊕ Fin L))) (ec_pair hny htrue)
   exact ec_le hp (by omega)
 have hcomp := ec_comp hprep (ec_bAC L)
 exact ec_le hcomp (by omega)
lemma bNat_bS_lt {α : Type} [Fintype α] (L : ℕ) (xs : α × Fin L → Bool)
   (hlt : ∑ a : α, bNat L (fun l => xs (a, l)) < 2 ^ L) :
   bNat L (bvSum L xs) = ∑ a : α, bNat L (fun l => xs (a, l)) := by
 have hval := bitsVal_bvSum L xs
 unfold bitsVal at hval
 rw [← Nat.cast_sum] at hval
 have hmod := (ZMod.natCast_eq_natCast_iff' _ _ (2 ^ L)).mp hval
 rw [Nat.mod_eq_of_lt (bNat_lt L _), Nat.mod_eq_of_lt hlt] at hmod
 exact hmod
lemma bNat_tB (L : ℕ) (v : ℕ) (hv : v < 2 ^ L) :
   bNat L (fun i : Fin L => v.testBit i.val) = v := by
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases hi : i < L
 · exact bNat_tb L (fun j : Fin L => v.testBit j.val) ⟨i, hi⟩
 · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bNat_lt L _) (Nat.pow_le_pow_right (by omega) (by omega))),
     Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))]
def loVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
 if i.val = 0 then 0 else (1 : ℕ) <<< (2 * i.val - 1)
def hiVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
 if i.val = 0 then 0 else (1 : ℕ) <<< (2 * i.val)
def vecBit (m : ℕ) (w : ℕ) (i : Fin m) : ZMod 2 :=
 if w.testBit i.val then 1 else 0
def incVec {n : ℕ} (u v : Fin (n + 1)) (j : Fin n) : ZMod 2 :=
 (if u.val = j.val + 1 then 1 else 0) + (if v.val = j.val + 1 then 1 else 0)
def Isub {n : ℕ} (F : List (Fin (n + 1) × Fin (n + 1))) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
 Submodule.span (ZMod 2) { v | ∃ e ∈ F, v = incVec e.1 e.2 }
def ext0 {n : ℕ} (g : Fin n → ZMod 2) (u : Fin (n + 1)) : ZMod 2 :=
 if h : u.val = 0 then 0 else g ⟨u.val - 1, by omega⟩
lemma dotProduct_incVec {n : ℕ} (u v : Fin (n + 1)) (g : Fin n → ZMod 2) :
   dotProduct (incVec u v) g = ext0 g u + ext0 g v := by
 unfold dotProduct incVec
 simp_rw [add_mul]
 rw [Finset.sum_add_distrib]
 have hsingle : ∀ w : Fin (n + 1),
     ∑ j : Fin n, (if w.val = j.val + 1 then (1 : ZMod 2) else 0) * g j = ext0 g w := by
   intro w
   by_cases hw : w.val = 0
   · simp only [ext0, hw, ↓reduceDIte]
     apply Finset.sum_eq_zero; intro j _; simp
   · simp only [ext0, hw, ↓reduceDIte]
     let j0 : Fin n := ⟨w.val - 1, by omega⟩
     rw [Finset.sum_eq_single j0]
     · have hfin : (⟨w.val - 1, by omega⟩ : Fin n) = j0 := rfl
       rw [hfin]
       have hjeq : w.val = j0.val + 1 := by dsimp [j0]; omega
       simp only [hjeq, ↓reduceIte, one_mul]
     · intro j _ hne
       have : w.val ≠ j.val + 1 := fun h => hne (Fin.ext (by dsimp [j0]; omega))
       simp [this]
     · intro h; exact absurd (Finset.mem_univ j0) h
 rw [hsingle u, hsingle v]
lemma finrank_Isub_eq {n : ℕ} (F : List (Fin (n + 1) × Fin (n + 1))) :
   Module.finrank (ZMod 2) (Isub F) =
     n + 1 - Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F)) ∧
   1 ≤ Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F)) ∧
   Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F)) ≤ n + 1 := by
 classical
 let rel : Fin (n + 1) → Fin (n + 1) → Prop := fun u v => (u, v) ∈ F
 let Q := Quot rel
 have hQ_fin : Finite Q := Finite.of_surjective (Quot.mk rel) Quot.exists_rep
 let _ : Fintype Q := Fintype.ofFinite Q
 have hQ_pos : 1 ≤ Nat.card Q := by
   rw [Nat.card_eq_fintype_card]
   have _ : Nonempty Q := ⟨Quot.mk rel 0⟩
   exact Fintype.card_pos
 have hQ_le : Nat.card Q ≤ n + 1 := by
   rw [Nat.card_eq_fintype_card]
   calc Fintype.card Q ≤ Fintype.card (Fin (n + 1)) :=
         Fintype.card_le_of_surjective (Quot.mk rel) Quot.exists_rep
     _ = n + 1 := Fintype.card_fin (n + 1)
 let M : Matrix (Fin F.length) (Fin n) (ZMod 2) :=
   fun idx j => incVec (F[idx]).1 (F[idx]).2 j
 have hIsub_eq : Isub F = Submodule.span (ZMod 2) (Set.range M) := by
   unfold Isub
   congr 1
   ext v
   constructor
   · rintro ⟨e, he, rfl⟩
     rw [List.mem_iff_getElem] at he
     obtain ⟨i, hi, rfl⟩ := he
     exact ⟨⟨i, hi⟩, rfl⟩
   · rintro ⟨idx, rfl⟩
     exact ⟨F[idx], List.getElem_mem idx.isLt, rfl⟩
 let K : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.ker M.mulVecLin
 have hdim_sum : Module.finrank (ZMod 2) (Isub F) + Module.finrank (ZMod 2) K = n := by
   have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
   rw [Module.finrank_pi, Fintype.card_fin] at hnull
   have hrg : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) =
       Module.finrank (ZMod 2) (Isub F) := by
     have h1 : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = M.rank := rfl
     rw [h1, ← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_cols, hIsub_eq]
     rfl
   rw [← hrg]
   exact hnull
 have hmemK : ∀ g : Fin n → ZMod 2, g ∈ K ↔ ∀ u v : Fin (n + 1), rel u v → ext0 g u = ext0 g v := by
   intro g
   have hker_iff : g ∈ K ↔ ∀ idx : Fin F.length, dotProduct (incVec (F[idx]).1 (F[idx]).2) g = 0 := by
     simp only [K, LinearMap.mem_ker, funext_iff, Pi.zero_apply]
     rfl
   rw [hker_iff]
   constructor
   · intro h u v huv
     change (u, v) ∈ F at huv
     rw [List.mem_iff_getElem] at huv
     obtain ⟨i, hi, heq⟩ := huv
     have h0 : ext0 g F[i].1 + ext0 g F[i].2 = 0 := by
       simpa [dotProduct_incVec] using h ⟨i, hi⟩
     have h1 : F[i].1 = u := congrArg Prod.fst heq
     have h2 : F[i].2 = v := congrArg Prod.snd heq
     rw [h1, h2] at h0
     have hadd := congrArg (fun x => x + ext0 g v) h0
     rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
     exact hadd
   · intro h idx
     have hmem : rel F[idx].1 F[idx].2 := List.getElem_mem idx.isLt
     rw [dotProduct_incVec, h _ _ hmem, zmod2_add_self]
 let eval0 : (Q → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (R := ZMod 2) (Quot.mk rel 0)
 let H0 : Submodule (ZMod 2) (Q → ZMod 2) := LinearMap.ker eval0
 have hK_equiv : K ≃ₗ[ZMod 2] H0 :=
   { toFun := fun g =>
       ⟨fun q => Quot.lift (ext0 g.val) (fun u v huv => (hmemK g.val).mp g.property u v huv) q,
        by simp [H0, eval0, ext0]⟩
     invFun := fun f =>
       ⟨fun j => f.val (Quot.mk rel ⟨j.val + 1, by omega⟩),
        (hmemK _).mpr (fun u v huv => by
          have hext : ∀ w : Fin (n + 1),
              ext0 (fun j => f.val (Quot.mk rel ⟨j.val + 1, by omega⟩)) w = f.val (Quot.mk rel w) := by
            intro w
            by_cases hw : w.val = 0
            · have hw0 : w = 0 := Fin.ext hw
              subst hw0
              have hf0 : f.val (Quot.mk rel 0) = 0 := f.property
              simp [ext0, hf0]
            · simp only [ext0, hw, ↓reduceDIte]
              exact congrArg (fun x => f.val (Quot.mk rel x)) (Fin.ext (by dsimp; omega))
          rw [hext u, hext v, Quot.sound huv])⟩
     map_add' := fun g1 g2 => by
       apply Subtype.ext; funext q
       induction q using Quot.ind with
       | _ u =>
         change ext0 (g1.val + g2.val) u = ext0 g1.val u + ext0 g2.val u
         by_cases hu : u.val = 0 <;> simp [ext0, hu]
     map_smul' := fun c g => by
       apply Subtype.ext; funext q
       induction q using Quot.ind with
       | _ u =>
         change ext0 (c • g.val) u = c • ext0 g.val u
         by_cases hu : u.val = 0 <;> simp [ext0, hu]
     left_inv := fun g => by
       apply Subtype.ext; funext j
       simp [ext0]
     right_inv := fun f => by
       apply Subtype.ext; funext q
       induction q using Quot.ind with
       | _ u =>
         change ext0 (fun j => f.val (Quot.mk rel ⟨j.val + 1, by omega⟩)) u = f.val (Quot.mk rel u)
         by_cases hu : u.val = 0
         · have hu0 : u = 0 := Fin.ext hu
           subst hu0
           have hf0 : f.val (Quot.mk rel 0) = 0 := f.property
           simp [ext0, hf0]
         · simp only [ext0, hu, ↓reduceDIte]
           exact congrArg (fun x => f.val (Quot.mk rel x)) (Fin.ext (by dsimp; omega)) }
 have hsurj : LinearMap.range eval0 = ⊤ := by
   rw [Submodule.eq_top_iff']
   intro c
   exact ⟨fun _ => c, rfl⟩
 have hH0_dim : 1 + Module.finrank (ZMod 2) H0 = Nat.card Q := by
   have hnull := LinearMap.finrank_range_add_finrank_ker eval0
   rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_pi, ← Nat.card_eq_fintype_card] at hnull
   exact hnull
 have hK_dim : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) H0 := hK_equiv.finrank_eq
 change Module.finrank (ZMod 2) (Isub F) = n + 1 - Nat.card Q ∧ 1 ≤ Nat.card Q ∧ Nat.card Q ≤ n + 1
 exact ⟨by omega, hQ_pos, hQ_le⟩
lemma finrank_Isub_inf {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) (h : ℕ) :
   Module.finrank (ZMod 2) ((Isub (E.take h) ⊓ Isub (E.drop h) : Submodule (ZMod 2) (Fin n → ZMod 2))) =
     n + 1 + Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ E)) -
       (Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ E.take h)) +
        Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ E.drop h))) := by
 have hsup : Isub (E.take h) ⊔ Isub (E.drop h) = Isub E := by
   unfold Isub
   rw [← Submodule.span_union]
   congr 1
   ext v
   simp only [Set.mem_union]
   constructor
   · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
     · exact ⟨e, List.mem_of_mem_take he, rfl⟩
     · exact ⟨e, List.mem_of_mem_drop he, rfl⟩
   · rintro ⟨e, he, rfl⟩
     rw [← List.take_append_drop h E, List.mem_append] at he
     rcases he with h1 | h2
     · exact Or.inl ⟨e, h1, rfl⟩
     · exact Or.inr ⟨e, h2, rfl⟩
 have hmod := Submodule.finrank_sup_add_finrank_inf_eq (Isub (E.take h)) (Isub (E.drop h))
 rw [hsup] at hmod
 obtain ⟨hE, hE1, hE2⟩ := finrank_Isub_eq E
 obtain ⟨hT, hT1, hT2⟩ := finrank_Isub_eq (E.take h)
 obtain ⟨hD, hD1, hD2⟩ := finrank_Isub_eq (E.drop h)
 omega
def laneEquiv (n : ℕ) :
   (ZMod 2 × (Fin n → ZMod 2) × (Fin n → ZMod 2)) ≃ₗ[ZMod 2] (Fin (2 * n + 1) → ZMod 2) :=
 { toFun := fun t i =>
     if hi0 : i.val = 0 then t.1
     else if i.val % 2 = 1 then t.2.1 ⟨(i.val - 1) / 2, by omega⟩
     else t.2.2 ⟨i.val / 2 - 1, by omega⟩
   invFun := fun v =>
     (v ⟨0, by omega⟩,
      fun j : Fin n => v ⟨2 * j.val + 1, by omega⟩,
      fun j : Fin n => v ⟨2 * j.val + 2, by omega⟩)
   map_add' := fun t1 t2 => by
     funext i
     simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
     split_ifs <;> rfl
   map_smul' := fun c t => by
     funext i
     simp only [RingHom.id_apply, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]
     split_ifs <;> rfl
   left_inv := fun ⟨a, l, h⟩ => by
     ext
     · simp
     · rename_i j
       have h2 : (2 * j.val + 1) % 2 = 1 := by omega
       simp [h2]
     · rename_i j
       have h1 : (2 * j.val + 2) % 2 ≠ 1 := by omega
       have h2 : (2 * j.val + 2) / 2 - 1 = j.val := by omega
       simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceDIte, h1, ↓reduceIte]
       exact congrArg h (Fin.ext h2)
   right_inv := fun v => by
     funext i
     by_cases hi0 : i.val = 0
     · simp only [hi0, ↓reduceDIte]; congr 1; exact Fin.ext hi0.symm
     · by_cases hodd : i.val % 2 = 1
       · simp only [hi0, hodd, ↓reduceDIte, ↓reduceIte]; congr 1; exact Fin.ext (by dsimp; omega)
       · simp only [hi0, hodd, ↓reduceDIte, ↓reduceIte]; congr 1; exact Fin.ext (by dsimp; omega) }
lemma laneEquiv_vec_one (n : ℕ) :
   (laneEquiv n).symm (vecBit (2 * n + 1) 1) = (1, 0, 0) := by
 ext
 · simp [laneEquiv, vecBit]
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Pi.zero_apply]
   have : (1 : ℕ).testBit (2 * j.val + 1) = false := by
     rw [Nat.testBit_lt_two_pow]
     calc 1 < 2 ^ 1 := by omega
       _ ≤ 2 ^ (2 * j.val + 1) := Nat.pow_le_pow_right (by omega) (by omega)
   simp [this]
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Pi.zero_apply]
   have : (1 : ℕ).testBit (2 * j.val + 2) = false := by
     rw [Nat.testBit_lt_two_pow]
     calc 1 < 2 ^ 1 := by omega
       _ ≤ 2 ^ (2 * j.val + 2) := Nat.pow_le_pow_right (by omega) (by omega)
   simp [this]
lemma testBit_loVal {n : ℕ} (u : Fin (n + 1)) (b : ℕ) :
   (loVal u).testBit b = decide (u.val ≠ 0 ∧ b = 2 * u.val - 1) := by
 unfold loVal
 by_cases hu : u.val = 0
 · simp [hu]
 · simp only [hu, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
   rw [Nat.testBit_shiftLeft]
   by_cases hge : 2 * u.val - 1 ≤ b
   · simp only [hge, decide_true, Bool.true_and]
     by_cases heq : b = 2 * u.val - 1
     · subst heq; simp
     · have hpos : 1 ≤ b - (2 * u.val - 1) := by omega
       have hlt : 1 < 2 ^ (b - (2 * u.val - 1)) := by
         calc 1 < 2 ^ 1 := by omega
           _ ≤ 2 ^ (b - (2 * u.val - 1)) := Nat.pow_le_pow_right (by omega) hpos
       simp [heq, Nat.testBit_lt_two_pow hlt]
   · have hne : b ≠ 2 * u.val - 1 := by omega
     simp [hge, hne]
lemma testBit_hiVal {n : ℕ} (u : Fin (n + 1)) (b : ℕ) :
   (hiVal u).testBit b = decide (u.val ≠ 0 ∧ b = 2 * u.val) := by
 unfold hiVal
 by_cases hu : u.val = 0
 · simp [hu]
 · simp only [hu, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
   rw [Nat.testBit_shiftLeft]
   by_cases hge : 2 * u.val ≤ b
   · simp only [hge, decide_true, Bool.true_and]
     by_cases heq : b = 2 * u.val
     · subst heq; simp
     · have hpos : 1 ≤ b - 2 * u.val := by omega
       have hlt : 1 < 2 ^ (b - 2 * u.val) := by
         calc 1 < 2 ^ 1 := by omega
           _ ≤ 2 ^ (b - 2 * u.val) := Nat.pow_le_pow_right (by omega) hpos
       simp [heq, Nat.testBit_lt_two_pow hlt]
   · have hne : b ≠ 2 * u.val := by omega
     simp [hge, hne]
lemma laneEquiv_vec_lo {n : ℕ} (u v : Fin (n + 1)) :
   (laneEquiv n).symm (vecBit (2 * n + 1) (loVal u ^^^ loVal v)) = (0, incVec u v, 0) := by
 ext
 · simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor]
   have h1 : (loVal u).testBit 0 = false := by rw [testBit_loVal, decide_eq_false_iff_not]; omega
   have h2 : (loVal v).testBit 0 = false := by rw [testBit_loVal, decide_eq_false_iff_not]; omega
   rw [h1, h2]; rfl
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor, testBit_loVal, incVec]
   have h1 : (u.val ≠ 0 ∧ 2 * j.val + 1 = 2 * u.val - 1) ↔ u.val = j.val + 1 := by omega
   have h2 : (v.val ≠ 0 ∧ 2 * j.val + 1 = 2 * v.val - 1) ↔ v.val = j.val + 1 := by omega
   simp only [h1, h2]
   by_cases hu : u.val = j.val + 1 <;> by_cases hv : v.val = j.val + 1 <;> simp [hu, hv, zmod2_add_self]
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor, Pi.zero_apply]
   have h1 : (loVal u).testBit (2 * j.val + 2) = false := by rw [testBit_loVal, decide_eq_false_iff_not]; omega
   have h2 : (loVal v).testBit (2 * j.val + 2) = false := by rw [testBit_loVal, decide_eq_false_iff_not]; omega
   rw [h1, h2]; rfl
lemma laneEquiv_vec_hi {n : ℕ} (u v : Fin (n + 1)) :
   (laneEquiv n).symm (vecBit (2 * n + 1) (hiVal u ^^^ hiVal v)) = (0, 0, incVec u v) := by
 ext
 · simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor]
   have h1 : (hiVal u).testBit 0 = false := by rw [testBit_hiVal, decide_eq_false_iff_not]; omega
   have h2 : (hiVal v).testBit 0 = false := by rw [testBit_hiVal, decide_eq_false_iff_not]; omega
   rw [h1, h2]; rfl
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor, Pi.zero_apply]
   have h1 : (hiVal u).testBit (2 * j.val + 1) = false := by rw [testBit_hiVal, decide_eq_false_iff_not]; omega
   have h2 : (hiVal v).testBit (2 * j.val + 1) = false := by rw [testBit_hiVal, decide_eq_false_iff_not]; omega
   rw [h1, h2]; rfl
 · rename_i j
   simp only [laneEquiv, LinearEquiv.coe_symm_mk, vecBit, Nat.testBit_xor, testBit_hiVal, incVec]
   have h1 : (u.val ≠ 0 ∧ 2 * j.val + 2 = 2 * u.val) ↔ u.val = j.val + 1 := by omega
   have h2 : (v.val ≠ 0 ∧ 2 * j.val + 2 = 2 * v.val) ↔ v.val = j.val + 1 := by omega
   simp only [h1, h2]
   by_cases hu : u.val = j.val + 1 <;> by_cases hv : v.val = j.val + 1 <;> simp [hu, hv, zmod2_add_self]
lemma span_triple_prod {n : ℕ} (has1 : Bool)
   (Flo Fhi : List (Fin (n + 1) × Fin (n + 1))) (L : List ℕ)
   (hL : ∀ w, w ∈ L ↔
     (has1 = true ∧ w = 1) ∨
     (∃ z ∈ Flo, w = loVal z.1 ^^^ loVal z.2) ∨
     (∃ z ∈ Fhi, w = hiVal z.1 ^^^ hiVal z.2)) :
   Submodule.map (laneEquiv n).symm.toLinearMap
       (Submodule.span (ZMod 2) { v | ∃ w ∈ L, v = vecBit (2 * n + 1) w }) =
     Submodule.prod (if has1 then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥)
       (Submodule.prod (Isub Flo) (Isub Fhi)) := by
 rw [Submodule.map_span]
 apply le_antisymm
 · rw [Submodule.span_le]
   rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
   rcases (hL w).mp hw with ⟨h1, rfl⟩ | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
   · change (laneEquiv n).symm (vecBit (2 * n + 1) 1) ∈ _
     rw [laneEquiv_vec_one]
     simp [h1]
   · change (laneEquiv n).symm (vecBit (2 * n + 1) (loVal z.1 ^^^ loVal z.2)) ∈ _
     rw [laneEquiv_vec_lo]
     refine ⟨Submodule.zero_mem _, Submodule.subset_span ⟨z, hz, rfl⟩, Submodule.zero_mem _⟩
   · change (laneEquiv n).symm (vecBit (2 * n + 1) (hiVal z.1 ^^^ hiVal z.2)) ∈ _
     rw [laneEquiv_vec_hi]
     refine ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.subset_span ⟨z, hz, rfl⟩⟩
 · rintro ⟨a, l, h⟩ ⟨ha, hl, hh⟩
   have hsplit : (a, l, h) = (a, 0, 0) + (0, l, 0) + (0, 0, h) := by ext <;> simp
   rw [hsplit]
   refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
   · cases has1
     · have ha0 : a = 0 := by simpa using ha
       subst ha0; exact Submodule.zero_mem _
     · have h1m : ((1 : ZMod 2), (0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2)) ∈
           Submodule.span (ZMod 2) ((laneEquiv n).symm.toLinearMap '' { v | ∃ w ∈ L, v = vecBit (2 * n + 1) w }) := by
         apply Submodule.subset_span
         refine ⟨vecBit (2 * n + 1) 1, ⟨1, (hL 1).mpr (Or.inl ⟨rfl, rfl⟩), rfl⟩, ?_⟩
         exact laneEquiv_vec_one n
       have := Submodule.smul_mem _ a h1m
       simpa using this
   · refine Submodule.span_induction
         (p := fun x _ => ((0 : ZMod 2), x, (0 : Fin n → ZMod 2)) ∈
           Submodule.span (ZMod 2) ((laneEquiv n).symm.toLinearMap '' { v | ∃ w ∈ L, v = vecBit (2 * n + 1) w }))
         ?_ ?_ ?_ ?_ hl
     · rintro _ ⟨z, hz, rfl⟩
       apply Submodule.subset_span
       refine ⟨vecBit (2 * n + 1) (loVal z.1 ^^^ loVal z.2),
         ⟨_, (hL _).mpr (Or.inr (Or.inl ⟨z, hz, rfl⟩)), rfl⟩, ?_⟩
       exact laneEquiv_vec_lo z.1 z.2
     · exact Submodule.zero_mem _
     · intro x y _ _ hx hy
       have := Submodule.add_mem _ hx hy; simpa using this
     · intro c x _ hx
       have := Submodule.smul_mem _ c hx; simpa using this
   · refine Submodule.span_induction
         (p := fun x _ => ((0 : ZMod 2), (0 : Fin n → ZMod 2), x) ∈
           Submodule.span (ZMod 2) ((laneEquiv n).symm.toLinearMap '' { v | ∃ w ∈ L, v = vecBit (2 * n + 1) w }))
         ?_ ?_ ?_ ?_ hh
     · rintro _ ⟨z, hz, rfl⟩
       apply Submodule.subset_span
       refine ⟨vecBit (2 * n + 1) (hiVal z.1 ^^^ hiVal z.2),
         ⟨_, (hL _).mpr (Or.inr (Or.inr ⟨z, hz, rfl⟩)), rfl⟩, ?_⟩
       exact laneEquiv_vec_hi z.1 z.2
     · exact Submodule.zero_mem _
     · intro x y _ _ hx hy
       have := Submodule.add_mem _ hx hy; simpa using this
     · intro c x _ hx
       have := Submodule.smul_mem _ c hx; simpa using this
def makeP {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) : List ℕ :=
 [1, 1, 1] ++ E.flatMap (fun z => [loVal z.1 ^^^ loVal z.2, hiVal z.1 ^^^ hiVal z.2, 1])
lemma makeP_length {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) :
   (makeP E).length = 3 * (E.length + 1) := by
 unfold makeP
 rw [List.length_append, List.length_flatMap]
 simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, smul_eq_mul]
 omega
lemma makeP_getElem {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) (i : ℕ)
   (hi : i < 3 * (E.length + 1)) :
   (makeP E)[i]'(by rw [makeP_length]; exact hi) =
     if h0 : i < 3 then 1
     else
       let z := E[i / 3 - 1]'(by omega)
       if i % 3 = 0 then loVal z.1 ^^^ loVal z.2
       else if i % 3 = 1 then hiVal z.1 ^^^ hiVal z.2
       else 1 := by
 induction E generalizing i with
 | nil =>
   have hi3 : i < 3 := by simpa using hi
   interval_cases i <;> simp [makeP]
 | cons hd tl ih =>
   by_cases h0 : i < 3
   · interval_cases i <;> simp [makeP]
   · by_cases h1 : i < 6
     · interval_cases i <;> simp [makeP]
     · have hi' : i - 3 < 3 * (tl.length + 1) := by simp at hi; omega
       have hstep : (makeP (hd :: tl))[i]'(by rw [makeP_length]; exact hi) =
           (makeP tl)[i - 3]'(by rw [makeP_length]; exact hi') := by
         unfold makeP
         simp only [List.flatMap_cons, List.cons_append, List.nil_append]
         rcases i with _ | _ | _ | _ | _ | _ | j
         · omega
         · omega
         · omega
         · omega
         · omega
         · omega
         · simp [show j + 6 - 3 = j + 3 by omega]
       rw [hstep, ih (i - 3) hi']
       have h0' : ¬ (i - 3 < 3) := by omega
       have hmod : (i - 3) % 3 = i % 3 := by omega
       have hidx : (hd :: tl)[i / 3 - 1]'(by simp; omega) = tl[(i - 3) / 3 - 1]'(by omega) := by
         have h1 : i / 3 - 1 = ((i - 3) / 3 - 1) + 1 := by omega
         calc (hd :: tl)[i / 3 - 1]'(by simp; omega)
             = (hd :: tl)[((i - 3) / 3 - 1) + 1]'(by simp; omega) := by congr 1
           _ = tl[(i - 3) / 3 - 1]'(by omega) := rfl
       simp only [h0, h0', ↓reduceDIte, hmod, hidx]
lemma makeP_take_mem {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) (H : ℕ)
   (hH : H ≤ 3 * (E.length + 1)) (w : ℕ) :
   w ∈ (makeP E).take H ↔
     (decide (1 ≤ H) = true ∧ w = 1) ∨
     (∃ z ∈ E.take (if H < 3 then 0 else (H - 1) / 3), w = loVal z.1 ^^^ loVal z.2) ∨
     (∃ z ∈ E.take (if H < 3 then 0 else (H - 2) / 3), w = hiVal z.1 ^^^ hiVal z.2) := by
 have hlen : (makeP E).length = 3 * (E.length + 1) := makeP_length E
 rw [List.mem_iff_getElem]
 constructor
 · rintro ⟨i, hi, rfl⟩
   rw [List.length_take, hlen, min_eq_left hH] at hi
   rw [List.getElem_take, makeP_getElem E i (by omega)]
   by_cases h0 : i < 3
   · simp only [h0, ↓reduceDIte]; left; exact ⟨decide_eq_true (by omega), trivial⟩
   · simp only [h0, ↓reduceDIte]
     by_cases hm0 : i % 3 = 0
     · simp only [hm0, ↓reduceIte]; right; left
       refine ⟨E[i / 3 - 1]'(by omega), ?_, rfl⟩
       rw [List.mem_iff_getElem]
       exact ⟨i / 3 - 1, by rw [List.length_take]; split_ifs <;> omega, List.getElem_take⟩
     · by_cases hm1 : i % 3 = 1
       · simp only [hm1, ↓reduceIte]; right; right
         refine ⟨E[i / 3 - 1]'(by omega), ?_, ?_⟩
         · rw [List.mem_iff_getElem]
           exact ⟨i / 3 - 1, by rw [List.length_take]; split_ifs <;> omega, List.getElem_take⟩
         · simp
       · simp only [hm0, hm1, ↓reduceIte]; left; exact ⟨decide_eq_true (by omega), trivial⟩
 · rintro (⟨h1, rfl⟩ | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
   · simp only [decide_eq_true_eq] at h1
     refine ⟨0, by rw [List.length_take, hlen, min_eq_left hH]; omega, ?_⟩
     rw [List.getElem_take, makeP_getElem E 0 (by omega)]; simp
   · rw [List.mem_iff_getElem] at hz
     obtain ⟨t, ht, rfl⟩ := hz
     rw [List.length_take] at ht
     have hH3 : ¬ (H < 3) := by by_contra hc; simp [hc] at ht
     simp only [hH3, ↓reduceIte, lt_min_iff] at ht
     let i := 3 * (t + 1)
     refine ⟨i, by rw [List.length_take, hlen, min_eq_left hH]; omega, ?_⟩
     rw [List.getElem_take, makeP_getElem E i (by omega)]
     have hi0 : ¬ (i < 3) := by omega
     have hmod : i % 3 = 0 := by omega
     have hdiv : i / 3 - 1 = t := by omega
     simp only [hi0, ↓reduceDIte, hmod, ↓reduceIte, hdiv, List.getElem_take]
   · rw [List.mem_iff_getElem] at hz
     obtain ⟨t, ht, rfl⟩ := hz
     rw [List.length_take] at ht
     have hH3 : ¬ (H < 3) := by by_contra hc; simp [hc] at ht
     simp only [hH3, ↓reduceIte, lt_min_iff] at ht
     let i := 3 * (t + 1) + 1
     refine ⟨i, by rw [List.length_take, hlen, min_eq_left hH]; omega, ?_⟩
     rw [List.getElem_take, makeP_getElem E i (by omega)]
     have hi0 : ¬ (i < 3) := by omega
     have hmod1 : i % 3 = 1 := by omega
     have hdiv : i / 3 - 1 = t := by omega
     simp only [hi0, ↓reduceDIte, hmod1, ↓reduceIte, hdiv, List.getElem_take]
     simp
lemma makeP_drop_mem {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1))) (H : ℕ)
   (hH : H ≤ 3 * (E.length + 1)) (w : ℕ) :
   w ∈ (makeP E).drop H ↔
     (decide (H < 3 * (E.length + 1)) = true ∧ w = 1) ∨
     (∃ z ∈ E.drop (if H < 3 then 0 else (H - 1) / 3), w = loVal z.1 ^^^ loVal z.2) ∨
     (∃ z ∈ E.drop (if H < 3 then 0 else (H - 2) / 3), w = hiVal z.1 ^^^ hiVal z.2) := by
 have hlen : (makeP E).length = 3 * (E.length + 1) := makeP_length E
 rw [List.mem_iff_getElem]
 constructor
 · rintro ⟨j, hj, rfl⟩
   rw [List.length_drop, hlen] at hj
   rw [List.getElem_drop, makeP_getElem E (H + j) (by omega)]
   by_cases h0 : H + j < 3
   · simp only [h0, ↓reduceDIte]; left; exact ⟨decide_eq_true (by omega), trivial⟩
   · simp only [h0, ↓reduceDIte]
     by_cases hm0 : (H + j) % 3 = 0
     · simp only [hm0, ↓reduceIte]; right; left
       refine ⟨E[(H + j) / 3 - 1]'(by omega), ?_, rfl⟩
       rw [List.mem_iff_getElem]
       let k0 := if H < 3 then 0 else (H - 1) / 3
       have hk0_le : k0 ≤ (H + j) / 3 - 1 := by dsimp [k0]; split_ifs <;> omega
       refine ⟨(H + j) / 3 - 1 - k0, by rw [List.length_drop]; omega, ?_⟩
       rw [List.getElem_drop]; congr 1; omega
     · by_cases hm1 : (H + j) % 3 = 1
       · simp only [hm1, ↓reduceIte]; right; right
         refine ⟨E[(H + j) / 3 - 1]'(by omega), ?_, ?_⟩
         · rw [List.mem_iff_getElem]
           let k0 := if H < 3 then 0 else (H - 2) / 3
           have hk0_le : k0 ≤ (H + j) / 3 - 1 := by dsimp [k0]; split_ifs <;> omega
           refine ⟨(H + j) / 3 - 1 - k0, by rw [List.length_drop]; omega, ?_⟩
           rw [List.getElem_drop]; congr 1; omega
         · simp
       · simp only [hm0, hm1, ↓reduceIte]; left; exact ⟨decide_eq_true (by omega), trivial⟩
 · rintro (⟨hlt, rfl⟩ | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
   · simp only [decide_eq_true_eq] at hlt
     let i := 3 * (E.length + 1) - 1
     refine ⟨i - H, by rw [List.length_drop, hlen]; omega, ?_⟩
     rw [List.getElem_drop]
     have hidx : (makeP E)[H + (i - H)]'(by rw [hlen]; omega) = (makeP E)[i]'(by rw [hlen]; omega) := by
       congr 1; omega
     rw [hidx, makeP_getElem E i (by omega)]
     by_cases h0 : i < 3
     · simp [h0]
     · have hm0 : i % 3 ≠ 0 := by omega
       have hm1 : i % 3 ≠ 1 := by omega
       simp [h0, hm0, hm1]
   · rw [List.mem_iff_getElem] at hz
     obtain ⟨j, hj, rfl⟩ := hz
     rw [List.length_drop] at hj
     let k0 := if H < 3 then 0 else (H - 1) / 3
     let t := k0 + j
     let i := 3 * (t + 1)
     have hHi : H ≤ i := by dsimp [i, t, k0]; split_ifs <;> omega
     refine ⟨i - H, by rw [List.length_drop, hlen]; omega, ?_⟩
     rw [List.getElem_drop]
     have hidx : (makeP E)[H + (i - H)]'(by rw [hlen]; omega) = (makeP E)[i]'(by rw [hlen]; omega) := by
       congr 1; omega
     rw [hidx, makeP_getElem E i (by omega)]
     have hi0 : ¬ (i < 3) := by omega
     have hmod : i % 3 = 0 := by omega
     have hdiv : i / 3 - 1 = t := by omega
     simp only [hi0, ↓reduceDIte, hmod, ↓reduceIte, hdiv, List.getElem_drop]
     rfl
   · rw [List.mem_iff_getElem] at hz
     obtain ⟨j, hj, rfl⟩ := hz
     rw [List.length_drop] at hj
     let k0 := if H < 3 then 0 else (H - 2) / 3
     let t := k0 + j
     let i := 3 * (t + 1) + 1
     have hHi : H ≤ i := by dsimp [i, t, k0]; split_ifs <;> omega
     refine ⟨i - H, by rw [List.length_drop, hlen]; omega, ?_⟩
     rw [List.getElem_drop]
     have hidx : (makeP E)[H + (i - H)]'(by rw [hlen]; omega) = (makeP E)[i]'(by rw [hlen]; omega) := by
       congr 1; omega
     rw [hidx, makeP_getElem E i (by omega)]
     have hi0 : ¬ (i < 3) := by omega
     have hmod1 : i % 3 = 1 := by omega
     have hdiv : i / 3 - 1 = t := by omega
     simp only [hi0, ↓reduceDIte, hmod1, ↓reduceIte, hdiv, List.getElem_drop]
     simp [t, k0]
lemma span_toFinset_eq {m : ℕ} [DecidableEq (Fin m → ZMod 2)] (L : List ℕ) :
   Submodule.span (ZMod 2)
       (↑((L.map (fun w (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
         Set (Fin m → ZMod 2)) =
     Submodule.span (ZMod 2) { v | ∃ w ∈ L, v = vecBit m w } := by
 congr 1
 ext v
 simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
 constructor
 · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
 · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
lemma finrank_submodule_prod {M₁ M₂ : Type*} [AddCommGroup M₁] [Module (ZMod 2) M₁]
   [AddCommGroup M₂] [Module (ZMod 2) M₂] [Module.Finite (ZMod 2) M₁] [Module.Finite (ZMod 2) M₂]
   (p : Submodule (ZMod 2) M₁) (q : Submodule (ZMod 2) M₂) :
   Module.finrank (ZMod 2) ↥(p.prod q) = Module.finrank (ZMod 2) ↥p + Module.finrank (ZMod 2) ↥q := by
 let e : ↥(p.prod q) ≃ₗ[ZMod 2] (↥p × ↥q) :=
   { toFun := fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
     invFun := fun y => ⟨(y.1.val, y.2.val), ⟨y.1.property, y.2.property⟩⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }
 rw [e.finrank_eq, Module.finrank_prod]
lemma finrank_makeP_cut {n : ℕ} [DecidableEq (Fin (2 * n + 1) → ZMod 2)]
   (E : List (Fin (n + 1) × Fin (n + 1))) (H : ℕ) (hH : H ≤ 3 * (E.length + 1)) :
   let spanP := fun L : List ℕ =>
     Submodule.span (ZMod 2)
       (↑((L.map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
         Set (Fin (2 * n + 1) → ZMod 2))
   let comps := fun F : List (Fin (n + 1) × Fin (n + 1)) =>
     Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F))
   let cutDim := fun h : ℕ => n + 1 + comps E - (comps (E.take h) + comps (E.drop h))
   Module.finrank (ZMod 2) ((spanP ((makeP E).take H) ⊓ spanP ((makeP E).drop H) :
       Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2))) =
     (if 1 ≤ H ∧ H < 3 * (E.length + 1) then 1 else 0) +
       cutDim (if H < 3 then 0 else (H - 1) / 3) +
       cutDim (if H < 3 then 0 else (H - 2) / 3) := by
 dsimp only
 let S1 := Submodule.span (ZMod 2) { v | ∃ w ∈ (makeP E).take H, v = vecBit (2 * n + 1) w }
 let S2 := Submodule.span (ZMod 2) { v | ∃ w ∈ (makeP E).drop H, v = vecBit (2 * n + 1) w }
 have hS : (Submodule.span (ZMod 2)
       (↑(((makeP E).take H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) ⊓
     Submodule.span (ZMod 2)
       (↑(((makeP E).drop H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
     Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2)) = S1 ⊓ S2 := by
   rw [span_toFinset_eq, span_toFinset_eq]
 have hSdim : Module.finrank (ZMod 2)
     ↥(Submodule.span (ZMod 2)
       (↑(((makeP E).take H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) ⊓
     Submodule.span (ZMod 2)
       (↑(((makeP E).drop H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
       Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2)) =
     Module.finrank (ZMod 2) ↥(S1 ⊓ S2) :=
   congrArg (fun X : Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2) => Module.finrank (ZMod 2) ↥X) hS
 rw [hSdim]
 have heq_dim : Module.finrank (ZMod 2) (S1 ⊓ S2 : Submodule (ZMod 2) _) =
     Module.finrank (ZMod 2) (Submodule.map (laneEquiv n).symm.toLinearMap (S1 ⊓ S2)) :=
   ((laneEquiv n).symm.submoduleMap (S1 ⊓ S2)).finrank_eq
 rw [heq_dim, Submodule.map_inf _ (laneEquiv n).symm.injective]
 rw [span_triple_prod _ _ _ _ (makeP_take_mem E H hH),
   span_triple_prod _ _ _ _ (makeP_drop_mem E H hH)]
 rw [Submodule.prod_inf_prod, Submodule.prod_inf_prod]
 rw [finrank_submodule_prod, finrank_submodule_prod]
 rw [finrank_Isub_inf, finrank_Isub_inf]
 have hA : Module.finrank (ZMod 2)
     (((if decide (1 ≤ H) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥) ⊓
       (if decide (H < 3 * (E.length + 1)) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥) :
         Submodule (ZMod 2) (ZMod 2))) =
     if 1 ≤ H ∧ H < 3 * (E.length + 1) then 1 else 0 := by
   by_cases hc : 1 ≤ H ∧ H < 3 * (E.length + 1)
   · simp only [hc, and_self, ↓reduceIte]
     have hsub : ((if decide (1 ≤ H) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥) ⊓
         (if decide (H < 3 * (E.length + 1)) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥)) = ⊤ := by
       simp [hc.1, hc.2]
     rw [congrArg (fun X : Submodule (ZMod 2) (ZMod 2) => Module.finrank (ZMod 2) ↥X) hsub,
       finrank_top, Module.finrank_self]
   · simp only [hc, ↓reduceIte]
     have hsub : ((if decide (1 ≤ H) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥) ⊓
         (if decide (H < 3 * (E.length + 1)) = true then (⊤ : Submodule (ZMod 2) (ZMod 2)) else ⊥)) = ⊥ := by
       by_cases h1 : 1 ≤ H <;> by_cases h2 : H < 3 * (E.length + 1) <;> simp_all
     rw [congrArg (fun X : Submodule (ZMod 2) (ZMod 2) => Module.finrank (ZMod 2) ↥X) hsub]
     exact finrank_bot (ZMod 2) (ZMod 2)
 rw [hA]
 omega
lemma peak_eq_one_add_two_width {n e : ℕ} [DecidableEq (Fin (2 * n + 1) → ZMod 2)]
   (edges : Fin e → Fin (n + 1) × Fin (n + 1)) :
   let E := List.ofFn edges
   let comps := fun F : List (Fin (n + 1) × Fin (n + 1)) =>
     Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F))
   let width := (Finset.range (e + 1)).sup (fun h => n + 1 + comps E - (comps (E.take h) + comps (E.drop h)))
   let P := makeP E
   let spanP := fun L : List ℕ =>
     Submodule.span (ZMod 2)
       (↑((L.map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
         Set (Fin (2 * n + 1) → ZMod 2))
   let peak := (Finset.range (3 * (e + 1) + 1)).sup (fun H =>
     Module.finrank (ZMod 2) ((spanP (P.take H) ⊓ spanP (P.drop H) : Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2))))
   peak = 1 + 2 * width := by
 dsimp only
 set E := List.ofFn edges
 have hElen : E.length = e := List.length_ofFn
 let comps := fun F : List (Fin (n + 1) × Fin (n + 1)) =>
   Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F))
 let cutDim := fun h : ℕ => n + 1 + comps E - (comps (E.take h) + comps (E.drop h))
 let width := (Finset.range (e + 1)).sup cutDim
 apply le_antisymm
 · rw [Finset.sup_le_iff]
   intro H hH
   rw [Finset.mem_range] at hH
   rw [finrank_makeP_cut E H (by rw [hElen]; omega)]
   have h1 : cutDim (if H < 3 then 0 else (H - 1) / 3) ≤ width :=
     Finset.le_sup (f := cutDim) (Finset.mem_range.mpr (by split_ifs <;> omega))
   have h2 : cutDim (if H < 3 then 0 else (H - 2) / 3) ≤ width :=
     Finset.le_sup (f := cutDim) (Finset.mem_range.mpr (by split_ifs <;> omega))
   have h01 : (if 1 ≤ H ∧ H < 3 * (E.length + 1) then 1 else 0) ≤ 1 := by split_ifs <;> omega
   change (if 1 ≤ H ∧ H < 3 * (E.length + 1) then 1 else 0) +
     cutDim (if H < 3 then 0 else (H - 1) / 3) +
     cutDim (if H < 3 then 0 else (H - 2) / 3) ≤ 1 + 2 * width
   omega
 · have hcut_le : ∀ h ∈ Finset.range (e + 1), 1 + 2 * cutDim h ≤
       (Finset.range (3 * (e + 1) + 1)).sup (fun H =>
         Module.finrank (ZMod 2)
           (((Submodule.span (ZMod 2)
               (↑(((makeP E).take H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) ⊓
             Submodule.span (ZMod 2)
               (↑(((makeP E).drop H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset)) :
             Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2)))) := by
     intro h hh
     rw [Finset.mem_range] at hh
     by_cases hlt : h < e
     · let H := 3 * (h + 1)
       have hHmem : H ∈ Finset.range (3 * (e + 1) + 1) := Finset.mem_range.mpr (by omega)
       have hval := finrank_makeP_cut E H (by rw [hElen]; omega)
       dsimp only at hval
       have hcond : 1 ≤ H ∧ H < 3 * (E.length + 1) := by rw [hElen]; omega
       have hn3 : ¬ (H < 3) := by omega
       have hd1 : (H - 1) / 3 = h := by omega
       have hd2 : (H - 2) / 3 = h := by omega
       have hle := Finset.le_sup (f := fun H =>
         Module.finrank (ZMod 2)
           (((Submodule.span (ZMod 2)
               (↑(((makeP E).take H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) ⊓
             Submodule.span (ZMod 2)
               (↑(((makeP E).drop H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset)) :
             Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2)))) hHmem
       rw [hval] at hle
       simp only [hcond, and_self, ↓reduceIte, hn3, hd1, hd2] at hle
       change 1 + cutDim h + cutDim h ≤ _ at hle
       omega
     · have heq : h = e := by omega
       rw [heq]
       have hcut_e : cutDim e = 0 := by
         have htk : E.take e = E := List.take_of_length_le (by omega)
         have hdr : E.drop e = [] := List.drop_eq_nil_of_le (by omega)
         have hnil : comps [] = n + 1 := by
           have heqv : Quot (fun u v : Fin (n + 1) => (u, v) ∈ ([] : List _)) ≃ Fin (n + 1) :=
             { toFun := Quot.lift id (fun _ _ h => by cases h)
               invFun := Quot.mk _
               left_inv := fun q => by induction q using Quot.ind with | _ _ => rfl
               right_inv := fun _ => rfl }
           change Nat.card _ = n + 1
           rw [Nat.card_congr heqv, Nat.card_eq_fintype_card, Fintype.card_fin]
         dsimp only [cutDim]
         rw [htk, hdr, hnil]
         omega
       rw [hcut_e, mul_zero, add_zero]
       have h1mem : 1 ∈ Finset.range (3 * (e + 1) + 1) := Finset.mem_range.mpr (by omega)
       have hval := finrank_makeP_cut E 1 (by rw [hElen]; omega)
       dsimp only at hval
       have hcond : 1 ≤ 1 ∧ 1 < 3 * (E.length + 1) := by rw [hElen]; omega
       have hle := Finset.le_sup (f := fun H =>
         Module.finrank (ZMod 2)
           (((Submodule.span (ZMod 2)
               (↑(((makeP E).take H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) ⊓
             Submodule.span (ZMod 2)
               (↑(((makeP E).drop H).map (fun w (i : Fin (2 * n + 1)) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset)) :
             Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2)))) h1mem
       rw [hval] at hle
       simp only [hcond, and_self, ↓reduceIte] at hle
       omega
   obtain ⟨h0, hh0, hsup_eq⟩ := Finset.exists_mem_eq_sup (Finset.range (e + 1))
     ⟨0, Finset.mem_range.mpr (by omega)⟩ cutDim
   change 1 + 2 * (Finset.range (e + 1)).sup cutDim ≤ _
   rw [hsup_eq]
   exact hcut_le h0 hh0
def rotN (k h w : ℕ) : ℕ :=
 ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2 ^ k
def stepN (k w : ℕ) : ℕ :=
 (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
   (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))).toNat <<< i)) 0
def stateN (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k)) : ℕ :=
 let g := if col then 2 else 1
 (List.finRange r).foldl (fun x j =>
   stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^
     rotN k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
   (rotN k (if col then 3 else 1) w ^^^ name)
def reachN (r : ℕ) (col : Bool) : ℕ := if col then 7 * r - 2 else 5 * r - 3
def delayN (r : ℕ) (col : Bool) : ℕ := if col then 3 * r + 1 else 2 * r - 2
lemma rotN_lt {k : ℕ} (h w : ℕ) : rotN k h w < 2 ^ k :=
 Nat.mod_lt _ (Nat.two_pow_pos k)
lemma rotN_testBit {k : ℕ} (hk : 0 < k) (h w : ℕ) (hw : w < 2 ^ k) (idx : ℕ) (hidx : idx < k) :
   (rotN k h w).testBit idx = w.testBit ((idx + k - h % k) % k) := by
 unfold rotN
 rw [Nat.testBit_mod_two_pow, decide_eq_true hidx, Bool.true_and, Nat.testBit_or,
   Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
 have hmod_lt : h % k < k := Nat.mod_lt h hk
 by_cases hge : h % k ≤ idx
 · have hhi : w.testBit (k - h % k + idx) = false := by
     apply Nat.testBit_lt_two_pow
     exact lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega))
   have hidx_eq : (idx + k - h % k) % k = idx - h % k := by
     have h1 : idx + k - h % k = (idx - h % k) + k := by omega
     rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
   rw [decide_eq_true hge, Bool.true_and, hhi, Bool.or_false, hidx_eq]
 · have hlt : idx < h % k := by omega
   have hidx_eq : (idx + k - h % k) % k = k - h % k + idx := by
     have h1 : idx + k - h % k = k - h % k + idx := by omega
     rw [h1, Nat.mod_eq_of_lt (by omega)]
   rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, hidx_eq]
lemma foldl_or_bit_spec (f : ℕ → Bool) (n : ℕ) :
   let val := (List.range n).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0
   val < 2 ^ n ∧ ∀ idx : ℕ, val.testBit idx = if idx < n then f idx else false := by
 induction n with
 | zero =>
   dsimp only
   simp [Nat.zero_testBit]
 | succ n ih =>
   dsimp only at ih ⊢
   rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
   set prev := (List.range n).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0
   obtain ⟨hlt, hbit⟩ := ih
   have hsh_lt : (f n).toNat <<< n < 2 ^ (n + 1) := by
     rw [Nat.shiftLeft_eq]
     cases f n
     · simp
     · simp only [Bool.toNat_true, one_mul, pow_succ']; omega
   have hprev_lt : prev < 2 ^ (n + 1) := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
   refine ⟨Nat.or_lt_two_pow hprev_lt hsh_lt, ?_⟩
   intro idx
   rw [Nat.testBit_or, hbit idx, Nat.testBit_shiftLeft]
   by_cases hlt_n : idx < n
   · have h1 : ¬ (n ≤ idx) := by omega
     have h2 : idx < n + 1 := by omega
     simp [hlt_n, h1, h2]
   · by_cases heq : idx = n
     · subst heq
       simp only [lt_irrefl, ↓reduceIte, Bool.false_or, le_refl, decide_true, Bool.true_and,
         Nat.sub_self, lt_add_iff_pos_right, zero_lt_one]
       cases f idx <;> decide
     · have hgt : n < idx := by omega
       have hnot1 : ¬ (idx < n + 1) := by omega
       have hpos : 1 ≤ idx - n := by omega
       have hzero : ((f n).toNat).testBit (idx - n) = false := by
         apply Nat.testBit_lt_two_pow
         cases f n
         · simp
         · calc (1 : ℕ) < 2 ^ 1 := by omega
             _ ≤ 2 ^ (idx - n) := Nat.pow_le_pow_right (by omega) hpos
       simp [hlt_n, hnot1, hzero]
lemma stepN_lt (k w : ℕ) : stepN k w < 2 ^ k :=
 (foldl_or_bit_spec _ k).1
lemma stepN_testBit (k w idx : ℕ) (hidx : idx < k) :
   (stepN k w).testBit idx =
     xor (w.testBit idx) (!(w.testBit ((idx + 1) % k)) && w.testBit ((idx + 2) % k)) := by
 have h := (foldl_or_bit_spec
   (fun i => xor (w.testBit i) (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))) k).2 idx
 simpa [stepN, hidx] using h
def rotB (k : ℕ) (hk : 0 < k) (h : ℕ) (w : Fin k → Bool) (idx : Fin k) : Bool :=
 w ⟨(idx.val + k - h % k) % k, Nat.mod_lt _ hk⟩
def stepB (k : ℕ) (hk : 0 < k) (w : Fin k → Bool) (idx : Fin k) : Bool :=
 xor (w idx) (!(w ⟨(idx.val + 1) % k, Nat.mod_lt _ hk⟩) && w ⟨(idx.val + 2) % k, Nat.mod_lt _ hk⟩)
def stateStepB (k : ℕ) (hk : 0 < k) (col : Bool) (j : ℕ)
   (inp : (Fin k ⊕ Fin k ⊕ Fin k) → Bool) (idx : Fin k) : Bool :=
 let x := fun i => inp (inl i)
 let w := fun i => inp (inr (inl i))
 let cj := fun i => inp (inr (inr i))
 let g := if col then 2 else 1
 let mix := fun i => xor (xor (x i) (rotB k hk g x i)) (rotB k hk (k - g) x i)
 xor (xor (stepB k hk mix idx) (rotB k hk (if col then 3 * (j + 1) + 1 else 2 * j) w idx)) (cj idx)
def stateB (k r : ℕ) (hk : 0 < k) (col : Bool)
   (inp : (Fin k ⊕ Fin k ⊕ (Fin r × Fin k)) → Bool) : Fin k → Bool :=
 let w := fun i => inp (inl i)
 let nm := fun i => inp (inr (inl i))
 let c := fun j i => inp (inr (inr (j, i)))
 let x0 := fun i => xor (rotB k hk (if col then 3 else 1) w i) (nm i)
 (List.finRange r).foldl
   (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w (c j)))) x0
lemma ec_stateStepB (k : ℕ) (hk : 0 < k) (col : Bool) (j : ℕ) :
   EC (40 * k) (stateStepB k hk col j) := by
 let I := Fin k ⊕ Fin k ⊕ Fin k
 let g := if col then 2 else 1
 have hx : EC 0 (fun (inp : I → Bool) (i : Fin k) => inp (inl i)) := ec_proj _
 have hrg : EC 0 (fun (inp : I → Bool) (i : Fin k) =>
     rotB k hk g (fun u => inp (inl u)) i) :=
   ec_proj (fun i : Fin k => (inl ⟨(i.val + k - g % k) % k, Nat.mod_lt _ hk⟩ : I))
 have hrkg : EC 0 (fun (inp : I → Bool) (i : Fin k) =>
     rotB k hk (k - g) (fun u => inp (inl u)) i) :=
   ec_proj (fun i : Fin k => (inl ⟨(i.val + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩ : I))
 have hmix : EC (12 * k)
     (fun (inp : I → Bool) (i : Fin k) =>
       xor (xor (inp (inl i)) (rotB k hk g (fun u => inp (inl u)) i))
         (rotB k hk (k - g) (fun u => inp (inl u)) i)) := by
   have h := ec_xor_of (ec_xor_of hx hrg) hrkg
   rw [Fintype.card_fin] at h
   exact ec_le h (by omega)
 let I1 := I ⊕ Fin k
 have hstep : EC (28 * k)
     (fun (y : I1 → Bool) (idx : Fin k) =>
       xor (xor (stepB k hk (fun i => y (inr i)) idx)
         (rotB k hk (if col then 3 * (j + 1) + 1 else 2 * j) (fun i => y (inl (inr (inl i)))) idx))
         (y (inl (inr (inr idx))))) := by
   have hm0 : EC 0 (fun (y : I1 → Bool) (idx : Fin k) => y (inr idx)) := ec_proj _
   have hm1 : EC 0 (fun (y : I1 → Bool) (idx : Fin k) =>
       y (inr ⟨(idx.val + 1) % k, Nat.mod_lt _ hk⟩)) := ec_proj _
   have hm2 : EC 0 (fun (y : I1 → Bool) (idx : Fin k) =>
       y (inr ⟨(idx.val + 2) % k, Nat.mod_lt _ hk⟩)) := ec_proj _
   have hst := ec_xor_of hm0 (ec_and_of (ec_not_of hm1) hm2)
   have hwf : EC 0 (fun (y : I1 → Bool) (idx : Fin k) =>
       rotB k hk (if col then 3 * (j + 1) + 1 else 2 * j)
         (fun i => y (inl (inr (inl i)))) idx) :=
     ec_proj (fun idx : Fin k =>
       (inl (inr (inl ⟨(idx.val + k - (if col then 3 * (j + 1) + 1 else 2 * j) % k) % k,
         Nat.mod_lt _ hk⟩)) : I1))
   have hcj : EC 0 (fun (y : I1 → Bool) (idx : Fin k) => y (inl (inr (inr idx)))) :=
     ec_proj _
   have htot := ec_xor_of (ec_xor_of hst hwf) hcj
   rw [Fintype.card_fin] at htot
   exact ec_le htot (by omega)
 have hlet := ec_let hmix hstep
 refine ec_le (ec_eq ?_ hlet) (by omega)
 intro inp idx; rfl
lemma ec_stateB (k r : ℕ) (hk : 0 < k) (col : Bool) :
   EC (40 * (r + 1) * k) (stateB k r hk col) := by
 let I := Fin k ⊕ Fin k ⊕ (Fin r × Fin k)
 have hx0 : EC (6 * k)
     (fun (inp : I → Bool) (i : Fin k) =>
       xor (rotB k hk (if col then 3 else 1) (fun u => inp (inl u)) i)
         (inp (inr (inl i)))) := by
   have h1 : EC 0 (fun (inp : I → Bool) (i : Fin k) =>
       rotB k hk (if col then 3 else 1) (fun u => inp (inl u)) i) :=
     ec_proj (fun i : Fin k =>
       (inl ⟨(i.val + k - (if col then 3 else 1) % k) % k, Nat.mod_lt _ hk⟩ : I))
   have h2 : EC 0 (fun (inp : I → Bool) (i : Fin k) => inp (inr (inl i))) := ec_proj _
   have h := ec_xor_of h1 h2
   rw [Fintype.card_fin] at h
   exact ec_le h (by omega)
 have htake : ∀ t : ℕ,
     EC (6 * k + t * (40 * k))
       (fun (inp : I → Bool) =>
         let w := fun i => inp (inl i)
         let nm := fun i => inp (inr (inl i))
         let c := fun j i => inp (inr (inr (j, i)))
         let x0 := fun i => xor (rotB k hk (if col then 3 else 1) w i) (nm i)
         ((List.finRange r).take t).foldl
           (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w (c j)))) x0) := by
   intro t
   induction t with
   | zero => simpa using hx0
   | succ t ih =>
     by_cases ht : t < r
     · let jj : Fin r := ⟨t, ht⟩
       let sel : (Fin k ⊕ Fin k ⊕ Fin k) → I ⊕ Fin k := fun q =>
         match q with
         | inl i => inr i
         | inr (inl i) => inl (inl i)
         | inr (inr i) => inl (inr (inr (jj, i)))
       have hstep := ec_comp (ec_proj sel) (ec_stateStepB k hk col jj.val)
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) (by nlinarith)
       intro inp idx
       have htk : (List.finRange r).take (t + 1) = (List.finRange r).take t ++ [jj] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange r) (i := t) (by simp; omega)
         simpa [jj] using h1
       simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
       congr 1; funext q; rcases q with _ | _ | _ <;> rfl
     · have htk : (List.finRange r).take (t + 1) = (List.finRange r).take t := by
         rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
       refine ec_le (ec_eq ?_ ih) (by nlinarith)
       intro inp idx; simp only [htk]
 have h := htake r
 rw [show (List.finRange r).take r = List.finRange r by rw [List.take_of_length_le]; simp] at h
 exact ec_le h (by nlinarith)
lemma stateB_eq_testBit {k r : ℕ} (hk : 0 < k) (col : Bool)
   (w name : ℕ) (hw : w < 2 ^ k) (hnm : name < 2 ^ k) (c : Fin r → Fin (2 ^ k)) :
   let wB : Fin k → Bool := fun i => w.testBit i.val
   let nmB : Fin k → Bool := fun i => name.testBit i.val
   let cB : Fin r × Fin k → Bool := fun p => (c p.1).val.testBit p.2.val
   stateN k r col w name c < 2 ^ k ∧
   ∀ idx : Fin k, (stateN k r col w name c).testBit idx.val =
     stateB k r hk col (Sum.elim wB (Sum.elim nmB cB)) idx := by
 dsimp only
 let g := if col then 2 else 1
 let wB : Fin k → Bool := fun i => w.testBit i.val
 let nmB : Fin k → Bool := fun i => name.testBit i.val
 let cB : Fin r × Fin k → Bool := fun p => (c p.1).val.testBit p.2.val
 have htake : ∀ t : ℕ, t ≤ r →
     let xN := ((List.finRange r).take t).foldl (fun x j =>
       stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^
         rotN k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
       (rotN k (if col then 3 else 1) w ^^^ name)
     let xB := ((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim wB (fun i => cB (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) wB i) (nmB i))
     xN < 2 ^ k ∧ ∀ idx : Fin k, xN.testBit idx.val = xB idx := by
   intro t
   induction t with
   | zero =>
     intro _
     simp only [List.take_zero, List.foldl_nil]
     refine ⟨Nat.xor_lt_two_pow (rotN_lt _ _) hnm, ?_⟩
     intro idx
     rw [Nat.testBit_xor, rotN_testBit hk _ w hw idx.val idx.isLt]
     rfl
   | succ t ih =>
     intro ht
     obtain ⟨hprev_lt, hprev_bit⟩ := ih (by omega)
     let jj : Fin r := ⟨t, ht⟩
     have htk : (List.finRange r).take (t + 1) = (List.finRange r).take t ++ [jj] := by
       have h1 := List.take_succ_eq_append_getElem (l := List.finRange r) (i := t) (by simp; omega)
       simpa [jj] using h1
     dsimp only
     rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil,
       List.foldl_append, List.foldl_cons, List.foldl_nil]
     set xN := ((List.finRange r).take t).foldl (fun x j =>
       stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^
         rotN k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
       (rotN k (if col then 3 else 1) w ^^^ name)
     set xB := ((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim wB (fun i => cB (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) wB i) (nmB i))
     refine ⟨Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepN_lt k _) (rotN_lt _ _)) (c jj).isLt, ?_⟩
     intro idx
     rw [Nat.testBit_xor, Nat.testBit_xor, stepN_testBit k _ idx.val idx.isLt,
       rotN_testBit hk _ w hw idx.val idx.isLt]
     have hmix_bit : ∀ u : Fin k,
         (xN ^^^ rotN k g xN ^^^ rotN k (k - g) xN).testBit u.val =
           xor (xor (xB u) (rotB k hk g xB u)) (rotB k hk (k - g) xB u) := by
       intro u
       rw [Nat.testBit_xor, Nat.testBit_xor, hprev_bit u,
         rotN_testBit hk g xN hprev_lt u.val u.isLt,
         rotN_testBit hk (k - g) xN hprev_lt u.val u.isLt]
       have h1 := hprev_bit ⟨(u.val + k - g % k) % k, Nat.mod_lt _ hk⟩
       have h2 := hprev_bit ⟨(u.val + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩
       rw [h1, h2]; rfl
     have h0 := hmix_bit idx
     have h1 := hmix_bit ⟨(idx.val + 1) % k, Nat.mod_lt _ hk⟩
     have h2 := hmix_bit ⟨(idx.val + 2) % k, Nat.mod_lt _ hk⟩
     rw [h0, h1, h2]
     rfl
 have h := htake r le_rfl
 rw [show (List.finRange r).take r = List.finRange r by rw [List.take_of_length_le]; simp] at h
 exact h
lemma mod_sub_shift {k : ℕ} (hk : 0 < k) (p m s : ℕ) (hms : s ≤ m) :
   ((p + m) % k + k - s % k) % k = (p + (m - s)) % k := by
 have h1 : (p + m) % k = ((p + (m - s)) % k + s % k) % k := by
   rw [← Nat.add_mod, show p + (m - s) + s = p + m by omega]
 set B := (p + (m - s)) % k
 set S := s % k
 have hB : B < k := Nat.mod_lt _ hk
 have hS : S < k := Nat.mod_lt _ hk
 rw [h1]
 by_cases hBS : B + S < k
 · rw [Nat.mod_eq_of_lt hBS, show B + S + k - S = B + k by omega,
     Nat.add_mod_right, Nat.mod_eq_of_lt hB]
 · have hmod : (B + S) % k = B + S - k := by
     calc (B + S) % k = ((B + S - k) + k) % k := by congr 1; omega
       _ = (B + S - k) % k := Nat.add_mod_right _ _
       _ = B + S - k := Nat.mod_eq_of_lt (by omega)
   rw [hmod, show B + S - k + k - S = B by omega, Nat.mod_eq_of_lt hB]
lemma mod_add_shift {k : ℕ} (_hk : 0 < k) (p m g : ℕ) (hg : g < k) :
   ((p + m) % k + k - (k - g) % k) % k = (p + (m + g)) % k := by
 by_cases hg0 : g = 0
 · subst hg0; simp [Nat.mod_self, Nat.add_mod_right]
 · rw [Nat.mod_eq_of_lt (by omega : k - g < k)]
   have h2 : (p + m) % k + k - (k - g) = (p + m) % k + g := by omega
   rw [h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
lemma stateB_congr_reach {k r : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (col : Bool)
   (hk3 : 2 < k) (p : ℕ) (w1 w2 nm : Fin k → Bool) (c : Fin r × Fin k → Bool)
   (hag : ∀ δ ≤ reachN r col,
     w1 ⟨(p + δ) % k, Nat.mod_lt _ hk⟩ = w2 ⟨(p + δ) % k, Nat.mod_lt _ hk⟩) :
   stateB k r hk col (Sum.elim w1 (Sum.elim nm c)) ⟨(p + delayN r col) % k, Nat.mod_lt _ hk⟩ =
   stateB k r hk col (Sum.elim w2 (Sum.elim nm c)) ⟨(p + delayN r col) % k, Nat.mod_lt _ hk⟩ := by
 let g := if col then 2 else 1
 let loT : ℕ → ℕ := fun t => delayN r col - g * (r - t)
 let hiT : ℕ → ℕ := fun t => delayN r col + (g + 2) * (r - t)
 have htake : ∀ t : ℕ, t ≤ r → ∀ m_pos : ℕ, loT t ≤ m_pos → m_pos ≤ hiT t →
     (((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w1 (fun i => c (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) w1 i) (nm i)))
         ⟨(p + m_pos) % k, Nat.mod_lt _ hk⟩ =
     (((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w2 (fun i => c (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) w2 i) (nm i)))
         ⟨(p + m_pos) % k, Nat.mod_lt _ hk⟩ := by
   intro t
   induction t with
   | zero =>
     intro _ m_pos hlo hhi
     simp only [List.take_zero, List.foldl_nil, rotB]
     congr 1
     have hsh : (if col then 3 else 1) ≤ m_pos := by
       cases col <;> simp only [loT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega
     have hrc : m_pos - (if col then 3 else 1) ≤ reachN r col := by
       cases col <;> simp only [hiT, delayN, reachN, g, Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega
     have hidx := mod_sub_shift hk p m_pos (if col then 3 else 1) hsh
     have hfin : (⟨((p + m_pos) % k + k - (if col then 3 else 1) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
         ⟨(p + (m_pos - (if col then 3 else 1))) % k, Nat.mod_lt _ hk⟩ := Fin.ext hidx
     rw [hfin]
     exact hag _ hrc
   | succ t ih =>
     intro ht m_pos hlo hhi
     have hih := ih (by omega)
     let jj : Fin r := ⟨t, ht⟩
     have htk : (List.finRange r).take (t + 1) = (List.finRange r).take t ++ [jj] := by
       have h1 := List.take_succ_eq_append_getElem (l := List.finRange r) (i := t) (by simp; omega)
       simpa [jj] using h1
     rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil,
       List.foldl_append, List.foldl_cons, List.foldl_nil]
     set x1 := ((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w1 (fun i => c (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) w1 i) (nm i))
     set x2 := ((List.finRange r).take t).foldl
       (fun x j => stateStepB k hk col j.val (Sum.elim x (Sum.elim w2 (fun i => c (j, i)))))
       (fun i => xor (rotB k hk (if col then 3 else 1) w2 i) (nm i))
     dsimp only [stateStepB, stepB, rotB, Sum.elim_inl, Sum.elim_inr]
     have hmix_eq : ∀ d2 : ℕ, d2 ≤ 2 →
         xor (xor (x1 ⟨((p + m_pos) % k + d2) % k, Nat.mod_lt _ hk⟩)
           (x1 ⟨(((p + m_pos) % k + d2) % k + k - g % k) % k, Nat.mod_lt _ hk⟩))
           (x1 ⟨(((p + m_pos) % k + d2) % k + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩) =
         xor (xor (x2 ⟨((p + m_pos) % k + d2) % k, Nat.mod_lt _ hk⟩)
           (x2 ⟨(((p + m_pos) % k + d2) % k + k - g % k) % k, Nat.mod_lt _ hk⟩))
           (x2 ⟨(((p + m_pos) % k + d2) % k + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩) := by
       intro d2 hd2
       have hmod_d2 : ((p + m_pos) % k + d2) % k = (p + (m_pos + d2)) % k := by
         rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
       have hg_lt : g < k := by cases col <;> simp only [g, Bool.false_eq_true, ↓reduceIte] <;> omega
       have hge_g : g ≤ m_pos + d2 := by
         cases col <;> simp only [loT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega
       have he0 : x1 ⟨((p + m_pos) % k + d2) % k, Nat.mod_lt _ hk⟩ =
           x2 ⟨((p + m_pos) % k + d2) % k, Nat.mod_lt _ hk⟩ := by
         have hf : (⟨((p + m_pos) % k + d2) % k, Nat.mod_lt _ hk⟩ : Fin k) =
             ⟨(p + (m_pos + d2)) % k, Nat.mod_lt _ hk⟩ := Fin.ext hmod_d2
         rw [hf]
         exact hih (m_pos + d2)
           (by cases col <;> simp only [loT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega)
           (by cases col <;> simp only [hiT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega)
       have he1 : x1 ⟨(((p + m_pos) % k + d2) % k + k - g % k) % k, Nat.mod_lt _ hk⟩ =
           x2 ⟨(((p + m_pos) % k + d2) % k + k - g % k) % k, Nat.mod_lt _ hk⟩ := by
         have hf : (⟨(((p + m_pos) % k + d2) % k + k - g % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
             ⟨(p + (m_pos + d2 - g)) % k, Nat.mod_lt _ hk⟩ := Fin.ext (by
           rw [hmod_d2]; exact mod_sub_shift hk p (m_pos + d2) g hge_g)
         rw [hf]
         exact hih (m_pos + d2 - g)
           (by cases col <;> simp only [loT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega)
           (by cases col <;> simp only [hiT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega)
       have he2 : x1 ⟨(((p + m_pos) % k + d2) % k + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩ =
           x2 ⟨(((p + m_pos) % k + d2) % k + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩ := by
         have hf : (⟨(((p + m_pos) % k + d2) % k + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
             ⟨(p + (m_pos + d2 + g)) % k, Nat.mod_lt _ hk⟩ := Fin.ext (by
           rw [hmod_d2]; exact mod_add_shift hk p (m_pos + d2) g hg_lt)
         rw [hf]
         exact hih (m_pos + d2 + g)
           (by cases col <;> simp only [loT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega)
           (by cases col <;> simp only [hiT, delayN, g, Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega)
       rw [he0, he1, he2]
     have hm0 := hmix_eq 0 (by omega)
     simp only [add_zero, Nat.mod_mod] at hm0
     have hm1 := hmix_eq 1 (by omega)
     have hm2 := hmix_eq 2 (by omega)
     have hw_eq : w1 ⟨((p + m_pos) % k + k - (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) % k) % k, Nat.mod_lt _ hk⟩ =
         w2 ⟨((p + m_pos) % k + k - (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) % k) % k, Nat.mod_lt _ hk⟩ := by
       have hsh : (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) ≤ m_pos := by
         cases col <;> simp only [loT, delayN, g, jj, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega
       have hrc : m_pos - (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) ≤ reachN r col := by
         cases col <;> simp only [hiT, delayN, reachN, g, jj, Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega
       have hf : (⟨((p + m_pos) % k + k - (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
           ⟨(p + (m_pos - (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val))) % k, Nat.mod_lt _ hk⟩ :=
         Fin.ext (mod_sub_shift hk p m_pos _ hsh)
       rw [hf]
       exact hag _ hrc
     rw [hm0, hm1, hm2, hw_eq]
 have h := htake r le_rfl (delayN r col) (by dsimp [loT]; omega) (by dsimp [hiT]; omega)
 rw [show (List.finRange r).take r = List.finRange r by rw [List.take_of_length_le]; simp] at h
 exact h
abbrev BSt (D m : ℕ) := (Fin D × Fin m) ⊕ Fin D
def bMt {D m : ℕ} (st : BSt D m → Bool) (l : Fin D) (j : Fin m) : Bool :=
 st (inl (l, j))
def bUs {D m : ℕ} (st : BSt D m → Bool) (l : Fin D) : Bool :=
 st (inr l)
def bVc {D m : ℕ} (st : BSt D m → Bool) (l : Fin D) (j : Fin m) : ZMod 2 :=
 b2z (bMt st l j)
def bDc {D m : ℕ} (st : BSt D m → Bool) (code : Fin D → Bool) (j : Fin m) : ZMod 2 :=
 ∑ l : Fin D, b2z (code l) * bVc st l j
def cVal {D m : ℕ} (st : BSt D m → Bool) (code : Fin D → Bool) : Prop :=
 ∀ l : Fin D, bUs st l = false → code l = false
def BInv {D m : ℕ} (I : Submodule (ZMod 2) (Fin m → ZMod 2)) (st : BSt D m → Bool) : Prop :=
 (∀ l : Fin D, bUs st l = false → bVc st l = 0) ∧
 LinearIndependent (ZMod 2) (fun l : {l : Fin D // bUs st l = true} => bVc st l.val) ∧
 Submodule.span (ZMod 2) (Set.range (fun l : {l : Fin D // bUs st l = true} => bVc st l.val)) = I
lemma bsDec_mem {D m : ℕ} {I : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st : BSt D m → Bool} (hinv : BInv I st) (code : Fin D → Bool) :
   bDc st code ∈ I := by
 have heq : bDc st code = ∑ l : Fin D, b2z (code l) • bVc st l := by
   funext j; simp [bDc]
 rw [heq]
 apply Submodule.sum_mem
 intro l _
 cases hu : bUs st l
 · rw [hinv.1 l hu, smul_zero]; exact Submodule.zero_mem _
 · apply Submodule.smul_mem
   rw [← hinv.2.2]
   exact Submodule.subset_span ⟨⟨l, hu⟩, rfl⟩
lemma bsDec_inj {D m : ℕ} {I : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st : BSt D m → Bool} (hinv : BInv I st)
   {c1 c2 : Fin D → Bool} (hc1 : cVal st c1) (hc2 : cVal st c2)
   (heq : bDc st c1 = bDc st c2) : c1 = c2 := by
 have hsum : ∑ l : {l : Fin D // bUs st l = true}, (b2z (c1 l.val) - b2z (c2 l.val)) • bVc st l.val = 0 := by
   funext j
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
   have hsub : ∀ c : Fin D → Bool, cVal st c →
       ∑ l : {l : Fin D // bUs st l = true}, b2z (c l.val) * bVc st l.val j = bDc st c j := by
     intro c hc
     unfold bDc
     rw [← Finset.sum_subset (Finset.filter_subset (fun l : Fin D => bUs st l = true) Finset.univ)]
     · symm
       exact Finset.sum_bij (fun l hl => ⟨l, (Finset.mem_filter.mp hl).2⟩)
         (fun _ _ => Finset.mem_univ _)
         (fun _ _ _ _ h => congrArg Subtype.val h)
         (fun r _ => ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property⟩, rfl⟩)
         (fun _ _ => rfl)
     · intro l _ hnot
       simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnot
       rw [hc l hnot]; simp [b2z]
   rw [hsub c1 hc1, hsub c2 hc2, heq, sub_self]
 have hlin := Fintype.linearIndependent_iff.mp hinv.2.1 _ hsum
 funext l
 cases hu : bUs st l
 · rw [hc1 l hu, hc2 l hu]
 · have hl := sub_eq_zero.mp (hlin ⟨l, hu⟩)
   rw [← z2b_b2z (c1 l), ← z2b_b2z (c2 l), hl]
lemma bsDec_surj {D m : ℕ} {I : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st : BSt D m → Bool} (hinv : BInv I st)
   {u : Fin m → ZMod 2} (hu : u ∈ I) :
   ∃ c : Fin D → Bool, cVal st c ∧ bDc st c = u := by
 rw [← hinv.2.2, Submodule.mem_span_range_iff_exists_fun] at hu
 obtain ⟨α, rfl⟩ := hu
 refine ⟨fun l => if h : bUs st l = true then z2b (α ⟨l, h⟩) else false,
   fun l h0 => by simp [h0], ?_⟩
 funext j
 unfold bDc
 simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
 rw [← Finset.sum_subset (Finset.filter_subset (fun l : Fin D => bUs st l = true) Finset.univ)]
 · exact Finset.sum_bij (fun l hl => ⟨l, (Finset.mem_filter.mp hl).2⟩)
     (fun _ _ => Finset.mem_univ _)
     (fun _ _ _ _ h => congrArg Subtype.val h)
     (fun r _ => ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property⟩, rfl⟩)
     (fun l hl => by
       have hlt : bUs st l = true := (Finset.mem_filter.mp hl).2
       simp only [hlt, ↓reduceDIte, b2z_z2b])
 · intro l _ hnot
   simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnot
   simp [hnot, b2z]
lemma bsInv_finrank {D m : ℕ} {I : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st : BSt D m → Bool} (hinv : BInv I st) :
   Module.finrank (ZMod 2) I = (Finset.univ.filter (fun l : Fin D => bUs st l = true)).card := by
 rw [← hinv.2.2, finrank_span_eq_card hinv.2.1, Fintype.card_subtype]
def iSN (m : ℕ) (inp : (Fin m × Fin m) ⊕ Fin m → Bool) (_ : Unit) : Bool :=
 decide (∀ f : Fin m,
   (List.finRange m).foldl (fun acc j => xor acc (inp (inl (f, j)) && inp (inr j))) false = false)
lemma foldl_xor_b2z {α : Type} [Fintype α] [DecidableEq α] (l : List α) (hnd : l.Nodup)
   (g : α → Bool) :
   b2z (l.foldl (fun acc x => xor acc (g x)) false) = ∑ x ∈ l.toFinset, b2z (g x) := by
 have hgen : ∀ init : Bool,
     b2z (l.foldl (fun acc x => xor acc (g x)) init) = b2z init + ∑ x ∈ l.toFinset, b2z (g x) := by
   induction l with
   | nil => intro init; simp
   | cons hd tl ih =>
     intro init
     rw [List.nodup_cons] at hnd
     rw [List.foldl_cons, ih hnd.2, b2z_xor, List.toFinset_cons,
       Finset.sum_insert (by simpa using hnd.1)]
     ring
 simpa [b2z] using hgen false
lemma ec_xorList {α : Type} [Fintype α] (ls : List α) :
   EC (5 * ls.length + 2) (fun (x : α → Bool) (_ : Unit) => ls.foldl (fun acc a => xor acc (x a)) false) := by
 induction ls using List.reverseRecOn with
 | nil => simpa using ec_const (ι := α) (fun (_ : Unit) => false)
 | append_singleton ls a ih =>
   have h1 := ec_xor_of ih (ec_proj (fun (_ : Unit) => a))
   rw [Fintype.card_unit] at h1
   refine ec_le (ec_eq ?_ h1) (by simp; omega)
   intro x u; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
lemma iSN_sp {R m : ℕ} (A0 : Fin R × Fin m → Bool) (v : Fin m → Bool) :
   iSN m (Sum.elim (fun p => rNV (rref A0) p.1 p.2) v) () = true ↔
     (fun j => b2z (v j)) ∈
       Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin m => b2z (A0 (i, j)))) := by
 rw [rref_in_rowSpace]
 unfold iSN
 rw [decide_eq_true_iff]
 simp only [Sum.elim_inl, Sum.elim_inr]
 apply forall_congr'; intro f
 have hfold := foldl_xor_b2z (List.finRange m) (List.nodup_finRange m)
   (fun j => rNV (rref A0) f j && v j)
 have hfin : (List.finRange m).toFinset = Finset.univ := by ext j; simp
 rw [hfin] at hfold
 simp_rw [b2z_and] at hfold
 constructor
 · intro h; rw [← hfold, h]; rfl
 · intro h
   have h0 : b2z ((List.finRange m).foldl (fun acc j => xor acc (rNV (rref A0) f j && v j)) false) = 0 := by
     rw [hfold]; exact h
   have h1 := z2b_b2z ((List.finRange m).foldl (fun acc j => xor acc (rNV (rref A0) f j && v j)) false)
   rw [← h1, h0]; rfl
lemma ec_iSN (m : ℕ) : EC (12 * (m + 1) * (m + 1)) (iSN m) := by
 let I := (Fin m × Fin m) ⊕ Fin m
 have hrow : EC (m * (8 * m + 5))
     (fun (inp : I → Bool) (f : Fin m) =>
       !((List.finRange m).foldl (fun acc j => xor acc (inp (inl (f, j)) && inp (inr j))) false)) := by
   have hfam : EC (Fintype.card (Fin m) * (8 * m + 5))
       (fun (inp : I → Bool) (p : Fin m × Unit) =>
         !((List.finRange m).foldl (fun acc j => xor acc (inp (inl (p.1, j)) && inp (inr j))) false)) :=
     ec_family (f := fun (f : Fin m) (inp : I → Bool) (_ : Unit) =>
         !((List.finRange m).foldl (fun acc j => xor acc (inp (inl (f, j)) && inp (inr j))) false))
       (fun f => by
         have hand : EC m (fun (inp : I → Bool) (j : Fin m) => inp (inl (f, j)) && inp (inr j)) := by
           have h := ec_and_of (ec_proj (fun j : Fin m => (inl (f, j) : I)))
             (ec_proj (fun j : Fin m => (inr j : I)))
           simpa [Fintype.card_fin] using h
         have hxor := ec_comp hand (ec_xorList (α := Fin m) (List.finRange m))
         have hnot := ec_not_of hxor
         rw [Fintype.card_unit, List.length_finRange] at hnot
         refine ec_le (ec_eq ?_ hnot) (by omega)
         intro inp u; rfl)
   rw [Fintype.card_fin] at hfam
   have hp := ec_comp hfam (ec_proj (fun f : Fin m => (f, ())))
   rw [add_zero] at hp; exact hp
 have hall := ec_comp hrow (ec_all (α := Fin m))
 rw [Fintype.card_fin] at hall
 refine ec_le (ec_eq ?_ hall) (by nlinarith)
 intro inp u
 simp only [iSN, Bool.not_eq_true']
def sBas (D m : ℕ) (inp : BSt D m ⊕ Fin m → Bool) : Unit ⊕ Fin D → Bool :=
 let cols : Fin D → Fin m → Bool := fun l j => inp (inl (inr l)) && inp (inl (inl (l, j)))
 let rhs : Fin m → Bool := fun j => inp (inr j)
 let st := rref (aMt cols rhs)
 Sum.elim
   (fun _ => !(rPC st (Fin.last D)))
   (fun l => inp (inl (inr l)) && rNV st (Fin.last D) l.castSucc)
lemma ec_sBas (D m : ℕ) :
   EC (100 * (D + 1) * (m + 1) * (m + D + 2)) (sBas D m) := by
 let I := BSt D m ⊕ Fin m
 have haug : EC (m * (D + 1))
     (fun (inp : I → Bool) (p : Fin m × Fin (D + 1)) =>
       aMt (fun l j => inp (inl (inr l)) && inp (inl (inl (l, j))))
         (fun j => inp (inr j)) p) := by
   have hcols : EC (D * m)
       (fun (inp : I → Bool) (p : Fin D × Fin m) =>
         inp (inl (inr p.1)) && inp (inl (inl p))) := by
     have h := ec_and_of (ec_proj (fun p : Fin D × Fin m => (inl (inr p.1) : I)))
       (ec_proj (fun p : Fin D × Fin m => (inl (inl p) : I)))
     simpa [Fintype.card_prod] using h
   let sel : Fin m × Fin (D + 1) → I ⊕ (Fin D × Fin m) := fun p =>
     Fin.lastCases (inl (inr p.1)) (fun q => inr (q, p.1)) p.2
   have htot := ec_let hcols (ec_proj sel)
   refine ec_le (ec_eq ?_ htot) (by nlinarith)
   intro inp p
   unfold aMt sel
   refine Fin.lastCases ?_ ?_ p.2 <;> simp
 have hrref := ec_comp haug (ec_rref m (D + 1))
 let I1 := I ⊕ RIdx m (D + 1)
 have hnv : EC (20 * (D + 1) * (D + 1) * (m + 2))
     (fun (y : I1 → Bool) (p : Fin (D + 1) × Fin (D + 1)) =>
       rNV (fun r => y (inr r)) p.1 p.2) := by
   have h := ec_comp (ec_proj (fun r : RIdx m (D + 1) => (inr r : I1))) (ec_rNV m (D + 1))
   rw [zero_add] at h
   exact ec_le h (by nlinarith)
 let I2 := I1 ⊕ (Fin (D + 1) × Fin (D + 1))
 have hout : EC (D + 2)
     (fun (z : I2 → Bool) =>
       Sum.elim
         (fun (_ : Unit) => !(z (inl (inr (inr (inr (Fin.last D)))))))
         (fun l : Fin D => z (inl (inl (inl (inr l)))) && z (inr (Fin.last D, l.castSucc)))) := by
   have h1 := ec_not_of (ec_proj (fun (_ : Unit) => (inl (inr (inr (inr (Fin.last D)))) : I2)))
   have h2 := ec_and_of (ec_proj (fun l : Fin D => (inl (inl (inl (inr l))) : I2)))
     (ec_proj (fun l : Fin D => (inr (Fin.last D, l.castSucc) : I2)))
   have hp := ec_pair h1 h2
   simp only [Fintype.card_unit, Fintype.card_fin] at hp
   exact ec_le hp (by omega)
 have htot := ec_let hrref (ec_let hnv hout)
 refine ec_le (ec_eq ?_ htot) ?_
 · intro inp q; rcases q with u | l <;> rfl
 · have h0 : m * (D + 1) ≤ (D + 1) * (m + 1) * (m + D + 2) := by
     have ha : m ≤ (m + 1) * (m + D + 2) := by nlinarith
     calc m * (D + 1) = (D + 1) * m := by ring
       _ ≤ (D + 1) * ((m + 1) * (m + D + 2)) := Nat.mul_le_mul_left _ ha
       _ = (D + 1) * (m + 1) * (m + D + 2) := by ring
   have h1 : (D + 1) * (D + 1) * (m + 2) ≤ 2 * (D + 1) * (m + 1) * (m + D + 2) := by
     have ha : (D + 1) * (m + 2) ≤ 2 * (m + 1) * (m + D + 2) := by nlinarith
     calc (D + 1) * (D + 1) * (m + 2) = (D + 1) * ((D + 1) * (m + 2)) := by ring
       _ ≤ (D + 1) * (2 * (m + 1) * (m + D + 2)) := Nat.mul_le_mul_left _ ha
       _ = 2 * (D + 1) * (m + 1) * (m + D + 2) := by ring
   have h2 : 4 + (D + 2) ≤ 6 * (D + 1) * (m + 1) * (m + D + 2) := by
     have ha : 1 ≤ (m + 1) * (m + D + 2) := by nlinarith
     calc 4 + (D + 2) ≤ 6 * (D + 1) := by omega
       _ ≤ 6 * (D + 1) * ((m + 1) * (m + D + 2)) := Nat.le_mul_of_pos_right _ ha
       _ = 6 * (D + 1) * (m + 1) * (m + D + 2) := by ring
   have h3 : 30 * (D + 1) * (m + 1) * (m + (D + 1) + 1) = 30 * (D + 1) * (m + 1) * (m + D + 2) := by ring
   linarith only [h0, h1, h2, h3]
lemma sBas_sp {D m : ℕ} (st : BSt D m → Bool) (rhs : Fin m → Bool)
   (hzero : ∀ l : Fin D, bUs st l = false → bVc st l = 0) :
   let out := sBas D m (Sum.elim st rhs)
   let I := Submodule.span (ZMod 2) (Set.range (fun l : {l : Fin D // bUs st l = true} => bVc st l.val))
   (out (inl ()) = true ↔ (fun j => b2z (rhs j)) ∈ I) ∧
   (out (inl ()) = true →
     cVal st (fun l => out (inr l)) ∧
     bDc st (fun l => out (inr l)) = fun j => b2z (rhs j)) := by
 dsimp only [sBas]
 let cols : Fin D → Fin m → Bool := fun l j => bUs st l && bMt st l j
 have hcols_eq : (fun l j => Sum.elim st rhs (inl (inr l)) && Sum.elim st rhs (inl (inl (l, j)))) =
     cols := rfl
 have hrhs_eq : (fun j => Sum.elim st rhs (inr j)) = rhs := rfl
 have hcol_vec : ∀ l : Fin D, (fun j => b2z (cols l j)) = bVc st l := by
   intro l
   cases hu : bUs st l
   · funext j
     have h0 := congrFun (hzero l hu) j
     simp [cols, hu, b2z, h0]
   · funext j; simp [cols, hu, bVc]
 obtain ⟨hiff, hsol⟩ := rref_solve_spec cols rhs
 have hspan_eq : (∃ α : Fin D → ZMod 2, ∑ l : Fin D, α l • (fun j => b2z (cols l j)) = fun j => b2z (rhs j)) ↔
     (fun j => b2z (rhs j)) ∈
       Submodule.span (ZMod 2) (Set.range (fun l : {l : Fin D // bUs st l = true} => bVc st l.val)) := by
   rw [Submodule.mem_span_range_iff_exists_fun]
   simp_rw [hcol_vec]
   constructor
   · rintro ⟨α, hα⟩
     refine ⟨fun l => α l.val, ?_⟩
     rw [← hα]; funext j
     simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
     rw [← Finset.sum_subset (Finset.filter_subset (fun l : Fin D => bUs st l = true) Finset.univ)]
     · symm
       exact Finset.sum_bij (fun l hl => ⟨l, (Finset.mem_filter.mp hl).2⟩)
         (fun _ _ => Finset.mem_univ _)
         (fun _ _ _ _ h => congrArg Subtype.val h)
         (fun r _ => ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property⟩, rfl⟩)
         (fun _ _ => rfl)
     · intro l _ hnot
       simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnot
       have h0 := congrFun (hzero l hnot) j
       change α l * bVc st l j = 0
       rw [h0]; simp
   · rintro ⟨α, hα⟩
     refine ⟨fun l => if h : bUs st l = true then α ⟨l, h⟩ else 0, ?_⟩
     rw [← hα]; funext j
     simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
     rw [← Finset.sum_subset (Finset.filter_subset (fun l : Fin D => bUs st l = true) Finset.univ)]
     · exact Finset.sum_bij (fun l hl => ⟨l, (Finset.mem_filter.mp hl).2⟩)
         (fun _ _ => Finset.mem_univ _)
         (fun _ _ _ _ h => congrArg Subtype.val h)
         (fun r _ => ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.property⟩, rfl⟩)
         (fun l hl => by
           have hlt : bUs st l = true := (Finset.mem_filter.mp hl).2
           simp only [hlt, ↓reduceDIte])
     · intro l _ hnot
       simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnot
       simp [hnot]
 constructor
 · simp only [Sum.elim_inl, Bool.not_eq_true']
   exact hiff.trans hspan_eq
 · intro hok
   simp only [Sum.elim_inl, Bool.not_eq_true'] at hok
   have hs := hsol hok
   refine ⟨fun l hu => by dsimp only [bUs] at hu; simp [hu], ?_⟩
   funext j
   have hj := congrFun hs j
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
   unfold bDc
   rw [← hj]
   apply Finset.sum_congr rfl; intro l _
   rw [show b2z (cols l j) = bVc st l j from congrFun (hcol_vec l) j]
   change b2z (bUs st l && rNV (rref (aMt cols rhs)) (Fin.last D) l.castSucc) * bVc st l j = _
   cases hu : bUs st l
   · have h0 := congrFun (hzero l hu) j
     simp [h0]
   · simp
abbrev SM (D : ℕ) := Fin 5 ⊕ Fin D ⊕ Fin D ⊕ Fin D ⊕ Unit
def sMd {D : ℕ} (md : SM D → Bool) (k5 : Fin 5) : Bool := md (inl k5)
def sSl {D : ℕ} (md : SM D → Bool) (l : Fin D) : Bool := md (inr (inl l))
def sFv {D : ℕ} (md : SM D → Bool) (l : Fin D) : Bool := md (inr (inr (inl l)))
def sAv {D : ℕ} (md : SM D → Bool) (l : Fin D) : Bool := md (inr (inr (inr (inl l))))
def sOv {D : ℕ} (md : SM D → Bool) : Bool := md (inr (inr (inr (inr ()))))
def stB (D m : ℕ) (inp : BSt D m ⊕ (Fin m × Fin m) ⊕ Fin m → Bool) :
   BSt D m ⊕ SM D → Bool :=
 let st : BSt D m → Bool := fun q => inp (inl q)
 let Nnext : Fin m × Fin m → Bool := fun p => inp (inr (inl p))
 let vi : Fin m → Bool := fun j => inp (inr (inr j))
 let vInR : Bool := iSN m (Sum.elim Nnext vi) ()
 let f : Fin D → Bool := fun l => bUs st l && !(iSN m (Sum.elim Nnext (fun j => bMt st l j)) ())
 let hasF : Bool := decide (∃ l : Fin D, f l = true)
 let firstF : Fin D → Bool := fun l => f l && decide (∀ l' : Fin D, l'.val < l.val → f l' = false)
 let bp : Fin m → Bool := fun j => decide (∃ l : Fin D, firstF l = true ∧ bMt st l j = true)
 let Bmid : Fin D × Fin m → Bool := fun p =>
   if firstF p.1 then false
   else if f p.1 then xor (bMt st p.1 p.2) (bp p.2)
   else bMt st p.1 p.2
 let usedMid : Fin D → Bool := fun l => bUs st l && !(firstF l)
 let bpXorV : Fin m → Bool := fun j => xor (bp j) (vi j)
 let sol1b := sBas D m (Sum.elim (Sum.elim Bmid usedMid) bpXorV)
 let inC : Bool := sol1b (inl ())
 let alpha1b : Fin D → Bool := fun l => sol1b (inr l)
 let sol3a := sBas D m (Sum.elim st vi)
 let inB : Bool := sol3a (inl ())
 let alpha3a : Fin D → Bool := fun l => sol3a (inr l)
 let hasFree : Bool := decide (∃ l : Fin D, bUs st l = false)
 let firstFree : Fin D → Bool := fun l =>
   !(bUs st l) && decide (∀ l' : Fin D, l'.val < l.val → bUs st l' = true)
 let m0 : Bool := vInR && inB
 let m1 : Bool := (!vInR) && (!hasF)
 let m2 : Bool := (!vInR) && hasF && (!inC)
 let m3 : Bool := (!vInR) && hasF && inC
 let m4 : Bool := vInR && (!inB) && hasFree
 let isOver : Bool := vInR && (!inB) && (!hasFree)
 let Bnext : Fin D × Fin m → Bool := fun p =>
   if m2 then (if firstF p.1 then bpXorV p.2 else Bmid p)
   else if m3 then Bmid p
   else if m4 then (if firstFree p.1 then vi p.2 else bMt st p.1 p.2)
   else bMt st p.1 p.2
 let usedNext : Fin D → Bool := fun l =>
   if m3 then usedMid l
   else if m4 then (bUs st l || firstFree l)
   else bUs st l
 let modes : Fin 5 → Bool := ![m0, m1, m2, m3, m4]
 let slot : Fin D → Bool := fun l => if m4 then firstFree l else if (m2 || m3) then firstF l else false
 let fvec : Fin D → Bool := fun l => if (m2 || m3) then f l else false
 let avec : Fin D → Bool := fun l => if m0 then alpha3a l else if m3 then alpha1b l else false
 Sum.elim (Sum.elim Bnext usedNext)
   (Sum.elim modes (Sum.elim slot (Sum.elim fvec (Sum.elim avec (fun _ => isOver)))))
lemma ec_stB (D m : ℕ) :
   EC (600 * (D + 1) * (m + 1) * (m + D + 3)) (stB D m) := by
 let I0 := BSt D m ⊕ (Fin m × Fin m) ⊕ Fin m
 have h1 : EC ((D + 1) * (12 * (m + 1) * (m + 1) + 4))
     (fun (inp : I0 → Bool) (q : Unit ⊕ Fin D) =>
       let Nnext := fun p => inp (inr (inl p))
       let vi := fun j => inp (inr (inr j))
       let st := fun a => inp (inl a)
       Sum.elim
         (fun _ => iSN m (Sum.elim Nnext vi) ())
         (fun l => bUs st l && !(iSN m (Sum.elim Nnext (fun j => bMt st l j)) ())) q) := by
   have hv : EC (12 * (m + 1) * (m + 1))
       (fun (inp : I0 → Bool) (_ : Unit) =>
         iSN m (Sum.elim (fun p => inp (inr (inl p))) (fun j => inp (inr (inr j)))) ()) := by
     let sel : (Fin m × Fin m) ⊕ Fin m → I0 :=
       Sum.elim (fun p => inr (inl p)) (fun j => inr (inr j))
     have h := ec_comp (ec_proj sel) (ec_iSN m)
     rw [zero_add] at h
     exact ec_eq (fun inp u => by congr 1; funext q; rcases q with _ | _ <;> rfl) h
   have hf : EC (D * (12 * (m + 1) * (m + 1) + 4))
       (fun (inp : I0 → Bool) (l : Fin D) =>
         inp (inl (inr l)) &&
           !(iSN m (Sum.elim (fun p => inp (inr (inl p))) (fun j => inp (inl (inl (l, j))))) ())) := by
     have hfam := ec_family (s := 12 * (m + 1) * (m + 1) + 4)
       (f := fun (l : Fin D) (inp : I0 → Bool) (_ : Unit) =>
         inp (inl (inr l)) &&
           !(iSN m (Sum.elim (fun p => inp (inr (inl p))) (fun j => inp (inl (inl (l, j))))) ()))
       (fun l => by
         let sel : (Fin m × Fin m) ⊕ Fin m → I0 :=
           Sum.elim (fun p => inr (inl p)) (fun j => inl (inl (l, j)))
         have hi := ec_comp (ec_proj sel) (ec_iSN m)
         rw [zero_add] at hi
         have hand := ec_and_of (ec_proj (fun (_ : Unit) => (inl (inr l) : I0))) (ec_not_of hi)
         rw [Fintype.card_unit] at hand
         refine ec_le (ec_eq ?_ hand) (by nlinarith)
         intro inp u; cases u
         congr 2)
     rw [Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun l : Fin D => (l, ())))
     rw [add_zero] at hp; exact hp
   have hp := ec_pair hv hf
   exact ec_le hp (by nlinarith)
 let I1 := I0 ⊕ (Unit ⊕ Fin D)
 have h2 : EC (10 * D * D + 30 * D + 20)
     (fun (y : I1 → Bool) (q : Unit ⊕ Fin D ⊕ Unit ⊕ Fin D) =>
       let f := fun l => y (inr (inr l))
       let used := fun l => y (inl (inl (inr l)))
       Sum.elim
         (fun _ => decide (∃ l : Fin D, f l = true))
         (Sum.elim
           (fun l => f l && decide (∀ l' : Fin D, l'.val < l.val → f l' = false))
           (Sum.elim
             (fun _ => decide (∃ l : Fin D, used l = false))
             (fun l => !(used l) && decide (∀ l' : Fin D, l'.val < l.val → used l' = true)))) q) := by
   have hhasF : EC (2 * D + 3)
       (fun (y : I1 → Bool) (_ : Unit) => decide (∃ l : Fin D, y (inr (inr l)) = true)) := by
     have h := ec_comp (ec_proj (fun l : Fin D => (inr (inr l) : I1))) (ec_any (α := Fin D))
     rw [zero_add, Fintype.card_fin] at h
     exact ec_eq (fun y u => by simp [decide_eq_decide]) h
   have hfirstF : EC (D * (5 * D + 10))
       (fun (y : I1 → Bool) (l : Fin D) =>
         y (inr (inr l)) && decide (∀ l' : Fin D, l'.val < l.val → y (inr (inr l')) = false)) := by
     have hfam := ec_family (s := 5 * D + 10)
       (f := fun (l : Fin D) (y : I1 → Bool) (_ : Unit) =>
         y (inr (inr l)) && decide (∀ l' : Fin D, l'.val < l.val → y (inr (inr l')) = false))
       (fun l => by
         have hcond : EC (2 * D + 4)
             (fun (y : I1 → Bool) (l' : Fin D) => !(decide (l'.val < l.val)) || !(y (inr (inr l')))) := by
           have h := ec_or_of (ec_const (ι := I1) (fun l' : Fin D => !(decide (l'.val < l.val))))
             (ec_not_of (ec_proj (fun l' : Fin D => (inr (inr l') : I1))))
           rw [Fintype.card_fin] at h; exact ec_le h (by omega)
         have hall := ec_comp hcond (ec_all (α := Fin D))
         rw [Fintype.card_fin] at hall
         have hlt : EC (5 * D + 8)
             (fun (y : I1 → Bool) (_ : Unit) => decide (∀ l' : Fin D, l'.val < l.val → y (inr (inr l')) = false)) := by
           refine ec_le (ec_eq ?_ hall) (by omega)
           intro y u; simp only [decide_eq_decide]
           constructor
           · intro h l' hl; have := h l'; simp [hl] at this; exact this
           · intro h l'; by_cases hl : l'.val < l.val <;> simp [hl, h]
         have hand := ec_and_of (ec_proj (fun (_ : Unit) => (inr (inr l) : I1))) hlt
         rw [Fintype.card_unit] at hand; exact ec_le hand (by omega))
     rw [Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun l : Fin D => (l, ())))
     rw [add_zero] at hp; exact hp
   have hhasFree : EC (3 * D + 6)
       (fun (y : I1 → Bool) (_ : Unit) => decide (∃ l : Fin D, y (inl (inl (inr l))) = false)) := by
     have hnot := ec_not_of (ec_proj (fun l : Fin D => (inl (inl (inr l)) : I1)))
     have hany := ec_comp hnot (ec_any (α := Fin D))
     rw [Fintype.card_fin] at hany
     refine ec_le (ec_eq ?_ hany) (by omega)
     intro y u; simp
   have hfirstFree : EC (D * (5 * D + 10))
       (fun (y : I1 → Bool) (l : Fin D) =>
         !(y (inl (inl (inr l)))) &&
           decide (∀ l' : Fin D, l'.val < l.val → y (inl (inl (inr l'))) = true)) := by
     have hfam := ec_family (s := 5 * D + 10)
       (f := fun (l : Fin D) (y : I1 → Bool) (_ : Unit) =>
         !(y (inl (inl (inr l)))) &&
           decide (∀ l' : Fin D, l'.val < l.val → y (inl (inl (inr l'))) = true))
       (fun l => by
         have hcond : EC (2 * D + 4)
             (fun (y : I1 → Bool) (l' : Fin D) => !(decide (l'.val < l.val)) || y (inl (inl (inr l')))) := by
           have h := ec_or_of (ec_const (ι := I1) (fun l' : Fin D => !(decide (l'.val < l.val))))
             (ec_proj (fun l' : Fin D => (inl (inl (inr l')) : I1)))
           rw [Fintype.card_fin] at h; exact ec_le h (by omega)
         have hall := ec_comp hcond (ec_all (α := Fin D))
         rw [Fintype.card_fin] at hall
         have hlt : EC (5 * D + 8)
             (fun (y : I1 → Bool) (_ : Unit) => decide (∀ l' : Fin D, l'.val < l.val → y (inl (inl (inr l'))) = true)) := by
           refine ec_le (ec_eq ?_ hall) (by omega)
           intro y u; simp only [decide_eq_decide]
           constructor
           · intro h l' hl; have := h l'; simp [hl] at this; exact this
           · intro h l'; by_cases hl : l'.val < l.val <;> simp [hl, h]
         have hand := ec_and_of (ec_not_of (ec_proj (fun (_ : Unit) => (inl (inl (inr l)) : I1)))) hlt
         rw [Fintype.card_unit] at hand; exact ec_le hand (by omega))
     rw [Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun l : Fin D => (l, ())))
     rw [add_zero] at hp; exact hp
   exact ec_le (ec_pair hhasF (ec_pair hfirstF (ec_pair hhasFree hfirstFree))) (by nlinarith)
 let I2 := I1 ⊕ (Unit ⊕ Fin D ⊕ Unit ⊕ Fin D)
 have hbp : EC (m * (4 * D + 6) + 6 * m)
     (fun (z : I2 → Bool) (q : Fin m ⊕ Fin m) =>
       let bp := fun j => decide (∃ l : Fin D, z (inr (inr (inl l))) = true ∧
           z (inl (inl (inl (inl (l, j))))) = true)
       Sum.elim bp (fun j => xor (bp j) (z (inl (inl (inr (inr j)))))) q) := by
   have h0 : EC (m * (4 * D + 6))
       (fun (z : I2 → Bool) (j : Fin m) =>
         decide (∃ l : Fin D, z (inr (inr (inl l))) = true ∧
           z (inl (inl (inl (inl (l, j))))) = true)) := by
     have hfam := ec_family (s := 4 * D + 6)
       (f := fun (j : Fin m) (z : I2 → Bool) (_ : Unit) =>
         decide (∃ l : Fin D, z (inr (inr (inl l))) = true ∧
           z (inl (inl (inl (inl (l, j))))) = true))
       (fun j => by
         have hand := ec_and_of (ec_proj (fun l : Fin D => (inr (inr (inl l)) : I2)))
           (ec_proj (fun l : Fin D => (inl (inl (inl (inl (l, j)))) : I2)))
         rw [Fintype.card_fin] at hand
         have hany := ec_comp hand (ec_any (α := Fin D))
         rw [Fintype.card_fin] at hany
         exact ec_le (ec_eq (fun z u => by simp [Bool.and_eq_true]) hany) (by omega))
     rw [Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun j : Fin m => (j, ())))
     rw [add_zero] at hp; exact hp
   let I2' := I2 ⊕ Fin m
   have hxor := ec_xor_of (ec_proj (fun j : Fin m => (inr j : I2')))
     (ec_proj (fun j : Fin m => (inl (inl (inl (inr (inr j)))) : I2')))
   rw [Fintype.card_fin] at hxor
   have hp := ec_pair (ec_proj (fun j : Fin m => (inr j : I2'))) hxor
   exact ec_le (ec_let h0 hp) (by omega)
 let I3 := I2 ⊕ (Fin m ⊕ Fin m)
 have hmid : EC (24 * D * m + 4 * D + 6)
     (fun (w : I3 → Bool) =>
       let Bmid : Fin D × Fin m → Bool := fun p =>
         if w (inl (inr (inr (inl p.1)))) then false
         else if w (inl (inl (inr (inr p.1)))) then
           xor (w (inl (inl (inl (inl (inl p)))))) (w (inr (inl p.2)))
         else w (inl (inl (inl (inl (inl p)))))
       let usedMid : Fin D → Bool := fun l =>
         w (inl (inl (inl (inl (inr l))))) &&
           !(w (inl (inr (inr (inl l)))))
       Sum.elim Bmid usedMid) := by
   have hB0 : EC 0 (fun (w : I3 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inl (inl p)))))) := ec_proj _
   have hbp' : EC 0 (fun (w : I3 → Bool) (p : Fin D × Fin m) => w (inr (inl p.2))) := ec_proj _
   have hfl : EC 0 (fun (w : I3 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inr (inr p.1))))) := ec_proj _
   have hff : EC 0 (fun (w : I3 → Bool) (p : Fin D × Fin m) =>
       w (inl (inr (inr (inl p.1))))) := ec_proj _
   have hBm := ec_ite_of hff (ec_const (fun _ => false)) (ec_ite_of hfl (ec_xor_of hB0 hbp') hB0)
   have huM := ec_and_of (ec_proj (fun l : Fin D => (inl (inl (inl (inl (inr l)))) : I3)))
     (ec_not_of (ec_proj (fun l : Fin D => (inl (inr (inr (inl l))) : I3))))
   simp only [Fintype.card_prod, Fintype.card_fin] at hBm huM
   exact ec_le (ec_pair hBm huM) (by nlinarith)
 let I4 := I3 ⊕ BSt D m
 have hsols : EC (200 * (D + 1) * (m + 1) * (m + D + 2))
     (fun (w : I4 → Bool) =>
       let s1b := sBas D m (Sum.elim (fun a => w (inr a)) (fun j => w (inl (inr (inr j)))))
       let s3a := sBas D m (Sum.elim (fun a => w (inl (inl (inl (inl (inl a))))))
         (fun j => w (inl (inl (inl (inl (inr (inr j))))))))
       Sum.elim s1b s3a) := by
   let sel1 : BSt D m ⊕ Fin m → I4 :=
     Sum.elim (fun a => inr a) (fun j => inl (inr (inr j)))
   let sel2 : BSt D m ⊕ Fin m → I4 :=
     Sum.elim (fun a => inl (inl (inl (inl (inl a)))))
       (fun j => inl (inl (inl (inl (inr (inr j))))))
   have hs1 := ec_comp (ec_proj sel1) (ec_sBas D m)
   have hs2 := ec_comp (ec_proj sel2) (ec_sBas D m)
   rw [zero_add] at hs1 hs2
   refine ec_le (ec_eq ?_ (ec_pair hs1 hs2)) (by nlinarith)
   intro w q; rcases q with q1 | q2
   · change sBas D m (fun r => w (sel1 r)) q1 = _
     congr 1; funext r; rcases r with _ | _ <;> rfl
   · change sBas D m (fun r => w (sel2 r)) q2 = _
     congr 1; funext r; rcases r with _ | _ <;> rfl
 let I5 := I4 ⊕ ((Unit ⊕ Fin D) ⊕ (Unit ⊕ Fin D))
 have hmodes : EC 60
     (fun (w : I5 → Bool) (q : Fin 5 ⊕ Unit) =>
       let vInR := w (inl (inl (inl (inl (inr (inl ()))))))
       let hasF := w (inl (inl (inl (inr (inl ())))))
       let inC := w (inr (inl (inl ())))
       let inB := w (inr (inr (inl ())))
       let hasFree := w (inl (inl (inl (inr (inr (inr (inl ())))))))
       Sum.elim
         ![vInR && inB, (!vInR) && (!hasF), (!vInR) && hasF && (!inC),
           (!vInR) && hasF && inC, vInR && (!inB) && hasFree]
         (fun _ => vInR && (!inB) && (!hasFree)) q) := by
   have hv : EC 0 (fun (w : I5 → Bool) (_ : Unit) =>
       w (inl (inl (inl (inl (inr (inl ()))))))) := ec_proj _
   have hf : EC 0 (fun (w : I5 → Bool) (_ : Unit) =>
       w (inl (inl (inl (inr (inl ())))))) := ec_proj _
   have hc : EC 0 (fun (w : I5 → Bool) (_ : Unit) => w (inr (inl (inl ())))) := ec_proj _
   have hb : EC 0 (fun (w : I5 → Bool) (_ : Unit) => w (inr (inr (inl ())))) := ec_proj _
   have hfr : EC 0 (fun (w : I5 → Bool) (_ : Unit) =>
       w (inl (inl (inl (inr (inr (inr (inl ())))))))) := ec_proj _
   have hm0 := ec_and_of hv hb
   have hm1 := ec_and_of (ec_not_of hv) (ec_not_of hf)
   have hm2 := ec_and_of (ec_and_of (ec_not_of hv) hf) (ec_not_of hc)
   have hm3 := ec_and_of (ec_and_of (ec_not_of hv) hf) hc
   have hm4 := ec_and_of (ec_and_of hv (ec_not_of hb)) hfr
   have hov := ec_and_of (ec_and_of hv (ec_not_of hb)) (ec_not_of hfr)
   have hall5 := ec_pair hm0 (ec_pair hm1 (ec_pair hm2 (ec_pair hm3 (ec_pair hm4 hov))))
   rw [Fintype.card_unit] at hall5
   let sel : Fin 5 ⊕ Unit → Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit :=
     Sum.elim (fun k5 => match k5 with
       | ⟨0, _⟩ => inl ()
       | ⟨1, _⟩ => inr (inl ())
       | ⟨2, _⟩ => inr (inr (inl ()))
       | ⟨3, _⟩ => inr (inr (inr (inl ())))
       | ⟨4, _⟩ => inr (inr (inr (inr (inl ())))))
       (fun _ => inr (inr (inr (inr (inr ())))))
   have hcomp := ec_comp hall5 (ec_proj sel)
   refine ec_le (ec_eq ?_ hcomp) (by omega)
   intro w q
   rcases q with k5 | u
   · fin_cases k5 <;> rfl
   · rfl
 let I6 := I5 ⊕ (Fin 5 ⊕ Unit)
 have hfinal : EC (60 * D * m + 80 * D + 20)
     (fun (w : I6 → Bool) =>
       let m0 := w (inr (inl 0))
       let m2 := w (inr (inl 2))
       let m3 := w (inr (inl 3))
       let m4 := w (inr (inl 4))
       let isOver := w (inr (inr ()))
       let B0 := fun p => w (inl (inl (inl (inl (inl (inl (inl (inl p))))))))
       let u0 := fun l => w (inl (inl (inl (inl (inl (inl (inl (inr l))))))))
       let vi := fun j => w (inl (inl (inl (inl (inl (inl (inr (inr j))))))))
       let f := fun l => w (inl (inl (inl (inl (inl (inr (inr l)))))))
       let ff := fun l => w (inl (inl (inl (inl (inr (inr (inl l)))))))
       let ffr := fun l => w (inl (inl (inl (inl (inr (inr (inr (inr l))))))))
       let bpv := fun j => w (inl (inl (inl (inr (inr j)))))
       let Bm := fun p => w (inl (inl (inr (inl p))))
       let uM := fun l => w (inl (inl (inr (inr l))))
       let a1b := fun l => w (inl (inr (inl (inr l))))
       let a3a := fun l => w (inl (inr (inr (inr l))))
       let Bnext := fun p : Fin D × Fin m =>
         if m2 then (if ff p.1 then bpv p.2 else Bm p)
         else if m3 then Bm p
         else if m4 then (if ffr p.1 then vi p.2 else B0 p)
         else B0 p
       let unext := fun l : Fin D =>
         if m3 then uM l else if m4 then (u0 l || ffr l) else u0 l
       let slot := fun l : Fin D => if m4 then ffr l else if (m2 || m3) then ff l else false
       let fvec := fun l : Fin D => if (m2 || m3) then f l else false
       let avec := fun l : Fin D => if m0 then a3a l else if m3 then a1b l else false
       Sum.elim (Sum.elim Bnext unext)
         (Sum.elim (fun k5 => w (inr (inl k5)))
           (Sum.elim slot (Sum.elim fvec (Sum.elim avec (fun (_ : Unit) => isOver)))))) := by
   have hm0D : EC 0 (fun (w : I6 → Bool) (_ : Fin D) => w (inr (inl 0))) := ec_proj _
   have hm2D : EC 0 (fun (w : I6 → Bool) (_ : Fin D) => w (inr (inl 2))) := ec_proj _
   have hm3D : EC 0 (fun (w : I6 → Bool) (_ : Fin D) => w (inr (inl 3))) := ec_proj _
   have hm4D : EC 0 (fun (w : I6 → Bool) (_ : Fin D) => w (inr (inl 4))) := ec_proj _
   have hm2P : EC 0 (fun (w : I6 → Bool) (_ : Fin D × Fin m) => w (inr (inl 2))) := ec_proj _
   have hm3P : EC 0 (fun (w : I6 → Bool) (_ : Fin D × Fin m) => w (inr (inl 3))) := ec_proj _
   have hm4P : EC 0 (fun (w : I6 → Bool) (_ : Fin D × Fin m) => w (inr (inl 4))) := ec_proj _
   have hB0P : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inl (inl (inl (inl (inl p))))))))) := ec_proj _
   have hBmP : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) => w (inl (inl (inr (inl p))))) := ec_proj _
   have hviP : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inl (inl (inl (inr (inr p.2))))))))) := ec_proj _
   have hbpvP : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inr (inr p.2)))))) := ec_proj _
   have hffP : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inl (inr (inr (inl p.1)))))))) := ec_proj _
   have hffrP : EC 0 (fun (w : I6 → Bool) (p : Fin D × Fin m) =>
       w (inl (inl (inl (inl (inr (inr (inr (inr p.1))))))))) := ec_proj _
   have hBnext := ec_ite_of hm2P (ec_ite_of hffP hbpvP hBmP)
     (ec_ite_of hm3P hBmP (ec_ite_of hm4P (ec_ite_of hffrP hviP hB0P) hB0P))
   have hu0D : EC 0 (fun (w : I6 → Bool) (l : Fin D) =>
       w (inl (inl (inl (inl (inl (inl (inl (inr l))))))))) := ec_proj _
   have huMD : EC 0 (fun (w : I6 → Bool) (l : Fin D) => w (inl (inl (inr (inr l))))) := ec_proj _
   have hffD : EC 0 (fun (w : I6 → Bool) (l : Fin D) =>
       w (inl (inl (inl (inl (inr (inr (inl l)))))))) := ec_proj _
   have hffrD : EC 0 (fun (w : I6 → Bool) (l : Fin D) =>
       w (inl (inl (inl (inl (inr (inr (inr (inr l))))))))) := ec_proj _
   have hfD : EC 0 (fun (w : I6 → Bool) (l : Fin D) =>
       w (inl (inl (inl (inl (inl (inr (inr l)))))))) := ec_proj _
   have ha1bD : EC 0 (fun (w : I6 → Bool) (l : Fin D) => w (inl (inr (inl (inr l))))) := ec_proj _
   have ha3aD : EC 0 (fun (w : I6 → Bool) (l : Fin D) => w (inl (inr (inr (inr l))))) := ec_proj _
   have hunext := ec_ite_of hm3D huMD (ec_ite_of hm4D (ec_or_of hu0D hffrD) hu0D)
   have hslot := ec_ite_of hm4D hffrD (ec_ite_of (ec_or_of hm2D hm3D) hffD (ec_const (fun _ => false)))
   have hfvec := ec_ite_of (ec_or_of hm2D hm3D) hfD (ec_const (fun _ => false))
   have havec := ec_ite_of hm0D ha3aD (ec_ite_of hm3D ha1bD (ec_const (fun _ => false)))
   have hmodesP : EC 0 (fun (w : I6 → Bool) (k5 : Fin 5) => w (inr (inl k5))) := ec_proj _
   have hovP : EC 0 (fun (w : I6 → Bool) (_ : Unit) => w (inr (inr ()))) := ec_proj _
   have hp := ec_pair (ec_pair hBnext hunext) (ec_pair hmodesP (ec_pair hslot (ec_pair hfvec (ec_pair havec hovP))))
   simp only [Fintype.card_prod, Fintype.card_fin] at hp
   exact ec_le hp (by nlinarith)
 have htot := ec_let h1 (ec_let h2 (ec_let hbp (ec_let hmid (ec_let hsols (ec_let hmodes hfinal)))))
 refine ec_le (ec_eq ?_ htot) ?_
 · intro inp q
   have hv0 : ∀ (a b c d e : Bool), ![a, b, c, d, e] 0 = a := fun _ _ _ _ _ => rfl
   have hv2 : ∀ (a b c d e : Bool), ![a, b, c, d, e] 2 = c := fun _ _ _ _ _ => rfl
   have hv3 : ∀ (a b c d e : Bool), ![a, b, c, d, e] 3 = d := fun _ _ _ _ _ => rfl
   have hv4 : ∀ (a b c d e : Bool), ![a, b, c, d, e] 4 = e := fun _ _ _ _ _ => rfl
   unfold stB
   rcases q with (⟨l, j⟩ | l) | (k5 | l | l | l | u) <;>
     (simp only [Sum.elim_inl, Sum.elim_inr, hv0, hv2, hv3, hv4, bMt, bUs]; rfl)
 · have hq1 : (D + 1) * (12 * (m + 1) * (m + 1) + 4) ≤ 16 * (D + 1) * (m + 1) * (m + D + 3) := by
     have ha : 12 * (m + 1) * (m + 1) + 4 ≤ 16 * (m + 1) * (m + D + 3) := by nlinarith
     calc (D + 1) * (12 * (m + 1) * (m + 1) + 4)
         ≤ (D + 1) * (16 * (m + 1) * (m + D + 3)) := Nat.mul_le_mul_left (D + 1) ha
       _ = 16 * (D + 1) * (m + 1) * (m + D + 3) := by ring
   have hq2 : 10 * D * D + 30 * D + 20 ≤ 30 * (D + 1) * (m + 1) * (m + D + 3) := by
     have ha : 10 * D * D + 30 * D + 20 ≤ 30 * (D + 1) * (m + D + 3) := by nlinarith
     have hb : 30 * (D + 1) * (m + D + 3) ≤ (30 * (D + 1) * (m + D + 3)) * (m + 1) :=
       Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
     calc 10 * D * D + 30 * D + 20 ≤ (30 * (D + 1) * (m + D + 3)) * (m + 1) := le_trans ha hb
       _ = 30 * (D + 1) * (m + 1) * (m + D + 3) := by ring
   have hq3 : m * (4 * D + 6) + 6 * m ≤ 12 * (D + 1) * (m + 1) * (m + D + 3) := by
     have ha : m * (4 * D + 6) + 6 * m ≤ 12 * (D + 1) * (m + 1) := by nlinarith
     exact le_trans ha (Nat.le_mul_of_pos_right _ (by omega))
   have hq4 : 24 * D * m + 4 * D + 6 ≤ 30 * (D + 1) * (m + 1) * (m + D + 3) := by nlinarith
   have hq5 : 200 * (D + 1) * (m + 1) * (m + D + 2) ≤ 200 * (D + 1) * (m + 1) * (m + D + 3) := by nlinarith
   have hq6 : 60 + (60 * D * m + 80 * D + 20) ≤ 100 * (D + 1) * (m + 1) * (m + D + 3) := by nlinarith
   linarith only [hq1, hq2, hq3, hq4, hq5, hq6]
lemma zmod2_fun_add_self {α : Type*} (x : α → ZMod 2) : x + x = 0 :=
 funext (fun _ => zmod2_add_self _)
lemma zmod2_subspace_step {m : ℕ} (L R' : Submodule (ZMod 2) (Fin m → ZMod 2))
   (v : Fin m → ZMod 2) (_hv : v ∉ R')
   (w : Fin m → ZMod 2) (hwL : w ∈ L) (hwR : w ∈ R' ⊔ Submodule.span (ZMod 2) {v}) (hwNR : w ∉ R') :
   w + v ∈ (L ⊔ Submodule.span (ZMod 2) {v}) ⊓ R' ∧
   (L ⊔ Submodule.span (ZMod 2) {v}) ⊓ R' = (L ⊓ R') ⊔ Submodule.span (ZMod 2) {w + v} := by
 rw [Submodule.mem_sup] at hwR
 obtain ⟨r, hr, s, hs, hrw⟩ := hwR
 rw [Submodule.mem_span_singleton] at hs
 obtain ⟨c, rfl⟩ := hs
 have hc1 : c = 1 := by
   rcases zmod2_cases c with rfl | rfl
   · simp only [zero_smul, add_zero] at hrw; rw [← hrw] at hwNR; exact absurd hr hwNR
   · rfl
 subst hc1
 rw [one_smul] at hrw
 have hwvR : w + v ∈ R' := by
   have : w + v = r := by rw [← hrw, add_assoc, zmod2_fun_add_self, add_zero]
   rw [this]; exact hr
 have hwvL : w + v ∈ L ⊔ Submodule.span (ZMod 2) {v} :=
   Submodule.add_mem _ (Submodule.mem_sup_left hwL) (Submodule.mem_sup_right (Submodule.subset_span rfl))
 refine ⟨⟨hwvL, hwvR⟩, le_antisymm ?_ ?_⟩
 · intro z ⟨hzL, hzR⟩
   change z ∈ L ⊔ Submodule.span (ZMod 2) {v} at hzL
   rw [Submodule.mem_sup] at hzL
   obtain ⟨u, hu, t, ht, rfl⟩ := hzL
   rw [Submodule.mem_span_singleton] at ht
   obtain ⟨a, rfl⟩ := ht
   rcases zmod2_cases a with rfl | rfl
   · rw [zero_smul, add_zero] at hzR ⊢
     exact Submodule.mem_sup_left ⟨hu, hzR⟩
   · rw [one_smul] at hzR ⊢
     have huw : u + w ∈ L ⊓ R' := by
       refine ⟨Submodule.add_mem _ hu hwL, ?_⟩
       have : u + w = (u + v) + (w + v) := by
         funext j; simp only [Pi.add_apply]
         have h2 := zmod2_add_self (v j)
         calc u j + w j = u j + w j + (v j + v j) := by rw [h2, add_zero]
           _ = (u j + v j) + (w j + v j) := by ring
       rw [this]
       exact Submodule.add_mem _ hzR hwvR
     have hdecomp : u + v = (u + w) + (w + v) := by
       funext j; simp only [Pi.add_apply]; rw [add_assoc, ← add_assoc (w j), zmod2_add_self, zero_add]
     rw [hdecomp]
     exact Submodule.add_mem _ (Submodule.mem_sup_left huw) (Submodule.mem_sup_right (Submodule.subset_span rfl))
 · refine sup_le ?_ ?_
   · exact inf_le_inf_right R' le_sup_left
   · rw [Submodule.span_singleton_le_iff_mem]; exact ⟨hwvL, hwvR⟩
def SMR {D m : ℕ} (I : Submodule (ZMod 2) (Fin m → ZMod 2))
   (st stNext : BSt D m → Bool)
   (vi : Fin m → ZMod 2) (md : SM D → Bool) : Prop :=
 (sMd md 0 = true ∧ sMd md 1 = false ∧ sMd md 2 = false ∧
   sMd md 3 = false ∧ sMd md 4 = false ∧
   stNext = st ∧ cVal st (sAv md) ∧ bDc st (sAv md) = vi) ∨
 (sMd md 0 = false ∧ sMd md 1 = true ∧ sMd md 2 = false ∧
   sMd md 3 = false ∧ sMd md 4 = false ∧
   stNext = st ∧ (∀ l : Fin D, sAv md l = false) ∧ vi ∉ I) ∨
 (sMd md 0 = false ∧ sMd md 1 = false ∧ sMd md 2 = true ∧
   sMd md 3 = false ∧ sMd md 4 = false ∧
   (∀ l : Fin D, sAv md l = false) ∧ vi ∉ I ∧
   ∃ p : Fin D, bUs st p = true ∧ sFv md p = true ∧
     (∀ l : Fin D, sSl md l = decide (l = p)) ∧
     (∀ l : Fin D, bUs st l = false → sFv md l = false) ∧
     (∀ l : Fin D, bUs stNext l = bUs st l) ∧
     bVc stNext p = bVc st p + vi ∧
     (∀ l : Fin D, l ≠ p → bVc stNext l = if sFv md l then bVc st l + bVc st p else bVc st l)) ∨
 (sMd md 0 = false ∧ sMd md 1 = false ∧ sMd md 2 = false ∧
   sMd md 3 = true ∧ sMd md 4 = false ∧
   ∃ p : Fin D, bUs st p = true ∧ sFv md p = true ∧
     (∀ l : Fin D, sSl md l = decide (l = p)) ∧
     (∀ l : Fin D, bUs st l = false → sFv md l = false) ∧
     (∀ l : Fin D, bUs stNext l = if l = p then false else bUs st l) ∧
     bVc stNext p = 0 ∧
     (∀ l : Fin D, l ≠ p → bVc stNext l = if sFv md l then bVc st l + bVc st p else bVc st l) ∧
     cVal stNext (sAv md) ∧ bDc stNext (sAv md) = bVc st p + vi) ∨
 (sMd md 0 = false ∧ sMd md 1 = false ∧ sMd md 2 = false ∧
   sMd md 3 = false ∧ sMd md 4 = true ∧
   (∀ l : Fin D, sAv md l = false) ∧ vi ∉ I ∧
   ∃ q : Fin D, bUs st q = false ∧
     (∀ l : Fin D, sSl md l = decide (l = q)) ∧
     (∀ l : Fin D, bUs stNext l = if l = q then true else bUs st l) ∧
     bVc stNext q = vi ∧
     (∀ l : Fin D, l ≠ q → bVc stNext l = bVc st l))
lemma exists_first_true {D : ℕ} (f : Fin D → Bool) (hex : ∃ l : Fin D, f l = true) :
   ∃ p : Fin D, f p = true ∧
     (∀ l : Fin D, (f l && decide (∀ l' : Fin D, l'.val < l.val → f l' = false)) = decide (l = p)) := by
 classical
 let S : Finset ℕ := (Finset.univ.filter (fun l : Fin D => f l = true)).image Fin.val
 have hne : S.Nonempty := by
   obtain ⟨l, hl⟩ := hex
   exact ⟨l.val, Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩⟩
 let m0 := S.min' hne
 have hm0_mem : m0 ∈ S := Finset.min'_mem S hne
 obtain ⟨p, hp_filt, hpm⟩ := Finset.mem_image.mp hm0_mem
 have hfp : f p = true := (Finset.mem_filter.mp hp_filt).2
 have hmin : ∀ l' : Fin D, l'.val < p.val → f l' = false := by
   intro l' hlt
   cases hfl' : f l'
   · rfl
   · have hl'_mem : l'.val ∈ S := Finset.mem_image.mpr ⟨l', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfl'⟩, rfl⟩
     have hle : m0 ≤ l'.val := Finset.min'_le S l'.val hl'_mem
     omega
 refine ⟨p, hfp, fun l => ?_⟩
 by_cases hlp : l = p
 · subst hlp
   simp only [hfp, Bool.true_and, decide_true, decide_eq_true_eq]
   exact hmin
 · simp only [hlp, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
   by_cases hfl : f l = true
   · right
     intro hall
     have hl_mem : l.val ∈ S := Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfl⟩, rfl⟩
     have hle : p.val ≤ l.val := by rw [hpm]; exact Finset.min'_le S l.val hl_mem
     have hlt : p.val < l.val := by
       rcases eq_or_lt_of_le hle with heq | hlt
       · exact absurd (Fin.ext heq.symm) hlp
       · exact hlt
     have := hall p hlt
     rw [hfp] at this; exact Bool.noConfusion this
   · left; cases h : f l <;> simp_all
lemma stB_sp {D m R : ℕ}
   (L R' : Submodule (ZMod 2) (Fin m → ZMod 2))
   (A_R : Fin R × Fin m → Bool)
   (hR_eq : R' = Submodule.span (ZMod 2) (Set.range (fun i : Fin R => fun j : Fin m => b2z (A_R (i, j)))))
   (viB : Fin m → Bool)
   (st : BSt D m → Bool)
   (hinv : BInv (L ⊓ (R' ⊔ Submodule.span (ZMod 2) {fun j => b2z (viB j)})) st) :
   let vi : Fin m → ZMod 2 := fun j => b2z (viB j)
   let L' := L ⊔ Submodule.span (ZMod 2) {vi}
   let Nnext : Fin m × Fin m → Bool := fun p => rNV (rref A_R) p.1 p.2
   let out := stB D m (Sum.elim st (Sum.elim Nnext viB))
   let stNext : BSt D m → Bool := fun a => out (inl a)
   let md : SM D → Bool := fun a => out (inr a)
   (sOv md = true ↔ D < Module.finrank (ZMod 2) ↥(L' ⊓ R')) ∧
   (sOv md = false → BInv (L' ⊓ R') stNext ∧ SMR (L ⊓ (R' ⊔ Submodule.span (ZMod 2) {vi})) st stNext vi md) := by
 dsimp only
 set vi : Fin m → ZMod 2 := fun j => b2z (viB j)
 set L' := L ⊔ Submodule.span (ZMod 2) {vi}
 set Rcur := R' ⊔ Submodule.span (ZMod 2) {vi}
 set Nnext : Fin m × Fin m → Bool := fun p => rNV (rref A_R) p.1 p.2
 set out := stB D m (Sum.elim st (Sum.elim Nnext viB))
 set stNext : BSt D m → Bool := fun a => out (inl a)
 set md : SM D → Bool := fun a => out (inr a)
 have hmemR : ∀ v : Fin m → Bool, iSN m (Sum.elim Nnext v) () = true ↔ (fun j => b2z (v j)) ∈ R' := by
   intro v; rw [hR_eq]; exact iSN_sp A_R v
 set vInR : Bool := iSN m (Sum.elim Nnext viB) ()
 set f : Fin D → Bool := fun l => bUs st l && !(iSN m (Sum.elim Nnext (fun j => bMt st l j)) ())
 set hasF : Bool := decide (∃ l : Fin D, f l = true)
 set firstF : Fin D → Bool := fun l => f l && decide (∀ l' : Fin D, l'.val < l.val → f l' = false)
 set bp : Fin m → Bool := fun j => decide (∃ l : Fin D, firstF l = true ∧ bMt st l j = true)
 set Bmid : Fin D × Fin m → Bool := fun p =>
   if firstF p.1 then false else if f p.1 then xor (bMt st p.1 p.2) (bp p.2) else bMt st p.1 p.2
 set usedMid : Fin D → Bool := fun l => bUs st l && !(firstF l)
 set bpXorV : Fin m → Bool := fun j => xor (bp j) (viB j)
 set sol1b := sBas D m (Sum.elim (Sum.elim Bmid usedMid) bpXorV)
 set inC : Bool := sol1b (inl ())
 set alpha1b : Fin D → Bool := fun l => sol1b (inr l)
 set sol3a := sBas D m (Sum.elim st viB)
 set inB : Bool := sol3a (inl ())
 set alpha3a : Fin D → Bool := fun l => sol3a (inr l)
 set hasFree : Bool := decide (∃ l : Fin D, bUs st l = false)
 set firstFree : Fin D → Bool := fun l =>
   !(bUs st l) && decide (∀ l' : Fin D, l'.val < l.val → bUs st l' = true)
 have hst_used_card : Module.finrank (ZMod 2) ↥(L ⊓ Rcur) =
     (Finset.univ.filter (fun l : Fin D => bUs st l = true)).card := bsInv_finrank hinv
 have hdim_le : Module.finrank (ZMod 2) ↥(L ⊓ Rcur) ≤ D := by
   rw [hst_used_card]
   calc _ ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_le_univ _
     _ = D := Finset.card_fin D
 have hfree_iff : hasFree = true ↔ Module.finrank (ZMod 2) ↥(L ⊓ Rcur) < D := by
   rw [hst_used_card]
   simp only [hasFree, decide_eq_true_eq]
   constructor
   · rintro ⟨l, hl⟩
     have hss : Finset.univ.filter (fun i : Fin D => bUs st i = true) ⊂ Finset.univ := by
       rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
       exact ⟨l, Finset.mem_univ _, by simp [hl]⟩
     simpa [Finset.card_fin] using Finset.card_lt_card hss
   · intro hlt
     by_contra hall
     push Not at hall
     have heq : Finset.univ.filter (fun i : Fin D => bUs st i = true) = Finset.univ := by
       ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
       cases hu : bUs st i
       · exact absurd hu (hall i)
       · simp
     rw [heq, Finset.card_fin] at hlt; omega
 have hsol3a := sBas_sp st viB hinv.1
 rw [hinv.2.2] at hsol3a
 have hmd_mode : ∀ k5 : Fin 5, sMd md k5 =
     ![vInR && inB, (!vInR) && (!hasF), (!vInR) && hasF && (!inC),
       (!vInR) && hasF && inC, vInR && (!inB) && hasFree] k5 := fun _ => rfl
 have hmd_over : sOv md = (vInR && (!inB) && (!hasFree)) := rfl
 have hmd_slot : ∀ l : Fin D, sSl md l =
     if (vInR && (!inB) && hasFree) then firstFree l
     else if ((!vInR) && hasF && (!inC) || (!vInR) && hasF && inC) then firstF l else false := fun _ => rfl
 have hmd_fvec : ∀ l : Fin D, sFv md l =
     if ((!vInR) && hasF && (!inC) || (!vInR) && hasF && inC) then f l else false := fun _ => rfl
 have hmd_avec : ∀ l : Fin D, sAv md l =
     if (vInR && inB) then alpha3a l else if ((!vInR) && hasF && inC) then alpha1b l else false := fun _ => rfl
 have hstNext_mat : ∀ l j, bMt stNext l j =
     if ((!vInR) && hasF && (!inC)) then (if firstF l then bpXorV j else Bmid (l, j))
     else if ((!vInR) && hasF && inC) then Bmid (l, j)
     else if (vInR && (!inB) && hasFree) then (if firstFree l then viB j else bMt st l j)
     else bMt st l j := fun _ _ => rfl
 have hstNext_used : ∀ l, bUs stNext l =
     if ((!vInR) && hasF && inC) then usedMid l
     else if (vInR && (!inB) && hasFree) then (bUs st l || firstFree l)
     else bUs st l := fun _ => rfl
 cases hvR : vInR
 ·
   have hviNR : vi ∉ R' := by
     intro hmem; have := (hmemR viB).mpr hmem; change vInR = true at this; rw [hvR] at this; exact Bool.false_ne_true this
   have hover_false : sOv md = false := by rw [hmd_over, hvR]; rfl
   cases hhf : hasF
   ·
     have hI_le_R : L ⊓ Rcur ≤ R' := by
       rw [← hinv.2.2, Submodule.span_le]
       rintro _ ⟨⟨l, hl⟩, rfl⟩
       have hf0 : f l = false := by
         by_contra hft
         have h1 : f l = true := by cases h : f l <;> simp_all
         have : hasF = true := decide_eq_true ⟨l, h1⟩
         rw [hhf] at this; exact Bool.false_ne_true this
       dsimp only [f] at hf0
       rw [hl, Bool.true_and, Bool.not_eq_false'] at hf0
       exact (hmemR _).mp hf0
     have hI_eq : L' ⊓ R' = L ⊓ Rcur := by
       apply le_antisymm
       · intro z ⟨hzL', hzR'⟩
         change z ∈ L ⊔ Submodule.span (ZMod 2) {vi} at hzL'
         rw [Submodule.mem_sup] at hzL'
         obtain ⟨u, hu, t, ht, rfl⟩ := hzL'
         rw [Submodule.mem_span_singleton] at ht
         obtain ⟨a, rfl⟩ := ht
         rcases zmod2_cases a with rfl | rfl
         · rw [zero_smul, add_zero] at hzR' ⊢
           exact ⟨hu, Submodule.mem_sup_left hzR'⟩
         · rw [one_smul] at hzR' ⊢
           have huRcur : u ∈ Rcur := by
             have : u = (u + vi) + vi := by rw [add_assoc, zmod2_fun_add_self, add_zero]
             rw [this]
             exact Submodule.add_mem _ (Submodule.mem_sup_left hzR') (Submodule.mem_sup_right (Submodule.subset_span rfl))
           have huR' : u ∈ R' := hI_le_R ⟨hu, huRcur⟩
           have hviR' : vi ∈ R' := by
             have : vi = (u + vi) + u := by rw [add_comm u vi, add_assoc, zmod2_fun_add_self, add_zero]
             rw [this]; exact Submodule.add_mem _ hzR' huR'
           exact absurd hviR' hviNR
       · intro z hz
         exact ⟨Submodule.mem_sup_left hz.1, hI_le_R hz⟩
     refine ⟨?_, fun _ => ?_⟩
     · rw [hover_false, hI_eq]; simp only [Bool.false_eq_true, false_iff, not_lt]; exact hdim_le
     · have hst_eq : stNext = st := by
         funext q; rcases q with ⟨l, j⟩ | l
         · change bMt stNext l j = bMt st l j; rw [hstNext_mat, hvR, hhf]; rfl
         · change bUs stNext l = bUs st l; rw [hstNext_used, hvR, hhf]; rfl
       rw [hI_eq, hst_eq]
       refine ⟨hinv, Or.inr (Or.inl ?_)⟩
       refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, fun hmem => hviNR (hI_le_R hmem)⟩
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR, hhf]; rfl
       · rw [hmd_mode, hvR, hhf]; rfl
       · rw [hmd_mode, hvR, hhf]; rfl
       · rw [hmd_mode, hvR]; rfl
       · intro l; rw [hmd_avec, hvR, hhf]; rfl
   ·
     have hexF : ∃ l : Fin D, f l = true := (decide_eq_true_iff).mp hhf
     obtain ⟨p, hfp, hfirst_eq⟩ := exists_first_true f hexF
     have hpu : bUs st p = true := (Bool.and_eq_true _ _).mp hfp |>.1
     have hpNR : bVc st p ∉ R' := by
       have hnot := (Bool.and_eq_true _ _).mp hfp |>.2
       rw [Bool.not_eq_true'] at hnot
       intro hmem; have := (hmemR _).mpr hmem; rw [hnot] at this; exact Bool.false_ne_true this
     have hpI : bVc st p ∈ L ⊓ Rcur := by
       rw [← hinv.2.2]; exact Submodule.subset_span ⟨⟨p, hpu⟩, rfl⟩
     have hbp_eq : ∀ j : Fin m, bp j = bMt st p j := by
       intro j
       have hff : ∀ l : Fin D, firstF l = decide (l = p) := hfirst_eq
       simp only [bp, hff]
       cases hm : bMt st p j
       · rw [decide_eq_false_iff_not]; rintro ⟨l, hl, hml⟩
         have hlp : l = p := by simpa using hl
         subst hlp; rw [hm] at hml; exact Bool.false_ne_true hml
       · exact decide_eq_true ⟨p, by simp, hm⟩
     have hbpVec : (fun j => b2z (bp j)) = bVc st p := by funext j; rw [hbp_eq j]; rfl
     have hbpXorV_vec : (fun j => b2z (bpXorV j)) = bVc st p + vi := by
       funext j; simp [bpXorV, b2z_xor, hbp_eq j, bVc, vi]
     have hBmid_vec : ∀ l : Fin D, (fun j => b2z (Bmid (l, j))) =
         if l = p then 0 else if f l then bVc st l + bVc st p else bVc st l := by
       intro l; funext j
       have hff : firstF l = decide (l = p) := hfirst_eq l
       dsimp only [Bmid]
       rw [hff, hbp_eq j]
       by_cases hlp : l = p
       · simp [hlp, b2z]
       · simp only [hlp, decide_false, Bool.false_eq_true, ↓reduceIte]
         cases hfl : f l <;> simp [b2z_xor, bVc]
     have husedMid_eq : ∀ l : Fin D, usedMid l = if l = p then false else bUs st l := by
       intro l; have hff : firstF l = decide (l = p) := hfirst_eq l
       dsimp only [usedMid]; rw [hff]
       by_cases hlp : l = p <;> simp [hlp]
     let stMid : BSt D m → Bool := Sum.elim Bmid usedMid
     have hMid_zero : ∀ l : Fin D, bUs stMid l = false → bVc stMid l = 0 := by
       intro l hl
       change (fun j => b2z (Bmid (l, j))) = 0
       rw [hBmid_vec l]
       change usedMid l = false at hl
       rw [husedMid_eq l] at hl
       by_cases hlp : l = p
       · simp [hlp]
       · simp only [hlp, ↓reduceIte] at hl ⊢
         have hfl0 : f l = false := by simp [f, hl]
         simp [hfl0, hinv.1 l hl]
     have hMid_li : LinearIndependent (ZMod 2)
         (fun l : {l : Fin D // bUs stMid l = true} => bVc stMid l.val) := by
       rw [Fintype.linearIndependent_iff]
       intro g hg l0
       let g' : {l : Fin D // bUs st l = true} → ZMod 2 := fun l =>
         if hlp : l.val = p then
           ∑ r : {r : Fin D // bUs stMid r = true}, if f r.val then g r else 0
         else g ⟨l.val, by
           change usedMid l.val = true; rw [husedMid_eq l.val]; simp [hlp, l.property]⟩
       have hsum_eq : ∑ l : {l : Fin D // bUs st l = true}, g' l • bVc st l.val =
           ∑ l : {l : Fin D // bUs stMid l = true}, g l • bVc stMid l.val := by
         funext j
         simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
         have hsplit := Finset.add_sum_erase Finset.univ
           (fun l : {l : Fin D // bUs st l = true} => g' l * bVc st l.val j)
           (Finset.mem_univ (⟨p, hpu⟩ : {l : Fin D // bUs st l = true}))
         rw [← hsplit]
         have hp_term : g' ⟨p, hpu⟩ * bVc st p j =
             ∑ r : {r : Fin D // bUs stMid r = true}, (if f r.val then g r else 0) * bVc st p j := by
           simp only [g', ↓reduceDIte, Finset.sum_mul]
         rw [hp_term]
         have herase : ∑ l ∈ Finset.univ.erase (⟨p, hpu⟩ : {l : Fin D // bUs st l = true}),
               g' l * bVc st l.val j =
             ∑ r : {r : Fin D // bUs stMid r = true}, g r * bVc st r.val j := by
           refine Finset.sum_bij
             (fun l hl => ⟨l.val, by
               have hne : l.val ≠ p := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               change usedMid l.val = true; rw [husedMid_eq l.val]; simp [hne, l.property]⟩)
             (fun _ _ => Finset.mem_univ _)
             (fun a _ b _ heq => Subtype.ext (by simpa [Subtype.ext_iff] using heq))
             (fun r _ => by
               have hr := r.property; change usedMid r.val = true at hr
               rw [husedMid_eq r.val] at hr
               have hne : r.val ≠ p := by intro h; simp [h] at hr
               simp only [hne, ↓reduceIte] at hr
               exact ⟨⟨r.val, hr⟩, Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩)
             (fun l hl => by
               have hne : l.val ≠ p := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               simp [g', hne])
         rw [herase, ← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl; intro r _
         have hr := r.property; change usedMid r.val = true at hr
         rw [husedMid_eq r.val] at hr
         have hne : r.val ≠ p := by intro h; simp [h] at hr
         change _ = g r * b2z (Bmid (r.val, j))
         have hbv := congrFun (hBmid_vec r.val) j
         simp only [hne, ↓reduceIte] at hbv
         rw [hbv]
         cases hfr : f r.val
         · simp
         · simp; ring
       have hlin := Fintype.linearIndependent_iff.mp hinv.2.1 g' (hsum_eq.trans hg)
       have hl0_prop := l0.property; change usedMid l0.val = true at hl0_prop
       rw [husedMid_eq l0.val] at hl0_prop
       have hne : l0.val ≠ p := by intro h; simp [h] at hl0_prop
       simp only [hne, ↓reduceIte] at hl0_prop
       have := hlin ⟨l0.val, hl0_prop⟩
       simpa [g', hne] using this
     have hMid_span : Submodule.span (ZMod 2)
         (Set.range (fun l : {l : Fin D // bUs stMid l = true} => bVc stMid l.val)) = L ⊓ R' := by
       apply le_antisymm
       · rw [Submodule.span_le]
         rintro _ ⟨⟨l, hl⟩, rfl⟩
         change usedMid l = true at hl
         rw [husedMid_eq l] at hl
         have hne : l ≠ p := by intro h; simp [h] at hl
         simp only [hne, ↓reduceIte] at hl
         have hbv : bVc stMid l = if f l then bVc st l + bVc st p else bVc st l := by
           change (fun j => b2z (Bmid (l, j))) = _; rw [hBmid_vec l]; simp only [hne, ↓reduceIte]
         dsimp only
         rw [hbv]
         have hlI : bVc st l ∈ L ⊓ Rcur := by
           rw [← hinv.2.2]; exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
         cases hfl : f l
         · simp only [Bool.false_eq_true, ↓reduceIte]
           dsimp only [f] at hfl; rw [hl, Bool.true_and, Bool.not_eq_false'] at hfl
           exact ⟨hlI.1, (hmemR _).mp hfl⟩
         · simp only [↓reduceIte]
           dsimp only [f] at hfl; rw [hl, Bool.true_and, Bool.not_eq_true'] at hfl
           have hlNR : bVc st l ∉ R' := fun hm => by
             have := (hmemR _).mpr hm; rw [hfl] at this; exact Bool.false_ne_true this
           have h1 := (zmod2_subspace_step L R' vi hviNR (bVc st l) hlI.1 hlI.2 hlNR).1.2
           have h2 := (zmod2_subspace_step L R' vi hviNR (bVc st p) hpI.1 hpI.2 hpNR).1.2
           refine ⟨Submodule.add_mem _ hlI.1 hpI.1, ?_⟩
           have : bVc st l + bVc st p = (bVc st l + vi) + (bVc st p + vi) := by
             funext j; simp only [Pi.add_apply]
             have h2 := zmod2_add_self (vi j)
             calc bVc st l j + bVc st p j = bVc st l j + bVc st p j + (vi j + vi j) := by rw [h2, add_zero]
               _ = (bVc st l j + vi j) + (bVc st p j + vi j) := by ring
           rw [this]; exact Submodule.add_mem _ h1 h2
       · intro z ⟨hzL, hzR'⟩
         have hzI : z ∈ L ⊓ Rcur := ⟨hzL, Submodule.mem_sup_left hzR'⟩
         obtain ⟨c, hc_val, hc_eq⟩ := bsDec_surj hinv hzI
         have hsum_f : (∑ l : Fin D, if f l then b2z (c l) else 0) = 0 := by
           by_contra hne0
           have h1 : (∑ l : Fin D, if f l then b2z (c l) else 0) = 1 := by
             rcases zmod2_cases _ with h0 | h1
             · exact absurd h0 hne0
             · exact h1
           have hdecomp : z = (∑ l : Fin D, if f l then b2z (c l) else 0) • bVc st p +
               ∑ l : Fin D, b2z (c l) • bVc stMid l := by
             funext j
             rw [← hc_eq]
             simp only [bDc, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
             rw [← Finset.sum_add_distrib]
             apply Finset.sum_congr rfl; intro l _
             have hbv := congrFun (hBmid_vec l) j
             change b2z (c l) * bVc st l j = (if f l then b2z (c l) else 0) * bVc st p j + b2z (c l) * b2z (Bmid (l, j))
             rw [hbv]
             by_cases hlp : l = p
             · subst hlp; simp [hfp]
             · simp only [hlp, ↓reduceIte]
               cases hfl : f l
               · simp
               · simp only [↓reduceIte, Pi.add_apply, mul_add]
                 have hz2 := zmod2_add_self (b2z (c l) * bVc st p j)
                 calc b2z (c l) * bVc st l j
                     = b2z (c l) * bVc st l j + (b2z (c l) * bVc st p j + b2z (c l) * bVc st p j) := by rw [hz2, add_zero]
                   _ = b2z (c l) * bVc st p j + (b2z (c l) * bVc st l j + b2z (c l) * bVc st p j) := by ring
           rw [h1, one_smul] at hdecomp
           have hmid_in : ∑ l : Fin D, b2z (c l) • bVc stMid l ∈ L ⊓ R' := by
             apply Submodule.sum_mem; intro l _
             cases hul : bUs stMid l
             · rw [hMid_zero l hul, smul_zero]; exact Submodule.zero_mem _
             · apply Submodule.smul_mem
               have hl := hul; change usedMid l = true at hl; rw [husedMid_eq l] at hl
               have hne : l ≠ p := by intro h; simp [h] at hl
               simp only [hne, ↓reduceIte] at hl
               have hbv : bVc stMid l = if f l then bVc st l + bVc st p else bVc st l := by
                 change (fun j => b2z (Bmid (l, j))) = _; rw [hBmid_vec l]; simp only [hne, ↓reduceIte]
               rw [hbv]
               have hlI : bVc st l ∈ L ⊓ Rcur := by rw [← hinv.2.2]; exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
               cases hfl : f l
               · simp only [Bool.false_eq_true, ↓reduceIte]
                 dsimp only [f] at hfl; rw [hl, Bool.true_and, Bool.not_eq_false'] at hfl
                 exact ⟨hlI.1, (hmemR _).mp hfl⟩
               · simp only [↓reduceIte]
                 dsimp only [f] at hfl; rw [hl, Bool.true_and, Bool.not_eq_true'] at hfl
                 have hlNR : bVc st l ∉ R' := fun hm => by
                   have := (hmemR _).mpr hm; rw [hfl] at this; exact Bool.false_ne_true this
                 have h1' := (zmod2_subspace_step L R' vi hviNR (bVc st l) hlI.1 hlI.2 hlNR).1.2
                 have h2' := (zmod2_subspace_step L R' vi hviNR (bVc st p) hpI.1 hpI.2 hpNR).1.2
                 refine ⟨Submodule.add_mem _ hlI.1 hpI.1, ?_⟩
                 have : bVc st l + bVc st p = (bVc st l + vi) + (bVc st p + vi) := by
                   funext j; simp only [Pi.add_apply]
                   have h2 := zmod2_add_self (vi j)
                   calc bVc st l j + bVc st p j = bVc st l j + bVc st p j + (vi j + vi j) := by rw [h2, add_zero]
                     _ = (bVc st l j + vi j) + (bVc st p j + vi j) := by ring
                 rw [this]; exact Submodule.add_mem _ h1' h2'
           have hpR' : bVc st p ∈ R' := by
             have : bVc st p = z + ∑ l : Fin D, b2z (c l) • bVc stMid l := by
               rw [hdecomp, add_assoc, zmod2_fun_add_self, add_zero]
             rw [this]; exact Submodule.add_mem _ hzR' hmid_in.2
           exact hpNR hpR'
         have hz_eq : z = ∑ l : Fin D, b2z (c l) • bVc stMid l := by
           funext j; rw [← hc_eq]
           have h0 := congrArg (fun a => a * bVc st p j) hsum_f
           rw [zero_mul, Finset.sum_mul] at h0
           simp only [bDc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
           rw [← zero_add (∑ l : Fin D, b2z (c l) * bVc stMid l j), ← h0, ← Finset.sum_add_distrib]
           apply Finset.sum_congr rfl; intro l _
           have hbv := congrFun (hBmid_vec l) j
           change b2z (c l) * bVc st l j = (if f l then b2z (c l) else 0) * bVc st p j + b2z (c l) * b2z (Bmid (l, j))
           rw [hbv]
           by_cases hlp : l = p
           · subst hlp; simp [hfp]
           · simp only [hlp, ↓reduceIte]
             cases hfl : f l
             · simp
             · simp only [↓reduceIte, Pi.add_apply, mul_add]
               have hz2 := zmod2_add_self (b2z (c l) * bVc st p j)
               calc b2z (c l) * bVc st l j
                   = b2z (c l) * bVc st l j + (b2z (c l) * bVc st p j + b2z (c l) * bVc st p j) := by rw [hz2, add_zero]
                 _ = b2z (c l) * bVc st p j + (b2z (c l) * bVc st l j + b2z (c l) * bVc st p j) := by ring
         rw [hz_eq]
         apply Submodule.sum_mem; intro l _
         cases hul : bUs stMid l
         · rw [hMid_zero l hul, smul_zero]; exact Submodule.zero_mem _
         · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, hul⟩, rfl⟩)
     have hMid_inv : BInv (L ⊓ R') stMid := ⟨hMid_zero, hMid_li, hMid_span⟩
     have hL'R'_eq := (zmod2_subspace_step L R' vi hviNR (bVc st p) hpI.1 hpI.2 hpNR).2
     have hsol1b := sBas_sp stMid bpXorV hMid_zero
     rw [hMid_span, hbpXorV_vec] at hsol1b
     have hdim_mid : Module.finrank (ZMod 2) ↥(L ⊓ R') + 1 = Module.finrank (ZMod 2) ↥(L ⊓ Rcur) := by
       rw [bsInv_finrank hMid_inv, hst_used_card]
       have hfilt_eq : Finset.univ.filter (fun l : Fin D => bUs st l = true) =
           insert p (Finset.univ.filter (fun l : Fin D => bUs stMid l = true)) := by
         ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
         change bUs st l = true ↔ l = p ∨ usedMid l = true
         rw [husedMid_eq l]
         by_cases hlp : l = p <;> simp [hlp, hpu]
       have hnot : p ∉ Finset.univ.filter (fun l : Fin D => bUs stMid l = true) := by
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         change usedMid p ≠ true; rw [husedMid_eq p]; simp
       rw [hfilt_eq, Finset.card_insert_of_notMem hnot]
     have hdim_L'R'_le : Module.finrank (ZMod 2) ↥(L' ⊓ R') ≤ D := by
       rw [hL'R'_eq]
       have hmod := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ R') (Submodule.span (ZMod 2) {bVc st p + vi})
       have hsp1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {bVc st p + vi}) ≤ 1 := by
         by_cases h0 : bVc st p + vi = 0
         · rw [h0, Submodule.span_zero_singleton, finrank_bot]; omega
         · rw [finrank_span_singleton h0]
       omega
     refine ⟨by rw [hover_false]; simp only [Bool.false_eq_true, false_iff, not_lt]; exact hdim_L'R'_le, fun _ => ?_⟩
     cases hinC : inC
     ·
       have hnotC : bVc st p + vi ∉ L ⊓ R' := by
         intro hmem; have := hsol1b.1.mpr hmem; change inC = true at this; rw [hinC] at this; exact Bool.noConfusion this
       have husedNext_eq : ∀ l : Fin D, bUs stNext l = bUs st l := fun l => by
         rw [hstNext_used, hvR, hhf, hinC]; rfl
       have hvecNext_eq : ∀ l : Fin D, bVc stNext l =
           if l = p then bVc st p + vi else bVc stMid l := by
         intro l; funext j
         change b2z (bMt stNext l j) = _
         rw [hstNext_mat, hvR, hhf, hinC]
         have hff : firstF l = decide (l = p) := hfirst_eq l
         change b2z (if firstF l = true then bpXorV j else Bmid (l, j)) = _
         rw [hff]
         by_cases hlp : l = p
         · simp only [hlp, decide_true, ↓reduceIte]
           exact congrFun hbpXorV_vec j
         · simp only [hlp, decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
       have hNext_zero : ∀ l : Fin D, bUs stNext l = false → bVc stNext l = 0 := by
         intro l hl
         rw [husedNext_eq l] at hl
         have hne : l ≠ p := fun h => by subst h; rw [hpu] at hl; exact Bool.noConfusion hl
         rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]
         exact hMid_zero l (by change usedMid l = false; rw [husedMid_eq l]; simp only [hne, ↓reduceIte]; exact hl)
       have hNext_li : LinearIndependent (ZMod 2)
           (fun l : {l : Fin D // bUs stNext l = true} => bVc stNext l.val) := by
         rw [Fintype.linearIndependent_iff]
         intro g hg
         have hpu' : bUs stNext p = true := by rw [husedNext_eq p]; exact hpu
         have hsplit := Finset.add_sum_erase Finset.univ
           (fun l : {l : Fin D // bUs stNext l = true} => g l • bVc stNext l.val)
           (Finset.mem_univ (⟨p, hpu'⟩ : {l : Fin D // bUs stNext l = true}))
         rw [hg] at hsplit
         have hrest_in : ∑ l ∈ Finset.univ.erase (⟨p, hpu'⟩ : {l : Fin D // bUs stNext l = true}),
             g l • bVc stNext l.val ∈ L ⊓ R' := by
           apply Submodule.sum_mem; intro l hl
           have hne : l.val ≠ p := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
           rw [hvecNext_eq l.val]; simp only [hne, ↓reduceIte]
           have huM : bUs stMid l.val = true := by
             change usedMid l.val = true; rw [husedMid_eq l.val]; simp only [hne, ↓reduceIte]; rw [← husedNext_eq l.val]; exact l.property
           exact Submodule.smul_mem _ _ (by rw [← hMid_span]; exact Submodule.subset_span ⟨⟨l.val, huM⟩, rfl⟩)
         have hgp0 : g ⟨p, hpu'⟩ = 0 := by
           rcases zmod2_cases (g ⟨p, hpu'⟩) with h0 | h1
           · exact h0
           · exfalso; apply hnotC
             rw [h1, one_smul, hvecNext_eq p] at hsplit; simp only [↓reduceIte] at hsplit
             have : bVc st p + vi = ∑ l ∈ Finset.univ.erase (⟨p, hpu'⟩ : {l : Fin D // bUs stNext l = true}),
                 g l • bVc stNext l.val := by
               have hadd := congrArg (fun x => x + ∑ l ∈ Finset.univ.erase ⟨p, hpu'⟩, g l • bVc stNext l.val) hsplit
               simp only [add_assoc, zmod2_fun_add_self, add_zero, zero_add] at hadd
               exact hadd
             rw [this]; exact hrest_in
         rw [hgp0, zero_smul, zero_add] at hsplit
         let gM : {l : Fin D // bUs stMid l = true} → ZMod 2 := fun l =>
           g ⟨l.val, by
             have hl := l.property; change usedMid l.val = true at hl; rw [husedMid_eq l.val] at hl
             have hne : l.val ≠ p := fun h => by simp [h] at hl
             simp only [hne, ↓reduceIte] at hl; rw [husedNext_eq l.val]; exact hl⟩
         have hsumM : ∑ l : {l : Fin D // bUs stMid l = true}, gM l • bVc stMid l.val = 0 := by
           rw [← hsplit]
           symm
           refine Finset.sum_bij
             (fun l hl => ⟨l.val, by
               have hne : l.val ≠ p := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               change usedMid l.val = true; rw [husedMid_eq l.val]; simp only [hne, ↓reduceIte]; rw [← husedNext_eq l.val]; exact l.property⟩)
             (fun _ _ => Finset.mem_univ _)
             (fun a _ b _ heq => Subtype.ext (by simpa [Subtype.ext_iff] using heq))
             (fun r _ => by
               have hr := r.property; change usedMid r.val = true at hr; rw [husedMid_eq r.val] at hr
               have hne : r.val ≠ p := fun h => by simp [h] at hr
               simp only [hne, ↓reduceIte] at hr
               exact ⟨⟨r.val, by rw [husedNext_eq r.val]; exact hr⟩,
                 Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩)
             (fun l hl => by
               have hne : l.val ≠ p := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               rw [hvecNext_eq l.val]; simp only [hne, ↓reduceIte]; rfl)
         have hlinM := Fintype.linearIndependent_iff.mp hMid_li gM hsumM
         intro l
         by_cases hlp : l.val = p
         · have : l = ⟨p, hpu'⟩ := Subtype.ext hlp
           rw [this]; exact hgp0
         · have huM : bUs stMid l.val = true := by
             change usedMid l.val = true; rw [husedMid_eq l.val]; simp only [hlp, ↓reduceIte]; rw [← husedNext_eq l.val]; exact l.property
           exact hlinM ⟨l.val, huM⟩
       have hNext_span : Submodule.span (ZMod 2)
           (Set.range (fun l : {l : Fin D // bUs stNext l = true} => bVc stNext l.val)) = L' ⊓ R' := by
         rw [hL'R'_eq]
         apply le_antisymm
         · rw [Submodule.span_le]
           rintro _ ⟨⟨l, hl⟩, rfl⟩
           dsimp only
           rw [hvecNext_eq l]
           by_cases hlp : l = p
           · simp only [hlp, ↓reduceIte]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
           · simp only [hlp, ↓reduceIte]
             have huM : bUs stMid l = true := by
               change usedMid l = true; rw [husedMid_eq l]; simp only [hlp, ↓reduceIte]; rw [← husedNext_eq l]; exact hl
             exact Submodule.mem_sup_left (by rw [← hMid_span]; exact Submodule.subset_span ⟨⟨l, huM⟩, rfl⟩)
         · refine sup_le ?_ ?_
           · rw [← hMid_span, Submodule.span_le]
             rintro _ ⟨⟨l, hl⟩, rfl⟩
             dsimp only
             have hl' := hl; change usedMid l = true at hl'; rw [husedMid_eq l] at hl'
             have hne : l ≠ p := fun h => by simp [h] at hl'
             simp only [hne, ↓reduceIte] at hl'
             have huN : bUs stNext l = true := by rw [husedNext_eq l]; exact hl'
             have hbv : bVc stMid l = bVc stNext l := by rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]
             rw [hbv]; exact Submodule.subset_span ⟨⟨l, huN⟩, rfl⟩
           · rw [Submodule.span_singleton_le_iff_mem]
             have hpu' : bUs stNext p = true := by rw [husedNext_eq p]; exact hpu
             have hbv : bVc st p + vi = bVc stNext p := by rw [hvecNext_eq p]; simp only [↓reduceIte]
             rw [hbv]; exact Submodule.subset_span ⟨⟨p, hpu'⟩, rfl⟩
       have hviNI_1a : vi ∉ L ⊓ Rcur := fun hmem => by
         apply hnotC
         have hR' := (zmod2_subspace_step L R' vi hviNR (bVc st p) hpI.1 hpI.2 hpNR).1.2
         exact ⟨Submodule.add_mem _ hpI.1 hmem.1, hR'⟩
       refine ⟨⟨hNext_zero, hNext_li, hNext_span⟩, Or.inr (Or.inr (Or.inl ?_))⟩
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hviNI_1a, p, hpu, ?_, ?_, ?_, husedNext_eq, ?_, ?_⟩
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR, hhf]; rfl
       · rw [hmd_mode, hvR, hhf, hinC]; rfl
       · rw [hmd_mode, hvR, hhf, hinC]; rfl
       · rw [hmd_mode, hvR]; rfl
       · intro l; rw [hmd_avec, hvR, hhf, hinC]; rfl
       · rw [hmd_fvec, hvR, hhf, hinC]; exact hfp
       · intro l; rw [hmd_slot, hvR, hhf, hinC]; exact hfirst_eq l
       · intro l hl; rw [hmd_fvec, hvR, hhf, hinC]; simp [f, hl]
       · rw [hvecNext_eq p]; simp only [↓reduceIte]
       · intro l hne
         rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]
         have hfv : sFv md l = f l := by rw [hmd_fvec, hvR, hhf, hinC]; rfl
         rw [hfv]
         have := hBmid_vec l; simp only [hne, ↓reduceIte] at this; exact this
     ·
       have hinC_mem : bVc st p + vi ∈ L ⊓ R' := hsol1b.1.mp hinC
       obtain ⟨hα_val, hα_eq⟩ := hsol1b.2 hinC
       have hI_eq : L' ⊓ R' = L ⊓ R' := by
         rw [hL'R'_eq, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hinC_mem
       have hstNext_eq : stNext = stMid := by
         funext q; rcases q with ⟨l, j⟩ | l
         · change bMt stNext l j = Bmid (l, j); rw [hstNext_mat, hvR, hhf, hinC]; rfl
         · change bUs stNext l = usedMid l; rw [hstNext_used, hvR, hhf, hinC]; rfl
       rw [hI_eq, hstNext_eq]
       refine ⟨hMid_inv, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
       have hfv : ∀ l, sFv md l = f l := fun l => by
         rw [hmd_fvec, hvR, hhf, hinC]; rfl
       have hav : sAv md = alpha1b := by
         funext l; rw [hmd_avec, hvR, hhf, hinC]; rfl
       refine ⟨?_, ?_, ?_, ?_, ?_, p, hpu, ?_, ?_, ?_, husedMid_eq, ?_, ?_, ?_, ?_⟩
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR, hhf]; rfl
       · rw [hmd_mode, hvR, hhf, hinC]; rfl
       · rw [hmd_mode, hvR, hhf, hinC]; rfl
       · rw [hmd_mode, hvR]; rfl
       · rw [hfv p]; exact hfp
       · intro l; rw [hmd_slot, hvR, hhf, hinC]; exact hfirst_eq l
       · intro l hl; rw [hfv l]; simp [f, hl]
       · have := hBmid_vec p; simp only [↓reduceIte] at this; exact this
       · intro l hne; rw [hfv l]; have := hBmid_vec l; simp only [hne, ↓reduceIte] at this; exact this
       · rw [hav]; exact hα_val
       · rw [hav]; exact hα_eq
 ·
   have hviR : vi ∈ R' := (hmemR viB).mp hvR
   have hRcur_eq : Rcur = R' := by
     dsimp only [Rcur]; rw [sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hviR
   have hL'R'_eq : L' ⊓ R' = (L ⊓ Rcur) ⊔ Submodule.span (ZMod 2) {vi} := by
     rw [hRcur_eq]
     apply le_antisymm
     · intro z ⟨hzL', hzR'⟩
       change z ∈ L ⊔ Submodule.span (ZMod 2) {vi} at hzL'
       rw [Submodule.mem_sup] at hzL'
       obtain ⟨u, hu, t, ht, rfl⟩ := hzL'
       rw [Submodule.mem_span_singleton] at ht
       obtain ⟨a, rfl⟩ := ht
       have huR' : u ∈ R' := by
         have : u = (u + a • vi) + a • vi := by
           funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc, zmod2_add_self, add_zero]
         rw [this]; exact Submodule.add_mem _ hzR' (Submodule.smul_mem _ a hviR)
       exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨hu, huR'⟩)
         (Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.subset_span rfl)))
     · refine sup_le (inf_le_inf_right R' le_sup_left) ?_
       rw [Submodule.span_singleton_le_iff_mem]
       exact ⟨Submodule.mem_sup_right (Submodule.subset_span rfl), hviR⟩
   cases hinB : inB
   ·
     have hviNI : vi ∉ L ⊓ Rcur := fun hm => by
       have := hsol3a.1.mpr hm; change inB = true at this; rw [hinB] at this; exact Bool.noConfusion this
     have hdim_succ : Module.finrank (ZMod 2) ↥(L' ⊓ R') = Module.finrank (ZMod 2) ↥(L ⊓ Rcur) + 1 := by
       rw [hL'R'_eq]
       have hmod := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ Rcur) (Submodule.span (ZMod 2) {vi})
       have hinf0 : (L ⊓ Rcur) ⊓ Submodule.span (ZMod 2) {vi} = ⊥ := by
         rw [eq_bot_iff]; intro z ⟨hzI, hzV⟩
         change z ∈ Submodule.span (ZMod 2) {vi} at hzV
         rw [Submodule.mem_span_singleton] at hzV
         obtain ⟨a, rfl⟩ := hzV
         rcases zmod2_cases a with rfl | rfl
         · simp
         · rw [one_smul] at hzI; exact absurd hzI hviNI
       have hvi_ne0 : vi ≠ 0 := fun h0 => hviNI (h0 ▸ Submodule.zero_mem _)
       have hsp1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {vi}) = 1 :=
         finrank_span_singleton hvi_ne0
       rw [hinf0, finrank_bot, add_zero, hsp1] at hmod
       exact hmod
     have hover_eq : sOv md = !hasFree := by
       rw [hmd_over, hvR, hinB]; rfl
     refine ⟨?_, ?_⟩
     · rw [hover_eq, Bool.not_eq_true', hdim_succ]
       constructor
       · intro hnf
         by_contra hle
         have hlt : Module.finrank (ZMod 2) ↥(L ⊓ Rcur) < D := by omega
         have := hfree_iff.mpr hlt; rw [hnf] at this; exact Bool.noConfusion this
       · intro hgt
         cases hf' : hasFree
         · rfl
         · have := hfree_iff.mp hf'; omega
     · intro hno_over
       rw [hover_eq, Bool.not_eq_false'] at hno_over
       have hexFree : ∃ l : Fin D, (!bUs st l) = true := by
         obtain ⟨l, hl⟩ := (decide_eq_true_iff).mp hno_over
         exact ⟨l, by simp [hl]⟩
       obtain ⟨q, hqu_not, hfirstFree_eq⟩ := exists_first_true (fun l => !(bUs st l)) hexFree
       have hqu : bUs st q = false := by simpa using hqu_not
       have hff_eq : ∀ l : Fin D, firstFree l = decide (l = q) := by
         intro l
         have h := hfirstFree_eq l
         have heq_dec : decide (∀ l' : Fin D, l'.val < l.val → bUs st l' = true) =
             decide (∀ l' : Fin D, l'.val < l.val → (!bUs st l') = false) := by
           simp only [Bool.not_eq_false']
         dsimp only [firstFree]; rw [heq_dec]; exact h
       have husedNext_eq : ∀ l : Fin D, bUs stNext l = if l = q then true else bUs st l := by
         intro l
         rw [hstNext_used, hvR, hinB, hno_over]
         have hff := hff_eq l
         change (bUs st l || firstFree l) = _
         rw [hff]
         by_cases hlq : l = q <;> simp [hlq]
       have hvecNext_eq : ∀ l : Fin D, bVc stNext l = if l = q then vi else bVc st l := by
         intro l; funext j
         change b2z (bMt stNext l j) = _
         rw [hstNext_mat, hvR, hinB, hno_over]
         have hff := hff_eq l
         change b2z (if firstFree l = true then viB j else bMt st l j) = _
         rw [hff]
         by_cases hlq : l = q <;> simp [hlq, vi, bVc]
       have hNext_zero : ∀ l : Fin D, bUs stNext l = false → bVc stNext l = 0 := by
         intro l hl; rw [husedNext_eq l] at hl
         have hne : l ≠ q := fun h => by simp [h] at hl
         simp only [hne, ↓reduceIte] at hl
         rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]; exact hinv.1 l hl
       have hNext_li : LinearIndependent (ZMod 2)
           (fun l : {l : Fin D // bUs stNext l = true} => bVc stNext l.val) := by
         rw [Fintype.linearIndependent_iff]
         intro g hg
         have hqu' : bUs stNext q = true := by rw [husedNext_eq q]; simp only [↓reduceIte]
         have hsplit := Finset.add_sum_erase Finset.univ
           (fun l : {l : Fin D // bUs stNext l = true} => g l • bVc stNext l.val)
           (Finset.mem_univ (⟨q, hqu'⟩ : {l : Fin D // bUs stNext l = true}))
         rw [hg] at hsplit
         have hrest_in : ∑ l ∈ Finset.univ.erase (⟨q, hqu'⟩ : {l : Fin D // bUs stNext l = true}),
             g l • bVc stNext l.val ∈ L ⊓ Rcur := by
           apply Submodule.sum_mem; intro l hl
           have hne : l.val ≠ q := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
           have hul : bUs st l.val = true := by have := l.property; rw [husedNext_eq l.val] at this; simp only [hne, ↓reduceIte] at this; exact this
           rw [hvecNext_eq l.val]; simp only [hne, ↓reduceIte]
           exact Submodule.smul_mem _ _ (by rw [← hinv.2.2]; exact Submodule.subset_span ⟨⟨l.val, hul⟩, rfl⟩)
         have hgq0 : g ⟨q, hqu'⟩ = 0 := by
           rcases zmod2_cases (g ⟨q, hqu'⟩) with h0 | h1
           · exact h0
           · exfalso; apply hviNI
             rw [h1, one_smul, hvecNext_eq q] at hsplit; simp only [↓reduceIte] at hsplit
             have : vi = ∑ l ∈ Finset.univ.erase (⟨q, hqu'⟩ : {l : Fin D // bUs stNext l = true}),
                 g l • bVc stNext l.val := by
               have hadd := congrArg (fun x => x + ∑ l ∈ Finset.univ.erase ⟨q, hqu'⟩, g l • bVc stNext l.val) hsplit
               simp only [add_assoc, zmod2_fun_add_self, add_zero, zero_add] at hadd
               exact hadd
             rw [this]; exact hrest_in
         rw [hgq0, zero_smul, zero_add] at hsplit
         let gO : {l : Fin D // bUs st l = true} → ZMod 2 := fun l =>
           g ⟨l.val, by rw [husedNext_eq l.val]; by_cases h : l.val = q <;> simp [h, l.property]⟩
         have hsumO : ∑ l : {l : Fin D // bUs st l = true}, gO l • bVc st l.val = 0 := by
           rw [← hsplit]; symm
           refine Finset.sum_bij
             (fun l hl => ⟨l.val, by
               have hne : l.val ≠ q := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               have := l.property; rw [husedNext_eq l.val] at this; simp only [hne, ↓reduceIte] at this; exact this⟩)
             (fun _ _ => Finset.mem_univ _)
             (fun a _ b _ heq => Subtype.ext (by simpa [Subtype.ext_iff] using heq))
             (fun r _ => by
               have hne : r.val ≠ q := fun h => by have hrp := r.property; rw [h, hqu] at hrp; exact Bool.noConfusion hrp
               exact ⟨⟨r.val, by rw [husedNext_eq r.val]; simp only [hne, ↓reduceIte]; exact r.property⟩,
                 Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩)
             (fun l hl => by
               have hne : l.val ≠ q := fun h => (Finset.mem_erase.mp hl).1 (Subtype.ext h)
               rw [hvecNext_eq l.val]; simp only [hne, ↓reduceIte]; rfl)
         have hlinO := Fintype.linearIndependent_iff.mp hinv.2.1 gO hsumO
         intro l
         by_cases hlq : l.val = q
         · have : l = ⟨q, hqu'⟩ := Subtype.ext hlq; rw [this]; exact hgq0
         · have hul : bUs st l.val = true := by have := l.property; rw [husedNext_eq l.val] at this; simp only [hlq, ↓reduceIte] at this; exact this
           exact hlinO ⟨l.val, hul⟩
       have hNext_span : Submodule.span (ZMod 2)
           (Set.range (fun l : {l : Fin D // bUs stNext l = true} => bVc stNext l.val)) = L' ⊓ R' := by
         rw [hL'R'_eq]
         apply le_antisymm
         · rw [Submodule.span_le]
           rintro _ ⟨⟨l, hl⟩, rfl⟩
           dsimp only
           rw [hvecNext_eq l]
           by_cases hlq : l = q
           · simp only [hlq, ↓reduceIte]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
           · simp only [hlq, ↓reduceIte]
             have hul : bUs st l = true := by rw [husedNext_eq l] at hl; simp only [hlq, ↓reduceIte] at hl; exact hl
             exact Submodule.mem_sup_left (by rw [← hinv.2.2]; exact Submodule.subset_span ⟨⟨l, hul⟩, rfl⟩)
         · refine sup_le ?_ ?_
           · rw [← hinv.2.2, Submodule.span_le]
             rintro _ ⟨⟨l, hl⟩, rfl⟩
             dsimp only
             have hne : l ≠ q := fun h => by subst h; rw [hqu] at hl; exact Bool.noConfusion hl
             have huN : bUs stNext l = true := by rw [husedNext_eq l]; simp only [hne, ↓reduceIte]; exact hl
             have hbv : bVc st l = bVc stNext l := by rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]
             rw [hbv]; exact Submodule.subset_span ⟨⟨l, huN⟩, rfl⟩
           · rw [Submodule.span_singleton_le_iff_mem]
             have hqu' : bUs stNext q = true := by rw [husedNext_eq q]; simp only [↓reduceIte]
             have hbv : vi = bVc stNext q := by rw [hvecNext_eq q]; simp only [↓reduceIte]
             rw [hbv]; exact Submodule.subset_span ⟨⟨q, hqu'⟩, rfl⟩
       refine ⟨⟨hNext_zero, hNext_li, hNext_span⟩, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hviNI, q, hqu, ?_, husedNext_eq, ?_, ?_⟩
       · rw [hmd_mode, hvR, hinB]; rfl
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR]; rfl
       · rw [hmd_mode, hvR, hinB, hno_over]; rfl
       · intro l; rw [hmd_avec, hvR, hinB]; rfl
       · intro l; rw [hmd_slot, hvR, hinB, hno_over]; exact hff_eq l
       · rw [hvecNext_eq q]; simp only [↓reduceIte]
       · intro l hne; rw [hvecNext_eq l]; simp only [hne, ↓reduceIte]
   ·
     have hviI : vi ∈ L ⊓ Rcur := hsol3a.1.mp hinB
     obtain ⟨hα_val, hα_eq⟩ := hsol3a.2 hinB
     have hI_eq : L' ⊓ R' = L ⊓ Rcur := by
       rw [hL'R'_eq, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hviI
     have hover_false : sOv md = false := by
       rw [hmd_over, hvR, hinB]; rfl
     refine ⟨by rw [hover_false, hI_eq]; simp only [Bool.false_eq_true, false_iff, not_lt]; exact hdim_le, fun _ => ?_⟩
     have hst_eq : stNext = st := by
       funext q; rcases q with ⟨l, j⟩ | l
       · change bMt stNext l j = bMt st l j; rw [hstNext_mat, hvR, hinB]; rfl
       · change bUs stNext l = bUs st l; rw [hstNext_used, hvR, hinB]; rfl
     have hav : sAv md = alpha3a := by
       funext l; rw [hmd_avec, hvR, hinB]; rfl
     rw [hI_eq, hst_eq]
     refine ⟨hinv, Or.inl ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩⟩
     · rw [hmd_mode, hvR, hinB]; rfl
     · rw [hmd_mode, hvR]; rfl
     · rw [hmd_mode, hvR]; rfl
     · rw [hmd_mode, hvR]; rfl
     · rw [hmd_mode, hvR, hinB]; rfl
     · rw [hav]; exact hα_val
     · rw [hav]; exact hα_eq
def flipBit {D : ℕ} (p : Fin D) (x : Fin D → Bool) (i : Fin D) : Bool :=
 if i = p then !(x p) else x i
def setBit {D : ℕ} (p : Fin D) (v : Bool) (x : Fin D → Bool) (i : Fin D) : Bool :=
 if i = p then v else x i
def aRAS {D Wbits : ℕ} (p l : Fin D)
   (inp : Unit ⊕ ((Fin D → Bool) × Fin Wbits) → Bool) (q : (Fin D → Bool) × Fin Wbits) : Bool :=
 let en := inp (inl ())
 if en && q.1 l then inp (inr (flipBit p q.1, q.2)) else inp (inr q)
def applyXorShiftStep {D Wbits : ℕ} (l : Fin D)
   (inp : Unit ⊕ ((Fin D → Bool) × Fin Wbits) → Bool) (q : (Fin D → Bool) × Fin Wbits) : Bool :=
 let en := inp (inl ())
 if en then inp (inr (flipBit l q.1, q.2)) else inp (inr q)
def aCS1 {D Wbits : ℕ} (md : SM D → Bool)
   (arr : (Fin D → Bool) × Fin Wbits → Bool) : (Fin D → Bool) × Fin Wbits → Bool :=
 let pairs : List (Fin D × Fin D) := (List.finRange D).flatMap (fun p => (List.finRange D).map (fun l => (p, l)))
 pairs.foldl (fun cur pl =>
   let en := (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)
   aRAS pl.1 pl.2 (Sum.elim (fun _ => en) cur)) arr
def aCS2 {D Wbits : ℕ} (md : SM D → Bool) (ci : Bool)
   (arr : (Fin D → Bool) × Fin Wbits → Bool) : (Fin D → Bool) × Fin Wbits → Bool :=
 (List.finRange D).foldl (fun cur l =>
   let en := ci && sAv md l
   applyXorShiftStep l (Sum.elim (fun _ => en) cur)) arr
def aCS3 {D Wbits : ℕ} (md : SM D → Bool) (ci : Bool)
   (arr : (Fin D → Bool) × Fin Wbits → Bool) (q : (Fin D → Bool) × Fin Wbits) : Bool :=
 let x := q.1
 let b := q.2
 let v0 := sMd md 0 && arr (x, b)
 let v1 := sMd md 1 && (!ci) && arr (x, b)
 let v2 := sMd md 2 && decide (∃ p : Fin D, sSl md p = true ∧ x p = ci) && arr (x, b)
 let v3 := sMd md 3 && decide (∃ p : Fin D, sSl md p = true ∧ x p = false ∧ arr (setBit p ci x, b) = true)
 let v4 := sMd md 4 && decide (∃ q0 : Fin D, sSl md q0 = true ∧ x q0 = ci ∧ arr (setBit q0 false x, b) = true)
 v0 || v1 || v2 || v3 || v4
def aCut (D Wbits : ℕ) (inp : SM D ⊕ Unit ⊕ ((Fin D → Bool) × Fin Wbits) → Bool)
   (q : (Fin D → Bool) × Fin Wbits) : Bool :=
 let md : SM D → Bool := fun a => inp (inl a)
 let ci : Bool := inp (inr (inl ()))
 let arr : (Fin D → Bool) × Fin Wbits → Bool := fun r => inp (inr (inr r))
 aCS3 md ci (aCS2 md ci (aCS1 md arr)) q
lemma ec_aRAS (D Wbits : ℕ) (p l : Fin D) :
   EC (10 * Wbits * 2 ^ D + 10) (aRAS (Wbits := Wbits) p l) := by
 let I := Unit ⊕ ((Fin D → Bool) × Fin Wbits)
 have hen : EC 0 (fun (inp : I → Bool) (_ : (Fin D → Bool) × Fin Wbits) => inp (inl ())) := ec_proj _
 have hxl : EC 2 (fun (_ : I → Bool) (q : (Fin D → Bool) × Fin Wbits) => q.1 l) := ec_const _
 have hcond := ec_and_of hen hxl
 have hflip : EC 0 (fun (inp : I → Bool) (q : (Fin D → Bool) × Fin Wbits) =>
     inp (inr (flipBit p q.1, q.2))) := ec_proj _
 have hcur : EC 0 (fun (inp : I → Bool) (q : (Fin D → Bool) × Fin Wbits) => inp (inr q)) := ec_proj _
 have hite := ec_ite_of hcond hflip hcur
 simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
   Finset.card_univ, Fintype.card_fin] at hite
 exact ec_le hite (by
   have hpow : 1 ≤ 2 ^ D := Nat.one_le_two_pow
   nlinarith)
lemma ec_applyXorShiftStep (D Wbits : ℕ) (l : Fin D) :
   EC (10 * Wbits * 2 ^ D + 10) (applyXorShiftStep (Wbits := Wbits) l) := by
 let I := Unit ⊕ ((Fin D → Bool) × Fin Wbits)
 have hen : EC 0 (fun (inp : I → Bool) (_ : (Fin D → Bool) × Fin Wbits) => inp (inl ())) := ec_proj _
 have hflip : EC 0 (fun (inp : I → Bool) (q : (Fin D → Bool) × Fin Wbits) =>
     inp (inr (flipBit l q.1, q.2))) := ec_proj _
 have hcur : EC 0 (fun (inp : I → Bool) (q : (Fin D → Bool) × Fin Wbits) => inp (inr q)) := ec_proj _
 have hite := ec_ite_of hen hflip hcur
 simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
   Finset.card_univ, Fintype.card_fin] at hite
 exact ec_le hite (by
   have hpow : 1 ≤ 2 ^ D := Nat.one_le_two_pow
   nlinarith)
lemma ec_aCut (D Wbits : ℕ) :
   EC (80 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 40 * (D + 1) * (D + 1)) (aCut D Wbits) := by
 let I := SM D ⊕ Unit ⊕ ((Fin D → Bool) × Fin Wbits)
 let A := (Fin D → Bool) × Fin Wbits
 have hcardA : Fintype.card A = 2 ^ D * Wbits := by
   simp only [A, Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
     Finset.card_univ, Fintype.card_fin]
 have hs1 : EC (D * D * (10 * Wbits * 2 ^ D + 20))
     (fun (inp : I → Bool) =>
       aCS1 (fun a => inp (inl a)) (fun r => inp (inr (inr r)))) := by
   let pairs : List (Fin D × Fin D) := (List.finRange D).flatMap (fun p => (List.finRange D).map (fun l => (p, l)))
   have hplen : pairs.length = D * D := by
     simp [pairs, List.length_flatMap, List.map_const', List.sum_replicate]
   have hfold : ∀ (ls : List (Fin D × Fin D)),
       EC (ls.length * (10 * Wbits * 2 ^ D + 20))
         (fun (inp : I → Bool) =>
           ls.foldl (fun cur pl =>
             let md := fun a => inp (inl a)
             let en := (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)
             aRAS pl.1 pl.2 (Sum.elim (fun _ => en) cur))
             (fun r => inp (inr (inr r)))) := by
     intro ls
     induction ls using List.reverseRecOn with
     | nil => simpa using ec_proj (fun r : A => (inr (inr r) : I))
     | append_singleton ls pl ih =>
       have hen : EC 10
           (fun (y : I ⊕ A → Bool) (_ : Unit) =>
             (y (inl (inl (inl 2))) || y (inl (inl (inl 3)))) &&
               y (inl (inl (inr (inl pl.1)))) &&
               y (inl (inl (inr (inr (inl pl.2))))) && decide (pl.2 ≠ pl.1)) := by
         have hm2 : EC 0 (fun (y : I ⊕ A → Bool) (_ : Unit) => y (inl (inl (inl 2)))) := ec_proj _
         have hm3 : EC 0 (fun (y : I ⊕ A → Bool) (_ : Unit) => y (inl (inl (inl 3)))) := ec_proj _
         have hsl : EC 0 (fun (y : I ⊕ A → Bool) (_ : Unit) => y (inl (inl (inr (inl pl.1))))) := ec_proj _
         have hfv : EC 0 (fun (y : I ⊕ A → Bool) (_ : Unit) => y (inl (inl (inr (inr (inl pl.2)))))) := ec_proj _
         have hne : EC 2 (fun (_ : I ⊕ A → Bool) (_ : Unit) => decide (pl.2 ≠ pl.1)) := ec_const _
         have h := ec_and_of (ec_and_of (ec_and_of (ec_or_of hm2 hm3) hsl) hfv) hne
         rw [Fintype.card_unit] at h; exact ec_le h (by omega)
       have hstep := ec_comp (ec_pair hen (ec_proj (fun r : A => (inr r : I ⊕ A))))
         (ec_aRAS D Wbits pl.1 pl.2)
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) ?_
       · intro inp q
         simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
         rfl
       · simp only [List.length_append, List.length_singleton]; nlinarith
   have h := hfold pairs
   rw [hplen] at h; exact h
 let I1 := I ⊕ A
 have hs2 : EC (D * (10 * Wbits * 2 ^ D + 14))
     (fun (y : I1 → Bool) =>
       aCS2 (fun a => y (inl (inl a))) (y (inl (inr (inl ()))))
         (fun r => y (inr r))) := by
   have hfold : ∀ (ls : List (Fin D)),
       EC (ls.length * (10 * Wbits * 2 ^ D + 14))
         (fun (y : I1 → Bool) =>
           ls.foldl (fun cur l =>
             let en := y (inl (inr (inl ()))) &&
               y (inl (inl (inr (inr (inr (inl l))))))
             applyXorShiftStep l (Sum.elim (fun _ => en) cur))
             (fun r => y (inr r))) := by
     intro ls
     induction ls using List.reverseRecOn with
     | nil => simpa using ec_proj (fun r : A => (inr r : I1))
     | append_singleton ls l ih =>
       have hen : EC 4
           (fun (z : I1 ⊕ A → Bool) (_ : Unit) =>
             z (inl (inl (inr (inl ())))) &&
               z (inl (inl (inl (inr (inr (inr (inl l)))))))) := by
         have h := ec_and_of
           (ec_proj (fun (_ : Unit) => (inl (inl (inr (inl ()))) : I1 ⊕ A)))
           (ec_proj (fun (_ : Unit) => (inl (inl (inl (inr (inr (inr (inl l)))))) : I1 ⊕ A)))
         rw [Fintype.card_unit] at h; exact ec_le h (by omega)
       have hstep := ec_comp (ec_pair hen (ec_proj (fun r : A => (inr r : I1 ⊕ A))))
         (ec_applyXorShiftStep D Wbits l)
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) ?_
       · intro y q
         simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
         rfl
       · simp only [List.length_append, List.length_singleton]; nlinarith
   have h := hfold (List.finRange D)
   rw [List.length_finRange] at h; exact h
 let I2 := I1 ⊕ A
 have hs3 : EC (2 ^ D * Wbits * (40 * D + 60))
     (fun (z : I2 → Bool) (q : A) =>
       aCS3 (fun a => z (inl (inl (inl a))))
         (z (inl (inl (inr (inl ())))))
         (fun r => z (inr r)) q) := by
   have hfam := ec_family (s := 40 * D + 60)
     (f := fun (q : A) (z : I2 → Bool) (_ : Unit) =>
       aCS3 (fun a => z (inl (inl (inl a))))
         (z (inl (inl (inr (inl ())))))
         (fun r => z (inr r)) q)
     (fun q => by
       have hm0 : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inl (inl 0))))) := ec_proj _
       have hm1 : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inl (inl 1))))) := ec_proj _
       have hm2 : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inl (inl 2))))) := ec_proj _
       have hm3 : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inl (inl 3))))) := ec_proj _
       have hm4 : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inl (inl 4))))) := ec_proj _
       have hci : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inl (inr (inl ()))))) := ec_proj _
       have harr : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inr q)) := ec_proj _
       have hv0 := ec_and_of hm0 harr
       have hv1 := ec_and_of (ec_and_of hm1 (ec_not_of hci)) harr
       have h2any : EC (9 * D + 6)
           (fun (z : I2 → Bool) (_ : Unit) =>
             decide (∃ p : Fin D, z (inl (inl (inl (inr (inl p))))) = true ∧
               q.1 p = z (inl (inl (inr (inl ())))))) := by
         have hsl : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inl (inl (inl (inr (inl p)))))) := ec_proj _
         have hciD : EC 0 (fun (z : I2 → Bool) (_ : Fin D) => z (inl (inl (inr (inl ()))))) := ec_proj _
         have heq : EC (5 * D + 2) (fun (z : I2 → Bool) (p : Fin D) => if q.1 p then z (inl (inl (inr (inl ())))) else !(z (inl (inl (inr (inl ())))))) := by
           have h := ec_ite_of (ec_const (fun p : Fin D => q.1 p)) hciD (ec_not_of hciD)
           rw [Fintype.card_fin] at h; exact ec_le h (by omega)
         have hand := ec_and_of hsl heq
         have hany := ec_comp hand (ec_any (α := Fin D))
         rw [Fintype.card_fin] at hany
         refine ec_le (ec_eq ?_ hany) (by omega)
         intro z u; simp only [decide_eq_decide]
         apply exists_congr; intro p
         cases q.1 p <;> cases z (inl (inl (inr (inl ())))) <;> simp
       have hv2 := ec_and_of (ec_and_of hm2 h2any) harr
       have h3any : EC (10 * D + 6)
           (fun (z : I2 → Bool) (_ : Unit) =>
             decide (∃ p : Fin D, z (inl (inl (inl (inr (inl p))))) = true ∧
               q.1 p = false ∧
               z (inr (setBit p (z (inl (inl (inr (inl ()))))) q.1, q.2)) = true)) := by
         have hsl : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inl (inl (inl (inr (inl p)))))) := ec_proj _
         have hxf : EC 2 (fun (_ : I2 → Bool) (p : Fin D) => !(q.1 p)) := ec_const _
         have hciD : EC 0 (fun (z : I2 → Bool) (_ : Fin D) => z (inl (inl (inr (inl ()))))) := ec_proj _
         have haT : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inr (setBit p true q.1, q.2))) := ec_proj _
         have haF : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inr (setBit p false q.1, q.2))) := ec_proj _
         have haC := ec_ite_of hciD haT haF
         have hand := ec_and_of (ec_and_of hsl hxf) haC
         have hany := ec_comp hand (ec_any (α := Fin D))
         rw [Fintype.card_fin] at hany
         refine ec_le (ec_eq ?_ hany) (by omega)
         intro z u; simp only [decide_eq_decide]
         apply exists_congr; intro p
         cases hci0 : z (inl (inl (inr (inl ())))) <;> cases q.1 p <;> simp [Bool.and_eq_true]
       have hv3 := ec_and_of hm3 h3any
       have h4any : EC (10 * D + 6)
           (fun (z : I2 → Bool) (_ : Unit) =>
             decide (∃ q0 : Fin D, z (inl (inl (inl (inr (inl q0))))) = true ∧
               q.1 q0 = z (inl (inl (inr (inl ())))) ∧
               z (inr (setBit q0 false q.1, q.2)) = true)) := by
         have hsl : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inl (inl (inl (inr (inl p)))))) := ec_proj _
         have hciD : EC 0 (fun (z : I2 → Bool) (_ : Fin D) => z (inl (inl (inr (inl ()))))) := ec_proj _
         have heq : EC (5 * D + 2) (fun (z : I2 → Bool) (p : Fin D) => if q.1 p then z (inl (inl (inr (inl ())))) else !(z (inl (inl (inr (inl ())))))) := by
           have h := ec_ite_of (ec_const (fun p : Fin D => q.1 p)) hciD (ec_not_of hciD)
           rw [Fintype.card_fin] at h; exact ec_le h (by omega)
         have haF : EC 0 (fun (z : I2 → Bool) (p : Fin D) => z (inr (setBit p false q.1, q.2))) := ec_proj _
         have hand := ec_and_of (ec_and_of hsl heq) haF
         have hany := ec_comp hand (ec_any (α := Fin D))
         rw [Fintype.card_fin] at hany
         refine ec_le (ec_eq ?_ hany) (by omega)
         intro z u; simp only [decide_eq_decide]
         apply exists_congr; intro p
         cases q.1 p <;> cases z (inl (inl (inr (inl ())))) <;> simp [Bool.and_eq_true]
       have hv4 := ec_and_of hm4 h4any
       have hall := ec_or_of (ec_or_of (ec_or_of (ec_or_of hv0 hv1) hv2) hv3) hv4
       rw [Fintype.card_unit] at hall
       exact ec_le (ec_eq (fun z u => rfl) hall) (by omega))
   rw [hcardA] at hfam
   have hp := ec_comp hfam (ec_proj (fun q : A => (q, ())))
   rw [add_zero] at hp; exact hp
 have htot := ec_let hs1 (ec_let hs2 hs3)
 refine ec_le (ec_eq ?_ htot) ?_
 · intro inp q; rfl
 · have h1 : D * D * (10 * Wbits * 2 ^ D + 20) ≤ 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 20 * (D + 1) * (D + 1) := by
     have ha : D * D * (10 * Wbits * 2 ^ D) ≤ 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by
       have hdd : D * D ≤ (D + 1) * (D + 1) := by nlinarith
       have h10 : 10 * Wbits * 2 ^ D ≤ 10 * (Wbits + 1) * 2 ^ D := by nlinarith [Nat.one_le_two_pow (n := D)]
       have hmul := Nat.mul_le_mul hdd h10
       calc D * D * (10 * Wbits * 2 ^ D) ≤ (D + 1) * (D + 1) * (10 * (Wbits + 1) * 2 ^ D) := hmul
         _ = 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by ring
     have hb : D * D * 20 ≤ 20 * (D + 1) * (D + 1) := by nlinarith
     linarith only [ha, hb]
   have h2 : D * (10 * Wbits * 2 ^ D + 14) ≤ 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 20 * (D + 1) * (D + 1) := by
     have ha : D * (10 * Wbits * 2 ^ D) ≤ 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by
       have hd : D ≤ (D + 1) * (D + 1) := by nlinarith
       have h10 : 10 * Wbits * 2 ^ D ≤ 10 * (Wbits + 1) * 2 ^ D := by nlinarith [Nat.one_le_two_pow (n := D)]
       have hmul := Nat.mul_le_mul hd h10
       calc D * (10 * Wbits * 2 ^ D) ≤ (D + 1) * (D + 1) * (10 * (Wbits + 1) * 2 ^ D) := hmul
         _ = 10 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by ring
     have hb : D * 14 ≤ 20 * (D + 1) * (D + 1) := by nlinarith
     linarith only [ha, hb]
   have h3 : 2 ^ D * Wbits * (40 * D + 60) ≤ 60 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by
     have h40 : Wbits * (40 * D + 60) ≤ 60 * (D + 1) * (D + 1) * (Wbits + 1) := by nlinarith
     have hmul := Nat.mul_le_mul_left (2 ^ D) h40
     calc 2 ^ D * Wbits * (40 * D + 60) = 2 ^ D * (Wbits * (40 * D + 60)) := by ring
       _ ≤ 2 ^ D * (60 * (D + 1) * (D + 1) * (Wbits + 1)) := hmul
       _ = 60 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D := by ring
   linarith only [h1, h2, h3]
lemma aCS1_np {D Wbits : ℕ} (md : SM D → Bool)
   (hm2 : sMd md 2 = false) (hm3 : sMd md 3 = false)
   (arr : (Fin D → Bool) × Fin Wbits → Bool) :
   aCS1 md arr = arr := by
 unfold aCS1
 have hgen : ∀ (ls : List (Fin D × Fin D)) (cur : (Fin D → Bool) × Fin Wbits → Bool),
     ls.foldl (fun c pl =>
       let en := (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)
       aRAS pl.1 pl.2 (Sum.elim (fun _ => en) c)) cur = cur := by
   intro ls
   induction ls with
   | nil => intro _; rfl
   | cons pl tl ih =>
     intro cur
     rw [List.foldl_cons]
     have hstep : aRAS pl.1 pl.2
         (Sum.elim (fun _ => (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)) cur) = cur := by
       funext q; simp [aRAS, hm2, hm3]
     rw [hstep, ih]
 exact hgen _ arr
lemma aCS1_rA {D Wbits : ℕ} (md : SM D → Bool)
   (hmode : sMd md 2 = true ∨ sMd md 3 = true)
   (p : Fin D) (hslot : ∀ l : Fin D, sSl md l = decide (l = p))
   (arr : (Fin D → Bool) × Fin Wbits → Bool) (x : Fin D → Bool) (b : Fin Wbits) :
   aCS1 md arr (x, b) =
     arr (fun i => if i = p then
       xor (x p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && x l)) false)
     else x i, b) := by
 have hm23 : (sMd md 2 || sMd md 3) = true := by rcases hmode with h | h <;> simp [h]
 unfold aCS1
 have hrow_p : ∀ (p0 : Fin D) (ls : List (Fin D)) (cur : (Fin D → Bool) × Fin Wbits → Bool)
     (y : Fin D → Bool),
     (ls.map (fun l => (p0, l))).foldl (fun c pl =>
       let en := (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)
       aRAS pl.1 pl.2 (Sum.elim (fun _ => en) c)) cur (y, b) =
     if p0 = p then
       cur (fun i => if i = p then
         xor (y p) (ls.foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && y l)) false)
       else y i, b)
     else cur (y, b) := by
   intro p0 ls
   induction ls with
   | nil =>
     intro cur y
     simp only [List.map_nil, List.foldl_nil]
     split_ifs
     · congr 1; exact Prod.ext (funext fun i => by by_cases hi : i = p <;> simp [hi]) rfl
     · rfl
   | cons l tl ih =>
     intro cur y
     simp only [List.map_cons, List.foldl_cons]
     rw [ih]
     by_cases hp0 : p0 = p
     · subst p0
       simp only [↓reduceIte, aRAS, Sum.elim_inl, Sum.elim_inr, hm23, hslot p,
         decide_true, Bool.true_and]
       let bit_l := sFv md l && decide (l ≠ p) && y l
       have hfl_eq : ∀ (init : Bool),
           tl.foldl (fun acc r => xor acc (sFv md r && decide (r ≠ p) && y r)) init =
           xor init (tl.foldl (fun acc r => xor acc (sFv md r && decide (r ≠ p) && y r)) false) := by
         clear ih; induction tl with
         | nil => intro init; simp
         | cons hd tl' ih' =>
           intro init; simp only [List.foldl_cons, Bool.false_xor]
           rw [ih' (xor init _), ih' (sFv md hd && decide (hd ≠ p) && y hd), Bool.xor_assoc]
       have heq_cond : (sFv md l && decide (l ≠ p) &&
           (if l = p then xor (y p) (tl.foldl (fun acc r => xor acc (sFv md r && decide (r ≠ p) && y r)) false) else y l)) =
           bit_l := by
         by_cases hlp : l = p
         · subst hlp; simp [bit_l]
         · simp [hlp, bit_l]
       rw [heq_cond, Bool.false_xor, hfl_eq bit_l]
       cases hbl : bit_l
       · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor]
       · simp only [↓reduceIte, Bool.true_xor]
         congr 1; congr 1; funext i
         unfold flipBit
         by_cases hip : i = p
         · rw [hip]; cases y p <;> simp
         · simp [hip]
     · simp only [hp0, ↓reduceIte]
       unfold aRAS
       simp [hslot p0, decide_eq_false hp0]
 have hflat : ∀ (ps : List (Fin D)) (hnd : ps.Nodup) (cur : (Fin D → Bool) × Fin Wbits → Bool) (y : Fin D → Bool),
     (ps.flatMap (fun p0 => (List.finRange D).map (fun l => (p0, l)))).foldl (fun c pl =>
       let en := (sMd md 2 || sMd md 3) && sSl md pl.1 && sFv md pl.2 && decide (pl.2 ≠ pl.1)
       aRAS pl.1 pl.2 (Sum.elim (fun _ => en) c)) cur (y, b) =
     if p ∈ ps then
       cur (fun i => if i = p then
         xor (y p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && y l)) false)
       else y i, b)
     else cur (y, b) := by
   intro ps
   induction ps with
   | nil => intro _ _ _; simp
   | cons p0 tl ih =>
     intro hnd cur y
     rw [List.nodup_cons] at hnd
     rw [List.flatMap_cons, List.foldl_append, ih hnd.2]
     by_cases hptl : p ∈ tl
     · have hne : p0 ≠ p := fun h => hnd.1 (h ▸ hptl)
       simp only [hptl, ↓reduceIte, List.mem_cons, or_true]
       rw [hrow_p p0]; simp only [hne, ↓reduceIte]
     · simp only [hptl, ↓reduceIte, List.mem_cons, or_false]
       rw [hrow_p p0]
       by_cases hp0 : p0 = p
       · subst hp0; simp
       · simp [hp0, Ne.symm hp0]
 have h := hflat (List.finRange D) (List.nodup_finRange D) arr x
 simpa using h
lemma aCS2_sp {D Wbits : ℕ} (md : SM D → Bool) (ci : Bool)
   (arr : (Fin D → Bool) × Fin Wbits → Bool) (x : Fin D → Bool) (b : Fin Wbits) :
   aCS2 md ci arr (x, b) =
     arr (fun i => xor (x i) (ci && sAv md i), b) := by
 unfold aCS2
 have hgen : ∀ (ls : List (Fin D)) (hnd : ls.Nodup) (cur : (Fin D → Bool) × Fin Wbits → Bool)
     (y : Fin D → Bool),
     ls.foldl (fun c l => applyXorShiftStep l (Sum.elim (fun _ => ci && sAv md l) c)) cur (y, b) =
       cur (fun i => if i ∈ ls then xor (y i) (ci && sAv md i) else y i, b) := by
   intro ls
   induction ls with
   | nil => intro _ cur y; simp
   | cons l tl ih =>
     intro hnd cur y
     rw [List.nodup_cons] at hnd
     rw [List.foldl_cons, ih hnd.2]
     dsimp only [applyXorShiftStep, Sum.elim_inl, Sum.elim_inr]
     cases hcl : ci && sAv md l
     · simp only [Bool.false_eq_true, ↓reduceIte]
       congr 1; congr 1; funext i
       by_cases hil : i = l
       · subst hil; simp [hnd.1, hcl]
       · simp [hil]
     · simp only [↓reduceIte]
       congr 1; congr 1; funext i
       unfold flipBit
       by_cases hil : i = l
       · subst hil; simp [hnd.1, hcl]
       · simp [hil]
 have h := hgen (List.finRange D) (List.nodup_finRange D) arr x
 simpa using h
lemma aCut_sp {D m Wbits : ℕ}
   {I I' : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st stNext : BSt D m → Bool}
   {vi : Fin m → ZMod 2} {md : SM D → Bool}
   (hinv : BInv I st) (hinvNext : BInv I' stNext)
   (hrel : SMR I st stNext vi md)
   (ci : Bool) (arr : (Fin D → Bool) × Fin Wbits → Bool)
   (hsupp : ∀ x : Fin D → Bool, ¬ cVal st x → ∀ b : Fin Wbits, arr (x, b) = false) :
   let out := aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) arr))
   (∀ x : Fin D → Bool, ¬ cVal stNext x → ∀ b : Fin Wbits, out (x, b) = false) ∧
   (∀ x : Fin D → Bool, cVal stNext x → ∀ b : Fin Wbits,
     (∀ xp : Fin D → Bool, cVal st xp → bDc st xp + b2z ci • vi = bDc stNext x →
       out (x, b) = arr (xp, b)) ∧
     ((¬ ∃ xp : Fin D → Bool, cVal st xp ∧ bDc st xp + b2z ci • vi = bDc stNext x) →
       out (x, b) = false)) := by
 dsimp only [aCut, Sum.elim_inl, Sum.elim_inr]
 have hrel_cases := hrel
 rcases hrel_cases with
   ⟨hm0, hm1, hm2, hm3, hm4, hst_eq, hav_val, hav_eq⟩ |
   ⟨hm0, hm1, hm2, hm3, hm4, hst_eq, hav0, hviNI⟩ |
   ⟨hm0, hm1, hm2, hm3, hm4, hav0, hviNI, p, hpu, hfp, hslot, hf_val, hused_eq, hp_vec, hother_vec⟩ |
   ⟨hm0, hm1, hm2, hm3, hm4, p, hpu, hfp, hslot, hf_val, hused_eq, hp_vec, hother_vec, hav_val, hav_eq⟩ |
   ⟨hm0, hm1, hm2, hm3, hm4, hav0, hviNI, q0, hqu, hslot, hused_eq, hq_vec, hother_vec⟩
 ·
   subst stNext
   have hout_eq : ∀ x b, aCS3 md ci (aCS2 md ci (aCS1 md arr)) (x, b) =
       arr (fun i => xor (x i) (ci && sAv md i), b) := by
     intro x b
     rw [aCS1_np md hm2 hm3]
     simp only [aCS3, hm0, hm1, hm2, hm3, hm4, Bool.true_and, Bool.false_and, Bool.or_false,
       aCS2_sp]
   refine ⟨?_, ?_⟩
   · intro x hnv b; rw [hout_eq x b]
     apply hsupp _ _ b
     intro hval; apply hnv; intro l hu
     have h1 := hval l hu; have h2 := hav_val l hu
     simp only [h2, Bool.and_false, Bool.xor_false] at h1; exact h1
   · intro x hx b
     let xp : Fin D → Bool := fun i => xor (x i) (ci && sAv md i)
     have hxp_val : cVal st xp := fun l hu => by
       dsimp only [xp]; rw [hx l hu, hav_val l hu]; simp
     have hxp_dec : bDc st xp + b2z ci • vi = bDc st x := by
       funext j
       simp only [bDc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hav_eq]
       rw [Finset.mul_sum, ← Finset.sum_add_distrib]
       apply Finset.sum_congr rfl; intro l _
       simp only [xp, b2z_xor, b2z_and]
       have h2 := zmod2_add_self (b2z ci * b2z (sAv md l) * bVc st l j)
       calc (b2z (x l) + b2z ci * b2z (sAv md l)) * bVc st l j +
             b2z ci * (b2z (sAv md l) * bVc st l j)
           = b2z (x l) * bVc st l j +
               (b2z ci * b2z (sAv md l) * bVc st l j + b2z ci * b2z (sAv md l) * bVc st l j) := by ring
         _ = b2z (x l) * bVc st l j := by rw [h2, add_zero]
     refine ⟨fun xp' hxp' heq => ?_, fun hno => absurd ⟨xp, hxp_val, hxp_dec⟩ hno⟩
     have hsame : xp' = xp := bsDec_inj hinv hxp' hxp_val (by
       have h1 : bDc st xp' + b2z ci • vi = bDc st xp + b2z ci • vi := heq.trans hxp_dec.symm
       exact add_right_cancel h1)
     rw [hout_eq x b, hsame]
 ·
   subst stNext
   have hout_eq : ∀ x b, aCS3 md ci (aCS2 md ci (aCS1 md arr)) (x, b) =
       ((!ci) && arr (x, b)) := by
     intro x b
     rw [aCS1_np md hm2 hm3]
     simp only [aCS3, hm0, hm1, hm2, hm3, hm4, Bool.true_and, Bool.false_and, Bool.or_false,
       Bool.false_or, aCS2_sp]
     congr 1; congr 1; congr 1; funext i; simp [hav0 i]
   refine ⟨fun x hnv b => by rw [hout_eq x b, hsupp x hnv b, Bool.and_false], ?_⟩
   intro x hx b
   rw [hout_eq x b]
   cases ci
   · simp only [Bool.not_false, Bool.true_and, b2z, Bool.false_eq_true, ↓reduceIte, zero_smul, add_zero]
     refine ⟨fun xp hxp heq => ?_, fun hno => absurd ⟨x, hx, rfl⟩ hno⟩
     rw [bsDec_inj hinv hxp hx heq]
   · simp only [Bool.not_true, Bool.false_and, b2z, ↓reduceIte, one_smul]
     refine ⟨fun xp _ heq => ?_, fun _ => trivial⟩
     exfalso; apply hviNI
     have : vi = bDc st xp + bDc st x := by
       funext j; have hj := congrFun heq j; simp only [Pi.add_apply] at hj ⊢
       rw [← hj, ← add_assoc, zmod2_add_self, zero_add]
     rw [this]; exact Submodule.add_mem _ (bsDec_mem hinv xp) (bsDec_mem hinv x)
 ·
   have hstage2_id : ∀ (f0 : (Fin D → Bool) × Fin Wbits → Bool) (x : Fin D → Bool) (b : Fin Wbits),
       aCS2 md ci f0 (x, b) = f0 (x, b) := by
     intro f0 x b; rw [aCS2_sp]; congr 1; congr 1; funext i; simp [hav0 i]
   have hfold_b2z : ∀ y : Fin D → Bool,
       b2z ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && y l)) false) =
         ∑ l : Fin D, if l ≠ p ∧ sFv md l = true then b2z (y l) else 0 := by
     intro y
     rw [foldl_xor_b2z (List.finRange D) (List.nodup_finRange D)]
     rw [show (List.finRange D).toFinset = Finset.univ by ext l; simp]
     apply Finset.sum_congr rfl; intro l _
     by_cases hne : l ≠ p <;> cases sFv md l <;> simp [hne, b2z]
   have hrow_map : ∀ x : Fin D → Bool,
       let xp : Fin D → Bool := fun i =>
         if i = p then xor (x p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && x l)) false)
         else x i
       bDc st xp + b2z (x p) • vi = bDc stNext x := by
     intro x; dsimp only; funext j
     simp only [bDc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
     rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
     simp only [↓reduceIte, b2z_xor, hfold_b2z x]
     rw [show bVc stNext p j = bVc st p j + vi j from congrFun hp_vec j]
     have herase : ∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc stNext l j =
         (∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc st l j) +
         (∑ l : Fin D, if l ≠ p ∧ sFv md l = true then b2z (x l) else 0) * bVc st p j := by
       rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
       simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_mul, zero_add]
       rw [← Finset.sum_add_distrib]
       apply Finset.sum_congr rfl; intro l hl
       have hne : l ≠ p := (Finset.mem_erase.mp hl).1
       rw [show bVc stNext l j = (if sFv md l then bVc st l + bVc st p else bVc st l) j
         from congrFun (hother_vec l hne) j]
       cases sFv md l <;> simp [hne, mul_add]
     rw [herase]
     have herase_l : ∑ l ∈ Finset.univ.erase p,
           b2z (if l = p then xor (x p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && x l)) false) else x l) *
             bVc st l j =
         ∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc st l j := by
       apply Finset.sum_congr rfl; intro l hl
       have hne : l ≠ p := (Finset.mem_erase.mp hl).1; simp [hne]
     rw [herase_l]
     ring
   have hout_eq : ∀ x b, aCS3 md ci (aCS2 md ci (aCS1 md arr)) (x, b) =
       if x p = ci then
         arr (fun i => if i = p then xor (x p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && x l)) false) else x i, b)
       else false := by
     intro x b
     simp only [aCS3, hm0, hm1, hm2, hm3, hm4, Bool.true_and, Bool.false_and, Bool.or_false,
       Bool.false_or, hstage2_id]
     have hex : (∃ p0 : Fin D, sSl md p0 = true ∧ x p0 = ci) ↔ x p = ci := by
       constructor
       · rintro ⟨p0, hp0, heq⟩; rw [hslot p0] at hp0; have heqp := of_decide_eq_true hp0; subst heqp; exact heq
       · intro heq; exact ⟨p, by rw [hslot p]; exact decide_eq_true rfl, heq⟩
     simp only [hex]
     by_cases hxp : x p = ci
     · rw [aCS1_rA md (Or.inl hm2) p hslot arr x b]
       simp only [hxp, decide_true, Bool.true_and, ↓reduceIte]
     · simp [hxp]
   refine ⟨?_, ?_⟩
   · intro x hnv b; rw [hout_eq x b]
     split_ifs
     · apply hsupp _ _ b
       intro hval; apply hnv; intro l hl
       rw [hused_eq l] at hl
       have hne : l ≠ p := fun h => by subst h; rw [hpu] at hl; exact Bool.noConfusion hl
       have := hval l hl; simp [hne] at this; exact this
     · rfl
   · intro x hx b
     rw [hout_eq x b]
     let xp : Fin D → Bool := fun i =>
       if i = p then xor (x p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && x l)) false)
       else x i
     have hxp_val : cVal st xp := fun l hl => by
       have hne : l ≠ p := fun h => by subst h; rw [hpu] at hl; exact Bool.noConfusion hl
       simp only [xp, hne, ↓reduceIte]
       exact hx l (by rw [hused_eq l]; exact hl)
     by_cases hpc : x p = ci
     · simp only [hpc, ↓reduceIte]
       have hdec : bDc st xp + b2z ci • vi = bDc stNext x := by rw [← hpc]; exact hrow_map x
       refine ⟨fun xp' hxp' heq => ?_, fun hno => absurd ⟨xp, hxp_val, hdec⟩ hno⟩
       have hsame : xp' = xp := bsDec_inj hinv hxp' hxp_val (add_right_cancel (heq.trans hdec.symm))
       rw [hsame]; simp only [xp, hpc]
     · simp only [hpc, ↓reduceIte]
       refine ⟨fun xp' _ heq => ?_, fun _ => trivial⟩
       exfalso; apply hviNI
       have hdiff : b2z ci + b2z (x p) = 1 := by
         cases h1 : ci <;> cases h2 : x p <;> simp_all [b2z]
       have hvi_eq : vi = bDc st xp' + bDc st xp := by
         have h1 := hrow_map x
         have h2 : bDc st xp' + b2z ci • vi = bDc st xp + b2z (x p) • vi := heq.trans h1.symm
         funext j
         have hj := congrFun h2 j
         simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
         have hsum := congrArg (fun a => a + bDc st xp j + b2z (x p) * vi j) hj
         have h3 : (b2z ci + b2z (x p)) * vi j = bDc st xp' j + bDc st xp j := by
           calc (b2z ci + b2z (x p)) * vi j
               = (bDc st xp' j + b2z ci * vi j + bDc st xp j + b2z (x p) * vi j) + (bDc st xp' j + bDc st xp j) := by
                 have hza := zmod2_add_self (bDc st xp' j)
                 have hzb := zmod2_add_self (bDc st xp j)
                 calc (b2z ci + b2z (x p)) * vi j
                     = (b2z ci * vi j + b2z (x p) * vi j) + (bDc st xp' j + bDc st xp' j) + (bDc st xp j + bDc st xp j) := by
                       rw [hza, hzb, add_zero, add_zero]; ring
                   _ = _ := by ring
             _ = (bDc st xp j + b2z (x p) * vi j + bDc st xp j + b2z (x p) * vi j) + (bDc st xp' j + bDc st xp j) := by
                 rw [hsum]
             _ = bDc st xp' j + bDc st xp j := by
                 have hza := zmod2_add_self (bDc st xp j)
                 have hzb := zmod2_add_self (b2z (x p) * vi j)
                 calc _ = (bDc st xp j + bDc st xp j) + (b2z (x p) * vi j + b2z (x p) * vi j) + (bDc st xp' j + bDc st xp j) := by ring
                   _ = bDc st xp' j + bDc st xp j := by rw [hza, hzb, zero_add, zero_add]
         rw [hdiff, one_mul] at h3; exact h3
       rw [hvi_eq]; exact Submodule.add_mem _ (bsDec_mem hinv xp') (bsDec_mem hinv xp)
 ·
   have hfold_b2z : ∀ y : Fin D → Bool,
       b2z ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && y l)) false) =
         ∑ l : Fin D, if l ≠ p ∧ sFv md l = true then b2z (y l) else 0 := by
     intro y
     rw [foldl_xor_b2z (List.finRange D) (List.nodup_finRange D)]
     rw [show (List.finRange D).toFinset = Finset.univ by ext l; simp]
     apply Finset.sum_congr rfl; intro l _
     by_cases hne : l ≠ p <;> cases sFv md l <;> simp [hne, b2z]
   have hp_unused : bUs stNext p = false := by rw [hused_eq p]; simp only [↓reduceIte]
   have hav_p : sAv md p = false := hav_val p hp_unused
   have hout_eq : ∀ x b, aCS3 md ci (aCS2 md ci (aCS1 md arr)) (x, b) =
       if x p = false then
         let z : Fin D → Bool := fun i => xor (setBit p ci x i) (ci && sAv md i)
         arr (fun i => if i = p then xor (z p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && z l)) false) else z i, b)
       else false := by
     intro x b
     simp only [aCS3, hm0, hm1, hm2, hm3, hm4, Bool.true_and, Bool.false_and, Bool.or_false,
       Bool.false_or]
     have hex : (∃ p0 : Fin D, sSl md p0 = true ∧ x p0 = false ∧
           aCS2 md ci (aCS1 md arr) (setBit p0 ci x, b) = true) ↔
         (x p = false ∧ aCS2 md ci (aCS1 md arr) (setBit p ci x, b) = true) := by
       constructor
       · rintro ⟨p0, hp0, h1, h2⟩; rw [hslot p0] at hp0; have heqp := of_decide_eq_true hp0; subst heqp; exact ⟨h1, h2⟩
       · rintro ⟨h1, h2⟩; exact ⟨p, by rw [hslot p]; exact decide_eq_true rfl, h1, h2⟩
     simp only [hex]
     by_cases hxp : x p = false
     · simp only [hxp, true_and, ↓reduceIte, Bool.decide_eq_true, aCS2_sp]
       exact aCS1_rA md (Or.inr hm3) p hslot arr _ b
     · simp [hxp]
   refine ⟨?_, ?_⟩
   · intro x hnv b; rw [hout_eq x b]
     split_ifs with hxp
     · apply hsupp _ _ b
       intro hval; apply hnv; intro l hl
       rw [hused_eq l] at hl
       by_cases hlp : l = p
       · subst hlp; exact hxp
       · simp only [hlp, ↓reduceIte] at hl
         have h1 := hval l hl
         have h2 : sAv md l = false := hav_val l (by rw [hused_eq l]; simp only [hlp, ↓reduceIte]; exact hl)
         simp only [hlp, ↓reduceIte, setBit, h2, Bool.and_false, Bool.xor_false] at h1
         exact h1
     · rfl
   · intro x hx b
     have hxp : x p = false := hx p hp_unused
     rw [hout_eq x b]; simp only [hxp, ↓reduceIte]
     let z : Fin D → Bool := fun i => xor (setBit p ci x i) (ci && sAv md i)
     let xp : Fin D → Bool := fun i =>
       if i = p then xor (z p) ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && z l)) false)
       else z i
     have hzp : z p = ci := by simp [z, setBit, hav_p]
     have hxp_val : cVal st xp := fun l hl => by
       have hne : l ≠ p := fun h => by subst h; rw [hpu] at hl; exact Bool.noConfusion hl
       have hl' : bUs stNext l = false := by rw [hused_eq l]; simp only [hne, ↓reduceIte]; exact hl
       simp [xp, hne, z, setBit, hx l hl', hav_val l hl']
     have hxp_dec : bDc st xp + b2z ci • vi = bDc stNext x := by
       funext j
       simp only [bDc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
       rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
       simp only [xp, ↓reduceIte, hzp, b2z_xor, hfold_b2z z]
       rw [show bVc stNext p j = 0 from congrFun hp_vec j, mul_zero, zero_add]
       have hbpv : bVc st p j + vi j = ∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j := by
         have h1 := congrFun hav_eq j
         simp only [bDc, Pi.add_apply] at h1
         rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), show bVc stNext p j = 0 from congrFun hp_vec j,
           mul_zero, zero_add] at h1
         exact h1.symm
       have herase_l : ∑ l ∈ Finset.univ.erase p,
             b2z (if l = p then xor ci ((List.finRange D).foldl (fun acc l => xor acc (sFv md l && decide (l ≠ p) && z l)) false) else z l) *
               bVc st l j =
           ∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc st l j := by
         apply Finset.sum_congr rfl; intro l hl
         have hne : l ≠ p := (Finset.mem_erase.mp hl).1; simp [hne]
       rw [herase_l]
       have hz_sum : ∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc stNext l j =
           (∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc st l j) +
           (∑ l : Fin D, if l ≠ p ∧ sFv md l = true then b2z (z l) else 0) * bVc st p j := by
         rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
         simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_mul, zero_add]
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl; intro l hl
         have hne : l ≠ p := (Finset.mem_erase.mp hl).1
         rw [show bVc stNext l j = (if sFv md l then bVc st l + bVc st p else bVc st l) j
           from congrFun (hother_vec l hne) j]
         cases sFv md l <;> simp [hne, mul_add]
       have hz_x : ∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc stNext l j =
           (∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc stNext l j) +
           b2z ci * (∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j) := by
         rw [Finset.mul_sum, ← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl; intro l hl
         have hne : l ≠ p := (Finset.mem_erase.mp hl).1
         simp only [z, setBit, hne, ↓reduceIte, b2z_xor, b2z_and]
         ring
       have hstep : (b2z ci + ∑ l : Fin D, if l ≠ p ∧ sFv md l = true then b2z (z l) else 0) * bVc st p j +
             (∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc st l j) + b2z ci * vi j =
           b2z ci * (bVc st p j + vi j) + (∑ l ∈ Finset.univ.erase p, b2z (z l) * bVc stNext l j) := by
         rw [hz_sum]; ring
       rw [hstep, hz_x, hbpv]
       have h2 := zmod2_add_self (b2z ci * ∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j)
       calc b2z ci * (∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j) +
             ((∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc stNext l j) +
               b2z ci * (∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j))
           = (∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc stNext l j) +
               (b2z ci * (∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j) +
                b2z ci * (∑ l ∈ Finset.univ.erase p, b2z (sAv md l) * bVc stNext l j)) := by ring
         _ = ∑ l ∈ Finset.univ.erase p, b2z (x l) * bVc stNext l j := by rw [h2, add_zero]
     refine ⟨fun xp' hxp' heq => ?_, fun hno => absurd ⟨xp, hxp_val, hxp_dec⟩ hno⟩
     have hsame : xp' = xp := bsDec_inj hinv hxp' hxp_val (add_right_cancel (heq.trans hxp_dec.symm))
     rw [hsame]
 ·
   have hstage2_id : ∀ (f0 : (Fin D → Bool) × Fin Wbits → Bool) (x : Fin D → Bool) (b : Fin Wbits),
       aCS2 md ci f0 (x, b) = f0 (x, b) := by
     intro f0 x b; rw [aCS2_sp]; congr 1; congr 1; funext i; simp [hav0 i]
   have hout_eq : ∀ x b, aCS3 md ci (aCS2 md ci (aCS1 md arr)) (x, b) =
       if x q0 = ci then arr (setBit q0 false x, b) else false := by
     intro x b
     rw [aCS1_np md hm2 hm3]
     simp only [aCS3, hm0, hm1, hm2, hm3, hm4, Bool.true_and, Bool.false_and, Bool.or_false,
       Bool.false_or, hstage2_id]
     have hex : (∃ q : Fin D, sSl md q = true ∧ x q = ci ∧ arr (setBit q false x, b) = true) ↔
         (x q0 = ci ∧ arr (setBit q0 false x, b) = true) := by
       constructor
       · rintro ⟨q, hq, h1, h2⟩; rw [hslot q] at hq; have heqq := of_decide_eq_true hq; subst heqq; exact ⟨h1, h2⟩
       · rintro ⟨h1, h2⟩; exact ⟨q0, by rw [hslot q0]; exact decide_eq_true rfl, h1, h2⟩
     simp only [hex]
     by_cases hxq : x q0 = ci
     · simp [hxq]
     · simp [hxq]
   have hsplit_dec : ∀ x : Fin D → Bool,
       bDc stNext x = b2z (x q0) • vi + bDc st (setBit q0 false x) := by
     intro x; funext j
     simp only [bDc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
     rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q0), ← Finset.add_sum_erase _ _ (Finset.mem_univ q0)]
     simp only [setBit, ↓reduceIte, b2z, Bool.false_eq_true, zero_mul, zero_add]
     rw [show bVc stNext q0 j = vi j from congrFun hq_vec j]
     congr 1
     apply Finset.sum_congr rfl; intro l hl
     have hne : l ≠ q0 := (Finset.mem_erase.mp hl).1
     simp only [hne, ↓reduceIte]
     rw [show bVc stNext l j = bVc st l j from congrFun (hother_vec l hne) j]
   refine ⟨?_, ?_⟩
   · intro x hnv b; rw [hout_eq x b]
     split_ifs
     · apply hsupp _ _ b
       intro hval; apply hnv; intro l hl
       rw [hused_eq l] at hl
       have hne : l ≠ q0 := fun h => by simp [h] at hl
       simp only [hne, ↓reduceIte] at hl
       have := hval l hl; simp [setBit, hne] at this; exact this
     · rfl
   · intro x hx b
     rw [hout_eq x b]
     let xp : Fin D → Bool := setBit q0 false x
     have hxp_val : cVal st xp := fun l hl => by
       by_cases hne : l = q0
       · subst hne; simp [xp, setBit]
       · simp only [xp, setBit, hne, ↓reduceIte]
         exact hx l (by rw [hused_eq l]; simp only [hne, ↓reduceIte]; exact hl)
     by_cases hqc : x q0 = ci
     · simp only [hqc, ↓reduceIte]
       have hdec : bDc st xp + b2z ci • vi = bDc stNext x := by
         rw [hsplit_dec x, hqc, add_comm]
       refine ⟨fun xp' hxp' heq => ?_, fun hno => absurd ⟨xp, hxp_val, hdec⟩ hno⟩
       have hsame : xp' = xp := bsDec_inj hinv hxp' hxp_val (add_right_cancel (heq.trans hdec.symm))
       rw [hsame]
     · simp only [hqc, ↓reduceIte]
       refine ⟨fun xp' _ heq => ?_, fun _ => trivial⟩
       exfalso; apply hviNI
       have hdiff : b2z ci + b2z (x q0) = 1 := by
         cases h1 : ci <;> cases h2 : x q0 <;> simp_all [b2z]
       have hvi_eq : vi = bDc st xp' + bDc st xp := by
         have h2 : bDc st xp' + b2z ci • vi = bDc st xp + b2z (x q0) • vi := by
           rw [heq, hsplit_dec x, add_comm]
         funext j
         have hj := congrFun h2 j
         simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
         have hsum := congrArg (fun a => a + bDc st xp j + b2z (x q0) * vi j) hj
         have h3 : (b2z ci + b2z (x q0)) * vi j = bDc st xp' j + bDc st xp j := by
           calc (b2z ci + b2z (x q0)) * vi j
               = (bDc st xp' j + b2z ci * vi j + bDc st xp j + b2z (x q0) * vi j) + (bDc st xp' j + bDc st xp j) := by
                 have hza := zmod2_add_self (bDc st xp' j)
                 have hzb := zmod2_add_self (bDc st xp j)
                 calc (b2z ci + b2z (x q0)) * vi j
                     = (b2z ci * vi j + b2z (x q0) * vi j) + (bDc st xp' j + bDc st xp' j) + (bDc st xp j + bDc st xp j) := by
                       rw [hza, hzb, add_zero, add_zero]; ring
                   _ = _ := by ring
             _ = (bDc st xp j + b2z (x q0) * vi j + bDc st xp j + b2z (x q0) * vi j) + (bDc st xp' j + bDc st xp j) := by
                 rw [hsum]
             _ = bDc st xp' j + bDc st xp j := by
                 have hza := zmod2_add_self (bDc st xp j)
                 have hzb := zmod2_add_self (b2z (x q0) * vi j)
                 calc _ = (bDc st xp j + bDc st xp j) + (b2z (x q0) * vi j + b2z (x q0) * vi j) + (bDc st xp' j + bDc st xp j) := by ring
                   _ = bDc st xp' j + bDc st xp j := by rw [hza, hzb, zero_add, zero_add]
         rw [hdiff, one_mul] at h3; exact h3
       rw [hvi_eq]; exact Submodule.add_mem _ (bsDec_mem hinv xp') (bsDec_mem hinv xp)
abbrev RIn (n e s r : ℕ) :=
 (Fin e × Bool × Fin (n + 1)) ⊕
 Fin (3 * (e + 1) * s) ⊕
 Fin (3 * (e + 1) * s) ⊕
 (Fin r × Fin (3 * (e + 1) * s)) ⊕
 (Fin r × Fin (3 * (e + 1) * s)) ⊕
 Fin (3 * (e + 1) * s) ⊕
 Fin (3 * (e + 1)) ⊕
 Fin (2 * n + 1) ⊕
 Fin (3 * (e + 1) * s + 1) ⊕
 Fin (3 * (e + 1) * s + 1)
def rEdg {n e s r : ℕ} (raw : RIn n e s r → Bool) (ei : Fin e) (side : Bool) (b : Fin (n + 1)) : Bool :=
 raw (inl (ei, side, b))
def rNr {n e s r : ℕ} (raw : RIn n e s r → Bool) (p : Fin (3 * (e + 1) * s)) : Bool :=
 raw (inr (inl p))
def rNc {n e s r : ℕ} (raw : RIn n e s r → Bool) (p : Fin (3 * (e + 1) * s)) : Bool :=
 raw (inr (inr (inl p)))
def rCr {n e s r : ℕ} (raw : RIn n e s r → Bool) (ri : Fin r) (p : Fin (3 * (e + 1) * s)) : Bool :=
 raw (inr (inr (inr (inl (ri, p)))))
def rCc {n e s r : ℕ} (raw : RIn n e s r → Bool) (ci : Fin r) (p : Fin (3 * (e + 1) * s)) : Bool :=
 raw (inr (inr (inr (inr (inl (ci, p))))))
def rOff {n e s r : ℕ} (raw : RIn n e s r → Bool) (p : Fin (3 * (e + 1) * s)) : Bool :=
 raw (inr (inr (inr (inr (inr (inl p))))))
def rBnk {n e s r : ℕ} (raw : RIn n e s r → Bool) (i : Fin (3 * (e + 1))) : Bool :=
 raw (inr (inr (inr (inr (inr (inr (inl i)))))))
def rY {n e s r : ℕ} (raw : RIn n e s r → Bool) (b : Fin (2 * n + 1)) : Bool :=
 raw (inr (inr (inr (inr (inr (inr (inr (inl b))))))))
def rT {n e s r : ℕ} (raw : RIn n e s r → Bool) (b : Fin (3 * (e + 1) * s + 1)) : Bool :=
 raw (inr (inr (inr (inr (inr (inr (inr (inr (inl b)))))))))
def rJ {n e s r : ℕ} (raw : RIn n e s r → Bool) (b : Fin (3 * (e + 1) * s + 1)) : Bool :=
 raw (inr (inr (inr (inr (inr (inr (inr (inr (inr b)))))))))
def eCB (L val : ℕ) (x : Fin L → Bool) (_ : Unit) : Bool :=
 decide (∀ b : Fin L, x b = val.testBit b.val)
lemma eCB_sp (L val : ℕ) (x : Fin L → Bool) (v : ℕ) (hv : v < 2 ^ L) (hval : val < 2 ^ L)
   (hx : ∀ b : Fin L, x b = v.testBit b.val) :
   eCB L val x () = decide (v = val) := by
 unfold eCB
 simp only [decide_eq_decide]
 constructor
 · intro hall
   apply Nat.eq_of_testBit_eq; intro i
   by_cases hi : i < L
   · rw [← hx ⟨i, hi⟩]; exact hall ⟨i, hi⟩
   · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))),
       Nat.testBit_lt_two_pow (lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega)))]
 · intro heq b; rw [hx b, heq]
lemma ec_eCB (L val : ℕ) : EC (8 * L + 10) (eCB L val) := by
 have hbit : EC (5 * L + 2)
     (fun (x : Fin L → Bool) (b : Fin L) => if val.testBit b.val then x b else !(x b)) := by
   have h := ec_ite_of (ec_const (ι := Fin L) (fun b : Fin L => val.testBit b.val))
     (ec_id (ι := Fin L)) (ec_not_of (ec_id (ι := Fin L)))
   rw [Fintype.card_fin] at h; exact ec_le h (by omega)
 have hall := ec_comp hbit (ec_all (α := Fin L))
 rw [Fintype.card_fin] at hall
 refine ec_le (ec_eq ?_ hall) (by omega)
 intro x u; unfold eCB; simp only [decide_eq_decide]
 apply forall_congr'; intro b
 cases val.testBit b.val <;> cases x b <;> simp
def buildP (n e s r : ℕ) (raw : RIn n e s r → Bool) (p : Fin (3 * (e + 1)) × Fin (2 * n + 1)) : Bool :=
 let i := p.1
 let bit := p.2
 if h0 : i.val < 3 then decide (bit.val = 0)
 else
   let ei : Fin e := ⟨i.val / 3 - 1, by have := i.isLt; omega⟩
   if i.val % 3 = 0 then
     if bit.val = 0 then false
     else if bit.val % 2 = 1 then
       let vval := (bit.val - 1) / 2 + 1
       xor (eCB (n + 1) vval (fun b => rEdg raw ei false b) ())
           (eCB (n + 1) vval (fun b => rEdg raw ei true b) ())
     else false
   else if i.val % 3 = 1 then
     if bit.val = 0 then false
     else if bit.val % 2 = 0 then
       let vval := bit.val / 2
       xor (eCB (n + 1) vval (fun b => rEdg raw ei false b) ())
           (eCB (n + 1) vval (fun b => rEdg raw ei true b) ())
     else false
   else decide (bit.val = 0)
lemma ec_buildP (n e s r : ℕ) :
   EC (3 * (e + 1) * (2 * n + 1) * (20 * n + 50)) (buildP n e s r) := by
 let I := RIn n e s r
 have hfam := ec_family (s := 20 * n + 50)
   (f := fun (p : Fin (3 * (e + 1)) × Fin (2 * n + 1)) (raw : I → Bool) (_ : Unit) =>
     buildP n e s r raw p)
   (fun p => by
     dsimp only [buildP]
     by_cases h0 : p.1.val < 3
     · simp only [h0, ↓reduceDIte]
       exact ec_le (ec_const (fun _ => decide (p.2.val = 0))) (by omega)
     · simp only [h0, ↓reduceDIte]
       let ei : Fin e := ⟨p.1.val / 3 - 1, by have := p.1.isLt; omega⟩
       by_cases hm0 : p.1.val % 3 = 0
       · simp only [hm0, ↓reduceIte]
         by_cases hb0 : p.2.val = 0
         · simp only [hb0, ↓reduceIte]; exact ec_le (ec_const (fun _ => false)) (by omega)
         · by_cases hodd : p.2.val % 2 = 1
           · simp only [hb0, hodd, ↓reduceIte]
             have h1 := ec_comp (ec_proj (fun b : Fin (n + 1) => (inl (ei, false, b) : I)))
               (ec_eCB (n + 1) ((p.2.val - 1) / 2 + 1))
             have h2 := ec_comp (ec_proj (fun b : Fin (n + 1) => (inl (ei, true, b) : I)))
               (ec_eCB (n + 1) ((p.2.val - 1) / 2 + 1))
             have hx := ec_xor_of h1 h2
             rw [Fintype.card_unit] at hx; exact ec_le hx (by omega)
           · simp only [hb0, hodd, ↓reduceIte]; exact ec_le (ec_const (fun _ => false)) (by omega)
       · by_cases hm1 : p.1.val % 3 = 1
         · simp only [hm0, ↓reduceIte]
           simp only [hm1, ↓reduceIte]
           by_cases hb0 : p.2.val = 0
           · simp only [hb0, ↓reduceIte]; exact ec_le (ec_const (fun _ => false)) (by omega)
           · by_cases hev : p.2.val % 2 = 0
             · simp only [hb0, hev, ↓reduceIte]
               have h1 := ec_comp (ec_proj (fun b : Fin (n + 1) => (inl (ei, false, b) : I)))
                 (ec_eCB (n + 1) (p.2.val / 2))
               have h2 := ec_comp (ec_proj (fun b : Fin (n + 1) => (inl (ei, true, b) : I)))
                 (ec_eCB (n + 1) (p.2.val / 2))
               have hx := ec_xor_of h1 h2
               rw [Fintype.card_unit] at hx; exact ec_le hx (by omega)
             · simp only [hb0, hev, ↓reduceIte]; exact ec_le (ec_const (fun _ => false)) (by omega)
         · simp only [hm0, hm1, ↓reduceIte]
           exact ec_le (ec_const (fun _ => decide (p.2.val = 0))) (by omega))
 simp only [Fintype.card_prod, Fintype.card_fin] at hfam
 have hp := ec_comp hfam (ec_proj (fun p : Fin (3 * (e + 1)) × Fin (2 * n + 1) => (p, ())))
 rw [add_zero] at hp; exact hp
lemma buildP_spec {n e s r : ℕ} (edges : Fin e → Fin (n + 1) × Fin (n + 1))
   (raw : RIn n e s r → Bool)
   (hG : ∀ (ei : Fin e) (b : Fin (n + 1)),
     rEdg raw ei false b = (edges ei).1.val.testBit b.val ∧
     rEdg raw ei true b = (edges ei).2.val.testBit b.val)
   (i : Fin (3 * (e + 1))) (bit : Fin (2 * n + 1)) :
   buildP n e s r raw (i, bit) =
     ((makeP (List.ofFn edges))[i.val]?.getD 0).testBit bit.val := by
 have hlen : (makeP (List.ofFn edges)).length = 3 * (e + 1) := by
   rw [makeP_length, List.length_ofFn]
 have hget : (makeP (List.ofFn edges))[i.val]?.getD 0 =
     (makeP (List.ofFn edges))[i.val]'(by rw [hlen]; exact i.isLt) := by
   rw [List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt)]; rfl
 rw [hget, makeP_getElem (List.ofFn edges) i.val (by rw [List.length_ofFn]; exact i.isLt)]
 have hpow : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
 unfold buildP
 by_cases h0 : i.val < 3
 · simp only [h0, ↓reduceDIte]
   by_cases hb0 : bit.val = 0
   · rw [hb0]; decide
   · rw [decide_eq_false hb0]
     symm; apply Nat.testBit_lt_two_pow
     calc (1 : ℕ) < 2 ^ 1 := by omega
       _ ≤ 2 ^ bit.val := Nat.pow_le_pow_right (by omega) (by omega)
 · simp only [h0, ↓reduceDIte]
   let ei : Fin e := ⟨i.val / 3 - 1, by have := i.isLt; omega⟩
   have hEei : (List.ofFn edges)[i.val / 3 - 1]'(by rw [List.length_ofFn]; exact ei.isLt) = edges ei := by
     simp [ei]
   rw [hEei]
   by_cases hm0 : i.val % 3 = 0
   · simp only [hm0, ↓reduceIte, Nat.testBit_xor, testBit_loVal]
     by_cases hb0 : bit.val = 0
     · simp only [hb0, ↓reduceIte]
       have h1 : ¬ ((edges ei).1.val ≠ 0 ∧ 0 = 2 * (edges ei).1.val - 1) := by omega
       have h2 : ¬ ((edges ei).2.val ≠ 0 ∧ 0 = 2 * (edges ei).2.val - 1) := by omega
       rw [decide_eq_false h1, decide_eq_false h2]; rfl
     · by_cases hodd : bit.val % 2 = 1
       · simp only [hb0, hodd, ↓reduceIte]
         let vval := (bit.val - 1) / 2 + 1
         have hvlt : vval < 2 ^ (n + 1) := by have := bit.isLt; omega
         have heq1 := eCB_sp (n + 1) vval (fun b => rEdg raw ei false b)
           (edges ei).1.val (lt_trans (edges ei).1.isLt hpow) hvlt (fun b => (hG ei b).1)
         have heq2 := eCB_sp (n + 1) vval (fun b => rEdg raw ei true b)
           (edges ei).2.val (lt_trans (edges ei).2.isLt hpow) hvlt (fun b => (hG ei b).2)
         rw [heq1, heq2]
         have hiff1 : ((edges ei).1.val = vval) ↔ ((edges ei).1.val ≠ 0 ∧ bit.val = 2 * (edges ei).1.val - 1) := by
           dsimp [vval]; omega
         have hiff2 : ((edges ei).2.val = vval) ↔ ((edges ei).2.val ≠ 0 ∧ bit.val = 2 * (edges ei).2.val - 1) := by
           dsimp [vval]; omega
         rw [decide_eq_decide.mpr hiff1, decide_eq_decide.mpr hiff2]
       · simp only [hb0, hodd, ↓reduceIte]
         have h1 : ¬ ((edges ei).1.val ≠ 0 ∧ bit.val = 2 * (edges ei).1.val - 1) := by omega
         have h2 : ¬ ((edges ei).2.val ≠ 0 ∧ bit.val = 2 * (edges ei).2.val - 1) := by omega
         rw [decide_eq_false h1, decide_eq_false h2]; rfl
   · by_cases hm1 : i.val % 3 = 1
     · simp only [hm0, ↓reduceIte]
       simp only [hm1, ↓reduceIte, Nat.testBit_xor, testBit_hiVal]
       by_cases hb0 : bit.val = 0
       · simp only [hb0, ↓reduceIte]
         have h1 : ¬ ((edges ei).1.val ≠ 0 ∧ 0 = 2 * (edges ei).1.val) := by omega
         have h2 : ¬ ((edges ei).2.val ≠ 0 ∧ 0 = 2 * (edges ei).2.val) := by omega
         rw [decide_eq_false h1, decide_eq_false h2]; rfl
       · by_cases hev : bit.val % 2 = 0
         · simp only [hb0, hev, ↓reduceIte]
           let vval := bit.val / 2
           have hvlt : vval < 2 ^ (n + 1) := by have := bit.isLt; omega
           have heq1 := eCB_sp (n + 1) vval (fun b => rEdg raw ei false b)
             (edges ei).1.val (lt_trans (edges ei).1.isLt hpow) hvlt (fun b => (hG ei b).1)
           have heq2 := eCB_sp (n + 1) vval (fun b => rEdg raw ei true b)
             (edges ei).2.val (lt_trans (edges ei).2.isLt hpow) hvlt (fun b => (hG ei b).2)
           rw [heq1, heq2]
           have hiff1 : ((edges ei).1.val = vval) ↔ ((edges ei).1.val ≠ 0 ∧ bit.val = 2 * (edges ei).1.val) := by
             dsimp [vval]; omega
           have hiff2 : ((edges ei).2.val = vval) ↔ ((edges ei).2.val ≠ 0 ∧ bit.val = 2 * (edges ei).2.val) := by
             dsimp [vval]; omega
           rw [decide_eq_decide.mpr hiff1, decide_eq_decide.mpr hiff2]
         · simp only [hb0, hev, ↓reduceIte]
           have h1 : ¬ ((edges ei).1.val ≠ 0 ∧ bit.val = 2 * (edges ei).1.val) := by omega
           have h2 : ¬ ((edges ei).2.val ≠ 0 ∧ bit.val = 2 * (edges ei).2.val) := by omega
           rw [decide_eq_false h1, decide_eq_false h2]; rfl
     · simp only [hm0, hm1, ↓reduceIte]
       by_cases hb0 : bit.val = 0
       · rw [hb0]; decide
       · rw [decide_eq_false hb0]
         symm; apply Nat.testBit_lt_two_pow
         calc (1 : ℕ) < 2 ^ 1 := by omega
           _ ≤ 2 ^ bit.val := Nat.pow_le_pow_right (by omega) (by omega)
abbrev FOut (e s d a : ℕ) :=
 Unit ⊕
 Fin (3 * (e + 1)) ⊕
 (Fin (3 * (e + 1)) × SM (1 + 2 * a)) ⊕
 (Fin (3 * (e + 1)) × (Fin (d + 1 - s) → Bool) × (Fin s → Bool)) ⊕
 Fin (3 * (e + 1) * s)
def rBC (q D m : ℕ)
   (inp : (Fin q × Fin m) ⊕ (Fin q × Fin m × Fin m) → Bool) :
   BSt D m ⊕ (Fin q × SM D) → Bool :=
 let Pmat : Fin q → Fin m → Bool := fun i j => inp (inl (i, j))
 let Nall : Fin q → Fin m × Fin m → Bool := fun i p => inp (inr (i, p))
 (List.finRange q).foldl
   (fun acc i =>
     let st : BSt D m → Bool := fun a => acc (inl a)
     let mds : Fin q × SM D → Bool := fun p => acc (inr p)
     let res := stB D m (Sum.elim st (Sum.elim (Nall i) (Pmat i)))
     Sum.elim (fun a => res (inl a))
       (fun p => if p.1 = i then res (inr p.2) else mds p))
   (fun _ => false)
lemma ec_rBC (q D m : ℕ) :
   EC (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3))) (rBC q D m) := by
 let I := (Fin q × Fin m) ⊕ (Fin q × Fin m × Fin m)
 let A := BSt D m ⊕ (Fin q × SM D)
 have htake : ∀ t : ℕ,
     EC (2 + t * (600 * (D + 1) * (m + 1) * (m + D + 3)))
       (fun (inp : I → Bool) =>
         ((List.finRange q).take t).foldl
           (fun acc i =>
             let st : BSt D m → Bool := fun a => acc (inl a)
             let mds : Fin q × SM D → Bool := fun p => acc (inr p)
             let res := stB D m (Sum.elim st (Sum.elim (fun p => inp (inr (i, p))) (fun j => inp (inl (i, j)))))
             Sum.elim (fun a => res (inl a))
               (fun p => if p.1 = i then res (inr p.2) else mds p))
           (fun _ => false)) := by
   intro t
   induction t with
   | zero => simpa using ec_const (ι := I) (fun (_ : A) => false)
   | succ t ih =>
     by_cases ht : t < q
     · let ii : Fin q := ⟨t, ht⟩
       let selStep : (BSt D m ⊕ (Fin m × Fin m) ⊕ Fin m) → I ⊕ A := fun q0 =>
         match q0 with
         | inl a => inr (inl a)
         | inr (inl p) => inl (inr (ii, p))
         | inr (inr j) => inl (inl (ii, j))
       have hsb := ec_comp (ec_proj selStep) (ec_stB D m)
       rw [zero_add] at hsb
       let selOut : A → (I ⊕ A) ⊕ (BSt D m ⊕ SM D) := fun q0 =>
         match q0 with
         | inl a => inr (inl a)
         | inr p => if p.1 = ii then inr (inr p.2) else inl (inr (inr p))
       have hstep := ec_let hsb (ec_proj selOut)
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) (by nlinarith)
       intro inp a
       have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t ++ [ii] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange q) (i := t) (by simp; omega)
         simpa [ii] using h1
       simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
       rcases a with b | ⟨i0, m0⟩
       · dsimp only [selOut, Sum.elim_inl, Sum.elim_inr]
         congr 1; funext q0; rcases q0 with _ | _ | _ <;> rfl
       · dsimp only [selOut, Sum.elim_inl, Sum.elim_inr]
         by_cases heq : i0 = ii
         · simp only [heq, ↓reduceIte, Sum.elim_inr]
           congr 1; funext q0; rcases q0 with _ | _ | _ <;> rfl
         · simp only [heq, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
     · have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t := by
         rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
       refine ec_le (ec_eq ?_ ih) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ t)) 2)
       intro inp a; simp only [htk]
 have h := htake q
 rwa [show (List.finRange q).take q = List.finRange q by rw [List.take_of_length_le]; simp] at h
def pOE (k r s d : ℕ) (hk : 0 < k) (hs : s ≤ d + 1)
   (i_val : ℕ) (win : Fin (d + 1 - s) → Bool) (nxt : Fin s → Bool)
   (inp : Fin k ⊕ Fin k ⊕ Fin k ⊕ (Fin r × Fin k) ⊕ (Fin r × Fin k) ⊕ Unit → Bool) (_ : Unit) : Bool :=
 let eqOff : Fin k → Bool := fun o => inp (inl o)
 let nr : Fin k → Bool := fun p => inp (inr (inl p))
 let nc : Fin k → Bool := fun p => inp (inr (inr (inl p)))
 let cr : Fin r × Fin k → Bool := fun p => inp (inr (inr (inr (inl p))))
 let cc : Fin r × Fin k → Bool := fun p => inp (inr (inr (inr (inr (inl p)))))
 let bank_i : Bool := inp (inr (inr (inr (inr (inr ())))))
 let wnBit : Fin (d + 1) → Bool := fun δ =>
   if h : δ.val < d + 1 - s then win ⟨δ.val, h⟩ else nxt ⟨δ.val - (d + 1 - s), by omega⟩
 let wPad : Fin k → Bool := fun pos =>
   decide (∃ o : Fin k, eqOff o = true ∧
     decide (∃ δ : Fin (d + 1), (o.val + i_val * s + δ.val) % k = pos.val ∧ wnBit δ = true) = true)
 let stF := stateB k r hk false (Sum.elim wPad (Sum.elim nr cr))
 let stT := stateB k r hk true (Sum.elim wPad (Sum.elim nc cc))
 let outF := decide (∃ o : Fin k, eqOff o = true ∧
   stF ⟨((o.val + i_val * s) % k + delayN r false) % k, Nat.mod_lt _ hk⟩ = true)
 let outT := decide (∃ o : Fin k, eqOff o = true ∧
   stT ⟨((o.val + i_val * s) % k + delayN r true) % k, Nat.mod_lt _ hk⟩ = true)
 if bank_i then outT else outF
lemma ec_pOE (k r s d : ℕ) (hk : 0 < k) (hs : s ≤ d + 1)
   (i_val : ℕ) (win : Fin (d + 1 - s) → Bool) (nxt : Fin s → Bool) :
   EC (100 * (k + 1) * (k + r + 2)) (pOE k r s d hk hs i_val win nxt) := by
 let I := Fin k ⊕ Fin k ⊕ Fin k ⊕ (Fin r × Fin k) ⊕ (Fin r × Fin k) ⊕ Unit
 let wnBit : Fin (d + 1) → Bool := fun δ =>
   if h : δ.val < d + 1 - s then win ⟨δ.val, h⟩ else nxt ⟨δ.val - (d + 1 - s), by omega⟩
 have hwPad : EC (k * (3 * k + 5))
     (fun (inp : I → Bool) (pos : Fin k) =>
       decide (∃ o : Fin k, inp (inl o) = true ∧
         decide (∃ δ : Fin (d + 1), (o.val + i_val * s + δ.val) % k = pos.val ∧ wnBit δ = true) = true)) := by
   have hfam := ec_family (s := 3 * k + 5)
     (f := fun (pos : Fin k) (inp : I → Bool) (_ : Unit) =>
       decide (∃ o : Fin k, inp (inl o) = true ∧
         decide (∃ δ : Fin (d + 1), (o.val + i_val * s + δ.val) % k = pos.val ∧ wnBit δ = true) = true))
     (fun pos => by
       have hc := ec_const (ι := I) (fun o : Fin k =>
         decide (∃ δ : Fin (d + 1), (o.val + i_val * s + δ.val) % k = pos.val ∧ wnBit δ = true))
       have hand := ec_and_of (ec_proj (fun o : Fin k => (inl o : I))) hc
       have hany := ec_comp hand (ec_any (α := Fin k))
       rw [Fintype.card_fin] at hany
       exact ec_le (ec_eq (fun inp u => by simp [Bool.and_eq_true]) hany) (by omega))
   rw [Fintype.card_fin] at hfam
   have hp := ec_comp hfam (ec_proj (fun pos : Fin k => (pos, ())))
   rw [add_zero] at hp; exact hp
 let I1 := I ⊕ Fin k
 have hst : EC (80 * (r + 1) * k)
     (fun (y : I1 → Bool) =>
       let wPad := fun pos => y (inr pos)
       Sum.elim
         (stateB k r hk false (Sum.elim wPad (Sum.elim (fun p => y (inl (inr (inl p))))
           (fun p => y (inl (inr (inr (inr (inl p)))))))))
         (stateB k r hk true (Sum.elim wPad (Sum.elim (fun p => y (inl (inr (inr (inl p)))))
           (fun p => y (inl (inr (inr (inr (inr (inl p))))))))))) := by
   let selF : (Fin k ⊕ Fin k ⊕ (Fin r × Fin k)) → I1 :=
     Sum.elim (fun pos => inr pos) (Sum.elim (fun p => inl (inr (inl p)))
       (fun p => inl (inr (inr (inr (inl p))))))
   let selT : (Fin k ⊕ Fin k ⊕ (Fin r × Fin k)) → I1 :=
     Sum.elim (fun pos => inr pos) (Sum.elim (fun p => inl (inr (inr (inl p))))
       (fun p => inl (inr (inr (inr (inr (inl p)))))))
   have hF := ec_comp (ec_proj selF) (ec_stateB k r hk false)
   have hT := ec_comp (ec_proj selT) (ec_stateB k r hk true)
   rw [zero_add] at hF hT
   refine ec_le (ec_eq ?_ (ec_pair hF hT)) (by nlinarith)
   intro y q; rcases q with p | p
   · change stateB k r hk false (fun r => y (selF r)) p = _
     congr 1; funext r; rcases r with _ | _ | _ <;> rfl
   · change stateB k r hk true (fun r => y (selT r)) p = _
     congr 1; funext r; rcases r with _ | _ | _ <;> rfl
 let I2 := I1 ⊕ (Fin k ⊕ Fin k)
 have hout : EC (6 * k + 15)
     (fun (z : I2 → Bool) (_ : Unit) =>
       let outF := decide (∃ o : Fin k, z (inl (inl (inl o))) = true ∧
         z (inr (inl ⟨((o.val + i_val * s) % k + delayN r false) % k, Nat.mod_lt _ hk⟩)) = true)
       let outT := decide (∃ o : Fin k, z (inl (inl (inl o))) = true ∧
         z (inr (inr ⟨((o.val + i_val * s) % k + delayN r true) % k, Nat.mod_lt _ hk⟩)) = true)
       if z (inl (inl (inr (inr (inr (inr (inr ()))))))) then outT else outF) := by
   have hF : EC (3 * k + 3)
       (fun (z : I2 → Bool) (_ : Unit) =>
         decide (∃ o : Fin k, z (inl (inl (inl o))) = true ∧
           z (inr (inl ⟨((o.val + i_val * s) % k + delayN r false) % k, Nat.mod_lt _ hk⟩)) = true)) := by
     have hand := ec_and_of (ec_proj (fun o : Fin k => (inl (inl (inl o)) : I2)))
       (ec_proj (fun o : Fin k => (inr (inl ⟨((o.val + i_val * s) % k + delayN r false) % k, Nat.mod_lt _ hk⟩) : I2)))
     have hany := ec_comp hand (ec_any (α := Fin k))
     rw [Fintype.card_fin] at hany
     exact ec_le (ec_eq (fun z u => by simp [Bool.and_eq_true]) hany) (by omega)
   have hT : EC (3 * k + 3)
       (fun (z : I2 → Bool) (_ : Unit) =>
         decide (∃ o : Fin k, z (inl (inl (inl o))) = true ∧
           z (inr (inr ⟨((o.val + i_val * s) % k + delayN r true) % k, Nat.mod_lt _ hk⟩)) = true)) := by
     have hand := ec_and_of (ec_proj (fun o : Fin k => (inl (inl (inl o)) : I2)))
       (ec_proj (fun o : Fin k => (inr (inr ⟨((o.val + i_val * s) % k + delayN r true) % k, Nat.mod_lt _ hk⟩) : I2)))
     have hany := ec_comp hand (ec_any (α := Fin k))
     rw [Fintype.card_fin] at hany
     exact ec_le (ec_eq (fun z u => by simp [Bool.and_eq_true]) hany) (by omega)
   have hite := ec_ite_of (ec_proj (fun (_ : Unit) =>
     (inl (inl (inr (inr (inr (inr (inr ())))))) : I2))) hT hF
   rw [Fintype.card_unit] at hite
   exact ec_le hite (by omega)
 have htot := ec_let hwPad (ec_let hst hout)
 refine ec_le (ec_eq ?_ htot) (by nlinarith)
 intro inp u; rfl
lemma pOE_sp {k r s d : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (hs : s ≤ d + 1)
   (hd_lt : d < k) (hk3 : 2 < k)
   (i_val : ℕ) (off : Fin k) (bank_i : Bool) (hreach : reachN r bank_i ≤ d)
   (nr nc : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
   (w : Fin (2 ^ k)) (win : Fin (d + 1 - s) → Bool) (nxt : Fin s → Bool)
   (hwin : ∀ u : Fin (d + 1 - s), win u = w.val.testBit ((off.val + i_val * s + u.val) % k))
   (hnxt : ∀ u : Fin s, nxt u = w.val.testBit ((off.val + i_val * s + (d + 1 - s) + u.val) % k)) :
   let eqOff : Fin k → Bool := fun o => decide (o = off)
   let nrB : Fin k → Bool := fun p => nr.val.testBit p.val
   let ncB : Fin k → Bool := fun p => nc.val.testBit p.val
   let crB : Fin r × Fin k → Bool := fun p => (cr p.1).val.testBit p.2.val
   let ccB : Fin r × Fin k → Bool := fun p => (cc p.1).val.testBit p.2.val
   pOE k r s d hk hs i_val win nxt
     (Sum.elim eqOff (Sum.elim nrB (Sum.elim ncB (Sum.elim crB (Sum.elim ccB (fun _ => bank_i)))))) () =
   (stateN k r bank_i w.val (if bank_i then nc.val else nr.val) (if bank_i then cc else cr)).testBit
     (((off.val + i_val * s) % k + delayN r bank_i) % k) := by
 let wnBit : Fin (d + 1) → Bool := fun δ =>
   if h : δ.val < d + 1 - s then win ⟨δ.val, h⟩ else nxt ⟨δ.val - (d + 1 - s), by omega⟩
 have hwn_eq : ∀ δ : Fin (d + 1), wnBit δ = w.val.testBit ((off.val + i_val * s + δ.val) % k) := by
   intro δ
   dsimp only [wnBit]
   split_ifs with hlt
   · exact hwin ⟨δ.val, hlt⟩
   · rw [hnxt ⟨δ.val - (d + 1 - s), by omega⟩]
     rw [show off.val + i_val * s + (d + 1 - s) + (δ.val - (d + 1 - s)) = off.val + i_val * s + δ.val by omega]
 let wPad : Fin k → Bool := fun pos =>
   decide (∃ o : Fin k, decide (o = off) = true ∧
     decide (∃ δ : Fin (d + 1), (o.val + i_val * s + δ.val) % k = pos.val ∧ wnBit δ = true) = true)
 have hwPad_ag : ∀ δ ≤ reachN r bank_i,
     wPad ⟨((off.val + i_val * s) % k + δ) % k, Nat.mod_lt _ hk⟩ =
     w.val.testBit (((off.val + i_val * s) % k + δ) % k) := by
   intro δ hδ
   have hδ_lt : δ < d + 1 := by omega
   have hmod_eq : ((off.val + i_val * s) % k + δ) % k = (off.val + i_val * s + δ) % k := by
     rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
   change decide (∃ o : Fin k, decide (o = off) = true ∧
       decide (∃ δ' : Fin (d + 1), (o.val + i_val * s + δ'.val) % k = ((off.val + i_val * s) % k + δ) % k ∧ wnBit δ' = true) = true) =
     w.val.testBit (((off.val + i_val * s) % k + δ) % k)
   rw [hmod_eq]
   have hex_iff : (∃ o : Fin k, decide (o = off) = true ∧
         decide (∃ δ' : Fin (d + 1), (o.val + i_val * s + δ'.val) % k = (off.val + i_val * s + δ) % k ∧ wnBit δ' = true) = true) ↔
       wnBit ⟨δ, hδ_lt⟩ = true := by
     constructor
     · rintro ⟨o, ho, hδ'⟩
       have heqo : o = off := of_decide_eq_true ho; subst o
       obtain ⟨δ', heq, hwn⟩ := (decide_eq_true_iff).mp hδ'
       have hsame : δ'.val = δ := by
         have h1 : (off.val + i_val * s + δ'.val) % k = (off.val + i_val * s + δ) % k := heq
         have hsub1 := mod_sub_shift hk 0 (off.val + i_val * s + δ'.val) (off.val + i_val * s) (by omega)
         have hsub2 := mod_sub_shift hk 0 (off.val + i_val * s + δ) (off.val + i_val * s) (by omega)
         simp only [zero_add, Nat.add_sub_cancel_left] at hsub1 hsub2
         rw [← Nat.mod_eq_of_lt (lt_of_lt_of_le δ'.isLt (by omega : d + 1 ≤ k)), ← hsub1, h1, hsub2,
           Nat.mod_eq_of_lt (by omega : δ < k)]
       have : δ' = ⟨δ, hδ_lt⟩ := Fin.ext hsame
       rwa [← this]
     · intro hwn
       exact ⟨off, decide_eq_true rfl, decide_eq_true ⟨⟨δ, hδ_lt⟩, rfl, hwn⟩⟩
   have hdec : decide (∃ o : Fin k, decide (o = off) = true ∧
         decide (∃ δ' : Fin (d + 1), (o.val + i_val * s + δ'.val) % k = (off.val + i_val * s + δ) % k ∧ wnBit δ' = true) = true) =
       decide (wnBit ⟨δ, hδ_lt⟩ = true) := decide_eq_decide.mpr hex_iff
   rw [hdec, Bool.decide_eq_true, hwn_eq ⟨δ, hδ_lt⟩]
 have hout_one : ∀ (st : Fin k → Bool) (c0 : Bool),
     decide (∃ o : Fin k, decide (o = off) = true ∧
       st ⟨((o.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ = true) =
     st ⟨((off.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ := by
   intro st c0
   have hiff : (∃ o : Fin k, decide (o = off) = true ∧
         st ⟨((o.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ = true) ↔
       st ⟨((off.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ = true := by
     constructor
     · rintro ⟨o, ho, hst⟩; have heqo : o = off := of_decide_eq_true ho; subst o; exact hst
     · intro hst; exact ⟨off, decide_eq_true rfl, hst⟩
   have hdec : decide (∃ o : Fin k, decide (o = off) = true ∧
         st ⟨((o.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ = true) =
       decide (st ⟨((off.val + i_val * s) % k + delayN r c0) % k, Nat.mod_lt _ hk⟩ = true) :=
     decide_eq_decide.mpr hiff
   rw [hdec, Bool.decide_eq_true]
 have hbit := (stateB_eq_testBit hk bank_i w.val (if bank_i then nc.val else nr.val) w.isLt
   (by cases bank_i <;> simp [nr.isLt, nc.isLt]) (if bank_i then cc else cr)).2
   ⟨((off.val + i_val * s) % k + delayN r bank_i) % k, Nat.mod_lt _ hk⟩
 rw [hbit]
 cases bank_i
 · change decide (∃ o : Fin k, decide (o = off) = true ∧
       stateB k r hk false (Sum.elim wPad (Sum.elim (fun p => nr.val.testBit p.val) (fun p => (cr p.1).val.testBit p.2.val)))
         ⟨((o.val + i_val * s) % k + delayN r false) % k, Nat.mod_lt _ hk⟩ = true) = _
   rw [hout_one _ false]
   simp only [Bool.false_eq_true, ↓reduceIte]
   exact stateB_congr_reach hk hr false hk3 ((off.val + i_val * s) % k) wPad
     (fun i => w.val.testBit i.val) _ _ hwPad_ag
 · change decide (∃ o : Fin k, decide (o = off) = true ∧
       stateB k r hk true (Sum.elim wPad (Sum.elim (fun p => nc.val.testBit p.val) (fun p => (cc p.1).val.testBit p.2.val)))
         ⟨((o.val + i_val * s) % k + delayN r true) % k, Nat.mod_lt _ hk⟩ = true) = _
   rw [hout_one _ true]
   simp only [↓reduceIte]
   exact stateB_congr_reach hk hr true hk3 ((off.val + i_val * s) % k) wPad
     (fun i => w.val.testBit i.val) _ _ hwPad_ag
def bSN (q m : ℕ) (Pmat : Fin q × Fin m → Bool) : Fin q × Fin m × Fin m → Bool :=
 fun p =>
   let A : Fin (q - 1 - p.1.val) × Fin m → Bool :=
     fun rj => Pmat (⟨p.1.val + 1 + rj.1.val, by have := rj.1.isLt; omega⟩, rj.2)
   rNV (rref A) p.2.1 p.2.2
lemma ec_bSN (q m : ℕ) :
   EC (q * (50 * (q + 1) * (m + 1) * (q + m + 3))) (bSN q m) := by
 let I := Fin q × Fin m
 have hfam := ec_family (s := 50 * (q + 1) * (m + 1) * (q + m + 3))
   (f := fun (i : Fin q) (Pmat : I → Bool) (p : Fin m × Fin m) =>
     let A : Fin (q - 1 - i.val) × Fin m → Bool :=
       fun rj => Pmat (⟨i.val + 1 + rj.1.val, by have := rj.1.isLt; omega⟩, rj.2)
     rNV (rref A) p.1 p.2)
   (fun i => by
     let R := q - 1 - i.val
     have hR : R ≤ q := by omega
     let sel : Fin R × Fin m → I :=
       fun rj => (⟨i.val + 1 + rj.1.val, by have := rj.1.isLt; omega⟩, rj.2)
     have hr := ec_comp (ec_proj sel) (ec_rref R m)
     have hnv := ec_comp hr (ec_rNV R m)
     rw [zero_add] at hnv
     refine ec_le hnv ?_
     have h1 : 30 * m * (R + 1) * (R + m + 1) ≤ 30 * (q + 1) * (m + 1) * (q + m + 3) := by
       have ha : m * (R + 1) ≤ (q + 1) * (m + 1) := by nlinarith
       have hb : R + m + 1 ≤ q + m + 3 := by omega
       have hm := Nat.mul_le_mul ha hb
       calc 30 * m * (R + 1) * (R + m + 1) = 30 * (m * (R + 1) * (R + m + 1)) := by ring
         _ ≤ 30 * ((q + 1) * (m + 1) * (q + m + 3)) := Nat.mul_le_mul_left 30 hm
         _ = 30 * (q + 1) * (m + 1) * (q + m + 3) := by ring
     have h2 : m * m * (4 * R + 15) ≤ 15 * (q + 1) * (m + 1) * (q + m + 3) := by
       have ha : m * m ≤ (m + 1) * (q + m + 3) := by nlinarith
       have hb : 4 * R + 15 ≤ 15 * (q + 1) := by omega
       have hm := Nat.mul_le_mul hb ha
       calc m * m * (4 * R + 15) = (4 * R + 15) * (m * m) := by ring
         _ ≤ (15 * (q + 1)) * ((m + 1) * (q + m + 3)) := hm
         _ = 15 * (q + 1) * (m + 1) * (q + m + 3) := by ring
     have h3 : 8 ≤ 5 * (q + 1) * (m + 1) * (q + m + 3) := by
       have ha : 1 ≤ (q + 1) * (m + 1) := Nat.mul_pos (by omega) (by omega)
       have hb : 3 ≤ q + m + 3 := by omega
       calc 8 ≤ 5 * (1 * 3) := by omega
         _ ≤ 5 * ((q + 1) * (m + 1) * (q + m + 3)) := Nat.mul_le_mul_left 5 (Nat.mul_le_mul ha hb)
         _ = 5 * (q + 1) * (m + 1) * (q + m + 3) := by ring
     linarith only [h1, h2, h3])
 rw [Fintype.card_fin] at hfam
 have hp := ec_comp hfam (ec_proj (fun p : Fin q × Fin m × Fin m => (p.1, p.2)))
 rw [add_zero] at hp; exact hp
def feB (n e s d r a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hs : s ≤ d + 1)
   (raw : RIn n e s r → Bool) : FOut e s d a → Bool :=
 let m := 2 * n + 1
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let Pmat := buildP n e s r raw
 let eqOff : Fin k → Bool := fun o => eCB k o.val (rOff raw) ()
 let validBank : Bool := decide (∀ i : Fin q,
   (if rBnk raw i then decide (reachN r true ≤ d) else decide (reachN r false ≤ d)) = true)
 let stY := rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw))
 let yOk : Bool := !(rPC stY (Fin.last q))
 let alpha : Fin q → Bool := fun i => rNV stY (Fin.last q) i.castSucc
 let Nall := bSN q m Pmat
 let chain := rBC q D m (Sum.elim Pmat Nall)
 let mds : Fin q × SM D → Bool := fun p => chain (inr p)
 let anyOver : Bool := decide (∃ i : Fin q, sOv (fun x => mds (i, x)) = true)
 let validAll : Bool := validBank && yOk && (!anyOver)
 let probeTbl : Fin q × (Fin (d + 1 - s) → Bool) × (Fin s → Bool) → Bool := fun p =>
   pOE k r s d hk hs p.1.val p.2.1 p.2.2
     (Sum.elim eqOff (Sum.elim (rNr raw) (Sum.elim (rNc raw)
       (Sum.elim (fun x => rCr raw x.1 x.2) (Sum.elim (fun x => rCc raw x.1 x.2)
         (fun _ => rBnk raw p.1)))))) ()
 Sum.elim (fun _ => validAll) (Sum.elim alpha (Sum.elim mds (Sum.elim probeTbl eqOff)))
lemma ec_feB (n e s d r a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hs : s ≤ d + 1) :
   let m := 2 * n + 1
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   EC (
     q * m * (20 * n + 50) +
     k * (8 * k + 10) +
     (20 * q + 20) +
     100 * (q + 1) * (m + 1) * (q + m + 3) +
     q * (50 * (q + 1) * (m + 1) * (q + m + 3)) +
     (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3))) +
     (4 * q + 30) +
     q * 2 ^ (d + 1 - s) * 2 ^ s * (100 * (k + 1) * (k + r + 2))
   ) (feB n e s d r a hk hs) := by
 let m := 2 * n + 1
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let I0 := RIn n e s r
 have hP := ec_buildP n e s r
 have heqOff : EC (k * (8 * k + 10))
     (fun (raw : I0 → Bool) (o : Fin k) => eCB k o.val (rOff raw) ()) := by
   have hfam := ec_family (s := 8 * k + 10)
     (f := fun (o : Fin k) (raw : I0 → Bool) (_ : Unit) => eCB k o.val (rOff raw) ())
     (fun o => by
       have h := ec_comp (ec_proj (fun p : Fin k => (inr (inr (inr (inr (inr (inl p))))) : I0)))
         (ec_eCB k o.val)
       rw [zero_add] at h; exact h)
   rw [Fintype.card_fin] at hfam
   have hp := ec_comp hfam (ec_proj (fun o : Fin k => (o, ())))
   rw [add_zero] at hp; exact hp
 have hvBank : EC (20 * q + 20)
     (fun (raw : I0 → Bool) (_ : Unit) =>
       decide (∀ i : Fin q,
         (if rBnk raw i then decide (reachN r true ≤ d) else decide (reachN r false ≤ d)) = true)) := by
   have hite := ec_ite_of
     (ec_proj (fun i : Fin q => (inr (inr (inr (inr (inr (inr (inl i)))))) : I0)))
     (ec_const (fun (_ : Fin q) => decide (reachN r true ≤ d)))
     (ec_const (fun (_ : Fin q) => decide (reachN r false ≤ d)))
   rw [Fintype.card_fin] at hite
   have hall := ec_comp hite (ec_all (α := Fin q))
   rw [Fintype.card_fin] at hall
   refine ec_le (ec_eq ?_ hall) (by dsimp only [q]; omega)
   intro raw _; simp only [decide_eq_decide]; rfl
 have hs1 := ec_pair hP (ec_pair heqOff hvBank)
 let I1 := I0 ⊕ ((Fin q × Fin m) ⊕ Fin k ⊕ Unit)
 have hY : EC (100 * (q + 1) * (m + 1) * (q + m + 3))
     (fun (y : I1 → Bool) =>
       let Pmat := fun p => y (inr (inl p))
       let stY := rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j))
         (fun b => y (inl (inr (inr (inr (inr (inr (inr (inr (inl b)))))))))))
       Sum.elim (fun (_ : Unit) => !(rPC stY (Fin.last q)))
         (fun i : Fin q => rNV stY (Fin.last q) i.castSucc)) := by
   let selAug : Fin m × Fin (q + 1) → I1 := fun p =>
     Fin.lastCases
       (inl (inr (inr (inr (inr (inr (inr (inr (inl p.1)))))))))
       (fun i => inr (inl (i, p.1))) p.2
   have hr := ec_comp (ec_proj selAug) (ec_rref m (q + 1))
   rw [zero_add] at hr
   have hnv := ec_comp (ec_proj (fun x : RIdx m (q + 1) => (inr x : I1 ⊕ RIdx m (q + 1))))
     (ec_rNV m (q + 1))
   rw [zero_add] at hnv
   let I1b := (I1 ⊕ RIdx m (q + 1)) ⊕ (Fin (q + 1) × Fin (q + 1))
   have hout : EC 2
       (fun (z : I1b → Bool) =>
         Sum.elim (fun (_ : Unit) => !(z (inl (inr (inr (inr (Fin.last q)))))))
           (fun i : Fin q => z (inr (Fin.last q, i.castSucc)))) := by
     have h1 := ec_not_of (ec_proj (fun (_ : Unit) => (inl (inr (inr (inr (Fin.last q)))) : I1b)))
     have h2 := ec_proj (fun i : Fin q => (inr (Fin.last q, i.castSucc) : I1b))
     have hp := ec_pair h1 h2
     rw [Fintype.card_unit] at hp; exact ec_le hp (by omega)
   have htot := ec_let hr (ec_let hnv hout)
   refine ec_le (ec_eq ?_ htot) ?_
   · intro y p
     have harg : (fun rj => y (selAug rj)) =
         aMt (fun (i : Fin q) (j : Fin m) => y (inr (inl (i, j))))
           (fun b => y (inl (inr (inr (inr (inr (inr (inr (inr (inl b)))))))))) := by
       funext rj; unfold aMt selAug; refine Fin.lastCases ?_ ?_ rj.2 <;> simp
     rcases p with u | i
     · simp only [Sum.elim_inl, Sum.elim_inr, rPC]; rw [harg]
     · simp only [Sum.elim_inl, Sum.elim_inr]; rw [harg]
   · have h1 : 30 * (q + 1) * (m + 1) * (m + (q + 1) + 1) ≤ 30 * (q + 1) * (m + 1) * (q + m + 3) := by
       have hlt : m + (q + 1) + 1 ≤ q + m + 3 := by omega
       exact Nat.mul_le_mul_left _ hlt
     have h2 : (q + 1) * (q + 1) * (4 * m + 15) ≤ 60 * (q + 1) * (m + 1) * (q + m + 3) := by
       have ha : q + 1 ≤ q + m + 3 := by omega
       have hb : 4 * m + 15 ≤ 60 * (m + 1) := by omega
       have hm := Nat.mul_le_mul ha hb
       calc (q + 1) * (q + 1) * (4 * m + 15) = (q + 1) * ((q + 1) * (4 * m + 15)) := by ring
         _ ≤ (q + 1) * ((q + m + 3) * (60 * (m + 1))) := Nat.mul_le_mul_left _ hm
         _ = 60 * (q + 1) * (m + 1) * (q + m + 3) := by ring
     have h3 : 10 ≤ 10 * (q + 1) * (m + 1) * (q + m + 3) := by
       have ha : 1 ≤ (q + 1) * (m + 1) * (q + m + 3) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
       calc 10 = 10 * 1 := by ring
         _ ≤ 10 * ((q + 1) * (m + 1) * (q + m + 3)) := Nat.mul_le_mul_left 10 ha
         _ = 10 * (q + 1) * (m + 1) * (q + m + 3) := by ring
     linarith only [h1, h2, h3]
 have hNall : EC (q * (50 * (q + 1) * (m + 1) * (q + m + 3)))
     (fun (y : I1 → Bool) => bSN q m (fun p => y (inr (inl p)))) := by
   have h := ec_comp (ec_proj (fun p : Fin q × Fin m => (inr (inl p) : I1))) (ec_bSN q m)
   rwa [zero_add] at h
 have hs2 := ec_pair hY hNall
 let I2 := I1 ⊕ ((Unit ⊕ Fin q) ⊕ (Fin q × Fin m × Fin m))
 have hchain : EC (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3)))
     (fun (z : I2 → Bool) =>
       rBC q D m (Sum.elim (fun p => z (inl (inr (inl p)))) (fun p => z (inr (inr p))))) := by
   let sel : (Fin q × Fin m) ⊕ (Fin q × Fin m × Fin m) → I2 :=
     Sum.elim (fun p => inl (inr (inl p))) (fun p => inr (inr p))
   have h := ec_comp (ec_proj sel) (ec_rBC q D m)
   rw [zero_add] at h
   refine ec_eq ?_ h
   intro z a; congr 1; funext x; rcases x with _ | _ <;> rfl
 let I3 := I2 ⊕ (BSt D m ⊕ (Fin q × SM D))
 have hvalid : EC (4 * q + 30)
     (fun (w : I3 → Bool) (_ : Unit) =>
       let validBank := w (inl (inl (inr (inr (inr ())))))
       let yOk := w (inl (inr (inl (inl ()))))
       let anyOver := decide (∃ i : Fin q,
         w (inr (inr (i, inr (inr (inr (inr ())))))) = true)
       validBank && yOk && (!anyOver)) := by
   have hany := ec_comp (ec_proj (fun i : Fin q =>
       (inr (inr (i, inr (inr (inr (inr ()))))) : I3))) (ec_any (α := Fin q))
   rw [zero_add, Fintype.card_fin] at hany
   have hvb : EC 0 (fun (w : I3 → Bool) (_ : Unit) =>
       w (inl (inl (inr (inr (inr ())))))) := ec_proj _
   have hy : EC 0 (fun (w : I3 → Bool) (_ : Unit) =>
       w (inl (inr (inl (inl ()))))) := ec_proj _
   have hand := ec_and_of (ec_and_of hvb hy) (ec_not_of hany)
   rw [Fintype.card_unit] at hand
   refine ec_le (ec_eq ?_ hand) (by dsimp only [q]; omega)
   intro w _; congr 2; exact decide_eq_decide.mpr Iff.rfl
 have hprobe : EC (q * 2 ^ (d + 1 - s) * 2 ^ s * (100 * (k + 1) * (k + r + 2)))
     (fun (w : I3 → Bool) (p : Fin q × (Fin (d + 1 - s) → Bool) × (Fin s → Bool)) =>
       pOE k r s d hk hs p.1.val p.2.1 p.2.2
         (Sum.elim (fun o => w (inl (inl (inr (inr (inl o))))))
           (Sum.elim (fun x => w (inl (inl (inl (inr (inl x))))))
             (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inl x)))))))
               (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inr (inl x))))))))
                 (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inr (inr (inl x)))))))))
                   (fun _ => w (inl (inl (inl (inr (inr (inr (inr (inr (inr (inl p.1)))))))))))))))) ()) := by
   let PIdx := Fin q × (Fin (d + 1 - s) → Bool) × (Fin s → Bool)
   have hcardP : Fintype.card PIdx = q * 2 ^ (d + 1 - s) * 2 ^ s := by
     simp only [PIdx, Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
       Finset.card_univ, Fintype.card_fin]
     ring
   have hfam := ec_family (s := 100 * (k + 1) * (k + r + 2))
     (f := fun (p : PIdx) (w : I3 → Bool) (_ : Unit) =>
       pOE k r s d hk hs p.1.val p.2.1 p.2.2
         (Sum.elim (fun o => w (inl (inl (inr (inr (inl o))))))
           (Sum.elim (fun x => w (inl (inl (inl (inr (inl x))))))
             (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inl x)))))))
               (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inr (inl x))))))))
                 (Sum.elim (fun x => w (inl (inl (inl (inr (inr (inr (inr (inl x)))))))))
                   (fun _ => w (inl (inl (inl (inr (inr (inr (inr (inr (inr (inl p.1)))))))))))))))) ())
     (fun p => by
       let sel : Fin k ⊕ Fin k ⊕ Fin k ⊕ (Fin r × Fin k) ⊕ (Fin r × Fin k) ⊕ Unit → I3 :=
         Sum.elim (fun o => inl (inl (inr (inr (inl o)))))
           (Sum.elim (fun x => inl (inl (inl (inr (inl x)))))
             (Sum.elim (fun x => inl (inl (inl (inr (inr (inl x))))))
               (Sum.elim (fun x => inl (inl (inl (inr (inr (inr (inl x)))))))
                 (Sum.elim (fun x => inl (inl (inl (inr (inr (inr (inr (inl x))))))))
                   (fun _ => inl (inl (inl (inr (inr (inr (inr (inr (inr (inl p.1))))))))))))))
       have h := ec_comp (ec_proj sel) (ec_pOE k r s d hk hs p.1.val p.2.1 p.2.2)
       rw [zero_add] at h
       refine ec_eq ?_ h
       intro w u; congr 1; funext x; rcases x with _ | _ | _ | _ | _ | _ <;> rfl)
   rw [hcardP] at hfam
   have hp := ec_comp hfam (ec_proj (fun p : PIdx => (p, ())))
   rw [add_zero] at hp; exact hp
 have hout := ec_pair hvalid
   (ec_pair (ec_proj (fun i : Fin q => (inl (inr (inl (inr i))) : I3)))
     (ec_pair (ec_proj (fun p : Fin q × SM D => (inr (inr p) : I3)))
       (ec_pair hprobe (ec_proj (fun o : Fin k => (inl (inl (inr (inr (inl o)))) : I3))))))
 have htot := ec_let hs1 (ec_let hs2 (ec_let hchain hout))
 refine ec_le (ec_eq ?_ htot) (by dsimp only [m, q, k, D]; omega)
 intro raw x
 rcases x with u | i | p | p | o <;> rfl
def Lsub {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (h : ℕ) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
 Submodule.span (ZMod 2) { v | ∃ i : Fin q, i.val < h ∧ v = Pvec i }
def Rsub {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (h : ℕ) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
 Submodule.span (ZMod 2) { v | ∃ i : Fin q, h ≤ i.val ∧ v = Pvec i }
lemma Lsub_zero {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) : Lsub Pvec 0 = ⊥ := by
 unfold Lsub
 have : ({ v | ∃ i : Fin q, i.val < 0 ∧ v = Pvec i } : Set (Fin m → ZMod 2)) = ∅ := by
   ext v; simp
 rw [this, Submodule.span_empty]
lemma Rsub_end {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) : Rsub Pvec q = ⊥ := by
 unfold Rsub
 have : ({ v | ∃ i : Fin q, q ≤ i.val ∧ v = Pvec i } : Set (Fin m → ZMod 2)) = ∅ := by
   ext v; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
   intro i hi; have := i.isLt; omega
 rw [this, Submodule.span_empty]
lemma Lsub_succ {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (i : Fin q) :
   Lsub Pvec (i.val + 1) = Lsub Pvec i.val ⊔ Submodule.span (ZMod 2) {Pvec i} := by
 unfold Lsub
 rw [← Submodule.span_union]
 congr 1; ext v; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
 constructor
 · rintro ⟨j, hj, rfl⟩
   by_cases hlt : j.val < i.val
   · exact Or.inl ⟨j, hlt, rfl⟩
   · have heq : j = i := Fin.ext (by omega)
     subst heq; exact Or.inr rfl
 · rintro (⟨j, hj, rfl⟩ | rfl)
   · exact ⟨j, by omega, rfl⟩
   · exact ⟨i, by omega, rfl⟩
lemma Rsub_succ {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (i : Fin q) :
   Rsub Pvec i.val = Rsub Pvec (i.val + 1) ⊔ Submodule.span (ZMod 2) {Pvec i} := by
 unfold Rsub
 rw [← Submodule.span_union]
 congr 1; ext v; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
 constructor
 · rintro ⟨j, hj, rfl⟩
   by_cases hle : i.val + 1 ≤ j.val
   · exact Or.inl ⟨j, hle, rfl⟩
   · have heq : j = i := Fin.ext (by omega)
     subst heq; exact Or.inr rfl
 · rintro (⟨j, hj, rfl⟩ | rfl)
   · exact ⟨j, by omega, rfl⟩
   · exact ⟨i, le_rfl, rfl⟩
lemma Rsub_eq_range {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (i : Fin q) :
   Rsub Pvec (i.val + 1) =
     Submodule.span (ZMod 2) (Set.range (fun t : Fin (q - 1 - i.val) => Pvec ⟨i.val + 1 + t.val, by have := t.isLt; omega⟩)) := by
 unfold Rsub; congr 1; ext v; simp only [Set.mem_ofPred_eq, Set.mem_range]
 constructor
 · rintro ⟨j, hj, rfl⟩
   exact ⟨⟨j.val - (i.val + 1), by have := j.isLt; omega⟩, by congr 1; ext; dsimp; omega⟩
 · rintro ⟨t, rfl⟩
   exact ⟨⟨i.val + 1 + t.val, by have := t.isLt; omega⟩, by dsimp; omega, rfl⟩
lemma Lsub_eq_list_take {q m : ℕ} (P : List ℕ) (hlen : P.length = q) (h : ℕ) :
   Lsub (fun i : Fin q => vecBit m (P[i.val]?.getD 0)) h =
     Submodule.span (ZMod 2)
       (↑((List.map (fun w (j : Fin m) => if w.testBit j.val then (1 : ZMod 2) else 0) (P.take h)).toFinset) :
         Set (Fin m → ZMod 2)) := by
 unfold Lsub; congr 1; ext v
 simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
 constructor
 · rintro ⟨i, hi, rfl⟩
   refine ⟨P[i.val]'(by omega), ?_, ?_⟩
   · have hlt : i.val < (P.take h).length := by rw [List.length_take]; omega
     have hget : (P.take h)[i.val]'hlt = P[i.val]'(by omega) := List.getElem_take
     rw [← hget]; exact List.getElem_mem hlt
   · rw [List.getElem?_eq_getElem (by omega)]; rfl
 · rintro ⟨w, hw, rfl⟩
   rw [List.mem_iff_getElem] at hw
   obtain ⟨idx, hidx, hget⟩ := hw
   have hidx_h : idx < h := by rw [List.length_take] at hidx; omega
   have hidx_q : idx < q := by rw [List.length_take] at hidx; omega
   refine ⟨⟨idx, hidx_q⟩, hidx_h, ?_⟩
   rw [List.getElem?_eq_getElem (by omega)]
   have hgt : (P.take h)[idx]'hidx = P[idx]'(by omega) := List.getElem_take
   rw [hgt] at hget; rw [← hget]; rfl
lemma Rsub_eq_list_drop {q m : ℕ} (P : List ℕ) (hlen : P.length = q) (h : ℕ) :
   Rsub (fun i : Fin q => vecBit m (P[i.val]?.getD 0)) h =
     Submodule.span (ZMod 2)
       (↑((List.map (fun w (j : Fin m) => if w.testBit j.val then (1 : ZMod 2) else 0) (P.drop h)).toFinset) :
         Set (Fin m → ZMod 2)) := by
 unfold Rsub; congr 1; ext v
 simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
 constructor
 · rintro ⟨i, hi, rfl⟩
   refine ⟨P[i.val]'(by omega), ?_, ?_⟩
   · have hlt : i.val - h < (P.drop h).length := by rw [List.length_drop]; omega
     have hget : (P.drop h)[i.val - h]'hlt = P[i.val]'(by omega) := by
       rw [List.getElem_drop]; congr 1; omega
     rw [← hget]; exact List.getElem_mem hlt
   · rw [List.getElem?_eq_getElem (by omega)]; rfl
 · rintro ⟨w, hw, rfl⟩
   rw [List.mem_iff_getElem] at hw
   obtain ⟨idx, hidx, hget⟩ := hw
   have hidx_q : h + idx < q := by rw [List.length_drop] at hidx; omega
   refine ⟨⟨h + idx, hidx_q⟩, by dsimp; omega, ?_⟩
   rw [List.getElem?_eq_getElem (by omega)]
   rw [List.getElem_drop] at hget; rw [← hget]; rfl
def cPfx (q D m : ℕ) (Pmat : Fin q × Fin m → Bool) (Nall : Fin q × Fin m × Fin m → Bool) (t : ℕ) :
   BSt D m ⊕ (Fin q × SM D) → Bool :=
 ((List.finRange q).take t).foldl
   (fun acc i =>
     let st : BSt D m → Bool := fun a => acc (inl a)
     let mds : Fin q × SM D → Bool := fun p => acc (inr p)
     let res := stB D m (Sum.elim st (Sum.elim (fun p => Nall (i, p)) (fun j => Pmat (i, j))))
     Sum.elim (fun a => res (inl a))
       (fun p => if p.1 = i then res (inr p.2) else mds p))
   (fun _ => false)
lemma rBC_sp {q D m : ℕ} (Pmat : Fin q × Fin m → Bool) :
   let Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
   let Nall := bSN q m Pmat
   let out := rBC q D m (Sum.elim Pmat Nall)
   let mds : Fin q → SM D → Bool := fun i a => out (inr (i, a))
   let stAt : ℕ → BSt D m → Bool := fun t a => cPfx q D m Pmat Nall t (inl a)
   ((∃ i : Fin q, sOv (mds i) = true) ↔
     ∃ h : ℕ, h ≤ q ∧ D < Module.finrank (ZMod 2) ↥(Lsub Pvec h ⊓ Rsub Pvec h)) ∧
   ((∀ i : Fin q, sOv (mds i) = false) →
     (∀ t : ℕ, t ≤ q → BInv (Lsub Pvec t ⊓ Rsub Pvec t) (stAt t)) ∧
     (∀ i : Fin q, SMR (Lsub Pvec i.val ⊓ Rsub Pvec i.val)
       (stAt i.val) (stAt (i.val + 1)) (Pvec i) (mds i))) := by
 dsimp only
 set Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
 set Nall := bSN q m Pmat
 have hprefix_step : ∀ (t : ℕ) (ht : t < q),
     let ii : Fin q := ⟨t, ht⟩
     let prev := cPfx q D m Pmat Nall t
     let res := stB D m (Sum.elim (fun a => prev (inl a))
       (Sum.elim (fun p => Nall (ii, p)) (fun j => Pmat (ii, j))))
     (∀ a, cPfx q D m Pmat Nall (t + 1) (inl a) = res (inl a)) ∧
     (∀ p : Fin q × SM D, cPfx q D m Pmat Nall (t + 1) (inr p) =
       if p.1 = ii then res (inr p.2) else prev (inr p)) := by
   intro t ht
   let ii : Fin q := ⟨t, ht⟩
   have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t ++ [ii] := by
     have h1 := List.take_succ_eq_append_getElem (l := List.finRange q) (i := t) (by simp; omega)
     simpa [ii] using h1
   constructor
   · intro a; unfold cPfx; rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
   · intro p; unfold cPfx; rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
 have hmd_stable : ∀ (t1 t2 : ℕ) (i : Fin q), i.val < t1 → t1 ≤ t2 → t2 ≤ q →
     ∀ a, cPfx q D m Pmat Nall t2 (inr (i, a)) =
          cPfx q D m Pmat Nall t1 (inr (i, a)) := by
   intro t1 t2 i hi hle hq a
   induction t2 with
   | zero => omega
   | succ t2 ih =>
     by_cases heq : t1 = t2 + 1
     · subst heq; rfl
     · have hne : i ≠ ⟨t2, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
       rw [(hprefix_step t2 (by omega)).2 (i, a)]
       simp only [hne, ↓reduceIte]
       exact ih (by omega) (by omega)
 have hinv0 : BInv (Lsub Pvec 0 ⊓ Rsub Pvec 0) (fun a => cPfx q D m Pmat Nall 0 (inl a)) := by
   rw [Lsub_zero, bot_inf_eq]
   refine ⟨fun l _ => by funext j; rfl, ?_, ?_⟩
   · rw [Fintype.linearIndependent_iff]; intro g _ l; exact Bool.noConfusion l.property
   · rw [eq_bot_iff, Submodule.span_le]; rintro _ ⟨⟨l, hl⟩, _⟩; exact Bool.noConfusion hl
 have hind : ∀ t : ℕ, t ≤ q →
     ((∃ i : Fin q, i.val < t ∧ sOv (fun a => cPfx q D m Pmat Nall t (inr (i, a))) = true) ↔
       ∃ h : ℕ, h ≤ t ∧ D < Module.finrank (ZMod 2) ↥(Lsub Pvec h ⊓ Rsub Pvec h)) ∧
     ((∀ i : Fin q, i.val < t → sOv (fun a => cPfx q D m Pmat Nall t (inr (i, a))) = false) →
       (∀ u : ℕ, u ≤ t → BInv (Lsub Pvec u ⊓ Rsub Pvec u) (fun a => cPfx q D m Pmat Nall u (inl a))) ∧
       (∀ i : Fin q, i.val < t →
         SMR (Lsub Pvec i.val ⊓ Rsub Pvec i.val)
           (fun a => cPfx q D m Pmat Nall i.val (inl a))
           (fun a => cPfx q D m Pmat Nall (i.val + 1) (inl a))
           (Pvec i) (fun a => cPfx q D m Pmat Nall t (inr (i, a))))) := by
   intro t
   induction t with
   | zero =>
     intro _
     constructor
     · constructor
       · rintro ⟨i, hi, _⟩; omega
       · rintro ⟨h, hh, hgt⟩
         have hh0 : h = 0 := by omega
         subst hh0; rw [Lsub_zero, bot_inf_eq, finrank_bot] at hgt; omega
     · intro _; refine ⟨fun u hu => ?_, fun i hi => by omega⟩
       have hu0 : u = 0 := by omega
       subst hu0; exact hinv0
   | succ t ih =>
     intro ht
     obtain ⟨ih_ov, ih_ok⟩ := ih (by omega)
     let ii : Fin q := ⟨t, ht⟩
     have hst_succ := (hprefix_step t ht).1
     have hmd_succ := (hprefix_step t ht).2
     have hprev_eq : ∀ i : Fin q, i.val < t →
         (fun a => cPfx q D m Pmat Nall (t + 1) (inr (i, a))) =
         (fun a => cPfx q D m Pmat Nall t (inr (i, a))) := fun i hi =>
       funext (fun a => hmd_stable t (t + 1) i hi (by omega) ht a)
     by_cases hprev_ov : ∃ i : Fin q, i.val < t ∧ sOv (fun a => cPfx q D m Pmat Nall t (inr (i, a))) = true
     · obtain ⟨h0, hh0, hgt0⟩ := ih_ov.mp hprev_ov
       obtain ⟨i0, hi0, hov0⟩ := hprev_ov
       constructor
       · refine ⟨fun _ => ⟨h0, by omega, hgt0⟩, fun _ => ⟨i0, by omega, ?_⟩⟩
         rw [hprev_eq i0 hi0]; exact hov0
       · intro hall
         have h1 := hall i0 (by omega)
         rw [hprev_eq i0 hi0, hov0] at h1; exact Bool.noConfusion h1
     · have hprev_all : ∀ i : Fin q, i.val < t →
           sOv (fun a => cPfx q D m Pmat Nall t (inr (i, a))) = false := by
         intro i hi
         cases hc : sOv (fun a => cPfx q D m Pmat Nall t (inr (i, a)))
         · rfl
         · exact absurd ⟨i, hi, hc⟩ hprev_ov
       obtain ⟨hinv_le, hrel_lt⟩ := ih_ok hprev_all
       have hinv_t := hinv_le t le_rfl
       have hspec := stB_sp
         (Lsub Pvec t) (Rsub Pvec (t + 1))
         (fun rj : Fin (q - 1 - t) × Fin m => Pmat (⟨t + 1 + rj.1.val, by have := rj.1.isLt; omega⟩, rj.2))
         (Rsub_eq_range Pvec ii)
         (fun j => Pmat (ii, j))
         (fun a => cPfx q D m Pmat Nall t (inl a))
         (by rw [← Rsub_succ Pvec ii]; exact hinv_t)
       dsimp only at hspec
       rw [← Lsub_succ Pvec ii] at hspec
       have hmd_ii : (fun a => cPfx q D m Pmat Nall (t + 1) (inr (ii, a))) =
           fun a => stB D m (Sum.elim (fun x => cPfx q D m Pmat Nall t (inl x))
             (Sum.elim (fun p => Nall (ii, p)) (fun j => Pmat (ii, j)))) (inr a) := by
         funext a; rw [hmd_succ (ii, a)]; dsimp only [ii]; simp only [↓reduceIte]
       have hst_next : (fun a => cPfx q D m Pmat Nall (t + 1) (inl a)) =
           fun a => stB D m (Sum.elim (fun x => cPfx q D m Pmat Nall t (inl x))
             (Sum.elim (fun p => Nall (ii, p)) (fun j => Pmat (ii, j)))) (inl a) :=
         funext hst_succ
       have hNii : (fun p : Fin m × Fin m => rNV (rref
           (fun rj : Fin (q - 1 - t) × Fin m => Pmat (⟨t + 1 + rj.1.val, by have := rj.1.isLt; omega⟩, rj.2))) p.1 p.2) =
           fun p => Nall (ii, p) := rfl
       rw [hNii] at hspec
       constructor
       · constructor
         · rintro ⟨i, hi, hovi⟩
           by_cases hlt : i.val < t
           · rw [hprev_eq i hlt, hprev_all i hlt] at hovi; exact Bool.noConfusion hovi
           · have heqi : i = ii := Fin.ext (by dsimp [ii]; omega)
             subst heqi; rw [hmd_ii] at hovi
             exact ⟨t + 1, le_rfl, hspec.1.mp hovi⟩
         · rintro ⟨h0, hh0, hgt0⟩
           by_cases hle : h0 ≤ t
           · exact absurd (ih_ov.mpr ⟨h0, hle, hgt0⟩) hprev_ov
           · have heq : h0 = t + 1 := by omega
             subst heq
             exact ⟨ii, by dsimp [ii]; omega, by rw [hmd_ii]; exact hspec.1.mpr hgt0⟩
       · intro hall
         have hno_ii : sOv (fun a => stB D m (Sum.elim (fun x => cPfx q D m Pmat Nall t (inl x))
             (Sum.elim (fun p => Nall (ii, p)) (fun j => Pmat (ii, j)))) (inr a)) = false := by
           rw [← hmd_ii]; exact hall ii (by dsimp [ii]; omega)
         obtain ⟨hinv_next, hrel_ii⟩ := hspec.2 hno_ii
         rw [← hst_next] at hinv_next hrel_ii
         rw [← hmd_ii] at hrel_ii
         refine ⟨fun u hu => ?_, fun i hi => ?_⟩
         · by_cases hle : u ≤ t
           · exact hinv_le u hle
           · have heq : u = t + 1 := by omega
             subst heq; exact hinv_next
         · by_cases hlt : i.val < t
           · rw [hprev_eq i hlt]; exact hrel_lt i hlt
           · have heqi : i = ii := Fin.ext (by dsimp [ii]; omega)
             subst heqi; rw [← Rsub_succ Pvec ii] at hrel_ii; exact hrel_ii
 have hout_eq : rBC q D m (Sum.elim Pmat Nall) = cPfx q D m Pmat Nall q := by
   unfold rBC cPfx
   rw [List.take_of_length_le (by simp)]
   rfl
 obtain ⟨h1, h2⟩ := hind q le_rfl
 rw [hout_eq]
 refine ⟨?_, ?_⟩
 · simpa [Fin.isLt] using h1
 · intro hall
   obtain ⟨ha, hb⟩ := h2 (fun i _ => hall i)
   exact ⟨ha, fun i => hb i i.isLt⟩
lemma ps_cut {q m : ℕ} (Pvec : Fin q → Fin m → ZMod 2) (c : Fin q → Bool) :
   (∑ i : Fin q, b2z (c i) • Pvec i = 0) ↔
     (∀ t : ℕ, t ≤ q →
       (∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t), b2z (c i) • Pvec i) ∈
         Lsub Pvec t ⊓ Rsub Pvec t) := by
 constructor
 · intro hsum t _
   refine ⟨?_, ?_⟩
   · apply Submodule.sum_mem; intro i hi
     exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩)
   · have hpart : (∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t), b2z (c i) • Pvec i) +
         (∑ i ∈ Finset.univ.filter (fun i : Fin q => t ≤ i.val), b2z (c i) • Pvec i) =
         ∑ i : Fin q, b2z (c i) • Pvec i := by
       have hcomp : Finset.univ.filter (fun i : Fin q => t ≤ i.val) =
           Finset.univ.filter (fun i : Fin q => ¬ i.val < t) := by
         ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
       rw [hcomp]
       exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin q => i.val < t) _
     rw [hsum] at hpart
     have heq : (∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t), b2z (c i) • Pvec i) =
         ∑ i ∈ Finset.univ.filter (fun i : Fin q => t ≤ i.val), b2z (c i) • Pvec i := by
       have hadd := congrArg (fun x => x + ∑ i ∈ Finset.univ.filter (fun i : Fin q => t ≤ i.val), b2z (c i) • Pvec i) hpart
       simp only [add_assoc, zmod2_fun_add_self, add_zero, zero_add] at hadd
       exact hadd
     rw [heq]
     apply Submodule.sum_mem; intro i hi
     exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩)
 · intro hall
   have hq := (hall q le_rfl).2
   rw [Rsub_end] at hq
   have hq0 := (Submodule.mem_bot (ZMod 2)).mp hq
   have hf : Finset.univ.filter (fun i : Fin q => i.val < q) = Finset.univ := by
     ext i; simp
   rwa [hf] at hq0
def sWin {L s : ℕ} (hsL : s ≤ L) (wp : Fin L → Bool) (nxt : Fin s → Bool) : Fin L → Bool :=
 fun u => if h : u.val < L - s then wp ⟨s + u.val, by omega⟩ else nxt ⟨u.val - (L - s), by omega⟩
def pWin {L s : ℕ} (_ : s ≤ L) (wn : Fin L → Bool) (ps : Fin s → Bool) : Fin L → Bool :=
 fun u => if h : u.val < s then ps ⟨u.val, h⟩ else wn ⟨u.val - s, by omega⟩
def hBlk {L s : ℕ} (hsL : s ≤ L) (w : Fin L → Bool) : Fin s → Bool :=
 fun u => w ⟨u.val, by omega⟩
def tBlk {L s : ℕ} (hsL : s ≤ L) (w : Fin L → Bool) : Fin s → Bool :=
 fun u => w ⟨L - s + u.val, by omega⟩
lemma shiftWin_iff {L s : ℕ} (hsL : s ≤ L) (wp wn : Fin L → Bool) (nxt : Fin s → Bool) :
   sWin hsL wp nxt = wn ↔
     wp = pWin hsL wn (hBlk hsL wp) ∧ nxt = tBlk hsL wn := by
 constructor
 · intro heq
   constructor
   · funext u; unfold pWin hBlk
     split_ifs with hlt
     · rfl
     · have := congrFun heq ⟨u.val - s, by omega⟩
       dsimp only [sWin] at this
       have hlt2 : u.val - s < L - s := by omega
       simp only [hlt2, ↓reduceDIte] at this
       rw [← this]; congr 1; ext; dsimp; omega
   · funext u; unfold tBlk
     have := congrFun heq ⟨L - s + u.val, by omega⟩
     dsimp only [sWin] at this
     have hge : ¬ (L - s + u.val < L - s) := by omega
     simp only [hge, ↓reduceDIte] at this
     rw [← this]; congr 1; ext; dsimp; omega
 · rintro ⟨hwp, hnxt⟩
   funext u; unfold sWin
   split_ifs with hlt
   · rw [hwp]; unfold pWin
     have hge : ¬ (s + u.val < s) := by omega
     simp only [hge, ↓reduceDIte]; congr 1; ext; dsimp; omega
   · rw [hnxt]; unfold tBlk
     congr 1; ext; dsimp; omega
lemma headBlk_prevWin {L s : ℕ} (hsL : s ≤ L) (wn : Fin L → Bool) (ps : Fin s → Bool) :
   hBlk hsL (pWin hsL wn ps) = ps := by
 funext u; simp [hBlk, pWin, u.isLt]
noncomputable def dpStep (L s D Wbits : ℕ) (hsL : s ≤ L)
   (inp : SM D ⊕ Unit ⊕ ((Fin L → Bool) × (Fin s → Bool)) ⊕ Fin s ⊕ Fin s ⊕
     ((Fin L → Bool) × (Fin D → Bool) × Fin Wbits) → Bool)
   (q : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits) : Bool :=
 let md : SM D → Bool := fun a => inp (inl a)
 let alpha_i : Bool := inp (inr (inl ()))
 let probe_i : (Fin L → Bool) × (Fin s → Bool) → Bool := fun p => inp (inr (inr (inl p)))
 let mask_i : Fin s → Bool := fun u => inp (inr (inr (inr (inl u))))
 let val_i : Fin s → Bool := fun u => inp (inr (inr (inr (inr (inl u)))))
 let dp : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits → Bool :=
   fun p => inp (inr (inr (inr (inr (inr p)))))
 let T0 : (Fin L → Bool) → (Fin D → Bool) × Fin Wbits → Bool := fun wp =>
   aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (wp, r))))
 let T1 : (Fin L → Bool) → (Fin D → Bool) × Fin Wbits → Bool := fun wp =>
   aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (wp, r))))
 let wn := q.1
 let x := q.2.1
 let b := q.2.2
 let nxt := tBlk hsL wn
 let terms : (Fin s → Bool) × Fin Wbits → Bool := fun pb =>
   let ps := pb.1
   let wp := pWin hsL wn ps
   let ok := decide (∀ u : Fin s, mask_i u = true → ps u = val_i u)
   let ci := xor (probe_i (wp, nxt)) alpha_i
   ok && (if ci then T1 wp (x, pb.2) else T0 wp (x, pb.2))
 bvSum (α := Fin s → Bool) Wbits terms b
lemma ec_dpStep (L s D Wbits : ℕ) (hsL : s ≤ L) :
   EC (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (Wbits + s + 2) + 120 * (D + 1) * (D + 1)))
     (dpStep L s D Wbits hsL) := by
 let I0 := SM D ⊕ Unit ⊕ ((Fin L → Bool) × (Fin s → Bool)) ⊕ Fin s ⊕ Fin s ⊕
     ((Fin L → Bool) × (Fin D → Bool) × Fin Wbits)
 have hcardL : Fintype.card (Fin L → Bool) = 2 ^ L := by
   simp [Fintype.card_pi, Finset.prod_const]
 have hcardD : Fintype.card (Fin D → Bool) = 2 ^ D := by
   simp [Fintype.card_pi, Finset.prod_const]
 have hcardS : Fintype.card (Fin s → Bool) = 2 ^ s := by
   simp [Fintype.card_pi, Finset.prod_const]
 have hT : EC (2 ^ L * (160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4))
     (fun (inp : I0 → Bool) (p : (Fin L → Bool) × (Bool × (Fin D → Bool) × Fin Wbits)) =>
       aCut D Wbits (Sum.elim (fun a => inp (inl a))
         (Sum.elim (fun _ => p.2.1) (fun r => inp (inr (inr (inr (inr (inr (p.1, r))))))))) p.2.2) := by
   have hfam := ec_family (s := 160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4)
     (f := fun (wp : Fin L → Bool) (inp : I0 → Bool) (q : Bool × (Fin D → Bool) × Fin Wbits) =>
       aCut D Wbits (Sum.elim (fun a => inp (inl a))
         (Sum.elim (fun _ => q.1) (fun r => inp (inr (inr (inr (inr (inr (wp, r))))))))) q.2)
     (fun wp => by
       have hmk : ∀ c : Bool, EC (80 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 40 * (D + 1) * (D + 1) + 2)
           (fun (inp : I0 → Bool) (r : (Fin D → Bool) × Fin Wbits) =>
             aCut D Wbits (Sum.elim (fun a => inp (inl a))
               (Sum.elim (fun _ => c) (fun r' => inp (inr (inr (inr (inr (inr (wp, r'))))))))) r) := by
         intro c
         have hin := ec_pair (ec_proj (fun a : SM D => (inl a : I0)))
           (ec_pair (ec_const (ι := I0) (fun (_ : Unit) => c))
             (ec_proj (fun r' : (Fin D → Bool) × Fin Wbits => (inr (inr (inr (inr (inr (wp, r'))))) : I0))))
         have hc := ec_comp hin (ec_aCut D Wbits)
         exact ec_le hc (by omega)
       have hp := ec_pair (hmk false) (hmk true)
       let sel : Bool × (Fin D → Bool) × Fin Wbits → ((Fin D → Bool) × Fin Wbits) ⊕ ((Fin D → Bool) × Fin Wbits) :=
         fun q => if q.1 then inr q.2 else inl q.2
       have hcomp := ec_comp hp (ec_proj sel)
       refine ec_le (ec_eq ?_ hcomp) (by
         have h1 : (80 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 40 * (D + 1) * (D + 1) + 2) +
             (80 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 40 * (D + 1) * (D + 1) + 2) + 0 =
             160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4 := by ring
         exact le_of_eq h1)
       intro inp q; cases hq : q.1 <;> simp [sel, hq])
   rw [hcardL] at hfam; exact hfam
 let I1 := I0 ⊕ ((Fin L → Bool) × (Bool × (Fin D → Bool) × Fin Wbits))
 have hokAll : EC (2 ^ s * (8 * s + 10))
     (fun (y : I1 → Bool) (ps : Fin s → Bool) =>
       decide (∀ u : Fin s, y (inl (inr (inr (inr (inl u))))) = true →
         ps u = y (inl (inr (inr (inr (inr (inl u)))))))) := by
   have hfam := ec_family (s := 8 * s + 10)
     (f := fun (ps : Fin s → Bool) (y : I1 → Bool) (_ : Unit) =>
       decide (∀ u : Fin s, y (inl (inr (inr (inr (inl u))))) = true →
         ps u = y (inl (inr (inr (inr (inr (inl u))))))))
     (fun ps => by
       have hm : EC 0 (fun (y : I1 → Bool) (u : Fin s) => y (inl (inr (inr (inr (inl u)))))) := ec_proj _
       have hv : EC 0 (fun (y : I1 → Bool) (u : Fin s) => y (inl (inr (inr (inr (inr (inl u))))))) := ec_proj _
       have heq := ec_ite_of (ec_const (ι := I1) ps) hv (ec_not_of hv)
       have himp := ec_or_of (ec_not_of hm) heq
       have hall := ec_comp himp (ec_all (α := Fin s))
       rw [Fintype.card_fin] at hall
       refine ec_le (ec_eq ?_ hall) (by omega)
       intro y u; simp only [decide_eq_decide]
       apply forall_congr'; intro b
       cases ps b <;> cases y (inl (inr (inr (inr (inl b))))) <;>
         cases y (inl (inr (inr (inr (inr (inl b)))))) <;> simp)
   rw [hcardS] at hfam
   have hp := ec_comp hfam (ec_proj (fun ps : Fin s → Bool => (ps, ())))
   rw [add_zero] at hp; exact hp
 let I2 := I1 ⊕ (Fin s → Bool)
 have hsumAll : EC (2 ^ L * 2 ^ D * (2 ^ s * (30 * Wbits + 40)))
     (fun (z : I2 → Bool) (q : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits) =>
       let wn := q.1
       let x := q.2.1
       let nxt := tBlk hsL wn
       let terms : (Fin s → Bool) × Fin Wbits → Bool := fun pb =>
         let ps := pb.1
         let wp := pWin hsL wn ps
         let ok := z (inr ps)
         let ci := xor (z (inl (inl (inr (inr (inl (wp, nxt)))))))
                       (z (inl (inl (inr (inl ())))))
         ok && (if ci then z (inl (inr (wp, (true, x, pb.2))))
                else z (inl (inr (wp, (false, x, pb.2)))))
       bvSum (α := Fin s → Bool) Wbits terms q.2.2) := by
   have hfam := ec_family (s := 2 ^ s * (30 * Wbits + 40))
     (f := fun (wx : (Fin L → Bool) × (Fin D → Bool)) (z : I2 → Bool) (b : Fin Wbits) =>
       let wn := wx.1
       let x := wx.2
       let nxt := tBlk hsL wn
       let terms : (Fin s → Bool) × Fin Wbits → Bool := fun pb =>
         let ps := pb.1
         let wp := pWin hsL wn ps
         let ok := z (inr ps)
         let ci := xor (z (inl (inl (inr (inr (inl (wp, nxt)))))))
                       (z (inl (inl (inr (inl ())))))
         ok && (if ci then z (inl (inr (wp, (true, x, pb.2))))
                else z (inl (inr (wp, (false, x, pb.2)))))
       bvSum (α := Fin s → Bool) Wbits terms b)
     (fun wx => by
       let wn := wx.1
       let x := wx.2
       let nxt := tBlk hsL wn
       have hok : EC 0 (fun (z : I2 → Bool) (pb : (Fin s → Bool) × Fin Wbits) => z (inr pb.1)) := ec_proj _
       have hpr : EC 0 (fun (z : I2 → Bool) (pb : (Fin s → Bool) × Fin Wbits) =>
           z (inl (inl (inr (inr (inl (pWin hsL wn pb.1, nxt))))))) := ec_proj _
       have hal : EC 0 (fun (z : I2 → Bool) (_ : (Fin s → Bool) × Fin Wbits) =>
           z (inl (inl (inr (inl ()))))) := ec_proj _
       have ht1 : EC 0 (fun (z : I2 → Bool) (pb : (Fin s → Bool) × Fin Wbits) =>
           z (inl (inr (pWin hsL wn pb.1, (true, x, pb.2))))) := ec_proj _
       have ht0 : EC 0 (fun (z : I2 → Bool) (pb : (Fin s → Bool) × Fin Wbits) =>
           z (inl (inr (pWin hsL wn pb.1, (false, x, pb.2))))) := ec_proj _
       have hterms := ec_and_of hok (ec_ite_of (ec_xor_of hpr hal) ht1 ht0)
       simp only [Fintype.card_prod, hcardS, Fintype.card_fin] at hterms
       have hsum := ec_comp hterms (ec_bvSum (α := Fin s → Bool) Wbits)
       rw [hcardS] at hsum
       refine ec_le hsum ?_
       have hpow : 1 ≤ 2 ^ s := Nat.one_le_two_pow
       nlinarith)
   simp only [Fintype.card_prod, hcardL, hcardD] at hfam
   have hp := ec_comp hfam (ec_proj (fun q : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits => ((q.1, q.2.1), q.2.2)))
   rw [add_zero] at hp; exact hp
 have htot := ec_let hT (ec_let hokAll hsumAll)
 refine ec_le (ec_eq ?_ htot) ?_
 · intro inp q; rfl
 · have hpowL : 1 ≤ 2 ^ L := Nat.one_le_two_pow
   have hpowD : 1 ≤ 2 ^ D := Nat.one_le_two_pow
   have hpowS : 1 ≤ 2 ^ s := Nat.one_le_two_pow
   have hdd1 : 1 ≤ (D + 1) * (D + 1) := Nat.mul_pos (by omega) (by omega)
   have h1 : 2 ^ L * (160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4) ≤
       2 ^ L * 2 ^ D * 2 ^ s * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) := by
     have ha : 160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4 ≤
         2 ^ D * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) := by
       have h1a : 160 * (D + 1) * (D + 1) * (Wbits + 1) ≤ 160 * (D + 1) * (D + 1) * (Wbits + s + 2) :=
         Nat.mul_le_mul_left _ (by omega)
       have h1b : 80 * (D + 1) * (D + 1) + 4 ≤ 84 * (D + 1) * (D + 1) := by nlinarith
       have h1c : 80 * (D + 1) * (D + 1) + 4 ≤ 2 ^ D * (84 * (D + 1) * (D + 1)) :=
         le_trans h1b (Nat.le_mul_of_pos_left _ (by omega))
       have h1d := Nat.mul_le_mul_right (2 ^ D) h1a
       calc 160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4
           ≤ 160 * (D + 1) * (D + 1) * (Wbits + s + 2) * 2 ^ D + 2 ^ D * (84 * (D + 1) * (D + 1)) := by omega
         _ = 2 ^ D * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) := by ring
     have hb := Nat.mul_le_mul_left (2 ^ L) ha
     have hc := Nat.le_mul_of_pos_right (2 ^ L * 2 ^ D) (by omega : 0 < 2 ^ s)
     have hd := Nat.mul_le_mul_right (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) hc
     calc 2 ^ L * (160 * (D + 1) * (D + 1) * (Wbits + 1) * 2 ^ D + 80 * (D + 1) * (D + 1) + 4)
         ≤ 2 ^ L * (2 ^ D * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1))) := hb
       _ = 2 ^ L * 2 ^ D * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) := by ring
       _ ≤ 2 ^ L * 2 ^ D * 2 ^ s * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) := hd
   have h2 : 2 ^ s * (8 * s + 10) ≤ 2 ^ L * 2 ^ D * 2 ^ s * (10 * (D + 1) * (D + 1) * (Wbits + s + 2)) := by
     have ha : 8 * s + 10 ≤ 10 * (D + 1) * (D + 1) * (Wbits + s + 2) := by
       have h2a : 8 * s + 10 ≤ 10 * (Wbits + s + 2) := by omega
       have h2b : 10 * (Wbits + s + 2) ≤ (D + 1) * (D + 1) * (10 * (Wbits + s + 2)) := Nat.le_mul_of_pos_left _ hdd1
       calc 8 * s + 10 ≤ (D + 1) * (D + 1) * (10 * (Wbits + s + 2)) := le_trans h2a h2b
         _ = 10 * (D + 1) * (D + 1) * (Wbits + s + 2) := by ring
     have hb : 2 ^ s ≤ 2 ^ L * 2 ^ D * 2 ^ s := by
       have hLD : 1 ≤ 2 ^ L * 2 ^ D := Nat.mul_pos hpowL hpowD
       exact Nat.le_mul_of_pos_left (2 ^ s) hLD |> (fun h => by linarith only [h])
     exact Nat.mul_le_mul hb ha
   have h3 : 2 ^ L * 2 ^ D * (2 ^ s * (30 * Wbits + 40)) ≤
       2 ^ L * 2 ^ D * 2 ^ s * (30 * (D + 1) * (D + 1) * (Wbits + s + 2) + 36 * (D + 1) * (D + 1)) := by
     have ha : 30 * Wbits + 40 ≤ 30 * (D + 1) * (D + 1) * (Wbits + s + 2) + 36 * (D + 1) * (D + 1) := by
       have h3a : 30 * Wbits + 40 ≤ 30 * (Wbits + s + 2) := by omega
       have h3b : 30 * (Wbits + s + 2) ≤ (D + 1) * (D + 1) * (30 * (Wbits + s + 2)) := Nat.le_mul_of_pos_left _ hdd1
       have h3c : 30 * Wbits + 40 ≤ 30 * (D + 1) * (D + 1) * (Wbits + s + 2) := by
         calc 30 * Wbits + 40 ≤ (D + 1) * (D + 1) * (30 * (Wbits + s + 2)) := le_trans h3a h3b
           _ = 30 * (D + 1) * (D + 1) * (Wbits + s + 2) := by ring
       omega
     calc 2 ^ L * 2 ^ D * (2 ^ s * (30 * Wbits + 40))
         = 2 ^ L * 2 ^ D * 2 ^ s * (30 * Wbits + 40) := by ring
       _ ≤ 2 ^ L * 2 ^ D * 2 ^ s * (30 * (D + 1) * (D + 1) * (Wbits + s + 2) + 36 * (D + 1) * (D + 1)) :=
           Nat.mul_le_mul_left _ ha
   have htot_eq :
       2 ^ L * 2 ^ D * 2 ^ s * (160 * (D + 1) * (D + 1) * (Wbits + s + 2) + 84 * (D + 1) * (D + 1)) +
       2 ^ L * 2 ^ D * 2 ^ s * (10 * (D + 1) * (D + 1) * (Wbits + s + 2)) +
       2 ^ L * 2 ^ D * 2 ^ s * (30 * (D + 1) * (D + 1) * (Wbits + s + 2) + 36 * (D + 1) * (D + 1)) =
       2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (Wbits + s + 2) + 120 * (D + 1) * (D + 1)) := by ring
   linarith only [h1, h2, h3, htot_eq]
noncomputable def cDS (e s d a : ℕ) (hsL : s ≤ d + 1 - s) (seam : Fin (d + 1 - s) → Bool)
   (inp : FOut e s d a ⊕ (Fin (3 * (e + 1)) × Fin s) ⊕ (Fin (3 * (e + 1)) × Fin s) → Bool) :
   Fin (3 * (e + 1) * s + 1) → Bool :=
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let L := d + 1 - s
 let Wbits := k + 1
 let fo : FOut e s d a → Bool := fun x => inp (inl x)
 let maskOff : Fin q × Fin s → Bool := fun p => inp (inr (inl p))
 let valOff : Fin q × Fin s → Bool := fun p => inp (inr (inr p))
 let alpha : Fin q → Bool := fun i => fo (inr (inl i))
 let mds : Fin q × SM D → Bool := fun p => fo (inr (inr (inl p)))
 let probeTbl : Fin q × (Fin L → Bool) × (Fin s → Bool) → Bool := fun p => fo (inr (inr (inr (inl p))))
 let initDP : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits → Bool := fun p =>
   decide (p.1 = seam ∧ p.2.1 = (fun _ => false) ∧ p.2.2.val = 0)
 let finalDP := (List.finRange q).foldl
   (fun dp i =>
     dpStep L s D Wbits hsL
       (Sum.elim (fun x => mds (i, x))
         (Sum.elim (fun _ => alpha i)
           (Sum.elim (fun p => probeTbl (i, p))
             (Sum.elim (fun u => maskOff (i, u))
               (Sum.elim (fun u => valOff (i, u)) dp))))))
   initDP
 fun b => finalDP (seam, (fun _ => false), b)
lemma ec_cDS (e s d a : ℕ) (hsL : s ≤ d + 1 - s) (seam : Fin (d + 1 - s) → Bool) :
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let L := d + 1 - s
   EC (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1))))
     (cDS e s d a hsL seam) := by
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let L := d + 1 - s
 let Wbits := k + 1
 let I := FOut e s d a ⊕ (Fin q × Fin s) ⊕ (Fin q × Fin s)
 let A := (Fin L → Bool) × (Fin D → Bool) × Fin Wbits
 let stepCost := 2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (Wbits + s + 2) + 120 * (D + 1) * (D + 1))
 have htake : ∀ t : ℕ,
     EC (2 + t * stepCost)
       (fun (inp : I → Bool) =>
         ((List.finRange q).take t).foldl
           (fun dp i =>
             dpStep L s D Wbits hsL
               (Sum.elim (fun x => inp (inl (inr (inr (inl (i, x))))))
                 (Sum.elim (fun _ => inp (inl (inr (inl i))))
                   (Sum.elim (fun p => inp (inl (inr (inr (inr (inl (i, p)))))))
                     (Sum.elim (fun u => inp (inr (inl (i, u))))
                       (Sum.elim (fun u => inp (inr (inr (i, u)))) dp))))))
           (fun p : A => decide (p.1 = seam ∧ p.2.1 = (fun _ => false) ∧ p.2.2.val = 0))) := by
   intro t
   induction t with
   | zero => simpa using ec_const (ι := I) (fun p : A => decide (p.1 = seam ∧ p.2.1 = (fun _ => false) ∧ p.2.2.val = 0))
   | succ t ih =>
     by_cases ht : t < q
     · let ii : Fin q := ⟨t, ht⟩
       let sel : SM D ⊕ Unit ⊕ ((Fin L → Bool) × (Fin s → Bool)) ⊕ Fin s ⊕ Fin s ⊕ A → I ⊕ A :=
         Sum.elim (fun x => inl (inl (inr (inr (inl (ii, x))))))
           (Sum.elim (fun _ => inl (inl (inr (inl ii))))
             (Sum.elim (fun p => inl (inl (inr (inr (inr (inl (ii, p)))))))
               (Sum.elim (fun u => inl (inr (inl (ii, u))))
                 (Sum.elim (fun u => inl (inr (inr (ii, u)))) (fun r => inr r)))))
       have hstep := ec_comp (ec_proj sel) (ec_dpStep L s D Wbits hsL)
       rw [zero_add] at hstep
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) (by change 2 + t * stepCost + stepCost ≤ 2 + (t + 1) * stepCost; rw [Nat.succ_mul, Nat.add_assoc])
       intro inp p
       have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t ++ [ii] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange q) (i := t) (by simp; omega)
         simpa [ii] using h1
       simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
       congr 1; funext x; rcases x with _ | _ | _ | _ | _ | _ <;> rfl
     · have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t := by
         rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
       refine ec_le (ec_eq ?_ ih) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ t)) 2)
       intro inp p; simp only [htk]
 have hq := htake q
 rw [show (List.finRange q).take q = List.finRange q by rw [List.take_of_length_le]; simp] at hq
 have hp := ec_comp hq (ec_proj (fun b : Fin Wbits => (seam, (fun _ => false), b)))
 rw [add_zero] at hp
 refine ec_le hp ?_
 have hW : Wbits + s + 2 = k + s + 3 := by dsimp [Wbits]; omega
 dsimp only [stepCost]; rw [hW]
noncomputable def cDR (e s d a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s)
   (inp : FOut e s d a ⊕ Fin (3 * (e + 1) * s) ⊕ Fin (3 * (e + 1) * s) → Bool) :
   Fin (3 * (e + 1) * s + 1) → Bool :=
 let q := 3 * (e + 1)
 let k := q * s
 let L := d + 1 - s
 let fo : FOut e s d a → Bool := fun x => inp (inl x)
 let maskF : Fin k → Bool := fun b => inp (inr (inl b))
 let valF : Fin k → Bool := fun b => inp (inr (inr b))
 let eqOff : Fin k → Bool := fun o => fo (inr (inr (inr (inr o))))
 let maskOff : Fin q × Fin s → Bool := fun p =>
   decide (∃ o : Fin k, eqOff o = true ∧ maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true)
 let valOff : Fin q × Fin s → Bool := fun p =>
   decide (∃ o : Fin k, eqOff o = true ∧ valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true)
 let seamRes : (Fin L → Bool) × Fin (k + 1) → Bool := fun pb =>
   cDS e s d a hsL pb.1 (Sum.elim fo (Sum.elim maskOff valOff)) pb.2
 bvSum (α := Fin L → Bool) (k + 1) seamRes
lemma ec_cDR (e s d a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s) :
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let L := d + 1 - s
   EC (
     2 * k * (3 * k + 5) +
     2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
     (2 + 2 ^ L * (20 * (k + 2)))
   ) (cDR e s d a hk hsL) := by
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let L := d + 1 - s
 let I0 := FOut e s d a ⊕ Fin k ⊕ Fin k
 have hcardL : Fintype.card (Fin L → Bool) = 2 ^ L := by
   simp [Fintype.card_pi, Finset.prod_const]
 have hmv : EC (2 * k * (3 * k + 5))
     (fun (inp : I0 → Bool) =>
       let eqOff := fun o => inp (inl (inr (inr (inr (inr o)))))
       let maskOff : Fin q × Fin s → Bool := fun p =>
         decide (∃ o : Fin k, eqOff o = true ∧ inp (inr (inl ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩)) = true)
       let valOff : Fin q × Fin s → Bool := fun p =>
         decide (∃ o : Fin k, eqOff o = true ∧ inp (inr (inr ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩)) = true)
       Sum.elim maskOff valOff) := by
   have hmk : ∀ isVal : Bool, EC (k * (3 * k + 5))
       (fun (inp : I0 → Bool) (p : Fin q × Fin s) =>
         decide (∃ o : Fin k, inp (inl (inr (inr (inr (inr o))))) = true ∧
           (if isVal then inp (inr (inr ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))
            else inp (inr (inl ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))) = true)) := by
     intro isVal
     have hfam := ec_family (s := 3 * k + 5)
       (f := fun (p : Fin q × Fin s) (inp : I0 → Bool) (_ : Unit) =>
         decide (∃ o : Fin k, inp (inl (inr (inr (inr (inr o))))) = true ∧
           (if isVal then inp (inr (inr ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))
            else inp (inr (inl ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))) = true))
       (fun p => by
         have h1 : EC 0 (fun (inp : I0 → Bool) (o : Fin k) => inp (inl (inr (inr (inr (inr o)))))) := ec_proj _
         have h2 : EC 0 (fun (inp : I0 → Bool) (o : Fin k) =>
             if isVal then inp (inr (inr ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))
             else inp (inr (inl ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩))) := by
           cases isVal <;> exact ec_proj _
         have hand := ec_and_of h1 h2
         have hany := ec_comp hand (ec_any (α := Fin k))
         rw [Fintype.card_fin] at hany
         exact ec_le (ec_eq (fun inp u => by simp [Bool.and_eq_true]) hany) (by omega))
     simp only [Fintype.card_prod, Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun p : Fin q × Fin s => (p, ())))
     rw [add_zero] at hp; exact hp
   have hp := ec_pair (hmk false) (hmk true)
   refine ec_le (ec_eq ?_ hp) (by dsimp only [k]; ring_nf; omega)
   intro inp q0; rcases q0 with p | p <;> rfl
 let I1 := I0 ⊕ ((Fin q × Fin s) ⊕ (Fin q × Fin s))
 let seamCost := 2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))
 have hseams : EC (2 ^ L * seamCost)
     (fun (y : I1 → Bool) (pb : (Fin L → Bool) × Fin (k + 1)) =>
       cDS e s d a hsL pb.1 (Sum.elim (fun x => y (inl (inl x))) (fun p => y (inr p))) pb.2) := by
   have hfam := ec_family (s := seamCost)
     (f := fun (seam : Fin L → Bool) (y : I1 → Bool) (b : Fin (k + 1)) =>
       cDS e s d a hsL seam (Sum.elim (fun x => y (inl (inl x))) (fun p => y (inr p))) b)
     (fun seam => by
       let sel : FOut e s d a ⊕ (Fin q × Fin s) ⊕ (Fin q × Fin s) → I1 :=
         Sum.elim (fun x => inl (inl x)) (fun p => inr p)
       have h := ec_comp (ec_proj sel) (ec_cDS e s d a hsL seam)
       rw [zero_add] at h
       refine ec_eq ?_ h
       intro y b; congr 1; funext x; rcases x with _ | _ | _ <;> rfl)
   rw [hcardL] at hfam; exact hfam
 have hsum := ec_comp hseams (ec_bvSum (α := Fin L → Bool) (k + 1))
 rw [hcardL] at hsum
 have htot := ec_let hmv hsum
 refine ec_le (ec_eq ?_ htot) (le_of_eq (Nat.add_assoc _ _ _).symm)
 intro inp b; rfl
def winAt {L s : ℕ} (hsL : s ≤ L) (seam : Fin L → Bool) :
   ∀ {t : ℕ}, (Fin t → Fin s → Bool) → Fin L → Bool
 | 0, _ => seam
 | t + 1, seq => sWin hsL (winAt hsL seam (fun i : Fin t => seq i.castSucc)) (seq (Fin.last t))
lemma card_seq_le {s : ℕ} (t : ℕ) : Fintype.card (Fin t → Fin s → Bool) = 2 ^ (t * s) := by
 simp [Fintype.card_pi, Finset.prod_const, ← pow_mul, mul_comm]
open Classical in
lemma dpStep_spec {L s D m Wbits : ℕ} (hsL : s ≤ L)
   {I I' : Submodule (ZMod 2) (Fin m → ZMod 2)}
   {st stNext : BSt D m → Bool}
   {vi : Fin m → ZMod 2} {md : SM D → Bool}
   (hinv : BInv I st) (hinvNext : BInv I' stNext)
   (hrel : SMR I st stNext vi md)
   (alpha_i : Bool) (probe_i : (Fin L → Bool) × (Fin s → Bool) → Bool)
   (mask_i val_i : Fin s → Bool)
   (dp : (Fin L → Bool) × (Fin D → Bool) × Fin Wbits → Bool)
   (hsupp : ∀ wp x, ¬ cVal st x → ∀ b, dp (wp, x, b) = false)
   (hlt : ∀ (wn : Fin L → Bool) (x : Fin D → Bool),
     ∑ ps : Fin s → Bool,
       (if (∀ u : Fin s, mask_i u = true → ps u = val_i u) then
         ∑ xp : Fin D → Bool,
           if cVal st xp ∧ bDc st xp + b2z (xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i) • vi = bDc stNext x
           then bNat Wbits (fun b => dp (pWin hsL wn ps, xp, b)) else 0
       else 0) < 2 ^ Wbits) :
   let dpN := dpStep L s D Wbits hsL
     (Sum.elim md (Sum.elim (fun _ => alpha_i) (Sum.elim probe_i (Sum.elim mask_i (Sum.elim val_i dp)))))
   (∀ wn x, ¬ cVal stNext x → ∀ b, dpN (wn, x, b) = false) ∧
   (∀ wn x, cVal stNext x →
     bNat Wbits (fun b => dpN (wn, x, b)) =
       ∑ ps : Fin s → Bool,
         if (∀ u : Fin s, mask_i u = true → ps u = val_i u) then
           ∑ xp : Fin D → Bool,
             if cVal st xp ∧ bDc st xp + b2z (xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i) • vi = bDc stNext x
             then bNat Wbits (fun b => dp (pWin hsL wn ps, xp, b)) else 0
         else 0) := by
 dsimp only [dpStep, Sum.elim_inl, Sum.elim_inr]
 have hT_spec : ∀ (wp : Fin L → Bool) (ci : Bool),
     let out := aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) (fun r => dp (wp, r))))
     (∀ x, ¬ cVal stNext x → ∀ b, out (x, b) = false) ∧
     (∀ x, cVal stNext x → ∀ b,
       (∀ xp, cVal st xp → bDc st xp + b2z ci • vi = bDc stNext x → out (x, b) = dp (wp, xp, b)) ∧
       ((¬ ∃ xp, cVal st xp ∧ bDc st xp + b2z ci • vi = bDc stNext x) → out (x, b) = false)) :=
   fun wp ci => aCut_sp hinv hinvNext hrel ci (fun r => dp (wp, r)) (fun x hnv b => hsupp wp x hnv b)
 constructor
 · intro wn x hnv b
   have hall0 : ∀ (ps : Fin s → Bool) (b0 : Fin Wbits),
       (decide (∀ u : Fin s, mask_i u = true → ps u = val_i u) &&
         (if xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i = true then
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (pWin hsL wn ps, r)))) (x, b0)
         else
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (pWin hsL wn ps, r)))) (x, b0))) = false := by
     intro ps b0
     cases xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i
     · simp only [Bool.false_eq_true, ↓reduceIte, (hT_spec (pWin hsL wn ps) false).1 x hnv b0, Bool.and_false]
     · simp only [↓reduceIte, (hT_spec (pWin hsL wn ps) true).1 x hnv b0, Bool.and_false]
   have hsum0 : bNat Wbits (bvSum (α := Fin s → Bool) Wbits (fun pb =>
       decide (∀ u : Fin s, mask_i u = true → pb.1 u = val_i u) &&
         (if xor (probe_i (pWin hsL wn pb.1, tBlk hsL wn)) alpha_i = true then
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (pWin hsL wn pb.1, r)))) (x, pb.2)
         else
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (pWin hsL wn pb.1, r)))) (x, pb.2)))) = 0 := by
     rw [bNat_bS_lt]
     · apply Finset.sum_eq_zero; intro ps _
       simp only [bNat, hall0 ps, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero]
     · have h0 : ∑ ps : Fin s → Bool, bNat Wbits (fun b0 =>
           decide (∀ u : Fin s, mask_i u = true → ps u = val_i u) &&
             (if xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i = true then
               aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (pWin hsL wn ps, r)))) (x, b0)
             else
               aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (pWin hsL wn ps, r)))) (x, b0))) = 0 := by
         apply Finset.sum_eq_zero; intro ps _
         simp only [bNat, hall0 ps, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero]
       rw [h0]; exact Nat.pos_of_ne_zero (by positivity)
   have htb := bNat_tb Wbits (bvSum (α := Fin s → Bool) Wbits (fun pb =>
       decide (∀ u : Fin s, mask_i u = true → pb.1 u = val_i u) &&
         (if xor (probe_i (pWin hsL wn pb.1, tBlk hsL wn)) alpha_i = true then
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (pWin hsL wn pb.1, r)))) (x, pb.2)
         else
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (pWin hsL wn pb.1, r)))) (x, pb.2)))) b
   rw [hsum0, Nat.zero_testBit] at htb
   exact htb.symm
 · intro wn x hx
   have hterm_eq : ∀ ps : Fin s → Bool,
       bNat Wbits (fun b0 =>
         decide (∀ u : Fin s, mask_i u = true → ps u = val_i u) &&
           (if xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i = true then
             aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (pWin hsL wn ps, r)))) (x, b0)
           else
             aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (pWin hsL wn ps, r)))) (x, b0))) =
       if (∀ u : Fin s, mask_i u = true → ps u = val_i u) then
         ∑ xp : Fin D → Bool,
           if cVal st xp ∧ bDc st xp + b2z (xor (probe_i (pWin hsL wn ps, tBlk hsL wn)) alpha_i) • vi = bDc stNext x
           then bNat Wbits (fun b => dp (pWin hsL wn ps, xp, b)) else 0
       else 0 := by
     intro ps
     let wp := pWin hsL wn ps
     let ci := xor (probe_i (wp, tBlk hsL wn)) alpha_i
     by_cases hok : ∀ u : Fin s, mask_i u = true → ps u = val_i u
     · conv_rhs => rw [ite_eq_left_iff.mpr (fun hn => absurd hok hn)]
       rw [decide_eq_true hok]; simp only [Bool.true_and]
       have hif : (fun b0 => if ci = true then
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => true) (fun r => dp (wp, r)))) (x, b0)
         else
           aCut D Wbits (Sum.elim md (Sum.elim (fun _ => false) (fun r => dp (wp, r)))) (x, b0)) =
           fun b0 => aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) (fun r => dp (wp, r)))) (x, b0) := by
         funext b0; cases ci <;> rfl
       rw [hif]
       by_cases hex : ∃ xp : Fin D → Bool, cVal st xp ∧ bDc st xp + b2z ci • vi = bDc stNext x
       · obtain ⟨xp0, hxp0_v, hxp0_e⟩ := hex
         have hout_eq : (fun b0 => aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) (fun r => dp (wp, r)))) (x, b0)) =
             fun b0 => dp (wp, xp0, b0) :=
           funext (fun b0 => ((hT_spec wp ci).2 x hx b0).1 xp0 hxp0_v hxp0_e)
         rw [hout_eq]
         symm
         rw [Finset.sum_eq_single xp0]
         · split_ifs with h
           · rfl
           · exact absurd ⟨hxp0_v, hxp0_e⟩ h
         · intro xp' _ hne
           have hnot : ¬ (cVal st xp' ∧ bDc st xp' + b2z ci • vi = bDc stNext x) := by
             rintro ⟨hv', he'⟩
             exact hne (bsDec_inj hinv hv' hxp0_v (add_right_cancel (he'.trans hxp0_e.symm)))
           split_ifs with h
           · exact absurd h hnot
           · rfl
         · intro hm; exact absurd (Finset.mem_univ _) hm
       · have hout0 : ∀ b0, aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) (fun r => dp (wp, r)))) (x, b0) = false :=
           fun b0 => ((hT_spec wp ci).2 x hx b0).2 hex
         have h0 : bNat Wbits (fun b0 => aCut D Wbits (Sum.elim md (Sum.elim (fun _ => ci) (fun r => dp (wp, r)))) (x, b0)) = 0 := by
           simp only [bNat, hout0, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero]
         rw [h0]; symm
         apply Finset.sum_eq_zero; intro xp' _
         have hnot : ¬ (cVal st xp' ∧ bDc st xp' + b2z ci • vi = bDc stNext x) := fun h => hex ⟨xp', h⟩
         split_ifs with h
         · exact absurd h hnot
         · rfl
     · conv_rhs => rw [ite_eq_right_iff.mpr (fun hp => absurd hp hok)]
       rw [decide_eq_false hok]; simp only [Bool.false_and]
       simp only [bNat, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero]
   rw [bNat_bS_lt]
   · exact Finset.sum_congr rfl (fun ps _ => hterm_eq ps)
   · convert hlt wn x using 1
     exact Finset.sum_congr rfl (fun ps _ => hterm_eq ps)
open Classical in
lemma cDS_sp {n e s d a : ℕ} (hsL : s ≤ d + 1 - s)
   (Pmat : Fin (3 * (e + 1)) × Fin (2 * n + 1) → Bool)
   (alpha : Fin (3 * (e + 1)) → Bool)
   (probeTbl : Fin (3 * (e + 1)) × (Fin (d + 1 - s) → Bool) × (Fin s → Bool) → Bool)
   (eqOff : Fin (3 * (e + 1) * s) → Bool)
   (maskOff valOff : Fin (3 * (e + 1)) × Fin s → Bool)
   (validAll : Bool) (seam : Fin (d + 1 - s) → Bool)
   (hnoOver : ∀ i : Fin (3 * (e + 1)),
     sOv (fun x => rBC (3 * (e + 1)) (1 + 2 * a) (2 * n + 1)
       (Sum.elim Pmat (bSN (3 * (e + 1)) (2 * n + 1) Pmat)) (inr (i, x))) = false) :
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let m := 2 * n + 1
   let Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
   let mds : Fin q × SM D → Bool := fun p =>
     rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr p)
   let fo : FOut e s d a → Bool :=
     Sum.elim (fun _ => validAll) (Sum.elim alpha (Sum.elim mds (Sum.elim probeTbl eqOff)))
   bNat (k + 1) (cDS e s d a hsL seam (Sum.elim fo (Sum.elim maskOff valOff))) =
     Nat.card { seq : Fin q → Fin s → Bool //
       winAt hsL seam seq = seam ∧
       (∀ i : Fin q, ∀ u : Fin s, maskOff (i, u) = true →
         hBlk hsL (winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, lt_trans j.isLt i.isLt⟩)) u = valOff (i, u)) ∧
       (∑ i : Fin q, b2z (xor (probeTbl (i,
         winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, lt_trans j.isLt i.isLt⟩), seq i)) (alpha i)) • Pvec i = 0) } := by
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let m := 2 * n + 1
 let L := d + 1 - s
 let Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
 let Nall := bSN q m Pmat
 let mds : Fin q × SM D → Bool := fun p => rBC q D m (Sum.elim Pmat Nall) (inr p)
 let stAt : ℕ → BSt D m → Bool := fun t x => cPfx q D m Pmat Nall t (inl x)
 obtain ⟨hinv_all, hrel_all⟩ := (rBC_sp (D := D) Pmat).2 hnoOver
 let dpAt : ℕ → (Fin L → Bool) × (Fin D → Bool) × Fin (k + 1) → Bool := fun t =>
   ((List.finRange q).take t).foldl
     (fun dp i =>
       dpStep L s D (k + 1) hsL
         (Sum.elim (fun x => mds (i, x))
           (Sum.elim (fun _ => alpha i)
             (Sum.elim (fun p => probeTbl (i, p))
               (Sum.elim (fun u => maskOff (i, u))
                 (Sum.elim (fun u => valOff (i, u)) dp))))))
     (fun p => decide (p.1 = seam ∧ p.2.1 = (fun _ => false) ∧ p.2.2.val = 0))
 let goodSeq : ∀ (t : ℕ), t ≤ q → (Fin L → Bool) → (Fin D → Bool) → (Fin t → Fin s → Bool) → Prop :=
   fun t ht wn x seq =>
     winAt hsL seam seq = wn ∧
     (∀ i : Fin t, ∀ u : Fin s, maskOff (⟨i.val, lt_of_lt_of_le i.isLt ht⟩, u) = true →
       hBlk hsL (winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, lt_trans j.isLt i.isLt⟩)) u =
         valOff (⟨i.val, lt_of_lt_of_le i.isLt ht⟩, u)) ∧
     (∀ (u : ℕ) (hu : u ≤ t),
       (∑ i : Fin u, b2z (xor (probeTbl (⟨i.val, by have := i.isLt; omega⟩,
         winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩), seq ⟨i.val, by have := i.isLt; omega⟩))
         (alpha ⟨i.val, by have := i.isLt; omega⟩)) • Pvec ⟨i.val, by have := i.isLt; omega⟩) ∈ Lsub Pvec u ⊓ Rsub Pvec u) ∧
     (∑ i : Fin t, b2z (xor (probeTbl (⟨i.val, lt_of_lt_of_le i.isLt ht⟩,
       winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, lt_trans j.isLt i.isLt⟩), seq i))
       (alpha ⟨i.val, lt_of_lt_of_le i.isLt ht⟩)) • Pvec ⟨i.val, lt_of_lt_of_le i.isLt ht⟩ = bDc (stAt t) x)
 have hind : ∀ (t : ℕ) (ht : t ≤ q),
     (∀ wn x, ¬ cVal (stAt t) x → ∀ b, dpAt t (wn, x, b) = false) ∧
     (∀ wn x, cVal (stAt t) x →
       bNat (k + 1) (fun b => dpAt t (wn, x, b)) =
         Fintype.card { seq : Fin t → Fin s → Bool // goodSeq t ht wn x seq }) := by
   intro t
   induction t with
   | zero =>
     intro ht
     have hst0 : stAt 0 = fun _ => false := rfl
     have hcv0 : ∀ x : Fin D → Bool, cVal (stAt 0) x ↔ x = (fun _ => false) := fun x => by
       constructor
       · intro hx; funext l; exact hx l rfl
       · intro heq l _; rw [heq]
     constructor
     · intro wn x hnv b
       have hne : x ≠ (fun _ => false) := fun h => hnv ((hcv0 x).mpr h)
       change decide (wn = seam ∧ x = (fun _ => false) ∧ b.val = 0) = false
       simp [hne]
     · intro wn x hx
       have hx0 : x = (fun _ => false) := (hcv0 x).mp hx
       subst hx0
       by_cases hws : wn = seam
       · subst wn
         have hbits : bNat (k + 1) (fun b => decide (seam = seam ∧ (fun _ : Fin D => false) = (fun _ => false) ∧ b.val = 0)) = 1 := by
           unfold bNat
           rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (k + 1))]
           · simp
           · intro b _ hne
             have hb0 : b.val ≠ 0 := fun h => hne (Fin.ext h)
             simp [hb0]
           · intro hm; exact absurd (Finset.mem_univ _) hm
         change bNat (k + 1) (fun b => decide (seam = seam ∧ (fun _ : Fin D => false) = (fun _ => false) ∧ b.val = 0)) = _
         rw [hbits]
         symm
         have huniq : Unique { seq : Fin 0 → Fin s → Bool // goodSeq 0 ht seam (fun _ => false) seq } :=
           { default := ⟨Fin.elim0, rfl, fun i => i.elim0, fun u hu => by
               have hu0 : u = 0 := by omega
               subst hu0; simp [Lsub_zero], by funext j; simp [bDc, b2z]⟩
             uniq := fun ⟨f, _⟩ => Subtype.ext (funext (fun i => i.elim0)) }
         exact Fintype.card_unique
       · have hbits : bNat (k + 1) (fun b => decide (wn = seam ∧ (fun _ : Fin D => false) = (fun _ => false) ∧ b.val = 0)) = 0 := by
           unfold bNat; apply Finset.sum_eq_zero; intro b _; simp [hws]
         change bNat (k + 1) (fun b => decide (wn = seam ∧ (fun _ : Fin D => false) = (fun _ => false) ∧ b.val = 0)) = _
         rw [hbits]
         symm
         have hempty : IsEmpty { seq : Fin 0 → Fin s → Bool // goodSeq 0 ht wn (fun _ => false) seq } :=
           ⟨fun ⟨_, h⟩ => hws h.1.symm⟩
         exact Fintype.card_eq_zero
   | succ t ih =>
     intro ht
     obtain ⟨ih_supp, ih_cnt⟩ := ih (by omega)
     let ii : Fin q := ⟨t, ht⟩
     have hdp_eq : dpAt (t + 1) = dpStep L s D (k + 1) hsL
         (Sum.elim (fun x => mds (ii, x))
           (Sum.elim (fun _ => alpha ii)
             (Sum.elim (fun p => probeTbl (ii, p))
               (Sum.elim (fun u => maskOff (ii, u))
                 (Sum.elim (fun u => valOff (ii, u)) (dpAt t)))))) := by
       dsimp only [dpAt]
       have htk : (List.finRange q).take (t + 1) = (List.finRange q).take t ++ [ii] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange q) (i := t) (by simp; omega)
         simpa [ii] using h1
       rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
     have hsum_eq_card : ∀ (wn : Fin L → Bool) (x : Fin D → Bool), cVal (stAt (t + 1)) x →
         (∑ ps : Fin s → Bool,
           if (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) then
             ∑ xp : Fin D → Bool,
               if cVal (stAt t) xp ∧
                   bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                     bDc (stAt (t + 1)) x
               then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0
           else 0) =
         Fintype.card { seq : Fin (t + 1) → Fin s → Bool // goodSeq (t + 1) ht wn x seq } := by
       intro wn x hx
       have hinner : ∀ ps : Fin s → Bool,
           (∑ xp : Fin D → Bool,
             if cVal (stAt t) xp ∧
                 bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                   bDc (stAt (t + 1)) x
             then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) =
           Fintype.card { seq0 : Fin t → Fin s → Bool //
             ∃ xp : Fin D → Bool, cVal (stAt t) xp ∧
               bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                 bDc (stAt (t + 1)) x ∧
               goodSeq t (by omega) (pWin hsL wn ps) xp seq0 } := by
         intro ps
         have h1 : ∀ xp : Fin D → Bool,
             (if cVal (stAt t) xp ∧
                 bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                   bDc (stAt (t + 1)) x
             then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) =
             Fintype.card { seq0 : Fin t → Fin s → Bool //
               cVal (stAt t) xp ∧
               bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                 bDc (stAt (t + 1)) x ∧
               goodSeq t (by omega) (pWin hsL wn ps) xp seq0 } := by
           intro xp
           split_ifs with hc
           · rw [ih_cnt (pWin hsL wn ps) xp hc.1]
             exact Fintype.card_congr
               { toFun := fun s0 => ⟨s0.1, hc.1, hc.2, s0.2⟩
                 invFun := fun s0 => ⟨s0.1, s0.2.2.2⟩
                 left_inv := fun _ => rfl
                 right_inv := fun _ => rfl }
           · symm; exact Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, h1, h2, _⟩ => hc ⟨h1, h2⟩⟩
         simp_rw [h1]
         rw [← Fintype.card_sigma]
         refine Fintype.card_congr
           { toFun := fun ⟨xp, ⟨seq0, h1, h2, h3⟩⟩ => ⟨seq0, xp, h1, h2, h3⟩
             invFun := fun ⟨seq0, h⟩ => ⟨Classical.choose h, ⟨seq0, Classical.choose_spec h⟩⟩
             left_inv := fun ⟨xp, ⟨seq0, h1, h2, h3⟩⟩ => by
               let Pex : (Fin D → Bool) → Prop := fun xp' =>
                 cVal (stAt t) xp' ∧
                 bDc (stAt t) xp' + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                   bDc (stAt (t + 1)) x ∧
                 goodSeq t (by omega) (pWin hsL wn ps) xp' seq0
               have hhex : ∃ xp', Pex xp' := ⟨xp, h1, h2, h3⟩
               have hspec := Classical.choose_spec hhex
               have heq : Classical.choose hhex = xp :=
                 bsDec_inj (hinv_all t (by omega)) hspec.1 h1 (add_right_cancel (hspec.2.1.trans h2.symm))
               exact Sigma.ext heq (by subst heq; rfl)
             right_inv := fun ⟨seq0, h⟩ => rfl }
       have houter : (∑ ps : Fin s → Bool,
           if (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) then
             Fintype.card { seq0 : Fin t → Fin s → Bool //
               ∃ xp : Fin D → Bool, cVal (stAt t) xp ∧
                 bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                   bDc (stAt (t + 1)) x ∧
                 goodSeq t (by omega) (pWin hsL wn ps) xp seq0 }
           else 0) =
           Fintype.card { seq : Fin (t + 1) → Fin s → Bool // goodSeq (t + 1) ht wn x seq } := by
         have h2 : ∀ ps : Fin s → Bool,
             (if (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) then
               Fintype.card { seq0 : Fin t → Fin s → Bool //
                 ∃ xp : Fin D → Bool, cVal (stAt t) xp ∧
                   bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                     bDc (stAt (t + 1)) x ∧
                   goodSeq t (by omega) (pWin hsL wn ps) xp seq0 }
             else 0) =
             Fintype.card { seq0 : Fin t → Fin s → Bool //
               (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) ∧
               ∃ xp : Fin D → Bool, cVal (stAt t) xp ∧
                 bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                   bDc (stAt (t + 1)) x ∧
                 goodSeq t (by omega) (pWin hsL wn ps) xp seq0 } := by
           intro ps
           split_ifs with hm
           · exact Fintype.card_congr
               { toFun := fun s0 => ⟨s0.1, hm, s0.2⟩
                 invFun := fun s0 => ⟨s0.1, s0.2.2⟩
                 left_inv := fun _ => rfl
                 right_inv := fun _ => rfl }
           · symm; exact Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, h1, _⟩ => hm h1⟩
         simp_rw [h2]
         rw [← Fintype.card_sigma]
         refine Fintype.card_congr
           { toFun := fun ⟨ps, ⟨seq0, hmask, hex⟩⟩ =>
               ⟨Fin.snoc seq0 (tBlk hsL wn), by
                 obtain ⟨xp, hxp_v, hxp_e, hg0⟩ := hex
                 have hcast : (fun j : Fin t => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) j.castSucc) = seq0 :=
                   funext (fun j => Fin.snoc_castSucc (α := fun _ => Fin s → Bool) (tBlk hsL wn) seq0 j)
                 have hlast : (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) (Fin.last t) = tBlk hsL wn := by
                   simp [Fin.snoc_last]
                 have hw_eq : winAt hsL seam (Fin.snoc seq0 (tBlk hsL wn)) = wn := by
                   dsimp only [winAt]; rw [hcast, hlast, hg0.1]
                   exact (shiftWin_iff hsL _ wn _).mpr ⟨by rw [headBlk_prevWin], rfl⟩
                 have hsum_split : ∀ (u : ℕ) (hu : u ≤ t),
                     (∑ i : Fin u, b2z (xor (probeTbl (⟨i.val, by have := i.isLt; omega⟩,
                       winAt hsL seam (fun j : Fin i.val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩),
                       (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨i.val, by have := i.isLt; omega⟩))
                       (alpha ⟨i.val, by have := i.isLt; omega⟩)) • Pvec ⟨i.val, by have := i.isLt; omega⟩) =
                     ∑ i : Fin u, b2z (xor (probeTbl (⟨i.val, by have := i.isLt; omega⟩,
                       winAt hsL seam (fun j : Fin i.val => seq0 ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩),
                       seq0 ⟨i.val, by have := i.isLt; omega⟩))
                       (alpha ⟨i.val, by have := i.isLt; omega⟩)) • Pvec ⟨i.val, by have := i.isLt; omega⟩ := by
                   intro u hu; apply Finset.sum_congr rfl; intro i _
                   have hsub : (fun j : Fin i.val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩) =
                       fun j : Fin i.val => seq0 ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩ := by
                     funext j
                     exact Fin.snoc_castSucc (α := fun _ => Fin s → Bool) (tBlk hsL wn) seq0 ⟨j.val, by have := i.isLt; have := j.isLt; omega⟩
                   have hsel : (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨i.val, by have := i.isLt; omega⟩ = seq0 ⟨i.val, by have := i.isLt; omega⟩ :=
                     Fin.snoc_castSucc (α := fun _ => Fin s → Bool) (tBlk hsL wn) seq0 ⟨i.val, by have := i.isLt; omega⟩
                   rw [hsub, hsel]
                 have hsum_t1 : (∑ i : Fin (t + 1), b2z (xor (probeTbl (⟨i.val, lt_of_lt_of_le i.isLt ht⟩,
                     winAt hsL seam (fun j : Fin i.val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, lt_trans j.isLt i.isLt⟩),
                     (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) i))
                     (alpha ⟨i.val, lt_of_lt_of_le i.isLt ht⟩)) • Pvec ⟨i.val, lt_of_lt_of_le i.isLt ht⟩) =
                     bDc (stAt (t + 1)) x := by
                   rw [Fin.sum_univ_castSucc]
                   have h1' : (∑ i : Fin t, b2z (xor (probeTbl (⟨i.castSucc.val, lt_of_lt_of_le i.castSucc.isLt ht⟩,
                       winAt hsL seam (fun j : Fin i.castSucc.val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, lt_trans j.isLt i.castSucc.isLt⟩),
                       (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) i.castSucc))
                       (alpha ⟨i.castSucc.val, lt_of_lt_of_le i.castSucc.isLt ht⟩)) • Pvec ⟨i.castSucc.val, lt_of_lt_of_le i.castSucc.isLt ht⟩) =
                       bDc (stAt t) xp := (hsum_split t le_rfl).trans hg0.2.2.2
                   have h2 : (fun j : Fin (Fin.last t).val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, lt_trans j.isLt (Fin.last t).isLt⟩) = seq0 := hcast
                   rw [h1', h2, hg0.1, hlast]
                   exact hxp_e
                 refine ⟨hw_eq, ?_, ?_, hsum_t1⟩
                 · intro i u hmu
                   by_cases hilt : i.val < t
                   · have hsub : (fun j : Fin i.val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, lt_trans j.isLt i.isLt⟩) =
                         fun j : Fin i.val => seq0 ⟨j.val, by omega⟩ := by
                       funext j; exact Fin.snoc_castSucc (α := fun _ => Fin s → Bool) (tBlk hsL wn) seq0 ⟨j.val, by omega⟩
                     rw [hsub]; exact hg0.2.1 ⟨i.val, hilt⟩ u hmu
                   · have hi_eq : i.val = t := by omega
                     have hfi_last : i = Fin.last t := Fin.ext hi_eq
                     subst hfi_last
                     have hsub : winAt hsL seam (fun j : Fin (Fin.last t).val => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) ⟨j.val, lt_trans j.isLt (Fin.last t).isLt⟩) =
                         pWin hsL wn ps := by
                       change winAt hsL seam (fun j : Fin t => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) j.castSucc) = pWin hsL wn ps
                       rw [hcast]; exact hg0.1
                     rw [hsub, headBlk_prevWin]
                     exact hmask u hmu
                 · intro u hu
                   by_cases hule : u ≤ t
                   · rw [hsum_split u hule]; exact hg0.2.2.1 u hule
                   · have hueq : u = t + 1 := by omega
                     subst hueq; rw [hsum_t1]; exact bsDec_mem (hinv_all (t + 1) ht) x⟩
             invFun := fun ⟨seq, hg⟩ =>
               let seq0 : Fin t → Fin s → Bool := fun j => seq j.castSucc
               let wp := winAt hsL seam seq0
               let ps := hBlk hsL wp
               ⟨ps, ⟨seq0, by
                 have hsh := (shiftWin_iff hsL wp wn (seq (Fin.last t))).mp hg.1
                 have hwp_eq : wp = pWin hsL wn ps := hsh.1
                 have hnxt_eq : seq (Fin.last t) = tBlk hsL wn := hsh.2
                 have hmask : ∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u) := by
                   intro u hmu
                   exact hg.2.1 (Fin.last t) u hmu
                 have hSt_in : (∑ i : Fin t, b2z (xor (probeTbl (⟨i.val, by have := i.isLt; omega⟩,
                     winAt hsL seam (fun j : Fin i.val => seq0 ⟨j.val, lt_trans j.isLt i.isLt⟩), seq0 i))
                     (alpha ⟨i.val, by have := i.isLt; omega⟩)) • Pvec ⟨i.val, by have := i.isLt; omega⟩) ∈ Lsub Pvec t ⊓ Rsub Pvec t :=
                   hg.2.2.1 t (by omega)
                 obtain ⟨xp, hxp_v, hxp_dec⟩ := bsDec_surj (hinv_all t (by omega)) hSt_in
                 refine ⟨hmask, xp, hxp_v, ?_, hwp_eq, ?_, ?_, hxp_dec.symm⟩
                 · have htot := hg.2.2.2
                   rw [Fin.sum_univ_castSucc] at htot
                   rw [hxp_dec, ← hwp_eq, ← hnxt_eq]; exact htot
                 · intro i u hmu; exact hg.2.1 i.castSucc u hmu
                 · intro u hu; exact hg.2.2.1 u (by omega)⟩⟩
             left_inv := fun ⟨ps, ⟨seq0, _, hex⟩⟩ => by
               obtain ⟨_, _, _, hg0⟩ := hex
               have hcast : (fun j : Fin t => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) j.castSucc) = seq0 :=
                 funext (fun j => Fin.snoc_castSucc (α := fun _ => Fin s → Bool) (tBlk hsL wn) seq0 j)
               have hps : hBlk hsL (winAt hsL seam (fun j : Fin t => (Fin.snoc seq0 (tBlk hsL wn) : Fin (t + 1) → Fin s → Bool) j.castSucc)) = ps := by
                 rw [hcast, hg0.1, headBlk_prevWin]
               refine Sigma.ext hps ?_
               subst hps
               exact heq_of_eq (Subtype.ext hcast)
             right_inv := fun ⟨seq, hg⟩ => by
               apply Subtype.ext; funext i
               dsimp only
               refine Fin.lastCases ?_ ?_ i
               · rw [Fin.snoc_last]; exact ((shiftWin_iff hsL _ wn _).mp hg.1).2.symm
               · intro j; simp [Fin.snoc_castSucc] }
       rw [← houter]
       apply Finset.sum_congr rfl; intro ps _
       split_ifs
       · exact hinner ps
       · rfl
     have hlt_step : ∀ (wn : Fin L → Bool) (x : Fin D → Bool),
         (∑ ps : Fin s → Bool,
           if (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) then
             ∑ xp : Fin D → Bool,
               if cVal (stAt t) xp ∧
                   bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                     bDc (stAt (t + 1)) x
               then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0
           else 0) < 2 ^ (k + 1) := by
       intro wn x
       by_cases hx : cVal (stAt (t + 1)) x
       · rw [hsum_eq_card wn x hx]
         calc Fintype.card { seq : Fin (t + 1) → Fin s → Bool // goodSeq (t + 1) ht wn x seq }
             ≤ Fintype.card (Fin (t + 1) → Fin s → Bool) := Fintype.card_subtype_le _
           _ = 2 ^ ((t + 1) * s) := card_seq_le (t + 1)
           _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right s ht)
           _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
       · have hsum_le : (∑ ps : Fin s → Bool,
             if (∀ u : Fin s, maskOff (ii, u) = true → ps u = valOff (ii, u)) then
               ∑ xp : Fin D → Bool,
                 if cVal (stAt t) xp ∧
                     bDc (stAt t) xp + b2z (xor (probeTbl (ii, pWin hsL wn ps, tBlk hsL wn)) (alpha ii)) • Pvec ii =
                       bDc (stAt (t + 1)) x
                 then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0
             else 0) ≤
             ∑ ps : Fin s → Bool, ∑ xp : Fin D → Bool,
               if cVal (stAt t) xp then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0 := by
           apply Finset.sum_le_sum; intro ps _
           split_ifs
           · apply Finset.sum_le_sum; intro xp _
             split_ifs with h1 h2
             · exact le_rfl
             · exact absurd h1.1 h2
             · exact Nat.zero_le _
             · exact le_rfl
           · exact Nat.zero_le _
         have hbound : (∑ ps : Fin s → Bool, ∑ xp : Fin D → Bool,
             if cVal (stAt t) xp then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) ≤
             2 ^ ((t + 1) * s) := by
           have h1 : ∀ ps : Fin s → Bool,
               (∑ xp : Fin D → Bool,
                 if cVal (stAt t) xp then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) ≤
               2 ^ (t * s) := by
             intro ps
             have hconv : (∑ xp : Fin D → Bool,
                 if cVal (stAt t) xp then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) =
                 Fintype.card { p : (Fin D → Bool) × (Fin t → Fin s → Bool) //
                   cVal (stAt t) p.1 ∧ goodSeq t (by omega) (pWin hsL wn ps) p.1 p.2 } := by
               have h2 : ∀ xp : Fin D → Bool,
                   (if cVal (stAt t) xp then bNat (k + 1) (fun b => dpAt t (pWin hsL wn ps, xp, b)) else 0) =
                   Fintype.card { seq0 : Fin t → Fin s → Bool //
                     cVal (stAt t) xp ∧ goodSeq t (by omega) (pWin hsL wn ps) xp seq0 } := by
                 intro xp
                 split_ifs with hxv
                 · rw [ih_cnt (pWin hsL wn ps) xp hxv]
                   exact Fintype.card_congr ⟨fun s0 => ⟨s0.1, hxv, s0.2⟩, fun s0 => ⟨s0.1, s0.2.2⟩, fun _ => rfl, fun _ => rfl⟩
                 · symm; exact Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, h1, _⟩ => hxv h1⟩
               simp_rw [h2]; rw [← Fintype.card_sigma]
               exact Fintype.card_congr ⟨fun ⟨xp, ⟨s0, h⟩⟩ => ⟨(xp, s0), h⟩, fun ⟨⟨xp, s0⟩, h⟩ => ⟨xp, ⟨s0, h⟩⟩, fun _ => rfl, fun _ => rfl⟩
             rw [hconv]
             have hinj : Function.Injective (fun p : { p : (Fin D → Bool) × (Fin t → Fin s → Bool) //
                 cVal (stAt t) p.1 ∧ goodSeq t (by omega) (pWin hsL wn ps) p.1 p.2 } => p.1.2) := by
               intro a b hab
               apply Subtype.ext; apply Prod.ext
               · exact bsDec_inj (hinv_all t (by omega)) a.2.1 b.2.1
                   (a.2.2.2.2.2.symm.trans (by dsimp only at hab; rw [hab]; exact b.2.2.2.2.2))
               · exact hab
             calc Fintype.card _ ≤ Fintype.card (Fin t → Fin s → Bool) := Fintype.card_le_of_injective _ hinj
               _ = 2 ^ (t * s) := card_seq_le t
           calc _ ≤ ∑ _ : Fin s → Bool, 2 ^ (t * s) := Finset.sum_le_sum (fun ps _ => h1 ps)
             _ = 2 ^ s * 2 ^ (t * s) := by simp [Finset.sum_const, Fintype.card_pi, Finset.prod_const]
             _ = 2 ^ ((t + 1) * s) := by rw [← pow_add]; congr 1; ring
         calc _ ≤ 2 ^ ((t + 1) * s) := le_trans hsum_le hbound
           _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right s ht)
           _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
     have hds := dpStep_spec hsL (hinv_all t (by omega)) (hinv_all (t + 1) ht) (hrel_all ii)
       (alpha ii) (fun p => probeTbl (ii, p)) (fun u => maskOff (ii, u)) (fun u => valOff (ii, u))
       (dpAt t) ih_supp hlt_step
     rw [hdp_eq]
     exact ⟨hds.1, fun wn x hx => (hds.2 wn x hx).trans (hsum_eq_card wn x hx)⟩
 have hq_valid : cVal (stAt q) (fun _ => false) := fun _ _ => rfl
 have hdpq : cDS e s d a hsL seam (Sum.elim (Sum.elim (fun _ => validAll)
     (Sum.elim alpha (Sum.elim mds (Sum.elim probeTbl eqOff)))) (Sum.elim maskOff valOff)) =
     fun b => dpAt q (seam, (fun _ => false), b) := by
   funext b; unfold cDS; dsimp only [dpAt]
   rw [List.take_of_length_le (by simp)]; rfl
 dsimp only
 rw [hdpq, (hind q le_rfl).2 seam (fun _ => false) hq_valid, Nat.card_eq_fintype_card]
 refine Fintype.card_congr
   { toFun := fun ⟨seq, hg⟩ => ⟨seq, hg.1, hg.2.1, by
       have hsum := hg.2.2.2
       have h0 : bDc (stAt q) (fun _ => false) = 0 := by funext j; simp [bDc, b2z]
       rw [h0] at hsum; exact hsum⟩
     invFun := fun ⟨seq, h1, h2, h3⟩ => ⟨seq, h1, h2, ?_, ?_⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }
 · intro u hu
   let c : Fin q → Bool := fun i => xor (probeTbl (i,
     winAt hsL seam (fun j : Fin i.val => seq ⟨j.val, lt_trans j.isLt i.isLt⟩), seq i)) (alpha i)
   have hps := (ps_cut Pvec c).mp h3 u hu
   have heq_sum : (∑ i : Fin u, b2z (c ⟨i.val, by have := i.isLt; omega⟩) • Pvec ⟨i.val, by have := i.isLt; omega⟩) =
       ∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < u), b2z (c i) • Pvec i :=
     Finset.sum_bij (fun i _ => ⟨i.val, by have := i.isLt; omega⟩)
       (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩)
       (fun _ _ _ _ h => Fin.ext (by simpa [Fin.ext_iff] using h))
       (fun j hj => ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
       (fun _ _ => rfl)
   rw [heq_sum]; exact hps
 · have h0 : bDc (stAt q) (fun _ => false) = 0 := by funext j; simp [bDc, b2z]
   rw [h0]; exact h3
def seamOf {e s d : ℕ} (_ : 0 < 3 * (e + 1) * s) (off : Fin (3 * (e + 1) * s))
   (w : Fin (2 ^ (3 * (e + 1) * s))) : Fin (d + 1 - s) → Bool :=
 fun u => w.val.testBit ((off.val + u.val) % (3 * (e + 1) * s))
def seqOf {e s d : ℕ} (_ : 0 < 3 * (e + 1) * s) (off : Fin (3 * (e + 1) * s))
   (w : Fin (2 ^ (3 * (e + 1) * s))) : Fin (3 * (e + 1)) → Fin s → Bool :=
 fun i u => w.val.testBit ((off.val + i.val * s + (d + 1 - s) + u.val) % (3 * (e + 1) * s))
lemma wA_sO {e s d : ℕ} (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s)
   (off : Fin (3 * (e + 1) * s)) (w : Fin (2 ^ (3 * (e + 1) * s))) (t : ℕ) (ht : t ≤ 3 * (e + 1)) :
   winAt hsL (seamOf (d := d) hk off w) (fun i : Fin t => seqOf (d := d) hk off w ⟨i.val, lt_of_lt_of_le i.isLt ht⟩) =
     fun u : Fin (d + 1 - s) => w.val.testBit ((off.val + t * s + u.val) % (3 * (e + 1) * s)) := by
 induction t with
 | zero => funext u; simp [winAt, seamOf]
 | succ t ih =>
   funext u
   dsimp only [winAt, sWin]
   have hcast : (fun i : Fin t => seqOf (d := d) hk off w ⟨i.castSucc.val, lt_of_lt_of_le i.castSucc.isLt ht⟩) =
       fun i : Fin t => seqOf (d := d) hk off w ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ := rfl
   rw [hcast, ih (by omega)]
   split_ifs with hlt
   · ring_nf
   · dsimp only [seqOf]; simp only [Fin.val_last]; congr 2; rw [Nat.succ_mul t s]; omega
lemma wA_qi {e s d : ℕ} (hsL : s ≤ d + 1 - s) (hL2s : d + 1 - s ≤ 2 * s)
   (seam1 seam2 : Fin (d + 1 - s) → Bool) (seq : Fin (3 * (e + 1)) → Fin s → Bool) :
   winAt hsL seam1 seq = winAt hsL seam2 seq := by
 let q := 3 * (e + 1)
 have hstep2 : ∀ (t : ℕ) (f : Fin (t + 2) → Fin s → Bool) (a b : Fin (d + 1 - s) → Bool),
     winAt hsL a f = winAt hsL b f := by
   intro t f a b
   funext u
   change sWin hsL (winAt hsL a (fun i : Fin (t + 1) => f i.castSucc)) (f (Fin.last (t + 1))) u =
     sWin hsL (winAt hsL b (fun i : Fin (t + 1) => f i.castSucc)) (f (Fin.last (t + 1))) u
   dsimp only [sWin]
   split_ifs with h1
   · change sWin hsL (winAt hsL a _) (f (Fin.last t).castSucc) ⟨s + u.val, _⟩ =
       sWin hsL (winAt hsL b _) (f (Fin.last t).castSucc) ⟨s + u.val, _⟩
     dsimp only [sWin]
     have h2 : ¬ (s + u.val < (d + 1 - s) - s) := by omega
     simp only [h2, ↓reduceDIte]
   · rfl
 let f : Fin ((q - 2) + 2) → Fin s → Bool := fun i => seq ⟨i.val, by omega⟩
 have h1 : winAt hsL seam1 seq = winAt hsL seam1 f := by
   have heq : q = (q - 2) + 2 := by omega
   cases heq; rfl
 have h2 : winAt hsL seam2 seq = winAt hsL seam2 f := by
   have heq : q = (q - 2) + 2 := by omega
   cases heq; rfl
 rw [h1, h2]; exact hstep2 (q - 2) f seam1 seam2
lemma sO_bij {e s d : ℕ} (hk : 0 < 3 * (e + 1) * s) (_hs : 0 < s)
   (off : Fin (3 * (e + 1) * s)) :
   Function.Bijective (seqOf (e := e) (s := s) (d := d) hk off) := by
 let q := 3 * (e + 1)
 let k := q * s
 let L := d + 1 - s
 have hidx_bij : Function.Bijective (fun p : Fin q × Fin s =>
     (⟨(off.val + p.1.val * s + L + p.2.val) % k, Nat.mod_lt _ hk⟩ : Fin k)) := by
   refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [k]⟩
   intro p1 p2 heq
   have hv : (off.val + p1.1.val * s + L + p1.2.val) % k = (off.val + p2.1.val * s + L + p2.2.val) % k :=
     congrArg Fin.val heq
   have ha1 : p1.1.val * s + p1.2.val < k := by
     have hp1 := p1.1.isLt; have hp2 := p1.2.isLt; dsimp only [k]; nlinarith
   have ha2 : p2.1.val * s + p2.2.val < k := by
     have hp1 := p2.1.isLt; have hp2 := p2.2.isLt; dsimp only [k]; nlinarith
   have hsub1 := mod_sub_shift hk 0 (off.val + L + (p1.1.val * s + p1.2.val)) (off.val + L) (by omega)
   have hsub2 := mod_sub_shift hk 0 (off.val + L + (p2.1.val * s + p2.2.val)) (off.val + L) (by omega)
   simp only [zero_add, Nat.add_sub_cancel_left] at hsub1 hsub2
   have hmod_eq : (p1.1.val * s + p1.2.val) % k = (p2.1.val * s + p2.2.val) % k := by
     rw [← hsub1, ← hsub2]
     have ha : off.val + p1.1.val * s + L + p1.2.val = off.val + L + (p1.1.val * s + p1.2.val) := by omega
     have hb : off.val + p2.1.val * s + L + p2.2.val = off.val + L + (p2.1.val * s + p2.2.val) := by omega
     rw [← ha, ← hb, hv]
   rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2] at hmod_eq
   have hq_eq : p1.1.val = p2.1.val := by
     have h1 := Nat.div_eq_of_lt_le (by nlinarith : p1.1.val * s ≤ p1.1.val * s + p1.2.val)
       (by have := p1.2.isLt; nlinarith)
     have h2 := Nat.div_eq_of_lt_le (by nlinarith : p2.1.val * s ≤ p2.1.val * s + p2.2.val)
       (by have := p2.2.isLt; nlinarith)
     rw [← h1, ← h2, hmod_eq]
   have hr_eq : p1.2.val = p2.2.val := by nlinarith
   exact Prod.ext (Fin.ext hq_eq) (Fin.ext hr_eq)
 refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by rw [Fintype.card_fin, card_seq_le, mul_comm]⟩
 intro w1 w2 heq
 apply Fin.ext; apply Nat.eq_of_testBit_eq; intro b
 by_cases hb : b < k
 · obtain ⟨⟨i, u⟩, hiu⟩ := hidx_bij.2 ⟨b, hb⟩
   have hval := congrFun (congrFun heq i) u
   dsimp only [seqOf] at hval
   have hbv : (off.val + i.val * s + L + u.val) % k = b := congrArg Fin.val hiu
   rwa [hbv] at hval
 · have hb' : k ≤ b := Nat.le_of_not_lt hb
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le w1.isLt (Nat.pow_le_pow_right (by omega) hb')),
       Nat.testBit_lt_two_pow (lt_of_lt_of_le w2.isLt (Nat.pow_le_pow_right (by omega) hb'))]
lemma cDR_sp {n e s d r a : ℕ} (hs : 0 < s) (hr : 4 ≤ r) (h2s : 2 * s ≤ d) (hd3s : d < 3 * s)
   (edges : Fin e → Fin (n + 1) × Fin (n + 1))
   (nr nc : Fin (2 ^ (3 * (e + 1) * s))) (cr cc : Fin r → Fin (2 ^ (3 * (e + 1) * s)))
   (off : Fin (3 * (e + 1) * s)) (bank : Fin (3 * (e + 1)) → Bool)
   (y : Fin (2 ^ (2 * n + 1))) (_t _j : Fin (2 ^ (3 * (e + 1) * s + 1)))
   (raw : RIn n e s r → Bool)
   (hG : ∀ (ei : Fin e) (b : Fin (n + 1)),
     rEdg raw ei false b = (edges ei).1.val.testBit b.val ∧
     rEdg raw ei true b = (edges ei).2.val.testBit b.val)
   (hnr : ∀ p, rNr raw p = nr.val.testBit p.val)
   (hnc : ∀ p, rNc raw p = nc.val.testBit p.val)
   (hcr : ∀ ri p, rCr raw ri p = (cr ri).val.testBit p.val)
   (hcc : ∀ ci p, rCc raw ci p = (cc ci).val.testBit p.val)
   (hoff : ∀ p, rOff raw p = off.val.testBit p.val)
   (hbank : ∀ i, rBnk raw i = bank i)
   (hy : ∀ b, rY raw b = y.val.testBit b.val)
   (hvalidAll : feB n e s d r a (by positivity) (by omega) raw (inl ()) = true)
   (maskF valF : Fin (3 * (e + 1) * s) → Bool) :
   let q := 3 * (e + 1)
   let k := q * s
   let hk : 0 < k := by positivity
   let hsL : s ≤ d + 1 - s := by omega
   let fo := feB n e s d r a hk (by omega) raw
   let P := makeP (List.ofFn edges)
   let hit := fun (w : Fin (2 ^ k)) =>
     (List.finRange q).foldl (fun z i =>
       let p := (off.val + i.val * s) % k
       let col := bank i
       let bit := (stateN k r col w.val (if col then nc.val else nr.val)
         (if col then cc else cr)).testBit ((p + delayN r col) % k)
       if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val
   bNat (k + 1) (cDR e s d a hk hsL (Sum.elim fo (Sum.elim maskF valF))) =
     Nat.card { w : Fin (2 ^ k) // hit w ∧ ∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b } := by
 let q := 3 * (e + 1)
 let k := q * s
 let m := 2 * n + 1
 let D := 1 + 2 * a
 let L := d + 1 - s
 have hk : 0 < k := by positivity
 have hsL : s ≤ L := by omega
 have hL2s : L ≤ 2 * s := by omega
 have hd_lt : d < k := by
   have : 3 * s ≤ k := by dsimp [k, q]; nlinarith
   omega
 have hk3 : 2 < k := by
   have : 3 * s ≤ k := by dsimp [k, q]; nlinarith
   omega
 have hv_and := (Bool.and_eq_true _ _).mp hvalidAll
 have hv_and2 := (Bool.and_eq_true _ _).mp hv_and.1
 have hvalidBank : ∀ i : Fin q, reachN r (bank i) ≤ d := by
   intro i
   have h1 := (decide_eq_true_iff).mp hv_and2.1 i
   rw [hbank i] at h1
   cases hb : bank i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h1 <;> exact h1
 have hyOk : rPC (rref (aMt (fun (i : Fin q) (j : Fin m) => buildP n e s r raw (i, j)) (rY raw)))
     (Fin.last q) = false := by
   have h1 := hv_and2.2; simpa [Bool.not_eq_true'] using h1
 have hnoOver : ∀ i : Fin q,
     sOv (fun x => rBC q D m (Sum.elim (buildP n e s r raw)
       (bSN q m (buildP n e s r raw))) (inr (i, x))) = false := by
   intro i
   have h1 := hv_and.2
   simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_exists] at h1
   cases hc : sOv (fun x => rBC q D m (Sum.elim (buildP n e s r raw)
       (bSN q m (buildP n e s r raw))) (inr (i, x)))
   · rfl
   · exact absurd hc (h1 i)
 let P := makeP (List.ofFn edges)
 let Pmat := buildP n e s r raw
 let Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
 have hPvec_eq : ∀ i j, Pvec i j = vecBit m (P[i.val]?.getD 0) j := by
   intro i j; dsimp only [Pvec, Pmat, vecBit, b2z]; rw [buildP_spec edges raw hG i j]
 let stY := rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw))
 let alpha : Fin q → Bool := fun i => rNV stY (Fin.last q) i.castSucc
 have halpha_sum : ∑ i : Fin q, b2z (alpha i) • Pvec i = fun j => b2z (y.val.testBit j.val) := by
   have hsol := (rref_solve_spec (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw)).2 hyOk
   rw [show (fun j => b2z (rY raw j)) = (fun j => b2z (y.val.testBit j.val)) by funext j; rw [hy j]] at hsol
   exact hsol
 have heqOff : ∀ o : Fin k, eCB k o.val (rOff raw) () = decide (o = off) := by
   intro o
   rw [eCB_sp k o.val (rOff raw) off.val (lt_trans off.isLt Nat.lt_two_pow_self)
     (lt_trans o.isLt Nat.lt_two_pow_self) hoff]
   simp only [decide_eq_decide, Fin.ext_iff]; exact eq_comm
 have hmaskOff : ∀ p : Fin q × Fin s,
     decide (∃ o : Fin k, eCB k o.val (rOff raw) () = true ∧
       maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) =
     maskF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ := by
   intro p
   simp_rw [heqOff]
   have hiff : (∃ o : Fin k, decide (o = off) = true ∧
       maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) ↔
       maskF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true :=
     ⟨fun ⟨o, ho, hm⟩ => by have heq : o = off := of_decide_eq_true ho; subst o; exact hm,
      fun hm => ⟨off, decide_eq_true rfl, hm⟩⟩
   have hdec : decide (∃ o : Fin k, decide (o = off) = true ∧
       maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) =
       decide (maskF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) :=
     decide_eq_decide.mpr hiff
   rw [hdec, Bool.decide_eq_true]
 have hvalOff : ∀ p : Fin q × Fin s,
     decide (∃ o : Fin k, eCB k o.val (rOff raw) () = true ∧
       valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) =
     valF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ := by
   intro p
   simp_rw [heqOff]
   have hiff : (∃ o : Fin k, decide (o = off) = true ∧
       valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) ↔
       valF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true :=
     ⟨fun ⟨o, ho, hm⟩ => by have heq : o = off := of_decide_eq_true ho; subst o; exact hm,
      fun hm => ⟨off, decide_eq_true rfl, hm⟩⟩
   have hdec : decide (∃ o : Fin k, decide (o = off) = true ∧
       valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) =
       decide (valF ⟨(off.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true) :=
     decide_eq_decide.mpr hiff
   rw [hdec, Bool.decide_eq_true]
 have hprobe_eq : ∀ (w : Fin (2 ^ k)) (i : Fin q),
     let fo := feB n e s d r a hk (by omega) raw
     let probeTbl := fun p => fo (inr (inr (inr (inl p))))
     probeTbl (i, winAt hsL (seamOf (d := d) hk off w)
         (fun j : Fin i.val => seqOf (d := d) hk off w ⟨j.val, lt_trans j.isLt i.isLt⟩),
       seqOf (d := d) hk off w i) =
     (stateN k r (bank i) w.val (if bank i then nc.val else nr.val) (if bank i then cc else cr)).testBit
       (((off.val + i.val * s) % k + delayN r (bank i)) % k) := by
   intro w i
   have hwin_eq : winAt hsL (seamOf (d := d) hk off w)
       (fun j : Fin i.val => seqOf (d := d) hk off w ⟨j.val, lt_trans j.isLt i.isLt⟩) =
       fun u : Fin L => w.val.testBit ((off.val + i.val * s + u.val) % k) :=
     wA_sO hk hsL off w i.val (le_of_lt i.isLt)
   have hps := pOE_sp hk hr (by omega : s ≤ d + 1) hd_lt hk3 i.val off (bank i) (hvalidBank i)
     nr nc cr cc w _ (seqOf (d := d) hk off w i) (fun u => congrFun hwin_eq u) (fun u => rfl)
   rw [← hps]
   dsimp only [feB, Sum.elim_inl, Sum.elim_inr]
   congr 1; funext x
   rcases x with o | p | p | ⟨ri, p⟩ | ⟨ci, p⟩ | u
   · exact heqOff o
   · exact hnr p
   · exact hnc p
   · exact hcr ri p
   · exact hcc ci p
   · exact hbank i
 have hhit_iff : ∀ w : Fin (2 ^ k),
     ((List.finRange q).foldl (fun z i =>
       let p := (off.val + i.val * s) % k
       let col := bank i
       let bit := (stateN k r col w.val (if col then nc.val else nr.val)
         (if col then cc else cr)).testBit ((p + delayN r col) % k)
       if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val) ↔
     (∑ i : Fin q, b2z (xor ((stateN k r (bank i) w.val (if bank i then nc.val else nr.val)
       (if bank i then cc else cr)).testBit (((off.val + i.val * s) % k + delayN r (bank i)) % k)) (alpha i)) • Pvec i = 0) := by
   intro w
   let bitOf : Fin q → Bool := fun i =>
     (stateN k r (bank i) w.val (if bank i then nc.val else nr.val)
       (if bank i then cc else cr)).testBit (((off.val + i.val * s) % k + delayN r (bank i)) % k)
   have hPlt : ∀ i : Fin q, P[i.val]?.getD 0 < 2 ^ m := by
     intro i
     have hlen : P.length = q := by rw [makeP_length, List.length_ofFn]
     rw [List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt)]
     dsimp only [Option.getD]
     rw [makeP_getElem (List.ofFn edges) i.val (by rw [List.length_ofFn]; exact i.isLt)]
     have hlo_lt : ∀ v : Fin (n + 1), loVal v < 2 ^ m := by
       intro v; unfold loVal; split_ifs with h0
       · exact Nat.pos_of_ne_zero (by positivity)
       · rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) (by have := v.isLt; dsimp [m]; omega)
     have hhi_lt : ∀ v : Fin (n + 1), hiVal v < 2 ^ m := by
       intro v; unfold hiVal; split_ifs with h0
       · exact Nat.pos_of_ne_zero (by positivity)
       · rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) (by have := v.isLt; dsimp [m]; omega)
     have h1lt : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
     split_ifs
     · exact h1lt
     · exact Nat.xor_lt_two_pow (hlo_lt _) (hlo_lt _)
     · exact Nat.xor_lt_two_pow (hhi_lt _) (hhi_lt _)
     · exact h1lt
   have hfold_lt : ∀ (ls : List (Fin q)) (acc : ℕ), acc < 2 ^ m →
       ls.foldl (fun z i => if bitOf i then z ^^^ (P[i.val]?.getD 0) else z) acc < 2 ^ m := by
     intro ls; induction ls with
     | nil => intro acc h; exact h
     | cons i tl ih =>
       intro acc h; rw [List.foldl_cons]; apply ih
       split_ifs
       · exact Nat.xor_lt_two_pow h (hPlt i)
       · exact h
   have hfold_bit : ∀ (ls : List (Fin q)) (hnd : ls.Nodup) (acc : ℕ) (b : Fin m),
       b2z ((ls.foldl (fun z i => if bitOf i then z ^^^ (P[i.val]?.getD 0) else z) acc).testBit b.val) =
         b2z (acc.testBit b.val) + ∑ i ∈ ls.toFinset, b2z (bitOf i) * Pvec i b := by
     intro ls; induction ls with
     | nil => intro _ acc b; simp
     | cons i tl ih =>
       intro hnd acc b
       rw [List.nodup_cons] at hnd
       rw [List.foldl_cons, ih hnd.2]
       rw [List.toFinset_cons, Finset.sum_insert (by simpa using hnd.1)]
       have hstep : b2z ((if bitOf i then acc ^^^ (P[i.val]?.getD 0) else acc).testBit b.val) =
           b2z (acc.testBit b.val) + b2z (bitOf i) * Pvec i b := by
         rw [hPvec_eq i b]; unfold vecBit
         cases bitOf i
         · simp only [Bool.false_eq_true, ↓reduceIte, b2z, zero_mul, add_zero]
         · simp only [↓reduceIte, Nat.testBit_xor]
           cases acc.testBit b.val <;> cases (P[i.val]?.getD 0).testBit b.val <;> decide
       rw [hstep]; ring
   have hlt_rep := hfold_lt (List.finRange q) 0 (Nat.pos_of_ne_zero (by positivity))
   constructor
   · intro hrep
     funext b
     simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
     have hb := hfold_bit (List.finRange q) (List.nodup_finRange q) 0 b
     rw [hrep, show (List.finRange q).toFinset = Finset.univ by ext x; simp, Nat.zero_testBit] at hb
     have h0 : b2z false = 0 := rfl
     rw [h0, zero_add] at hb
     have hal := congrFun halpha_sum b
     simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hal
     have hsplit : ∑ i : Fin q, b2z (xor (bitOf i) (alpha i)) * Pvec i b =
         (∑ i : Fin q, b2z (bitOf i) * Pvec i b) + (∑ i : Fin q, b2z (alpha i) * Pvec i b) := by
       rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [b2z_xor, add_mul]
     rw [hsplit, ← hb, hal, zmod2_add_self]
   · intro hsum0
     apply Nat.eq_of_testBit_eq; intro b
     by_cases hb : b < m
     · let bf : Fin m := ⟨b, hb⟩
       have hfold := hfold_bit (List.finRange q) (List.nodup_finRange q) 0 bf
       rw [show (List.finRange q).toFinset = Finset.univ by ext x; simp, Nat.zero_testBit] at hfold
       have h0 : b2z false = 0 := rfl
       rw [h0, zero_add] at hfold
       have hsb := congrFun hsum0 bf
       simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsb
       have hsplit : ∑ i : Fin q, b2z (xor (bitOf i) (alpha i)) * Pvec i bf =
           (∑ i : Fin q, b2z (bitOf i) * Pvec i bf) + (∑ i : Fin q, b2z (alpha i) * Pvec i bf) := by
         rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [b2z_xor, add_mul]
       rw [hsplit, ← hfold] at hsb
       have hal := congrFun halpha_sum bf
       simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hal
       rw [hal] at hsb
       have heq_z : b2z (((List.finRange q).foldl (fun z i => if bitOf i then z ^^^ (P[i.val]?.getD 0) else z) 0).testBit b) =
           b2z (y.val.testBit b) := by
         have hadd := congrArg (fun x => x + b2z (y.val.testBit bf.val)) hsb
         simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
         exact hadd
       exact (z2b_b2z _).symm.trans ((congrArg z2b heq_z).trans (z2b_b2z _))
     · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt_rep (Nat.pow_le_pow_right (by omega) (by omega))),
           Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]
 have hmask_iff : ∀ w : Fin (2 ^ k),
     (∀ i : Fin q, ∀ u : Fin s,
       maskF ⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true →
       hBlk hsL (winAt hsL (seamOf (d := d) hk off w)
         (fun j : Fin i.val => seqOf (d := d) hk off w ⟨j.val, lt_trans j.isLt i.isLt⟩)) u =
       valF ⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩) ↔
     (∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b) := by
   intro w
   have hblk_eq : ∀ (i : Fin q) (u : Fin s),
       hBlk hsL (winAt hsL (seamOf (d := d) hk off w)
         (fun j : Fin i.val => seqOf (d := d) hk off w ⟨j.val, lt_trans j.isLt i.isLt⟩)) u =
       w.val.testBit ((off.val + i.val * s + u.val) % k) := fun i u => by
     rw [wA_sO hk hsL off w i.val (le_of_lt i.isLt)]; rfl
   simp_rw [hblk_eq]
   constructor
   · intro h b hmb
     let shift := (b.val + k - off.val) % k
     have hsh_lt : shift < k := Nat.mod_lt _ hk
     let i : Fin q := ⟨shift / s, by
       have : shift < q * s := hsh_lt
       exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
     let u : Fin s := ⟨shift % s, Nat.mod_lt _ hs⟩
     have hpos : (⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ : Fin k) = b := by
       apply Fin.ext; dsimp only [i, u]
       have hdm : shift / s * s + shift % s = shift := by
         have := Nat.div_add_mod shift s; linarith
       rw [Nat.add_assoc, hdm]
       have h2 := mod_add_shift hk off.val (b.val + k - off.val)
       have h3 : (off.val + (b.val + k - off.val)) % k = b.val := by
         have hle_off : off.val ≤ b.val + k := by have := off.isLt; dsimp only [k, q] at *; omega
         have hadd : off.val + (b.val + k - off.val) = b.val + k := Nat.add_sub_of_le hle_off
         rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
       dsimp only [shift]
       rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h3]
     have hi := h i u (by rwa [hpos])
     rw [hpos] at hi
     have hval : (off.val + i.val * s + u.val) % k = b.val := congrArg Fin.val hpos
     rwa [hval] at hi
   · intro h i u hm; exact h ⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ hm
 let fo := feB n e s d r a hk (by omega) raw
 have hseam_card : ∀ seam : Fin L → Bool,
     bNat (k + 1) (fun b => cDS e s d a hsL seam
       (Sum.elim fo (Sum.elim
         (fun p => decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
           maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true))
         (fun p => decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
           valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true)))) b) =
     Fintype.card { w : Fin (2 ^ k) // seamOf (d := d) hk off w = seam ∧
       ((List.finRange q).foldl (fun z i =>
         let p := (off.val + i.val * s) % k
         let col := bank i
         let bit := (stateN k r col w.val (if col then nc.val else nr.val)
           (if col then cc else cr)).testBit ((p + delayN r col) % k)
         if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val) ∧
       (∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b) } := by
   intro seam
   have hcs := cDS_sp (n := n) (e := e) (s := s) (d := d) (a := a) hsL
     Pmat alpha (fun p => fo (inr (inr (inr (inl p)))))
     (fun o => fo (inr (inr (inr (inr o)))))
     (fun p => decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
       maskF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true))
     (fun p => decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
       valF ⟨(o.val + p.1.val * s + p.2.val) % k, Nat.mod_lt _ hk⟩ = true))
     (fo (inl ())) seam hnoOver
   have hfo_eq : Sum.elim (fun _ => fo (inl ())) (Sum.elim alpha (Sum.elim
       (fun p => rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr p))
       (Sum.elim (fun p => fo (inr (inr (inr (inl p)))))
         (fun o => fo (inr (inr (inr (inr o)))))))) = fo := by
     funext x; rcases x with u | i | p | p | o <;> rfl
   dsimp only at hcs
   rw [hfo_eq, Nat.card_eq_fintype_card] at hcs
   rw [hcs]
   let eqSeq : Fin (2 ^ k) ≃ (Fin q → Fin s → Bool) := Equiv.ofBijective _ (sO_bij (d := d) hk hs off)
   symm
   refine Fintype.card_congr
     { toFun := fun ⟨w, hsm, hhit, hmk⟩ => ⟨eqSeq w, by
         have hw_q : winAt hsL seam (eqSeq w) = seam := by
           rw [← hsm]
           have h1 := wA_sO (d := d) hk hsL off w q le_rfl
           have h2 : (fun i : Fin q => seqOf (d := d) hk off w ⟨i.val, i.isLt⟩) = eqSeq w := rfl
           rw [h2] at h1; rw [h1]; funext u; dsimp only [seamOf]
           congr 1; rw [Nat.add_assoc, Nat.add_comm (q * s), ← Nat.add_assoc, Nat.add_mod_right]
         refine ⟨hw_q, ?_, ?_⟩
         · intro i u hmu
           have hmu' : maskF ⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true := by
             rw [← hmaskOff (i, u)]; exact hmu
           change _ = decide (∃ o : Fin k, eCB k o.val (rOff raw) () = true ∧
             valF ⟨(o.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true)
           rw [hvalOff (i, u), ← hsm]
           exact (hmask_iff w).mpr hmk i u hmu'
         · rw [← hsm]
           have hsum := (hhit_iff w).mp hhit
           rw [← hsum]; apply Finset.sum_congr rfl; intro i _
           have hp_i := hprobe_eq w i
           dsimp only [fo] at hp_i ⊢
           exact congrArg (fun b => b2z (xor b (alpha i)) • Pvec i) hp_i⟩
       invFun := fun ⟨seq, hwinq, hmk, hsum⟩ =>
         let w := eqSeq.symm seq
         have hseq : seqOf (d := d) hk off w = seq := eqSeq.apply_symm_apply seq
         have hsm : seamOf (d := d) hk off w = seam := by
           have h1 := wA_sO (d := d) hk hsL off w q le_rfl
           have h2 : (fun i : Fin q => seqOf (d := d) hk off w ⟨i.val, i.isLt⟩) = seq := hseq
           rw [h2] at h1
           have h3 : winAt hsL (seamOf (d := d) hk off w) seq = seamOf (d := d) hk off w := by
             rw [h1]; funext u; dsimp only [seamOf]
             congr 1; rw [Nat.add_assoc, Nat.add_comm (q * s), ← Nat.add_assoc, Nat.add_mod_right]
           rw [← h3, wA_qi hsL hL2s (seamOf (d := d) hk off w) seam seq, hwinq]
         ⟨w, hsm, (hhit_iff w).mpr (by
             rw [← hsum]; apply Finset.sum_congr rfl; intro i _
             have hp_i := hprobe_eq w i
             dsimp only [fo] at hp_i ⊢
             rw [← hsm, ← hseq]
             exact congrArg (fun b => b2z (xor b (alpha i)) • Pvec i) hp_i.symm),
           (hmask_iff w).mp (fun i u hmu => by
             have hmu' : decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
                 maskF ⟨(o.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true) = true := by
               change decide (∃ o : Fin k, eCB k o.val (rOff raw) () = true ∧
                 maskF ⟨(o.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true) = true
               rw [hmaskOff (i, u)]; exact hmu
             have h1 := hmk i u hmu'
             have hval_eq : decide (∃ o : Fin k, fo (inr (inr (inr (inr o)))) = true ∧
                 valF ⟨(o.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ = true) =
                 valF ⟨(off.val + i.val * s + u.val) % k, Nat.mod_lt _ hk⟩ := hvalOff (i, u)
             rw [hval_eq] at h1
             rwa [hsm, hseq])⟩
       left_inv := fun ⟨w, _⟩ => Subtype.ext (eqSeq.symm_apply_apply w)
       right_inv := fun ⟨seq, _⟩ => Subtype.ext (eqSeq.apply_symm_apply seq) }
 have htot_card : (∑ seam : Fin L → Bool,
     Fintype.card { w : Fin (2 ^ k) // seamOf (d := d) hk off w = seam ∧
       ((List.finRange q).foldl (fun z i =>
         let p := (off.val + i.val * s) % k
         let col := bank i
         let bit := (stateN k r col w.val (if col then nc.val else nr.val)
           (if col then cc else cr)).testBit ((p + delayN r col) % k)
         if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val) ∧
       (∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b) }) =
     Nat.card { w : Fin (2 ^ k) //
       ((List.finRange q).foldl (fun z i =>
         let p := (off.val + i.val * s) % k
         let col := bank i
         let bit := (stateN k r col w.val (if col then nc.val else nr.val)
           (if col then cc else cr)).testBit ((p + delayN r col) % k)
         if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val) ∧
       (∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b) } := by
   rw [← Fintype.card_sigma, Nat.card_eq_fintype_card]
   exact Fintype.card_congr
     { toFun := fun ⟨_, ⟨w, _, h1, h2⟩⟩ => ⟨w, h1, h2⟩
       invFun := fun ⟨w, h1, h2⟩ => ⟨seamOf (d := d) hk off w, ⟨w, rfl, h1, h2⟩⟩
       left_inv := fun ⟨sm, ⟨w, hsm, _, _⟩⟩ => by subst hsm; rfl
       right_inv := fun _ => rfl }
 dsimp only [cDR, Sum.elim_inl, Sum.elim_inr]
 rw [bNat_bS_lt]
 · rw [← htot_card]; exact Finset.sum_congr rfl (fun sm _ => hseam_card sm)
 · refine lt_of_eq_of_lt ((Finset.sum_congr rfl (fun sm _ => hseam_card sm)).trans htot_card) ?_
   rw [Nat.card_eq_fintype_card]
   calc Fintype.card _ ≤ Fintype.card (Fin (2 ^ k)) := Fintype.card_subtype_le _
     _ = 2 ^ k := Fintype.card_fin _
     _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
noncomputable def uSt (e s d a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s)
   (pos : Fin (3 * (e + 1) * s))
   (inp : FOut e s d a ⊕ (Fin (3 * (e + 1) * s + 1) ⊕ Fin (3 * (e + 1) * s)) → Bool) :
   Fin (3 * (e + 1) * s + 1) ⊕ Fin (3 * (e + 1) * s) → Bool :=
 let k := 3 * (e + 1) * s
 let fo : FOut e s d a → Bool := fun x => inp (inl x)
 let rem : Fin (k + 1) → Bool := fun b => inp (inr (inl b))
 let wBits : Fin k → Bool := fun b => inp (inr (inr b))
 let mask0 : Fin k → Bool := fun b => decide (pos.val ≤ b.val)
 let val0 : Fin k → Bool := fun b => if b = pos then false else wBits b
 let cnt0 := cDR e s d a hk hsL (Sum.elim fo (Sum.elim mask0 val0))
 let sub := bSC (k + 1) (Sum.elim rem cnt0)
 let goRight : Bool := sub (inr ())
 Sum.elim
   (fun b => if goRight then sub (inl b) else rem b)
   (fun b => if b = pos then goRight else wBits b)
lemma ec_uSt (e s d a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s)
   (pos : Fin (3 * (e + 1) * s)) :
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let L := d + 1 - s
   EC (
     (2 * k * (3 * k + 5) +
      2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
      (2 + 2 ^ L * (20 * (k + 2)))) +
     40 * (k + 2)
   ) (uSt e s d a hk hsL pos) := by
 let q := 3 * (e + 1)
 let k := q * s
 let I0 := FOut e s d a ⊕ (Fin (k + 1) ⊕ Fin k)
 have hmv : EC 4
     (fun (inp : I0 → Bool) =>
       Sum.elim (fun x => inp (inl x))
         (Sum.elim (fun b : Fin k => decide (pos.val ≤ b.val))
           (fun b : Fin k => if b = pos then false else inp (inr (inr b))))) := by
   have hval : EC 2 (fun (inp : I0 → Bool) (b : Fin k) =>
       if b = pos then false else inp (inr (inr b))) := by
     have h := ec_ite_of (ec_const (ι := I0) (fun b : Fin k => decide (b = pos)))
       (ec_const (fun _ => false)) (ec_proj (fun b : Fin k => (inr (inr b) : I0)))
     let sel : Fin k → I0 ⊕ Unit := fun b => if b = pos then inr () else inl (inr (inr b))
     have h2 := ec_let (ec_const (ι := I0) (fun (_ : Unit) => false)) (ec_proj sel)
     refine ec_le (ec_eq ?_ h2) (by omega)
     intro inp b; dsimp only [sel]; by_cases hbp : b = pos <;> simp [hbp]
   have hp := ec_pair (ec_proj (fun x : FOut e s d a => (inl x : I0)))
     (ec_pair (ec_const (ι := I0) (fun b : Fin k => decide (pos.val ≤ b.val))) hval)
   exact ec_le hp (by omega)
 have hcnt := ec_comp hmv (ec_cDR e s d a hk hsL)
 let I1 := I0 ⊕ Fin (k + 1)
 have hsub : EC (20 * (k + 2))
     (fun (y : I1 → Bool) =>
       bSC (k + 1) (Sum.elim (fun b => y (inl (inr (inl b)))) (fun b => y (inr b)))) := by
   let sel : Fin (k + 1) ⊕ Fin (k + 1) → I1 :=
     Sum.elim (fun b => inl (inr (inl b))) (fun b => inr b)
   have h := ec_comp (ec_proj sel) (ec_bSC (k + 1))
   rw [zero_add] at h
   refine ec_eq ?_ h
   intro y x; congr 1; funext z; rcases z with _ | _ <;> rfl
 let I2 := I1 ⊕ (Fin (k + 1) ⊕ Unit)
 have hout : EC (10 * (k + 2))
     (fun (z : I2 → Bool) =>
       Sum.elim
         (fun b : Fin (k + 1) => if z (inr (inr ())) then z (inr (inl b))
           else z (inl (inl (inr (inl b)))))
         (fun b : Fin k => if b = pos then z (inr (inr ()))
           else z (inl (inl (inr (inr b)))))) := by
   have hrem := ec_ite_of
     (ec_proj (fun (_ : Fin (k + 1)) => (inr (inr ()) : I2)))
     (ec_proj (fun b : Fin (k + 1) => (inr (inl b) : I2)))
     (ec_proj (fun b : Fin (k + 1) => (inl (inl (inr (inl b))) : I2)))
   rw [Fintype.card_fin] at hrem
   have hw : EC 0 (fun (z : I2 → Bool) (b : Fin k) =>
       if b = pos then z (inr (inr ()))
       else z (inl (inl (inr (inr b))))) := by
     let sel : Fin k → I2 := fun b => if b = pos then inr (inr ()) else inl (inl (inr (inr b)))
     exact ec_eq (fun z b => by dsimp only [sel]; by_cases hbp : b = pos <;> simp [hbp]) (ec_proj sel)
   exact ec_le (ec_pair hrem hw) (by omega)
 have htot := ec_let hcnt (ec_let hsub hout)
 refine ec_le (ec_eq ?_ htot) (by dsimp only [k, q]; omega)
 intro inp q0; rcases q0 with b | b <;> rfl
noncomputable def uOut (n e s d r a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s)
   (raw : RIn n e s r → Bool) (_ : Unit) : Bool :=
 let q := 3 * (e + 1)
 let k := q * s
 let fo := feB n e s d r a hk (by omega) raw
 let validAll := fo (inl ())
 let tot := cDR e s d a hk hsL (Sum.elim fo (Sum.elim (fun _ => false) (fun _ => false)))
 let tLtTot := !(bSC (k + 1) (Sum.elim (rT raw) tot) (inr ()))
 let finalSt := (List.finRange k).foldl
   (fun st stepIdx =>
     let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
     uSt e s d a hk hsL pos (Sum.elim fo st))
   (Sum.elim (rT raw) (fun _ => false))
 let wStar : Fin k → Bool := fun b => finalSt (inr b)
 let bitOk : Bool :=
   eCB (k + 1) 0 (rJ raw) () ||
     decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) (rJ raw) () = true ∧ wStar u = true)
 validAll && tLtTot && bitOk
lemma ec_uOut (n e s d r a : ℕ) (hk : 0 < 3 * (e + 1) * s) (hsL : s ≤ d + 1 - s) :
   let m := 2 * n + 1
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let L := d + 1 - s
   let frontCost :=
     q * m * (20 * n + 50) +
     k * (8 * k + 10) +
     (20 * q + 20) +
     100 * (q + 1) * (m + 1) * (q + m + 3) +
     q * (50 * (q + 1) * (m + 1) * (q + m + 3)) +
     (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3))) +
     (4 * q + 30) +
     q * 2 ^ L * 2 ^ s * (100 * (k + 1) * (k + r + 2))
   let dpCost :=
     2 * k * (3 * k + 5) +
     2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
     (2 + 2 ^ L * (20 * (k + 2)))
   EC (frontCost + (k + 1) * (dpCost + 40 * (k + 2)) + 20 * (k + 2) * (k + 2))
     (uOut n e s d r a hk hsL) := by
 let m := 2 * n + 1
 let q := 3 * (e + 1)
 let k := q * s
 let D := 1 + 2 * a
 let L := d + 1 - s
 let I0 := RIn n e s r
 let dpCost :=
   2 * k * (3 * k + 5) +
   2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
   (2 + 2 ^ L * (20 * (k + 2)))
 have hfront := ec_feB n e s d r a hk (by omega)
 let I1 := I0 ⊕ FOut e s d a
 have htot_dp : EC (dpCost + 20 * (k + 2) + 8)
     (fun (y : I1 → Bool) (_ : Unit) =>
       let tot := cDR e s d a hk hsL (Sum.elim (fun x => y (inr x)) (Sum.elim (fun _ => false) (fun _ => false)))
       !(bSC (k + 1) (Sum.elim (fun b => rT (fun a => y (inl a)) b) tot) (inr ()))) := by
   have hin := ec_pair (ec_proj (fun x : FOut e s d a => (inr x : I1)))
     (ec_pair (ec_const (ι := I1) (fun (_ : Fin k) => false)) (ec_const (ι := I1) (fun (_ : Fin k) => false)))
   have hc := ec_comp hin (ec_cDR e s d a hk hsL)
   let I1b := I1 ⊕ Fin (k + 1)
   let sel : Fin (k + 1) ⊕ Fin (k + 1) → I1b :=
     Sum.elim (fun b => inl (inl (inr (inr (inr (inr (inr (inr (inr (inr (inl b)))))))))))
       (fun b => inr b)
   have hsub := ec_comp (ec_proj sel) (ec_bSC (k + 1))
   rw [zero_add] at hsub
   have hnot := ec_not_of (ec_comp hsub (ec_proj (fun (_ : Unit) => (inr () : Fin (k + 1) ⊕ Unit))))
   rw [Fintype.card_unit, add_zero] at hnot
   have hlt := ec_let hc hnot
   refine ec_le (ec_eq ?_ hlt) (by dsimp only [dpCost, q, k, D, L]; omega)
   intro y u; congr 2; funext z; rcases z with _ | _ <;> rfl
 have hfold : ∀ t : ℕ,
     EC (2 + t * (dpCost + 40 * (k + 2)))
       (fun (y : I1 → Bool) =>
         ((List.finRange k).take t).foldl
           (fun st stepIdx =>
             let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
             uSt e s d a hk hsL pos (Sum.elim (fun x => y (inr x)) st))
           (Sum.elim (fun b => rT (fun a => y (inl a)) b) (fun _ => false))) := by
   intro t
   induction t with
   | zero =>
     have hp := ec_pair
       (ec_proj (fun b : Fin (k + 1) =>
         (inl (inr (inr (inr (inr (inr (inr (inr (inr (inl b))))))))) : I1)))
       (ec_const (ι := I1) (fun (_ : Fin k) => false))
     refine ec_le (ec_eq ?_ hp) (by omega)
     intro y q0; rcases q0 with b | b <;> rfl
   | succ t ih =>
     by_cases ht : t < k
     · let si : Fin k := ⟨t, ht⟩
       let pos : Fin k := ⟨k - 1 - t, by omega⟩
       let sel : FOut e s d a ⊕ (Fin (k + 1) ⊕ Fin k) → I1 ⊕ (Fin (k + 1) ⊕ Fin k) :=
         Sum.elim (fun x => inl (inr x)) (fun r => inr r)
       have hstep := ec_comp (ec_proj sel) (ec_uSt e s d a hk hsL pos)
       rw [zero_add] at hstep
       have htot := ec_let ih hstep
       refine ec_le (ec_eq ?_ htot) (by change 2 + t * (dpCost + 40 * (k + 2)) + (dpCost + 40 * (k + 2)) ≤ 2 + (t + 1) * (dpCost + 40 * (k + 2)); rw [Nat.succ_mul t, Nat.add_assoc])
       intro y q0
       have htk : (List.finRange k).take (t + 1) = (List.finRange k).take t ++ [si] := by
         have h1 := List.take_succ_eq_append_getElem (l := List.finRange k) (i := t) (by simp; omega)
         simpa [si] using h1
       simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
       congr 1; funext x; rcases x with _ | _ <;> rfl
     · have htk : (List.finRange k).take (t + 1) = (List.finRange k).take t := by
         rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
       refine ec_le (ec_eq ?_ ih) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ t)) 2)
       intro y q0; simp only [htk]
 have hfold_k := hfold k
 rw [show (List.finRange k).take k = List.finRange k by rw [List.take_of_length_le]; simp] at hfold_k
 let I2 := I1 ⊕ (Unit ⊕ (Fin (k + 1) ⊕ Fin k))
 let jWire : Fin (k + 1) → I2 := fun b =>
   inl (inl (inr (inr (inr (inr (inr (inr (inr (inr (inr b))))))))))
 have hfinal : EC (12 * (k + 2) * (k + 2))
     (fun (z : I2 → Bool) (_ : Unit) =>
       let validAll := z (inl (inr (inl ())))
       let tLtTot := z (inr (inl ()))
       let wStar : Fin k → Bool := fun u => z (inr (inr (inr u)))
       let jBits : Fin (k + 1) → Bool := fun b => z (jWire b)
       let bitOk := eCB (k + 1) 0 jBits () ||
         decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) jBits () = true ∧ wStar u = true)
       validAll && tLtTot && bitOk) := by
   have hj0 := ec_comp (ec_proj jWire) (ec_eCB (k + 1) 0)
   rw [zero_add] at hj0
   have hex : EC (k * (8 * (k + 1) + 12) + 2 * k + 4)
       (fun (z : I2 → Bool) (_ : Unit) =>
         decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) (fun b => z (jWire b)) () = true ∧
           z (inr (inr (inr u))) = true)) := by
     have hfam := ec_family (s := 8 * (k + 1) + 12)
       (f := fun (u : Fin k) (z : I2 → Bool) (_ : Unit) =>
         eCB (k + 1) (u.val + 1) (fun b => z (jWire b)) () && z (inr (inr (inr u))))
       (fun u => by
         have heq := ec_comp (ec_proj jWire) (ec_eCB (k + 1) (u.val + 1))
         rw [zero_add] at heq
         have hand := ec_and_of heq (ec_proj (fun (_ : Unit) => (inr (inr (inr u)) : I2)))
         rw [Fintype.card_unit] at hand; exact ec_le hand (by omega))
     rw [Fintype.card_fin] at hfam
     have hp := ec_comp hfam (ec_proj (fun u : Fin k => (u, ())))
     rw [add_zero] at hp
     have hany := ec_comp hp (ec_any (α := Fin k))
     rw [Fintype.card_fin] at hany
     refine ec_le (ec_eq ?_ hany) (by omega)
     intro z u; simp [Bool.and_eq_true]
   have hbit := ec_or_of hj0 hex
   have hva : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inl (inr (inl ())))) := ec_proj _
   have htl : EC 0 (fun (z : I2 → Bool) (_ : Unit) => z (inr (inl ()))) := ec_proj _
   have hand := ec_and_of (ec_and_of hva htl) hbit
   rw [Fintype.card_unit] at hand
   exact ec_le hand (by nlinarith)
 have htot := ec_let hfront (ec_let (ec_pair htot_dp hfold_k) hfinal)
 refine ec_le (ec_eq ?_ htot) ?_
 · intro raw u; rfl
 · have h1 : (dpCost + 20 * (k + 2) + 8) + (2 + k * (dpCost + 40 * (k + 2))) ≤
       (k + 1) * (dpCost + 40 * (k + 2)) := by
     have hstep : dpCost + 20 * (k + 2) + 8 + 2 ≤ dpCost + 40 * (k + 2) := by omega
     calc (dpCost + 20 * (k + 2) + 8) + (2 + k * (dpCost + 40 * (k + 2)))
         = k * (dpCost + 40 * (k + 2)) + (dpCost + 20 * (k + 2) + 8 + 2) := by ring
       _ ≤ k * (dpCost + 40 * (k + 2)) + (dpCost + 40 * (k + 2)) := Nat.add_le_add_left hstep _
       _ = (k + 1) * (dpCost + 40 * (k + 2)) := by ring
   have h2 : 12 * (k + 2) * (k + 2) ≤ 20 * (k + 2) * (k + 2) := by
     have hsq : 0 ≤ (k + 2) * (k + 2) := Nat.zero_le _
     linarith only [hsq]
   change _ + ((dpCost + 20 * (k + 2) + 8) + (2 + k * (dpCost + 40 * (k + 2))) + 12 * (k + 2) * (k + 2)) ≤
     _ + (k + 1) * (dpCost + 40 * (k + 2)) + 20 * (k + 2) * (k + 2)
   omega
lemma int_tb {k : ℕ} (u : ℕ) (hu : u ≤ k) (wBits : Fin k → Bool) (w : Fin (2 ^ k)) :
   let lo := ∑ b ∈ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val), if wBits b then 2 ^ b.val else 0
   (lo ≤ w.val ∧ w.val < lo + 2 ^ (k - u)) ↔
     (∀ b : Fin k, k - u ≤ b.val → w.val.testBit b.val = wBits b) := by
 dsimp only
 let lo := ∑ b ∈ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val), if wBits b then 2 ^ b.val else 0
 let hiPart := ∑ b ∈ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val), if w.val.testBit b.val then 2 ^ b.val else 0
 let loPart := ∑ b ∈ Finset.univ.filter (fun b : Fin k => b.val < k - u), if w.val.testBit b.val then 2 ^ b.val else 0
 have hw_decomp : w.val = hiPart + loPart := by
   have hbn := bNat_tB k w.val w.isLt
   rw [← hbn]; unfold bNat; dsimp only [hiPart, loPart]
   have hcomp : Finset.univ.filter (fun b : Fin k => b.val < k - u) =
       Finset.univ.filter (fun b : Fin k => ¬ k - u ≤ b.val) := by
     ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
   rw [hcomp]
   exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin k => k - u ≤ b.val) _).symm
 have hloPart_lt : loPart < 2 ^ (k - u) := by
   have hle : loPart ≤ bNat (k - u) (fun b : Fin (k - u) => w.val.testBit b.val) := by
     unfold loPart bNat
     apply le_of_eq
     exact Finset.sum_bij (fun b hb => ⟨b.val, (Finset.mem_filter.mp hb).2⟩)
       (fun _ _ => Finset.mem_univ _)
       (fun _ _ _ _ h => Fin.ext (by simpa [Fin.ext_iff] using h))
       (fun b _ => ⟨⟨b.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩, rfl⟩)
       (fun _ _ => rfl)
   exact lt_of_le_of_lt hle (bNat_lt (k - u) _)
 have hdvd_pow : ∀ b : Fin k, k - u ≤ b.val → 2 ^ (k - u) ∣ 2 ^ b.val := fun b hb =>
   Nat.pow_dvd_pow 2 hb
 have hlo_dvd : 2 ^ (k - u) ∣ lo :=
   Finset.dvd_sum (fun b hb => by split_ifs; exact hdvd_pow b (Finset.mem_filter.mp hb).2; exact dvd_zero _)
 have hhi_dvd : 2 ^ (k - u) ∣ hiPart :=
   Finset.dvd_sum (fun b hb => by split_ifs; exact hdvd_pow b (Finset.mem_filter.mp hb).2; exact dvd_zero _)
 constructor
 · rintro ⟨hge, hlt⟩
   change lo ≤ w.val at hge
   change w.val < lo + 2 ^ (k - u) at hlt
   have hhi_eq : hiPart = lo := by
     obtain ⟨q1, hq1⟩ := hlo_dvd
     obtain ⟨q2, hq2⟩ := hhi_dvd
     rw [hw_decomp, hq1, hq2] at hge hlt
     have hpos : 0 < 2 ^ (k - u) := Nat.pos_of_ne_zero (by positivity)
     have hq_eq : q2 = q1 := by nlinarith
     rw [hq1, hq2, hq_eq]
   intro b hb
   have htb1 : lo.testBit b.val = wBits b := by
     let f : Fin k → Bool := fun b' => if k - u ≤ b'.val then wBits b' else false
     have hlo_eq : lo = bNat k f := by
       unfold lo bNat
       rw [← Finset.sum_subset (Finset.filter_subset (fun b' : Fin k => k - u ≤ b'.val) Finset.univ)]
       · apply Finset.sum_congr rfl; intro b' hb'
         simp only [f, (Finset.mem_filter.mp hb').2, ↓reduceIte]
       · intro b' _ hn
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
         have hf0 : f b' = false := by simp only [f, hn, ↓reduceIte]
         rw [hf0]; rfl
     have hfb : f b = wBits b := by simp only [f, hb, ↓reduceIte]
     rw [hlo_eq, bNat_tb k f b, hfb]
   have htb2 : hiPart.testBit b.val = w.val.testBit b.val := by
     let f : Fin k → Bool := fun b' => if k - u ≤ b'.val then w.val.testBit b'.val else false
     have hhi_eq2 : hiPart = bNat k f := by
       unfold hiPart bNat
       rw [← Finset.sum_subset (Finset.filter_subset (fun b' : Fin k => k - u ≤ b'.val) Finset.univ)]
       · apply Finset.sum_congr rfl; intro b' hb'
         simp only [f, (Finset.mem_filter.mp hb').2, ↓reduceIte]
       · intro b' _ hn
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
         have hf0 : f b' = false := by simp only [f, hn, ↓reduceIte]
         rw [hf0]; rfl
     have hfb : f b = w.val.testBit b.val := by simp only [f, hb, ↓reduceIte]
     rw [hhi_eq2, bNat_tb k f b, hfb]
   rw [← htb2, hhi_eq, htb1]
 · intro hall
   have hhi_eq : hiPart = lo := Finset.sum_congr rfl (fun b hb => by rw [hall b (Finset.mem_filter.mp hb).2])
   rw [hw_decomp, hhi_eq]; omega
lemma uOut_sp {n e s d r a : ℕ} (hs : 0 < s) (hr : 4 ≤ r) (h2s : 2 * s ≤ d) (hd3s : d < 3 * s)
   (edges : Fin e → Fin (n + 1) × Fin (n + 1))
   (nr nc : Fin (2 ^ (3 * (e + 1) * s))) (cr cc : Fin r → Fin (2 ^ (3 * (e + 1) * s)))
   (off : Fin (3 * (e + 1) * s)) (bank : Fin (3 * (e + 1)) → Bool)
   (y : Fin (2 ^ (2 * n + 1))) (t : Fin (2 ^ (3 * (e + 1) * s + 1))) (j : Fin (3 * (e + 1) * s + 1))
   (raw : RIn n e s r → Bool)
   (hG : ∀ (ei : Fin e) (b : Fin (n + 1)),
     rEdg raw ei false b = (edges ei).1.val.testBit b.val ∧
     rEdg raw ei true b = (edges ei).2.val.testBit b.val)
   (hnr : ∀ p, rNr raw p = nr.val.testBit p.val)
   (hnc : ∀ p, rNc raw p = nc.val.testBit p.val)
   (hcr : ∀ ri p, rCr raw ri p = (cr ri).val.testBit p.val)
   (hcc : ∀ ci p, rCc raw ci p = (cc ci).val.testBit p.val)
   (hoff : ∀ p, rOff raw p = off.val.testBit p.val)
   (hbank : ∀ i, rBnk raw i = bank i)
   (hy : ∀ b, rY raw b = y.val.testBit b.val)
   (ht : ∀ b, rT raw b = t.val.testBit b.val)
   (hj : ∀ b, rJ raw b = j.val.testBit b.val) :
   let q := 3 * (e + 1)
   let k := q * s
   let hk : 0 < k := by positivity
   let hsL : s ≤ d + 1 - s := by omega
   let E := List.ofFn edges
   let comps := fun F : List (Fin (n + 1) × Fin (n + 1)) =>
     Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F))
   let width := (Finset.range (e + 1)).sup (fun h =>
     n + 1 + comps E - (comps (E.take h) + comps (E.drop h)))
   let P := makeP E
   let valid := width ≤ a ∧ ∀ i : Fin q, reachN r (bank i) ≤ d
   let hit := fun (w : Fin (2 ^ k)) =>
     (List.finRange q).foldl (fun z i =>
       let p := (off.val + i.val * s) % k
       let col := bank i
       let bit := (stateN k r col w.val (if col then nc.val else nr.val)
         (if col then cc else cr)).testBit ((p + delayN r col) % k)
       if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val
   uOut n e s d r a hk hsL raw () =
     decide (valid ∧ ∃ w : Fin (2 ^ k), hit w ∧
       Nat.card { z : Fin (2 ^ k) // z < w ∧ hit z } = t.val ∧
       (j.val = 0 ∨ w.val.testBit (j.val - 1) = true)) := by
 dsimp only
 let q := 3 * (e + 1)
 let k := q * s
 let m := 2 * n + 1
 let D := 1 + 2 * a
 let E := List.ofFn edges
 let P := makeP E
 have hk : 0 < k := by positivity
 have hsL : s ≤ d + 1 - s := by omega
 let comps := fun F : List (Fin (n + 1) × Fin (n + 1)) =>
   Nat.card (Quot (fun u v : Fin (n + 1) => (u, v) ∈ F))
 let width := (Finset.range (e + 1)).sup (fun h =>
   n + 1 + comps E - (comps (E.take h) + comps (E.drop h)))
 let valid := width ≤ a ∧ ∀ i : Fin q, reachN r (bank i) ≤ d
 let hit := fun (w : Fin (2 ^ k)) =>
   (List.finRange q).foldl (fun z i =>
     let p := (off.val + i.val * s) % k
     let col := bank i
     let bit := (stateN k r col w.val (if col then nc.val else nr.val)
       (if col then cc else cr)).testBit ((p + delayN r col) % k)
     if bit then z ^^^ (P[i.val]?.getD 0) else z) 0 = y.val
 let fo := feB n e s d r a hk (by omega) raw
 let Pmat := buildP n e s r raw
 let Pvec : Fin q → Fin m → ZMod 2 := fun i j => b2z (Pmat (i, j))
 have hPvec_eq : ∀ i j, Pvec i j = vecBit m (P[i.val]?.getD 0) j := by
   intro i j; dsimp only [Pvec, Pmat, vecBit, b2z]; rw [buildP_spec edges raw hG i j]
 have hPlen : P.length = q := by rw [makeP_length, List.length_ofFn]
 let peakFn : ℕ → ℕ := fun h => Module.finrank (ZMod 2) ↥(
   Submodule.span (ZMod 2)
     (↑((P.take h).map (fun w (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset : Set (Fin m → ZMod 2)) ⊓
   Submodule.span (ZMod 2)
     (↑((P.drop h).map (fun w (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset : Set (Fin m → ZMod 2)))
 have hpeak_eq : (Finset.range (q + 1)).sup peakFn = 1 + 2 * width := peak_eq_one_add_two_width edges
 have hover_iff : (decide (∃ i : Fin q,
     sOv (fun x => rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr (i, x))) = true) = false) ↔
     width ≤ a := by
   rw [decide_eq_false_iff_not, (rBC_sp (D := D) Pmat).1]
   have hspan_eq : ∀ h : ℕ, h ≤ q →
       Module.finrank (ZMod 2) ↥(Lsub Pvec h ⊓ Rsub Pvec h) = peakFn h := by
     intro h _
     have hPfun : Pvec = fun i : Fin q => vecBit m (P[i.val]?.getD 0) := funext (fun i => funext (hPvec_eq i))
     rw [hPfun, Lsub_eq_list_take P hPlen h, Rsub_eq_list_drop P hPlen h]
   constructor
   · intro hno
     have hsup_le : (Finset.range (q + 1)).sup peakFn ≤ D := by
       rw [Finset.sup_le_iff]
       intro h hh
       have hhq : h ≤ q := by rw [Finset.mem_range] at hh; omega
       rw [← hspan_eq h hhq]
       by_contra hgt; push Not at hgt; exact hno ⟨h, hhq, hgt⟩
     rw [hpeak_eq] at hsup_le; dsimp [D] at hsup_le; omega
   · intro hwa ⟨h, hhq, hgt⟩
     have hle : Module.finrank (ZMod 2) ↥(Lsub Pvec h ⊓ Rsub Pvec h) ≤ 1 + 2 * width := by
       rw [hspan_eq h hhq, ← hpeak_eq]
       exact Finset.le_sup (f := peakFn) (Finset.mem_range.mpr (by omega))
     change 1 + 2 * a < Module.finrank (ZMod 2) ↥(Lsub Pvec h ⊓ Rsub Pvec h) at hgt; omega
 have hbank_iff : (decide (∀ i : Fin q,
     (if rBnk raw i then decide (reachN r true ≤ d) else decide (reachN r false ≤ d)) = true) = true) ↔
     (∀ i : Fin q, reachN r (bank i) ≤ d) := by
   rw [decide_eq_true_iff]
   apply forall_congr'; intro i
   rw [hbank i]; cases bank i <;> simp
 have hyOk_iff : ((!(rPC (rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw)))
     (Fin.last q))) = true) ↔
     ∃ α : Fin q → ZMod 2, ∑ i : Fin q, α i • Pvec i = fun b : Fin m => b2z (y.val.testBit b.val) := by
   rw [Bool.not_eq_true']
   have h := (rref_solve_spec (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw)).1
   rw [show (fun b => b2z (rY raw b)) = (fun b => b2z (y.val.testBit b.val)) by funext b; rw [hy b]] at h
   exact h
 have hhit_implies_yOk : (∃ w : Fin (2 ^ k), hit w) →
     ∃ α : Fin q → ZMod 2, ∑ i : Fin q, α i • Pvec i = fun b : Fin m => b2z (y.val.testBit b.val) := by
   rintro ⟨w, hw⟩
   let bitOf : Fin q → Bool := fun i =>
     (stateN k r (bank i) w.val (if bank i then nc.val else nr.val)
       (if bank i then cc else cr)).testBit (((off.val + i.val * s) % k + delayN r (bank i)) % k)
   refine ⟨fun i => b2z (bitOf i), ?_⟩
   have hfold_bit : ∀ (ls : List (Fin q)) (hnd : ls.Nodup) (acc : ℕ) (b : Fin m),
       b2z ((ls.foldl (fun z i => if bitOf i then z ^^^ (P[i.val]?.getD 0) else z) acc).testBit b.val) =
         b2z (acc.testBit b.val) + ∑ i ∈ ls.toFinset, b2z (bitOf i) * Pvec i b := by
     intro ls; induction ls with
     | nil => intro _ acc b; simp
     | cons i tl ih =>
       intro hnd acc b; rw [List.nodup_cons] at hnd
       rw [List.foldl_cons, ih hnd.2, List.toFinset_cons, Finset.sum_insert (by simpa using hnd.1)]
       have hstep : b2z ((if bitOf i then acc ^^^ (P[i.val]?.getD 0) else acc).testBit b.val) =
           b2z (acc.testBit b.val) + b2z (bitOf i) * Pvec i b := by
         rw [hPvec_eq i b]; unfold vecBit
         cases bitOf i
         · simp only [Bool.false_eq_true, ↓reduceIte, b2z, zero_mul, add_zero]
         · simp only [↓reduceIte, Nat.testBit_xor]
           cases acc.testBit b.val <;> cases (P[i.val]?.getD 0).testBit b.val <;> decide
       rw [hstep]; ring
   funext b
   simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
   have hb := hfold_bit (List.finRange q) (List.nodup_finRange q) 0 b
   rw [hw, show (List.finRange q).toFinset = Finset.univ by ext x; simp, Nat.zero_testBit] at hb
   have h0 : b2z false = 0 := rfl
   rw [h0, zero_add] at hb
   exact hb.symm
 cases hva : fo (inl ())
 ·
   have hlhs : uOut n e s d r a hk hsL raw () = false := by
     unfold uOut; dsimp only
     rw [show feB n e s d r a hk (by omega) raw (inl ()) = false from hva]; rfl
   rw [hlhs]; symm; rw [decide_eq_false_iff_not]
   rintro ⟨⟨hwa, hbr⟩, ⟨w, hhit, _, _⟩⟩
   have h1 : decide (∀ i : Fin q,
       (if rBnk raw i then decide (reachN r true ≤ d) else decide (reachN r false ≤ d)) = true) = true :=
     hbank_iff.mpr hbr
   have h2 : ((!(rPC (rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw)))
       (Fin.last q))) = true) := hyOk_iff.mpr (hhit_implies_yOk ⟨w, hhit⟩)
   have h3 : ((!(decide (∃ i : Fin q,
       sOv (fun x => rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr (i, x))) = true))) = true) := by
     rw [Bool.not_eq_true']; exact hover_iff.mpr hwa
   have htrue : fo (inl ()) = true := by
     change ((decide (∀ i : Fin q,
         (if rBnk raw i then decide (reachN r true ≤ d) else decide (reachN r false ≤ d)) = true)) &&
       (!(rPC (rref (aMt (fun (i : Fin q) (j : Fin m) => Pmat (i, j)) (rY raw))) (Fin.last q))) &&
       (!(decide (∃ i : Fin q,
         sOv (fun x => rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr (i, x))) = true)))) = true
     rw [h1, h2, h3]; rfl
   rw [hva] at htrue; exact Bool.noConfusion htrue
 ·
   have hvalid : valid := by
     have hv1 := (Bool.and_eq_true _ _).mp hva
     have hv2 := (Bool.and_eq_true _ _).mp hv1.1
     have hno : decide (∃ i : Fin q,
         sOv (fun x => rBC q D m (Sum.elim Pmat (bSN q m Pmat)) (inr (i, x))) = true) = false := by
       simpa using hv1.2
     exact ⟨hover_iff.mp hno, hbank_iff.mp hv2.1⟩
   have hcnt_spec : ∀ maskF valF : Fin k → Bool,
       bNat (k + 1) (cDR e s d a hk hsL (Sum.elim fo (Sum.elim maskF valF))) =
         Nat.card { w : Fin (2 ^ k) // hit w ∧ ∀ b : Fin k, maskF b = true → w.val.testBit b.val = valF b } :=
     fun maskF valF => cDR_sp hs hr h2s hd3s edges nr nc cr cc off bank y t t raw
       hG hnr hnc hcr hcc hoff hbank hy hva maskF valF
   let totBits := cDR e s d a hk hsL (Sum.elim fo (Sum.elim (fun _ => false) (fun _ => false)))
   have htot_val : bNat (k + 1) totBits = Nat.card { w : Fin (2 ^ k) // hit w } := by
     rw [hcnt_spec (fun _ => false) (fun _ => false), Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
     exact Fintype.card_congr ⟨fun ⟨w, h, _⟩ => ⟨w, h⟩, fun ⟨w, h⟩ => ⟨w, h, fun _ hm => Bool.noConfusion hm⟩,
       fun _ => rfl, fun _ => rfl⟩
   have hrawT_val : bNat (k + 1) (rT raw) = t.val := by
     rw [show rT raw = fun b => t.val.testBit b.val from funext ht]
     exact bNat_tB (k + 1) t.val t.isLt
   have hsubTot := (bSC_sp (k + 1) (rT raw) totBits).1
   rw [hrawT_val, htot_val] at hsubTot
   by_cases htlt : t.val < Nat.card { w : Fin (2 ^ k) // hit w }
   ·
     have htLtTot : ((!(bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ()))) = true) := by
       rw [Bool.not_eq_true']
       cases hc : bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ())
       · rfl
       · have := hsubTot.mp hc; omega
     let stAt : ℕ → Fin (k + 1) ⊕ Fin k → Bool := fun u =>
       ((List.finRange k).take u).foldl
         (fun st stepIdx =>
           let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
           uSt e s d a hk hsL pos (Sum.elim fo st))
         (Sum.elim (rT raw) (fun _ => false))
     let loAt : ℕ → ℕ := fun u =>
       ∑ b ∈ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val), if stAt u (inr b) then 2 ^ b.val else 0
     have hind : ∀ u : ℕ, u ≤ k →
         Nat.card { w : Fin (2 ^ k) // hit w ∧ w.val < loAt u } + bNat (k + 1) (fun b => stAt u (inl b)) = t.val ∧
         bNat (k + 1) (fun b => stAt u (inl b)) <
           Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u ≤ w.val ∧ w.val < loAt u + 2 ^ (k - u) } := by
       intro u
       induction u with
       | zero =>
         intro _
         have hlo0 : loAt 0 = 0 := by
           dsimp only [loAt]; apply Finset.sum_eq_zero; intro b hb
           rw [Finset.mem_filter] at hb; have := b.isLt; omega
         have hrem0 : bNat (k + 1) (fun b => stAt 0 (inl b)) = t.val := hrawT_val
         rw [hlo0, hrem0]
         have hlt0 : Nat.card { w : Fin (2 ^ k) // hit w ∧ w.val < 0 } = 0 := by
           rw [Nat.card_eq_fintype_card]; exact Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, _, h⟩ => by omega⟩
         have hall_eq : Nat.card { w : Fin (2 ^ k) // hit w ∧ 0 ≤ w.val ∧ w.val < 0 + 2 ^ (k - 0) } =
             Nat.card { w : Fin (2 ^ k) // hit w } := by
           rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
           exact Fintype.card_congr ⟨fun ⟨w, h, _⟩ => ⟨w, h⟩, fun ⟨w, h⟩ => ⟨w, h, Nat.zero_le _, by rw [zero_add, Nat.sub_zero]; exact w.isLt⟩,
             fun _ => rfl, fun _ => rfl⟩
         rw [hlt0, zero_add, hall_eq]; exact ⟨rfl, htlt⟩
       | succ u ih =>
         intro hu
         obtain ⟨ih_sum, ih_lt⟩ := ih (by omega)
         let si : Fin k := ⟨u, hu⟩
         let pos : Fin k := ⟨k - 1 - u, by omega⟩
         have hst_succ : stAt (u + 1) = uSt e s d a hk hsL pos (Sum.elim fo (stAt u)) := by
           dsimp only [stAt]
           have htk : (List.finRange k).take (u + 1) = (List.finRange k).take u ++ [si] := by
             have h1 := List.take_succ_eq_append_getElem (l := List.finRange k) (i := u) (by simp; omega)
             simpa [si] using h1
           rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
         let wU : Fin k → Bool := fun b => stAt u (inr b)
         let remU : Fin (k + 1) → Bool := fun b => stAt u (inl b)
         let mask0 : Fin k → Bool := fun b => decide (pos.val ≤ b.val)
         let val0 : Fin k → Bool := fun b => if b = pos then false else wU b
         let cnt0Bits := cDR e s d a hk hsL (Sum.elim fo (Sum.elim mask0 val0))
         let sub := bSC (k + 1) (Sum.elim remU cnt0Bits)
         let goRight : Bool := sub (inr ())
         have hwNext : ∀ b : Fin k, stAt (u + 1) (inr b) = if b = pos then goRight else wU b := fun b => by
           rw [hst_succ]; rfl
         have hremNext : (fun b => stAt (u + 1) (inl b)) =
             fun b => if goRight then sub (inl b) else remU b := by
           funext b; rw [hst_succ]; rfl
         have hlo_succ : loAt (u + 1) = loAt u + (if goRight then 2 ^ (k - 1 - u) else 0) := by
           dsimp only [loAt]
           have hfilt : Finset.univ.filter (fun b : Fin k => k - (u + 1) ≤ b.val) =
               insert pos (Finset.univ.filter (fun b : Fin k => k - u ≤ b.val)) := by
             ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Fin.ext_iff, pos]; omega
           have hnot : pos ∉ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val) := by
             simp only [Finset.mem_filter, Finset.mem_univ, true_and, pos]; omega
           rw [hfilt, Finset.sum_insert hnot, hwNext pos]
           simp only [↓reduceIte, pos]
           rw [add_comm]
           congr 1
           apply Finset.sum_congr rfl; intro b hb
           have hne : b ≠ pos := fun h => hnot (h ▸ hb)
           rw [hwNext b]; simp only [hne, ↓reduceIte]; rfl
         have hcnt0_eq : bNat (k + 1) cnt0Bits =
             Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u ≤ w.val ∧ w.val < loAt u + 2 ^ (k - 1 - u) } := by
           rw [hcnt_spec mask0 val0, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
           have hlo_val0 : (∑ b ∈ Finset.univ.filter (fun b : Fin k => k - (u + 1) ≤ b.val),
               if val0 b then 2 ^ b.val else 0) = loAt u := by
             dsimp only [loAt]
             have hfilt : Finset.univ.filter (fun b : Fin k => k - (u + 1) ≤ b.val) =
                 insert pos (Finset.univ.filter (fun b : Fin k => k - u ≤ b.val)) := by
               ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                 Fin.ext_iff, pos]; omega
             have hnot : pos ∉ Finset.univ.filter (fun b : Fin k => k - u ≤ b.val) := by
               simp only [Finset.mem_filter, Finset.mem_univ, true_and, pos]; omega
             rw [hfilt, Finset.sum_insert hnot]
             simp only [val0, ↓reduceIte, Bool.false_eq_true, zero_add]
             apply Finset.sum_congr rfl; intro b hb
             have hne : b ≠ pos := fun h => hnot (h ▸ hb)
             simp only [hne, ↓reduceIte]; rfl
           refine Fintype.card_congr
             { toFun := fun ⟨w, hh, hmk⟩ => ⟨w, hh, by
                 have hint := (int_tb (u + 1) hu val0 w).mpr (fun b hb => by
                   exact hmk b (decide_eq_true (by dsimp [pos]; omega)))
                 rw [hlo_val0] at hint
                 simpa [show k - (u + 1) = k - 1 - u by omega] using hint⟩
               invFun := fun ⟨w, hh, hge, hlt⟩ => ⟨w, hh, fun b hmb => by
                 have hble : k - (u + 1) ≤ b.val := by
                   have := of_decide_eq_true hmb; dsimp [pos] at this; omega
                 have hint := (int_tb (u + 1) hu val0 w).mp
                   (by rw [hlo_val0]; simpa [show k - (u + 1) = k - 1 - u by omega] using And.intro hge hlt)
                 exact hint b hble⟩
               left_inv := fun _ => rfl
               right_inv := fun _ => rfl }
         have hpow_split : 2 ^ (k - u) = 2 ^ (k - 1 - u) + 2 ^ (k - 1 - u) := by
           have heq : k - u = (k - 1 - u) + 1 := by omega
           rw [heq, pow_succ]; omega
         have hpart_lr : Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u ≤ w.val ∧ w.val < loAt u + 2 ^ (k - 1 - u) } +
             Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u + 2 ^ (k - 1 - u) ≤ w.val ∧ w.val < loAt u + 2 ^ (k - u) } =
             Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u ≤ w.val ∧ w.val < loAt u + 2 ^ (k - u) } := by
           simp only [Nat.card_eq_fintype_card, ← Fintype.card_sum]
           refine Fintype.card_congr
             { toFun := fun x => match x with
                 | inl ⟨w, h, h1, h2⟩ => ⟨w, h, h1, by omega⟩
                 | inr ⟨w, h, h1, h2⟩ => ⟨w, h, by omega, h2⟩
               invFun := fun ⟨w, h, h1, h2⟩ =>
                 if hlt : w.val < loAt u + 2 ^ (k - 1 - u) then inl ⟨w, h, h1, hlt⟩
                 else inr ⟨w, h, by omega, h2⟩
               left_inv := fun x => by
                 rcases x with ⟨w, h, h1, h2⟩ | ⟨w, h, h1, h2⟩
                 · simp [h2]
                 · have hnot : ¬ w.val < loAt u + 2 ^ (k - 1 - u) := by omega
                   simp [hnot]
               right_inv := fun ⟨w, h, h1, h2⟩ => by dsimp only; split_ifs <;> rfl }
         have hsub_spec := bSC_sp (k + 1) remU cnt0Bits
         cases hgr : goRight
         ·
           have hlt_cnt : bNat (k + 1) remU < bNat (k + 1) cnt0Bits := by
             by_contra hge; push Not at hge
             have := hsub_spec.1.mpr hge; change goRight = true at this; rw [hgr] at this; exact Bool.noConfusion this
           rw [hremNext, hlo_succ, hgr]
           simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
           rw [hcnt0_eq] at hlt_cnt
           exact ⟨ih_sum, by simpa [show k - (u + 1) = k - 1 - u by omega] using hlt_cnt⟩
         ·
           have hle_cnt : bNat (k + 1) cnt0Bits ≤ bNat (k + 1) remU := hsub_spec.1.mp hgr
           have hrem_diff : bNat (k + 1) (fun b => sub (inl b)) = bNat (k + 1) remU - bNat (k + 1) cnt0Bits :=
             hsub_spec.2 hle_cnt
           rw [hremNext, hlo_succ, hgr]
           simp only [↓reduceIte, hrem_diff]
           have hpart_less : Nat.card { w : Fin (2 ^ k) // hit w ∧ w.val < loAt u } +
               Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt u ≤ w.val ∧ w.val < loAt u + 2 ^ (k - 1 - u) } =
               Nat.card { w : Fin (2 ^ k) // hit w ∧ w.val < loAt u + 2 ^ (k - 1 - u) } := by
             simp only [Nat.card_eq_fintype_card, ← Fintype.card_sum]
             refine Fintype.card_congr
               { toFun := fun x => match x with
                   | inl ⟨w, h, h1⟩ => ⟨w, h, Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)⟩
                   | inr ⟨w, h, _, h2⟩ => ⟨w, h, h2⟩
                 invFun := fun ⟨w, h, hlt⟩ =>
                   if h1 : w.val < loAt u then inl ⟨w, h, h1⟩
                   else inr ⟨w, h, by omega, hlt⟩
                 left_inv := fun x => by
                   rcases x with ⟨w, h, h1⟩ | ⟨w, h, h1, h2⟩
                   · simp [h1]
                   · have hnot : ¬ w.val < loAt u := by omega
                     simp [hnot]
                 right_inv := fun ⟨w, h, hlt⟩ => by dsimp only; split_ifs <;> rfl }
           rw [hcnt0_eq] at hle_cnt ⊢
           have h1 : loAt u + 2 ^ (k - 1 - u) + 2 ^ (k - (u + 1)) = loAt u + 2 ^ (k - u) := by
             rw [show k - (u + 1) = k - 1 - u by omega]; omega
           rw [h1]
           dsimp only [remU] at hle_cnt ⊢
           constructor <;> omega
     obtain ⟨hfinal_sum, hfinal_lt⟩ := hind k le_rfl
     have hlo_k_eq : loAt k = bNat k (fun b => stAt k (inr b)) := by
       dsimp only [loAt, bNat]
       have hf : Finset.univ.filter (fun b : Fin k => k - k ≤ b.val) = Finset.univ := by ext b; simp
       rw [hf]
     have hlo_k_lt : loAt k < 2 ^ k := by rw [hlo_k_eq]; exact bNat_lt k _
     let wStar : Fin (2 ^ k) := ⟨loAt k, hlo_k_lt⟩
     have hcard_sing : Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt k ≤ w.val ∧ w.val < loAt k + 2 ^ (k - k) } ≤ 1 := by
       rw [Nat.card_eq_fintype_card, Nat.sub_self, pow_zero]
       have hsub : Subsingleton { w : Fin (2 ^ k) // hit w ∧ loAt k ≤ w.val ∧ w.val < loAt k + 1 } :=
         ⟨fun ⟨w1, _, a1, b1⟩ ⟨w2, _, a2, b2⟩ =>
           Subtype.ext (Fin.ext ((Nat.le_antisymm (Nat.le_of_lt_succ b1) a1).trans (Nat.le_antisymm (Nat.le_of_lt_succ b2) a2).symm))⟩
       exact Fintype.card_le_one_iff_subsingleton.mpr hsub
     have hrem_zero : bNat (k + 1) (fun b => stAt k (inl b)) = 0 := by omega
     have hcard_pos : 0 < Nat.card { w : Fin (2 ^ k) // hit w ∧ loAt k ≤ w.val ∧ w.val < loAt k + 1 } := by
       simpa [Nat.sub_self] using lt_of_le_of_lt (Nat.zero_le _) hfinal_lt
     have hwStar_hit : hit wStar := by
       rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hcard_pos
       obtain ⟨w, hhit, hge, hlt⟩ := hcard_pos.some
       have heq : w = wStar := Fin.ext (by dsimp [wStar]; omega)
       rwa [← heq]
     have hwStar_rank : Nat.card { z : Fin (2 ^ k) // z < wStar ∧ hit z } = t.val := by
       rw [hrem_zero, add_zero] at hfinal_sum
       rw [← hfinal_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
       exact Fintype.card_congr ⟨fun ⟨z, hz, hh⟩ => ⟨z, hh, hz⟩, fun ⟨z, hh, hz⟩ => ⟨z, hz, hh⟩,
         fun _ => rfl, fun _ => rfl⟩
     have hwStar_uniq : ∀ w : Fin (2 ^ k), hit w → Nat.card { z : Fin (2 ^ k) // z < w ∧ hit z } = t.val → w = wStar := by
       intro w hhw hrk
       by_contra hne
       have hlt_or : w < wStar ∨ wStar < w := lt_or_gt_of_ne hne
       have hstrict : ∀ a b : Fin (2 ^ k), a < b → hit a →
           Nat.card { z : Fin (2 ^ k) // z < a ∧ hit z } < Nat.card { z : Fin (2 ^ k) // z < b ∧ hit z } := by
         intro a b hab ha
         rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
         have hfin : (Finset.univ.filter (fun z : Fin (2 ^ k) => z < a ∧ hit z)) ⊂
             (Finset.univ.filter (fun z : Fin (2 ^ k) => z < b ∧ hit z)) := by
           rw [Finset.ssubset_iff_of_subset]
           · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, ha⟩, by simp⟩
           · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
             exact ⟨lt_trans hz.1 hab, hz.2⟩
         have hc := Finset.card_lt_card hfin
         simpa [Fintype.card_subtype] using hc
       rcases hlt_or with hlt | hgt
       · have := hstrict w wStar hlt hhw; omega
       · have := hstrict wStar w hgt hwStar_hit; omega
     have hstK_eq : (List.finRange k).foldl
         (fun st stepIdx =>
           let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
           uSt e s d a hk hsL pos (Sum.elim fo st))
         (Sum.elim (rT raw) (fun _ => false)) = stAt k := by
       dsimp only [stAt]; rw [List.take_of_length_le (by simp)]
     have hwStar_bit : ∀ u : Fin k, stAt k (inr u) = wStar.val.testBit u.val := fun u => by
       dsimp only [wStar]; rw [hlo_k_eq, bNat_tb]
     have hbitOk : (eCB (k + 1) 0 (rJ raw) () ||
         decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) (rJ raw) () = true ∧
           stAt k (inr u) = true)) =
         decide (j.val = 0 ∨ wStar.val.testBit (j.val - 1) = true) := by
       have hjlt : j.val < 2 ^ (k + 1) := lt_trans j.isLt Nat.lt_two_pow_self
       have heq0 := eCB_sp (k + 1) 0 (rJ raw) j.val hjlt (Nat.pos_of_ne_zero (by positivity)) hj
       have hequ : ∀ u : Fin k, eCB (k + 1) (u.val + 1) (rJ raw) () = decide (j.val = u.val + 1) := fun u =>
         eCB_sp (k + 1) (u.val + 1) (rJ raw) j.val hjlt
           (lt_of_lt_of_le (by have := u.isLt; omega : u.val + 1 < k + 1) (Nat.le_of_lt Nat.lt_two_pow_self)) hj
       rw [heq0]
       simp_rw [hequ, hwStar_bit]
       by_cases hj0 : j.val = 0
       · simp [hj0]
       · simp only [hj0, decide_false, Bool.false_or, false_or, decide_eq_decide]
         constructor
         · rintro ⟨u, hu, hb⟩; have heq := of_decide_eq_true hu; rw [heq]; simpa using hb
         · intro hb
           exact ⟨⟨j.val - 1, by have := j.isLt; dsimp only [k, q] at *; omega⟩, decide_eq_true (by dsimp only; omega), hb⟩
     have hlhs : uOut n e s d r a hk hsL raw () =
         decide (j.val = 0 ∨ wStar.val.testBit (j.val - 1) = true) := by
       change (fo (inl ()) && !(bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ())) &&
         (eCB (k + 1) 0 (rJ raw) () ||
           decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) (rJ raw) () = true ∧
             ((List.finRange k).foldl
               (fun st stepIdx =>
                 let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
                 uSt e s d a hk hsL pos (Sum.elim fo st))
               (Sum.elim (rT raw) (fun _ => false))) (inr u) = true))) = _
       rw [hva, htLtTot, Bool.true_and, Bool.true_and, hstK_eq, hbitOk]
     rw [hlhs]
     simp only [decide_eq_decide]
     constructor
     · intro hbit; exact ⟨hvalid, wStar, hwStar_hit, hwStar_rank, hbit⟩
     · rintro ⟨_, w, hhw, hrk, hbit⟩
       rwa [hwStar_uniq w hhw hrk] at hbit
   ·
     have hge : bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ()) = true := hsubTot.mpr (by omega)
     have htGeTot : ((!(bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ()))) = false) := by
       rw [hge]; rfl
     have hlhs : uOut n e s d r a hk hsL raw () = false := by
       change (fo (inl ()) && !(bSC (k + 1) (Sum.elim (rT raw) totBits) (inr ())) &&
         (eCB (k + 1) 0 (rJ raw) () ||
           decide (∃ u : Fin k, eCB (k + 1) (u.val + 1) (rJ raw) () = true ∧
             ((List.finRange k).foldl
               (fun st stepIdx =>
                 let pos : Fin k := ⟨k - 1 - stepIdx.val, by omega⟩
                 uSt e s d a hk hsL pos (Sum.elim fo st))
               (Sum.elim (rT raw) (fun _ => false))) (inr u) = true))) = false
       rw [hva, htGeTot]; rfl
     rw [hlhs]; symm; rw [decide_eq_false_iff_not]
     rintro ⟨_, w, hhw, hrk, _⟩
     have hlt_tot : Nat.card { z : Fin (2 ^ k) // z < w ∧ hit z } < Nat.card { z : Fin (2 ^ k) // hit z } := by
       rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
       have hfin : (Finset.univ.filter (fun z : Fin (2 ^ k) => z < w ∧ hit z)) ⊂
           (Finset.univ.filter (fun z : Fin (2 ^ k) => hit z)) := by
         rw [Finset.ssubset_iff_of_subset]
         · exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhw⟩, by simp⟩
         · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; exact hz.2
       have hc := Finset.card_lt_card hfin
       simpa [Fintype.card_subtype] using hc
     change Nat.card { z : Fin (2 ^ k) // z < w ∧ hit z } = t.val at hrk
     omega
def rTF (n e s r : ℕ) :
   RIn n e s r →
     Fin (2 * e * (n + 1) + 3 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) +
       3 * (e + 1) + (2 * n + 1) + 2 * (3 * (e + 1) * s + 1))
 | inl (ei, side, b) =>
     ⟨ei.val * (2 * (n + 1)) + (if side then n + 1 else 0) + b.val, by
       have hb := b.isLt
       have h1 : ei.val * (2 * (n + 1)) + 2 * (n + 1) ≤ 2 * e * (n + 1) := by
         calc _ = (ei.val + 1) * (2 * (n + 1)) := by ring
           _ ≤ e * (2 * (n + 1)) := Nat.mul_le_mul_right _ ei.isLt
           _ = 2 * e * (n + 1) := by ring
       cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
 | inr (inl p) =>
     ⟨2 * e * (n + 1) + p.val, by have := p.isLt; omega⟩
 | inr (inr (inl p)) =>
     ⟨2 * e * (n + 1) + 3 * (e + 1) * s + p.val, by have := p.isLt; omega⟩
 | inr (inr (inr (inl (ri, p)))) =>
     ⟨2 * e * (n + 1) + 2 * (3 * (e + 1) * s) + ri.val * (3 * (e + 1) * s) + p.val, by
       have hp := p.isLt
       have h1 : ri.val * (3 * (e + 1) * s) + 3 * (e + 1) * s ≤ r * (3 * (e + 1) * s) := by
         calc _ = (ri.val + 1) * (3 * (e + 1) * s) := by ring
           _ ≤ r * (3 * (e + 1) * s) := Nat.mul_le_mul_right _ ri.isLt
       have h2 : 2 * r * (3 * (e + 1) * s) = r * (3 * (e + 1) * s) + r * (3 * (e + 1) * s) := by ring
       have h3 : 3 * (3 * (e + 1) * s) = 2 * (3 * (e + 1) * s) + 3 * (e + 1) * s := by ring
       omega⟩
 | inr (inr (inr (inr (inl (ci, p))))) =>
     ⟨2 * e * (n + 1) + 2 * (3 * (e + 1) * s) + r * (3 * (e + 1) * s) + ci.val * (3 * (e + 1) * s) + p.val, by
       have hp := p.isLt
       have h1 : ci.val * (3 * (e + 1) * s) + 3 * (e + 1) * s ≤ r * (3 * (e + 1) * s) := by
         calc _ = (ci.val + 1) * (3 * (e + 1) * s) := by ring
           _ ≤ r * (3 * (e + 1) * s) := Nat.mul_le_mul_right _ ci.isLt
       have h2 : 2 * r * (3 * (e + 1) * s) = r * (3 * (e + 1) * s) + r * (3 * (e + 1) * s) := by ring
       have h3 : 3 * (3 * (e + 1) * s) = 2 * (3 * (e + 1) * s) + 3 * (e + 1) * s := by ring
       omega⟩
 | inr (inr (inr (inr (inr (inl p))))) =>
     ⟨2 * e * (n + 1) + 2 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) + p.val, by have := p.isLt; omega⟩
 | inr (inr (inr (inr (inr (inr (inl i)))))) =>
     ⟨2 * e * (n + 1) + 3 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) + i.val, by have := i.isLt; omega⟩
 | inr (inr (inr (inr (inr (inr (inr (inl b))))))) =>
     ⟨2 * e * (n + 1) + 3 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) + 3 * (e + 1) + b.val, by have := b.isLt; omega⟩
 | inr (inr (inr (inr (inr (inr (inr (inr (inl b)))))))) =>
     ⟨2 * e * (n + 1) + 3 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) + 3 * (e + 1) + (2 * n + 1) + b.val, by have := b.isLt; omega⟩
 | inr (inr (inr (inr (inr (inr (inr (inr (inr b)))))))) =>
     ⟨2 * e * (n + 1) + 3 * (3 * (e + 1) * s) + 2 * r * (3 * (e + 1) * s) + 3 * (e + 1) + (2 * n + 1) + (3 * (e + 1) * s + 1) + b.val, by have := b.isLt; omega⟩
lemma gD_fm {α β : Type*} (ls : List α) (f : α → List β) (K : ℕ)
   (hlen : ∀ a ∈ ls, (f a).length = K) :
   (ls.flatMap f).length = ls.length * K ∧
   ∀ (i : ℕ) (hi : i < ls.length) (p : ℕ), p < K → ∀ (d : β),
     (ls.flatMap f).getD (i * K + p) d = (f (ls[i]'hi)).getD p d := by
 induction ls with
 | nil => exact ⟨by simp, fun _ hi => by simp at hi⟩
 | cons hd tl ih =>
   have hhd : (f hd).length = K := hlen hd (List.mem_cons_self ..)
   obtain ⟨htl_len, htl_get⟩ := ih (fun a ha => hlen a (List.mem_cons_of_mem _ ha))
   constructor
   · rw [List.flatMap_cons, List.length_append, hhd, htl_len, List.length_cons]; ring
   · intro i hi p hp d
     rw [List.flatMap_cons]
     cases i with
     | zero =>
       simp only [zero_mul, zero_add, List.getElem_cons_zero]
       exact gD_al (f hd) (tl.flatMap f) p (by omega) d
     | succ i' =>
       have hi' : i' < tl.length := by simp at hi; omega
       have hmul1 : (i' + 1) * K = i' * K + K := by ring
       have hmul2 : i' * K + K ≤ tl.length * K := by
         rw [← hmul1]; exact Nat.mul_le_mul_right K hi'
       have hge : (f hd).length ≤ (i' + 1) * K + p := by rw [hhd, hmul1]; omega
       have hlt2 : (i' + 1) * K + p - (f hd).length < (tl.flatMap f).length := by
         rw [hhd, htl_len, hmul1]; omega
       rw [gD_ar (f hd) (tl.flatMap f) _ hge hlt2 d]
       have hsub : (i' + 1) * K + p - (f hd).length = i' * K + p := by rw [hhd, hmul1]; omega
       rw [hsub, htl_get i' hi' p hp d]
       rfl
lemma gD_bl (a x i : ℕ) (hi : i < a) :
   ((List.range a).map (fun j => x.testBit j)).getD i false = x.testBit i := by
 rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range]
lemma getD_seg {α : Type*} (pre seg suf : List α) (n i : ℕ) (hpre : pre.length = n) (hi : i < seg.length) (d : α) :
   (pre ++ seg ++ suf).getD (n + i) d = seg.getD i d := by
 rw [gD_al (pre ++ seg) suf (n + i) (by rw [List.length_append, hpre]; omega) d]
 rw [gD_ar pre seg (n + i) (by omega) (by omega) d]
 rw [show n + i - pre.length = i by omega]
lemma gD_c10 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : List α) (d : α)
   {n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : ℕ}
   (h0 : a0.length = n0) (h1 : a1.length = n1) (h2 : a2.length = n2) (h3 : a3.length = n3)
   (h4 : a4.length = n4) (h5 : a5.length = n5) (h6 : a6.length = n6) (h7 : a7.length = n7)
   (h8 : a8.length = n8) (h9 : a9.length = n9) :
   let L := a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9
   L.length = n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 ∧
   (∀ i < n0, L.getD i d = a0.getD i d) ∧
   (∀ i < n1, L.getD (n0 + i) d = a1.getD i d) ∧
   (∀ i < n2, L.getD (n0 + n1 + i) d = a2.getD i d) ∧
   (∀ i < n3, L.getD (n0 + n1 + n2 + i) d = a3.getD i d) ∧
   (∀ i < n4, L.getD (n0 + n1 + n2 + n3 + i) d = a4.getD i d) ∧
   (∀ i < n5, L.getD (n0 + n1 + n2 + n3 + n4 + i) d = a5.getD i d) ∧
   (∀ i < n6, L.getD (n0 + n1 + n2 + n3 + n4 + n5 + i) d = a6.getD i d) ∧
   (∀ i < n7, L.getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + i) d = a7.getD i d) ∧
   (∀ i < n8, L.getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + i) d = a8.getD i d) ∧
   (∀ i < n9, L.getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + i) d = a9.getD i d) := by
 dsimp only
 have hl : (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9).length =
     n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 := by
   simp only [List.length_append, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
 refine ⟨hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     a0 ++ (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact gD_al a0 _ i (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     a0 ++ a1 ++ (a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg a0 a1 _ n0 i h0 (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1) ++ a2 ++ (a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1) a2 _ (n0 + n1) i (by simp only [List.length_append, h0, h1]) (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1 ++ a2) ++ a3 ++ (a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1 ++ a2) a3 _ (n0 + n1 + n2) i (by simp only [List.length_append, h0, h1, h2]) (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1 ++ a2 ++ a3) ++ a4 ++ (a5 ++ a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1 ++ a2 ++ a3) a4 _ (n0 + n1 + n2 + n3) i (by simp only [List.length_append, h0, h1, h2, h3]) (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1 ++ a2 ++ a3 ++ a4) ++ a5 ++ (a6 ++ a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1 ++ a2 ++ a3 ++ a4) a5 _ (n0 + n1 + n2 + n3 + n4) i (by simp only [List.length_append, h0, h1, h2, h3, h4]) (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5) ++ a6 ++ (a7 ++ a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5) a6 _ (n0 + n1 + n2 + n3 + n4 + n5) i (by simp only [List.length_append, h0, h1, h2, h3, h4, h5]) (by omega) d
 · intro i hi
   rw [show a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 =
     (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6) ++ a7 ++ (a8 ++ a9) by simp only [List.append_assoc]]
   exact getD_seg (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6) a7 _ (n0 + n1 + n2 + n3 + n4 + n5 + n6) i (by simp only [List.length_append, h0, h1, h2, h3, h4, h5, h6]) (by omega) d
 · intro i hi
   exact getD_seg (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7) a8 a9 (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7) i
     (by simp only [List.length_append, h0, h1, h2, h3, h4, h5, h6, h7]) (by omega) d
 · intro i hi
   have hpre : (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8).length =
       n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 := by
     simp only [List.length_append, h0, h1, h2, h3, h4, h5, h6, h7, h8]
   rw [gD_ar (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8) a9 _ (by omega) (by omega) d]
   rw [show n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + i -
     (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8).length = i by omega]
lemma pk_sp {n e s r : ℕ}
   (edges : Fin e → Fin (n + 1) × Fin (n + 1))
   (nr nc : Fin (2 ^ (3 * (e + 1) * s)))
   (cr cc : Fin r → Fin (2 ^ (3 * (e + 1) * s)))
   (off : Fin (3 * (e + 1) * s))
   (bank : Fin (3 * (e + 1)) → Bool)
   (y : Fin (2 ^ (2 * n + 1)))
   (t : Fin (2 ^ (3 * (e + 1) * s + 1)))
   (j : Fin (3 * (e + 1) * s + 1)) :
   let q := 3 * (e + 1)
   let k := q * s
   let m := 2 * n + 1
   let bits := fun (a x : ℕ) => (List.range a).map (fun i => x.testBit i)
   let sched := fun (c : Fin r → Fin (2 ^ k)) => (List.finRange r).flatMap (fun i => bits k (c i).val)
   let G := (List.ofFn edges).flatMap (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val)
   let inp := G ++ bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++
     bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k + 1) t.val ++ bits (k + 1) j.val
   let raw : RIn n e s r → Bool := fun x => inp.getD (rTF n e s r x).val false
   inp.length = 2 * e * (n + 1) + 3 * k + 2 * r * k + q + m + 2 * (k + 1) ∧
   (∀ (ei : Fin e) (b : Fin (n + 1)),
     rEdg raw ei false b = (edges ei).1.val.testBit b.val ∧
     rEdg raw ei true b = (edges ei).2.val.testBit b.val) ∧
   (∀ p, rNr raw p = nr.val.testBit p.val) ∧
   (∀ p, rNc raw p = nc.val.testBit p.val) ∧
   (∀ ri p, rCr raw ri p = (cr ri).val.testBit p.val) ∧
   (∀ ci p, rCc raw ci p = (cc ci).val.testBit p.val) ∧
   (∀ p, rOff raw p = off.val.testBit p.val) ∧
   (∀ i, rBnk raw i = bank i) ∧
   (∀ b, rY raw b = y.val.testBit b.val) ∧
   (∀ b, rT raw b = t.val.testBit b.val) ∧
   (∀ b, rJ raw b = j.val.testBit b.val) := by
 dsimp only
 let q := 3 * (e + 1)
 let k := q * s
 let m := 2 * n + 1
 let bits := fun (a x : ℕ) => (List.range a).map (fun i => x.testBit i)
 let sched := fun (c : Fin r → Fin (2 ^ k)) => (List.finRange r).flatMap (fun i => bits k (c i).val)
 let G := (List.ofFn edges).flatMap (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val)
 have hbits_len : ∀ a x, (bits a x).length = a := fun a x => by simp [bits]
 have hG_info := gD_fm (List.ofFn edges)
   (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val) (2 * (n + 1))
   (fun z _ => by simp [bits]; omega)
 have hG_len : G.length = 2 * e * (n + 1) := by
   have h := hG_info.1; rw [List.length_ofFn] at h
   calc G.length = e * (2 * (n + 1)) := h
     _ = 2 * e * (n + 1) := by ring
 have hcr_info := gD_fm (List.finRange r) (fun i => bits k (cr i).val) k (fun _ _ => hbits_len k _)
 have hcc_info := gD_fm (List.finRange r) (fun i => bits k (cc i).val) k (fun _ _ => hbits_len k _)
 have hcr_len : (sched cr).length = r * k := by simpa [sched] using hcr_info.1
 have hcc_len : (sched cc).length = r * k := by simpa [sched] using hcc_info.1
 have hbank_len : (List.ofFn bank).length = q := List.length_ofFn
 obtain ⟨hlen, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ :=
   gD_c10 G (bits k nr.val) (bits k nc.val) (sched cr) (sched cc)
     (bits k off.val) (List.ofFn bank) (bits m y.val) (bits (k + 1) t.val) (bits (k + 1) j.val) false
     hG_len (hbits_len k nr.val) (hbits_len k nc.val) hcr_len hcc_len
     (hbits_len k off.val) hbank_len (hbits_len m y.val) (hbits_len (k + 1) t.val) (hbits_len (k + 1) j.val)
 refine ⟨by rw [hlen]; ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro ei b
   have hmul : ei.val * (2 * (n + 1)) + 2 * (n + 1) ≤ 2 * e * (n + 1) := by
     calc _ = (ei.val + 1) * (2 * (n + 1)) := by ring
       _ ≤ e * (2 * (n + 1)) := Nat.mul_le_mul_right _ ei.isLt
       _ = 2 * e * (n + 1) := by ring
   have hb := b.isLt
   constructor
   · simp only [rEdg, rTF, Bool.false_eq_true, ↓reduceIte, add_zero]
     rw [hg0 _ (by omega)]
     have hg := hG_info.2 ei.val (by simp [ei.isLt]) b.val (by omega) false
     simp only [List.getElem_ofFn] at hg
     rw [hg, gD_al _ _ b.val (by rw [hbits_len]; exact hb) false]
     exact gD_bl (n + 1) (edges ei).1.val b.val hb
   · simp only [rEdg, rTF, ↓reduceIte]
     rw [hg0 _ (by omega), show ei.val * (2 * (n + 1)) + (n + 1) + b.val = ei.val * (2 * (n + 1)) + ((n + 1) + b.val) by omega]
     have hg := hG_info.2 ei.val (by simp [ei.isLt]) ((n + 1) + b.val) (by omega) false
     simp only [List.getElem_ofFn] at hg
     rw [hg, gD_ar _ _ ((n + 1) + b.val) (by simp only [hbits_len]; omega) (by simp only [hbits_len]; omega) false]
     rw [show (n + 1) + b.val - (bits (n + 1) (edges ei).1.val).length = b.val by rw [hbits_len]; omega]
     exact gD_bl (n + 1) (edges ei).2.val b.val hb
 · intro p; dsimp only [rNr, rTF]; rw [hg1 p.val p.isLt]; exact gD_bl k nr.val p.val p.isLt
 · intro p; dsimp only [rNc, rTF]; rw [hg2 p.val p.isLt]; exact gD_bl k nc.val p.val p.isLt
 · intro ri p; dsimp only [rCr, rTF]
   have hp : p.val < k := p.isLt
   have hmul : ri.val * k + k ≤ r * k := by
     calc _ = (ri.val + 1) * k := by ring
       _ ≤ r * k := Nat.mul_le_mul_right k ri.isLt
   rw [show 2 * e * (n + 1) + 2 * k + ri.val * k + p.val = 2 * e * (n + 1) + k + k + (ri.val * k + p.val) by omega]
   rw [hg3 (ri.val * k + p.val) (by omega)]
   have hg := hcr_info.2 ri.val (by simp [ri.isLt]) p.val hp false
   simp only [List.getElem_finRange] at hg
   rw [hg]; exact gD_bl k (cr ri).val p.val hp
 · intro ci p; dsimp only [rCc, rTF]
   have hp : p.val < k := p.isLt
   have hmul : ci.val * k + k ≤ r * k := by
     calc _ = (ci.val + 1) * k := by ring
       _ ≤ r * k := Nat.mul_le_mul_right k ci.isLt
   rw [show 2 * e * (n + 1) + 2 * k + r * k + ci.val * k + p.val =
     2 * e * (n + 1) + k + k + r * k + (ci.val * k + p.val) by omega]
   rw [hg4 (ci.val * k + p.val) (by omega)]
   have hg := hcc_info.2 ci.val (by simp [ci.isLt]) p.val hp false
   simp only [List.getElem_finRange] at hg
   rw [hg]; exact gD_bl k (cc ci).val p.val hp
 · intro p; dsimp only [rOff, rTF]
   rw [show 2 * e * (n + 1) + 2 * k + 2 * r * k + p.val = 2 * e * (n + 1) + k + k + r * k + r * k + p.val by ring]
   rw [hg5 p.val p.isLt]; exact gD_bl k off.val p.val p.isLt
 · intro i; dsimp only [rBnk, rTF]
   rw [show 2 * e * (n + 1) + 3 * k + 2 * r * k + i.val = 2 * e * (n + 1) + k + k + r * k + r * k + k + i.val by ring]
   rw [hg6 i.val i.isLt, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
 · intro b; dsimp only [rY, rTF]
   rw [show 2 * e * (n + 1) + 3 * k + 2 * r * k + q + b.val = 2 * e * (n + 1) + k + k + r * k + r * k + k + q + b.val by ring]
   rw [hg7 b.val b.isLt]; exact gD_bl m y.val b.val b.isLt
 · intro b; dsimp only [rT, rTF]
   rw [show 2 * e * (n + 1) + 3 * k + 2 * r * k + q + m + b.val = 2 * e * (n + 1) + k + k + r * k + r * k + k + q + m + b.val by ring]
   rw [hg8 b.val b.isLt]; exact gD_bl (k + 1) t.val b.val b.isLt
 · intro b; dsimp only [rJ, rTF]
   rw [show 2 * e * (n + 1) + 3 * k + 2 * r * k + q + m + (k + 1) + b.val =
     2 * e * (n + 1) + k + k + r * k + r * k + k + q + m + (k + 1) + b.val by ring]
   rw [hg9 b.val b.isLt]; exact gD_bl (k + 1) j.val b.val b.isLt
lemma fs_bnd (n e s d r a N : ℕ) (hs : 0 < s) (han : a ≤ n)
   (hN : 3 * (e + 1) * s + r + (2 * n + 1) + 5 ≤ N) :
   let m := 2 * n + 1
   let q := 3 * (e + 1)
   let k := q * s
   let D := 1 + 2 * a
   let L := d + 1 - s
   let frontCost :=
     q * m * (20 * n + 50) +
     k * (8 * k + 10) +
     (20 * q + 20) +
     100 * (q + 1) * (m + 1) * (q + m + 3) +
     q * (50 * (q + 1) * (m + 1) * (q + m + 3)) +
     (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3))) +
     (4 * q + 30) +
     q * 2 ^ L * 2 ^ s * (100 * (k + 1) * (k + r + 2))
   let dpCost :=
     2 * k * (3 * k + 5) +
     2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
     (2 + 2 ^ L * (20 * (k + 2)))
   frontCost + (k + 1) * (dpCost + 40 * (k + 2)) + 20 * (k + 2) * (k + 2) ≤
     2 ^ 56 * N ^ 24 * 2 ^ (s + 2 * L + D) := by
 dsimp only
 set m := 2 * n + 1
 set q := 3 * (e + 1)
 set k := q * s
 set D := 1 + 2 * a
 set L := d + 1 - s
 have hqk : q ≤ k := Nat.le_mul_of_pos_right q hs
 have hsk : s ≤ k := Nat.le_mul_of_pos_left s (by dsimp [q]; omega)
 have hDm : D ≤ m := by dsimp [D, m]; omega
 have hN1 : 1 ≤ N := by omega
 have hqN : q ≤ N := by omega
 have hkN : k ≤ N := by omega
 have hmN : m ≤ N := by omega
 have hrN : r ≤ N := by omega
 have hDN : D ≤ N := by omega
 have hq1N : q + 1 ≤ N := by omega
 have hk1N : k + 1 ≤ N := by omega
 have hk2N : k + 2 ≤ N := by omega
 have hm1N : m + 1 ≤ N := by omega
 have hD1N : D + 1 ≤ N := by omega
 have hqm3 : q + m + 3 ≤ 2 * N := by omega
 have hmD3 : m + D + 3 ≤ 2 * N := by omega
 have hkr2 : k + r + 2 ≤ 2 * N := by omega
 have hks3 : k + s + 3 ≤ 2 * N := by omega
 have h16n : 20 * n + 50 ≤ 20 * N := by dsimp [m] at hmN; omega
 have hpow_eq : 2 ^ (s + 2 * L + D) = 2 ^ L * 2 ^ L * 2 ^ D * 2 ^ s := by
   rw [show s + 2 * L + D = L + L + D + s by omega, pow_add, pow_add, pow_add]
 have hP1 : 1 ≤ 2 ^ (s + 2 * L + D) := Nat.one_le_two_pow
 have hPL : 2 ^ L ≤ 2 ^ (s + 2 * L + D) := Nat.pow_le_pow_right (by omega) (by omega)
 have hPLs : 2 ^ L * 2 ^ s ≤ 2 ^ (s + 2 * L + D) := by
   rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
 have hN14 : N ≤ N ^ 4 := by
   calc N = N ^ 1 := (pow_one N).symm
     _ ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
 have hN23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN1 (by omega)
 have hN24 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
 have hN34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
 have hf1 : q * m * (20 * n + 50) ≤ 20 * N ^ 4 := by
   calc q * m * (20 * n + 50) ≤ (N * N) * (20 * N) := Nat.mul_le_mul (Nat.mul_le_mul hqN hmN) h16n
     _ = 20 * N ^ 3 := by ring
     _ ≤ 20 * N ^ 4 := Nat.mul_le_mul_left 20 hN34
 have hf2 : k * (8 * k + 10) ≤ 18 * N ^ 4 := by
   calc k * (8 * k + 10) ≤ N * (18 * N) := Nat.mul_le_mul hkN (by omega)
     _ = 18 * N ^ 2 := by ring
     _ ≤ 18 * N ^ 4 := Nat.mul_le_mul_left 18 hN24
 have hf3 : (20 * q + 20) + (4 * q + 30) + 2 ≤ 60 * N ^ 4 := by omega
 have hf4 : 100 * (q + 1) * (m + 1) * (q + m + 3) ≤ 200 * N ^ 4 := by
   calc 100 * (q + 1) * (m + 1) * (q + m + 3)
       = 100 * (((q + 1) * (m + 1)) * (q + m + 3)) := by ring
     _ ≤ 100 * ((N * N) * (2 * N)) := Nat.mul_le_mul_left 100 (Nat.mul_le_mul (Nat.mul_le_mul hq1N hm1N) hqm3)
     _ = 200 * N ^ 3 := by ring
     _ ≤ 200 * N ^ 4 := Nat.mul_le_mul_left 200 hN34
 have hf5 : q * (50 * (q + 1) * (m + 1) * (q + m + 3)) ≤ 100 * N ^ 4 := by
   calc q * (50 * (q + 1) * (m + 1) * (q + m + 3))
       = 50 * (q * (((q + 1) * (m + 1)) * (q + m + 3))) := by ring
     _ ≤ 50 * (N * ((N * N) * (2 * N))) :=
         Nat.mul_le_mul_left 50 (Nat.mul_le_mul hqN (Nat.mul_le_mul (Nat.mul_le_mul hq1N hm1N) hqm3))
     _ = 100 * N ^ 4 := by ring
 have hf6 : q * (600 * (D + 1) * (m + 1) * (m + D + 3)) ≤ 1200 * N ^ 4 := by
   calc q * (600 * (D + 1) * (m + 1) * (m + D + 3))
       = 600 * (q * (((D + 1) * (m + 1)) * (m + D + 3))) := by ring
     _ ≤ 600 * (N * ((N * N) * (2 * N))) :=
         Nat.mul_le_mul_left 600 (Nat.mul_le_mul hqN (Nat.mul_le_mul (Nat.mul_le_mul hD1N hm1N) hmD3))
     _ = 1200 * N ^ 4 := by ring
 have hf7 : q * 2 ^ L * 2 ^ s * (100 * (k + 1) * (k + r + 2)) ≤ 200 * N ^ 4 * 2 ^ (s + 2 * L + D) := by
   have hd : 100 * (q * (k + 1) * (k + r + 2)) ≤ 200 * N ^ 4 := by
     calc 100 * (q * (k + 1) * (k + r + 2))
         ≤ 100 * ((N * N) * (2 * N)) := Nat.mul_le_mul_left 100 (Nat.mul_le_mul (Nat.mul_le_mul hqN hk1N) hkr2)
       _ = 200 * N ^ 3 := by ring
       _ ≤ 200 * N ^ 4 := Nat.mul_le_mul_left 200 hN34
   calc q * 2 ^ L * 2 ^ s * (100 * (k + 1) * (k + r + 2))
       = (100 * (q * (k + 1) * (k + r + 2))) * (2 ^ L * 2 ^ s) := by ring
     _ ≤ (200 * N ^ 4) * 2 ^ (s + 2 * L + D) := Nat.mul_le_mul hd hPLs
 have hfront_le :
     (q * m * (20 * n + 50) + k * (8 * k + 10) + (20 * q + 20) +
       100 * (q + 1) * (m + 1) * (q + m + 3) + q * (50 * (q + 1) * (m + 1) * (q + m + 3)) +
       (2 + q * (600 * (D + 1) * (m + 1) * (m + D + 3))) + (4 * q + 30) +
       q * 2 ^ L * 2 ^ s * (100 * (k + 1) * (k + r + 2))) ≤
     2000 * N ^ 4 * 2 ^ (s + 2 * L + D) := by
   have hmul1 : 1800 * N ^ 4 ≤ 1800 * N ^ 4 * 2 ^ (s + 2 * L + D) := Nat.le_mul_of_pos_right _ hP1
   linarith only [hf1, hf2, hf3, hf4, hf5, hf6, hf7, hmul1]
 have hd1 : 2 * k * (3 * k + 5) ≤ 16 * N ^ 4 := by
   calc 2 * k * (3 * k + 5) = 2 * (k * (3 * k + 5)) := by ring
     _ ≤ 2 * (N * (8 * N)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hkN (by omega))
     _ = 16 * N ^ 2 := by ring
     _ ≤ 16 * N ^ 4 := Nat.mul_le_mul_left 16 hN24
 have hd2 : 2 ^ L * 2 + 2 + 2 ^ L * (20 * (k + 2)) ≤ 24 * N ^ 4 * 2 ^ (s + 2 * L + D) := by
   have ha : 2 + 20 * (k + 2) ≤ 22 * N ^ 4 := by omega
   have hb := Nat.mul_le_mul ha hPL
   have h1 : 1 ≤ N ^ 4 * 2 ^ (s + 2 * L + D) := Nat.mul_pos (Nat.pow_pos hN1) hP1
   calc 2 ^ L * 2 + 2 + 2 ^ L * (20 * (k + 2))
       = (2 + 20 * (k + 2)) * 2 ^ L + 2 := by ring
     _ ≤ 22 * N ^ 4 * 2 ^ (s + 2 * L + D) + 2 := Nat.add_le_add_right hb 2
     _ = 22 * (N ^ 4 * 2 ^ (s + 2 * L + D)) + 2 := by ring
     _ ≤ 24 * (N ^ 4 * 2 ^ (s + 2 * L + D)) := by omega
     _ = 24 * N ^ 4 * 2 ^ (s + 2 * L + D) := by ring
 have hd3 : 2 ^ L * (q * (2 ^ L * 2 ^ D * 2 ^ s *
       (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) ≤
     600 * N ^ 4 * 2 ^ (s + 2 * L + D) := by
   have hc : 200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1) ≤ 600 * N ^ 3 := by
     have h1 : 200 * (D + 1) * (D + 1) * (k + s + 3) ≤ 400 * N ^ 3 := by
       calc 200 * (D + 1) * (D + 1) * (k + s + 3)
           = 200 * (((D + 1) * (D + 1)) * (k + s + 3)) := by ring
         _ ≤ 200 * ((N * N) * (2 * N)) := Nat.mul_le_mul_left 200 (Nat.mul_le_mul (Nat.mul_le_mul hD1N hD1N) hks3)
         _ = 400 * N ^ 3 := by ring
     have h2 : 120 * (D + 1) * (D + 1) ≤ 120 * N ^ 3 := by
       calc 120 * (D + 1) * (D + 1) = 120 * ((D + 1) * (D + 1)) := by ring
         _ ≤ 120 * (N * N) := Nat.mul_le_mul_left 120 (Nat.mul_le_mul hD1N hD1N)
         _ = 120 * N ^ 2 := by ring
         _ ≤ 120 * N ^ 3 := Nat.mul_le_mul_left 120 hN23
     omega
   have he : q * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)) ≤ 600 * N ^ 4 := by
     calc _ ≤ N * (600 * N ^ 3) := Nat.mul_le_mul hqN hc
       _ = 600 * N ^ 4 := by ring
   calc 2 ^ L * (q * (2 ^ L * 2 ^ D * 2 ^ s *
         (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1))))
       = (q * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1))) *
           (2 ^ L * 2 ^ L * 2 ^ D * 2 ^ s) := by ring
     _ = (q * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1))) * 2 ^ (s + 2 * L + D) := by rw [hpow_eq]
     _ ≤ 600 * N ^ 4 * 2 ^ (s + 2 * L + D) := Nat.mul_le_mul_right _ he
 have hdp_le :
     (2 * k * (3 * k + 5) +
       2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
       (2 + 2 ^ L * (20 * (k + 2)))) + 40 * (k + 2) ≤
     700 * N ^ 4 * 2 ^ (s + 2 * L + D) := by
   have hmul1 : 16 * N ^ 4 ≤ 16 * N ^ 4 * 2 ^ (s + 2 * L + D) := Nat.le_mul_of_pos_right _ hP1
   have h40 : 40 * (k + 2) ≤ 40 * N ^ 4 * 2 ^ (s + 2 * L + D) :=
     le_trans (by omega : 40 * (k + 2) ≤ 40 * N ^ 4) (Nat.le_mul_of_pos_right _ hP1)
   have hsplit : 2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s *
         (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) =
       2 ^ L * 2 + 2 ^ L * (q * (2 ^ L * 2 ^ D * 2 ^ s *
         (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) := by ring
   linarith only [hd1, hd2, hd3, hmul1, h40, hsplit]
 have hloop_le :
     (k + 1) * ((2 * k * (3 * k + 5) +
       2 ^ L * (2 + q * (2 ^ L * 2 ^ D * 2 ^ s * (200 * (D + 1) * (D + 1) * (k + s + 3) + 120 * (D + 1) * (D + 1)))) +
       (2 + 2 ^ L * (20 * (k + 2)))) + 40 * (k + 2)) ≤
     700 * N ^ 5 * 2 ^ (s + 2 * L + D) := by
   calc _ ≤ N * (700 * N ^ 4 * 2 ^ (s + 2 * L + D)) := Nat.mul_le_mul hk1N hdp_le
     _ = 700 * N ^ 5 * 2 ^ (s + 2 * L + D) := by ring
 have htail_le : 20 * (k + 2) * (k + 2) ≤ 20 * N ^ 5 * 2 ^ (s + 2 * L + D) := by
   have hc : 20 * (k + 2) * (k + 2) ≤ 20 * N ^ 5 := by
     calc 20 * (k + 2) * (k + 2) = 20 * ((k + 2) * (k + 2)) := by ring
       _ ≤ 20 * (N * N) := Nat.mul_le_mul_left 20 (Nat.mul_le_mul hk2N hk2N)
       _ = 20 * N ^ 2 := by ring
       _ ≤ 20 * N ^ 5 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_right hN1 (by omega))
   exact le_trans hc (Nat.le_mul_of_pos_right _ hP1)
 have h45 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN1 (by omega)
 have h524 : N ^ 5 ≤ N ^ 24 := Nat.pow_le_pow_right hN1 (by omega)
 have hfront5 : 2000 * N ^ 4 * 2 ^ (s + 2 * L + D) ≤ 2000 * N ^ 5 * 2 ^ (s + 2 * L + D) :=
   Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2000 h45)
 have hsum5 : 2720 * N ^ 5 * 2 ^ (s + 2 * L + D) ≤ 2 ^ 56 * N ^ 24 * 2 ^ (s + 2 * L + D) :=
   Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) h524)
 linarith only [hfront_le, hfront5, hloop_le, htail_le, hsum5]
lemma L_meta_33651_core (n e s d r a : Nat) (hs : 0 < s) (hr : 4 ≤ r)
   (h2s : 2 * s ≤ d) (hd3s : d < 3 * s) (han : a ≤ n) :
   let V := Fin (n + 1)
   let m := 2 * n + 1
   let q := 3 * (e + 1)
   let k := q * s
   let W := Fin (2 ^ k)
   let Y := Fin (2 ^ m)
   let comps := fun (E : List (V × V)) => Nat.card (Quot (fun u v : V => (u, v) ∈ E))
   let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
   let sched := fun (c : Fin r → Fin (2 ^ k)) =>
     (List.finRange r).flatMap (fun j => bits k (c j).val)
   ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
     PEqualNP.MetaComplexity.FanInTwo C ∧
     PEqualNP.MetaComplexity.NestedCover.ReadsBack
       (2 * e * (n + 1) + 3 * k + 2 * r * k + q + m + 2 * (k + 1)) C ∧
     C.size ≤ 2 ^ 56 * (k + r + m + 5) ^ 24 * 2 ^ (s + 2 * (d + 1 - s) + 1 + 2 * a) ∧
     ∀ (edges : Fin e → V × V),
       let E := List.ofFn edges
       let width := (Finset.range (e + 1)).sup (fun h =>
         n + 1 + comps E - (comps (E.take h) + comps (E.drop h)))
       let P : List Nat := makeP E
       ∀ (nr nc : W) (cr cc : Fin r → W) (off : Fin k) (bank : Fin q → Bool)
         (y : Y) (t : Fin (2 ^ (k + 1))) (j : Fin (k + 1)),
         let valid := width ≤ a ∧ ∀ i, reachN r (bank i) ≤ d
         let hit := fun (w : W) => (List.finRange q).foldl (fun z i =>
           let p := (off.val + i.val * s) % k
           let col := bank i
           let bit := (stateN k r col w.val (if col then nc.val else nr.val)
             (if col then cc else cr)).testBit ((p + delayN r col) % k)
           if bit then z ^^^ (P[i.val]?.getD 0) else z) (0 : Nat) = y.val
         let G := E.flatMap (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val)
         C.eval (G ++ bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++
           bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k + 1) t.val ++ bits (k + 1) j.val) =
           decide (valid ∧ ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
             (j.val = 0 ∨ w.val.testBit (j.val - 1) = true)) := by
 let m := 2 * n + 1
 let q := 3 * (e + 1)
 let k := q * s
 have hk : 0 < k := by positivity
 have hsL : s ≤ d + 1 - s := by omega
 have hec_raw := ec_uOut n e s d r a hk hsL
 have hec_fin := ec_comp (ec_proj (rTF n e s r)) hec_raw
 rw [zero_add] at hec_fin
 have hbound := fs_bnd n e s d r a (k + r + m + 5) hs han le_rfl
 dsimp only at hbound
 rw [show s + 2 * (d + 1 - s) + (1 + 2 * a) = s + 2 * (d + 1 - s) + 1 + 2 * a by omega] at hbound
 have hec_bnd := ec_le hec_fin hbound
 obtain ⟨C, hF, hB, hS, hE⟩ := ec_to_eval_circuit hec_bnd
 refine ⟨C, hF, hB, hS, ?_⟩
 intro edges
 dsimp only
 intro nr nc cr cc off bank y t j
 let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
 let sched := fun (c : Fin r → Fin (2 ^ k)) => (List.finRange r).flatMap (fun i => bits k (c i).val)
 let G := (List.ofFn edges).flatMap (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val)
 let inp := G ++ bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++
   bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k + 1) t.val ++ bits (k + 1) j.val
 obtain ⟨hlen, hG, hnr, hnc, hcr, hcc, hoff, hbank, hy, ht, hj⟩ :=
   pk_sp edges nr nc cr cc off bank y t j
 rw [hE inp hlen]
 exact uOut_sp hs hr h2s hd3s edges nr nc cr cc off bank y t j
   (fun x => inp.getD (rTF n e s r x).val false)
   hG hnr hnc hcr hcc hoff hbank hy ht hj
end PEqualNP.Outside.L_meta_33651_aux
open PEqualNP.Outside.L_meta_33651_aux in
theorem PEqualNP.Outside.L_meta_33651 :
   ∀ (n e s d r a : Nat), 0 < s → 4 ≤ r → 2 * s ≤ d → d < 3 * s → a ≤ n →
     letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     let V := Fin (n + 1)
     let m := 2 * n + 1
     let q := 3 * (e + 1)
     let k := q * s
     let W := Fin (2 ^ k)
     let Y := Fin (2 ^ m)
     let lo := fun i : V => if i.val = 0 then 0 else (1 : Nat) <<< (2 * i.val - 1)
     let hi := fun i : V => if i.val = 0 then 0 else (1 : Nat) <<< (2 * i.val)
     let comps := fun (E : List (V × V)) => Nat.card (Quot (fun u v : V => (u, v) ∈ E))
     let span := fun (P : List Nat) => Submodule.span (ZMod 2)
       (↑((P.map (fun w (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0)).toFinset) :
         Set (Fin m → ZMod 2))
     let rot := fun (h w : Nat) =>
       ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2 ^ k
     let step := fun (w : Nat) =>
       (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
         (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))).toNat <<< i)) 0
     let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2 ^ k)) =>
       let g := if col then 2 else 1
       (List.finRange r).foldl (fun x j =>
         step (x ^^^ rot g x ^^^ rot (k - g) x) ^^^
           rot (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
         (rot (if col then 3 else 1) w ^^^ name)
     let reach := fun col : Bool => if col then 7 * r - 2 else 5 * r - 3
     let delay := fun col : Bool => if col then 3 * r + 1 else 2 * r - 2
     let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
     let sched := fun (c : Fin r → Fin (2 ^ k)) =>
       (List.finRange r).flatMap (fun j => bits k (c j).val)
     ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
       PEqualNP.MetaComplexity.FanInTwo C ∧
       PEqualNP.MetaComplexity.NestedCover.ReadsBack
         (2 * e * (n + 1) + 3 * k + 2 * r * k + q + m + 2 * (k + 1)) C ∧
       C.size ≤ 2 ^ 56 * (k + r + m + 5) ^ 24 * 2 ^ (s + 2 * (d + 1 - s) + 1 + 2 * a) ∧
       ∀ (edges : Fin e → V × V),
         let E := List.ofFn edges
         let width := (Finset.range (e + 1)).sup (fun h =>
           n + 1 + comps E - (comps (E.take h) + comps (E.drop h)))
         let P : List Nat := [1, 1, 1] ++ E.flatMap
           (fun z => [lo z.1 ^^^ lo z.2, hi z.1 ^^^ hi z.2, 1])
         let peak := (Finset.range (q + 1)).sup (fun h =>
           Module.finrank (ZMod 2) (span (P.take h) ⊓ span (P.drop h) : Submodule (ZMod 2) (Fin m → ZMod 2)))
         peak = 1 + 2 * width ∧
         ∀ (nr nc : W) (cr cc : Fin r → W) (off : Fin k) (bank : Fin q → Bool)
           (y : Y) (t : Fin (2 ^ (k + 1))) (j : Fin (k + 1)),
           let valid := width ≤ a ∧ ∀ i, reach (bank i) ≤ d
           let report := fun (w : W) => (List.finRange q).foldl (fun z i =>
             let p := (off.val + i.val * s) % k
             let col := bank i
             let bit := (state col w.val (if col then nc.val else nr.val)
               (if col then cc else cr)).testBit ((p + delay col) % k)
             if bit then z ^^^ (P[i.val]?.getD 0) else z) (0 : Nat)
           let hit := fun w => report w = y.val
           let G := E.flatMap (fun z => bits (n + 1) z.1.val ++ bits (n + 1) z.2.val)
           C.eval (G ++ bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++
             bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k + 1) t.val ++ bits (k + 1) j.val) =
             decide (valid ∧ ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
               (j.val = 0 ∨ w.val.testBit (j.val - 1) = true)) := by
 intro n e s d r a hs hr h2s hd3s han
 obtain ⟨C, hF, hB, hS, hEval⟩ := L_meta_33651_core n e s d r a hs hr h2s hd3s han
 refine ⟨C, hF, hB, hS, fun edges => ?_⟩
 let k := 3 * (e + 1) * s
 let lo0 : Fin (n + 1) → Nat := fun i => @ite Nat (i.val = 0) (Classical.propDecidable _) 0 ((1 : Nat) <<< (2 * i.val - 1))
 let hi0 : Fin (n + 1) → Nat := fun i => @ite Nat (i.val = 0) (Classical.propDecidable _) 0 ((1 : Nat) <<< (2 * i.val))
 let P0 : List Nat := [1, 1, 1] ++ (List.ofFn edges).flatMap (fun z => [lo0 z.1 ^^^ lo0 z.2, hi0 z.1 ^^^ hi0 z.2, 1])
 have hlo : ∀ i, lo0 i = loVal i := fun i => by unfold lo0 loVal; by_cases h : i.val = 0 <;> simp only [h, ↓reduceIte]
 have hhi : ∀ i, hi0 i = hiVal i := fun i => by unfold hi0 hiVal; by_cases h : i.val = 0 <;> simp only [h, ↓reduceIte]
 have hP_eq : P0 = makeP (List.ofFn edges) := by
   unfold P0 makeP; congr 1; apply List.flatMap_congr; intro z _; rw [hlo z.1, hlo z.2, hhi z.1, hhi z.2]
 refine ⟨?_, ?_⟩
 · dsimp only
   have hpk := peak_eq_one_add_two_width edges
   dsimp only at hpk
   rw [← hpk]
   apply Finset.sup_congr rfl; intro H _
   have hP_def : ([1, 1, 1] ++ (List.ofFn edges).flatMap (fun z =>
       [lo0 z.1 ^^^ lo0 z.2, hi0 z.1 ^^^ hi0 z.2, 1])) = makeP (List.ofFn edges) := hP_eq
   rw [hP_def]
   apply congrArg (fun X : Submodule (ZMod 2) (Fin (2 * n + 1) → ZMod 2) => Module.finrank (ZMod 2) ↥X)
   apply congrArg₂ (· ⊓ ·)
   · apply congrArg (Submodule.span (ZMod 2)); ext v
     simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
     constructor <;> (rintro ⟨w, hw, rfl⟩; refine ⟨w, hw, ?_⟩; funext i; cases w.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte])
   · apply congrArg (Submodule.span (ZMod 2)); ext v
     simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
     constructor <;> (rintro ⟨w, hw, rfl⟩; refine ⟨w, hw, ?_⟩; funext i; cases w.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte])
 · intro nr nc cr cc off bank y t j
   dsimp only
   rw [hEval edges nr nc cr cc off bank y t j]
   simp only [decide_eq_decide]
   let reach0 : Bool → Nat := fun col => @ite Nat (col = true) (Classical.propDecidable _) (7 * r - 2) (5 * r - 3)
   let delay0 : Bool → Nat := fun col => @ite Nat (col = true) (Classical.propDecidable _) (3 * r + 1) (2 * r - 2)
   let state0 : Bool → Nat → Nat → (Fin r → Fin (2 ^ k)) → Nat := fun col w name c =>
     let g := @ite Nat (col = true) (Classical.propDecidable _) 2 1
     (List.finRange r).foldl (fun x j =>
       stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^
         rotN k (@ite Nat (col = true) (Classical.propDecidable _) (3 * (j.val + 1) + 1) (2 * j.val)) w ^^^ (c j).val)
       (rotN k (@ite Nat (col = true) (Classical.propDecidable _) 3 1) w ^^^ name)
   have hreach : ∀ col, reach0 col = reachN r col := fun col => by
     unfold reach0 reachN; cases col <;> simp only [Bool.false_eq_true, ↓reduceIte]
   have hdelay : ∀ col, delay0 col = delayN r col := fun col => by
     unfold delay0 delayN; cases col <;> simp only [Bool.false_eq_true, ↓reduceIte]
   have hstate : ∀ col w name c, state0 col w name c = stateN k r col w name c := fun col w name c => by
     unfold state0 stateN; cases col <;> simp only [Bool.false_eq_true, ↓reduceIte]
   have hhit_eq : ∀ w : Fin (2 ^ k),
       ((List.finRange (3 * (e + 1))).foldl (fun z i =>
         let p := (off.val + i.val * s) % k
         let col := bank i
         let bit := (stateN k r col w.val (if col then nc.val else nr.val) (if col then cc else cr)).testBit ((p + delayN r col) % k)
         if bit then z ^^^ ((makeP (List.ofFn edges))[i.val]?.getD 0) else z) 0 = y.val) ↔
       ((List.finRange (3 * (e + 1))).foldl (fun z i =>
         let p := (off.val + i.val * s) % k
         let col := bank i
         let bit := (state0 col w.val (@ite Nat (col = true) (Classical.propDecidable _) nc.val nr.val)
           (@ite (Fin r → Fin (2 ^ k)) (col = true) (Classical.propDecidable _) cc cr)).testBit ((p + delay0 col) % k)
         @ite Nat (bit = true) (Classical.propDecidable _) (z ^^^ (P0[i.val]?.getD 0)) z) 0 = y.val) := by
     intro w
     suffices hfold : ∀ (ls : List (Fin (3 * (e + 1)))) (acc : Nat),
         ls.foldl (fun z i =>
           let p := (off.val + i.val * s) % k
           let col := bank i
           let bit := (stateN k r col w.val (if col then nc.val else nr.val) (if col then cc else cr)).testBit ((p + delayN r col) % k)
           if bit then z ^^^ ((makeP (List.ofFn edges))[i.val]?.getD 0) else z) acc =
         ls.foldl (fun z i =>
           let p := (off.val + i.val * s) % k
           let col := bank i
           let bit := (state0 col w.val (@ite Nat (col = true) (Classical.propDecidable _) nc.val nr.val)
             (@ite (Fin r → Fin (2 ^ k)) (col = true) (Classical.propDecidable _) cc cr)).testBit ((p + delay0 col) % k)
           @ite Nat (bit = true) (Classical.propDecidable _) (z ^^^ (P0[i.val]?.getD 0)) z) acc by
       rw [hfold (List.finRange (3 * (e + 1))) 0]
     intro ls; induction ls with
     | nil => intro _; rfl
     | cons i tl ih =>
       intro acc; rw [List.foldl_cons, List.foldl_cons]
       have hstep : (let p := (off.val + i.val * s) % k; let col := bank i
           let bit := (stateN k r col w.val (if col then nc.val else nr.val) (if col then cc else cr)).testBit ((p + delayN r col) % k)
           if bit then acc ^^^ ((makeP (List.ofFn edges))[i.val]?.getD 0) else acc) =
           (let p := (off.val + i.val * s) % k; let col := bank i
           let bit := (state0 col w.val (@ite Nat (col = true) (Classical.propDecidable _) nc.val nr.val)
             (@ite (Fin r → Fin (2 ^ k)) (col = true) (Classical.propDecidable _) cc cr)).testBit ((p + delay0 col) % k)
           @ite Nat (bit = true) (Classical.propDecidable _) (acc ^^^ (P0[i.val]?.getD 0)) acc) := by
         dsimp only; rw [hP_eq, hdelay (bank i), hstate (bank i)]
         cases bank i <;> simp only [Bool.false_eq_true, ↓reduceIte]
       rw [hstep]; exact ih _
   refine and_congr (and_congr Iff.rfl (forall_congr' (fun i => by
       change reachN r (bank i) ≤ d ↔ reach0 (bank i) ≤ d; rw [hreach (bank i)])))
     (exists_congr (fun w => and_congr (hhit_eq w) (and_congr ?_ Iff.rfl)))
   apply Iff.of_eq; apply congrArg (· = t.val); apply congrArg Nat.card; apply congrArg Subtype; funext z
   exact propext (and_congr Iff.rfl (hhit_eq z))
