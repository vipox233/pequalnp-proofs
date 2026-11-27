import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27349
open PEqualNP.CircuitLowerBounds

def lab {α : Type} (comb : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [comb g w]) init

theorem lab_length {α : Type} (comb : Gate → List α → α) (gs : List Gate) (init : List α) :
    (lab comb gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [lab]
  | cons g gs ih =>
    have h : lab comb (g :: gs) init = lab comb gs (init ++ [comb g init]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem lab_getD_lt {α : Type} (comb : Gate → List α → α) (d : α) (gs : List Gate)
    (init : List α) (i : ℕ) (hi : i < init.length) :
    (lab comb gs init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    have h : lab comb (g :: gs) init = lab comb gs (init ++ [comb g init]) := rfl
    rw [h, ih _ (by simp only [List.length_append]; omega), List.getD_append _ _ _ _ hi]

theorem lab_split {α : Type} (comb : Gate → List α → α) (gs : List Gate) (init : List α) (j : ℕ) :
    lab comb gs init = lab comb (gs.drop j) (lab comb (gs.take j) init) := by
  unfold lab
  rw [← List.foldl_append, List.take_append_drop]

theorem lab_rec {α : Type} (φ : Gate → List α → α) (d : α) (gs : List Gate) (init : List α)
    (n : ℕ) (hn : init.length = n) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ gs[j].inputs, i < n + j) :
    (lab (fun g W => φ g (g.inputs.map fun i => W.getD i d)) gs init).getD (n + j) d =
      φ gs[j] (gs[j].inputs.map fun i =>
        (lab (fun g W => φ g (g.inputs.map fun i => W.getD i d)) gs init).getD i d) := by
  generalize hcomb : (fun (g : Gate) (W : List α) => φ g (g.inputs.map fun i => W.getD i d)) = comb
  have hlen : (lab comb (gs.take j) init).length = n + j := by
    rw [lab_length, hn, List.length_take]
    omega
  have h1 : (lab comb gs init).getD (n + j) d = comb gs[j] (lab comb (gs.take j) init) := by
    rw [lab_split comb gs init j, List.drop_eq_getElem_cons hj]
    have h : lab comb (gs[j] :: gs.drop (j + 1)) (lab comb (gs.take j) init) =
        lab comb (gs.drop (j + 1))
          (lab comb (gs.take j) init ++ [comb gs[j] (lab comb (gs.take j) init)]) := rfl
    rw [h, lab_getD_lt _ _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]
    simp
  rw [h1, ← hcomb]
  show φ gs[j] _ = φ gs[j] _
  congr 1
  apply List.map_congr_left
  intro i hi
  have e : (lab comb gs init).getD i d = (lab comb (gs.take j) init).getD i d := by
    rw [lab_split comb gs init j]
    exact lab_getD_lt comb d (gs.drop j) _ i (by rw [hlen]; exact hin i hi)
  rw [hcomb]
  exact e.symm

def WB (gs : List Gate) (x : List Bool) : List Bool :=
  lab (fun g W => g.op.eval (g.inputs.map fun i => W.getD i false)) gs x

def WN (gs : List Gate) (x : List ℕ) : List ℕ :=
  lab (fun g W => (g.inputs.map fun i => W.getD i 0).sum) gs x

theorem WB_rec (gs : List Gate) (x : List Bool) (hx : x.length = 11) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ gs[j].inputs, i < 11 + j) :
    (WB gs x).getD (11 + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (WB gs x).getD i false) :=
  lab_rec (fun g l => g.op.eval l) false gs x 11 hx j hj hin

theorem WN_rec (gs : List Gate) (x : List ℕ) (hx : x.length = 11) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ gs[j].inputs, i < 11 + j) :
    (WN gs x).getD (11 + j) 0 = (gs[j].inputs.map fun i => (WN gs x).getD i 0).sum :=
  lab_rec (fun _ l => l.sum) 0 gs x 11 hx j hj hin

theorem WB_bin (gs : List Gate) (x : List Bool) (hx : x.length = 11) (j : ℕ) (hj : j < gs.length)
    (a b : ℕ) (hab : a < b) (hb : b < 11 + j) (hi : gs[j].inputs = [a, b]) :
    (WB gs x).getD (11 + j) false =
      gs[j].op.eval [(WB gs x).getD a false, (WB gs x).getD b false] := by
  have h := WB_rec gs x hx j hj (by
    intro i hi'
    rw [hi] at hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    omega)
  rw [hi] at h
  exact h

theorem WN_bin (gs : List Gate) (x : List ℕ) (hx : x.length = 11) (j : ℕ) (hj : j < gs.length)
    (a b : ℕ) (hab : a < b) (hb : b < 11 + j) (hi : gs[j].inputs = [a, b]) :
    (WN gs x).getD (11 + j) 0 = (WN gs x).getD a 0 + (WN gs x).getD b 0 := by
  have h := WN_rec gs x hx j hj (by
    intro i hi'
    rw [hi] at hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    omega)
  rw [hi] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  exact h

theorem indep (gs : List Gate)
    (hin : ∀ j, ∀ hj : j < gs.length, ∀ m ∈ gs[j].inputs, m < 11 + j)
    (i : ℕ) (hi : ∀ j, ∀ hj : j < gs.length, i ∉ gs[j].inputs)
    (x y : List Bool) (hx : x.length = 11) (hy : y.length = 11)
    (hxy : ∀ m, m < 11 → m ≠ i → x.getD m false = y.getD m false) :
    ∀ k, k < 11 + gs.length → k ≠ i → (WB gs x).getD k false = (WB gs y).getD k false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hki
    by_cases h11 : k < 11
    · unfold WB
      rw [lab_getD_lt _ _ _ _ _ (by omega), lab_getD_lt _ _ _ _ _ (by omega)]
      exact hxy k h11 hki
    · obtain ⟨j, rfl⟩ : ∃ j, k = 11 + j := ⟨k - 11, by omega⟩
      have hj : j < gs.length := by omega
      rw [WB_rec gs x hx j hj (hin j hj), WB_rec gs y hy j hj (hin j hj)]
      congr 1
      apply List.map_congr_left
      intro m hm
      have hm' := hin j hj m hm
      exact ih m hm' (by omega) (fun h => hi j hj (h ▸ hm))

def pm (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Bool) : Bool :=
  (x0 && x4 && x8) || (x0 && x5 && x7) || (x1 && x3 && x8) || (x1 && x5 && x6) ||
    (x2 && x3 && x7) || (x2 && x4 && x6)

theorem sens (gs : List Gate)
    (hin : ∀ j, ∀ hj : j < gs.length, ∀ m ∈ gs[j].inputs, m < 11 + j)
    (hE : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, (WB gs [a0, a1, a2, a3, a4, a5, a6, a7, a8, a0 && a1, a2 || a3]).getD (10 + gs.length) false =
      pm a0 a1 a2 a3 a4 a5 a6 a7 a8)
    (i : ℕ) (hi : i < 10) (a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (hxy : ∀ m, m < 11 → m ≠ i →
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a0 && a1, a2 || a3].getD m false =
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b0 && b1, b2 || b3].getD m false)
    (hne : pm a0 a1 a2 a3 a4 a5 a6 a7 a8 ≠ pm b0 b1 b2 b3 b4 b5 b6 b7 b8) :
    ∃ j, ∃ hj : j < gs.length, i ∈ gs[j].inputs := by
  by_contra h
  have h' : ∀ j, ∀ hj : j < gs.length, i ∉ gs[j].inputs := by
    intro j hj hm
    exact h ⟨j, hj, hm⟩
  have h2 := indep gs hin i h' _ _ rfl rfl hxy (10 + gs.length) (by omega) (by omega)
  rw [hE, hE] at h2
  exact hne h2

theorem flat_len (l : List Gate) (h : ∀ g ∈ l, g.inputs.length ≤ 2) :
    ((l.map Gate.inputs).flatten).length ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h g (by simp)
    have h2 := ih (fun g' hg' => h g' (by simp [hg']))
    omega

theorem len10 (l : List Gate) (h : l.length = 10) :
    ∃ g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : Gate, l = [g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] := by
  obtain _ | ⟨g2, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g3, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g4, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g5, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g6, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g7, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g8, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g9, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g10, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g11, l⟩ := l
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  obtain _ | ⟨g12, l⟩ := l
  · exact ⟨g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, rfl⟩
  · exact absurd h (by simp only [List.length_cons]; omega)

theorem shape (g : Gate) (n : ℕ)
    (h : (g.op = GateOp.not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a, b])) :
    g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a, b]) := by
  rcases h with ⟨_, a, _, he⟩ | h
  · rw [he]
    refine ⟨by simp, fun h2 => ?_⟩
    simp at h2
  · obtain ⟨_, a, b, _, _, he⟩ := id h
    refine ⟨by rw [he]; simp, fun _ => h⟩

theorem gate_step (gs : List Gate)
    (hbin : ∀ j, ∀ hj : j < gs.length, (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j ∧ gs[j].inputs = [a, b])
    (k : ℕ) (h11 : 11 ≤ k) (hk : k < 11 + gs.length) :
    ∃ a b, a < k ∧ b < k ∧
      ((∀ x : List Bool, x.length = 11 →
          (WB gs x).getD k false = ((WB gs x).getD a false && (WB gs x).getD b false)) ∨
        (∀ x : List Bool, x.length = 11 →
          (WB gs x).getD k false = ((WB gs x).getD a false || (WB gs x).getD b false))) ∧
      ∀ x : List ℕ, x.length = 11 →
        (WN gs x).getD k 0 = (WN gs x).getD a 0 + (WN gs x).getD b 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 11 + j := ⟨k - 11, by omega⟩
  have hj : j < gs.length := by omega
  obtain ⟨hop, a, b, hab, hb, he⟩ := hbin j hj
  refine ⟨a, b, by omega, hb, ?_, fun x hx => WN_bin gs x hx j hj a b hab hb he⟩
  rcases hop with hop | hop
  · left
    intro x hx
    rw [WB_bin gs x hx j hj a b hab hb he, hop]
    simp [GateOp.eval]
  · right
    intro x hx
    rw [WB_bin gs x hx j hj a b hab hb he, hop]
    simp [GateOp.eval]

def CL : List ℕ :=
  [0, 4, 32, 36, 64, 68, 96, 100, 128, 132, 160, 164, 192, 196, 224, 228, 8388836, 8421476, 8421604, 8913060, 8913124, 8945892, 8947748, 8947812, 8947876, 8947940, 10485956, 10485988, 10518756, 10526788, 10526820, 10526916, 10526948, 11010276, 11045092, 11051236, 11053156, 11053284, 11141252, 11141284, 11141316, 11141348, 11174116, 11176100, 11176164, 11182276, 11182308, 11184356, 11184644, 11184676, 11184708, 11184740, 11184772, 11184804, 11184836, 11184868, 12583136, 12583140, 12615908, 12632160, 12632164, 12632288, 12632292, 13107428, 13142244, 13156580, 13158500, 13158628, 13369504, 13369508, 13369568, 13369572, 13402340, 13404324, 13404388, 13418720, 13418724, 13420772, 13421600, 13421604, 13421664, 13421668, 13421728, 13421732, 13421792, 13421796, 14680292, 14721252, 14729444, 14737508, 14737636, 15335652, 15379172, 15384804, 15395428, 15395556, 15466724, 15507684, 15518948, 15527012, 15527140, 15597732, 15597796, 15641252, 15641316, 15649956, 15650020, 15655140, 15657700, 15658212, 15658532, 15658596, 15658660, 15658724, 15728832, 15728836, 15728864, 15728868, 15761636, 15769796, 15769828, 15778016, 15778020, 15786212, 15790144, 15790148, 15790176, 15790180, 15790272, 15790276, 15790304, 15790308, 16253156, 16287972, 16314596, 16316516, 16316644, 16384196, 16384228, 16427716, 16427748, 16435428, 16444132, 16445636, 16445668, 16447716, 16448068, 16448100, 16448196, 16448228, 16515296, 16515300, 16558308, 16567520, 16567524, 16575716, 16576736, 16576740, 16578788, 16579680, 16579684, 16579808, 16579812, 16646372, 16689892, 16698596, 16707300, 16707812, 16710372, 16710884, 16711268, 16711396, 16711808, 16711812, 16711840, 16711844, 16711872, 16711876, 16711904, 16711908, 16744676, 16746660, 16746724, 16752836, 16752868, 16754916, 16755332, 16755364, 16755396, 16755428, 16761056, 16761060, 16763108, 16764064, 16764068, 16764128, 16764132, 16769252, 16771812, 16772324, 16772772, 16772836, 16773312, 16773316, 16773344, 16773348, 16775396, 16775876, 16775908, 16776416, 16776420, 16776932, 16776960, 16776964, 16776992, 16776996, 16777024, 16777028, 16777056, 16777060, 16777088, 16777092, 16777120, 16777124, 16777152, 16777156, 16777184, 16777188]

def Q (val : ℕ → ℕ → Bool) (c : ℕ → ℕ → ℕ) (k : ℕ) : Prop :=
  (∀ v, c v k ≤ 1) → ∃ code, CL.contains code = true ∧
    (∀ i, i < 16 → val k i = (code / 256).testBit i) ∧
    ∀ v, (code % 256).testBit v = true → c v k = 1

def chk (f : ℕ → ℕ → ℕ) : Bool :=
  CL.all fun ca => CL.all fun cb =>
    (ca % 256 &&& cb % 256 != 0) ||
      CL.contains (f (ca / 256) (cb / 256) * 256 + (ca % 256 ||| cb % 256))

theorem chk_and : chk (fun a b => a &&& b) = true := by decide +kernel

theorem chk_or : chk (fun a b => a ||| b) = true := by decide +kernel

theorem Qstep (f : ℕ → ℕ → ℕ) (g : Bool → Bool → Bool)
    (hfg : ∀ a b i, (f a b).testBit i = g (a.testBit i) (b.testBit i))
    (hchk : chk f = true) (val : ℕ → ℕ → Bool) (c : ℕ → ℕ → ℕ) (k a b : ℕ)
    (hval : ∀ i, val k i = g (val a i) (val b i))
    (hc : ∀ v, c v k = c v a + c v b)
    (ha : Q val c a) (hb : Q val c b) : Q val c k := by
  intro hk
  obtain ⟨ca, hca, hva, hda⟩ := ha (fun v => by have := hk v; have := hc v; omega)
  obtain ⟨cb, hcb, hvb, hdb⟩ := hb (fun v => by have := hk v; have := hc v; omega)
  have h := hchk
  unfold chk at h
  rw [List.all_eq_true] at h
  have h2 := h ca (by simpa using hca)
  rw [List.all_eq_true] at h2
  have h3 := h2 cb (by simpa using hcb)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · exfalso
    have hne : ca % 256 &&& cb % 256 ≠ 0 := by simpa using h3
    obtain ⟨v, hv⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_and, Bool.and_eq_true] at hv
    have := hda v hv.1
    have := hdb v hv.2
    have := hk v
    have := hc v
    omega
  · have hd : (ca % 256 ||| cb % 256) < 2 ^ 8 :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    refine ⟨_, h3, ?_, ?_⟩
    · intro i hi
      have e : (f (ca / 256) (cb / 256) * 256 + (ca % 256 ||| cb % 256)) / 256 =
          f (ca / 256) (cb / 256) := by
        generalize (ca % 256 ||| cb % 256) = y at hd
        generalize f (ca / 256) (cb / 256) = z
        omega
      rw [e, hfg, hval, hva i hi, hvb i hi]
    · intro v hv
      have e : (f (ca / 256) (cb / 256) * 256 + (ca % 256 ||| cb % 256)) % 256 =
          (ca % 256 ||| cb % 256) := by
        generalize (ca % 256 ||| cb % 256) = y at hd
        generalize f (ca / 256) (cb / 256) = z
        omega
      rw [e, Nat.testBit_or, Bool.or_eq_true] at hv
      have := hk v
      have := hc v
      rcases hv with hv | hv
      · have := hda v hv
        omega
      · have := hdb v hv
        omega

def inp (i : ℕ) : List Bool :=
  [true, false, i.testBit 0, true, true, i.testBit 1, i.testBit 2, i.testBit 3, false, false, true]

def leafC : List ℕ :=
  [16776960, 0, 11184644, 16776960, 16776960, 13421600, 15790144, 16711808, 0, 0, 16776960]

def leafw (v : ℕ) : List ℕ :=
  [if 0 = v then 1 else 0, if 1 = v then 1 else 0, if 2 = v then 1 else 0,
    if 3 = v then 1 else 0, if 4 = v then 1 else 0, if 5 = v then 1 else 0,
    if 6 = v then 1 else 0, if 7 = v then 1 else 0, if 8 = v then 1 else 0,
    if 9 = v then 1 else 0, if 10 = v then 1 else 0]

theorem leaf_ok : ∀ k, k < 11 → CL.contains (leafC.getD k 0) = true ∧
    (∀ i, i < 16 → (inp i).getD k false = (leafC.getD k 0 / 256).testBit i) ∧
    ∀ v, v < 8 → (leafC.getD k 0 % 256).testBit v = true → k = v := by decide +kernel

theorem leafw_sum (v : ℕ) : ((leafw v).map id).sum ≤ 1 := by
  by_cases hv : v < 11
  · interval_cases v <;> decide
  · simp only [leafw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, id]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega

theorem leafw_get (v k : ℕ) (hk : k < 11) : (leafw v).getD k 0 = if k = v then 1 else 0 := by
  interval_cases k <;> rfl

def hB (i : ℕ) : Bool :=
  pm true false (i.testBit 0) true true (i.testBit 1) (i.testBit 2) (i.testBit 3) false

theorem fin_chk :
    CL.all (fun code => (List.range 16).any fun i => (code / 256).testBit i != hB i) = true := by
  decide +kernel

theorem core (rest : List Gate) (hn : rest.length ≤ 10)
    (hF : ∀ j, ∀ hj : j < rest.length,
      (rest[j].op = GateOp.not ∧ ∃ a, a < 11 + j ∧ rest[j].inputs = [a]) ∨
      ((rest[j].op = GateOp.and ∨ rest[j].op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 11 + j ∧ rest[j].inputs = [a, b]))
    (hU : ∀ k, 9 ≤ k → k < 10 + rest.length → ∃ j, ∃ hj : j < rest.length, k ∈ rest[j].inputs)
    (hE : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, (WB rest [a0, a1, a2, a3, a4, a5, a6, a7, a8, a0 && a1, a2 || a3]).getD (10 + rest.length) false =
      pm a0 a1 a2 a3 a4 a5 a6 a7 a8) : False := by
  have hin : ∀ j, ∀ hj : j < rest.length, ∀ m ∈ rest[j].inputs, m < 11 + j := by
    intro j hj m hm
    rcases hF j hj with ⟨_, a, ha, he⟩ | ⟨_, a, b, hab, hb, he⟩
    · rw [he] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    · rw [he] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
  have hread : ∀ k, k < 10 + rest.length → ∃ j, ∃ hj : j < rest.length, k ∈ rest[j].inputs := by
    intro k hk
    by_cases h9 : 9 ≤ k
    · exact hU k h9 hk
    · have hk9 : k < 9 := by omega
      interval_cases k
      · exact sens rest hin hE 0 (by omega) true false false false true false false false true
          false false false false true false false false true (by decide) (by decide)
      · exact sens rest hin hE 1 (by omega) false true false true false false false false true
          false false false true false false false false true (by decide) (by decide)
      · exact sens rest hin hE 2 (by omega) false false true true true false true false false
          false false false true true false true false false (by decide) (by decide)
      · exact sens rest hin hE 3 (by omega) false true true true false false false false true
          false true true false false false false false true (by decide) (by decide)
      · exact sens rest hin hE 4 (by omega) true false false false true false false false true
          true false false false false false false false true (by decide) (by decide)
      · exact sens rest hin hE 5 (by omega) true false false false false true false true false
          true false false false false false false true false (by decide) (by decide)
      · exact sens rest hin hE 6 (by omega) false true false false false true true false false
          false true false false false true false false false (by decide) (by decide)
      · exact sens rest hin hE 7 (by omega) true false false false false true false true false
          true false false false false true false false false (by decide) (by decide)
      · exact sens rest hin hE 8 (by omega) true false false false true false false false true
          true false false false true false false false false (by decide) (by decide)
  have hsub : List.range (10 + rest.length) ⊆ (rest.map Gate.inputs).flatten := by
    intro k hk
    rw [List.mem_range] at hk
    obtain ⟨j, hj, hm⟩ := hread k hk
    rw [List.mem_flatten]
    exact ⟨rest[j].inputs, List.mem_map.mpr ⟨rest[j], List.getElem_mem hj, rfl⟩, hm⟩
  have hsp := (List.nodup_range (n := 10 + rest.length)).subperm hsub
  have hlen : ((rest.map Gate.inputs).flatten).length ≤ 2 * rest.length := by
    apply flat_len
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (shape _ _ (hF j hj)).1
  have h1 := hsp.length_le
  rw [List.length_range] at h1
  have h10 : rest.length = 10 := by omega
  have hperm := hsp.perm_of_length_le (by rw [List.length_range]; omega)
  have hlen20 := hperm.length_eq
  rw [List.length_range] at hlen20
  obtain ⟨g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, rfl⟩ := len10 rest h10
  have s0 := shape g2 11 (hF 0 (by simp))
  have s1 := shape g3 12 (hF 1 (by simp))
  have s2 := shape g4 13 (hF 2 (by simp))
  have s3 := shape g5 14 (hF 3 (by simp))
  have s4 := shape g6 15 (hF 4 (by simp))
  have s5 := shape g7 16 (hF 5 (by simp))
  have s6 := shape g8 17 (hF 6 (by simp))
  have s7 := shape g9 18 (hF 7 (by simp))
  have s8 := shape g10 19 (hF 8 (by simp))
  have s9 := shape g11 20 (hF 9 (by simp))
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.length_append,
    List.length_cons, List.length_nil] at hlen20
  obtain ⟨o0, a0, b0, hab0, hb0, e0⟩ := s0.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o1, a1, b1, hab1, hb1, e1⟩ := s1.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o2, a2, b2, hab2, hb2, e2⟩ := s2.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o3, a3, b3, hab3, hb3, e3⟩ := s3.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o4, a4, b4, hab4, hb4, e4⟩ := s4.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o5, a5, b5, hab5, hb5, e5⟩ := s5.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o6, a6, b6, hab6, hb6, e6⟩ := s6.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o7, a7, b7, hab7, hb7, e7⟩ := s7.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o8, a8, b8, hab8, hb8, e8⟩ := s8.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  obtain ⟨o9, a9, b9, hab9, hb9, e9⟩ := s9.2 (by have := s0.1; have := s1.1; have := s2.1; have := s3.1; have := s4.1; have := s5.1; have := s6.1; have := s7.1; have := s8.1; have := s9.1; omega)
  have hperm' : (List.range 20).Perm [a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8, a9, b9] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9,
      List.cons_append, List.nil_append, List.append_nil] at hperm
    exact hperm
  have hbin : ∀ j, ∀ hj : j < [g2, g3, g4, g5, g6, g7, g8, g9, g10, g11].length,
      ([g2, g3, g4, g5, g6, g7, g8, g9, g10, g11][j].op = GateOp.and ∨ [g2, g3, g4, g5, g6, g7, g8, g9, g10, g11][j].op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j ∧ [g2, g3, g4, g5, g6, g7, g8, g9, g10, g11][j].inputs = [a, b] := by
    intro j hj
    have hj' : j < 10 := hj
    interval_cases j
    · exact ⟨o0, a0, b0, hab0, hb0, e0⟩
    · exact ⟨o1, a1, b1, hab1, hb1, e1⟩
    · exact ⟨o2, a2, b2, hab2, hb2, e2⟩
    · exact ⟨o3, a3, b3, hab3, hb3, e3⟩
    · exact ⟨o4, a4, b4, hab4, hb4, e4⟩
    · exact ⟨o5, a5, b5, hab5, hb5, e5⟩
    · exact ⟨o6, a6, b6, hab6, hb6, e6⟩
    · exact ⟨o7, a7, b7, hab7, hb7, e7⟩
    · exact ⟨o8, a8, b8, hab8, hb8, e8⟩
    · exact ⟨o9, a9, b9, hab9, hb9, e9⟩
  generalize hR : ([g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] : List Gate) = R at hE hbin
  have hRl : R.length = 10 := by rw [← hR]; rfl
  have hval20 : ∀ i, (WB R (inp i)).getD 20 false = hB i := by
    intro i
    have h := hE true false (i.testBit 0) true true (i.testBit 1) (i.testBit 2) (i.testBit 3) false
    rw [Bool.or_true, hRl] at h
    exact h
  have hgate := gate_step R hbin
  rw [hRl] at hgate
  have hQ : ∀ k, k < 21 → Q (fun k i => (WB R (inp i)).getD k false)
      (fun v k => (WN R (leafw v)).getD k 0) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases h11 : k < 11
      · intro _
        obtain ⟨q1, q2, q3⟩ := leaf_ok k h11
        refine ⟨leafC.getD k 0, q1, fun i hi => ?_, fun v hv => ?_⟩
        · show (WB R (inp i)).getD k false = _
          unfold WB
          rw [lab_getD_lt _ _ _ _ _ (show k < (inp i).length from h11)]
          exact q2 i hi
        · show (WN R (leafw v)).getD k 0 = 1
          unfold WN
          rw [lab_getD_lt _ _ _ _ _ (show k < (leafw v).length from h11), leafw_get v k h11]
          have hv8 : v < 8 := by
            by_contra hc
            have h256 : leafC.getD k 0 % 256 < 2 ^ v :=
              lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
                (show 256 ≤ 2 ^ v from le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 8 ≤ v by omega)))
            rw [Nat.testBit_lt_two_pow h256] at hv
            exact Bool.false_ne_true hv
          rw [if_pos (q3 v hv8 hv)]
      · obtain ⟨a, b, ha, hb, hop, hcc⟩ := hgate k (by omega) (by omega)
        rcases hop with hop | hop
        · exact Qstep _ _ (fun a b i => Nat.testBit_and a b i) chk_and _ _ k a b
            (fun i => hop (inp i) rfl) (fun v => hcc (leafw v) rfl)
            (ih a ha (by omega)) (ih b hb (by omega))
        · exact Qstep _ _ (fun a b i => Nat.testBit_or a b i) chk_or _ _ k a b
            (fun i => hop (inp i) rfl) (fun v => hcc (leafw v) rfl)
            (ih a ha (by omega)) (ih b hb (by omega))
  have hsum : ∀ v, (WN R (leafw v)).getD 20 0 ≤ 1 := by
    intro v
    have hp := (hperm'.map (fun k => (WN R (leafw v)).getD k 0)).sum_eq
    rw [show List.range 20 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
      from by decide] at hp
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hp
    have c0 : (WN R (leafw v)).getD 11 0 = (WN R (leafw v)).getD a0 0 + (WN R (leafw v)).getD b0 0 :=
      WN_bin R (leafw v) rfl 0 (by rw [hRl]; norm_num) a0 b0 hab0 hb0 (by subst hR; exact e0)
    have c1 : (WN R (leafw v)).getD 12 0 = (WN R (leafw v)).getD a1 0 + (WN R (leafw v)).getD b1 0 :=
      WN_bin R (leafw v) rfl 1 (by rw [hRl]; norm_num) a1 b1 hab1 hb1 (by subst hR; exact e1)
    have c2 : (WN R (leafw v)).getD 13 0 = (WN R (leafw v)).getD a2 0 + (WN R (leafw v)).getD b2 0 :=
      WN_bin R (leafw v) rfl 2 (by rw [hRl]; norm_num) a2 b2 hab2 hb2 (by subst hR; exact e2)
    have c3 : (WN R (leafw v)).getD 14 0 = (WN R (leafw v)).getD a3 0 + (WN R (leafw v)).getD b3 0 :=
      WN_bin R (leafw v) rfl 3 (by rw [hRl]; norm_num) a3 b3 hab3 hb3 (by subst hR; exact e3)
    have c4 : (WN R (leafw v)).getD 15 0 = (WN R (leafw v)).getD a4 0 + (WN R (leafw v)).getD b4 0 :=
      WN_bin R (leafw v) rfl 4 (by rw [hRl]; norm_num) a4 b4 hab4 hb4 (by subst hR; exact e4)
    have c5 : (WN R (leafw v)).getD 16 0 = (WN R (leafw v)).getD a5 0 + (WN R (leafw v)).getD b5 0 :=
      WN_bin R (leafw v) rfl 5 (by rw [hRl]; norm_num) a5 b5 hab5 hb5 (by subst hR; exact e5)
    have c6 : (WN R (leafw v)).getD 17 0 = (WN R (leafw v)).getD a6 0 + (WN R (leafw v)).getD b6 0 :=
      WN_bin R (leafw v) rfl 6 (by rw [hRl]; norm_num) a6 b6 hab6 hb6 (by subst hR; exact e6)
    have c7 : (WN R (leafw v)).getD 18 0 = (WN R (leafw v)).getD a7 0 + (WN R (leafw v)).getD b7 0 :=
      WN_bin R (leafw v) rfl 7 (by rw [hRl]; norm_num) a7 b7 hab7 hb7 (by subst hR; exact e7)
    have c8 : (WN R (leafw v)).getD 19 0 = (WN R (leafw v)).getD a8 0 + (WN R (leafw v)).getD b8 0 :=
      WN_bin R (leafw v) rfl 8 (by rw [hRl]; norm_num) a8 b8 hab8 hb8 (by subst hR; exact e8)
    have c9 : (WN R (leafw v)).getD 20 0 = (WN R (leafw v)).getD a9 0 + (WN R (leafw v)).getD b9 0 :=
      WN_bin R (leafw v) rfl 9 (by rw [hRl]; norm_num) a9 b9 hab9 hb9 (by subst hR; exact e9)
    have hl := leafw_sum v
    have hg : ∀ k, k < 11 → (WN R (leafw v)).getD k 0 = if k = v then 1 else 0 := by
      intro k hk
      rw [← leafw_get v k hk]
      unfold WN
      exact lab_getD_lt _ _ _ _ _ (show k < (leafw v).length from hk)
    simp only [leafw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, id] at hl
    have g0 := hg 0 (by norm_num)
    have g1 := hg 1 (by norm_num)
    have g2' := hg 2 (by norm_num)
    have g3' := hg 3 (by norm_num)
    have g4' := hg 4 (by norm_num)
    have g5' := hg 5 (by norm_num)
    have g6' := hg 6 (by norm_num)
    have g7' := hg 7 (by norm_num)
    have g8' := hg 8 (by norm_num)
    have g9' := hg 9 (by norm_num)
    have g10' := hg 10 (by norm_num)
    omega
  obtain ⟨code, hcode, hv, _⟩ := hQ 20 (by norm_num) hsum
  have hf := fin_chk
  rw [List.all_eq_true] at hf
  have hf2 := hf code (by simpa using hcode)
  rw [List.any_eq_true] at hf2
  obtain ⟨i, hi, hne⟩ := hf2
  rw [List.mem_range] at hi
  have h1 := hv i hi
  have h2 := hval20 i
  simp only at h1
  rw [h2] at h1
  rw [h1] at hne
  simp at hne

theorem eval_prefix (rest : List Gate) (out : ℕ) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool) :
    Circuit.eval ⟨⟨GateOp.and, [0, 1]⟩ :: ⟨GateOp.or, [2, 3]⟩ :: rest, out⟩ [a0, a1, a2, a3, a4, a5, a6, a7, a8] =
      (WB rest [a0, a1, a2, a3, a4, a5, a6, a7, a8, a0 && a1, a2 || a3]).getD out false := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> rfl

end PEqualNP.Outside.L_meta_27349

theorem PEqualNP.Outside.L_meta_27349 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩)) := by
  rintro ⟨C, -, hsize, heval, hout, hF, -, hU, hh0, hh1⟩
  obtain ⟨gates, out⟩ := C
  rcases gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hh0
  · simp at hh1
  simp only [List.head?_cons, List.tail_cons, Option.some.injEq] at hh0 hh1
  subst hh0 hh1
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons] at hsize hout
  have hout' : out = 10 + rest.length := by omega
  subst hout'
  refine PEqualNP.Outside.L_meta_27349.core rest (by omega) ?_ ?_ ?_
  · intro j hj
    have h := hF ⟨j + 2, by simp only [List.length_cons]; omega⟩
    simp only [List.get_eq_getElem, List.getElem_cons_succ] at h
    rw [show 9 + (j + 2) = 11 + j by omega] at h
    exact h
  · intro k h9 hk
    obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
    obtain ⟨⟨m, hm⟩, hjm, hmem⟩ := hU ⟨j, by simp only [List.length_cons]; omega⟩
      (by simp only [List.length_cons]; omega)
    rcases m with _ | _ | m
    · simp at hjm
    · simp at hmem
      omega
    · simp only [List.length_cons] at hm
      refine ⟨m, by omega, ?_⟩
      simpa using hmem
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8
    have h := heval ![a0, a1, a2, a3, a4, a5, a6, a7, a8]
    rw [← PEqualNP.Outside.L_meta_27349.eval_prefix]
    exact h
