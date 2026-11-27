import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_044

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

private def wires (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

private def val (gs : List Gate) (x : List Bool) (i : Nat) : Bool :=
  (wires gs x).getD i false

private def fits (k : Nat) (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < k

private def good (n : Nat) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), fits (n + j) gs[j]

private theorem good_prefix {n : Nat} {as bs : List Gate}
    (h : as <+: bs) (hg : good n bs) : good n as := by
  obtain ⟨cs, rfl⟩ := h
  intro j hj
  simpa only [List.getElem_append_left hj] using
    hg j (show j < (as ++ cs).length by simp; omega)

private theorem good_add {n : Nat} {gs : List Gate} {g : Gate}
    (h : good n gs) (hg : fits (n + gs.length) g) : good n (gs ++ [g]) := by
  intro j hj
  by_cases hj' : j < gs.length
  · simpa only [List.getElem_append_left hj'] using h j hj'
  · have e : j = gs.length := by
      simp at hj
      omega
    subst j
    simpa using hg

private theorem good_of_circuit {n : Nat} {C : Circuit} (hf : FanInTwo C)
    (hr : ReadsBack n C) : good n C.gates := by
  intro j hj
  have m : C.gates[j] ∈ C.gates := List.mem_iff_getElem.mpr ⟨j, hj, rfl⟩
  have hb := hr j hj
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some] at hb
  exact ⟨(hf _ m).1, (hf _ m).2, hb⟩

private theorem good_to_circuit {n : Nat} {C : Circuit} (h : good n C.gates) :
    FanInTwo C ∧ ReadsBack n C := by
  constructor
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨(h j hj).1, (h j hj).2.1⟩
  · intro j hj
    simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some] using (h j hj).2.2

private theorem wires_add (gs : List Gate) (x : List Bool) (g : Gate) :
    wires (gs ++ [g]) x = wires gs x ++ [g.op.eval (g.inputs.map (val gs x))] := by
  unfold val
  simp [wires, Circuit.wires, List.foldl_append]

private theorem wires_len (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires, Circuit.wires]
  | append_singleton gs g ih => simp [wires_add, ih, Nat.add_assoc]

private theorem wires_append (as bs : List Gate) (x : List Bool) :
    ∃ ys, wires (as ++ bs) x = wires as x ++ ys := by
  induction bs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton bs b ih =>
    obtain ⟨ys, hy⟩ := ih
    rw [← List.append_assoc, wires_add, hy, List.append_assoc]
    exact ⟨_, rfl⟩

private theorem val_prefix {as bs : List Gate} (h : as <+: bs) (x : List Bool)
    (i : Nat) (hi : i < x.length + as.length) : val bs x i = val as x i := by
  obtain ⟨cs, rfl⟩ := h
  obtain ⟨ys, hy⟩ := wires_append as cs x
  simp only [val, hy, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rwa [wires_len])]

private theorem val_add (gs : List Gate) (x : List Bool) (g : Gate) :
    val (gs ++ [g]) x (x.length + gs.length) = g.op.eval (g.inputs.map (val gs x)) := by
  simp only [val, wires_add, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [wires_len])]
  simp [wires_len]

private def rebase (n k i : Nat) : Nat := if i < n then i else i + k

private def copy (n k : Nat) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map (rebase n k)⟩

private theorem rebase_lt {n k j i : Nat} (h : i < n + j) :
    rebase n k i < n + k + j := by
  unfold rebase
  split <;> omega

private theorem copy_good {n : Nat} {as bs : List Gate} (ha : good n as)
    (hb : good n bs) : good n (as ++ copy n as.length bs) := by
  intro j hj
  by_cases h : j < as.length
  · simpa only [List.getElem_append_left h] using ha j h
  · have hk : j - as.length < bs.length := by
      simp [copy] at hj
      omega
    have he : j = as.length + (j - as.length) := by omega
    have hg := hb (j - as.length) hk
    rw [List.getElem_append_right (by omega)]
    simp only [copy, List.getElem_map]
    refine ⟨hg.1, by simpa using hg.2.1, ?_⟩
    intro i hi
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hi
    have hl := rebase_lt (k := as.length) (hg.2.2 a hmem)
    omega

private theorem val_copy {n : Nat} (as bs : List Gate) (hb : good n bs)
    (x : List Bool) (hx : x.length = n) (i : Nat) (hi : i < n + bs.length) :
    val (as ++ copy n as.length bs) x (rebase n as.length i) = val bs x i := by
  induction bs using List.reverseRecOn generalizing i with
  | nil =>
    have hn : i < n := by simpa using hi
    simp only [copy, List.map_nil, List.append_nil, rebase, ite_eq_left hn]
    exact val_prefix (List.prefix_append [] as) x i (by simpa [hx] using hn)
  | append_singleton bs g ih =>
    have hp := good_prefix (List.prefix_append bs [g]) hb
    rw [copy, List.map_append, List.map_singleton, ← List.append_assoc]
    change val ((as ++ copy n as.length bs) ++ [⟨g.op, g.inputs.map (rebase n as.length)⟩])
      x (rebase n as.length i) = val (bs ++ [g]) x i
    by_cases h : i < n + bs.length
    · rw [val_prefix (List.prefix_append _ [_]) x _ (by
          simpa [hx, copy, Nat.add_assoc] using rebase_lt (k := as.length) h),
          val_prefix (List.prefix_append _ [_]) x _ (by simpa [hx] using h)]
      exact ih hp i h
    · have e : i = n + bs.length := by simp at hi; omega
      subst i
      rw [rebase, ite_eq_right (by omega)]
      have he : n + bs.length + as.length = x.length + (as ++ copy n as.length bs).length := by
        simp [hx, copy]; omega
      have hx' : n + bs.length = x.length + bs.length := by omega
      rw [he, val_add, hx', val_add]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro a ha
      apply ih hp
      have hg : fits (n + bs.length) g := by
        simpa using hb bs.length (by simp)
      exact hg.2.2 a ha

private def reach {n : Nat} (m k : Nat)
    (guard : Fin k → Nat → (Fin n → Bool) → Bool)
    (s : Nat) (x : Fin n → Bool) : Prop :=
  ∃ w : Nat, w < 2 ^ k * m ∧ w % m = s ∧
    ∀ i : Fin k, guard i ((w / 2 ^ i.val) % (2 * m)) x = true

private theorem reach_zero {n m s : Nat}
    (guard : Fin 0 → Nat → (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (hs : s < m) : reach m 0 guard s x :=
  ⟨s, by simpa using hs, Nat.mod_eq_of_lt hs, fun i => Fin.elim0 i⟩

private theorem low_window {m v e : Nat} (hm : 0 < m) (he : e < 2) :
    (2 * v + e) % (2 * m) = 2 * (v % m) + e := by
  have h := Nat.mod_lt v hm
  have h' : 2 * v + e = (2 * (v % m) + e) + (2 * m) * (v / m) := by
    calc
      _ = 2 * (v % m + m * (v / m)) + e := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [h', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem shifted_div {v e : Nat} (he : e < 2) (i : Nat) :
    (2 * v + e) / 2 ^ (i + 1) = v / 2 ^ i := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  congr 1
  omega

private theorem reach_split {n m k s : Nat} (hm : 0 < m) (hs : s < m)
    (guard : Fin (k + 1) → Nat → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    reach m (k + 1) guard s x ↔
      (reach m k (fun i => guard i.succ) (s / 2) x ∧ guard 0 s x = true) ∨
      (reach m k (fun i => guard i.succ) ((s + m) / 2) x ∧ guard 0 (s + m) x = true) := by
  have hdvd : m ∣ 2 * m := ⟨2, by omega⟩
  have hpow : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by rw [pow_succ']; ring
  constructor
  · rintro ⟨w, hw, hsm, hall⟩
    let v := w / 2
    let e := w % 2
    let p := w % (2 * m)
    have he : e < 2 := Nat.mod_lt _ (by decide)
    have hwv : w = 2 * v + e := by
      dsimp [v, e]
      have := Nat.mod_add_div w 2
      omega
    have hp : p = 2 * (v % m) + e := by
      change w % (2 * m) = _
      conv_lhs => rw [hwv]
      exact low_window hm he
    have hpm : p % m = s := (Nat.mod_mod_of_dvd w hdvd).trans hsm
    have hplt : p < 2 * m := Nat.mod_lt _ (by omega)
    have hcases : p = s ∨ p = s + m := by
      by_cases hp0 : p < m
      · exact Or.inl ((Nat.mod_eq_of_lt hp0).symm.trans hpm)
      · have hq : p - m < m := by omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hq] at hpm
        exact Or.inr (by omega)
    have htail : reach m k (fun i => guard i.succ) (p / 2) x := by
      refine ⟨v, ?_, by omega, ?_⟩
      · rw [hpow] at hw
        omega
      · intro i
        have hshift : w / 2 ^ (i.val + 1) = v / 2 ^ i.val := by
          conv_lhs => rw [hwv]
          exact shifted_div he _
        simpa only [Fin.val_succ, hshift] using hall i.succ
    have hfirst : guard 0 p x = true := by simpa [p] using hall 0
    rcases hcases with h | h
    · exact Or.inl ⟨h ▸ htail, h ▸ hfirst⟩
    · exact Or.inr ⟨h ▸ htail, h ▸ hfirst⟩
  · have aux : ∀ p < 2 * m, p % m = s →
        reach m k (fun i => guard i.succ) (p / 2) x →
        guard 0 p x = true → reach m (k + 1) guard s x := by
      intro p hp hps htail hfirst
      obtain ⟨v, hv, hvm, hrest⟩ := htail
      let e := p % 2
      let w := 2 * v + e
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hwp : w % (2 * m) = p := by
        change (2 * v + e) % (2 * m) = _
        rw [low_window hm he, hvm]
        have := Nat.mod_add_div p 2
        dsimp [e]
        omega
      refine ⟨w, by rw [hpow]; dsimp [w]; omega, ?_, ?_⟩
      · rw [← Nat.mod_mod_of_dvd w hdvd, hwp, hps]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [hwp] using hfirst
        · simpa only [Fin.val_succ, w, shifted_div he] using hrest j
    rintro (⟨ht, hg⟩ | ⟨ht, hg⟩)
    · exact aux s (by omega) (Nat.mod_eq_of_lt hs) ht hg
    · apply aux (s + m) (by omega) ?_ ht hg
      rw [Nat.mod_eq_sub_mod (by omega)]
      simpa using Nat.mod_eq_of_lt hs

private def wire {n : Nat} (gs : List Gate) (o : Nat) (P : (Fin n → Bool) → Prop) : Prop :=
  o < n + gs.length ∧ ∀ x, val gs (List.ofFn x) o = true ↔ P x

private def bank {n : Nat} (gs : List Gate) (k : Nat)
    (P : Nat → (Fin n → Bool) → Prop) : Prop :=
  ∀ j < k, ∃ o, wire gs o (P j)

private theorem wire_keep {n : Nat} {as bs : List Gate} {o : Nat}
    {P : (Fin n → Bool) → Prop} (h : as <+: bs) (hw : wire as o P) : wire bs o P := by
  refine ⟨by have := h.length_le; have := hw.1; omega, fun x => ?_⟩
  rw [val_prefix h _ _ (by simpa using hw.1)]
  exact hw.2 x

private theorem wire_iff {n : Nat} {gs : List Gate} {o : Nat}
    {P Q : (Fin n → Bool) → Prop} (hw : wire gs o P) (he : ∀ x, P x ↔ Q x) :
    wire gs o Q :=
  ⟨hw.1, fun x => (hw.2 x).trans (he x)⟩

private theorem append_bin {n : Nat} {gs : List Gate} {a b : Nat}
    {P Q : (Fin n → Bool) → Prop} (hg : good n gs) (ha : wire gs a P) (hb : wire gs b Q)
    (both : Bool) :
    ∃ hs, gs <+: hs ∧ good n hs ∧ hs.length = gs.length + 1 ∧
      wire hs (n + gs.length) (fun x => if both then P x ∧ Q x else P x ∨ Q x) := by
  let g : Gate := ⟨if both then .and else .or, [a, b]⟩
  have hfit : fits (n + gs.length) g := by
    refine ⟨?_, by simp [g], ?_⟩
    · cases both <;> simp [g]
    · intro i hi
      simp [g] at hi
      rcases hi with rfl | rfl
      · exact ha.1
      · exact hb.1
  refine ⟨gs ++ [g], List.prefix_append _ _, good_add hg hfit, by simp, by simp, ?_⟩
  intro x
  rw [show n + gs.length = (List.ofFn x).length + gs.length by simp, val_add]
  cases both <;> simp [g, GateOp.eval, ha.2 x, hb.2 x]

private theorem append_guard {n b : Nat} {gs : List Gate}
    {P : (Fin n → Bool) → Bool} (hg : good n gs) (hf : wire (n := n) gs n (fun _ => False))
    (G : Circuit) (hG : good n G.gates) (hsize : G.size ≤ b)
    (hval : ∀ x, G.eval (List.ofFn x) = P x) :
    ∃ hs, gs <+: hs ∧ good n hs ∧ hs.length ≤ gs.length + b ∧
      ∃ o, wire hs o (fun x => P x = true) := by
  let hs := gs ++ copy n gs.length G.gates
  have hp : gs <+: hs := List.prefix_append _ _
  have hlen : hs.length = gs.length + G.gates.length := by simp [hs, copy]
  have hsize' : G.gates.length ≤ b := hsize
  refine ⟨hs, hp, copy_good hg hG, by omega, ?_⟩
  by_cases ho : G.output < n + G.gates.length
  · refine ⟨rebase n gs.length G.output, by
      rw [hlen, ← Nat.add_assoc]
      exact rebase_lt ho, ?_⟩
    intro x
    rw [val_copy gs G.gates hG _ (by simp) _ ho]
    have hv : val G.gates (List.ofFn x) G.output = P x := hval x
    rw [hv]
  · refine ⟨n, wire_iff (wire_keep hp hf) fun x => ?_⟩
    have hout : G.eval (List.ofFn x) = false := by
      change val G.gates (List.ofFn x) G.output = false
      unfold val
      have hlen' : (wires G.gates (List.ofFn x)).length ≤ G.output := by
        rw [wires_len, List.length_ofFn]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen']
      rfl
    simp [← hval x, hout]

private theorem collect {n : Nat} (base : List Gate) (cost k : Nat)
    (P : Nat → (Fin n → Bool) → Prop) (hg : good n base)
    (step : ∀ j < k, ∀ gs, base <+: gs → good n gs →
      ∃ hs, gs <+: hs ∧ good n hs ∧ hs.length ≤ gs.length + cost ∧
        ∃ o, wire hs o (P j)) :
    ∃ hs, base <+: hs ∧ good n hs ∧ hs.length ≤ base.length + k * cost ∧ bank hs k P := by
  induction k with
  | zero => exact ⟨base, ⟨[], by simp⟩, hg, by simp, fun j hj => by omega⟩
  | succ k ih =>
    obtain ⟨gs, hp, hgs, hlen, hb⟩ := ih (fun j hj => step j (by omega))
    obtain ⟨hs, hq, hhs, hlen', o, ho⟩ := step k (by omega) gs hp hgs
    refine ⟨hs, hp.trans hq, hhs, by rw [Nat.succ_mul]; omega, ?_⟩
    intro j hj
    by_cases hj' : j < k
    · obtain ⟨w, hw⟩ := hb j hj'
      exact ⟨w, wire_keep hq hw⟩
    · have e : j = k := by omega
      subst j
      exact ⟨o, ho⟩

private theorem layer {n m k b : Nat} (hm : 0 < m)
    {guard : Fin (k + 1) → Nat → (Fin n → Bool) → Bool}
    (hguard : ∀ (i : Fin (k + 1)) (p : Nat), p < 2 * m →
      ∃ G : Circuit, FanInTwo G ∧ ReadsBack n G ∧ G.size ≤ b ∧
        ∀ x : Fin n → Bool, G.eval (List.ofFn x) = guard i p x)
    (base : List Gate) (hg : good n base) (hf : wire (n := n) base n (fun _ => False))
    (hb : bank base m (fun s => reach m k (fun i => guard i.succ) s)) :
    ∃ hs, base <+: hs ∧ good n hs ∧ hs.length ≤ base.length + m * (2 * b + 3) ∧
      bank hs m (fun s => reach m (k + 1) guard s) := by
  apply collect base (2 * b + 3) m _ hg
  intro s hs gs hp hgs
  obtain ⟨u, hu⟩ := hb (s / 2) (by omega)
  obtain ⟨v, hv⟩ := hb ((s + m) / 2) (by omega)
  obtain ⟨G, hGf, hGr, hGsize, hGval⟩ := hguard 0 s (by omega)
  obtain ⟨H, hHf, hHr, hHsize, hHval⟩ := hguard 0 (s + m) (by omega)
  obtain ⟨gs1, hp1, hg1, hlen1, a, ha⟩ :=
    append_guard hgs (wire_keep hp hf) G (good_of_circuit hGf hGr) hGsize hGval
  obtain ⟨gs2, hp2, hg2, hlen2, c, hc⟩ :=
    append_guard hg1 (wire_keep (hp.trans hp1) hf) H (good_of_circuit hHf hHr) hHsize hHval
  have hu2 := wire_keep (hp.trans (hp1.trans hp2)) hu
  have hv2 := wire_keep (hp.trans (hp1.trans hp2)) hv
  obtain ⟨gs3, hp3, hg3, hlen3, h3⟩ := append_bin hg2 hu2 (wire_keep hp2 ha) true
  obtain ⟨gs4, hp4, hg4, hlen4, h4⟩ :=
    append_bin hg3 (wire_keep hp3 hv2) (wire_keep hp3 hc) true
  obtain ⟨gs5, hp5, hg5, hlen5, h5⟩ := append_bin hg4 (wire_keep hp4 h3) h4 false
  refine ⟨gs5, hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5))), hg5, by omega,
    n + gs4.length, wire_iff h5 ?_⟩
  intro x
  simpa only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] using (reach_split hm hs guard x).symm

private theorem layers {n m b : Nat} (hm : 0 < m) (k : Nat)
    (guard : Fin k → Nat → (Fin n → Bool) → Bool)
    (hguard : ∀ (i : Fin k) (p : Nat), p < 2 * m →
      ∃ G : Circuit, FanInTwo G ∧ ReadsBack n G ∧ G.size ≤ b ∧
        ∀ x : Fin n → Bool, G.eval (List.ofFn x) = guard i p x)
    (base : List Gate) (hg : good n base)
    (hf : wire (n := n) base n (fun _ => False))
    (ht : wire (n := n) base (n + 1) (fun _ => True)) :
    ∃ gs, base <+: gs ∧ good n gs ∧ gs.length ≤ base.length + k * (m * (2 * b + 3)) ∧
      bank gs m (fun s => reach m k guard s) := by
  induction k with
  | zero =>
    refine ⟨base, ⟨[], by simp⟩, hg, by simp, ?_⟩
    intro s hs
    exact ⟨n + 1, wire_iff ht (fun x => iff_true_intro (reach_zero guard x hs) |>.symm)⟩
  | succ k ih =>
    obtain ⟨gs, hp, hgs, hlen, hb⟩ :=
      ih (fun i => guard i.succ) (fun i p h => hguard i.succ p h)
    obtain ⟨hs, hp', hhs, hlen', hb'⟩ :=
      layer hm hguard gs hgs (wire_keep hp hf) hb
    refine ⟨hs, hp.trans hp', hhs, by rw [Nat.succ_mul]; omega, hb'⟩

private theorem finish {n : Nat} (base : List Gate) (k : Nat)
    (P : Nat → (Fin n → Bool) → Prop) (hg : good n base)
    (hf : wire (n := n) base n (fun _ => False)) (hb : bank base k P) :
    ∃ gs o, base <+: gs ∧ good n gs ∧ gs.length ≤ base.length + k ∧
      wire gs o (fun x => ∃ s < k, P s x) := by
  induction k with
  | zero =>
    exact ⟨base, n, ⟨[], by simp⟩, hg, by simp, wire_iff hf (fun x => by simp)⟩
  | succ k ih =>
    obtain ⟨gs, o, hp, hgs, hlen, ho⟩ := ih (fun j hj => hb j (by omega))
    obtain ⟨w, hw⟩ := hb k (by omega)
    obtain ⟨hs, hp', hhs, hlen', h⟩ := append_bin hgs ho (wire_keep hp hw) false
    refine ⟨hs, n + gs.length, hp.trans hp', hhs, by omega, wire_iff h ?_⟩
    intro x
    change ((∃ s < k, P s x) ∨ P k x) ↔ ∃ s < k + 1, P s x
    constructor
    · rintro (⟨s, hs, hxs⟩ | hx)
      · exact ⟨s, by omega, hxs⟩
      · exact ⟨k, by omega, hx⟩
    · rintro ⟨s, hs, hx⟩
      by_cases hlt : s < k
      · exact Or.inl ⟨s, hlt, hx⟩
      · have e : s = k := by omega
        exact Or.inr (e ▸ hx)

private theorem constants (n : Nat) :
    ∃ base : List Gate, base.length = 2 ∧ good n base ∧
      wire (n := n) base n (fun _ => False) ∧ wire (n := n) base (n + 1) (fun _ => True) := by
  let f : Gate := ⟨.or, []⟩
  let t : Gate := ⟨.and, []⟩
  have hg0 : good n [] := by intro j h; simp at h
  have hg1 : good n [f] := good_add hg0 (by simp [fits, f])
  have hg2 : good n ([f] ++ [t]) := good_add hg1 (by simp [fits, t])
  have hf : wire (n := n) [f] n (fun _ => False) := by
    refine ⟨by simp, fun x => ?_⟩
    have h := val_add [] (List.ofFn x) f
    simpa [f, GateOp.eval] using h
  refine ⟨[f] ++ [t], rfl, hg2, wire_keep (List.prefix_append _ _) hf, by simp, fun x => ?_⟩
  have h := val_add [f] (List.ofFn x) t
  simpa [t, GateOp.eval] using h

end PEqualNP.Outside.L_clb_044

open PEqualNP.Outside.L_clb_044

theorem PEqualNP.Outside.L_clb_044 : (∀ (n t d b : Nat)
  (guard : Fin t → Nat → (Fin n → Bool) → Bool),
  (∀ (i : Fin t) (pattern : Nat), pattern < 2 ^ (d + 1) →
    ∃ G : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo G ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n G ∧
      G.size ≤ b ∧
      ∀ x : Fin n → Bool, G.eval (List.ofFn x) = guard i pattern x) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    C.size ≤ 2 ^ d * (t * (2 * b + 3) + 1) + 2 ∧
    ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ word : Fin (2 ^ (t + d)), ∀ i : Fin t,
        guard i ((word.val / 2 ^ i.val) % 2 ^ (d + 1)) x = true)) := by
  intro n t d b guard hguard
  let m : Nat := 2 ^ d
  have hm : 0 < m := by positivity
  have hd : 2 ^ (d + 1) = 2 * m := by simp [m, pow_succ']
  rw [hd] at hguard
  obtain ⟨base, hlen, hg, hf, ht⟩ := constants n
  obtain ⟨gs, hp, hgs, hsize, hb⟩ := layers hm t guard hguard base hg hf ht
  obtain ⟨hs, o, _, hhs, hsize', hw⟩ :=
    finish gs m (fun s => reach m t guard s) hgs (wire_keep hp hf) hb
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨hs, o⟩
  have hC := good_to_circuit (n := n) (C := C) hhs
  refine ⟨C, hC.1, hC.2, ?_, fun x => ?_⟩
  · change hs.length ≤ _
    change hs.length ≤ m * (t * (2 * b + 3) + 1) + 2
    have hcal : m * (t * (2 * b + 3) + 1) + 2 = 2 + t * (m * (2 * b + 3)) + m := by ring
    rw [hcal]
    omega
  · change val hs (List.ofFn x) o = true ↔ _
    rw [hw.2 x]
    have hpow : 2 ^ (t + d) = 2 ^ t * m := by rw [pow_add]
    constructor
    · rintro ⟨s, _, w, hlt, _, h⟩
      refine ⟨⟨w, by rwa [hpow]⟩, fun i => ?_⟩
      simpa only [hd] using h i
    · rintro ⟨w, h⟩
      refine ⟨w.val % m, Nat.mod_lt _ hm, w.val, by rw [← hpow]; exact w.isLt, rfl, fun i => ?_⟩
      simpa only [hd] using h i
