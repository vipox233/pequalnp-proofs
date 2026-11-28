import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_446

lemma mass_bound (n m b : ℕ)
    (mass : (Fin n → Bool) → ℕ)
    (w : Fin m → Bool → Fin (2^b))
    (edgeBit : (Fin n → Bool) → Fin m → Bool)
    (h : ∀ x, mass x ≤ ∏ e, (w e (edgeBit x e)).val) :
    ∑ x, mass x < 2 ^ (n + m*b + 1) := by
  have bound (x : Fin n → Bool) : mass x ≤ 2^(m*b) := by
    calc
      mass x ≤ ∏ e, (w e (edgeBit x e)).val := h x
      _ ≤ ∏ _e : Fin m, 2^b := Finset.prod_le_prod fun e _ => (w e (edgeBit x e)).isLt.le
      _ = 2^(m*b) := by simp [← Nat.pow_mul, Nat.mul_comm]
  calc
    ∑ x, mass x ≤ ∑ _x : Fin n → Bool, 2 ^ (m*b) := Finset.sum_le_sum fun x _ => bound x
    _ = 2 ^ (n + m*b) := by simp [Nat.pow_add]
    _ < 2 ^ (n + m*b + 1) := by rw [pow_succ]; have := Nat.two_pow_pos (n + m*b); omega

lemma bit_sum_mod (v d : ℕ) :
    (∑ i ∈ Finset.range d, (v.testBit i).toNat * 2^i) = v % 2^d := by
  induction d with
  | zero => simp [Nat.mod_one]
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm (v / 2^d % 2)]

lemma decode (v d : ℕ) (hv : v < 2^d) :
    (∑ i : Fin d, (v.testBit i.val).toNat * 2^i.val) = v := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (v.testBit i).toNat * 2^i)]
  exact (bit_sum_mod v d).trans (Nat.mod_eq_of_lt hv)

lemma input_size (n m t b : ℕ) :
    2+(1+t*t)*(m+1)^3*(n+m*b+1)+2*t+t*t+3*(m+1)+(n+m*b+1) ≤
      (n+m+t+b+2)^9 := by
  let k := n+m+t+b+2
  have hn : n ≤ k := by dsimp [k]; omega
  have hm : m ≤ k := by dsimp [k]; omega
  have ht : t ≤ k := by dsimp [k]; omega
  have hb : b ≤ k := by dsimp [k]; omega
  have hm1 : m+1 ≤ k := by dsimp [k]; omega
  change _ ≤ k^9
  calc
    _ ≤ 2+(1+k*k)*k^3*(k+k*k+1)+2*k+k*k+3*k+(k+k*k+1) := by gcongr
    _ ≤ k^9 := by
      dsimp [k]
      generalize n+m+t+b = q

      ring_nf
      omega

lemma weighted_prefix {α : Type} [Fintype α]
    (mass code : α → ℕ) (limit index : ℕ) (hpos : 0 < limit)
    (hcode : ∀ x, code x < limit) (hindex : index < ∑ x, mass x) :
    ∃ k < limit, (∑ x, if code x < k then mass x else 0) ≤ index ∧
      index < ∑ x, if code x ≤ k then mass x else 0 := by
  classical
  let P := fun k : ℕ => index < ∑ x, if code x ≤ k then mass x else 0
  have last : P (limit-1) := by
    dsimp [P]
    have hc : ∀ x, code x ≤ limit-1 := by intro x; have := hcode x; omega
    simpa [hc] using hindex
  have ex : ∃ k, P k := ⟨_,last⟩
  refine ⟨Nat.find ex, by have := Nat.find_min' ex last; omega, ?_, Nat.find_spec ex⟩
  match hk : Nat.find ex with
  | 0 => simp
  | k+1 =>
    have h : ¬ P k := Nat.find_min ex (by omega)
    simpa [P, Nat.lt_succ_iff] using h

lemma flat_length {α : Type} {n m : ℕ}
    (f : Fin n → List α) (h : ∀ i, (f i).length = m) :
    (List.ofFn f).flatten.length = n*m := by
  rw [List.length_flatten, List.map_ofFn]
  have hc : List.length ∘ f = fun _ => m := funext h
  rw [hc, List.ofFn_const, List.sum_replicate_nat]

lemma block_length {m d : ℕ}
    (cell : Fin (m+1) → Fin (m+1) → Fin (m+1) → Fin d → Bool) :
    ((List.ofFn fun l => (List.ofFn fun r =>
      (List.ofFn fun h => List.ofFn (cell l r h)).flatten).flatten).flatten).length =
    (m+1)^3*d := by
  have hinner (l r : Fin (m+1)) :
      (List.ofFn fun h => List.ofFn (cell l r h)).flatten.length = (m+1)*d :=
    flat_length _ fun _ => List.length_ofFn
  have hmid (l : Fin (m+1)) :
      (List.ofFn fun r => (List.ofFn fun h => List.ofFn (cell l r h)).flatten).flatten.length =
        (m+1)*((m+1)*d) :=
    flat_length _ (hinner l)
  rw [flat_length _ hmid]
  ring

lemma layout {m t d : ℕ}
    (block : Finset (Fin t) → List Bool) (hblock : ∀ p, (block p).length = (m+1)^3*d)
    (per : Fin t → Bool → Bool) (order : Equiv.Perm (Fin t))
    (hot : Fin (m+1) → List Bool) (hhot : ∀ i, (hot i).length = m+1)
    (a y z : Fin (m+1)) (bits : List Bool) (hbits : bits.length = d) :
    let pairs := (List.ofFn fun i : Fin t =>
      (List.ofFn fun j : Fin t => block (if i = j then ∅ else {i,j})).flatten).flatten
    let mask := (List.ofFn fun i : Fin t => [per i false, per i true]).flatten
    let perm := (List.ofFn fun i : Fin t => List.ofFn fun j : Fin t => decide (order i = j)).flatten
    ([false,true] ++ block ∅ ++ pairs ++ mask ++ perm ++ hot a ++ hot y ++ hot z ++ bits).length =
      2+(1+t*t)*(m+1)^3*d+2*t+t*t+3*(m+1)+d := by
  dsimp only
  have hp (i : Fin t) : (List.ofFn fun j : Fin t =>
      block (if i = j then ∅ else {i,j})).flatten.length = t*((m+1)^3*d) :=
    flat_length _ fun _ => hblock _
  simp only [List.length_append, List.length_cons, List.length_nil, hblock, hhot, hbits]
  rw [flat_length _ hp,
      flat_length (m := 2) (fun i : Fin t => [per i false,per i true]) (fun _ => rfl),
      flat_length _ (fun _ => List.length_ofFn :
        ∀ i : Fin t, (List.ofFn fun j : Fin t => decide (order i = j)).length = t)]
  ring

lemma word_bound {t : ℕ} (w : Fin t → Bool) :
    (∑ i : Fin t, (w i).toNat * 2^(t-1-i.val)) < 2^t := by
  have hrev := Equiv.sum_comp (Fin.revPerm : Fin t ≃ Fin t) (fun i : Fin t => 2^i.val : Fin t → ℕ)
  have hsum : (∑ i : Fin t, 2^(t-1-i.val) : ℕ) = ∑ i : Fin t, 2^i.val := by
    simpa [Nat.sub_sub, Nat.add_comm] using hrev
  have hgeom (n : ℕ) : (∑ i ∈ Finset.range n, 2^i : ℕ) + 1 = 2^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
  calc
    _ ≤ ∑ i : Fin t, 2^(t-1-i.val) := Finset.sum_le_sum fun i _ => by cases w i <;> simp
    _ = ∑ i : Fin t, 2^i.val := hsum
    _ < 2^t := by rw [Fin.sum_univ_eq_sum_range (fun i => 2^i) t]; have := hgeom t; omega

lemma word_encode {t k : ℕ} (hk : k < 2^t) :
    (∑ i : Fin t, (k.testBit (t-1-i.val)).toNat * 2^(t-1-i.val)) = k := by
  have h := Equiv.sum_comp (Fin.revPerm : Fin t ≃ Fin t)
    (fun i : Fin t => (k.testBit i.val).toNat * 2^i.val)
  exact (by simpa [Nat.sub_sub, Nat.add_comm] using h :
    (∑ i : Fin t, (k.testBit (t-1-i.val)).toNat * 2^(t-1-i.val)) =
    (∑ i : Fin t, (k.testBit i.val).toNat * 2^i.val)).trans
      (decode k t hk)

private def pcxCompareStep (k a b c : ℕ) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.not,[a]⟩, ⟨.or,[b,c]⟩, ⟨.and,[k,k+1]⟩, ⟨.and,[b,c]⟩, ⟨.or,[k+2,k+3]⟩], k+4⟩

private theorem pcxCompareStep_shape (k a b c : ℕ) (ha : a < k) (hb : b < k) (hc : c < k) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack k (pcxCompareStep k a b c) ∧
    (pcxCompareStep k a b c).size = 5 ∧
    ∀ g ∈ (pcxCompareStep k a b c).gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1) := by
  constructor
  · intro j hj i hi
    change j < 5 at hj
    interval_cases j <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt, pcxCompareStep] at hi <;> omega
  · refine ⟨rfl, ?_⟩
    intro g hg
    simp [pcxCompareStep] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl <;> simp

private theorem pcxCompareStep_eval (w : List Bool) (a b c : ℕ)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) :
    (pcxCompareStep w.length a b c).eval w =
      ((!w.getD a false && (w.getD b false || w.getD c false)) ||
        (w.getD b false && w.getD c false)) := by
  simp [pcxCompareStep, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
    List.getElem?_append_left, ha, hb, hc, List.getD]

private theorem pcxCompareStep_bit (a b : Bool) (x y bound : ℕ)
    (hx : x < bound) (hy : y < bound) :
    ((!a && (b || decide (x < y))) || (b && decide (x < y))) =
      decide (x+a.toNat*bound < y+b.toNat*bound) := by
  cases a <;> cases b <;> simp <;> omega

private def pcxCompare (n start : ℕ) (a b : ℕ → ℕ) : ℕ → PEqualNP.CircuitLowerBounds.Circuit
  | 0 => ⟨[], start⟩
  | k+1 =>
    let c := pcxCompare n start a b k
    let s := pcxCompareStep (n+c.size) (a k) (b k) c.output
    ⟨c.gates ++ s.gates, s.output⟩

private theorem pcxCompare_size (n start : ℕ) (a b : ℕ → ℕ) (k : ℕ) :
    (pcxCompare n start a b k).size = 5*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((pcxCompare n start a b k).gates ++ _).length = _
    rw [List.length_append]
    change (pcxCompare n start a b k).size + 5 = _
    rw [ih, Nat.mul_succ]

private theorem pcxCompare_output (n start : ℕ) (a b : ℕ → ℕ) (hstart : start < n) (k : ℕ) :
    (pcxCompare n start a b k).output < n+(pcxCompare n start a b k).size := by
  cases k with
  | zero => exact hstart
  | succ k =>
    change n + (pcxCompare n start a b k).size + 4 < _
    rw [pcxCompare_size,pcxCompare_size]
    omega

private theorem pcxWireSuffix (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    ∃ u, (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires w = w ++ u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [PEqualNP.CircuitLowerBounds.Circuit.wires],rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨u,h,hu⟩ := ih (w++[v])
    exact ⟨v::u, by simpa [PEqualNP.CircuitLowerBounds.Circuit.wires,v,List.append_assoc] using h,
      by simp [hu]⟩

private theorem pcxEvalAppend (C S : PEqualNP.CircuitLowerBounds.Circuit) (w : List Bool) :
    (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates ++ S.gates) S.output).eval w =
      S.eval (C.wires w) := by
  simp [PEqualNP.CircuitLowerBounds.Circuit.eval,PEqualNP.CircuitLowerBounds.Circuit.wires,
    List.foldl_append]

private theorem pcxCompare_eval (n start : ℕ) (a b : ℕ → ℕ) (x y k : ℕ) (w : List Bool)
    (hlen : w.length = n) (hs : start < n) (hz : w.getD start false = false)
    (ha : ∀ j, a j < n) (hb : ∀ j, b j < n)
    (hbits : ∀ j < k, w.getD (a j) false = x.testBit j ∧ w.getD (b j) false = y.testBit j) :
    (pcxCompare n start a b k).eval w = decide (x % 2^k < y % 2^k) := by
  induction k with
  | zero => simpa [pcxCompare, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, Nat.mod_one] using hz
  | succ k ih =>
    let C := pcxCompare n start a b k
    obtain ⟨u,hu,huLen⟩ := pcxWireSuffix C.gates w
    change C.wires w = w ++ u at hu
    have hwLen : (C.wires w).length = n+C.size := by
      rw [hu,List.length_append,hlen,huLen]; rfl
    have hA : a k < w.length := hlen ▸ ha k
    have hB : b k < w.length := hlen ▸ hb k
    have hA' : a k < (C.wires w).length := by rw [hwLen]; have := ha k; omega
    have hB' : b k < (C.wires w).length := by rw [hwLen]; have := hb k; omega
    have hOut : C.output < (C.wires w).length :=
      hwLen ▸ pcxCompare_output n start a b hs k
    have input := hbits k (Nat.lt_succ_self k)
    have eA : (C.wires w).getD (a k) false = x.testBit k := by
      simpa [hu, List.getD, List.getElem?_append_left, hA] using input.1
    have eB : (C.wires w).getD (b k) false = y.testBit k := by
      simpa [hu, List.getD, List.getElem?_append_left, hB] using input.2
    have carry : (C.wires w).getD C.output false = decide (x % 2^k < y % 2^k) :=
      ih fun i hi => hbits i (by omega)
    change (PEqualNP.CircuitLowerBounds.Circuit.mk _ _).eval w = _
    rw [pcxEvalAppend]
    change (pcxCompareStep (n+C.size) (a k) (b k) C.output).eval (C.wires w) = _
    rw [← hwLen, pcxCompareStep_eval _ _ _ _ hA' hB' hOut, eA,eB,carry]
    rw [pcxCompareStep_bit _ _ _ _ (2^k) (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [Nat.toNat_testBit,Nat.mod_pow_succ]
    rw [Nat.mul_comm (x / 2^k % 2),Nat.mul_comm (y / 2^k % 2)]

private theorem pcxBackAppend (n : ℕ) (C S : PEqualNP.CircuitLowerBounds.Circuit)
    (hc : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hs : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+C.size) S) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n
      (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates++S.gates) S.output) := by
  intro j hj i hi
  change j < (C.gates++S.gates).length at hj
  rw [List.length_append] at hj
  by_cases h : j < C.gates.length
  · apply hc j h i
    simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h] using hi
  · have hg : j-C.gates.length < S.gates.length := by omega
    have hm : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt S (j-C.gates.length)).inputs := by
      simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (Nat.le_of_not_gt h)] using hi
    have hc := hs _ hg i hm
    change i < n+C.gates.length+(j-C.gates.length) at hc
    omega

private theorem pcxCompare_shape (n start : ℕ) (a b : ℕ → ℕ) (hs : start < n)
    (ha : ∀ i, a i < n) (hb : ∀ i, b i < n) (k : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (pcxCompare n start a b k) ∧
    ∀ g ∈ (pcxCompare n start a b k).gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1) := by
  induction k with
  | zero =>
    constructor
    · intro j hj; exact False.elim (Nat.not_lt_zero j hj)
    · simp [pcxCompare]
  | succ k ih =>
    let C := pcxCompare n start a b k
    let S := pcxCompareStep (n+C.size) (a k) (b k) C.output
    have h := pcxCompareStep_shape (n+C.size) (a k) (b k) C.output
      (by have := ha k; omega) (by have := hb k; omega) (pcxCompare_output n start a b hs k)
    refine ⟨pcxBackAppend n C S ih.1 h.1, ?_⟩
    intro g hg
    change g ∈ C.gates ++ S.gates at hg
    rcases List.mem_append.mp hg with hg|hg
    · exact ih.2 g hg
    · exact h.2.2 g hg

private theorem pcxFlagCircuit (n d start : ℕ) (a b : ℕ → ℕ)
    (hs : start < n) (ha : ∀ i, a i < n) (hb : ∀ i, b i < n) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 5*d ∧ C.output < n+C.size ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)) ∧
      ∀ (w : List Bool) (x y : ℕ), w.length = n → w.getD start false = false →
        x < 2^d → y < 2^d →
        (∀ i < d, w.getD (a i) false = x.testBit i ∧ w.getD (b i) false = y.testBit i) →
        C.eval w = decide (x < y) := by
  obtain ⟨back, fan⟩ := pcxCompare_shape n start a b hs ha hb d
  refine ⟨pcxCompare n start a b d, pcxCompare_size _ _ _ _ _, pcxCompare_output _ _ _ _ hs _,
    back, fan, ?_⟩
  intro w x y hw hz hx hy bits
  simpa [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using
    pcxCompare_eval n start a b x y d w hw hs hz ha hb bits

private def pcxMuxStep (k a b c : ℕ) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and,[a,b]⟩,⟨.or,[c,k]⟩],k+1⟩

private def pcxMux (n start : ℕ) (sel val : ℕ → ℕ) : ℕ → PEqualNP.CircuitLowerBounds.Circuit
  | 0 => ⟨[],start⟩
  | k+1 =>
    let c := pcxMux n start sel val k
    let s := pcxMuxStep (n+c.size) (sel k) (val k) c.output
    ⟨c.gates++s.gates,s.output⟩

private theorem pcxMux_shape (n start : ℕ) (sel val : ℕ → ℕ) (hs : start < n)
    (hsel : ∀ i, sel i < n) (hval : ∀ i, val i < n) (k : ℕ) :
    let c := pcxMux n start sel val k
    c.size = 2*k ∧ c.output < n+c.size ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n c ∧
      ∀ g ∈ c.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction k with
  | zero =>
    refine ⟨rfl,hs,?_,?_⟩
    · intro j hj; exact False.elim (Nat.not_lt_zero j hj)
    · simp [pcxMux]
  | succ k ih =>
    let c := pcxMux n start sel val k
    let s := pcxMuxStep (n+c.size) (sel k) (val k) c.output
    have hsSize : (pcxMux n start sel val (k+1)).size = c.size+2 := by
      change (c.gates++s.gates).length = _
      rw [List.length_append]
      rfl
    have hsBack : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+c.size) s := by
      intro j hj i hi
      change j < 2 at hj
      have h1 := hsel k
      have h2 := hval k
      have h3 : c.output < n+c.size := ih.2.1
      interval_cases j <;> simp [s,pcxMuxStep,PEqualNP.MetaComplexity.NestedCover.gateAt] at hi <;> omega
    dsimp only
    refine ⟨by rw [hsSize,show c.size = 2*k from ih.1]; omega,?_,pcxBackAppend n c s ih.2.2.1 hsBack,?_⟩
    · rw [hsSize]
      change n+c.size+1 < n+(c.size+2)
      omega
    · intro g hg
      change g ∈ c.gates ++ s.gates at hg
      rcases List.mem_append.mp hg with h|h
      · exact ih.2.2.2 _ h
      · simp [s,pcxMuxStep] at h
        rcases h with rfl|rfl <;> simp

private theorem pcxMuxStep_eval (w : List Bool) (a b c : ℕ)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) :
    (pcxMuxStep w.length a b c).eval w =
      (w.getD c false || (w.getD a false && w.getD b false)) := by
  simp [pcxMuxStep, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
    List.getElem?_append_left,ha,hb,hc,List.getD]

private theorem pcxMux_eval (n start : ℕ) (sel val : ℕ → ℕ) (k : ℕ) (w : List Bool)
    (hlen : w.length = n) (hs : start < n) (hz : w.getD start false = false)
    (hsel : ∀ i, sel i < n) (hval : ∀ i, val i < n) :
    (pcxMux n start sel val k).eval w =
      (List.range k).any (fun i => w.getD (sel i) false && w.getD (val i) false) := by
  induction k with
  | zero => simpa [pcxMux,PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires] using hz
  | succ k ih =>
    let c := pcxMux n start sel val k
    obtain ⟨u,hu,huLen⟩ := pcxWireSuffix c.gates w
    change c.wires w = w++u at hu
    have hLen : (c.wires w).length = n+c.size := by rw [hu,List.length_append,hlen,huLen]; rfl
    have ha : sel k < w.length := hlen ▸ hsel k
    have hb : val k < w.length := hlen ▸ hval k
    have ha' : sel k < (c.wires w).length := by rw [hLen]; have := hsel k; omega
    have hb' : val k < (c.wires w).length := by rw [hLen]; have := hval k; omega
    have hc : c.output < (c.wires w).length := hLen ▸ (pcxMux_shape n start sel val hs hsel hval k).2.1
    have hA : (c.wires w).getD (sel k) false = w.getD (sel k) false := by
      simp [hu,List.getD,List.getElem?_append_left,ha]
    have hB : (c.wires w).getD (val k) false = w.getD (val k) false := by
      simp [hu,List.getD,List.getElem?_append_left,hb]
    have carry : (c.wires w).getD c.output false = _ := ih
    change (PEqualNP.CircuitLowerBounds.Circuit.mk _ _).eval w = _
    rw [pcxEvalAppend]
    change (pcxMuxStep (n+c.size) (sel k) (val k) c.output).eval (c.wires w) = _
    rw [← hLen, pcxMuxStep_eval _ _ _ _ ha' hb' hc, hA,hB,carry]
    simp [List.range_succ]

private theorem pcxMux_hot (n start : ℕ) (sel val : ℕ → ℕ) (k j : ℕ) (w : List Bool)
    (hlen : w.length = n) (hs : start < n) (hz : w.getD start false = false)
    (hsel : ∀ i, sel i < n) (hval : ∀ i, val i < n) (hj : j < k)
    (hot : ∀ i < k, w.getD (sel i) false = decide (i=j)) :
    (pcxMux n start sel val k).eval w = w.getD (val j) false := by
  rw [pcxMux_eval _ _ _ _ _ _ hlen hs hz hsel hval]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i,hi,yes⟩
    have hk := List.mem_range.mp hi
    rw [hot i hk] at yes
    have eq := of_decide_eq_true (Bool.and_eq_true_iff.mp yes).1
    simpa [eq] using (Bool.and_eq_true_iff.mp yes).2
  · intro h
    exact ⟨j,List.mem_range.mpr hj,Bool.and_eq_true_iff.mpr ⟨(hot j hj).trans (by simp),h⟩⟩

private def packed (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: tail => a + 2^d * packed d tail

private theorem packed_width (d : ℕ) (xs : List ℕ) (small : ∀ a ∈ xs, a < 2^d) :
    packed d xs < 2^(d*xs.length) := by
  induction xs with
  | nil => simp [packed]
  | cons a tail ih =>
    have ha := small a (by simp)
    have ht := ih (fun b hb => small b (by simp [hb]))
    simp only [packed, List.length_cons, Nat.mul_succ, pow_add]
    have h := Nat.mul_le_mul_left (2^d) (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at h
    rw [Nat.mul_comm (2 ^ (d * tail.length))]
    omega

private theorem packed_digit (d : ℕ) (xs : List ℕ) (small : ∀ a ∈ xs, a < 2^d)
    (k j : ℕ) (hj : j < d) :
    (packed d xs).testBit (d*k+j) = (xs.getD k 0).testBit j := by
  induction xs generalizing k with
  | nil => simp [packed]
  | cons a tail ih =>
    have ha := small a (by simp)
    have ht := ih (fun b hb => small b (by simp [hb]))
    cases k with
    | zero =>
      change (a + 2^d * packed d tail).testBit (d*0+j) = a.testBit j
      simp only [Nat.mul_zero,Nat.zero_add]
      have hm := Nat.testBit_mod_two_pow (a + 2^d * packed d tail) d j
      simpa [hj, Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha] using hm.symm
    | succ k =>
      change (a + 2^d * packed d tail).testBit (d*(k+1)+j) = (tail.getD k 0).testBit j
      rw [show d*(k+1)+j = (d*k+j)+d by rw [Nat.mul_succ]; omega,
        ← Nat.testBit_div_two_pow]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d),Nat.div_eq_of_lt ha,Nat.zero_add]
      exact ht k

private theorem packed_monomial (m d : ℕ) (w : Fin m → Bool → ℕ) (col : Fin m → Fin 3)
    (diff : Fin m → Bool) :
    let s := m + 1
    let B := 2^d
    let tally (k : Fin 3) := (Finset.univ.filter (fun e => col e = k ∧ diff e = true)).card
    let digit (k : Fin 3) := if k = 0 then s*s else if k = 1 then s else 1
    (∏ e, w e (diff e) * B^(if diff e then digit (col e) else 0)) =
      (∏ e, w e (diff e)) * B^(tally 0 * (s*s) + tally 1 * s + tally 2) := by
  classical
  intro s B tally digit
  let ind (e : Fin m) (k : Fin 3) : ℕ := if col e = k ∧ diff e = true then 1 else 0
  have hs (e : Fin m) : (if diff e then digit (col e) else 0) =
      ind e 0 * (s*s) + ind e 1 * s + ind e 2 := by
    cases h : diff e <;> rcases (show col e = 0 ∨ col e = 1 ∨ col e = 2 by
      generalize col e = c
      fin_cases c <;> decide) with hcol|hcol|hcol <;> simp [ind,digit,h,hcol]
  have hc (k : Fin 3) : (∑ e, ind e k) = tally k := by
    simp [ind,tally,Finset.sum_boole]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  simp_rw [hs, Finset.sum_add_distrib, ← Finset.sum_mul, hc]
private theorem partition_by_histogram {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (cell : X → J) (v : X → ℕ) (B : ℕ) (slot : J → ℕ) :
    (∑ j, (∑ x, if cell x = j then v x else 0)*B^(slot j)) =
    ∑ x, v x * B^(slot (cell x)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

private theorem partition_positive_iff {X : Type*} [Fintype X] (v : X → ℕ)
    (B : ℕ) (hB : 0 < B) (slot : X → ℕ) :
    (∑ x, v x * B^(slot x)) = 0 ↔ ∀ x, v x = 0 := by
  simp [Nat.ne_of_gt hB]

private theorem weighted_prefix_branch {X : Type*} [Fintype X] (mass code : X → ℕ)
    (a b m i : ℕ) (hab : a ≤ m) (_hmb : m ≤ b)
    (hlo : (∑ x, if code x < a then mass x else 0) ≤ i)
    (_hhi : i < ∑ x, if code x < b then mass x else 0) :
    let left := ∑ x, if a ≤ code x ∧ code x < m then mass x else 0
    let offset := i - ∑ x, if code x < a then mass x else 0
    (if offset < left then
      i < ∑ x, if code x < m then mass x else 0
     else (∑ x, if code x < m then mass x else 0) ≤ i) := by
  classical
  intro left offset
  have hpart : (∑ x, if code x < m then mass x else 0) =
      (∑ x, if code x < a then mass x else 0) + left := by
    dsimp [left]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : code x < a
    · have h' : code x < m := by omega
      simp [h, h', Nat.not_le_of_gt h]
    · have hx : a ≤ code x := by omega
      simp [h,hx]
  dsimp only [offset]
  split <;> omega

private def locate (mass : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | k+1, a, i =>
    let mid := a + 2^k
    let left := mass a mid
    if i < left then locate mass k a i else locate mass k mid (i-left)

private theorem locate_spec (P : ℕ → ℕ) (hm : Monotone P)
    (mass : ℕ → ℕ → ℕ) (hM : ∀ a b, a ≤ b → mass a b = P b - P a)
    (k a i : ℕ) (valid : i < mass a (a + 2^k)) :
    let q := locate mass k a i
    a ≤ q ∧ q < a + 2^k ∧ P q ≤ P a+i ∧ P a+i < P (q+1) := by
  induction k generalizing a i with
  | zero =>
    simp only [pow_zero,locate]
    simp only [pow_zero] at valid
    rw [hM _ _ (by omega)] at valid
    omega
  | succ k ih =>
    let mid := a+2^k
    have hsplit : a + 2^(k+1) = mid + 2^k := by dsimp [mid]; rw [pow_succ]; omega
    have ha : a ≤ mid := by exact Nat.le_add_right _ _
    have hb : mid ≤ mid+2^k := by omega
    have hp := hm ha
    simp only [locate]
    rw [show a+2^k = mid by rfl]
    split
    next hx =>
      obtain ⟨l,u,p,v⟩ := ih a i hx
      refine ⟨l, ?_,p,v⟩
      rw [hsplit]
      omega
    next hx =>
      have hRight : i - mass a mid < mass mid (mid+2^k) := by
        rw [hsplit,hM _ _ (ha.trans hb)] at valid
        rw [hM _ _ ha] at hx ⊢
        rw [hM _ _ hb]
        omega
      obtain ⟨l,u,p,v⟩ := ih mid (i-mass a mid) hRight
      have heq : P mid + (i-mass a mid) = P a+i := by rw [hM _ _ ha] at hx ⊢; omega
      exact ⟨ha.trans l,hsplit ▸ u,heq ▸ p,heq ▸ v⟩

private def pcxPairInputs (d : ℕ) : List ℕ → List ℕ
  | [] => [d,d]
  | [a] => [a,a]
  | a::b::_ => [a,b]

private def pcxExactGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  match g.op with
  | .and => ⟨.and,pcxPairInputs 1 g.inputs⟩
  | .or => ⟨.or,pcxPairInputs 0 g.inputs⟩
  | _ => ⟨.not,[g.inputs.headD 0]⟩

private theorem pcxExactGate_shape (g : PEqualNP.CircuitLowerBounds.Gate) :
    (((pcxExactGate g).op = .and ∨ (pcxExactGate g).op = .or) ∧
      (pcxExactGate g).inputs.length = 2) ∨
       ((pcxExactGate g).op = .not ∧ (pcxExactGate g).inputs.length = 1) := by
  obtain ⟨o,l⟩ := g
  rcases l with _ | ⟨a,_|⟨b,l⟩⟩ <;> cases o <;> simp [pcxExactGate,pcxPairInputs]

private theorem pcxExactGate_back (g : PEqualNP.CircuitLowerBounds.Gate) (k : ℕ) (hk : 1 < k)
    (h : ∀ i ∈ g.inputs, i < k) : ∀ i ∈ (pcxExactGate g).inputs, i < k := by
  obtain ⟨o,l⟩ := g
  rcases l with _ | ⟨a,_|⟨b,l⟩⟩ <;> cases o <;>
    simp [pcxExactGate,pcxPairInputs] at h ⊢ <;> aesop (add safe (by omega))

private theorem pcxExactGate_eval (g : PEqualNP.CircuitLowerBounds.Gate)
    (ops : g.op ∈ ({.and,.or,.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (length : g.inputs.length ≤ 2) (w : List Bool) (h0 : w.getD 0 false = false)
    (h1 : w.getD 1 false = true) :
    (pcxExactGate g).op.eval ((pcxExactGate g).inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨o,l⟩ := g
  change o ∈ _ at ops
  simp at ops
  rcases ops with rfl|rfl|rfl <;> rcases l with _ | ⟨a,_|⟨b,_|⟨c,l⟩⟩⟩ <;>
    first | solve | simp at length | simp only [pcxExactGate,pcxPairInputs,List.map_cons,List.map_nil,
      List.headD_nil,List.headD_cons,PEqualNP.CircuitLowerBounds.GateOp.eval,List.all_cons,List.all_nil,
      List.any_cons,List.any_nil,id_eq,h0,h1] <;> simp

private def pcxExactCircuit (c : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨c.gates.map pcxExactGate,c.output⟩

private theorem pcxExactCircuit_back (n : ℕ) (c : PEqualNP.CircuitLowerBounds.Circuit)
    (hn : 1 < n) (back : PEqualNP.MetaComplexity.NestedCover.ReadsBack n c) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (pcxExactCircuit c) := by
  intro j hj i hi
  have h : j < c.gates.length := by simpa [pcxExactCircuit] using hj
  have original : PEqualNP.MetaComplexity.NestedCover.gateAt c j = c.gates[j] :=
    List.getD_eq_getElem _ _ h
  have translated : PEqualNP.MetaComplexity.NestedCover.gateAt (pcxExactCircuit c) j =
      pcxExactGate c.gates[j] := by
    change (c.gates.map pcxExactGate).getD j _ = _
    rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
  rw [translated] at hi
  apply pcxExactGate_back _ _ (by omega) _ i hi
  intro k hk
  exact back j h k (original ▸ hk)

private theorem pcxExactFold (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (fan : PEqualNP.MetaComplexity.FanInTwo (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0))
    (w : List Bool) (length : 1 < w.length) (h0 : w.getD 0 false = false)
    (h1 : w.getD 1 false = true) :
    (PEqualNP.CircuitLowerBounds.Circuit.mk (gs.map pcxExactGate) 0).wires w =
      (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := fan g (by simp)
    have rest : PEqualNP.MetaComplexity.FanInTwo (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0) :=
      fun a ha => fan a (List.mem_cons_of_mem _ ha)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.wires,List.map_cons,List.foldl_cons]
    rw [pcxExactGate_eval _ hg.1 hg.2 _ h0 h1]
    apply ih rest
    · simp; omega
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : 0 < w.length)] using h0
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left length] using h1

private lemma pcxDetBound (k L : ℕ) (A : Matrix (Fin k) (Fin k) ℤ)
    (ha : ∀ i j, |A i j| ≤ (2:ℤ)^L) : |A.det| ≤ (2:ℤ)^(k*(k+L)) := by
  classical
  have each (σ : Equiv.Perm (Fin k)) :
      |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| ≤ ((2:ℤ)^L)^k := by
    rw [abs_mul]
    have hsign : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> rw [h] <;> decide
    rw [hsign,one_mul,Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin k, (2:ℤ)^L :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => ha (σ i) i)
      _ = _ := by simp
  have hpow : k.factorial ≤ 2^(k*k) := by
    calc
      _ ≤ k^k := Nat.factorial_le_pow k
      _ ≤ (2^k)^k := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) k
      _ = _ := (Nat.pow_mul _ _ _).symm
  calc
    |A.det| = |∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| := by
      simp [Matrix.det_apply']
    _ ≤ ∑ σ : Equiv.Perm (Fin k), |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ((2:ℤ)^L)^k := Finset.sum_le_sum (fun i _ => each i)
    _ = (k.factorial : ℤ) * ((2:ℤ)^L)^k := by simp [Fintype.card_perm]
    _ ≤ ((2:ℤ)^(k*k)) * ((2:ℤ)^L)^k := by
      gcongr
      exact_mod_cast hpow
    _ = (2:ℤ)^(k*(k+L)) := by rw [←pow_mul,←pow_add]; congr 1; ring

private theorem pcxDetShift (k modulus : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) :
    (((A + (modulus : ℤ) • (1 : Matrix (Fin k) (Fin k) ℤ)).det : ℤ) : ZMod modulus) =
      (A.det : ZMod modulus) := by
  let f := Int.castRingHom (ZMod modulus)
  change f _ = f _
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  change f (A i j + (modulus : ℤ) * (1 : Matrix (Fin k) (Fin k) ℤ) i j) = f (A i j)
  simp [f]

private lemma pcxShiftNonsingular (k : ℕ) (q bound : ℝ) (A : Matrix (Fin k) (Fin k) ℝ)
    (hB : 0 ≤ bound) (hq : ((k : ℝ) + 1) * bound < q)
    (ha : ∀ i j, |A i j| ≤ bound) : (A + q • 1).det ≠ 0 := by
  classical
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hrow : ∑ j ∈ Finset.univ.erase i, ‖(A + q • 1) i j‖ ≤ k * bound := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, bound := by
        apply Finset.sum_le_sum
        intro j hj
        have hne := (Finset.mem_erase.mp hj).1
        simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne.symm, Real.norm_eq_abs] using ha i j
      _ ≤ ∑ _j : Fin k, bound :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => hB)
      _ = _ := by simp
  apply lt_of_le_of_lt hrow
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,Real.norm_eq_abs]
  apply lt_of_lt_of_le _ (le_abs_self _)
  have hneg := (abs_le.mp (ha i i)).1
  linarith

private lemma pcxShiftPrincipals (k : ℕ) (q bound : ℝ) (A : Matrix (Fin k) (Fin k) ℝ)
    (hB : 0 ≤ bound) (hq : ((k : ℝ) + 1) * bound < q)
    (ha : ∀ i j, |A i j| ≤ bound) (r : ℕ) (f : Fin r ↪ Fin k) :
    ((A + q • 1).submatrix f f).det ≠ 0 := by
  have hr : r ≤ k := by simpa using Fintype.card_le_of_injective f f.injective
  have hq' : ((r : ℝ) + 1) * bound < q :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hr 1) hB) hq
  have heq : (A + q • 1).submatrix f f = A.submatrix f f + q • 1 := by
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,f.injective.eq_iff]
  rw [heq]
  exact pcxShiftNonsingular r q bound _ hB hq' (fun i j => ha (f i) (f j))

namespace Pcx446Arithmetic
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Sig (N : Nat) := (Fin N → Bool) → Bool

def Scheduled (N : Nat) (sz : Nat) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = sz ∧ ReadsBack N ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < N + sz ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

lemma wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma realizeDeps {N sz : Nat} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < N + sz ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < N + sz) ∧
      ∀ x : Fin N → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

lemma pushSched {N sz : Nat} {S : Set (Sig N)}
    (h : Scheduled N sz S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (sz + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + sz := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by change is.length ≤ 2; simpa only [his] using hlen⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨N + sz, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

def Build {N : Nat} (A B : Set (Sig N)) (b : Nat) : Prop :=
  ∀ (sz : Nat) (S : Set (Sig N)), Scheduled N sz S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (sz + c) (S ∪ B)

lemma idleB {N : Nat} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  fun _ _ hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩

lemma relaxB {N : Nat} {A A' B B' : Set (Sig N)} {b b' : Nat}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  fun sz S hs ha => by
    obtain ⟨c, hc, hsc⟩ := H sz S hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)

lemma seqB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  fun sz S hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1 sz S hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2 (sz + c1) (S ∪ B) hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2

lemma seq2B {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

lemma extB {N : Nat} {A B : Set (Sig N)} {b : Nat} (H : Build A B b) : Build A (A ∪ B) b :=
  relaxB H le_rfl le_rfl le_rfl

lemma transB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build B C c) : Build A C (b + c) :=
  relaxB (seqB H1 (relaxB H2 Set.subset_union_right Set.subset_union_right le_rfl))
    le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

lemma unionB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

lemma gateB {N : Nat} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  fun _ _ hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩

lemma notB {N : Nat} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

lemma andB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma orB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma xorB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let s1 : Sig N := fun x => f x || g x
  let s2 : Sig N := fun x => f x && g x
  let s3 : Sig N := fun x => !(s2 x)
  let s4 : Sig N := fun x => s1 x && s3 x
  have h1 : Build A {s1} 1 := orB hf hg
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hf) (Or.inl hg)
  have h3 : Build ((A ∪ {s1}) ∪ {s2}) {s3} 1 := notB (Or.inr rfl)
  have h4 : Build (((A ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 :=
    andB (Or.inl (Or.inl (Or.inr rfl))) (Or.inr rfl)
  have heq : s4 = fun x => xor (f x) (g x) := by
    funext x; simp only [s4, s3, s2, s1]; cases f x <;> cases g x <;> rfl
  rw [← heq]
  exact relaxB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) h4)
    le_rfl Set.subset_union_right (by omega)

lemma listB {N : Nat} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : Nat)
    (l : List α) (h : ∀ a ∈ l, Build A (F a) c) :
    Build A (⋃ a ∈ l, F a) (l.length * c) := by
  induction l with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    intro f hf
    simp at hf
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    have hu := unionB h1 h2
    refine relaxB hu le_rfl ?_ (by simp only [List.length_cons, Nat.succ_mul]; omega)
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hbl, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨b, hbl, hfb⟩))

lemma finB {N n : Nat} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : Nat)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  rw [List.length_finRange] at hl
  refine relaxB hl le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, List.mem_finRange i, hfi⟩)

lemma finSigB {N n : Nat} {A : Set (Sig N)} (F : Fin n → Sig N) (c : Nat)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

lemma fullAdderB {N : Nat} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let t1 : Sig N := fun x => xor (fa x) (fb x)
  let sOut : Sig N := fun x => xor (t1 x) (fc x)
  let c1 : Sig N := fun x => fa x && fb x
  let c2 : Sig N := fun x => t1 x && fc x
  let cOut : Sig N := fun x => c1 x || c2 x
  have h1 : Build A {t1} 4 := xorB ha hb
  have h2 : Build (A ∪ {t1}) {sOut} 4 := xorB (Or.inr rfl) (Or.inl hc)
  have h3 : Build ((A ∪ {t1}) ∪ {sOut}) {c1} 1 := andB (Or.inl (Or.inl ha)) (Or.inl (Or.inl hb))
  have h4 : Build (((A ∪ {t1}) ∪ {sOut}) ∪ {c1}) {c2} 1 :=
    andB (Or.inl (Or.inl (Or.inr rfl))) (Or.inl (Or.inl (Or.inl hc)))
  have h5 : Build ((((A ∪ {t1}) ∪ {sOut}) ∪ {c1}) ∪ {c2}) {cOut} 1 :=
    orB (Or.inl (Or.inr rfl)) (Or.inr rfl)
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1' : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1' x || fc x
  let tcAnd : Sig N := fun x => t1' x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut' : Sig N := fun x => tcOr x && tcNand x
  let cOut' : Sig N := fun x => abAnd x || tcAnd x
  have g1 : Build A {abOr} 1 := orB ha hb
  have g2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have g3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have g4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1'} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have g5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have g6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have g7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have g8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut'} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have g9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut'})) {cOut'} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB g1 g2) g3) g4) g5) g6) g7) g8) g9
  have hsEq : sOut' = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x; simp only [sOut', tcOr, tcNand, tcAnd, t1', abOr, abNand, abAnd, faSum]
    cases fa x <;> cases fb x <;> cases fc x <;> rfl
  have hcEq : cOut' = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x; simp only [cOut', tcAnd, t1', abOr, abNand, abAnd, faCarry]
    cases fa x <;> cases fb x <;> cases fc x <;> rfl
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]; exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]; exact Or.inr (Or.inr rfl)

def rippleCarry (a b : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

lemma testBit_eq_decide_div_mod (x j : Nat) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

lemma mod_two_pow_succ_eq (a j : Nat) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

lemma rippleCarry_spec (a b : Nat) :
    ∀ j : Nat,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : Nat, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]; omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]; exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;> simp [faSum, hc, ha, hb]

def bitsOf {N : Nat} (L : Nat) (F : (Fin N → Bool) → Nat) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

lemma rippleB {N : Nat} {A : Set (Sig N)} (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : Nat,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x; unfold bitsOf; rw [hjeq]; exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

lemma sumTwoB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl (fun _ hf => Or.inr (Or.inl hf)) le_rfl

def sumListVal {N : Nat} : List ((Fin N → Bool) → Nat) → (Fin N → Bool) → Nat
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

lemma sumListVal_eq_sum {N : Nat} (Fs : List ((Fin N → Bool) → Nat)) (x : Fin N → Bool) :
    sumListVal Fs x = (Fs.map (fun F => F x)).sum := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [sumListVal, ih]

lemma sumListB {N : Nat} {A : Set (Sig N)} (L : Nat)
    (hfalse : (fun _ => false) ∈ A)
    (Fs : List ((Fin N → Bool) → Nat))
    (hFs : ∀ F ∈ Fs, ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal Fs))) (Fs.length * (9 * L)) := by
  induction Fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have : bitsOf L (sumListVal ([] : List ((Fin N → Bool) → Nat))) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons F Fs ih =>
    have h1 := ih (fun G hG => hFs G (List.mem_cons_of_mem F hG))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal Fs)))
        (Set.range (bitsOf L (fun x => F x + sumListVal Fs x))) (9 * L) :=
      sumTwoB L F (sumListVal Fs) (Or.inl hfalse)
        (fun j => Or.inl (hFs F List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    refine relaxB (seq2B h1 h2) le_rfl Set.subset_union_right ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

private def pcxMulRow {N : ℕ} (F G : (Fin N → Bool) → ℕ) (j : ℕ) (x : Fin N → Bool) : ℕ :=
  if (G x).testBit j then 2^j * F x else 0

private theorem pcxMulBuild {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (hF : ∀ i : Fin L, bitsOf L F i ∈ A)
    (hG : ∀ i : Fin L, bitsOf L G i ∈ A)
    (hdecode : ∀ x, (∑ j : Fin L, ((G x).testBit j.val).toNat * 2^j.val) = G x) :
    Build A (Set.range (bitsOf L (fun x => F x * G x))) (10*L^2) := by
  let row := fun j : Fin L => pcxMulRow F G j.val
  let cols := fun j : Fin L => Set.range (bitsOf L (row j))
  have hrow (j i : Fin L) : Build A {bitsOf L (row j) i} 1 := by
    by_cases hji : j ≤ i
    · let k : Fin L := ⟨i.val-j.val,by have := i.isLt; omega⟩
      have eq : bitsOf L (row j) i = (fun x => (G x).testBit j.val && (F x).testBit k.val) := by
        funext x
        dsimp [bitsOf,row,pcxMulRow,k]
        cases e : (G x).testBit j.val <;> simp [Nat.testBit_two_pow_mul,Fin.le_iff_val_le_val.mp hji]
      rw [eq]
      exact andB (hG j) (hF k)
    · have eq : bitsOf L (row j) i = fun _ => false := by
        funext x
        dsimp [bitsOf,row,pcxMulRow]
        cases e : (G x).testBit j.val <;> simp [Nat.testBit_two_pow_mul,
          show ¬ j.val ≤ i.val from hji]
      rw [eq]
      exact relaxB (idleB (A := A) (B := {fun _ => false}) (by simpa using hfalse)) le_rfl Set.subset_union_right (by omega)
  have first : Build A (⋃ j, cols j) (L*L) := by
    simpa [cols] using (finB cols (L*1) (fun j => finSigB (bitsOf L (row j)) 1 (hrow j)))
  let rows := List.ofFn row
  have second := sumListB (A := A ∪ ⋃ j, cols j) L (Or.inl hfalse) rows (by
    intro f hf i
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    exact Or.inr (Set.mem_iUnion.mpr ⟨j,⟨i,rfl⟩⟩))
  have hSum : sumListVal rows = fun x => F x * G x := by
    funext x
    rw [sumListVal_eq_sum]
    dsimp [rows]
    rw [List.map_ofFn,List.sum_ofFn]
    calc
      _ = ∑ j : Fin L, F x * (((G x).testBit j.val).toNat * 2^j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        cases e : (G x).testBit j.val <;> simp [row,pcxMulRow,e,Nat.mul_comm]
      _ = _ := by rw [← Finset.mul_sum,hdecode]
  rw [hSum] at second
  exact relaxB (seq2B first second) le_rfl Set.subset_union_right (by simp [rows]; ring_nf; omega)

lemma iteB {N : Nat} {A : Set (Sig N)} {c a b : Sig N}
    (hc : c ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Build A {fun x => if c x then a x else b x} 4 := by
  let s1 : Sig N := fun x => !(c x)
  let s2 : Sig N := fun x => c x && a x
  let s3 : Sig N := fun x => s1 x && b x
  let s4 : Sig N := fun x => s2 x || s3 x
  have h1 : Build A {s1} 1 := notB hc
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hc) (Or.inl ha)
  have h3 : Build ((A ∪ {s1}) ∪ {s2}) {s3} 1 := andB (Or.inl (Or.inr rfl)) (Or.inl (Or.inl hb))
  have h4 : Build (((A ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 := orB (Or.inl (Or.inr rfl)) (Or.inr rfl)
  have heq : s4 = fun x => if c x then a x else b x := by
    funext x; simp only [s4, s3, s2, s1]; cases c x <;> cases a x <;> cases b x <;> rfl
  rw [← heq]
  exact relaxB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) h4)
    le_rfl Set.subset_union_right (by omega)

lemma testBit_two_pow_sub_one_sub {L b j : Nat} (hb : b < 2 ^ L) (hj : j < L) :
    (2 ^ L - 1 - b).testBit j = !(b.testBit j) := by
  have h1 : (2 ^ L - 1 - b) + b = 2 ^ L - 1 := by omega
  have hpow : ∀ n k, (2 ^ n - 1).testBit k = decide (k < n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [testBit_eq_decide_div_mod]
      cases k with
      | zero =>
        simp only [Nat.pow_zero, Nat.div_one, Nat.zero_lt_succ, decide_true]
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hm : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
        simp [hm]
      | succ k =>
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hdiv : (2 ^ (n + 1) - 1) / 2 ^ (k + 1) = (2 ^ n - 1) / 2 ^ k := by
          rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
          congr 1; omega
        rw [hdiv, ← testBit_eq_decide_div_mod, ih k]; simp
  have hcarry : ∀ k ≤ L, rippleCarry (2 ^ L - 1 - b) b k = false := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hkL : k < L := by omega
      have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b k).2
      rw [h1, hpow L k, decide_eq_true hkL, ih (by omega)] at hspec
      unfold rippleCarry
      rw [ih (by omega)]
      simp only [faSum, Bool.xor_false] at hspec
      cases hA : (2 ^ L - 1 - b).testBit k <;> cases hB : b.testBit k <;>
        simp [hA, hB, faCarry] at hspec ⊢
  have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b j).2
  rw [h1, hpow L j, decide_eq_true hj, hcarry j (by omega)] at hspec
  simp only [faSum, Bool.xor_false] at hspec
  cases hA : (2 ^ L - 1 - b).testBit j <;> cases hB : b.testBit j <;>
    simp [hA, hB] at hspec ⊢

lemma subModB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hGlt : ∀ x, G x < 2 ^ L) :
    Build A (Set.range (bitsOf L (fun x => (F x + (2 ^ L - 1 - G x + 1)) % 2 ^ L))) (19 * L) := by
  let compG : (Fin N → Bool) → Nat := fun x => 2 ^ L - 1 - G x
  let oneF : (Fin N → Bool) → Nat := fun _ => 1
  have hcomp : Build A (Set.range (bitsOf L compG)) L := by
    have h1 := finSigB (A := A) (fun j : Fin L => fun x => !(bitsOf L G j x)) 1
      (fun j => notB (hG j))
    refine relaxB h1 le_rfl ?_ (by omega)
    rintro _ ⟨j, rfl⟩
    have heq : bitsOf L compG j = fun x => !(bitsOf L G j x) := by
      funext x; exact testBit_two_pow_sub_one_sub (hGlt x) j.isLt
    rw [heq]; exact Or.inr ⟨j, rfl⟩
  have hone : ∀ j : Fin L, bitsOf L oneF j ∈ A := by
    intro j
    by_cases hj : j.val = 0
    · have heq : bitsOf L oneF j = fun _ => true := by funext x; simp [bitsOf, oneF, hj]
      rw [heq]; exact htrue
    · have heq : bitsOf L oneF j = fun _ => false := by
        funext x; simp only [bitsOf, oneF]
        exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
          (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
      rw [heq]; exact hfalse
  have hadd1 : Build (A ∪ Set.range (bitsOf L compG))
      (Set.range (bitsOf L (fun x => compG x + oneF x))) (9 * L) :=
    sumTwoB L compG oneF (Or.inl hfalse) (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (hone j))
  have hadd2 : Build (A ∪ (Set.range (bitsOf L compG) ∪
      Set.range (bitsOf L (fun x => compG x + oneF x))))
      (Set.range (bitsOf L (fun x => F x + (compG x + oneF x)))) (9 * L) :=
    sumTwoB L F (fun x => compG x + oneF x) (Or.inl hfalse)
      (fun j => Or.inl (hF j)) (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
  refine relaxB (seq2B (seqB hcomp hadd1) hadd2) le_rfl ?_ (by omega)
  rintro _ ⟨j, rfl⟩
  have heq : bitsOf L (fun x => (F x + (2 ^ L - 1 - G x + 1)) % 2 ^ L) j =
      bitsOf L (fun x => F x + (compG x + oneF x)) j := by
    funext x; unfold bitsOf compG oneF; dsimp only
    rw [Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and]
  rw [heq]; exact Or.inr ⟨j, rfl⟩

def ltAux (a b : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => (!(a.testBit j) && b.testBit j) || ((!(a.testBit j) || b.testBit j) && ltAux a b j)

lemma ltAux_spec (a b : Nat) : ∀ j : Nat, ltAux a b j = decide (a % 2 ^ j < b % 2 ^ j) := by
  intro j
  induction j with
  | zero => simp [ltAux, Nat.mod_one]
  | succ j ih =>
    unfold ltAux
    rw [ih, mod_two_pow_succ_eq a j, mod_two_pow_succ_eq b j]
    have ha : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    cases a.testBit j
    · cases b.testBit j
      · simp
      · have hlt : a % 2 ^ j < b % 2 ^ j + 2 ^ j := by omega
        simp [hlt]
    · cases b.testBit j
      · have hge : ¬(a % 2 ^ j + 2 ^ j < b % 2 ^ j) := by omega
        simp [hge]
      · simp

lemma ltB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hFlt : ∀ x, F x < 2 ^ L) (hGlt : ∀ x, G x < 2 ^ L) :
    Build A {fun x => decide (F x < G x)} (5 * L) := by
  have haux : ∀ j ≤ L, Build A {fun x => ltAux (F x) (G x) j} (5 * j) := by
    intro j
    induction j with
    | zero =>
      intro _; simpa [ltAux] using idleB (Set.singleton_subset_iff.mpr hfalse)
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      set aS : Sig N := bitsOf L F ⟨j, hj⟩
      set bS : Sig N := bitsOf L G ⟨j, hj⟩
      set pS : Sig N := fun x => ltAux (F x) (G x) j
      have haA : aS ∈ A := hF ⟨j, hj⟩
      have hbA : bS ∈ A := hG ⟨j, hj⟩
      let na : Sig N := fun x => !(aS x)
      let s1 : Sig N := fun x => na x && bS x
      let s2 : Sig N := fun x => na x || bS x
      let s3 : Sig N := fun x => s2 x && pS x
      let s4 : Sig N := fun x => s1 x || s3 x
      have g1 : Build (A ∪ {pS}) {na} 1 := notB (Or.inl haA)
      have g2 : Build ((A ∪ {pS}) ∪ {na}) {s1} 1 := andB (Or.inr rfl) (Or.inl (Or.inl hbA))
      have g3 : Build (((A ∪ {pS}) ∪ {na}) ∪ {s1}) {s2} 1 :=
        orB (Or.inl (Or.inr rfl)) (Or.inl (Or.inl (Or.inl hbA)))
      have g4 : Build ((((A ∪ {pS}) ∪ {na}) ∪ {s1}) ∪ {s2}) {s3} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
      have g5 : Build (((((A ∪ {pS}) ∪ {na}) ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 :=
        orB (Or.inl (Or.inl (Or.inr rfl))) (Or.inr rfl)
      have hstep : Build (A ∪ {pS}) {s4} 5 :=
        relaxB (transB (transB (transB (transB (extB g1) (extB g2)) (extB g3)) (extB g4)) g5)
          le_rfl Set.subset_union_right (by omega)
      have heq : s4 = fun x => ltAux (F x) (G x) (j + 1) := by
        funext x; rfl
      rw [heq] at hstep
      exact relaxB (seq2B hprev hstep) le_rfl Set.subset_union_right (by omega)
  have hL := haux L le_rfl
  have heq : (fun x => ltAux (F x) (G x) L) = fun x => decide (F x < G x) := by
    funext x
    rw [ltAux_spec, Nat.mod_eq_of_lt (hFlt x), Nat.mod_eq_of_lt (hGlt x)]
  rw [heq] at hL
  exact hL

private theorem pcxRestoringStep (p g : ℕ) (bit : Bool) (hg : 0 < g) :
    let trial := 2*(p%g)+bit.toNat
    let newQ := 2*(p/g)+(decide (g≤trial)).toNat
    let newR := if trial<g then trial else trial-g
    newQ = (2*p+bit.toNat)/g ∧ newR = (2*p+bit.toNat)%g := by
  dsimp only
  have split := Nat.mod_add_div p g
  have rlt := Nat.mod_lt p hg
  have bitlt : bit.toNat ≤ 1 := by cases bit <;> decide
  have sum : 2*p+bit.toNat = (2*(p%g)+bit.toNat) + g*(2*(p/g)) := by
    calc
      _ = 2*(p%g + g*(p/g))+bit.toNat := by rw [split]
      _ = _ := by ring
  rw [sum, Nat.add_mul_div_left _ _ hg, Nat.add_mul_mod_self_left]
  by_cases h : 2*(p%g)+bit.toNat < g
  · simp [h,Nat.not_le_of_lt h,Nat.mod_eq_of_lt h,Nat.div_eq_of_lt h]
  · have lo := Nat.le_of_not_gt h
    have hi : 2*(p%g)+bit.toNat < g*2 := by omega
    have quot : (2*(p%g)+bit.toNat)/g = 1 := Nat.div_eq_of_lt_le (by simpa using lo) (by omega)
    have rem := Nat.mod_add_div (2*(p%g)+bit.toNat) g
    rw [quot,Nat.mul_one] at rem
    simp [h,lo,quot]
    omega
private lemma pcxBitWires {N W : ℕ} {A : Set (Sig N)} {hi : (Fin N → Bool) → ℕ} {lo : Sig N}
    (hhi : ∀ i : Fin W, bitsOf W hi i ∈ A) (hlo : lo ∈ A) (i : Fin W) :
    bitsOf W (fun x => Nat.bit (lo x) (hi x)) i ∈ A := by
  obtain ⟨j,hj⟩ := i
  cases j with
  | zero =>
    have e : bitsOf W (fun x => Nat.bit (lo x) (hi x)) ⟨0,hj⟩ = lo := funext fun x => Nat.testBit_bit_zero _ _
    exact e.symm ▸ hlo
  | succ j =>
    let t : Fin W := ⟨j,by omega⟩
    have e : bitsOf W (fun x => Nat.bit (lo x) (hi x)) ⟨j+1,hj⟩ = bitsOf W hi t := funext fun x => Nat.testBit_bit_succ j _ _
    exact e.symm ▸ hhi t

private lemma pcxRestoreBuild {N W : ℕ} {A : Set (Sig N)} (P G : (Fin N → Bool) → ℕ)
    (digit : Sig N) (hh0 : (fun _ => false) ∈ A) (hh1 : (fun _ => true) ∈ A)
    (hQ : ∀ i : Fin W, bitsOf W (fun x => P x/G x) i ∈ A)
    (hR : ∀ i : Fin W, bitsOf W (fun x => P x%G x) i ∈ A)
    (hG : ∀ i : Fin W, bitsOf W G i ∈ A) (hd : digit ∈ A)
    (positive : ∀ x, 0 < G x) (width : ∀ x, 2*G x ≤ 2^W) :
    let next := fun x => Nat.bit (digit x) (P x)
    Build A (Set.range (bitsOf W (fun x => next x/G x)) ∪
             Set.range (bitsOf W (fun x => next x%G x))) (28*W+1) := by
  dsimp only
  let trial := fun x => Nat.bit (digit x) (P x%G x)
  let lt : Sig N := fun x => decide (trial x < G x)
  let take : Sig N := fun x => !(lt x)
  let diff := fun x => (trial x + (2^W-1-G x+1)) % 2^W
  have ht : ∀ i : Fin W, bitsOf W trial i ∈ A := pcxBitWires hR hd
  have trialWidth (x) : trial x < 2^W := by
    have rb := Nat.mod_lt (P x) (positive x)
    have bnd : (digit x).toNat ≤ 1 := by cases digit x <;> decide
    have := width x
    dsimp [trial]
    rw [Nat.bit_val]
    omega
  have gw (x) : G x < 2^W := by have := width x; have := positive x; omega
  have hlt : Build A {lt} (5*W) := ltB W trial G hh0 ht hG trialWidth gw
  have htake : Build (A ∪ {lt}) {take} 1 := notB (Or.inr rfl)
  have hdiff : Build A (Set.range (bitsOf W diff)) (19*W) := subModB W trial G hh0 hh1 ht hG gw
  have initial := unionB (seqB hlt htake) hdiff
  let src := A ∪ (({lt} ∪ {take}) ∪ Set.range (bitsOf W diff))
  have qr (x) : Nat.bit (take x) (P x/G x) = (Nat.bit (digit x) (P x))/G x := by
    have h := (pcxRestoringStep (P x) (G x) (digit x) (positive x)).1
    have eq : take x = decide (G x ≤ trial x) := by
      by_cases v : trial x < G x
      · simp [take,lt,v,Nat.not_le_of_lt v]
      · simp [take,lt,v,Nat.le_of_not_gt v]
    rw [Nat.bit_val,eq]
    simpa [trial,Nat.bit_val] using h
  have rr (x) : (if lt x then trial x else diff x) = (Nat.bit (digit x) (P x))%G x := by
    have h := (pcxRestoringStep (P x) (G x) (digit x) (positive x)).2
    rw [Nat.bit_val]
    change (if lt x then trial x else diff x) = _
    rw [←h, ←Nat.bit_val]
    by_cases hh : trial x < G x
    · simp [lt,hh,trial]
    · have w := gw x
      have tw := trialWidth x
      have eq : trial x+(2^W-1-G x+1)=(trial x-G x)+2^W := by omega
      have dw : trial x-G x < 2^W := by omega
      simp [lt,hh,diff,eq,Nat.mod_eq_of_lt dw,trial] at *
  let R := fun x => (Nat.bit (digit x) (P x))%G x
  have output (i : Fin W) : Build src {bitsOf W R i} 4 := by
    have h : Build src {fun x => if lt x then bitsOf W trial i x else bitsOf W diff i x} 4 :=
      iteB (Or.inr (Or.inl (Or.inl rfl))) (Or.inl (ht i)) (Or.inr (Or.inr ⟨i,rfl⟩))
    convert h using 4
    simp only [bitsOf,R,←rr]
    split <;> rfl
  have oq : ∀ i : Fin W, bitsOf W (fun x => Nat.bit (digit x) (P x)/G x) i ∈ src := by
    intro i
    simp_rw [←qr]
    exact pcxBitWires (fun j => Or.inl (hQ j)) (Or.inr (Or.inl (Or.inr rfl))) i
  have oqr := finSigB (bitsOf W R) 4 output
  apply relaxB (seqB initial oqr) le_rfl _ (by omega)
  rintro a (⟨i,rfl⟩|⟨i,rfl⟩)
  · rcases oq i with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨i,rfl⟩)
private lemma pcxDivideBuild {N W : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hF : ∀ i : Fin L, bitsOf L F i ∈ A) (small : ∀ x, F x < 2^L)
    (hG : ∀ i : Fin W, bitsOf W G i ∈ A) (positive : ∀ x, 0 < G x)
    (width : ∀ x, 2*G x ≤ 2^W) :
    Build A (Set.range (bitsOf W (fun x => F x/G x)) ∪
      Set.range (bitsOf W (fun x => F x%G x))) (L*(28*W+1)) := by
  induction L generalizing F with
  | zero =>
    rw [Nat.zero_mul]
    have fzero : F = fun _ => 0 := funext fun x => by have := small x; simpa using this
    rw [fzero]
    apply idleB
    rintro a (⟨i,rfl⟩ | ⟨i,rfl⟩) <;>
      convert h0 using 1 <;> funext x <;> simp [bitsOf]
  | succ L ih =>
    let half := fun x => F x >>> 1
    let digit : Sig N := fun x => (F x).testBit 0
    have dec (x) : Nat.bit (digit x) (half x) = F x := Nat.bit_testBit_zero_shiftRight_one _
    have hh (i : Fin L) : bitsOf L half i ∈ A := by
      have e : bitsOf L half i = bitsOf (L+1) F ⟨i.val+1,by omega⟩ := by
        funext x
        simp [bitsOf,half,Nat.testBit_shiftRight,Nat.add_comm]
      rw [e]
      exact hF _
    have hs (x) : half x < 2^L := by
      dsimp [half]
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa [pow_succ] using small x
    have before := ih half hh hs
    have present : digit ∈ A := hF ⟨0,by omega⟩
    have step := pcxRestoreBuild (A := A ∪ (Set.range (bitsOf W (fun x => half x/G x)) ∪
      Set.range (bitsOf W (fun x => half x%G x)))) half G digit (Or.inl h0) (Or.inl h1)
      (fun i => Or.inr (Or.inl ⟨i,rfl⟩)) (fun i => Or.inr (Or.inr ⟨i,rfl⟩))
      (fun i => Or.inl (hG i)) (Or.inl present) positive width
    dsimp only at step
    simp_rw [dec] at step
    exact relaxB (seq2B before step) le_rfl Set.subset_union_right (by nlinarith)

private lemma pcxSqrtDigit (n : ℕ) :
    Nat.bit (decide ((2*(n/4).sqrt+1)^2≤n)) (n/4).sqrt = n.sqrt := by
  let a := (n/4).sqrt
  have low := Nat.sqrt_le' (n/4)
  have hi := Nat.lt_succ_sqrt' (n/4)
  change a^2 ≤ n/4 at low
  change n/4 < (a+1)^2 at hi
  have cut : 4*(n/4) ≤ n ∧ n < 4*(n/4+1) := by omega
  change Nat.bit (decide ((2*a+1)^2 ≤ n)) a = n.sqrt
  apply Nat.eq_sqrt'.mpr
  by_cases h : (2*a+1)^2≤n
  · simp only [h,decide_true,Nat.bit_val,Bool.toNat_true]
    exact ⟨True.intro,by nlinarith⟩
  · simp only [h,decide_false,Nat.bit_val,Bool.toNat_false,add_zero]
    exact ⟨by nlinarith,by omega⟩

private lemma pcxSqrtB {N W : ℕ} {A : Set (Sig N)} (L : ℕ) (F : (Fin N → Bool) → ℕ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A)
    (hF : ∀ i : Fin W, bitsOf W F i∈A) (width : 2*L ≤ W) (small : ∀ x, F x < 2^(2*L)) :
    Build A (Set.range (bitsOf W (fun x=>(F x).sqrt))) (L*(10*W^2+5*W+1)) := by
  induction L generalizing F with
  | zero =>
    rw [Nat.zero_mul]
    apply idleB
    rintro _ ⟨i,rfl⟩
    have fzero : F = fun _ => 0 := funext fun x => by have := small x; simpa using this
    rw [fzero]
    convert h0 using 1 <;> funext x <;> simp [bitsOf]
  | succ L ih =>
    let half := fun x => F x / 4
    let root := fun x => (half x).sqrt
    let candidate := fun x => Nat.bit true (root x)
    let sq := fun x => candidate x * candidate x
    let cmp : Sig N := fun x => decide (F x < sq x)
    have fw (x) : F x < 2^W :=
      (small x).trans_le (Nat.pow_le_pow_right (by decide) width)
    have sh (i : Fin W) : bitsOf W half i ∈ A := by
      have shift (x) : bitsOf W half i x = (F x).testBit (i.val+2) := by
        change ((F x)/(2^2)).testBit i.val = _
        rw [Nat.testBit_div_two_pow]
      by_cases lo : i.val+2<W
      · have eq : bitsOf W half i = bitsOf W F ⟨i.val+2,lo⟩ := funext shift
        exact eq.symm ▸ hF _
      · have eq : bitsOf W half i = fun _=>false := funext fun x =>
          (shift x).trans (Nat.testBit_eq_false_of_lt ((fw x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
        exact eq.symm ▸ h0
    have hs (x) : half x < 2^(2*L) := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr
      have e : 2^(2*(L+1)) = 2^(2*L)*4 := by rw [Nat.mul_succ,pow_add];rfl
      simpa only [e] using small x
    have prev := ih half sh (by omega) hs
    let S := A ∪ Set.range (bitsOf W root)
    have cs : ∀ i : Fin W, bitsOf W candidate i ∈ S :=
      pcxBitWires (fun i=>Or.inr ⟨i,rfl⟩) (Or.inl h1)
    have cw (x) : candidate x < 2^(L+1) := by
      have sr : root x < 2^L := Nat.sqrt_lt'.mpr (by simpa [←pow_mul,Nat.mul_comm] using hs x)
      dsimp only [candidate]
      rw [Nat.bit_val,pow_succ]
      simp only [Bool.toNat_true];omega
    have sw (x) : sq x < 2^W := by
      calc
        _ < 2^(L+1)*2^(L+1) := Nat.mul_self_lt_mul_self (cw x)
        _ = 2^(2*(L+1)) := by rw [←pow_add]; congr 1;omega
        _ ≤ _ := Nat.pow_le_pow_right (by decide) width
    have candWidth (x) : candidate x < 2^W :=
      (cw x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have mul : Build S (Set.range (bitsOf W sq)) (10*W^2) :=
      pcxMulBuild W candidate candidate (Or.inl h0) cs cs
        (fun x=>decode _ W (candWidth x))
    have compare : Build (S ∪ Set.range (bitsOf W sq)) {cmp} (5*W) :=
      ltB W F sq (Or.inl (Or.inl h0)) (fun i=>Or.inl (Or.inl (hF i))) (fun i=>Or.inr ⟨i,rfl⟩) fw sw
    let keep : Sig N := fun x=>!(cmp x)
    have stage := seq2B mul compare
    have negGate : Build (S ∪ {cmp}) {keep} 1 := notB (Or.inr rfl)
    have done := seq2B stage negGate
    have rootEq (x) : Nat.bit (keep x) (root x) = (F x).sqrt := by
      have same : keep x = decide (sq x≤F x) := by
        by_cases b : F x < sq x
        · simp [keep,cmp,b,Nat.not_le_of_lt b]
        · simp [keep,cmp,b,Nat.le_of_not_gt b]
      rw [same]
      simpa [sq,candidate,Nat.bit_val,root,half,pow_two] using pcxSqrtDigit (F x)
    have step := relaxB done le_rfl (B' := Set.range (bitsOf W (fun x=>(F x).sqrt))) (by
      rintro _ ⟨i,rfl⟩
      simp_rw [←rootEq]
      exact pcxBitWires (fun j=>Or.inl (Or.inr ⟨j,rfl⟩)) (Or.inr rfl) i) le_rfl
    exact relaxB (seq2B prev step) le_rfl Set.subset_union_right (by nlinarith)

private def pcxWord (W : ℕ) (z : ℤ) : ℕ := (z : ZMod (2^W)).val

private lemma pcxWord_bound (W : ℕ) (z : ℤ) : pcxWord W z < 2^W := ZMod.val_lt _

private lemma pcxWord_small (W : ℕ) (z : ℤ) (h0 : 0 ≤ z) (h1 : z < (2:ℤ)^W) :
    pcxWord W z = z.toNat := by
  have v : (pcxWord W z : ℤ) = z := by
    rw [pcxWord,ZMod.val_intCast,Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]
  omega

private lemma pcxWord_plus (W : ℕ) (a b : ℤ) :
    pcxWord W (a+b) = (pcxWord W a + pcxWord W b) % 2^W := by
  simp [pcxWord, ZMod.val_add]

private lemma pcxWord_times (W : ℕ) (a b : ℤ) :
    pcxWord W (a*b) = (pcxWord W a * pcxWord W b) % 2^W := by
  simp [pcxWord, ZMod.val_mul]

private lemma pcxWord_minus (W : ℕ) (a b : ℤ) :
    pcxWord W (a-b) = (pcxWord W a + (2^W-1-pcxWord W b+1)) % 2^W := by
  have hb := pcxWord_bound W b
  rw [show 2^W-1-pcxWord W b+1 = 2^W-pcxWord W b by omega]
  rw [←ZMod.val_natCast]
  apply congrArg ZMod.val
  rw [Nat.cast_add,Nat.cast_sub hb.le]
  simp [pcxWord]
  ring

private lemma pcxExactDivideNat (z d r H : ℤ) (nonzero : d ≠ 0) (divisible : z=d*r)
    (lo : 0 ≤ H+r) :
    (z*d + H*(d*d)).toNat / (d*d).toNat = (H+r).toNat := by
  have pos : 0 < d*d := mul_self_pos.mpr nonzero
  have pos' : 0 < (d*d).toNat := by omega
  have fac : z*d + H*(d*d) = d*d*(H+r) := by rw [divisible];ring
  rw [fac,Int.toNat_mul pos.le lo,Nat.mul_div_cancel_left _ pos']
private def pcxSet {N : ℕ} (W : ℕ) (F : (Fin N → Bool) → ℤ) :=
  Set.range (bitsOf W (fun x => pcxWord W (F x)))

private lemma pcxModRange {N : ℕ} (W : ℕ) (F : (Fin N → Bool) → ℕ) :
    Set.range (bitsOf W (fun x => F x % 2^W)) = Set.range (bitsOf W F) := by
  apply congrArg Set.range
  funext i x
  simp [bitsOf,Nat.testBit_mod_two_pow,i.isLt]

private lemma pcxSumWordB {N : ℕ} {A : Set (Sig N)} (W : ℕ) (F G : (Fin N → Bool) → ℤ)
    (h0 : (fun _=>false)∈A) (hf : pcxSet W F ⊆ A) (hg : pcxSet W G ⊆ A) :
    Build A (pcxSet W (fun x=>F x+G x)) (9*W) := by
  unfold pcxSet
  simp_rw [pcxWord_plus]
  rw [pcxModRange]
  exact sumTwoB W _ _ h0 (fun i=>hf ⟨i,rfl⟩) (fun i=>hg ⟨i,rfl⟩)

private lemma pcxSubWordB {N : ℕ} {A : Set (Sig N)} (W : ℕ) (F G : (Fin N → Bool) → ℤ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) (hf : pcxSet W F ⊆ A) (hg : pcxSet W G ⊆ A) :
    Build A (pcxSet W (fun x=>F x-G x)) (19*W) := by
  unfold pcxSet
  simp_rw [pcxWord_minus]
  exact subModB W _ _ h0 h1 (fun i=>hf ⟨i,rfl⟩) (fun i=>hg ⟨i,rfl⟩) (fun x=>pcxWord_bound W _)

private lemma pcxMulWordB {N : ℕ} {A : Set (Sig N)} (W : ℕ) (F G : (Fin N → Bool) → ℤ)
    (h0 : (fun _=>false)∈A) (hf : pcxSet W F ⊆ A) (hg : pcxSet W G ⊆ A) :
    Build A (pcxSet W (fun x=>F x*G x)) (10*W^2) := by
  unfold pcxSet
  simp_rw [pcxWord_times]
  rw [pcxModRange]
  exact pcxMulBuild W _ _ h0 (fun i=>hf ⟨i,rfl⟩) (fun i=>hg ⟨i,rfl⟩)
    (fun x=> decode _ W (pcxWord_bound W (G x)))
private lemma pcxConstWires {N : ℕ} {A : Set (Sig N)} (W : ℕ) (h : ℤ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) :
    pcxSet W (fun _ => h) ⊆ A := by
  rintro _ ⟨i,rfl⟩
  change (fun _ : Fin N → Bool => (pcxWord W h).testBit i.val) ∈ A
  cases (pcxWord W h).testBit i.val
  · exact h0
  · exact h1

private lemma pcxDivWordB {N : ℕ} {A : Set (Sig N)} (W : ℕ)
    (Z D R : (Fin N → Bool) → ℤ) (H : ℤ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A)
    (hz : pcxSet W Z ⊆ A) (hd : pcxSet W D ⊆ A)
    (nz : ∀ x, D x ≠ 0) (divisible : ∀ x, Z x = D x * R x)
    (rlo : ∀ x, 0 ≤ H+R x) (rhi : ∀ x, H+R x < (2:ℤ)^W)
    (gWidth : ∀ x, 2*(D x*D x) ≤ (2:ℤ)^W)
    (fWidth : ∀ x, Z x*D x+H*(D x*D x) < (2:ℤ)^W) :
    Build A (pcxSet W R) (58*W^2+29*W) := by
  let G := fun x => D x * D x
  let T := fun x => Z x * D x
  let B := fun x => H * G x
  let F := fun x => T x + B x
  let Q := fun x => H + R x
  have gp (x) : 0 < G x := mul_self_pos.mpr (nz x)
  have gw (x) : G x < (2:ℤ)^W := by have := gp x; have := gWidth x; change 2*G x ≤ _ at this; omega
  have fp (x) : 0 ≤ F x := by
    have e : F x = G x * Q x := by dsimp [F,T,B,G,Q]; rw [divisible x]; ring
    rw [e]; exact mul_nonneg (gp x).le (rlo x)
  have const := pcxConstWires W H h0 h1
  have g := pcxMulWordB W D D h0 hd hd
  have t := pcxMulWordB W Z D h0 hz hd
  have b : Build (A ∪ pcxSet W G) (pcxSet W B) (10*W^2) :=
    pcxMulWordB W (fun _ => H) G (Or.inl h0) (fun a ha=>Or.inl (const ha)) Set.subset_union_right
  have prep := unionB t (seqB g b)
  let PP := pcxSet W T ∪ (pcxSet W G ∪ pcxSet W B)
  have f : Build (A ∪ PP) (pcxSet W F) (9*W) :=
    pcxSumWordB W T B (Or.inl h0) (fun a ha=>Or.inr (Or.inl ha)) (fun a ha=>Or.inr (Or.inr (Or.inr ha)))
  have all := seqB prep f
  let src := A ∪ (PP ∪ pcxSet W F)
  have fs (i : Fin W) : bitsOf W (fun x => (F x).toNat) i ∈ src := by
    have e : bitsOf W (fun x => (F x).toNat) i = bitsOf W (fun x => pcxWord W (F x)) i := by
      funext x; rw [bitsOf, bitsOf,pcxWord_small W _ (fp x) (fWidth x)]
    exact e ▸ (show bitsOf W (fun x => pcxWord W (F x)) i ∈ src from Or.inr (Or.inr ⟨i,rfl⟩))
  have gs (i : Fin W) : bitsOf W (fun x => (G x).toNat) i ∈ src := by
    have e : bitsOf W (fun x => (G x).toNat) i = bitsOf W (fun x => pcxWord W (G x)) i := by
      funext x; rw [bitsOf,bitsOf,pcxWord_small W _ (gp x).le (gw x)]
    exact e ▸ (show bitsOf W (fun x => pcxWord W (G x)) i ∈ src from Or.inr (Or.inl (Or.inr (Or.inl ⟨i,rfl⟩))))
  have fw (x) : (F x).toNat < 2^W := by
    have hx : ((F x).toNat:ℤ) < (2:ℤ)^W := by rw [Int.toNat_of_nonneg (fp x)]; exact fWidth x
    exact_mod_cast hx
  have gn (x) : 2*(G x).toNat ≤ 2^W := by
    have hx : 2*((G x).toNat:ℤ) ≤ (2:ℤ)^W := by rw [Int.toNat_of_nonneg (gp x).le]; exact gWidth x
    exact_mod_cast hx
  have qa := pcxDivideBuild (A:=src) W (fun x=>(F x).toNat) (fun x=>(G x).toNat) (Or.inl h0) (Or.inl h1)
    fs fw gs (fun x=>by have := gp x; omega) gn
  have q := relaxB qa le_rfl (B' := pcxSet W Q) (by
    rintro a ⟨i,rfl⟩
    apply Or.inr; apply Or.inl; refine ⟨i,?_⟩
    funext x
    change ((F x).toNat/(G x).toNat).testBit i.val = (pcxWord W (Q x)).testBit i.val
    rw [pcxWord_small W _ (rlo x) (rhi x)]
    exact congrArg (fun k : ℕ => k.testBit i.val) (pcxExactDivideNat _ _ _ H (nz x) (divisible x) (rlo x))) le_rfl
  have calcAll := seq2B all q
  have finish : Build (A ∪ pcxSet W Q) (pcxSet W (fun x => Q x-H)) (19*W) :=
    pcxSubWordB W Q (fun _ => H) (Or.inl h0) (Or.inl h1) Set.subset_union_right (fun a ha=>Or.inl (const ha))
  have eq : (fun x => Q x-H) = R := by funext x; dsimp [Q]; ring
  rw [eq] at finish
  exact relaxB (seq2B calcAll finish) le_rfl Set.subset_union_right (by nlinarith)

end Pcx446Arithmetic

namespace DartFaces
open Function

def face {l : ℕ} (f : Fin l → Fin l) (d : Fin l) :=
  (Finset.range l).image (fun j => f^[j] d)

theorem mem_face {l : ℕ} (f : Fin l → Fin l) (inj : Injective f) (d x : Fin l) :
    x ∈ face f d ↔ ∃ i : ℕ, f^[i] d = x := by
  constructor
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    exact ⟨j,hj⟩
  · rintro ⟨i, rfl⟩
    have hp := minimalPeriod_pos_of_mem_periodicPts (inj.mem_periodicPts d)
    have hn : minimalPeriod f d ≤ l := by simpa using (minimalPeriod_le_card (f:=f) (x:=d))
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr ((Nat.mod_lt _ hp).trans_le hn),
      iterate_mod_minimalPeriod_eq⟩

theorem face_step {l : ℕ} (f : Fin l → Fin l) (inj : Injective f) (d : Fin l) :
    face f (f d) = face f d := by
  ext x
  rw [mem_face f inj, mem_face f inj]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i+1, by rw [Function.iterate_succ_apply]⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨k, hk, hper⟩ := inj.mem_periodicPts d
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hh : f^[a] (f d) = d := by simpa only [Function.iterate_succ_apply] using hper.eq
    exact ⟨i+a, by rw [Function.iterate_add_apply, hh]⟩

def Ends {V E : Type*} (u v : E → V) (a b : V) : Prop :=
  ∃ e, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)

theorem dualConnected {V E F : Type*} (src dst : E → V)
    (rot rev : Equiv.Perm E) (col : E → F)
    (faceStep : ∀ d, col (rot (rev d)) = col d)
    (source : Function.Injective (fun d => (src d,dst d)))
    (swap : ∀ d, src (rev d) = dst d ∧ dst (rev d) = src d)
    (localCycle : ∀ d e, src d = src e → ∃ j : ℕ, (rot ^ j) d = e)
    (primal : ∀ a b, Relation.ReflTransGen (Ends src dst) a b)
    (rep : Function.Surjective col) :
    ∀ f g, Relation.ReflTransGen (Ends col (fun d => col (rev d))) f g := by
  let R := Ends col (fun d => col (rev d))
  have invol (a : E) : rev (rev a) = a := source (Prod.ext
    ((swap (rev a)).1.trans (swap a).2) ((swap (rev a)).2.trans (swap a).1))
  have across (d : E) : Relation.ReflTransGen R (col d) (col (rev d)) :=
    .single ⟨d, Or.inl ⟨rfl,rfl⟩⟩
  have around (d : E) : Relation.ReflTransGen R (col d) (col (rot d)) := by
    have h := faceStep (rev d)
    rw [invol] at h
    rw [h]
    exact across d
  have arounds (d : E) (j : ℕ) : Relation.ReflTransGen R (col d) (col ((rot ^ j) d)) := by
    induction j with
    | zero => simpa using (Relation.ReflTransGen.refl (r:=R) (a:=col d))
    | succ j ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.trans (around _)
  have star (d e : E) (h : src d = src e) : Relation.ReflTransGen R (col d) (col e) := by
    obtain ⟨j,rfl⟩ := localCycle d e h
    exact arounds _ _
  intro x y
  obtain ⟨d,rfl⟩ := rep x
  obtain ⟨e,rfl⟩ := rep y
  have go (b : V) (p : Relation.ReflTransGen (Ends src dst) (src d) b) :
      ∀ k, src k = b → Relation.ReflTransGen R (col d) (col k) := by
    induction p with
    | refl => exact fun k hk => star _ _ hk.symm
    | tail _ he ih =>
      obtain ⟨j,h|h⟩ := he
      · intro k hk
        exact ((ih j h.1).trans (across j)).trans (star _ _ ((swap j).1.trans (h.2.trans hk.symm)))
      · intro k hk
        exact ((ih (rev j) ((swap j).1.trans h.2)).trans (across (rev j))).trans
          (star _ _ (by rw [invol]; exact h.1.trans hk.symm))
  exact go _ (primal _ _) _ rfl

theorem faces_have_zero_boundary {V D F R : Type*} [Fintype D] [DecidableEq V] [AddCommGroup R]
    (src : D → V) (rot rev : Equiv.Perm D) (face : D → F) (c : F → R)
    (rotSrc : ∀ d, src (rot d) = src d)
    (around : ∀ d, face (rot d) = face (rev d)) (v : V) :
    ∑ d : D, (if src d = v then c (face d) - c (face (rev d)) else 0) = 0 := by
  let f (d : D) := if src d = v then c (face d) else 0
  have h (d : D) : (if src d = v then c (face d) - c (face (rev d)) else 0) =
      f d - f (rot d) := by
    simp only [f,rotSrc,around]
    by_cases h : src d = v <;> simp [h]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp rot f, sub_self]

theorem safe_path_color {V D R : Type*} (src dst : D → V)
    (rot rev : Equiv.Perm D) (paint : D → R) (safe : V → Prop)
    (rotSrc : ∀ d, src (rot d) = src d)
    (revSrc : ∀ d, src (rev d) = dst d)
    (around : ∀ d, paint (rot d) = paint (rev d))
    (localCycle : ∀ d e, src d = src e → ∃ j : ℕ, (rot ^ j) d = e)
    (neutral : ∀ d, safe (src d) → paint d = paint (rev d))
    (d e : D) (start : safe (src d))
    (path : Relation.ReflTransGen (fun u v => safe u ∧ safe v ∧ Ends src dst u v) (src d) (src e)) :
    paint d = paint e := by
  have kept (x : D) (i : ℕ) : src ((rot ^ i) x) = src x := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ',Equiv.Perm.mul_apply,rotSrc,ih]
  have star (p q : D) (sp : safe (src p)) (hpq : src p = src q) : paint p = paint q := by
    obtain ⟨j,rfl⟩ := localCycle p q hpq
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,around]
      exact (ih (kept p j).symm).trans (neutral _ (by rwa [kept]))
  have go (y : V) (walk : Relation.ReflTransGen (fun u v => safe u ∧ safe v ∧ Ends src dst u v) (src d) y) :
      ∀ q, src q = y → paint d = paint q := by
    induction walk with
    | refl => exact fun q hq => star _ _ start hq.symm
    | tail _ edge ih =>
      obtain ⟨sx,sy,j,h|h⟩ := edge
      · intro q hq
        have js := revSrc j
        exact ((ih j h.1).trans (neutral _ (h.1 ▸ sx))).trans
          (star _ _ (js.trans h.2 ▸ sy) (js.trans (h.2.trans hq.symm)))
      · intro q hq
        have js := revSrc j
        exact ((ih (rev j) (js.trans h.2)).trans (neutral j (h.1 ▸ sy)).symm).trans
          (star _ _ (h.1 ▸ sy) (h.1.trans hq.symm))
  exact go _ path _ rfl
end DartFaces

namespace DartEdges

abbrev Preferred {l : ℕ} (rev : Equiv.Perm (Fin l)) := {d : Fin l // d < rev d}

def split {l : ℕ} (rev : Equiv.Perm (Fin l))
    (inv : ∀ d, rev (rev d) = d) (apart : ∀ d, rev d ≠ d) :
    Fin l ≃ (Preferred rev ⊕ Preferred rev) where
  toFun d := if h : d < rev d then Sum.inl ⟨d,h⟩
    else Sum.inr ⟨rev d, by rw [inv]; exact lt_of_le_of_ne (le_of_not_gt h) (apart d)⟩
  invFun := Sum.elim Subtype.val (fun d => rev d)
  left_inv d := by by_cases h : d < rev d <;> simp [h,inv]
  right_inv x := by
    cases x with
    | inl d => simp [d.property]
    | inr d =>
      have h : ¬rev d < rev (rev d) := by rw [inv]; exact not_lt_of_gt d.property
      simp [h, inv, not_lt_of_gt d.property]

theorem card_darts {l : ℕ} (rev : Equiv.Perm (Fin l))
    (inv : ∀ d, rev (rev d) = d) (apart : ∀ d, rev d ≠ d) :
    l = 2 * Fintype.card (Preferred rev) := by
  simpa [two_mul] using Fintype.card_congr (split rev inv apart)

theorem sum_darts {l : ℕ} {R : Type*} [AddCommMonoid R] (rev : Equiv.Perm (Fin l))
    (inv : ∀ d, rev (rev d) = d) (apart : ∀ d, rev d ≠ d) (f : Fin l → R) :
    ∑ d, f d = ∑ e : Preferred rev, (f e.val + f (rev e.val)) := by
  have h := Equiv.sum_comp (split rev inv apart).symm f
  rw [← h, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rfl

end DartEdges

namespace FiniteRotation

def endMatrix {K V E : Type*} [Field K] [DecidableEq V]
    (u v : E → V) : Matrix E V K :=
  fun e x => (if u e = x then 1 else 0) - (if v e = x then 1 else 0)

theorem endMatrix_mul {K V E : Type*} [Field K] [Fintype V] [DecidableEq V]
    (u v : E → V) (f : V → K) (e : E) :
    (endMatrix u v).mulVecLin f e = f (u e) - f (v e) := by
  classical
  change ∑ x, (((if u e = x then 1 else 0) - (if v e = x then 1 else 0)) * f x) = _
  simp_rw [sub_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_sub_distrib]
  simp

theorem endMatrix_transpose_mul {K V E : Type*} [Field K] [Fintype E] [DecidableEq V]
    (u v : E → V) (f : E → K) (x : V) :
    (endMatrix u v).transpose.mulVecLin f x =
      ∑ e, ((if u e = x then f e else 0) - (if v e = x then f e else 0)) := by
  change ∑ e, (((if u e = x then 1 else 0) - (if v e = x then 1 else 0)) * f e) = _
  simp_rw [sub_mul,ite_mul,one_mul,zero_mul]
end FiniteRotation

namespace FiniteRotation

def Ends {V E : Type*} (u v : E → V) (a b : V) : Prop :=
  ∃ e, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)

theorem gradientKernel {K V E : Type*} [Field K] [Fintype V] [Nonempty V]
    (u v : E → V) (g : (V → K) →ₗ[K] (E → K))
    (hgrad : ∀ c e, g c e = c (u e) - c (v e))
    (conn : ∀ a b, Relation.ReflTransGen (Ends u v) a b) :
    Module.finrank K (LinearMap.ker g) = 1 := by
  classical
  let base : V := Classical.choice inferInstance
  have constant (c : LinearMap.ker g) (a : V) : c.val a = c.val base := by
    have hz : g c.val = 0 := c.property
    induction conn base a with
    | refl => rfl
    | tail hab hbc ih =>
      obtain ⟨e, h | h⟩ := hbc
      all_goals
        have hrel := congrFun hz e
        rw [hgrad] at hrel
        have eq : c.val (u e) = c.val (v e) := sub_eq_zero.mp hrel
        rw [h.1,h.2] at eq
        exact eq ▸ ih
  let iso : (LinearMap.ker g) ≃ₗ[K] K := {
    toFun := fun c => c.val base
    invFun := fun b => ⟨fun _ => b, by
      apply LinearMap.mem_ker.mpr
      funext e
      simp [hgrad]⟩
    left_inv := fun c => Subtype.ext (funext fun a => (constant c a).symm)
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  simpa using iso.finrank_eq

theorem faceColoringExists {K V E F : Type*} [Field K] [Fintype V] [Fintype E]
    [Fintype F] [Nonempty V] [Nonempty F]
    (P : Matrix E V K) (D : Matrix E F K) (u v : E → V) (l r : E → F)
    (primal : ∀ c e, P.mulVecLin c e = c (u e) - c (v e))
    (dual : ∀ c e, D.mulVecLin c e = c (l e) - c (r e))
    (connP : ∀ a b, Relation.ReflTransGen (Ends u v) a b)
    (connD : ∀ a b, Relation.ReflTransGen (Ends l r) a b)
    (chain : LinearMap.range D.mulVecLin ≤ LinearMap.ker P.transpose.mulVecLin)
    (euler : Fintype.card V + Fintype.card F = Fintype.card E + 2) :
    ∀ x, P.transpose.mulVecLin x = 0 → ∃ c, D.mulVecLin c = x := by
  classical
  have pk := gradientKernel u v P.mulVecLin primal connP
  have dk := gradientKernel l r D.mulVecLin dual connD
  have pr := P.mulVecLin.finrank_range_add_finrank_ker
  have dr := D.mulVecLin.finrank_range_add_finrank_ker
  have tr := P.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, pk] at pr
  rw [Module.finrank_pi, dk] at dr
  rw [Module.finrank_pi] at tr
  have rk : Module.finrank K (LinearMap.range P.transpose.mulVecLin) =
      Module.finrank K (LinearMap.range P.mulVecLin) := Matrix.rank_transpose P
  have eq : LinearMap.range D.mulVecLin = LinearMap.ker P.transpose.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq chain (by omega)
  intro x hx
  change x ∈ LinearMap.range D.mulVecLin
  rwa [eq]
end FiniteRotation

namespace FiniteRotation

theorem interval_const {K : Type*} (f : ℕ → K) (a b : ℕ) (h : a ≤ b)
    (step : ∀ i, a ≤ i → i < b → f i = f (i+1)) : f a = f b := by
  induction b, h using Nat.le_induction with
  | base => rfl
  | succ i hi ih =>
    exact (ih (fun j hj hj' => step _ hj (by omega))).trans (step _ hi (by omega))

theorem opposite_spoke_faces {t : ℕ} {K : Type*} (paint : Fin t → K)
    (a b c d : Fin t) (ab : a < b) (bc : b < c) (cd : c < d)
    (step : ∀ (i j : Fin t), j.val = (i.val+1) % t →
      (paint i ≠ paint j ↔ i = a ∨ i = c)) : paint b ≠ paint d := by
  let f (i : ℕ) := if h : i < t then paint ⟨i,h⟩ else paint a
  have read (i : Fin t) : f i = paint i := by simp [f]
  have status (i : ℕ) (hi : i+1<t) :
      f i ≠ f (i+1) ↔ i = a.val ∨ i = c.val := by
    have h : i < t := by omega
    simpa [f,h,hi,Fin.ext_iff] using step ⟨i,h⟩ ⟨i+1,hi⟩ (Nat.mod_eq_of_lt hi).symm
  have bc' : f b = f c :=
    interval_const f b c (Nat.le_of_lt bc) (fun i h₁ h₂ => by
      have h₃ : i + 1 < t := by have := c.isLt; omega
      exact not_ne_iff.mp (fun hbad => by
        have := (status i h₃).mp hbad
        have h₄ : a.val < b.val := ab
        omega))
  have jump : f c ≠ f (c.val+1) := (status _ (by have := d.isLt; have : c.val<d.val := cd; omega)).mpr (Or.inr rfl)
  have cd' : f (c.val+1) = f d :=
    interval_const f _ _ cd (fun i h₁ h₂ => by
      have h₃ : i + 1 < t := by have := d.isLt; omega
      exact not_ne_iff.mp (fun hbad => by
        have := (status i h₃).mp hbad
        have h₄ : a.val < b.val := ab
        have h₅ : b.val < c.val := bc
        omega))
  rw [←read b,←read d,bc',←cd']
  exact jump
end FiniteRotation
namespace FiniteRotation

theorem prefEnds {n : ℕ} {V : Type*} (rev : Equiv.Perm (Fin n)) (s t : Fin n → V)
    (inv : ∀ d, rev (rev d) = d) (apart : ∀ d, rev d ≠ d)
    (st : ∀ d, s (rev d) = t d) (ts : ∀ d, t (rev d) = s d)
    {a b : V} (h : DartFaces.Ends s t a b) :
    Ends (fun d : DartEdges.Preferred rev => s d.val) (fun d => t d.val) a b := by
  obtain ⟨d,hd⟩ := h
  by_cases lt : d < rev d
  · exact ⟨⟨d,lt⟩,hd⟩
  · have hl : rev d < rev (rev d) := by rw [inv]; exact lt_of_le_of_ne (le_of_not_gt lt) (apart d)
    refine ⟨⟨rev d,hl⟩,?_⟩
    change ((s (rev d)=a ∧ t (rev d)=b) ∨ (s (rev d)=b ∧ t (rev d)=a))
    rw [st,ts]
    tauto

theorem divergence_darts {K V : Type*} [Field K] [DecidableEq V] {n : ℕ}
    (src dst : Fin n → V) (rev : Equiv.Perm (Fin n)) (inv : ∀ d, rev (rev d)=d)
    (apart : ∀ d, rev d ≠ d) (revSrc : ∀ d, src (rev d) = dst d)
    (x : Fin n → K) (anti : ∀ d, x (rev d) = -x d) (v : V) :
    (endMatrix (fun d : DartEdges.Preferred rev => src d.val) (fun d => dst d.val)).transpose.mulVecLin
      (fun d => x d.val) v = ∑ d, if src d = v then x d else 0 := by
  rw [endMatrix_transpose_mul,DartEdges.sum_darts rev inv apart]
  apply Finset.sum_congr rfl
  intro d _
  simp only [revSrc,anti]
  by_cases h : dst d.val = v <;> simp [h,sub_eq_add_neg]

theorem sphericalFaceGradient {K V F : Type*} [Field K] [Fintype V] [Fintype F]
    [DecidableEq V] [DecidableEq F] [Nonempty V] [Nonempty F] {n : ℕ}
    (src dst : Fin n → V) (rot rev : Equiv.Perm (Fin n)) (face : Fin n → F)
    (dartInj : Function.Injective (fun d => (src d, dst d)))
    (noLoop : ∀ d, src d ≠ dst d)
    (swap : ∀ d, src (rev d) = dst d ∧ dst (rev d)=src d)
    (around : ∀ d, src (rot d) = src d)
    (localCycle : ∀ d e, src d = src e → ∃ j : ℕ, (rot ^ j) d = e)
    (step : ∀ d, face (rot (rev d)) = face d)
    (faceRep : Function.Surjective face)
    (primal : ∀ a b, Relation.ReflTransGen (DartFaces.Ends src dst) a b)
    (euler : 2 * Fintype.card V + 2 * Fintype.card F = 4+n)
    (x : Fin n → K) (anti : ∀ d, x (rev d) = -x d)
    (balanced : ∀ v, ∑ d, (if src d = v then x d else 0) = 0) :
    ∃ c : F → K, ∀ d, x d = c (face d) - c (face (rev d)) := by
  classical
  have inv (d) : rev (rev d) = d := dartInj (Prod.ext
    ((swap (rev d)).1.trans (swap d).2) ((swap (rev d)).2.trans (swap d).1))
  have apart (d) : rev d ≠ d := fun he => noLoop d (by simpa only [he] using (swap d).1)
  have step' (d) : face (rot d) = face (rev d) := by simpa only [inv] using step (rev d)
  have dual := DartFaces.dualConnected src dst rot rev face step dartInj swap localCycle primal faceRep
  let E := DartEdges.Preferred rev
  let S (e : E) := src e.val
  let T (e : E) := dst e.val
  let L (e : E) := face e.val
  let R (e : E) := face (rev e.val)
  let P : Matrix E V K := endMatrix S T
  let D : Matrix E F K := endMatrix L R
  have cp (u v) : Relation.ReflTransGen (Ends S T) u v :=
    Relation.ReflTransGen.mono (fun _ _ h => prefEnds rev src dst inv apart (fun d => (swap d).1) (fun d => (swap d).2) h) u v (primal u v)
  have cd (u v) : Relation.ReflTransGen (Ends L R) u v :=
    Relation.ReflTransGen.mono (fun _ _ h => prefEnds rev face (fun d => face (rev d)) inv apart (fun _ => rfl) (fun d => by rw [inv]) h) u v (dual u v)
  have sub : LinearMap.range D.mulVecLin ≤ LinearMap.ker P.transpose.mulVecLin := by
    rintro z ⟨c,rfl⟩
    change P.transpose.mulVecLin (D.mulVecLin c) = 0
    funext v
    let h (d : Fin n) := c (face d) - c (face (rev d))
    have ant (d) : h (rev d) = -h d := by simp [h,inv]
    change (endMatrix S T).transpose.mulVecLin ((endMatrix L R).mulVecLin c) v = 0
    have funEq : (endMatrix L R).mulVecLin c = fun d => h d.val := funext (endMatrix_mul L R c)
    rw [funEq, divergence_darts src dst rev inv apart (fun d => (swap d).1) h ant]
    exact DartFaces.faces_have_zero_boundary src rot rev face c around step' v
  have opKernel : P.transpose.mulVecLin (fun d => x d.val) = 0 := by
    funext v
    exact (divergence_darts src dst rev inv apart (fun d => (swap d).1) x anti v).trans (balanced v)
  have eul : Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
    have := DartEdges.card_darts rev inv apart
    change Fintype.card V + Fintype.card F = Fintype.card (DartEdges.Preferred rev) + 2
    omega
  obtain ⟨c,hc⟩ := faceColoringExists P D S T L R (endMatrix_mul S T) (endMatrix_mul L R)
    cp cd sub eul _ opKernel
  have atPref (e : E) : x e.val = c (face e.val) - c (face (rev e.val)) :=
    (congrFun hc e).symm.trans (endMatrix_mul L R c e)
  refine ⟨c,fun d => ?_⟩
  by_cases h : d < rev d
  · exact atPref ⟨d,h⟩
  · have hl : rev d < rev (rev d) := by rw [inv]; exact lt_of_le_of_ne (le_of_not_gt h) (apart d)
    have op := atPref ⟨rev d,hl⟩
    change x (rev d) = c (face (rev d)) - c (face (rev (rev d))) at op
    rw [anti,inv] at op
    exact neg_injective (by simpa using op)
end FiniteRotation

namespace FiniteRotation
def atom {n : ℕ} (rev : Equiv.Perm (Fin n)) (e k : Fin n) : ZMod 2 :=
  (if k=e then 1 else 0) - (if k=rev e then 1 else 0)

def flowDiv {V : Type*} [DecidableEq V] {n : ℕ} (src : Fin n → V) (g : Fin n → ZMod 2) (v : V) :
    ZMod 2 := ∑ d, if src d = v then g d else 0

def atSite {V : Type*} [DecidableEq V] (v x : V) : ZMod 2 := if v=x then 1 else 0

theorem atom_rev {n} (rev : Equiv.Perm (Fin n)) (inv : ∀ k, rev (rev k) = k)
    (e k : Fin n) : atom rev e (rev k) = -atom rev e k := by
  have flip : rev k = e ↔ k = rev e :=
    ⟨fun h => (inv k).symm.trans (congrArg rev h), fun h => h ▸ inv _⟩
  simp [atom,flip]

theorem div_add {V : Type*} [DecidableEq V] {n : ℕ} (src : Fin n → V) (f g : Fin n → ZMod 2) (v) :
    flowDiv src (f+g) v = flowDiv src f v + flowDiv src g v := by
  unfold flowDiv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : src d=v <;> simp [h]

theorem atom_div {V : Type*} [DecidableEq V] {n : ℕ} (src dst : Fin n → V)
    (rev : Equiv.Perm (Fin n)) (hs : ∀ e, src (rev e)=dst e) (e k) :
    flowDiv src (atom rev e) k = atSite (src e) k - atSite (dst e) k := by
  have h (d : Fin n) :
      (if src d=k then atom rev e d else 0) =
      (if d=e then atSite (src e) k else 0) - (if d=rev e then atSite (dst e) k else 0) := by
    have eh := hs e
    by_cases he : d=e <;> by_cases hr : d=rev e <;>
      simp_all [atom,atSite,hs] <;> (try split) <;> (try simp_all)
    all_goals rw [←hs e, he]; simp_all
  simp only [flowDiv,h,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem walk_flow {V : Type*} [DecidableEq V] {n : ℕ} (src dst : Fin n → V) (rev : Equiv.Perm (Fin n))
    (inv : ∀ k, rev (rev k) = k) (hs : ∀ k, src (rev k)=dst k) (inside : V → Prop)
    (a b : V)
    (path : Relation.ReflTransGen (fun x y => inside x ∧ inside y ∧ ∃ d, src d=x ∧ dst d=y) a b) :
    ∃ g : Fin n → ZMod 2, (∀ d, g (rev d) = -g d) ∧
      (∀ d, ¬inside (src d) → g d = 0) ∧
      (∀ v, flowDiv src g v = atSite a v - atSite b v) := by
  induction path with
  | refl => exact ⟨0, by simp, by simp, by simp [flowDiv]⟩
  | tail _ edge ih =>
    obtain ⟨g,ag,supp,bound⟩ := ih
    obtain ⟨xin,yin,d,sd,dd⟩ := edge
    refine ⟨g+atom rev d, ?_, ?_, ?_⟩
    · intro e; simp only [Pi.add_apply, ag, atom_rev rev inv]; abel
    · intro e he
      have hd : e ≠ d := fun h => he (h ▸ sd ▸ xin)
      have hr : e ≠ rev d := fun h => he (by rw [h,hs,dd]; exact yin)
      simp [supp e he,atom,hd,hr]
    · intro v
      rw [div_add,bound,atom_div src dst rev hs,sd,dd]
      abel
end FiniteRotation
namespace FiniteRotation

theorem disjointAlternatingImpossible {n t : ℕ} {V F : Type*} [DecidableEq V]
    (src dst : Fin n → V) (rot rev : Equiv.Perm (Fin n))
    (inv : ∀ k, rev (rev k)=k) (rs : ∀ k, src (rev k)=dst k) (rd : ∀ k, dst (rev k)=src k)
    (rr : ∀ k, src (rot k)=src k)
    (localCycle : ∀ k j, src k = src j → ∃ h : ℕ, (rot^h) k=j)
    (face : Fin n → F) (around : ∀ k, face (rot k)=face (rev k))
    (span : ∀ x : Fin n → ZMod 2, (∀ k, x (rev k) = -x k) → (∀ v, flowDiv src x v=0) →
      ∃ h : F → ZMod 2, ∀ k, x k=h (face k)-h (face (rev k)))
    (hub : V) (sp : Fin t → Fin n) (inj : Function.Injective sp)
    (spSrc : ∀ i, src (sp i) = hub) (dist : ∀ i, dst (sp i) ≠ hub)
    (cyc : ∀ i j : Fin t, j.val = (i.val+1)%t → rot (sp i)=sp j)
    (a b c d : Fin t) (ab : a < b) (bc : b < c) (cd : c < d)
    (inside safe : V → Prop) (notHub : ¬inside hub) (notSafeHub : ¬safe hub)
    (disjoint : ∀ v, safe v → ¬inside v)
    (ain : inside (dst (sp a))) (cin : inside (dst (sp c)))
    (bsafe : safe (dst (sp b)))
    (firstPath : Relation.ReflTransGen (fun u v => inside u ∧ inside v ∧ ∃ k, src k=u ∧ dst k=v)
       (dst (sp a)) (dst (sp c)))
    (secondPath : Relation.ReflTransGen (fun u v => safe u ∧ safe v ∧ DartFaces.Ends src dst u v)
       (dst (sp b)) (dst (sp d))) : False := by
  obtain ⟨g,ag,sg,bg⟩ := walk_flow src dst rev inv rs inside _ _ firstPath
  let A := sp a
  let C := sp c
  let f := atom rev A + g + atom rev (rev C)
  have af (k) : f (rev k) = -f k := by
    simp only [f,Pi.add_apply,atom_rev rev inv,ag]; abel
  have bf (v) : flowDiv src f v=0 := by
    simp only [f,div_add,atom_div src dst rev rs,bg,rs,rd,A,C,spSrc]; abel
  obtain ⟨h,hf⟩ := span f af bf
  let paint (k) := h (face k)
  have jump (k) : paint k ≠ paint (rev k) ↔ f k ≠ 0 := by
    rw [hf]; exact sub_ne_zero.symm
  have calcSp (i) : f (sp i) = (if i=a then 1 else 0) - (if i=c then 1 else 0) := by
    have neOpp (j) : sp i ≠ rev (sp j) := fun h => dist j (by rw [←rs,←h,spSrc])
    simp [f,A,C,atom,sg (sp i) (by rwa [spSrc]), neOpp, inv,inj.eq_iff]
    split <;> split <;> decide
  have ac : a ≠ c := ne_of_lt (lt_trans ab bc)
  have nz (i) : f (sp i) ≠ 0 ↔ i = a ∨ i = c := by
    rw [calcSp]
    by_cases ha : i=a <;> by_cases hc : i=c <;> simp_all
  have steps (i j : Fin t) (next : j.val = (i.val+1)%t) :
      paint (sp i) ≠ paint (sp j) ↔ i = a ∨ i = c := by
    have eq : paint (sp j) = paint (rev (sp i)) := congrArg h ((congrArg face (cyc _ _ next)).symm.trans (around _))
    rw [eq,jump,nz]
  have sep := opposite_spoke_faces (fun i => paint (sp i)) a b c d ab bc cd steps
  have simple (k) (s : safe (src k)) : f k = 0 := by
    have nn (i) : k ≠ sp i := fun he => notSafeHub (by simpa [he,spSrc] using s)
    have nA : k ≠ rev A := fun he => disjoint _ s (by simpa only [A,he,rs] using ain)
    have nC : k ≠ rev C := fun he => disjoint _ s (by simpa only [C,he,rs] using cin)
    simp [f,sg k (disjoint _ s),atom,nn,nA,nC,inv,A,C] at *
  have neutral (k) (s : safe (src k)) : paint k=paint (rev k) :=
    not_ne_iff.mp (fun hbad => (jump k).mp hbad (simple k s))
  have q := DartFaces.safe_path_color src dst rot rev paint safe rr rs
    (fun k => congrArg h (around k)) localCycle neutral (rev (sp b)) (rev (sp d))
    (by rwa [rs]) (by simpa only [rs] using secondPath)
  have uncut (i) (h₁ : i ≠ a) (h₂ : i ≠ c) : paint (sp i) = paint (rev (sp i)) :=
    not_ne_iff.mp (fun bad => ((nz i).mp ((jump _).mp bad)).elim h₁ h₂)
  exact sep ((uncut b (ne_of_gt ab) (ne_of_lt bc)).trans (q.trans (uncut d
    (ne_of_gt ((lt_trans ab bc).trans cd)) (ne_of_gt cd)).symm))
end FiniteRotation
namespace FiniteRotation

theorem unitRotationNoCross {n m t l : ℕ} (u v : Fin m → Fin n) (pin : Fin t ↪ Fin n)
    (noLoop : ∀ e, u e ≠ v e)
    (connected : ∀ i j, Relation.ReflTransGen (fun x y => ∃ e, (u e=x ∧ v e=y) ∨ (u e=y ∧ v e=x)) i j)
    (src dst : Fin l → Option (Fin n)) (rot rev : Equiv.Perm (Fin l)) (sp : Fin t → Fin l)
    (uniq : Function.Injective (fun d => (src d,dst d)))
    (support : ∀ x y : Option (Fin n),
      x.elim (y.elim false (fun i => decide (∃ j, pin j=i)))
        (fun i => y.elim (decide (∃ j,pin j=i))
          (fun j => decide (∃ e : Fin m, (u e=i ∧ v e=j) ∨ (u e=j ∧ v e=i)))) = true ↔
      ∃ d, src d=x ∧ dst d=y)
    (revrot : ∀ d, src (rev d)=dst d ∧ dst (rev d)=src d ∧ src (rot d)=src d)
    (localCycle : ∀ d e, src d=src e → ∃ j : ℕ, (rot^j) d=e)
    (spoke : ∀ i, src (sp i)=none ∧ dst (sp i)=some (pin i) ∧
      ∀ j : Fin t, j.val=(i.val+1)%t → rot (sp i)=sp j)
    (euler : 2*(n+1) + 2*((Finset.univ : Finset (Fin l)).image
      (fun d => (Finset.range l).image (fun j => (fun k => rot (rev k))^[j] d))).card = 4+l)
    (a b c d : Fin t) (ab : a<b) (bc : b<c) (cd : c<d)
    (red blue : Option (Fin n) → Prop) (rh : ¬red none) (bh : ¬blue none)
    (disj : ∀ z, blue z → ¬ red z)
    (redA : red (some (pin a))) (redC : red (some (pin c))) (blueB : blue (some (pin b)))
    (redPath : Relation.ReflTransGen (fun i j => red i ∧ red j ∧ ∃ k, src k=i ∧ dst k=j)
        (some (pin a)) (some (pin c)))
    (bluePath : Relation.ReflTransGen (fun i j => blue i ∧ blue j ∧ DartFaces.Ends src dst i j)
        (some (pin b)) (some (pin d))) : False := by
  classical
  let walk (k : Fin l) := rot (rev k)
  let faces := (Finset.univ : Finset (Fin l)).image (DartFaces.face walk)
  let F := {s // s ∈ faces}
  let label (k : Fin l) : F := ⟨_,Finset.mem_image.mpr ⟨k,Finset.mem_univ k,rfl⟩⟩
  letI : Nonempty F := ⟨label (sp a)⟩
  have rep : Function.Surjective label := by
    intro y; obtain ⟨k,_,hk⟩ := Finset.mem_image.mp y.property
    exact ⟨k,Subtype.ext hk⟩
  have step (k) : label (rot (rev k)) = label k := Subtype.ext
    (DartFaces.face_step walk (rot.injective.comp rev.injective) k)
  have swap (k) := And.intro (revrot k).1 (revrot k).2.1
  have inv (k) : rev (rev k)=k := uniq (Prod.ext ((swap (rev k)).1.trans (swap k).2)
    ((swap (rev k)).2.trans (swap k).1))
  have around (k) : label (rot k)=label (rev k) := by simpa only [inv] using step (rev k)
  have loopless (k) : src k ≠ dst k := by
    intro eq
    have hk := (support (src k) (src k)).mpr ⟨k,rfl,eq.symm⟩
    cases e : src k with
    | none => simp [e] at hk
    | some x =>
      simp [e] at hk
      obtain ⟨i,hu,hv⟩ := hk
      exact noLoop i (hu.trans hv.symm)
  have primal0 (i j) : Relation.ReflTransGen (DartFaces.Ends src dst) (some i) (some j) := by
    induction connected i j with
    | refl => exact .refl
    | tail _ h ih =>
      apply ih.tail
      obtain ⟨k,hk⟩ := (support (some _) (some _)).mp (show (decide (∃ e, (u e=_ ∧ v e=_) ∨ (u e=_ ∧ v e=_)))=true from decide_eq_true h)
      exact ⟨k,Or.inl hk⟩
  have primal (x y) : Relation.ReflTransGen (DartFaces.Ends src dst) x y := by
    cases x with
    | none =>
      cases y with
      | none => exact .refl
      | some j =>
        exact (Relation.ReflTransGen.single (show DartFaces.Ends src dst none (some (pin a)) from
          ⟨sp a,Or.inl ⟨(spoke a).1,(spoke a).2.1⟩⟩)).trans (primal0 _ _)
    | some i =>
      cases y with
      | none => exact (primal0 i (pin a)).tail ⟨sp a,Or.inr ⟨(spoke a).1,(spoke a).2.1⟩⟩
      | some j => exact primal0 _ _
  have en : 2*Fintype.card (Option (Fin n)) + 2*Fintype.card F = 4+l := by
    have sz : Fintype.card F = faces.card := Fintype.card_coe _
    rw [sz, Fintype.card_option, Fintype.card_fin]
    exact euler
  have span := sphericalFaceGradient (K:=ZMod 2) src dst rot rev label uniq loopless swap
    (fun k => (revrot k).2.2) localCycle step rep primal en
  have spInj : Function.Injective sp := by
    intro i j h
    apply pin.injective
    exact Option.some.inj (((spoke i).2.1.symm.trans (congrArg dst h)).trans (spoke j).2.1)
  apply disjointAlternatingImpossible src dst rot rev inv (fun d => (revrot d).1)
    (fun d => (revrot d).2.1) (fun d => (revrot d).2.2) localCycle label around span
    none sp spInj (fun i => (spoke i).1) (fun i => by rw [(spoke i).2.1]; simp)
    (fun i => (spoke i).2.2) a b c d ab bc cd red blue rh bh disj
  · rwa [(spoke _).2.1]
  · rwa [(spoke _).2.1]
  · rwa [(spoke _).2.1]
  · simpa only [(spoke a).2.1,(spoke c).2.1] using redPath
  · simpa only [(spoke b).2.1,(spoke d).2.1] using bluePath
end FiniteRotation

namespace BoundarySwitch
open Finset

def Noncrossing {n : ℕ} {C : Type*} (B : Fin n → C) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → B a = B c → B b = B d → B a = B b

def fiber {n : ℕ} {C : Type*} [DecidableEq C] (B : Fin n → C) (k : C) : Finset (Fin n) :=
  univ.filter (fun i => B i = k)

theorem evenGap {n : ℕ} {C : Type*} [DecidableEq C] (B : Fin n → C)
    (nc : Noncrossing B) (even : ∀ k, 2 ∣ (fiber B k).card)
    (a c : Fin n) (ac : a < c) (same : B a = B c)
    (adj : ∀ i, a < i → i < c → B i ≠ B a) :
    2 ∣ c.val - a.val - 1 := by
  let s := Ioo a c
  have allin (b x : Fin n) (bmem : b ∈ s) (h : B b = B x) : x ∈ s := by
    obtain ⟨ab,bc⟩ := mem_Ioo.mp bmem
    have ne := adj b ab bc
    apply mem_Ioo.mpr
    constructor
    · rcases lt_trichotomy x a with xa|xa|xa
      · exact False.elim (ne (h.trans (nc x a b c xa ab bc h.symm same)))
      · exact False.elim (ne (xa ▸ h))
      · exact xa
    · rcases lt_trichotomy x c with xc|xc|xc
      · exact xc
      · exact False.elim (ne ((xc ▸ h).trans same.symm))
      · exact False.elim (ne (nc a b c x ab bc xc same h).symm)
  have hcard : 2 ∣ s.card := by
    rw [card_eq_sum_card_image B s]
    apply dvd_sum
    intro k hk
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hk
    have eq : s.filter (fun x => B x = B b) = fiber B (B b) := by
      ext x
      simp only [fiber,mem_filter,mem_univ,true_and]
      exact ⟨And.right, fun e => ⟨allin b x hb e.symm,e⟩⟩
    rw [eq]
    apply even
  simpa only [s,Fin.card_Ioo] using hcard

theorem adjacentSign {n : ℕ} {C : Type*} [DecidableEq C] (B : Fin n → C)
    (nc : Noncrossing B) (even : ∀ k, 2 ∣ (fiber B k).card) (k : C)
    {m : ℕ} (sz : (fiber B k).card = m)
    (i j : Fin m) (consec : j.val=i.val+1) :
    (-1 : ℤ)^((fiber B k).orderEmbOfFin sz j).val =
      -(-1 : ℤ)^((fiber B k).orderEmbOfFin sz i).val := by
  let S := fiber B k
  let e : Fin m ≃o S := S.orderIsoOfFin sz
  let a : Fin n := (e i).val
  let c : Fin n := (e j).val
  have color (l : Fin m) : B (e l).val = k := (mem_filter.mp (e l).property).2
  have ac : a<c := by
    have ij : i<j := by change i.val<j.val; omega
    exact e.strictMono ij
  have hgap : 2 ∣ c.val-a.val-1 := evenGap B nc even a c ac ((color i).trans (color j).symm) (by
    intro p ap pc h
    have hp : p ∈ S := mem_filter.mpr ⟨mem_univ _,h.trans (color i)⟩
    let l := e.symm ⟨p,hp⟩
    have hx : e l = ⟨p,hp⟩ := e.apply_symm_apply _
    have il : i<l := e.lt_iff_lt.mp (by rw [hx]; exact ap)
    have lj : l<j := e.lt_iff_lt.mp (by rw [hx]; exact pc)
    have il' : i.val<l.val := il
    have lj' : l.val<j.val := lj
    omega)
  obtain ⟨h,hh⟩ := hgap
  change (-1 : ℤ)^c.val = -(-1 : ℤ)^a.val
  have aclt : a.val < c.val := ac
  have eq : c.val = a.val + 2*h + 1 := by omega
  rw [eq,pow_succ,pow_add,pow_mul]
  simp

theorem evenSequence {m : ℕ} (v : Fin (m*2) → ℤ)
    (h : ∀ i j : Fin (m*2), j.val=i.val+1 → v j = -v i) : ∑ i, v i = 0 := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m:=m) (n:=2)) v,Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fin.sum_univ_two]
  have e := h (finProdFinEquiv (i,(0 : Fin 2))) (finProdFinEquiv (i,(1 : Fin 2))) (by
    change 1+2*i.val = 0+2*i.val+1
    omega)
  rw [e,add_neg_cancel]

theorem blockSign {n : ℕ} {C : Type*} [DecidableEq C] (B : Fin n → C)
    (nc : Noncrossing B) (even : ∀ k, 2 ∣ (fiber B k).card) (k : C) :
    ∑ i ∈ fiber B k, (-1 : ℤ)^i.val = 0 := by
  obtain ⟨m,hm⟩ := even k
  let S := fiber B k
  have sz : S.card=m*2 := by simpa [Nat.mul_comm] using hm
  let e : Fin (m*2) ≃o S := S.orderIsoOfFin sz
  rw [← Finset.sum_coe_sort]
  rw [← Equiv.sum_comp e.toEquiv]
  apply evenSequence
  intro i j h
  exact adjacentSign B nc even k sz i j h

theorem componentCancellation {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] (B : Fin n → C)
    (nc : Noncrossing B) (even : ∀ k, 2 ∣ (fiber B k).card)
    (w : Fin n → ℤ) (constant : ∀ i j, B i=B j → w i=w j) :
    ∑ i, (-1 : ℤ)^i.val * w i = 0 := by
  rw [←sum_fiberwise_of_maps_to (t:=univ) (g:=B) (fun _ _ => mem_univ _)]
  apply sum_eq_zero
  intro k _
  change (∑ i ∈ fiber B k, (-1 : ℤ)^i.val * w i) = 0
  by_cases ne : (fiber B k).Nonempty
  · obtain ⟨i,hi⟩ := ne
    calc
      _ = ∑ j ∈ fiber B k, (-1 : ℤ)^j.val * w i := by
        apply sum_congr rfl
        intro j hj
        rw [constant j i ((mem_filter.mp hj).2.trans (mem_filter.mp hi).2.symm)]
      _ = 0 := by rw [←sum_mul,blockSign B nc even,zero_mul]
  · simp [not_nonempty_iff_eq_empty.mp ne]

def translateFiber {A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (grad : A →+ H) (a b : H) (c : A) (move : grad c=b-a) :
    {x // grad x = a} ≃ {x // grad x = b} where
  toFun := fun x => ⟨x.val+c, by rw [map_add,x.property,move]; abel⟩
  invFun := fun y => ⟨y.val-c, by rw [map_sub,y.property,move]; abel⟩
  left_inv := fun x => Subtype.ext (add_sub_cancel_right _ _)
  right_inv := fun y => Subtype.ext (sub_add_cancel _ _)

theorem inRangeOfWalk {V A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (g : A →+ H) (source : V → H) (link : V → V → Prop)
    (edge : ∀ i j, link i j → ∃ x, g x = source j - source i) (i j : V)
    (h : Relation.ReflTransGen link i j) : ∃ x, g x = source j - source i := by
  induction h with
  | refl => exact ⟨0,by simp⟩
  | tail hp hnext ih =>
    obtain ⟨x,hx⟩ := ih
    obtain ⟨y,hy⟩ := edge _ _ hnext
    exact ⟨x+y,by rw [map_add,hx,hy]; abel⟩

theorem fixedPairSwitch {n : ℕ} [NeZero n] {C A H : Type*} [Fintype C] [DecidableEq C]
    [AddCommGroup A] [Fintype A] [AddCommGroup H] [DecidableEq H]
    (grad : A →+ H) (source : Fin n → H) (z : H) (B : Fin n → C)
    (nc : Noncrossing B) (even : ∀ k, 2 ∣ (fiber B k).card)
    (paths : ∀ i j, B i=B j → ∃ p, grad p = source j - source i) :
    (Fintype.card {x // grad x=z} : ℤ) =
      ∑ j ∈ univ.erase 0, -(-1 : ℤ)^j.val *
       Fintype.card {x // grad x=z + source j - source 0} := by
  let w (j : Fin n) : ℤ := Fintype.card {x // grad x=z+source j-source 0}
  have const (i j : Fin n) (same : B i=B j) : w i=w j := by
    obtain ⟨p,hp⟩ := paths i j same
    exact congrArg (fun k : ℕ => (k : ℤ)) (Fintype.card_congr
      (translateFiber grad _ _ p (by rw [hp]; abel)))
  have cancel := componentCancellation B nc even w const
  have split := add_sum_erase univ (fun i : Fin n => (-1 : ℤ)^i.val * w i) (mem_univ (0 : Fin n))
  rw [cancel] at split
  change _ = ∑ j ∈ univ.erase 0, -(-1 : ℤ)^j.val * w j
  simp_rw [neg_mul,Finset.sum_neg_distrib]
  have first : w 0 = Fintype.card {x // grad x=z} := by simp [w]
  simp only [Fin.val_zero,pow_zero,one_mul,first] at split
  omega

end BoundarySwitch
namespace BoundarySwitch
open Finset

def coefficient {A H : Type*} [Fintype A] [DecidableEq H] (grad : A → H) (W : A → ℤ) (z : H) :=
  ∑ x, if grad x=z then W x else 0

def paired {A H : Type*} [Fintype A] [AddCommGroup A] [DecidableEq H]
    (grad : A → H) (W : A → ℤ) (u : A) (z : H) :=
  ∑ x, if grad x=z then W x * W (u-x) else 0

theorem coefficient_product {A H : Type*} [Fintype A] [AddCommGroup A]
    [AddCommGroup H] [DecidableEq H] (grad : A →+ H) (W : A → ℤ) (S z : H) :
    coefficient grad W z * coefficient grad W (S-z) =
    ∑ u, if grad u=S then paired grad W u z else 0 := by
  classical
  unfold coefficient
  rw [sum_mul]
  simp_rw [mul_sum]
  trans ∑ u, ∑ x, if grad u=S then if grad x=z then W x * W (u-x) else 0 else 0
  · conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro x _
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight x)]
    simp only [Equiv.coe_addRight, map_add, add_sub_cancel_right]
    apply sum_congr rfl
    intro y _
    by_cases hx : grad x=z
    · subst z
      by_cases hy : grad y = S-grad x
      · have hg : grad y+grad x=S := sub_add_cancel S _ ▸ congrArg (·+grad x) hy
        simp [hy,hg]
      · have hg : grad y+grad x≠S := fun t => hy (eq_sub_iff_add_eq.mpr t)
        simp [hy,hg]
    · simp [hx]
  · apply sum_congr rfl
    intro u _
    by_cases hu : grad u=S <;> simp [hu,paired]

theorem pairedTranslate {A H : Type*} [Fintype A] [AddCommGroup A]
    [AddCommGroup H] [DecidableEq H] (grad : A →+ H) (W : A → ℤ) (u p : A)
    (a b : H) (shift : grad p=b-a)
    (invariant : ∀ x, W (x+p) * W (u-(x+p)) = W x * W (u-x)) :
    paired grad W u a = paired grad W u b := by
  unfold paired
  rw [← Equiv.sum_comp (Equiv.addRight p) (fun x => if grad x=b then W x * W (u-x) else 0)]
  apply sum_congr rfl
  intro x _
  simp only [Equiv.coe_addRight, map_add,shift,invariant]
  have cond : grad x+(b-a)=b ↔ grad x=a := by constructor <;> intro h <;> abel_nf at * <;> grind
  by_cases ha : grad x=a <;> simp [ha,cond]

def edgeWeight {E : Type*} [Fintype E] (w : E → ZMod 2 → ℤ) (x : E → ZMod 2) := ∏ e, w e (x e)

theorem pathWeight {E : Type*} [Fintype E] (w : E → ZMod 2 → ℤ) (u x p : E → ZMod 2)
    (supported : ∀ e, u e=0 → p e=0) :
    edgeWeight w (x+p) * edgeWeight w (u-(x+p)) = edgeWeight w x * edgeWeight w (u-x) := by
  simp only [edgeWeight, ←prod_mul_distrib]
  apply prod_congr rfl
  intro e _
  change w e (x e + p e) * w e (u e - (x e + p e)) = w e (x e) * w e (u e - x e)
  by_cases hp : p e=0
  · simp [hp]
  have hu : u e≠0 := fun h => hp (supported e h)
  have bin (q : ZMod 2) : q=0 ∨ q=1 := by fin_cases q <;> first | exact Or.inl rfl | exact Or.inr rfl
  have h1 := (bin (p e)).resolve_left hp
  have h2 := (bin (u e)).resolve_left hu
  have e2 : (1 + 1 : ZMod 2)=0 := by decide
  rcases bin (x e) with h|h <;> rw [h,h1,h2] <;> simp only [e2,zero_add,sub_zero,sub_self] <;> ring

theorem weightedSourceRecurrence {n : ℕ} [NeZero n] {E H C : Type*} [Fintype E]
    [DecidableEq E] [Fintype C] [DecidableEq C] [AddCommGroup H] [DecidableEq H]
    (grad : (E → ZMod 2) →+ H) (source : Fin n → H) (allSources : H)
    (w : E → ZMod 2 → ℤ)
    (hgraph : ∀ u, grad u=allSources →
      ∃ B : Fin n → C, Noncrossing B ∧ (∀ k, 2 ∣ (fiber B k).card) ∧
        ∀ i j, B i=B j → ∃ p, (∀ e, u e=0 → p e=0) ∧ grad p=source j-source i) :
    coefficient grad (edgeWeight w) 0 * coefficient grad (edgeWeight w) allSources =
      ∑ j ∈ univ.erase (0 : Fin n), -(-1 : ℤ)^j.val *
        (coefficient grad (edgeWeight w) (source j - source 0) *
         coefficient grad (edgeWeight w) (allSources - (source j - source 0))) := by
  classical
  let W := edgeWeight w
  have fact (z : H) := coefficient_product grad W allSources z
  change coefficient grad W 0 * coefficient grad W allSources = _
  conv_lhs => rw [←sub_zero allSources, fact]
  change _ = ∑ j ∈ univ.erase (0 : Fin n), -(-1 : ℤ)^j.val *
    (coefficient grad W (source j-source 0) * coefficient grad W (allSources-(source j-source 0)))
  simp_rw [fact, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  by_cases hu : grad u=allSources
  · obtain ⟨B,nc,even,paths⟩ := hgraph u hu
    let f (i : Fin n) := paired grad W u (source i-source 0)
    have const (i j) (same : B i=B j) : f i=f j := by
      obtain ⟨p,supp,move⟩ := paths i j same
      apply pairedTranslate grad W u p _ _ (by rw [move]; abel)
      exact fun x => pathWeight w u x p supp
    have c := componentCancellation B nc even f const
    have sep := add_sum_erase univ (fun i : Fin n => (-1 : ℤ)^i.val * f i) (mem_univ (0 : Fin n))
    rw [c] at sep
    simp only [hu,ite_true,Fin.val_zero,pow_zero,one_mul] at *
    change _ = ∑ j ∈ univ.erase (0 : Fin n), -(-1 : ℤ)^j.val * f j
    simp_rw [neg_mul, Finset.sum_neg_distrib]
    have eq : f 0 = paired grad W u 0 := by simp [f]
    omega
  · simp [hu]

end BoundarySwitch
namespace BoundarySwitch
open Finset

def groupLink {V E : Type*} (u v : E → V) (z : E → ZMod 2) (a b : V) : Prop :=
  ∃ e, z e ≠ 0 ∧ ((u e=a ∧ v e=b) ∨ (u e=b ∧ v e=a))

abbrev linked {V E : Type*} (u v : E → V) (z : E → ZMod 2) (a b : V) : Prop :=
  Relation.ReflTransGen (groupLink u v z) a b

theorem revLinked {V E : Type*} (u v : E → V) (z : E → ZMod 2) {a b : V}
    (p : linked u v z a b) : linked u v z b a := by
  induction p with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e,ez,ends⟩ := h
    exact (Relation.ReflTransGen.single ⟨e,ez,ends.symm⟩).trans ih

noncomputable def component {V E : Type*} [Fintype V] (u v : E → V) (z : E → ZMod 2)
    (a : V) : Finset V := by classical exact univ.filter (linked u v z a)

theorem mem_component {V E : Type*} [Fintype V] (u v : E → V) (z : E → ZMod 2) (a b : V) :
    b ∈ component u v z a ↔ linked u v z a b := by classical simp [component]

theorem same_component {V E : Type*} [Fintype V] (u v : E → V) (z : E → ZMod 2) (a b : V) :
    component u v z a = component u v z b ↔ linked u v z a b := by
  classical
  constructor
  · intro eq
    apply (mem_component ..).mp
    rw [eq]
    exact (mem_component ..).mpr .refl
  · intro h
    ext k; rw [mem_component,mem_component]
    exact ⟨fun p => (revLinked _ _ _ h).trans p, fun p => h.trans p⟩

def edgeSource {V : Type*} [DecidableEq V] (v : V) : V → ZMod 2 := fun k => if v=k then 1 else 0

def incidence {V E : Type*} [DecidableEq V] [Fintype E] (u v : E → V) :
    (E → ZMod 2) →+ (V → ZMod 2) where
  toFun z := fun x => ∑ e, ((if u e=x then z e else 0) - (if v e=x then z e else 0))
  map_zero' := by ext; simp
  map_add' := by
    intro x y
    funext k; simp only [Pi.add_apply,←sum_add_distrib]
    apply sum_congr rfl; intro e _
    by_cases hu : u e=k <;> by_cases hv : v e=k <;> simp [hu,hv] <;> abel

theorem incidence_atom {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] (u v : E → V) (e : E) :
    incidence u v (Pi.single e 1) = edgeSource (u e) - edgeSource (v e) := by
  funext k
  change (∑ f,((if u f=k then (Pi.single e 1 : E → ZMod 2) f else 0) -
     (if v f=k then (Pi.single e 1 : E → ZMod 2) f else 0))) = _
  rw [Finset.sum_eq_single e]
  · simp [edgeSource]
  · intro b _ ne
    simp [Pi.single_eq_of_ne ne]
  · simp

theorem supportedPath {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] (u v : E → V)
    (z : E → ZMod 2) (a b : V) (h : linked u v z a b) :
    ∃ p, (∀ e, z e=0 → p e=0) ∧ incidence u v p = edgeSource b-edgeSource a := by
  induction h with
  | refl => exact ⟨0, by simp, by simp⟩
  | tail _ hx ih =>
    obtain ⟨p,hp,hb⟩ := ih
    obtain ⟨e,ne,he|he⟩ := hx
    · refine ⟨p-Pi.single e 1,?_,?_⟩
      · intro f hf
        have hfe : f≠e := fun eq => ne (eq ▸ hf)
        simp [Pi.single_eq_of_ne hfe,hp f hf]
      · rw [map_sub,hb,incidence_atom,he.1,he.2]; abel
    · refine ⟨p+Pi.single e 1,?_,?_⟩
      · intro f hf
        have hfe : f≠e := fun eq => ne (eq ▸ hf)
        simp [Pi.single_eq_of_ne hfe,hp f hf]
      · rw [map_add,hb,incidence_atom,he.1,he.2]; abel

theorem sum_component_incidence {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (u v : E → V)
    (z : E → ZMod 2) (a : V) : ∑ x ∈ component u v z a, incidence u v z x = 0 := by
  classical
  change ∑ x ∈ component u v z a, ∑ e : E, ((if u e=x then z e else 0) - (if v e=x then z e else 0)) = 0
  rw [sum_comm]
  apply sum_eq_zero
  intro e _
  rw [sum_sub_distrib,sum_ite_eq,sum_ite_eq]
  by_cases he : z e=0
  · simp [he]
  · have eq : u e ∈ component u v z a ↔ v e ∈ component u v z a := by
      rw [mem_component,mem_component]
      have h : linked u v z (u e) (v e) := .single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
      exact ⟨fun p => p.trans h,fun p => p.trans (revLinked _ _ _ h)⟩
    by_cases hx : u e ∈ component u v z a <;> simp [hx,←eq]

theorem component_even {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] {n : ℕ}
    (u v : E → V) (z : E → ZMod 2) (q : Fin n → V)
    (h : incidence u v z=∑ i, edgeSource (q i)) (k : Finset V) :
    2 ∣ (fiber (fun i => component u v z (q i)) k).card := by
  classical
  by_cases hne : (fiber (fun i => component u v z (q i)) k).Nonempty
  · obtain ⟨i,hi⟩ := hne
    have eq := (mem_filter.mp hi).2
    change component u v z (q i)=k at eq
    subst k
    have hsum := sum_component_incidence u v z (q i)
    rw [h] at hsum
    simp_rw [Finset.sum_apply] at hsum
    rw [sum_comm] at hsum
    simp only [edgeSource,sum_ite_eq] at hsum
    have equal (j : Fin n) : q j ∈ component u v z (q i) ↔ component u v z (q j)=component u v z (q i) := by
      rw [mem_component,eq_comm,same_component]
    simp_rw [equal] at hsum
    rw [←ZMod.natCast_eq_zero_iff _ 2]
    simpa [fiber,Finset.sum_boole] using hsum
  · simp [not_nonempty_iff_eq_empty.mp hne]
end BoundarySwitch
namespace BoundarySwitch
open Finset
def colored {V E : Type*} (u v : E → V) (z : E → ZMod 2) (root : V) : Option V → Prop
  | none => False
  | some x => linked u v z root x

theorem liftWalk {V E D : Type*} (u v : E → V) (z : E → ZMod 2) (src dst : D → Option V)
    (rep : ∀ x y, groupLink u v z x y → ∃ d, src d=some x ∧ dst d=some y) (a b)
    (h : linked u v z a b) :
    Relation.ReflTransGen (fun x y => colored u v z a x ∧ colored u v z a y ∧ ∃ d, src d=x ∧ dst d=y)
      (some a) (some b) := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih =>
    exact ih.tail ⟨hprev,hprev.tail hstep,rep _ _ hstep⟩
theorem unitPartitionNoncross {n m t l : ℕ} (u v : Fin m → Fin n) (pin : Fin t ↪ Fin n)
    (noLoop : ∀ e, u e ≠ v e)
    (connected : ∀ i j, Relation.ReflTransGen (fun x y => ∃ e, (u e=x ∧ v e=y) ∨ (u e=y ∧ v e=x)) i j)
    (src dst : Fin l → Option (Fin n)) (rot rev : Equiv.Perm (Fin l)) (sp : Fin t → Fin l)
    (uniq : Function.Injective (fun d => (src d,dst d)))
    (support : ∀ x y : Option (Fin n),
      x.elim (y.elim false (fun i => decide (∃ j, pin j=i)))
        (fun i => y.elim (decide (∃ j,pin j=i))
          (fun j => decide (∃ e : Fin m, (u e=i ∧ v e=j) ∨ (u e=j ∧ v e=i)))) = true ↔
      ∃ d, src d=x ∧ dst d=y)
    (revrot : ∀ d, src (rev d)=dst d ∧ dst (rev d)=src d ∧ src (rot d)=src d)
    (localCycle : ∀ d e, src d=src e → ∃ j : ℕ, (rot^j) d=e)
    (spoke : ∀ i, src (sp i)=none ∧ dst (sp i)=some (pin i) ∧
      ∀ j : Fin t, j.val=(i.val+1)%t → rot (sp i)=sp j)
    (euler : 2*(n+1) + 2*((Finset.univ : Finset (Fin l)).image
      (fun d => (Finset.range l).image (fun j => (fun k => rot (rev k))^[j] d))).card = 4+l)
    {h : ℕ} (sel : Fin h ↪o Fin t) (z : Fin m → ZMod 2) :
    Noncrossing (fun i => component u v z (pin (sel i))) := by
  classical
  have rep (x y) (e : groupLink u v z x y) : ∃ d, src d=some x ∧ dst d=some y := by
    apply (support (some x) (some y)).mp
    obtain ⟨e,_,h⟩ := e
    exact decide_eq_true (show ∃ k, (u k=x ∧ v k=y) ∨ (u k=y ∧ v k=x) from ⟨e,h⟩)
  intro a b c d ab bc cd ac bd
  by_contra diff
  let A := pin (sel a)
  let B := pin (sel b)
  have aC := (same_component u v z _ _).mp ac
  have bD := (same_component u v z _ _).mp bd
  have noAB := fun p => diff ((same_component u v z _ _).mpr p)
  let red := colored u v z A
  let blue := colored u v z B
  apply FiniteRotation.unitRotationNoCross u v pin noLoop connected src dst rot rev sp uniq support
    revrot localCycle spoke euler (sel a) (sel b) (sel c) (sel d)
    (sel.strictMono ab) (sel.strictMono bc) (sel.strictMono cd) red blue id id
  · intro w hw hr
    cases w with
    | none => exact hr
    | some x => exact noAB (hr.trans (revLinked u v z hw))
  · exact Relation.ReflTransGen.refl
  · exact aC
  · exact Relation.ReflTransGen.refl
  · exact liftWalk u v z src dst rep A _ aC
  · exact Relation.ReflTransGen.mono (fun x y ⟨hx,hy,d,hd⟩ => ⟨hx,hy,d,Or.inl hd⟩)
      _ _ (liftWalk u v z src dst rep B _ bD)
theorem planarSourceRecurrence {n m t l : ℕ} (u v : Fin m → Fin n) (pin : Fin t ↪ Fin n)
    (noLoop : ∀ e, u e ≠ v e)
    (connected : ∀ i j, Relation.ReflTransGen (fun x y => ∃ e, (u e=x ∧ v e=y) ∨ (u e=y ∧ v e=x)) i j)
    (src dst : Fin l → Option (Fin n)) (rot rev : Equiv.Perm (Fin l)) (sp : Fin t → Fin l)
    (uniq : Function.Injective (fun d => (src d,dst d)))
    (support : ∀ x y : Option (Fin n),
      x.elim (y.elim false (fun i => decide (∃ j, pin j=i)))
        (fun i => y.elim (decide (∃ j,pin j=i))
          (fun j => decide (∃ e : Fin m, (u e=i ∧ v e=j) ∨ (u e=j ∧ v e=i)))) = true ↔
      ∃ d, src d=x ∧ dst d=y)
    (revrot : ∀ d, src (rev d)=dst d ∧ dst (rev d)=src d ∧ src (rot d)=src d)
    (localCycle : ∀ d e, src d=src e → ∃ j : ℕ, (rot^j) d=e)
    (spoke : ∀ i, src (sp i)=none ∧ dst (sp i)=some (pin i) ∧
      ∀ j : Fin t, j.val=(i.val+1)%t → rot (sp i)=sp j)
    (euler : 2*(n+1) + 2*((Finset.univ : Finset (Fin l)).image
      (fun d => (Finset.range l).image (fun j => (fun k => rot (rev k))^[j] d))).card = 4+l)
    {h : ℕ} [NeZero h] (sel : Fin h ↪o Fin t) (w : Fin m → ZMod 2 → ℤ) :
    let q := fun i => pin (sel i)
    let Z := coefficient (incidence u v) (edgeWeight w)
    let allS := ∑ i, edgeSource (q i)
    Z 0 * Z allS = ∑ j ∈ univ.erase (0 : Fin h), -(-1 : ℤ)^j.val *
       (Z (edgeSource (q j)-edgeSource (q 0)) * Z (allS - (edgeSource (q j)-edgeSource (q 0)))) := by
  classical
  dsimp only
  apply weightedSourceRecurrence (C:=Finset (Fin n)) (incidence u v) (fun i => edgeSource (pin (sel i)))
    (∑ i,edgeSource (pin (sel i))) w
  intro z hz
  refine ⟨fun i => component u v z (pin (sel i)),?_,?_,?_⟩
  · exact unitPartitionNoncross u v pin noLoop connected src dst rot rev sp uniq support revrot localCycle spoke euler sel z
  · exact component_even u v z (fun i => pin (sel i)) hz
  · intro i j same
    exact supportedPath u v z _ _ ((same_component u v z _ _).mp same)
end BoundarySwitch

namespace BoundarySwitch
open Finset

def binary (q : ZMod 2) : q=0 ∨ q=1 := by fin_cases q <;> first | exact Or.inl rfl | exact Or.inr rfl

def sgn (q : ZMod 2) : ℤ := if q=0 then 1 else -1

theorem sgn_add (a b : ZMod 2) : sgn (a+b)=sgn a * sgn b := by
  rcases binary a with ha|ha <;> rcases binary b with hb|hb <;> rw [ha,hb] <;> decide

theorem sgn_sum {A : Type*} [Fintype A] (f : A → ZMod 2) : sgn (∑ a, f a) = ∏ a, sgn (f a) := by
  classical
  suffices ∀ s : Finset A, sgn (∑ a ∈ s, f a) = ∏ a ∈ s, sgn (f a) from this univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert x s hx ih => rw [sum_insert hx,prod_insert hx,sgn_add,ih]

def dot {V : Type*} [Fintype V] (a b : V → ZMod 2) := ∑ v, a v*b v

theorem dot_add {V : Type*} [Fintype V] (a b x : V → ZMod 2) :
    dot (a+b) x = dot a x + dot b x := by simp [dot,add_mul,sum_add_distrib]

theorem dot_grad {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (u v : E→V)
    (y : E→ ZMod 2) (x : V→ZMod 2) :
    dot (incidence u v y) x = ∑ e, y e*(x (u e)-x (v e)) := by
  simp only [dot,incidence,AddMonoidHom.coe_mk,ZeroHom.coe_mk,sum_mul,sub_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro e _
  rw [sum_sub_distrib,sum_ite_eq,sum_ite_eq]
  simp [mul_sub]

theorem sum_sgn_bit (v : ZMod 2) : ∑ b : ZMod 2, sgn (v*b) = if v=0 then 2 else 0 := by
  rw [show (∑ b : ZMod 2, sgn (v*b)) = sgn (v*0) + sgn (v*1) from Fin.sum_univ_two _]
  rcases binary v with h|h <;> rw [h] <;> decide

theorem dot_orthogonal {V : Type*} [Fintype V] [DecidableEq V] (s : V → ZMod 2) :
    ∑ x, sgn (dot s x) = if s=0 then (2 : ℤ)^Fintype.card V else 0 := by
  classical
  simp only [dot,sgn_sum]
  rw [← Fintype.prod_sum (fun v (b : ZMod 2) => sgn (s v*b))]
  simp_rw [sum_sgn_bit]
  by_cases zero : s=0
  · simp [zero]
  · rw [if_neg zero]
    have ne : ∃ v, s v ≠ 0 := by
      by_contra! h; exact zero (funext h)
    obtain ⟨v,hv⟩ := ne
    exact prod_eq_zero (mem_univ v) (if_neg hv)

def expanded {E : Type*} (w : E → ZMod 2 → ℤ) (e : E) (i : ZMod 2) :=
  if i=0 then w e 0+w e 1 else w e 0-w e 1

theorem edge_fourier {E : Type*} (w : E → ZMod 2 → ℤ) (e : E) (b : ZMod 2) :
    2*w e b = ∑ y : ZMod 2, expanded w e y * sgn (y*b) := by
  rw [show (∑ y : ZMod 2, expanded w e y * sgn (y*b)) = expanded w e 0 * sgn (0*b) + expanded w e 1 * sgn (1*b) from Fin.sum_univ_two _]
  rcases binary b with hb|hb <;> rw [hb] <;> simp [expanded,sgn] <;> ring

def spin {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] (u v : E → V)
    (w : E → ZMod 2 → ℤ) (s : V → ZMod 2) :=
  ∑ x : V → ZMod 2, sgn (dot s x) * ∏ e, w e (x (u e)-x (v e))

theorem scaledSpin {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (u v : E → V) (w : E → ZMod 2 → ℤ) (s : V → ZMod 2) :
    (2 : ℤ)^Fintype.card E * spin u v w s =
    2^Fintype.card V * coefficient (incidence u v) (edgeWeight (expanded w)) s := by
  classical
  let W := edgeWeight (expanded w)
  have expandAt (x : V → ZMod 2) :
      (2 : ℤ)^Fintype.card E * ∏ e, w e (x (u e)-x (v e)) =
      ∑ y : E → ZMod 2, W y * sgn (dot (incidence u v y) x) := by
    calc
      _ = ∏ e, 2*w e (x (u e)-x (v e)) := by rw [prod_mul_distrib]; simp
      _ = _ := by
        simp_rw [edge_fourier]
        rw [Fintype.prod_sum]
        apply sum_congr rfl;intro y _
        rw [prod_mul_distrib,←sgn_sum,←dot_grad]
        rfl
  unfold spin
  rw [mul_sum]
  trans ∑ x : V → ZMod 2, ∑ y : E → ZMod 2, W y * sgn (dot (s+incidence u v y) x)
  · apply sum_congr rfl;intro x _
    rw [mul_left_comm,expandAt,mul_sum]
    apply sum_congr rfl;intro y _
    rw [dot_add,sgn_add]
    ring
  · rw [sum_comm]
    change _ = 2 ^ Fintype.card V * ∑ y, if incidence u v y=s then W y else 0
    rw [mul_sum]
    apply sum_congr rfl;intro y _
    rw [←mul_sum,dot_orthogonal]
    have char2 (a : ZMod 2) : a+a=0 := by rcases binary a with h|h <;> rw [h] <;> decide
    have eq : s + incidence u v y=0 ↔ incidence u v y=s := by
      constructor
      · intro h
        funext v'
        have hd := congrFun h v'
        change s v' + incidence u v y v'=0 at hd
        exact add_left_cancel (hd.trans (char2 (s v')).symm)
      · intro h; rw [h]; exact funext fun v' => char2 (s v')
    by_cases h : incidence u v y=s
    · rw [if_pos (eq.mpr h),if_pos h,mul_comm]
    · rw [if_neg (fun hh => h (eq.mp hh)),if_neg h,mul_zero,mul_zero]
end BoundarySwitch
namespace BoundarySwitch
open Finset
theorem planarSpinRecurrence {n m t l : ℕ} (u v : Fin m → Fin n) (pin : Fin t ↪ Fin n)
    (noLoop : ∀ e, u e ≠ v e)
    (connected : ∀ i j, Relation.ReflTransGen (fun x y => ∃ e, (u e=x ∧ v e=y) ∨ (u e=y ∧ v e=x)) i j)
    (src dst : Fin l → Option (Fin n)) (rot rev : Equiv.Perm (Fin l)) (sp : Fin t → Fin l)
    (uniq : Function.Injective (fun d => (src d,dst d)))
    (support : ∀ x y : Option (Fin n),
      x.elim (y.elim false (fun i => decide (∃ j, pin j=i)))
        (fun i => y.elim (decide (∃ j,pin j=i))
          (fun j => decide (∃ e : Fin m, (u e=i ∧ v e=j) ∨ (u e=j ∧ v e=i)))) = true ↔
      ∃ d, src d=x ∧ dst d=y)
    (revrot : ∀ d, src (rev d)=dst d ∧ dst (rev d)=src d ∧ src (rot d)=src d)
    (localCycle : ∀ d e, src d=src e → ∃ j : ℕ, (rot^j) d=e)
    (spoke : ∀ i, src (sp i)=none ∧ dst (sp i)=some (pin i) ∧
      ∀ j : Fin t, j.val=(i.val+1)%t → rot (sp i)=sp j)
    (euler : 2*(n+1) + 2*((Finset.univ : Finset (Fin l)).image
      (fun d => (Finset.range l).image (fun j => (fun k => rot (rev k))^[j] d))).card = 4+l)
    {h : ℕ} [NeZero h] (sel : Fin h ↪o Fin t) (w : Fin m → ZMod 2 → ℤ) :
    let q := fun i => pin (sel i)
    let Z := spin u v w
    let allS := ∑ i, edgeSource (q i)
    Z 0 * Z allS = ∑ j ∈ univ.erase (0 : Fin h), -(-1 : ℤ)^j.val *
       (Z (edgeSource (q j)-edgeSource (q 0)) * Z (allS - (edgeSource (q j)-edgeSource (q 0)))) := by
  classical
  dsimp only
  let Z := coefficient (incidence u v) (edgeWeight (expanded w))
  let moment := spin u v w
  let S := ∑ i, edgeSource (pin (sel i))
  let pair := fun i => edgeSource (pin (sel i)) - edgeSource (pin (sel 0))
  let M : ℤ := 2^m
  let K : ℤ := 2^n
  have scaled (s : Fin n → ZMod 2) : M*moment s=K*Z s := by simpa [M,K,moment,Z] using scaledSpin u v w s
  have both (x y) : M^2 * (moment x*moment y) = K^2*(Z x*Z y) := by
    calc
      _ = (M*moment x)*(M*moment y) := by ring
      _ = (K*Z x)*(K*Z y) := by rw [scaled,scaled]
      _ = _ := by ring
  have srcRec := planarSourceRecurrence u v pin noLoop connected src dst rot rev sp uniq support
    revrot localCycle spoke euler sel (expanded w)
  change Z 0*Z S=∑ j ∈ univ.erase (0 : Fin h), -(-1 : ℤ)^j.val * (Z (pair j)*Z (S-pair j)) at srcRec
  change moment 0*moment S=∑ j ∈ univ.erase (0 : Fin h), -(-1 : ℤ)^j.val * (moment (pair j)*moment (S-pair j))
  have ne : M^2 ≠ 0 := by dsimp [M]; positivity
  apply mul_left_cancel₀ ne
  rw [both,srcRec,mul_sum,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_left_comm (K^2),mul_left_comm (M^2),both]
end BoundarySwitch

namespace BoundaryMass

def flip {I : Type*} (x : I → Bool) : I → Bool := fun a => !(x a)

def flipEquiv (I : Type*) : (I → Bool) ≃ (I → Bool) where
  toFun := flip
  invFun := flip
  left_inv _ := by funext a; simp [flip]
  right_inv _ := by funext a; simp [flip]

theorem spinPair {I : Type*} [Fintype I] [DecidableEq I] (p q : I)
    (W : (I → Bool) → ℤ) (hs : ∀ x, W (flip x) = W x) :
    (∑ x, (if x p = x q then W x else -W x)) + ∑ x, W x =
      4 * ∑ x, (if x p = false ∧ x q = false then W x else 0) := by
  classical
  let H (x : I → Bool) : ℤ := if x p = false ∧ x q = false then W x else 0
  have h (x : I → Bool) :
      (if x p = x q then W x else -W x) + W x = 2 * (H x + H (flip x)) := by
    simp only [H,hs,flip]
    cases hp : x p <;> cases hq : x q <;> simp [hp,hq] <;> ring
  have shift : (∑ x, H (flip x)) = ∑ x, H x := (flipEquiv I).sum_comp H
  rw [← Finset.sum_add_distrib]
  change (∑ x, ((if x p = x q then W x else -W x) + W x)) = 4 * ∑ x, H x
  simp_rw [h]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, shift]
  ring

theorem fourPinPadding (z a01 a02 a03 a12 a13 a23 : ℤ) :
    (z+a01)*(z+a23) - (z-a02)*(z-a13) + (z+a03)*(z+a12) =
    z^2 + z*(a01+a02+a03+a12+a13+a23) + a01*a23-a02*a13+a03*a12 := by ring

end BoundaryMass

namespace BoundarySwitch
open Finset
def bitVal (x : Bool) : ZMod 2 := if x then 1 else 0

def bitEquiv : Bool ≃ ZMod 2 where
  toFun := bitVal
  invFun := fun q => decide (q ≠ 0)
  left_inv := by intro b; cases b <;> decide
  right_inv := by intro q; rcases binary q with h|h <;> rw [h] <;> decide

theorem bitDiff (a b : Bool) : bitVal (xor a b) = bitVal a - bitVal b := by
  cases a <;> cases b <;> decide

def rawIsing {V E : Type*} [Fintype E] (u v : E→V) (w : E→Bool→ℤ) (x : V → Bool) :=
  ∏ e, w e (xor (x (u e)) (x (v e)))

theorem rawFlip {V E : Type*} [Fintype E] (u v : E→V) (w : E→Bool→ℤ) (x : V→Bool) :
    rawIsing u v w (BoundaryMass.flip x) = rawIsing u v w x := by
  unfold rawIsing
  apply prod_congr rfl;intro e _
  simp [BoundaryMass.flip]

theorem spinBool {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (u v : E→V) (w : E→Bool→ℤ) (s : V→ZMod 2) :
    spin u v (fun e b => w e (bitEquiv.symm b)) s =
      ∑ x : V→Bool, sgn (dot s (fun j => bitVal (x j))) * rawIsing u v w x := by
  classical
  let conv : (V → Bool) ≃ (V → ZMod 2) := Equiv.piCongrRight (fun _ => bitEquiv)
  unfold spin
  rw [← Equiv.sum_comp conv]
  apply sum_congr rfl;intro x _
  change sgn (dot s (fun j => bitVal (x j))) * ∏ e,
    w e (bitEquiv.symm (bitVal (x (u e))-bitVal (x (v e)))) = _
  have cv (b : Bool) : bitEquiv.symm (bitVal b) = b := bitEquiv.symm_apply_apply b
  simp only [←bitDiff, cv, rawIsing]

theorem dotSite {V : Type*} [Fintype V] [DecidableEq V] (i : V) (x : V → ZMod 2) :
    dot (edgeSource i) x=x i := by
  simp [dot,edgeSource,ite_mul]

theorem pairSign {V : Type*} [Fintype V] [DecidableEq V] (i j : V) (x : V→Bool) :
    sgn (dot (edgeSource i - edgeSource j) (fun k => bitVal (x k))) =
      if x i = x j then 1 else -1 := by
  have minus (a b y : V → ZMod 2) : dot (a-b) y = dot a y-dot b y := by
    simp [dot,sub_mul,sum_sub_distrib]
  rw [minus,dotSite,dotSite]
  cases x i <;> cases x j <;> decide

theorem observablesAtGrid {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (u v : E→V) (w : E→Bool→ℤ) (i j : V) :
    let Z := spin u v (fun e b => w e (bitEquiv.symm b)) 0
    let M := spin u v (fun e b => w e (bitEquiv.symm b)) (edgeSource i-edgeSource j)
    Z = ∑ x, rawIsing u v w x ∧
    Z+M = 4 * ∑ x, if x i=false ∧ x j=false then rawIsing u v w x else 0 := by
  classical
  dsimp only
  have base : spin u v (fun e b => w e (bitEquiv.symm b)) 0 = ∑ x,rawIsing u v w x := by
    rw [spinBool]; simp [dot,sgn]
  refine ⟨base,?_⟩
  rw [base,spinBool,add_comm]
  simp_rw [pairSign,ite_mul,one_mul,neg_one_mul]
  exact BoundaryMass.spinPair i j (rawIsing u v w) (rawFlip u v w)
end BoundarySwitch

private def pcxOneBorder {R : Type*} [CommRing R] {k : ℕ} (H : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin 2) R) (C : Matrix (Fin 2) (Fin k) R)
    (D : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) : R :=
  (Matrix.fromBlocks H (fun a (_ : (Fin 1)) => B a j)
    (fun (_ : (Fin 1)) b => C i b) (fun (_ _ : (Fin 1)) => D i j)).det

private lemma pcxOneBorder_eq {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) [Invertible H]
    (B : Matrix (Fin k) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin k) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    pcxOneBorder H B C D i j = H.det * (D - C * ⅟H * B) i j := by
  rw [pcxOneBorder, Matrix.det_fromBlocks₁₁ H (fun a (_ : (Fin 1)) => B a j) (fun (_ : (Fin 1)) b => C i b) (fun (_ _ : (Fin 1)) => D i j),Matrix.det_unique (n := (Fin 1))]
  congr 1

private lemma pcxBorderEliminate {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) [Invertible H]
    (B : Matrix (Fin k) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin k) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ) :
    H.det * (Matrix.fromBlocks H B C D).det =
      pcxOneBorder H B C D 0 0 * pcxOneBorder H B C D 1 1 -
      pcxOneBorder H B C D 0 1 * pcxOneBorder H B C D 1 0 := by
  simp only [pcxOneBorder_eq, Matrix.det_fromBlocks₁₁,Matrix.det_fin_two]
  ring
private lemma pcxOneBorder_map {k : ℕ} (H : Matrix (Fin k) (Fin k) ℤ)
    (B : Matrix (Fin k) (Fin 2) ℤ) (C : Matrix (Fin 2) (Fin k) ℤ)
    (D : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) (f : ℤ →+* ℝ) :
    f (pcxOneBorder H B C D i j) = pcxOneBorder (H.map f) (B.map f) (C.map f) (D.map f) i j := by
  rw [pcxOneBorder, RingHom.map_det,pcxOneBorder]
  congr 1
  ext a b
  cases a <;> cases b <;> rfl

private lemma pcxBorderEliminateInt {k : ℕ} (H : Matrix (Fin k) (Fin k) ℤ) (hh : H.det ≠ 0)
    (B : Matrix (Fin k) (Fin 2) ℤ) (C : Matrix (Fin 2) (Fin k) ℤ)
    (D : Matrix (Fin 2) (Fin 2) ℤ) :
    H.det * (Matrix.fromBlocks H B C D).det =
      pcxOneBorder H B C D 0 0 * pcxOneBorder H B C D 1 1 -
      pcxOneBorder H B C D 0 1 * pcxOneBorder H B C D 1 0 := by
  let f := Int.castRingHom ℝ
  have hh' : f H.det ≠ 0 := by change (H.det : ℝ) ≠ 0; exact_mod_cast hh
  rw [RingHom.map_det] at hh'
  let : Invertible (f.mapMatrix H) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hh')
  have res := pcxBorderEliminate (f.mapMatrix H) (B.map f) (C.map f) (D.map f)
  apply (show Function.Injective f by exact Int.cast_injective).eq_iff.mp
  simpa only [map_mul,map_sub,pcxOneBorder_map,RingHom.map_det,RingHom.mapMatrix_apply,
    Matrix.fromBlocks_map] using res
private lemma pcxBareissStep {k : ℕ} (H : Matrix (Fin k) (Fin k) ℤ) (hh : H.det ≠ 0)
    (B : Matrix (Fin k) (Fin 2) ℤ) (C : Matrix (Fin 2) (Fin k) ℤ)
    (D : Matrix (Fin 2) (Fin 2) ℤ) :
    (Matrix.fromBlocks H B C D).det =
      (pcxOneBorder H B C D 0 0 * pcxOneBorder H B C D 1 1 -
       pcxOneBorder H B C D 0 1 * pcxOneBorder H B C D 1 0) / H.det := by
  rw [←pcxBorderEliminateInt H hh B C D,Int.mul_ediv_cancel_left _ hh]
private def pcxJoin {I : Type*} {k m : ℕ} (f : Fin k → I) (g : Fin m → I) :
    Fin (k+m) → I := Sum.elim f g ∘ finSumFinEquiv.symm

private def pcxAppend {I : Type*} {k : ℕ} (f : Fin k → I) (v : I) :
    Fin (k+1) → I := pcxJoin f (fun _ : Fin 1 => v)

private lemma pcxJoinAssoc {I : Type*} {k : ℕ} (f : Fin k → I) (a b : I) :
    pcxAppend (pcxAppend f a) b = pcxJoin f ![a,b] := by
  funext j
  obtain ⟨j,rfl⟩ := (finSumFinEquiv (m:=k) (n:=2)).surjective j
  change _ = Sum.elim f ![a,b] (finSumFinEquiv.symm (finSumFinEquiv j))
  rw [Equiv.symm_apply_apply]
  cases j with
  | inl j =>
    have e : (Fin.castAdd 2 j) = j.castSucc.castSucc := rfl
    simp [pcxAppend,pcxJoin,Function.comp_def,finSumFinEquiv_apply_left,e]
  | inr j =>
    fin_cases j <;> simp [pcxAppend,pcxJoin,Function.comp_def,finSumFinEquiv_apply_right,
      show (Fin.natAdd k (0:Fin 2)) = (Fin.last k).castSucc by rfl,
      show (Fin.natAdd k (1:Fin 2)) = (Fin.last (k+1)) by rfl]

private def pcxMinor {I : Type*} {k : ℕ} (A : Matrix I I ℤ) (rows cols : Fin k → I) :=
  (A.submatrix rows cols).det

private lemma pcxJoinMinor {I : Type*} {k m : ℕ} (A : Matrix I I ℤ)
    (r c : Fin k → I) (r' c' : Fin m → I) :
    pcxMinor A (pcxJoin r r') (pcxJoin c c') =
      (Matrix.fromBlocks (A.submatrix r c) (A.submatrix r c')
        (A.submatrix r' c) (A.submatrix r' c')).det := by
  unfold pcxMinor
  rw [←Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext i j
  cases i <;> cases j <;> simp [Matrix.submatrix_apply,pcxJoin,Function.comp_def,Matrix.fromBlocks]

private lemma pcxIndexedStep {I : Type*} {k : ℕ} (A : Matrix I I ℤ)
    (f : Fin k → I) (a i j : I) (positive : pcxMinor A f f ≠ 0) :
    let entry := fun i j => pcxMinor A (pcxAppend f i) (pcxAppend f j)
    pcxMinor A (pcxAppend (pcxAppend f a) i) (pcxAppend (pcxAppend f a) j) =
      (entry a a * entry i j - entry a j * entry i a) / pcxMinor A f f := by
  let rs : Fin 2 → I := ![a,i]
  let cs : Fin 2 → I := ![a,j]
  have base := pcxBareissStep (A.submatrix f f) positive (A.submatrix f cs)
    (A.submatrix rs f) (A.submatrix rs cs)
  dsimp only
  rw [pcxJoinAssoc,pcxJoinAssoc,pcxJoinMinor]
  unfold pcxAppend
  simp_rw [pcxJoinMinor]
  exact base
private lemma pcxNextIndices {k n : ℕ} (hk : k < n) :
    pcxAppend (Fin.castLE hk.le) (⟨k,hk⟩ : Fin n) = Fin.castLE hk := by
  funext j
  obtain ⟨j,rfl⟩ := (finSumFinEquiv (m:=k) (n:=1)).surjective j
  cases j with
  | inl j => simp [pcxAppend,pcxJoin,finSumFinEquiv_apply_left]; rfl
  | inr j => fin_cases j; simp [pcxAppend,pcxJoin,finSumFinEquiv_apply_right]; rfl

private def pcxEntry {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hk : k ≤ n) (i j : Fin n) :=
  pcxMinor A (pcxAppend (Fin.castLE hk) i) (pcxAppend (Fin.castLE hk) j)

private def pcxPrincipal {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hk : k ≤ n) :=
  pcxMinor A (Fin.castLE hk) (Fin.castLE hk)

private lemma pcxInitialEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    pcxEntry A (Nat.zero_le n) i j = A i j := by
  unfold pcxEntry pcxMinor
  rw [Matrix.det_unique (n := Fin 1)]
  have ev (a : Fin n) : pcxAppend (Fin.castLE (Nat.zero_le n)) a (0 : Fin 1) = a := by
    change (pcxJoin _ _) (finSumFinEquiv (Sum.inr (0 : Fin 1))) = a
    simp [pcxJoin]
  change A (pcxAppend _ i 0) (pcxAppend _ j 0) = _
  rw [ev,ev]

private lemma pcxNextPrincipal {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hk : k < n) :
    pcxPrincipal A hk = pcxEntry A hk.le ⟨k,hk⟩ ⟨k,hk⟩ := by
  rw [pcxEntry,pcxNextIndices,pcxPrincipal]

private lemma pcxEntryUpdate {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hk : k < n)
    (positive : pcxPrincipal A hk.le ≠ 0) (i j : Fin n) :
    let p : Fin n := ⟨k,hk⟩
    let cell := pcxEntry A hk.le
    pcxEntry A hk i j = (cell p p * cell i j - cell p j * cell i p) / pcxPrincipal A hk.le := by
  have st := pcxIndexedStep A (Fin.castLE hk.le) (⟨k,hk⟩ : Fin n) i j positive
  dsimp only at st ⊢
  rw [pcxNextIndices] at st
  simpa only [pcxEntry,pcxPrincipal,pcxNextIndices] using st

private lemma pcxFinalPrincipal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    pcxPrincipal A (Nat.le_refl n) = A.det := rfl

namespace BoundaryPadding

variable {X : Type*}
abbrev Moment (X : Type*) := List X → ℚ
def consAt (x : X) (m : Moment X) : Moment X := fun l => m (x::l)
def shift (x : X) (u : ℚ) (m : Moment X) : Moment X := m + u • consAt x m

def eval (v : X → ℚ) : List X → ℚ → Moment X → ℚ
  | [],_,m => m []
  | x::xs,s,m => eval v xs (-s) (shift x (s*v x) m)

def co (k : X → ℚ) : List X → Moment X → ℚ
  | [],_ => 0
  | x::xs,m => k x * m xs - co k xs (consAt x m)

def evalFun (v : X → ℚ) (s : ℚ) (m : Moment X) : Moment X := fun l => eval v l s m
def coFun (k : X → ℚ) (m : Moment X) : Moment X := fun l => co k l m
def parity (m : Moment X) : Moment X := fun l => (-1 : ℚ)^l.length * m l

theorem shift_add (x : X) (u : ℚ) (m n : Moment X) :
    shift x u (m+n) = shift x u m + shift x u n := by
  funext l; simp [shift,consAt]; ring

theorem shift_smul (x : X) (u c : ℚ) (m : Moment X) :
    shift x u (c • m) = c • shift x u m := by
  funext l; simp [shift,consAt]; ring

theorem eval_add (v : X→ℚ) (l : List X) (s) (m n : Moment X) :
    eval v l s (m+n) = eval v l s m + eval v l s n := by
  induction l generalizing s m n with
  | nil => rfl
  | cons x xs ih => rw [eval,eval,eval,shift_add,ih]

theorem eval_smul (v : X→ℚ) (l : List X) (s c) (m : Moment X) :
    eval v l s (c • m) = c * eval v l s m := by
  induction l generalizing s m with
  | nil => rfl
  | cons x xs ih => rw [eval,eval,shift_smul,ih]

theorem eval_shift (v : X→ℚ) (l : List X) (s) (x : X) (a : ℚ) (m : Moment X) :
    eval v l s (shift x a m) = eval v l s m + a * eval v l s (consAt x m) := by
  rw [shift,eval_add,eval_smul]

theorem eval_parity (v : X→ℚ) (l : List X) (s) (m : Moment X) :
    eval v l s (parity m) = eval v l (-s) m := by
  induction l generalizing s m with
  | nil => simp [eval,parity]
  | cons x xs ih =>
    have h : shift x (s*v x) (parity m) = parity (shift x (-s*v x) m) := by
      funext l; simp [shift,consAt,parity,pow_succ]; ring
    rw [eval,eval,h,ih]

theorem co_add_m (k : X→ℚ) (l : List X) (m n : Moment X) :
    co k l (m+n)=co k l m+co k l n := by
  induction l generalizing m n with
  | nil => simp [co]
  | cons x xs ih =>
    have h : consAt x (m+n)=consAt x m+consAt x n := rfl
    simp only [co,Pi.add_apply,h,ih]; ring

theorem co_smul_m (k : X→ℚ) (l : List X) (c : ℚ) (m : Moment X) :
    co k l (c • m)=c * co k l m := by
  induction l generalizing m with
  | nil => simp [co]
  | cons x xs ih =>
    have h : consAt x (c • m)=c • consAt x m := rfl
    simp only [co,Pi.smul_apply,smul_eq_mul,h,ih]; ring

theorem co_linear_k (g h : X→ℚ) (l : List X) (a : ℚ) (m : Moment X) :
    co (fun x => g x + a*h x) l m = co g l m + a*co h l m := by
  induction l generalizing m with
  | nil => simp [co]
  | cons x xs ih => simp only [co,ih]; ring

theorem co_const (v : X→ℚ) (l : List X) (s : ℚ) (m : Moment X) :
    2*co (fun _ => 1) l (evalFun v s m) =
      eval v l (-s) m - (-1 : ℚ)^l.length * eval v l s m := by
  induction l generalizing s m with
  | nil => simp [co,eval]
  | cons x xs ih =>
    have h : consAt x (evalFun v s m) = evalFun v (-s) (shift x (s*v x) m) := rfl
    simp only [co,h,evalFun,one_mul,eval,List.length_cons,pow_succ]
    have hrec := ih (-s) (shift x (s*v x) m)
    simp only [neg_neg,eval_shift] at hrec ⊢
    linarith

theorem co_weighted (a v : X→ℚ) (l : List X) (s : ℚ) (m : Moment X) :
    eval v l (-s) (coFun a m) =
      -s * co (fun x => v x*a x) l (evalFun v s m) := by
  induction l generalizing s m with
  | nil => simp [eval,coFun,co]
  | cons x xs ih =>
    have shiftC : shift x (-s*v x) (coFun a m) =
        coFun a (shift x (s*v x) m) + (-s*v x*a x) • m := by
      funext l
      simp only [shift,consAt,coFun,co,co_add_m,co_smul_m,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    have h : consAt x (evalFun v s m) = evalFun v (-s) (shift x (s*v x) m) := rfl
    rw [eval,shiftC,neg_neg,eval_add,eval_smul,co,h]
    have hrec := ih (-s) (shift x (s*v x) m)
    simp only [neg_neg] at hrec
    rw [hrec]
    change _ = -s * (_ * eval v xs s m - _)
    ring
end BoundaryPadding
namespace BoundaryPadding
variable {X : Type*}

def pf (a : X → X → ℚ) : (l : List X) → ℚ
  | [] => 1
  | x::xs => ∑ i : Fin xs.length, (-1 : ℚ)^i.val * a x xs[i.val] * pf a (xs.eraseIdx i.val)
termination_by l => l.length
decreasing_by
  simp [List.length_eraseIdx_of_lt i.isLt]

theorem co_indices (k : X → ℚ) (l : List X) (m : Moment X) :
    co k l m = ∑ i : Fin l.length, (-1 : ℚ)^i.val * k l[i.val] * m (l.eraseIdx i.val) := by
  induction l generalizing m with
  | nil => simp [co]
  | cons x xs ih =>
    rw [co, ih]
    simp only [List.length_cons, Fin.sum_univ_succ]
    simp [consAt, pow_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]

theorem pf_step (a : X → X → ℚ) (x : X) (xs : List X) :
    pf a (x::xs) = co (a x) xs (pf a) := by rw [pf, co_indices]

theorem pf_odd (a : X → X → ℚ) (l : List X) (h : Odd l.length) : pf a l = 0 := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    rw [pf]
    apply Finset.sum_eq_zero
    intro i _
    rw [pf_odd a (xs.eraseIdx i.val) (by
      rw [List.length_eraseIdx_of_lt i.isLt]
      simp only [List.length_cons] at h
      obtain ⟨k,hk⟩ := h
      exact ⟨k-1, by have := i.isLt; omega⟩), mul_zero]
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]

theorem parity_pf (a : X → X → ℚ) : parity (pf a) = pf a := by
  funext l
  rcases Nat.even_or_odd l.length with h|h
  · simp [parity,h.neg_one_pow]
  · simp [parity,pf_odd a l h]

end BoundaryPadding

namespace BoundaryPadding
variable {X : Type*}
def padK (a : X → X → ℚ) (v : X → ℚ) (x y : X) := 1 + (-v x)*(v y*a x y)

theorem eval_step (v : X → ℚ) (a : X → X → ℚ) (x : X) (xs : List X)
    (h : Odd xs.length) :
    eval v (x::xs) 1 (pf a) = co (padK a v x) xs (evalFun v 1 (pf a)) := by
  have hpar := eval_parity v xs 1 (pf a)
  rw [parity_pf] at hpar
  have hc := co_const v xs 1 (pf a)
  rw [h.neg_one_pow,←hpar] at hc
  have he : consAt x (pf a) = coFun (a x) (pf a) := funext (pf_step a x)
  rw [eval,eval_shift,he,co_weighted]
  change _ = co (fun y => (fun _ => (1:ℚ)) y + (-v x)*((fun z => v z*a x z) y)) xs _
  rw [co_linear_k,←hpar]
  linarith

theorem pf_padding (a : X → X → ℚ) (v : X → ℚ) (l : List X)
    (h : Even l.length) : eval v l 1 (pf a) = pf (padK a v) l := by
  cases l with
  | nil => simp [eval,pf]
  | cons x xs =>
    have ho : Odd xs.length := by
      obtain ⟨k,hk⟩ := h
      exact ⟨k-1, by simp only [List.length_cons] at hk; omega⟩
    rw [eval_step v a x xs ho,pf_step,co_indices,co_indices]
    apply Finset.sum_congr rfl
    intro i _
    unfold evalFun
    rw [pf_padding a v (xs.eraseIdx i.val) (by
      rw [List.length_eraseIdx_of_lt i.isLt]
      obtain ⟨k,hk⟩ := ho
      exact ⟨k,by omega⟩)]
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]
end BoundaryPadding

namespace BoundaryPadding
variable {X : Type*}

def prodAlt (v f : X → ℚ) : List X → ℚ → ℚ
  | [],_ => 1
  | x::xs,s => (1+s*v x*f x) * prodAlt v f xs (-s)
def monom (f : X → ℚ) (l : List X) := (l.map f).prod

theorem eval_monom (v f : X → ℚ) (l : List X) (s : ℚ) :
    eval v l s (monom f) = prodAlt v f l s := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have he : shift x (s*v x) (monom f) = (1+s*v x*f x) • monom f := by
      funext ys
      simp [shift,monom,consAt]
      ring
    rw [eval,he,eval_smul,ih,prodAlt]

theorem eval_sublist_congr (v : X → ℚ) (l : List X) (s : ℚ) (m n : Moment X)
    (h : ∀ t, t.Sublist l → m t = n t) : eval v l s m = eval v l s n := by
  induction l generalizing s m n with
  | nil => exact h [] (.slnil)
  | cons x xs ih =>
    apply ih
    intro t ht
    simp only [shift, Pi.add_apply, Pi.smul_apply, smul_eq_mul, consAt]
    rw [h t (ht.cons x),h (x::t) (ht.cons₂ x)]

theorem histogram_pf {Ω : Type*} (W : Finset Ω) (μ : Ω → ℚ) (f : Ω → X → ℚ)
    (a : X → X → ℚ) (v : X → ℚ) (l : List X) (h : Even l.length)
    (hw : ∀ t, t.Sublist l → (∑ ω ∈ W, μ ω * monom (f ω) t) = pf a t) :
    (∑ ω ∈ W, μ ω * prodAlt v (f ω) l 1) = pf (padK a v) l := by
  classical
  let m : Ω → Moment X := fun ω => μ ω • monom (f ω)
  have lin (U : Finset Ω) : eval v l 1 (∑ ω ∈ U, m ω) =
      ∑ ω ∈ U, μ ω * prodAlt v (f ω) l 1 := by
    induction U using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have hz := eval_smul v l 1 0 (0 : Moment X)
      simpa using hz
    | @insert x U hx ih =>
      rw [Finset.sum_insert hx,Finset.sum_insert hx,eval_add,ih]
      simp [m,eval_smul,eval_monom]
  rw [←lin,←pf_padding a v l h]
  apply eval_sublist_congr
  intro t ht
  simpa [m,Finset.sum_apply] using hw t ht

end BoundaryPadding

namespace BoundaryPadding
variable {X : Type*}
abbrev MaskLabel (X : Type*) := Option (X × Bool) × Nat
def spinSign (b : Bool) : ℚ := if b then -1 else 1
def maskV (z : MaskLabel X) : ℚ :=
  (-1:ℚ)^z.2 * (z.1.elim 0 (fun p => spinSign p.2))
def maskSpin (σ : X → Bool) (z : MaskLabel X) : ℚ :=
  z.1.elim 0 (fun p => spinSign (σ p.1))
def fits (σ : X → Bool) (z : Option (X × Bool)) : Bool :=
  z.elim true (fun p => σ p.1 == p.2)
def padded (ps : List (X × Bool)) : List (Option (X × Bool)) :=
  ps.map some ++ if Even ps.length then [] else [none]

theorem padded_even (ps : List (X × Bool)) : Even (padded ps).length := by
  unfold padded
  split <;> simp_all

theorem mask_product (σ : X → Bool) (l : List (Option (X × Bool))) (n : Nat) :
    prodAlt maskV (maskSpin σ) (l.zipIdx n) ((-1:ℚ)^n) =
      if l.all (fits σ) then (2:ℚ)^l.reduceOption.length else 0 := by
  induction l generalizing n with
  | nil => simp [prodAlt,List.reduceOption]
  | cons z zs ih =>
    have hn : -((-1:ℚ)^n) = (-1:ℚ)^(n+1) := by simp [pow_succ]
    have hs : ((-1:ℚ)^n)*((-1:ℚ)^n) = 1 := by rw [←mul_pow]; simp
    rw [List.zipIdx_cons,prodAlt,hn,ih]
    cases z with
    | none => simp [maskV,maskSpin,fits,List.reduceOption]
    | some p =>
      rcases p with ⟨x,b⟩
      cases hh : σ x <;> cases b <;> cases hh' : zs.all (fits σ) <;>
        simp [maskV,maskSpin,fits,spinSign,hh,hh',List.reduceOption,hs,pow_succ] <;> ring

theorem mask_histogram_pf {Ω : Type*} (W : Finset Ω) (μ : Ω → ℚ) (σ : Ω → X → Bool)
    (ps : List (X × Bool)) (a : MaskLabel X → MaskLabel X → ℚ)
    (hw : ∀ t, t.Sublist (padded ps).zipIdx →
      (∑ ω ∈ W, μ ω * monom (maskSpin (σ ω)) t) = pf a t) :
    (2:ℚ)^ps.length * (∑ ω ∈ W, if ps.all (fun p => σ ω p.1 == p.2) then μ ω else 0) =
      pf (padK a maskV) (padded ps).zipIdx := by
  have hh := histogram_pf W μ (fun ω => maskSpin (σ ω)) a maskV
    (padded ps).zipIdx (by simpa using padded_even ps) hw
  rw [←hh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have hp := mask_product (σ ω) (padded ps) 0
  rw [show ((-1:ℚ)^0)=1 by simp] at hp
  rw [hp]
  have hfit : (padded ps).all (fits (σ ω)) =
      ps.all (fun p => σ ω p.1 == p.2) := by
    unfold padded
    split <;> simp only [List.all_append,List.all_map,List.all_cons,List.all_nil,
      Bool.and_true, fits, Option.elim_none,Function.comp_def] <;> rfl
  have hlen : (padded ps).reduceOption.length = ps.length := by
    unfold padded
    split <;> simp [List.reduceOption, List.filterMap_append, List.filterMap_map,Function.comp_def]
  rw [hfit,hlen]
  split <;> ring
end BoundaryPadding
namespace BoundaryPadding
variable {X : Type*}

theorem pf_scale (a : X → X → ℚ) (c : ℚ) (l : List X) (h : Even l.length) :
    pf (fun x y => c*a x y) l = c^(l.length/2) * pf a l := by
  cases l with
  | nil => simp [pf]
  | cons x xs =>
    rw [pf_step,pf_step,co_indices,co_indices,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hlen := List.length_eraseIdx_of_lt i.isLt
    obtain ⟨k,hk⟩ := h
    simp only [List.length_cons] at hk
    have hev : Even (xs.eraseIdx i.val).length := by rw [hlen]; exact ⟨k-1,by have := i.isLt; omega⟩
    rw [pf_scale a c (xs.eraseIdx i.val) hev]
    have hp : (x::xs).length/2 = (xs.eraseIdx i.val).length/2 + 1 := by
      simp only [List.length_cons,hlen]
      have := i.isLt
      omega
    rw [hp,pow_succ]
    ring
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]

theorem wick_of_rec (m : Moment X) (a : X → X → ℚ) (l : List X)
    (hn : m [] = 1)
    (hrec : ∀ x xs, (x::xs).Sublist l → m (x::xs) = co (a x) xs m) :
    m l = pf a l := by
  cases l with
  | nil => simpa [pf] using hn
  | cons x xs =>
    rw [hrec _ _ (.refl _),pf_step,co_indices,co_indices]
    apply Finset.sum_congr rfl
    intro i _
    rw [wick_of_rec m a (xs.eraseIdx i.val) hn (by
      intro z zs h
      exact hrec _ _ ((h.trans (List.eraseIdx_sublist ..)).cons x))]
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]

end BoundaryPadding

private lemma pcxIndexedIdentity {I : Type*} {k : ℕ} (A : Matrix I I ℤ)
    (f : Fin k → I) (a i j : I) (positive : pcxMinor A f f ≠ 0) :
    let entry := fun i j => pcxMinor A (pcxAppend f i) (pcxAppend f j)
    pcxMinor A f f * pcxMinor A (pcxAppend (pcxAppend f a) i) (pcxAppend (pcxAppend f a) j) =
      entry a a * entry i j - entry a j * entry i a := by
  let rs : Fin 2 → I := ![a,i]
  let cs : Fin 2 → I := ![a,j]
  have base := pcxBorderEliminateInt (A.submatrix f f) positive (A.submatrix f cs)
    (A.submatrix rs f) (A.submatrix rs cs)
  dsimp only
  rw [pcxJoinAssoc,pcxJoinAssoc,pcxJoinMinor]
  unfold pcxAppend
  simp_rw [pcxJoinMinor]
  exact base

private lemma pcxEntryIdentity {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hk : k < n)
    (positive : pcxPrincipal A hk.le ≠ 0) (i j : Fin n) :
    let p : Fin n := ⟨k,hk⟩
    let cell := pcxEntry A hk.le
    cell p p * cell i j - cell p j * cell i p = pcxPrincipal A hk.le * pcxEntry A hk i j := by
  have st := (pcxIndexedIdentity A (Fin.castLE hk.le) (⟨k,hk⟩ : Fin n) i j positive).symm
  dsimp only at st ⊢
  simpa only [pcxEntry,pcxPrincipal,pcxNextIndices] using st

private lemma pcxInitialPrincipal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    pcxPrincipal A (Nat.zero_le n) = 1 := by
  unfold pcxPrincipal pcxMinor; simp

private lemma pcxDivBounds (W : ℕ) (z d r M : ℤ) (hm : 1≤M) (width : 2*M^3 < (2:ℤ)^W)
    (identity : z=d*r) (hd : |d|≤M) (hr : |r|≤M) :
    0 ≤ M+r ∧ M+r < (2:ℤ)^W ∧ 2*(d*d) ≤ (2:ℤ)^W ∧ z*d+M*(d*d) < (2:ℤ)^W := by
  have M0 : 0≤M := by omega
  have hsq : d*d ≤ M*M := by
    calc
      _ = |d| * |d| := by rw [←abs_mul,abs_of_nonneg (mul_self_nonneg _)]
      _ ≤ _ := mul_le_mul hd hd (abs_nonneg _) M0
  have hsq2 : M≤M*M := by nlinarith [mul_nonneg M0 (show 0≤M-1 by omega)]
  have hcube : M*M≤M^3 := by nlinarith [mul_nonneg (mul_self_nonneg M) (show 0≤M-1 by omega)]
  have lower := (abs_le.mp hr).1
  have upper := (abs_le.mp hr).2
  refine ⟨by omega,by omega,by omega,?_⟩
  calc
    _ = (d*d)*(M+r) := by rw [identity];ring
    _ ≤ (M*M)*(2*M) := mul_le_mul hsq (by omega) (by omega) (mul_self_nonneg _)
    _ = 2*M^3 := by ring
    _ < _ := width

namespace Pcx446Arithmetic

private def pcxLayer {N n k : ℕ} (W : ℕ) (A : (Fin N → Bool) → Matrix (Fin n) (Fin n) ℤ)
    (hk : k≤n) := pcxSet W (fun x=>pcxPrincipal (A x) hk) ∪
      ⋃ i, ⋃ j, pcxSet W (fun x=>pcxEntry (A x) hk i j)

private lemma pcxDetCellB {N n k : ℕ} {S : Set (Sig N)} (W : ℕ) (M : ℤ)
    (A : (Fin N → Bool) → Matrix (Fin n) (Fin n) ℤ) (hk : k<n) (i j : Fin n)
    (h0 : (fun _=>false)∈S) (h1 : (fun _=>true)∈S)
    (layer : pcxLayer W A hk.le ⊆ S) (hm : 1≤M) (wide : 2*M^3 < (2:ℤ)^W)
    (nz : ∀ x, pcxPrincipal (A x) hk.le ≠ 0)
    (db : ∀ x, |pcxPrincipal (A x) hk.le|≤M) (rb : ∀ x, |pcxEntry (A x) hk i j|≤M) :
    Build S (pcxSet W (fun x=>pcxEntry (A x) hk i j)) (78*W^2+48*W) := by
  let p : Fin n := ⟨k,hk⟩
  let old := fun a b x => pcxEntry (A x) hk.le a b
  let D := fun x => pcxPrincipal (A x) hk.le
  let R := fun x => pcxEntry (A x) hk i j
  let prod1 := fun x => old p p x * old i j x
  let prod2 := fun x => old p j x * old i p x
  let Z := fun x => prod1 x - prod2 x
  have avail (a b : Fin n) : pcxSet W (old a b) ⊆ S := fun sig hs =>
    layer (Or.inr <| Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨b,hs⟩⟩)
  have iden (x) : Z x = D x * R x := pcxEntryIdentity (A x) hk (nz x) i j
  have hbounds (x) := pcxDivBounds W (Z x) (D x) (R x) M hm wide (iden x) (db x) (rb x)
  have m1 := pcxMulWordB W (old p p) (old i j) h0 (avail p p) (avail i j)
  have m2 := pcxMulWordB W (old p j) (old i p) h0 (avail p j) (avail i p)
  have products := unionB m1 m2
  have difference : Build (S ∪ (pcxSet W prod1 ∪ pcxSet W prod2)) (pcxSet W Z) (19*W) :=
    pcxSubWordB W prod1 prod2 (Or.inl h0) (Or.inl h1) (fun a h=>Or.inr (Or.inl h)) (fun a h=>Or.inr (Or.inr h))
  have sub := seq2B products difference
  have div : Build (S ∪ pcxSet W Z) (pcxSet W R) (58*W^2+29*W) :=
    pcxDivWordB W Z D R M (Or.inl h0) (Or.inl h1) Set.subset_union_right (fun a h=>Or.inl (layer (Or.inl h)))
      nz iden (fun x=>(hbounds x).1) (fun x=>(hbounds x).2.1) (fun x=>(hbounds x).2.2.1) (fun x=>(hbounds x).2.2.2)
  exact relaxB (seq2B sub div) le_rfl Set.subset_union_right (by nlinarith)

private lemma pcxDetLayers {N n : ℕ} {S : Set (Sig N)} (W : ℕ) (M : ℤ)
    (A : (Fin N → Bool) → Matrix (Fin n) (Fin n) ℤ)
    (h0 : (fun _=>false)∈S) (h1 : (fun _=>true)∈S)
    (entries : ∀ i j, pcxSet W (fun x=>A x i j) ⊆ S) (hm : 1≤M) (wide : 2*M^3 < (2:ℤ)^W)
    (nz : ∀ k (hk:k<n) x, pcxPrincipal (A x) hk.le ≠ 0)
    (db : ∀ k (hk:k≤n) x, |pcxPrincipal (A x) hk|≤M)
    (rb : ∀ k (hk:k≤n) i j x, |pcxEntry (A x) hk i j|≤M) :
    Build S (pcxSet W (fun x=>(A x).det)) (n*(n*(n*(78*W^2+48*W)))) := by
  let cost := 78*W^2+48*W
  have layers (k) (hk:k≤n) : Build S (pcxLayer W A hk) (k*(n*(n*cost))) := by
    induction k with
    | zero =>
      rw [Nat.zero_mul]
      apply idleB
      intro a ha
      rcases ha with h|h
      · simp only [pcxInitialPrincipal] at h
        exact pcxConstWires W 1 h0 h1 h
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
        simp only [pcxInitialEntry] at hj
        exact entries i j hj
    | succ k ih =>
      have hprev := ih (Nat.le_of_succ_le hk)
      let Src := S ∪ pcxLayer W A (Nat.le_of_succ_le hk)
      let Cells := fun i j => pcxSet W (fun x=>pcxEntry (A x) hk i j)
      have allCells : Build Src (⋃ i, ⋃ j, Cells i j) (n*(n*cost)) :=
        finB _ (n*cost) (fun i => finB _ cost (fun j =>
          pcxDetCellB W M A hk i j (Or.inl h0) (Or.inl h1) Set.subset_union_right hm wide
            (nz k hk) (db k _) (rb (k+1) hk i j)))
      have step : Build Src (pcxLayer W A hk) (n*(n*cost)) := by
        apply relaxB allCells le_rfl _ le_rfl
        intro a ha
        rcases ha with h|h
        · simp only [pcxNextPrincipal] at h
          exact Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨k,hk⟩,Set.mem_iUnion.mpr ⟨⟨k,hk⟩,h⟩⟩)))
        · exact Or.inr h
      exact relaxB (seq2B hprev step) le_rfl Set.subset_union_right (by rw [Nat.succ_mul])
  apply relaxB (layers n le_rfl) le_rfl _ le_rfl
  intro a ha
  exact Or.inr (Or.inl ha)

end Pcx446Arithmetic

namespace BoundaryPin
open BoundarySwitch BoundaryPadding Finset

abbrev Src (n : ℕ) := Fin n → ZMod 2
def listSrc {X : Type*} {n : ℕ} (f : X → Src n) (l : List X) := (l.map f).sum
theorem eraseSrc {X : Type*} {n : ℕ} (f : X → Src n) (l : List X) (i : Fin l.length) :
    f l[i.val] + listSrc f (l.eraseIdx i.val) = listSrc f l := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [listSrc]
    · simpa [listSrc,add_left_comm] using congrArg (fun a => f x + a) (ih j)

def PlanarRec {n t : ℕ} (pin : Fin t → Fin n) (M : Src n → ℤ) : Prop :=
  ∀ {h : ℕ} [NeZero h] (sel : Fin h ↪o Fin t),
    let q := fun i => edgeSource (pin (sel i))
    let S := ∑ i, q i
    M 0 * M S = ∑ j ∈ univ.erase (0 : Fin h), -(-1:ℤ)^j.val *
      (M (q j-q 0) * M (S-(q j-q 0)))

theorem listRec {n t : ℕ} {X : Type*} (pin : Fin t → Fin n) (M : Src n → ℤ)
    (recM : PlanarRec pin M) (site : X → Fin t) (x : X) (xs : List X)
    (ord : (x::xs).Pairwise (fun i j => site i < site j)) :
    let f := fun y => edgeSource (pin (site y))
    M 0 * M (listSrc f (x::xs)) =
      ∑ i : Fin xs.length, (-1:ℤ)^i.val *
        (M (f xs[i.val] - f x) * M (listSrc f (xs.eraseIdx i.val))) := by
  classical
  let f := fun y => edgeSource (pin (site y))
  let sel : Fin (xs.length+1) ↪o Fin t :=
    OrderEmbedding.ofStrictMono (fun i : Fin (xs.length+1) => site ((x::xs).get i))
      (fun i j hij => List.pairwise_iff_get.mp ord i j hij)
  have hs : (∑ i, edgeSource (pin (sel i))) = listSrc f (x::xs) := by
    change (∑ i : Fin (x::xs).length, f ((x::xs).get i)) = _
    rw [←List.sum_ofFn]
    change (List.ofFn (f ∘ (x::xs).get)).sum = _
    rw [←List.map_ofFn]
    simp [listSrc]
  have r := recM sel
  dsimp only at r ⊢
  rw [hs,Finset.sum_erase_eq_sub (s := (univ : Finset (Fin (xs.length+1)))) (by simp),
    Fin.sum_univ_succ] at r
  simp only [add_sub_cancel_left, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_neg] at r
  refine r.trans ?_
  apply sum_congr rfl
  intro i _
  have he := eraseSrc f xs i
  have hn : - f x = f x := by
    funext j
    change - (f x j) = f x j
    rcases binary (f x j) with h|h <;> rw [h] <;> decide
  have hr : listSrc f (x::xs) - (f xs[i.val]-f x) = listSrc f (xs.eraseIdx i.val) := by
    change f x + listSrc f xs - (f xs[i.val]-f x) = _
    rw [←he,sub_eq_add_neg (f xs[i.val]),hn]
    abel
  change _ * (M (f xs[i.val]-f x) * M (listSrc f (x::xs) - (f xs[i.val]-f x))) = _
  rw [hr]
end BoundaryPin
namespace BoundaryPin
open BoundaryPadding BoundarySwitch Finset
def ratio {n : ℕ} (M : Src n → ℤ) (s : Src n) : ℚ := (M s : ℚ) / M 0

theorem wickGraph {n t : ℕ} {X : Type*} (pin : Fin t → Fin n) (M : Src n → ℤ)
    (recM : PlanarRec pin M) (hz : M 0 ≠ 0) (site : X → Fin t) (l : List X)
    (ord : l.Pairwise (fun i j => site i < site j)) :
    let f := fun x => edgeSource (pin (site x))
    ratio M (listSrc f l) = pf (fun i j => ratio M (f j-f i)) l := by
  let f := fun x => edgeSource (pin (site x))
  change (fun l => ratio M (listSrc f l)) l = _
  apply wick_of_rec (fun ys => ratio M (listSrc f ys)) (fun i j => ratio M (f j-f i)) l
  · simp [ratio,listSrc,hz]
  · intro x xs hsub
    rw [co_indices]
    have h := listRec pin M recM site x xs (ord.sublist hsub)
    dsimp only at h
    have hh : (M 0 : ℚ) * M (listSrc f (x::xs)) =
      ∑ i : Fin xs.length, (-1:ℚ)^i.val *
        ((M (f xs[i.val]-f x):ℚ)* M (listSrc f (xs.eraseIdx i.val))) := by
      exact_mod_cast h
    have hq : (M 0 : ℚ) ≠ 0 := by exact_mod_cast hz
    calc
      _ = ((M 0 : ℚ)* M (listSrc f (x::xs))) / (M 0 : ℚ)^2 := by
        simp only [ratio]; field_simp
      _ = _ := by
        rw [hh,Finset.sum_div]
        apply sum_congr rfl
        intro i _
        simp only [ratio]
        ring
end BoundaryPin
namespace BoundaryPin
open BoundaryPadding BoundarySwitch Finset

theorem pf_dead {X : Type*} (a : X → X → ℚ) (z : X)
    (hrow : ∀ x, a z x = 0) (hcol : ∀ x, a x z = 0) (l : List X) (hz : z ∈ l) :
    pf a l = 0 := by
  cases l with
  | nil => simp at hz
  | cons x xs =>
    rw [pf_step,co_indices]
    apply sum_eq_zero
    intro i _
    rcases List.mem_cons.mp hz with rfl|hh
    · simp [hrow]
    · have hm := (List.getElem_cons_eraseIdx_perm (l:=xs) i.isLt).mem_iff.mpr hh
      rcases List.mem_cons.mp hm with hi|he
      · simp [←hi,hcol]
      · rw [pf_dead a z hrow hcol (xs.eraseIdx i.val) he,mul_zero]
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]

theorem spinMonom {n m : ℕ} {X : Type*} (u v : Fin m → Fin n)
    (w : Fin m → Bool → ℤ) (f : X → Fin n) (l : List X) :
    (spin u v (fun e b => w e (bitEquiv.symm b)) (listSrc (fun y => edgeSource (f y)) l) : ℚ) =
      ∑ x : Fin n → Bool, (rawIsing u v w x : ℚ) * monom (fun y => spinSign (x (f y))) l := by
  rw [spinBool]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  have hm (ys : List X) : (sgn (dot (listSrc (fun y => edgeSource (f y)) ys)
      (fun j => bitVal (x j))) : ℚ) = monom (fun y => spinSign (x (f y))) ys := by
    induction ys with
    | nil => simp [listSrc,dot,sgn,monom]
    | cons y ys ih =>
      change (sgn (dot (edgeSource (f y) + listSrc _ ys) _) : ℚ) = _
      rw [dot_add,sgn_add,dotSite,Int.cast_mul,ih]
      have hb : (sgn (bitVal (x (f y))) : ℚ) = spinSign (x (f y)) := by
        cases x (f y) <;> decide
      simp [hb,monom]
  rw [hm,mul_comm]

end BoundaryPin
namespace BoundaryPin
open BoundaryPadding BoundarySwitch Finset
def atSite {t : ℕ} [NeZero t] (z : MaskLabel (Fin t)) : Fin t := z.1.elim 0 Prod.fst
def kernel {n t : ℕ} [NeZero t] (pin : Fin t → Fin n) (M : Src n → ℤ)
    (i j : MaskLabel (Fin t)) : ℚ :=
  if i.1.isSome && j.1.isSome then
    ratio M (edgeSource (pin (atSite j)) - edgeSource (pin (atSite i))) else 0

theorem pf_congr {X : Type*} (a b : X → X → ℚ) (l : List X)
    (hab : ∀ x ∈ l, ∀ y ∈ l, a x y = b x y) : pf a l = pf b l := by
  apply wick_of_rec (pf a) b l (by rw [pf])
  intro x xs h
  rw [pf_step,co_indices,co_indices]
  apply sum_congr rfl
  intro i _
  rw [hab x (h.subset (by simp)) _ (h.subset (List.mem_cons_of_mem _ (List.getElem_mem i.isLt)))]

theorem realOrder {t : ℕ} [NeZero t] (ps : List (Fin t × Bool))
    (ho : ps.Pairwise (fun i j => i.1 < j.1)) (l : List (MaskLabel (Fin t)))
    (hl : l.Sublist (padded ps).zipIdx) (hr : ∀ z ∈ l, z.1.isSome = true) :
    l.Pairwise (fun i j => atSite i < atSite j) := by
  let raw (z : MaskLabel (Fin t)) : Fin t × Bool := z.1.getD (0,false)
  have hraw (z) (hz : z ∈ l) : z.1 = some (raw z) := by
    have hh := hr z hz
    obtain ⟨o,k⟩ := z
    cases o <;> simp_all [raw]
  have sub := (hl.map Prod.fst).filterMap id
  rw [List.zipIdx_map_fst] at sub
  have drop : (padded ps).filterMap id = ps := by
    unfold padded
    split <;> simp [List.filterMap_append,List.filterMap_map]
  rw [drop,List.filterMap_map] at sub
  have heq : l.filterMap (id ∘ Prod.fst) = l.map raw :=
    List.filterMap_eq_map_iff_forall_eq_some.mpr hraw
  rw [heq] at sub
  have hw := List.pairwise_map.mp (ho.sublist sub)
  exact (List.pairwise_iff_get.mpr (fun i j hij => by
    have h := List.pairwise_iff_get.mp hw i j hij
    have hi := hraw (l.get i) (List.get_mem ..)
    have hj := hraw (l.get j) (List.get_mem ..)
    simpa only [atSite,hi,hj,Option.elim_some] using h))

theorem massGraph {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (pin : Fin t → Fin n)
    (w : Fin m → Bool → ℤ) (ps : List (Fin t × Bool)) (ord : ps.Pairwise (fun i j => i.1 < j.1))
    (recM : PlanarRec pin (spin u v (fun e b => w e (bitEquiv.symm b))))
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 ≠ 0) :
    let M := spin u v (fun e b => w e (bitEquiv.symm b))
    (2:ℚ)^ps.length * (∑ x : Fin n → Bool,
      if ps.all (fun p => x (pin p.1) == p.2) then (rawIsing u v w x : ℚ)/M 0 else 0) =
      pf (padK (kernel pin M) maskV) (padded ps).zipIdx := by
  classical
  let M := spin u v (fun e b => w e (bitEquiv.symm b))
  apply mask_histogram_pf univ (fun x => (rawIsing u v w x : ℚ)/M 0)
    (fun x i => x (pin i)) ps (kernel pin M)
  intro l hl
  by_cases hr : ∀ z ∈ l, z.1.isSome = true
  · have he (x : Fin n → Bool) : monom (maskSpin (fun i => x (pin i))) l =
        monom (fun i => spinSign (x (pin (atSite i)))) l := by
      unfold monom
      congr 1
      apply List.map_congr_left
      intro z hz
      have := hr z hz
      obtain ⟨o,k⟩ := z
      cases o <;> simp_all [maskSpin,atSite]
    let f := fun z : MaskLabel (Fin t) => edgeSource (pin (atSite z))
    calc
      _ = ratio M (listSrc f l) := by
        simp_rw [he,div_mul_eq_mul_div]
        rw [←Finset.sum_div]
        unfold ratio
        rw [spinMonom u v w (fun z => pin (atSite z)) l]
      _ = pf (fun i j => ratio M (f j-f i)) l :=
        wickGraph pin M recM hz atSite l (realOrder ps ord l hl hr)
      _ = _ := by
        apply pf_congr
        intro i hi j hj
        simp [kernel,hr i hi,hr j hj,f]
  · push Not at hr
    obtain ⟨z,hz,hz'⟩ := hr
    have hnone : z.1 = none := by cases h : z.1 <;> simp_all
    rw [pf_dead (kernel pin M) z (by simp [kernel,hnone]) (by simp [kernel,hnone]) l hz]
    apply sum_eq_zero
    intro x _
    have hmon : (0:ℚ) ∈ l.map (maskSpin (fun i => x (pin i))) :=
      List.mem_map.mpr ⟨z,hz,by simp [maskSpin,hnone]⟩
    simp [monom, List.prod_eq_zero hmon]

end BoundaryPin
namespace BoundaryPin
open BoundaryPadding BoundarySwitch Finset
def falsePair {n m t : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (i j : Fin t) : ℤ :=
  ∑ x : Fin n → Bool, if x (pin i)=false ∧ x (pin j)=false then rawIsing u v w x else 0
def observedMat {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (Z : ℤ) (i j : MaskLabel (Fin t)) : ℚ :=
  Z + (-maskV i)*(maskV j*(if i.1.isSome && j.1.isSome then
    (4:ℚ)*falsePair u v w pin (atSite j) (atSite i) - Z else 0))

theorem observedPinMass {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (pin : Fin t → Fin n)
    (w : Fin m → Bool → ℤ) (ps : List (Fin t × Bool)) (ord : ps.Pairwise (fun i j => i.1 < j.1))
    (recM : PlanarRec pin (spin u v (fun e b => w e (bitEquiv.symm b))))
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 ≠ 0) :
    let Z := spin u v (fun e b => w e (bitEquiv.symm b)) 0
    let W : ℤ := ∑ x : Fin n → Bool,
      if ps.all (fun p => x (pin p.1) == p.2) then rawIsing u v w x else 0
    (2:ℚ)^ps.length * (Z:ℚ)^((padded ps).length/2) * W =
      (Z:ℚ) * pf (observedMat u v w pin Z) (padded ps).zipIdx := by
  classical
  let M := spin u v (fun e b => w e (bitEquiv.symm b))
  let Z := M 0
  let W : ℤ := ∑ x : Fin n → Bool,
    if ps.all (fun p => x (pin p.1) == p.2) then rawIsing u v w x else 0
  change _ = (Z:ℚ) * pf _ _
  have hn : (Z:ℚ) ≠ 0 := by exact_mod_cast hz
  have heq : observedMat u v w pin Z = fun i j => (Z:ℚ) * padK (kernel pin M) maskV i j := by
    funext i j
    unfold observedMat padK kernel
    by_cases h : (i.1.isSome && j.1.isSome) = true
    · rw [ite_eq_left h,ite_eq_left h]
      have hobs := (observablesAtGrid u v w (pin (atSite j)) (pin (atSite i))).2
      change Z + M (edgeSource (pin (atSite j))-edgeSource (pin (atSite i))) =
        4 * falsePair u v w pin (atSite j) (atSite i) at hobs
      have hc : (Z:ℚ) + M (edgeSource (pin (atSite j))-edgeSource (pin (atSite i))) =
        4 * (falsePair u v w pin (atSite j) (atSite i):ℚ) := by exact_mod_cast hobs
      unfold ratio
      change _ = (Z:ℚ) * (1 + -maskV i * (maskV j * (_ / (Z:ℚ))))
      rw [←hc]
      field_simp
      ring
    · rw [ite_eq_right h,ite_eq_right h]
      ring
  have hm := massGraph u v pin w ps ord recM hz
  change (2:ℚ)^ps.length * (∑ x : Fin n → Bool, if
    ps.all (fun p => x (pin p.1) == p.2) then (rawIsing u v w x : ℚ)/Z else 0) = _ at hm
  have hW : (∑ x : Fin n → Bool, if ps.all (fun p => x (pin p.1) == p.2)
      then (rawIsing u v w x : ℚ)/Z else 0) = (W:ℚ)/Z := by
    unfold W
    push_cast
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro x _
    split <;> simp
  rw [hW] at hm
  rw [heq,pf_scale _ _ _ (by simpa using padded_even ps),List.length_zipIdx]
  rw [←hm]
  change (2:ℚ)^ps.length * (Z:ℚ)^((padded ps).length/2) * (W:ℚ) = _
  field_simp
end BoundaryPin
namespace BoundaryPin
open Finset BoundarySwitch BoundaryPadding
theorem planarObservedPinMass {n m t l : ℕ} [NeZero t] (u v : Fin m → Fin n) (pin : Fin t ↪ Fin n)
    (noLoop : ∀ e, u e ≠ v e)
    (connected : ∀ i j, Relation.ReflTransGen (fun x y => ∃ e, (u e=x ∧ v e=y) ∨ (u e=y ∧ v e=x)) i j)
    (src dst : Fin l → Option (Fin n)) (rot rev : Equiv.Perm (Fin l)) (sp : Fin t → Fin l)
    (uniq : Function.Injective (fun d => (src d,dst d)))
    (support : ∀ x y : Option (Fin n),
      x.elim (y.elim false (fun i => decide (∃ j, pin j=i)))
        (fun i => y.elim (decide (∃ j,pin j=i))
          (fun j => decide (∃ e : Fin m, (u e=i ∧ v e=j) ∨ (u e=j ∧ v e=i)))) = true ↔
      ∃ d, src d=x ∧ dst d=y)
    (revrot : ∀ d, src (rev d)=dst d ∧ dst (rev d)=src d ∧ src (rot d)=src d)
    (localCycle : ∀ d e, src d=src e → ∃ j : ℕ, (rot^j) d=e)
    (spoke : ∀ i, src (sp i)=none ∧ dst (sp i)=some (pin i) ∧
      ∀ j : Fin t, j.val=(i.val+1)%t → rot (sp i)=sp j)
    (euler : 2*(n+1) + 2*((Finset.univ : Finset (Fin l)).image
      (fun d => (Finset.range l).image (fun j => (fun k => rot (rev k))^[j] d))).card = 4+l)
    (w : Fin m → Bool → ℤ) (ps : List (Fin t × Bool)) (ord : ps.Pairwise (fun i j => i.1 < j.1))
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 ≠ 0) :
    let Z := spin u v (fun e b => w e (bitEquiv.symm b)) 0
    let W : ℤ := ∑ x : Fin n → Bool,
      if ps.all (fun p => x (pin p.1) == p.2) then rawIsing u v w x else 0
    (2:ℚ)^ps.length * (Z:ℚ)^((padded ps).length/2) * W =
      (Z:ℚ) * pf (observedMat u v w pin Z) (padded ps).zipIdx := by
  apply observedPinMass u v pin w ps ord _ hz
  intro h inst sel
  exact planarSpinRecurrence u v pin noLoop connected src dst rot rev sp uniq support
    revrot localCycle spoke euler sel (fun e b => w e (bitEquiv.symm b))

theorem zeroPinMass {n m t : ℕ} (u v : Fin m → Fin n) (pin : Fin t → Fin n)
    (w : Fin m → Bool → ℤ) (hw : ∀ e b, 0 ≤ w e b) (ps : List (Fin t × Bool))
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 = 0) :
    (∑ x : Fin n → Bool, if ps.all (fun p => x (pin p.1) == p.2) then rawIsing u v w x else 0) = 0 := by
  classical
  rw [spinBool] at hz
  simp [dot,sgn] at hz
  have hn (x : Fin n → Bool) : 0 ≤ rawIsing u v w x := prod_nonneg (fun _ _ => hw ..)
  have he := Finset.sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ univ) => hn x)
  apply sum_eq_zero
  intro x hx
  rw [(he.mp hz) x hx]
  simp
end BoundaryPin

namespace Pcx446Arithmetic

private def pcxExponent (n L : ℕ) := (n+1)*(n+1+L)
private def pcxDetShiftBits (n L : ℕ) := pcxExponent n L + 2
private def pcxDetWork (n L : ℕ) := 3*pcxExponent n (pcxDetShiftBits n L+1)+2

private lemma pcxMinorBound {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (L : ℕ)
    (entries : ∀ i j, |A i j| ≤ (2:ℤ)^L) (hk : k≤n+1) (r c : Fin k→Fin n) :
    |pcxMinor A r c| ≤ (2:ℤ)^(pcxExponent n L) := by
  have bound : k*(k+L) ≤ pcxExponent n L := Nat.mul_le_mul hk (by omega)
  exact (pcxDetBound k L (A.submatrix r c) (fun i j=>entries (r i) (c j))).trans
    (pow_le_pow_right₀ (by norm_num) bound)

private lemma pcxPositivePivot {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (q b : ℤ)
    (nonneg : 0≤b) (large : ((n:ℤ)+1)*b < q) (entries : ∀ i j, |A i j| ≤ b)
    (hk : k≤n) : pcxPrincipal (A + q • 1) hk ≠ 0 := by
  let f := Int.castRingHom ℝ
  let inj : Fin k ↪ Fin n := ⟨Fin.castLE hk,fun a b h => Fin.ext (congrArg (fun x : Fin n=>x.val) h)⟩
  have nz := pcxShiftPrincipals n (q:ℝ) (b:ℝ) (A.map f) (by exact_mod_cast nonneg)
    (by exact_mod_cast large) (fun i j=>by change |(A i j:ℝ)| ≤ (b:ℝ);exact_mod_cast entries i j) k inj
  intro he
  apply nz
  have castEq := congrArg f he
  change f ((A + q • 1).submatrix inj inj).det = f 0 at castEq
  rw [RingHom.map_det,map_zero] at castEq
  convert castEq using 2
  ext i j
  change f (A (inj i) (inj j)) + (q:ℝ) * (1 : Matrix _ _ ℝ) (inj i) (inj j) =
    f (A (inj i) (inj j) + q * (1 : Matrix _ _ ℤ) (inj i) (inj j))
  by_cases eq : inj i = inj j <;> simp [Matrix.one_apply,eq,f]

private lemma pcxLowSet {N : ℕ} (S W : ℕ) (h : S≤W) (F : (Fin N→Bool)→ℤ) :
    pcxSet S F ⊆ pcxSet W F := by
  rintro a ⟨i,rfl⟩
  refine ⟨⟨i.val,by omega⟩,?_⟩
  funext x
  have e : pcxWord W (F x) % 2^S = pcxWord S (F x) := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_mod,pcxWord,pcxWord,ZMod.val_intCast,ZMod.val_intCast]
    push_cast
    apply Int.emod_emod_of_dvd
    exact pow_dvd_pow _ h
  change (pcxWord W (F x)).testBit i.val = (pcxWord S (F x)).testBit i.val
  rw [← e,Nat.testBit_mod_two_pow]
  simp [i.isLt]

private lemma pcxShiftGate {N n : ℕ} {S : Set (Sig N)} (L : ℕ)
    (A : (Fin N→Bool)→ Matrix (Fin n) (Fin n) ℤ)
    (bound : ∀ x i j, |A x i j| ≤ (2:ℤ)^L)
    (h0 : (fun _=>false)∈S) (h1 : (fun _=>true)∈S)
    (entry : ∀ i j, pcxSet (pcxDetWork n L) (fun x=>A x i j) ⊆ S) :
    let T := pcxDetShiftBits n L
    let W := pcxDetWork n L
    Build S (pcxSet T (fun x=>(A x).det)) (n*(n*(9*W)) + n*(n*(n*(78*W^2+48*W)))) := by
  let T := pcxDetShiftBits n L
  let W := pcxDetWork n L
  let Q : ℤ := 2^T
  let B := fun x => A x + Q • 1
  let E := pcxExponent n (T+1)
  let M : ℤ := 2^E
  have hEL : n+1+L+1 ≤ T := by dsimp [T,pcxDetShiftBits,pcxExponent]; nlinarith
  have hTW : T ≤ W := by
    change T ≤ 3*((n+1)*(n+1+(T+1)))+2
    nlinarith [Nat.zero_le (n*T),Nat.zero_le (n*n)]
  have qb : (2:ℤ)^L ≤ Q := pow_le_pow_right₀ (by norm_num) (by omega)
  have large : ((n:ℤ)+1)*(2:ℤ)^L < Q := by
    calc
      _ ≤ (2:ℤ)^(n+1) * (2:ℤ)^L := by
        gcongr
        exact_mod_cast (Nat.lt_two_pow_self (n:=n+1)).le
      _ < _ := by rw [←pow_add]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have be (x) (i j : Fin n) : |B x i j| ≤ (2:ℤ)^(T+1) := by
    change |A x i j + Q*(1 : Matrix (Fin n) (Fin n) ℤ) i j| ≤ _
    by_cases eq : i=j
    · subst j; simp only [Matrix.one_apply_eq,mul_one, pow_succ]
      have := (abs_le.mp (bound x i i)).1
      have := (abs_le.mp (bound x i i)).2
      change |A x i i + Q| ≤ Q*2
      exact abs_le.mpr ⟨by omega,by omega⟩
    · simp [Matrix.one_apply,eq,pow_succ]
      have ourBound := bound x i j
      change |A x i j| ≤ Q*2
      apply (ourBound.trans qb).trans
      have q0 : 0≤Q := by dsimp [Q]; positivity
      omega
  have ready : Build S (⋃ i, ⋃ j, pcxSet W (fun x=> B x i j)) (n*(n*(9*W))) := by
    apply finB _ (n*(9*W))
    intro i
    apply finB _ (9*W)
    intro j
    exact pcxSumWordB W (fun x=>A x i j) (fun _=> Q*(1:Matrix (Fin n) (Fin n) ℤ) i j)
      h0 (entry i j) (pcxConstWires W _ h0 h1)
  have big : 2*M^3 < (2:ℤ)^W := by
    dsimp only [M,W,pcxDetWork,E,T]
    rw [←pow_mul,show 2*(2:ℤ)^(pcxExponent n (pcxDetShiftBits n L+1)*3) =
      (2:ℤ)^(pcxExponent n (pcxDetShiftBits n L+1)*3+1) by rw [pow_succ,mul_comm]]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have nodes := pcxDetLayers (S:=S ∪ ⋃ i, ⋃ j, pcxSet W (fun x=>B x i j)) W M B
    (Or.inl h0) (Or.inl h1) (fun i j a ha=>Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,ha⟩⟩))
    (by exact one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2)) big
    (fun k hk x=>pcxPositivePivot (A x) Q ((2:ℤ)^L) (by positivity) large (bound x) hk.le)
    (fun k hk x=>pcxMinorBound _ _ (be x) (by omega) _ _)
    (fun k hk i j x=>pcxMinorBound _ _ (be x) (by omega) _ _)
  have eq : pcxSet T (fun x=>(A x).det) = pcxSet T (fun x=>(B x).det) := by
    unfold pcxSet; congr 2; funext x; unfold pcxWord
    apply congrArg ZMod.val
    exact (pcxDetShift n (2^T) (A x)).symm
  apply relaxB (seq2B ready nodes) le_rfl _ le_rfl
  rw [eq]
  exact (pcxLowSet T W hTW _).trans Set.subset_union_right

end Pcx446Arithmetic

namespace Pcx446Arithmetic

structure PcxLayout (X : Type) where
  size : ℕ
  pos : X ≃ Fin size

def pcxLeaf (n : ℕ) : PcxLayout (Fin n) := ⟨n,Equiv.refl _⟩

def pcxCat {X Y : Type} (A : PcxLayout X) (B : PcxLayout Y) : PcxLayout (X⊕Y) :=
  ⟨A.size+B.size,(Equiv.sumCongr A.pos B.pos).trans finSumFinEquiv⟩

def pcxGroup {X : Type} (n : ℕ) (A : PcxLayout X) : PcxLayout (Fin n × X) :=
  ⟨n*A.size,(Equiv.prodCongr (Equiv.refl _) A.pos).trans finProdFinEquiv⟩

def pcxVec {X V : Type} (A : PcxLayout X) (f : X → V) := List.ofFn (fun i => f (A.pos.symm i))

lemma pcxCatVec {X Y V : Type} (A : PcxLayout X) (B : PcxLayout Y) (f : X⊕Y→V) :
    pcxVec (pcxCat A B) f = pcxVec A (fun x=>f (.inl x)) ++ pcxVec B (fun y=>f (.inr y)) := by
  unfold pcxVec pcxCat
  rw [List.ofFn_add]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> simp
  change f (Sum.map A.pos.symm B.pos.symm (finSumFinEquiv.symm (Fin.castAdd B.size i))) = _
  simp

lemma pcxGroupVec {X V : Type} (n : ℕ) (A : PcxLayout X) (f : Fin n × X→V) :
    pcxVec (pcxGroup n A) f = (List.ofFn (fun i => pcxVec A (fun x=>f (i,x)))).flatten := by
  unfold pcxVec pcxGroup
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn;funext i
  apply congrArg List.ofFn;funext j
  have h : ∀ (hn : i.val*A.size+j.val<n*A.size),
      (⟨i.val*A.size+j.val,hn⟩ : Fin (n*A.size)) = finProdFinEquiv (i,j) := by
    intro hn;ext;dsimp [finProdFinEquiv];ring
  simp [h]

def pcxGrid (s d : ℕ) := pcxGroup s (pcxGroup s (pcxGroup s (pcxLeaf d)))
def pcxPairGrid (t s d : ℕ) := pcxGroup t (pcxGroup t (pcxGrid s d))

def pcxFrame (t s d : ℕ) :=
  pcxCat (pcxCat (pcxCat (pcxCat (pcxCat (pcxCat (pcxCat (pcxCat
    (pcxLeaf 2) (pcxGrid s d)) (pcxPairGrid t s d)) (pcxGroup t (pcxLeaf 2)))
    (pcxGroup t (pcxLeaf t))) (pcxLeaf s)) (pcxLeaf s)) (pcxLeaf s)) (pcxLeaf d)

lemma pcxFrameSize (t s d : ℕ) : (pcxFrame t s d).size =
    2+(1+t*t)*s^3*d+2*t+t*t+3*s+d := by
  dsimp [pcxFrame,pcxGrid,pcxPairGrid,pcxGroup,pcxLeaf,pcxCat];ring

def pcxDomain {X : Type} (_ : PcxLayout X) := X

def pcxFrameValues {t s d : ℕ}
    (Z : Fin s→Fin s→Fin s→Fin d→Bool) (H : Fin t→Fin t→Fin s→Fin s→Fin s→Fin d→Bool)
    (mask : Fin t→Bool→Bool) (ord : Fin t→Fin t→Bool) (a y z : Fin s→Bool) (idx : Fin d→Bool) : pcxDomain (pcxFrame t s d) → Bool :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim
    (fun i : Fin 2 => decide (i.val=1)) (fun ⟨i,j,k,b⟩=>Z i j k b))
    (fun ⟨i,j,l,r,h,b⟩=>H i j l r h b)) (fun ⟨i,b⟩=>mask i (decide (b.val=1))))
    (fun ⟨i,j⟩=>ord i j)) a) y) z) idx

def pcxGridList {s d : ℕ} (f : Fin s→Fin s→Fin s→Fin d→Bool) :=
  (List.ofFn (fun i=> (List.ofFn (fun j=> (List.ofFn (fun k=>List.ofFn (f i j k))).flatten)).flatten)).flatten

lemma pcxFrameList {t s d : ℕ}
    (Z : Fin s→Fin s→Fin s→Fin d→Bool) (H : Fin t→Fin t→Fin s→Fin s→Fin s→Fin d→Bool)
    (mask : Fin t→Bool→Bool) (ord : Fin t→Fin t→Bool) (a y z : Fin s→Bool) (idx : Fin d→Bool) :
    pcxVec (pcxFrame t s d) (pcxFrameValues Z H mask ord a y z idx) =
      [false,true] ++ pcxGridList Z ++
        (List.ofFn (fun i=>(List.ofFn (fun j=>pcxGridList (H i j))).flatten)).flatten ++
        (List.ofFn (fun i=>[mask i false,mask i true])).flatten ++
        (List.ofFn (fun i=>List.ofFn (ord i))).flatten ++ List.ofFn a ++ List.ofFn y ++ List.ofFn z ++ List.ofFn idx := by
  simp only [pcxFrame,pcxCatVec,pcxGrid,pcxPairGrid,pcxGroupVec,pcxFrameValues,Sum.elim_inl,Sum.elim_inr,pcxGridList]
  rfl

def pcxBitsRead : (d : ℕ) → (Fin d → Bool) → ℕ
  | 0, _ => 0
  | d+1,b => Nat.bit (b 0) (pcxBitsRead d (fun i => b i.succ))

lemma pcxBitsRead_test (d : ℕ) (b : Fin d→Bool) (i : Fin d) :
    (pcxBitsRead d b).testBit i.val = b i := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j=>?_) i
    · exact Nat.testBit_bit_zero _ _
    · exact (Nat.testBit_bit_succ j.val _ _).trans (ih _ j)

lemma pcxBitsRead_lt (d : ℕ) (b : Fin d→Bool) : pcxBitsRead d b < 2^d := by
  induction d with
  | zero => simp [pcxBitsRead]
  | succ d ih =>
    rw [pcxBitsRead,Nat.bit_val,pow_succ]
    have := ih (fun i=>b i.succ)
    have hb : (b 0).toNat≤1 := by cases b 0 <;> decide
    omega

def pcxAddress (t s d : ℕ) (key : pcxDomain (pcxFrame t s d)) :
    Fin (2+(1+t*t)*s^3*d+2*t+t*t+3*s+d) :=
  Fin.cast (pcxFrameSize t s d) ((pcxFrame t s d).pos key)

def pcxBitsAt {N : ℕ} (L : ℕ) (ix : Fin L → Fin N) (x : Fin N→Bool) : ℕ :=
  pcxBitsRead L (fun i=>x (ix i))

lemma pcxBitsAt_gate {N L : ℕ} (ix : Fin L→Fin N) (j : Fin L) :
    bitsOf L (pcxBitsAt L ix) j = (fun x=>x (ix j)) := by
  funext x; exact pcxBitsRead_test _ _ _

def pcxInputData (t s d : ℕ) (key : pcxDomain (pcxFrame t s d)) : Sig (2+(1+t*t)*s^3*d+2*t+t*t+3*s+d) :=
  fun x => x (pcxAddress t s d key)

def pcxInputKey {t s d : ℕ} (q : Fin s × Fin s × Fin s × Fin d) :
    pcxDomain (pcxFrame t s d) :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr q)))))))

def pcxPairKey {t s d : ℕ} (i j : Fin t) (q : Fin s × Fin s × Fin s × Fin d) :
    pcxDomain (pcxFrame t s d) :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inr (i,j,q)))))))

def pcxMaskKey {t s d : ℕ} (i : Fin t) (b : Bool) : pcxDomain (pcxFrame t s d) :=
  .inl (.inl (.inl (.inl (.inl (.inr (i,⟨b.toNat,by cases b <;> decide⟩))))))

def pcxOrderKey {t s d : ℕ} (i j : Fin t) : pcxDomain (pcxFrame t s d) :=
  .inl (.inl (.inl (.inl (.inr (i,j)))))

def pcxGridCode {s : ℕ} (l r h : Fin s) : ℕ := l.val*s*s+r.val*s+h.val

lemma pcxGridPos {s d : ℕ} (l r h : Fin s) (j : Fin d) :
    ((pcxGrid s d).pos (l,r,h,j)).val = d*pcxGridCode l r h+j.val := by
  change j.val+d*h.val+(s*d)*r.val+(s*(s*d))*l.val = _
  unfold pcxGridCode;ring

def pcxGridPack {s d : ℕ} (f : Fin s × Fin s × Fin s × Fin d → Bool) :=
  pcxBitsRead (pcxGrid s d).size (fun j => f ((pcxGrid s d).pos.symm j))

lemma pcxGridPack_read {s d : ℕ} (f : Fin s × Fin s × Fin s × Fin d → Bool) (l r h : Fin s) (j : Fin d) :
    (pcxGridPack f).testBit (d*pcxGridCode l r h+j.val) = f (l,r,h,j) := by
  rw [←pcxGridPos l r h j]
  unfold pcxGridPack
  rw [pcxBitsRead_test]; simp

lemma pcxGridPack_width {s d : ℕ} (f : Fin s × Fin s × Fin s × Fin d → Bool) :
    pcxGridPack f < 2^(s^3*d) := by
  have h := pcxBitsRead_lt (pcxGrid s d).size (fun j=>f ((pcxGrid s d).pos.symm j))
  have e : (pcxGrid s d).size = s^3*d := by dsimp [pcxGrid,pcxGroup,pcxLeaf];ring
  simpa only [pcxGridPack,e] using h

lemma pcxGridPack_sum {s d : ℕ} (c : Fin s → Fin s → Fin s → ℕ)
    (hc : ∀ l r h, c l r h < 2^d) :
    pcxGridPack (fun q : Fin s × Fin s × Fin s × Fin d => (c q.1 q.2.1 q.2.2.1).testBit q.2.2.2.val) =
      ∑ l, ∑ r, ∑ h, c l r h * 2^(d*pcxGridCode l r h) := by
  let A := pcxGrid s d
  let data := fun q : Fin s × Fin s × Fin s × Fin d => (c q.1 q.2.1 q.2.2.1).testBit q.2.2.2.val
  let z := pcxGridPack data
  have hz : z < 2^A.size := pcxBitsRead_lt _ _
  change z = _
  rw [←decode z A.size hz,←Equiv.sum_comp A.pos]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl;intro r _
  apply Finset.sum_congr rfl;intro h _
  change (∑ j : Fin d, ((pcxGridPack data).testBit (((pcxGrid s d).pos (l,r,h,j)).val)).toNat *
    2^(((pcxGrid s d).pos (l,r,h,j)).val)) = _
  simp_rw [pcxGridPos,pcxGridPack_read]
  calc
    _ = (∑ j : Fin d, ((c l r h).testBit j.val).toNat*2^j.val) * 2^(d*pcxGridCode l r h) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _
      dsimp [data];rw [pow_add];ring
    _ = _ := by rw [decode _ _ (hc l r h)]

end Pcx446Arithmetic

namespace BoundaryDet
open BoundaryPadding Finset

variable {X : Type*}

theorem co_anti (k g : X → ℚ) (l : List X) (m : Moment X) :
    co k l (coFun g m) + co g l (coFun k m) = 0 := by
  induction l generalizing m with
  | nil => simp [co]
  | cons x xs ih =>
    have he (a : X → ℚ) : consAt x (coFun a m) =
        (a x) • m + (-1:ℚ) • coFun a (consAt x m) := by
      funext t
      simp [consAt,coFun,co,sub_eq_add_neg]
    simp only [co,he,co_add_m,co_smul_m]
    change k x * co g xs m - _ + (g x * co k xs m - _) = 0
    linarith [ih (consAt x m)]

theorem co_swap (k : X → ℚ) (m : Moment X) (p : List X) (a b : X) (s : List X)
    (h : ∀ q r : List X, q.length + r.length + 1 = p.length+s.length →
      m (q++a::b::r) = -m (q++b::a::r)) :
    co k (p++a::b::s) m = -co k (p++b::a::s) m := by
  induction p generalizing m with
  | nil =>
    simp only [List.nil_append,co,consAt]
    have hh : co k s (consAt b (consAt a m)) = -co k s (consAt a (consAt b m)) := by
      rw [co_indices,co_indices,←Finset.sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      have ht := h [] (s.eraseIdx i.val) (by simp [List.length_eraseIdx_of_lt i.isLt]; have := i.isLt; omega)
      simp only [List.nil_append] at ht
      simp [consAt,ht]
    change k a * m (b::s) - (k b * m (a::s) - _) = -(k b * m (a::s) - (k a * m (b::s) - _))
    rw [hh]; ring
  | cons z zs ih =>
    simp only [List.cons_append,co]
    rw [h zs s (by simp; omega),ih (consAt z m) (by
      intro q r hqr
      apply h (z::q) r
      simp only [List.length_cons] at hqr ⊢
      omega)]
    ring

theorem pf_swap (B : X → X → ℚ) (sk : ∀ i j, B i j = -B j i)
    (p : List X) (x y : X) (s : List X) :
    pf B (p++x::y::s) = -pf B (p++y::x::s) := by
  cases p with
  | nil =>
    simp only [List.nil_append]
    rw [pf_step,pf_step,co,co]
    have he (z : X) : consAt z (pf B) = coFun (B z) (pf B) := funext (pf_step B z)
    rw [he,he,sk x y]
    linarith [co_anti (B x) (B y) s (pf B)]
  | cons z zs =>
    simp only [List.cons_append,pf_step]
    apply co_swap
    intro q r h
    exact pf_swap B sk q x y r
termination_by p.length+s.length
decreasing_by subst p; simp_all; omega

theorem pf_move (B : X → X → ℚ) (sk : ∀ i j, B i j = -B j i)
    (p : List X) (l : List X) (i : Fin l.length) :
    pf B (p++l[i.val]::l.eraseIdx i.val) = (-1:ℚ)^i.val * pf B (p++l) := by
  induction l generalizing p with
  | nil => exact Fin.elim0 i
  | cons z zs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.val_succ,List.getElem_cons_succ,List.eraseIdx_cons_succ,pow_succ]
      rw [pf_swap B sk p]
      have he := ih (p++[z]) j
      simp only [List.append_assoc,List.cons_append,List.nil_append] at he
      rw [he]
      ring
end BoundaryDet
namespace BoundaryDet
open BoundaryPadding Finset
variable {X : Type*}
def defectMat (B : X → X → ℚ) (x y : X) {n : ℕ} (v : Fin n → X) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => B (Fin.cons (α := fun _ => X) x v i) (Fin.cons (α := fun _ => X) y v j)
def D (B : X → X → ℚ) (x y : X) {n : ℕ} (v : Fin n → X) := (defectMat B x y v).det

theorem defectLap (B : X → X → ℚ) (x y : X) {n : ℕ} (v : Fin (n+1) → X) :
    D B x y v = B x y * D B (v 0) (v 0) (Fin.tail v) -
      ∑ i : Fin (n+1), B x (v i) * D B (v i) y (i.removeNth v) := by
  let A := defectMat B x y v
  change A.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hd : A.submatrix Fin.succ (0 : Fin (n+2)).succAbove =
      defectMat B (v 0) (v 0) (Fin.tail v) := by
    ext i j
    simp [A,defectMat,Matrix.submatrix,Fin.cons_self_tail]
  rw [hd]
  change (1:ℚ) * B x y * _ + _ = _
  rw [one_mul,sub_eq_add_neg,←Finset.sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  let M := A.submatrix Fin.succ i.succ.succAbove
  have hminor : M.submatrix i.cycleRange.symm id = defectMat B (v i) y (i.removeNth v) := by
    ext r c
    cases r using Fin.cases <;> cases c using Fin.cases <;>
      simp [M,A,defectMat,Matrix.submatrix,Fin.removeNth]
  have hh := Matrix.det_permute i.cycleRange.symm M
  rw [hminor] at hh
  change D B (v i) y (i.removeNth v) = _ at hh
  rw [hh]
  simp [Fin.sign_cycleRange,pow_succ,A,M,defectMat, mul_assoc, mul_left_comm]

theorem eraseOfFn {n : ℕ} (v : Fin (n+1) → X) (i : Fin (n+1)) :
    (List.ofFn v).eraseIdx i.val = List.ofFn (i.removeNth v) := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [List.ofFn_succ,Fin.tail]
    | succ j =>
      rw [List.ofFn_succ,Fin.val_succ,List.eraseIdx_cons_succ,ih,List.ofFn_succ]
      simp [Fin.removeNth]; rfl

theorem co_fin {n : ℕ} (k : X → ℚ) (v : Fin (n+1) → X) (m : Moment X) :
    co k (List.ofFn v) m = ∑ i, (-1:ℚ)^i.val * k (v i) * m (List.ofFn (i.removeNth v)) := by
  rw [co_indices]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f:=v))) _ _
  intro j
  let i : Fin (n+1) := ⟨j.val,by simpa using j.isLt⟩
  change _ = (-1:ℚ)^i.val * k (v i) * m (List.ofFn (i.removeNth v))
  rw [←eraseOfFn v i]
  simp only [List.getElem_ofFn]
  rfl

theorem move_fin {n : ℕ} (B : X → X → ℚ) (sk : ∀ i j, B i j = -B j i) (p : List X)
    (v : Fin (n+1) → X) (i : Fin (n+1)) :
    pf B (p++v i::List.ofFn (i.removeNth v)) = (-1:ℚ)^i.val * pf B (p++List.ofFn v) := by
  have he := pf_move B sk p (List.ofFn v) ⟨i.val,by simpa using i.isLt⟩
  rw [←eraseOfFn v i]
  simpa only [List.getElem_ofFn] using he
end BoundaryDet
namespace BoundaryDet
open BoundaryPadding Finset
variable {X : Type*}
theorem defect_identity (B : X → X → ℚ) (sk : ∀ i j, B i j = -B j i) (x y : X) {n : ℕ}
    (v : Fin n → X) :
    D B x y v = if Even n then pf B (x::y::List.ofFn v) * pf B (List.ofFn v)
      else pf B (x::List.ofFn v) * pf B (y::List.ofFn v) := by
  induction n generalizing x y with
  | zero => simp [D,defectMat,Matrix.det_unique,pf_step,co,pf]
  | succ n ih =>
    rw [defectLap]
    have hv : v 0 :: List.ofFn (Fin.tail v) = List.ofFn v := List.ofFn_succ.symm
    have hd := ih (v 0) (v 0) (Fin.tail v)
    by_cases h : Even n
    · have hn : ¬Even (n+1) := by simpa [Nat.even_add_one] using h
      rw [ite_eq_right hn]
      rw [ite_eq_left h] at hd
      have hsame := pf_swap B sk [] (v 0) (v 0) (List.ofFn (Fin.tail v))
      simp only [List.nil_append] at hsame
      have hz : pf B (v 0::v 0::List.ofFn (Fin.tail v)) = 0 := by linarith
      rw [hd,hz,zero_mul,mul_zero,zero_sub]
      rw [pf_step B x,co_fin,Finset.sum_mul,←Finset.sum_neg_distrib]
      apply sum_congr rfl;intro i _
      have hm := move_fin B sk [y] v i
      simp only [List.cons_append,List.nil_append] at hm
      have hs := pf_swap B sk [] (v i) y (List.ofFn (i.removeNth v))
      simp only [List.nil_append] at hs
      rw [ih,ite_eq_left h,hs,hm]
      ring
    · have hn : Even (n+1) := by simpa [Nat.even_add_one] using h
      rw [ite_eq_left hn]
      rw [ite_eq_right h,hv] at hd
      rw [hd,pf_step B x,co,co_fin,sub_mul,Finset.sum_mul]
      simp only [consAt]
      congr 1
      · ring
      · apply sum_congr rfl;intro i _
        have hm := move_fin B sk [] v i
        simp only [List.nil_append] at hm
        rw [ih,ite_eq_right h,hm]
        ring

theorem det_pf_sq (B : X → X → ℚ) (sk : ∀ i j, B i j = -B j i) {n : ℕ} (v : Fin n → X) :
    Matrix.det (fun i j : Fin n => B (v i) (v j)) = (pf B (List.ofFn v))^2 := by
  cases n with
  | zero => exact (Matrix.det_isEmpty (A := Matrix.of (fun i j : Fin 0 => B (v i) (v j)))).trans (by simp [pf])
  | succ n =>
    have he : D B (v 0) (v 0) (Fin.tail v) =
        Matrix.det (fun i j : Fin (n+1) => B (v i) (v j)) := by
      unfold D; congr 1; ext i j; simp [defectMat,Fin.cons_self_tail]
    rw [←he,defect_identity B sk,List.ofFn_succ (f:=v)]
    by_cases h : Even n
    · rw [ite_eq_left h]
      have ha := pf_swap B sk [] (v 0) (v 0) (List.ofFn (Fin.tail v))
      simp only [List.nil_append] at ha
      have hz : pf B (v 0::v 0::List.ofFn (Fin.tail v)) = 0 := by linarith
      have ho : Odd (v 0::List.ofFn (fun i => v i.succ)).length := by
        simp only [List.length_cons,List.length_ofFn]; exact h.add_odd (by decide : Odd 1)
      simp [hz,pf_odd B _ ho]
    · rw [ite_eq_right h,pow_two]
      rfl

end BoundaryDet
namespace BoundaryDet
open BoundaryPadding
variable {X Y : Type*}
theorem pf_pairwise_congr (A B : X → X → ℚ) (l : List X)
    (h : l.Pairwise (fun i j => A i j = B i j)) : pf A l = pf B l := by
  apply wick_of_rec (pf A) B l (by rw [pf])
  intro x xs hx
  rw [pf_step,co_indices,co_indices]
  apply Finset.sum_congr rfl
  intro i _
  rw [(List.pairwise_cons.mp (h.sublist hx)).1 _ (List.getElem_mem ..)]

theorem co_map (f : X → Y) (k : Y → ℚ) (m : Moment Y) (l : List X) :
    co k (l.map f) m = co (fun x => k (f x)) l (fun xs => m (xs.map f)) := by
  induction l generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons,co,co,ih]; rfl

theorem pf_map (A : Y → Y → ℚ) (f : X → Y) (l : List X) :
    pf A (l.map f) = pf (fun i j => A (f i) (f j)) l := by
  apply wick_of_rec (fun ys => pf A (ys.map f)) _ l (by simp [pf])
  intro x xs _
  rw [List.map_cons,pf_step,co_map]

def skew {n : ℕ} (U : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  if i < j then U i j else if j < i then -U j i else 0

theorem skew_spec {n : ℕ} (U : Fin n → Fin n → ℤ) (i j : Fin n) :
    skew U i j = -skew U j i := by
  rcases lt_trichotomy i j with h|rfl|h <;> simp_all [skew,lt_asymm]

theorem skew_det_sq {n : ℕ} (A : X → X → ℤ) (v : Fin n → X) :
    ((Matrix.det (skew (fun i j => A (v i) (v j))) : ℤ) : ℚ) =
      (pf (fun i j => (A i j : ℚ)) (List.ofFn v))^2 := by
  let U := fun i j : Fin n => A (v i) (v j)
  let K := fun i j => (skew U i j : ℚ)
  have hsk (i j) : K i j = -K j i := by dsimp [K]; exact_mod_cast skew_spec U i j
  have he := det_pf_sq K hsk (fun i => i)
  have hp : pf K (List.ofFn (fun i : Fin n => i)) =
      pf (fun i j => (U i j : ℚ)) (List.ofFn (fun i : Fin n => i)) := by
    apply pf_pairwise_congr
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    simp [K,skew,show (⟨i,by simpa using hi⟩ : Fin n) < ⟨j,by simpa using hj⟩ from hij]
  rw [hp] at he
  have hm := pf_map (fun i j => (A i j : ℚ)) v (List.ofFn (fun i : Fin n => i))
  rw [List.map_ofFn] at hm
  change pf (fun i j => (A i j : ℚ)) (List.ofFn v) = _ at hm
  rw [hm]
  convert he using 1
  exact (Int.castRingHom ℚ).map_det (skew U)
end BoundaryDet

namespace Pcx446Arithmetic

abbrev PcxMask (N t : ℕ) := Fin t → Bool → Sig N
def pcxMaskSigs {N t : ℕ} (M : PcxMask N t) := ⋃ i, Set.range (M i)
def pcxBoolSig {N : ℕ} (c : Sig N) (b : Bool) : Sig N := fun x => c x == b

def pcxRestrict {N t : ℕ} (M : PcxMask N t) (row : Fin t→Sig N) (c : Sig N) : PcxMask N t :=
  fun i b x => M i b x && (!(row i x) || (c x == b))

lemma pcxRestrictB {N t : ℕ} {A : Set (Sig N)} (M : PcxMask N t) (row : Fin t→Sig N) (c : Sig N)
    (hm : pcxMaskSigs M ⊆ A) (hr : ∀ i,row i∈A) (hc : c∈A) :
    Build A (pcxMaskSigs (pcxRestrict M row c)) (8*t) := by
  have bit (i : Fin t) (b : Bool) : Build A {pcxRestrict M row c i b} 4 := by
    let nrow : Sig N := fun x=> !(row i x)
    let ok := pcxBoolSig c b
    have nr : Build A {nrow} 1 := notB (hr i)
    have okG : Build A {ok} 1 := by
      cases b with
      | false =>
        have e : pcxBoolSig c false = fun x=> !(c x) := by funext x; simp [pcxBoolSig]
        change Build A {pcxBoolSig c false} 1;rw [e];exact notB hc
      | true =>
        have e : pcxBoolSig c true = c := by funext x; simp [pcxBoolSig]
        change Build A {pcxBoolSig c true} 1; rw [e]
        exact relaxB (idleB (Set.singleton_subset_iff.mpr hc)) le_rfl Set.subset_union_right (by omega)
    let allow : Sig N := fun x=> nrow x || ok x
    have both := unionB nr okG
    have cond : Build (A ∪ ({nrow} ∪ {ok})) {allow} 1 :=
      orB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    have filter : Build (A∪{allow}) {pcxRestrict M row c i b} 1 :=
      andB (Or.inl (hm (Set.mem_iUnion.mpr ⟨i,⟨b,rfl⟩⟩))) (Or.inr rfl)
    exact relaxB (seq2B (seq2B both cond) filter) le_rfl Set.subset_union_right (by omega)
  have one (i : Fin t) : Build A (Set.range (pcxRestrict M row c i)) 8 := by
    apply relaxB (unionB (bit i false) (bit i true)) le_rfl _ (by omega)
    rintro a ⟨b,rfl⟩; cases b <;> simp
  simpa [pcxMaskSigs,Nat.mul_comm] using finB _ 8 one

structure PcxScan (N t : ℕ) where
  mask : PcxMask N t
  chosen : (Fin N→Bool)→ℕ
  rank : (Fin N→Bool)→ℕ

def pcxScanSigs {N t : ℕ} (d : ℕ) (s : PcxScan N t) :=
  pcxMaskSigs s.mask ∪ (Set.range (bitsOf t s.chosen) ∪ Set.range (bitsOf d s.rank))

def pcxAdvance {N t : ℕ} (s : PcxScan N t) (row : Fin t→Sig N)
    (count : PcxMask N t→(Fin N→Bool)→ℕ) : PcxScan N t :=
  let left := count (pcxRestrict s.mask row (fun _=>false))
  let take := fun x => decide (left x ≤ s.rank x)
  ⟨pcxRestrict s.mask row take,fun x=>Nat.bit (take x) (s.chosen x),
    fun x=>if take x then s.rank x-left x else s.rank x⟩

lemma pcxAdvanceB {N t d : ℕ} {A : Set (Sig N)} (s : PcxScan N t) (row : Fin t→Sig N)
    (count : PcxMask N t→(Fin N→Bool)→ℕ) (C : ℕ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A)
    (old : pcxScanSigs d s ⊆ A) (hr : ∀ i,row i ∈ A)
    (hw : ∀ x,s.rank x < 2^d) (cw : ∀ m x,count m x < 2^d)
    (oracle : ∀ (m : PcxMask N t) (S : Set (Sig N)), A⊆S → pcxMaskSigs m⊆S →
      Build S (Set.range (bitsOf d (count m))) C) :
    Build A (pcxScanSigs d (pcxAdvance s row count)) (16*t+28*d+1+C) := by
  let lm := pcxRestrict s.mask row (fun _=>false)
  let left := count lm
  let cmp : Sig N := fun x=>decide (s.rank x < left x)
  let take : Sig N := fun x=>decide (left x ≤ s.rank x)
  have mask := pcxRestrictB s.mask row (fun _=>false) (fun a h=>old (Or.inl h)) hr h0
  have readout := oracle lm (A∪pcxMaskSigs lm) Set.subset_union_left Set.subset_union_right
  have read := seq2B mask readout
  let Ls := Set.range (bitsOf d left)
  let S := A∪Ls
  have rank (i : Fin d) : bitsOf d s.rank i ∈ A := old (Or.inr (Or.inr ⟨i,rfl⟩))
  have ltg : Build S {cmp} (5*d) := ltB d s.rank left (Or.inl h0)
    (fun i=>Or.inl (rank i)) (fun i=>Or.inr ⟨i,rfl⟩) hw (cw lm)
  have ng : Build (S∪{cmp}) {take} 1 := by
    have eq : take = fun x=> !(cmp x) := by
      funext x
      by_cases h : s.rank x < left x <;> simp [take,cmp,h,Nat.not_le_of_lt,Nat.le_of_not_gt]
    rw [eq];exact notB (Or.inr rfl)
  let diff := fun x=>(s.rank x+(2^d-1-left x+1))%2^d
  have sub : Build S (Set.range (bitsOf d diff)) (19*d) :=
    subModB d s.rank left (Or.inl h0) (Or.inl h1) (fun i=>Or.inl (rank i)) (fun i=>Or.inr ⟨i,rfl⟩) (cw lm)
  have first := unionB (seq2B ltg ng) sub
  let T := S ∪ ({take} ∪ Set.range (bitsOf d diff))
  have tk : take ∈ T := Or.inr (Or.inl rfl)
  have base {f : Sig N} (hf : f∈A) : f ∈ T := Or.inl (Or.inl hf)
  let next := pcxAdvance s row count
  have masks : Build T (pcxMaskSigs next.mask) (8*t) :=
    pcxRestrictB s.mask row take (fun a h=>base (old (Or.inl h))) (fun i=>base (hr i)) tk
  have newrank (i : Fin d) : Build T {bitsOf d next.rank i} 4 := by
    have a : Build T {fun x => if take x then bitsOf d diff i x else bitsOf d s.rank i x} 4 :=
      iteB tk (Or.inr (Or.inr ⟨i,rfl⟩)) (base (rank i))
    convert a using 4
    rename_i x
    change (if take x then s.rank x-left x else s.rank x).testBit i.val = _
    by_cases h : take x = true
    · have hl : left x ≤ s.rank x := of_decide_eq_true h
      have hrank := hw x
      have hleft := cw lm x
      have eq : s.rank x+(2^d-1-left x+1)=(s.rank x-left x)+2^d := by dsimp [left] at *;omega
      have sd : s.rank x-left x<2^d := by omega
      simp [h,bitsOf,diff,eq,Nat.mod_eq_of_lt sd]
    · simp [h,bitsOf]
  have assembly := unionB masks (finSigB _ 4 newrank)
  have endpt := relaxB assembly le_rfl (B' := pcxScanSigs d next) (by
    rintro a (h|⟨i,rfl⟩|h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (pcxBitWires (fun j=>base (old (Or.inr (Or.inl ⟨j,rfl⟩)))) tk i)
    · exact Or.inr (Or.inr h)) le_rfl
  exact relaxB (seq2B read (seq2B first endpt)) le_rfl Set.subset_union_right (by nlinarith)

def pcxRun {N t : ℕ} (M : PcxMask N t) (rank : (Fin N→Bool)→ℕ) (row : ℕ→Fin t→Sig N)
    (count : PcxMask N t→(Fin N→Bool)→ℕ) : ℕ→PcxScan N t
  | 0 => ⟨M, fun _=>0, rank⟩
  | k+1 => pcxAdvance (pcxRun M rank row count k) (row k) count

lemma pcxRunB {N t d : ℕ} {A : Set (Sig N)} (M : PcxMask N t) (rank : (Fin N→Bool)→ℕ)
    (row : ℕ→Fin t→Sig N) (count : PcxMask N t→(Fin N→Bool)→ℕ) (C k : ℕ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) (hm : pcxMaskSigs M⊆A)
    (hrank : Set.range (bitsOf d rank) ⊆ A) (rows : ∀ k i,row k i∈A)
    (rw : ∀ x,rank x<2^d) (cw : ∀ m x,count m x<2^d)
    (oracle : ∀ (m : PcxMask N t) (S : Set (Sig N)), A⊆S → pcxMaskSigs m⊆S →
      Build S (Set.range (bitsOf d (count m))) C) :
    Build A (pcxScanSigs d (pcxRun M rank row count k)) (k*(16*t+28*d+1+C)) := by
  let s := pcxRun M rank row count
  have small (k) (x) : (s k).rank x < 2^d := by
    induction k with
    | zero => exact rw x
    | succ k ih =>
      change (if _ then (s k).rank x - _ else (s k).rank x) < _
      split
      · exact lt_of_le_of_lt (Nat.sub_le _ _) ih
      · exact ih
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    apply idleB
    rintro a (ha|⟨i,rfl⟩|ha)
    · exact hm ha
    · convert h0 using 1; funext x; simp [pcxRun,bitsOf]
    · exact hrank ha
  | succ k ih =>
    have step := pcxAdvanceB (A:=A∪pcxScanSigs d (s k)) (s k) (row k) count C
      (Or.inl h0) (Or.inl h1) Set.subset_union_right (fun i=>Or.inl (rows k i)) (small k) cw
      (fun m S hs h=>oracle m S (Set.subset_union_left.trans hs) h)
    exact relaxB (seq2B ih step) le_rfl Set.subset_union_right (by nlinarith)

def pcxPicked {N t : ℕ} (idx : (Fin N→Bool)→ℕ) (count : PcxMask N t→(Fin N→Bool)→ℕ)
    (M : PcxMask N t) (rows : ℕ→Fin t→Sig N) (x : Fin N→Bool) :=
  if idx x < count M x then (pcxRun M idx rows count t).chosen x else 0

lemma pcxOutputsB {N t d : ℕ} {A : Set (Sig N)} (M : PcxMask N t) (index : (Fin N→Bool)→ℕ)
    (row : ℕ→Fin t→Sig N) (count : PcxMask N t→(Fin N→Bool)→ℕ) (C : ℕ)
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) (hm : pcxMaskSigs M⊆A)
    (hi : Set.range (bitsOf d index)⊆A) (rows : ∀ k i,row k i∈A)
    (iw : ∀ x,index x<2^d) (cw : ∀ m x,count m x<2^d)
    (oracle : ∀ (m : PcxMask N t) (S : Set (Sig N)), A⊆S → pcxMaskSigs m⊆S →
      Build S (Set.range (bitsOf d (count m))) C) :
    Build A ({fun x=>decide (index x<count M x)} ∪ Set.range (bitsOf t (pcxPicked index count M row)))
      (t*(16*t+28*d+1+C)+C+5*d+t) := by
  let st := pcxRun M index row count t
  let flag : Sig N := fun x=>decide (index x<count M x)
  have run := pcxRunB M index row count C t h0 h1 hm hi rows iw cw oracle
  have query := oracle M A le_rfl hm
  have flagG : Build (A∪Set.range (bitsOf d (count M))) {flag} (5*d) :=
    ltB d index (count M) (Or.inl h0) (fun j=>Or.inl (hi ⟨j,rfl⟩)) (fun j=>Or.inr ⟨j,rfl⟩) iw (cw M)
  have prep := unionB run (seq2B query flagG)
  let stage := A∪(pcxScanSigs d st∪{flag})
  have bits (i : Fin t) : Build stage {bitsOf t (pcxPicked index count M row) i} 1 := by
    have e : bitsOf t (pcxPicked index count M row) i = fun x=> flag x && (st.chosen x).testBit i.val := by
      funext x
      by_cases b : index x<count M x <;> simp [bitsOf,pcxPicked,flag,st,b]
    rw [e]
    exact andB (Or.inr (Or.inr rfl)) (Or.inr (Or.inl (Or.inr (Or.inl ⟨i,rfl⟩))))
  have out := finSigB (bitsOf t (pcxPicked index count M row)) 1 bits
  apply relaxB (seqB prep out) le_rfl _ (by nlinarith)
  rintro a (rfl|ha)
  · exact Or.inr (Or.inl (Or.inr rfl))
  · exact Or.inr (Or.inr ha)

def pcxKey (b : ℕ→Bool) : ℕ→ℕ
  | 0=>0
  | k+1=>Nat.bit (b k) (pcxKey b k)

def pcxFits {N t : ℕ} (M : PcxMask N t) (x : Fin N→Bool) (σ : Fin t→Bool) : Prop :=
  ∀ i, M i (σ i) x = true

instance pcxFitsDec {N t : ℕ} (M : PcxMask N t) (x : Fin N→Bool) (σ : Fin t→Bool) :
    Decidable (pcxFits M x σ) := inferInstanceAs (Decidable (∀ i,M i (σ i) x = true))

lemma pcxFitsRestrict {N t : ℕ} (M : PcxMask N t) (row : Fin t→Sig N) (take : Sig N)
    (x : Fin N→Bool) (σ : Fin t→Bool) (i : Fin t)
    (hr : ∀ j,row j x = decide (i=j)) :
    pcxFits (pcxRestrict M row take) x σ ↔ pcxFits M x σ ∧ σ i=take x := by
  constructor
  · intro h
    refine ⟨fun j=> (Bool.and_eq_true_iff.mp (h j)).1,?_⟩
    have q := (Bool.and_eq_true_iff.mp (h i)).2
    simp [hr] at q;exact q.symm
  · rintro ⟨hm,h⟩ j
    change M j (σ j) x && (!(row j x) || (take x == σ j)) = true
    apply Bool.and_eq_true_iff.mpr; refine ⟨hm j,?_⟩
    by_cases e : i=j
    · subst j; simp [hr,h]
    · simp [hr,e]

lemma pcxBitEq (a b : Bool) (p q : ℕ) :
    Nat.bit a p = Nat.bit b q ↔ p=q ∧ a=b := by
  cases a <;> cases b <;> simp [Nat.bit_val] <;> omega

lemma pcxBitLt (a b : Bool) (p q : ℕ) :
    Nat.bit a p < Nat.bit b q ↔ p<q ∨ (p=q ∧ a=false ∧ b=true) := by
  cases a <;> cases b <;> simp [Nat.bit_val] <;> omega

def pcxBelow {Ω : Type} [Fintype Ω] (μ code : Ω→ℕ) (k : ℕ) := ∑ ω, if code ω<k then μ ω else 0
def pcxTied {Ω : Type} [Fintype Ω] (μ code : Ω→ℕ) (k : ℕ) := ∑ ω, if code ω=k then μ ω else 0

lemma pcxBelowNext {Ω : Type} [Fintype Ω] (μ code : Ω→ℕ) (k : ℕ) (b : Ω→Bool) (take : Bool) :
    pcxBelow μ (fun ω=>Nat.bit (b ω) (code ω)) (Nat.bit take k) =
      pcxBelow μ code k + if take then ∑ ω, if code ω=k ∧ b ω=false then μ ω else 0 else 0 := by
  unfold pcxBelow
  simp_rw [pcxBitLt]
  cases take <;> simp only [Bool.false_eq_true,ite_false,add_zero,ite_true]
  · apply Finset.sum_congr rfl;intro ω _;simp [pcxBitLt]
  · rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro ω _
    by_cases ha : code ω<k <;> by_cases hb : code ω=k <;> by_cases hc : b ω=false <;> simp_all [pcxBitLt]

lemma pcxTiedNext {Ω : Type} [Fintype Ω] (μ code : Ω→ℕ) (k : ℕ) (b : Ω→Bool) (take : Bool) :
    pcxTied μ (fun ω=>Nat.bit (b ω) (code ω)) (Nat.bit take k) =
      ∑ ω, if code ω=k ∧ b ω=take then μ ω else 0 := by
  unfold pcxTied;simp [pcxBitEq]

lemma pcxTiedSplit {Ω : Type} [Fintype Ω] (μ code : Ω→ℕ) (k : ℕ) (b : Ω→Bool) :
    pcxTied μ code k = (∑ ω, if code ω=k ∧ b ω=false then μ ω else 0) +
      (∑ ω, if code ω=k ∧ b ω=true then μ ω else 0) := by
  rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro ω _
  by_cases h : code ω=k <;> cases hc : b ω <;> simp [h,hc]

lemma pcxRunQuantile {N t : ℕ} {Ω : Type} [Fintype Ω] (M : PcxMask N t) (index : (Fin N→Bool)→ℕ)
    (row : ℕ→Fin t→Sig N) (count : PcxMask N t→(Fin N→Bool)→ℕ)
    (raw : Ω→ℕ) (σ : Ω→Fin t→Bool) (order : ℕ→Fin t) (x : Fin N→Bool)
    (hot : ∀ k j, row k j x = decide (order k=j)) (countSpec : ∀ P, count P x =
      ∑ ω, if pcxFits P x (σ ω) then raw ω else 0) (valid : index x<count M x) (k : ℕ) :
    let s := pcxRun M index row count k
    let key := fun ω=>pcxKey (fun k=>σ ω (order k)) k
    let μ := fun ω=> if pcxFits M x (σ ω) then raw ω else 0
    (∀ ω,pcxFits s.mask x (σ ω) ↔ pcxFits M x (σ ω) ∧ key ω = s.chosen x) ∧
    index x = pcxBelow μ key (s.chosen x) + s.rank x ∧ s.rank x < pcxTied μ key (s.chosen x) := by
  classical
  let μ := fun ω=>if pcxFits M x (σ ω) then raw ω else 0
  induction k with
  | zero =>
    dsimp only [pcxRun,pcxKey]
    simp only [and_true,pcxBelow,lt_self_iff_false,ite_false,Finset.sum_const_zero,
      zero_add,pcxTied,ite_true,eq_self,true_and]
    rw [countSpec] at valid
    exact ⟨fun _=>True.intro,valid⟩
  | succ k ih =>
    let s := pcxRun M index row count k
    let key := fun ω=>pcxKey (fun k=>σ ω (order k)) k
    let b := fun ω=>σ ω (order k)
    let p := s.chosen x
    let L := ∑ ω, if key ω = p ∧ b ω=false then μ ω else 0
    let R := ∑ ω, if key ω = p ∧ b ω=true then μ ω else 0
    let take : Sig N := fun y=>decide (count (pcxRestrict s.mask (row k) (fun _=>false)) y ≤ s.rank y)
    have leftCount : count (pcxRestrict s.mask (row k) (fun _=>false)) x = L := by
      rw [countSpec];unfold L
      apply Finset.sum_congr rfl;intro ω _
      rw [if_congr (pcxFitsRestrict _ _ _ _ _ _ (hot k)) rfl rfl]
      have iff : pcxFits s.mask x (σ ω) ↔ pcxFits M x (σ ω) ∧ key ω=p := ih.1 ω
      simp only [iff]
      by_cases hm : pcxFits M x (σ ω) <;> simp [μ,hm,key,p,s,b]
    have choose : take x = decide (L ≤ s.rank x) := by simp [take,leftCount]
    have split : pcxTied μ key p = L+R := pcxTiedSplit μ key p b
    have sum := ih.2.1
    have active := ih.2.2
    change index x = pcxBelow μ key p + s.rank x at sum
    change s.rank x < pcxTied μ key p at active
    rw [split] at active
    change (∀ ω, pcxFits (pcxRestrict s.mask (row k) take) x (σ ω) ↔
      pcxFits M x (σ ω) ∧ Nat.bit (b ω) (key ω) = Nat.bit (take x) p) ∧
      index x = pcxBelow μ (fun ω=>Nat.bit (b ω) (key ω)) (Nat.bit (take x) p) +
        (if take x then s.rank x-count (pcxRestrict s.mask (row k) (fun _=>false)) x else s.rank x) ∧
      (if take x then s.rank x-count (pcxRestrict s.mask (row k) (fun _=>false)) x else s.rank x) <
        pcxTied μ (fun ω=>Nat.bit (b ω) (key ω)) (Nat.bit (take x) p)
    refine ⟨fun ω=>?_,?_⟩
    · rw [pcxFitsRestrict _ _ _ _ _ _ (hot k),ih.1 ω,pcxBitEq]; tauto
    · rw [pcxBelowNext,pcxTiedNext,leftCount,choose]
      by_cases c : L ≤ s.rank x
      · simp only [c,decide_true,ite_true]
        change index x = pcxBelow μ key p+L+(s.rank x-L) ∧ s.rank x-L<R
        omega
      · simp only [c,decide_false,Bool.false_eq_true,ite_false,add_zero]
        change index x = pcxBelow μ key p+s.rank x ∧ s.rank x<L
        omega
lemma pcxKeySum (b : ℕ→Bool) (k : ℕ) :
    pcxKey b k = ∑ i : Fin k,(b i.val).toNat*2^(k-1-i.val) := by
  induction k with
  | zero=> simp [pcxKey]
  | succ k ih=>
    rw [pcxKey,Nat.bit_val,ih,Fin.sum_univ_castSucc,Finset.mul_sum]
    simp only [Fin.val_last,Fin.val_castSucc,Nat.add_sub_cancel,Nat.sub_self,pow_zero,mul_one]
    congr 1
    apply Finset.sum_congr rfl;intro i _
    have eq : k-i.val = (k-1-i.val)+1 := by have := i.isLt;omega
    rw [eq,pow_succ];ring

lemma pcxKeySmall (b : ℕ→Bool) (k : ℕ) : pcxKey b k < 2^k := by
  induction k with
  | zero=>exact Nat.zero_lt_one
  | succ k ih=>
    rw [pcxKey,Nat.bit_val,pow_succ]
    have hb : (b k).toNat ≤ 1 := by cases b k <;> decide
    omega

lemma pcxChosenSmall {N t : ℕ} (M : PcxMask N t) (index : (Fin N→Bool)→ℕ)
    (row : ℕ→Fin t→Sig N) (count : PcxMask N t→(Fin N→Bool)→ℕ) (k : ℕ) (x : Fin N→Bool) :
    (pcxRun M index row count k).chosen x < 2^k := by
  induction k with
  | zero=>exact Nat.zero_lt_one
  | succ k ih=>
    change Nat.bit _ ((pcxRun M index row count k).chosen x) < _
    rw [Nat.bit_val,pow_succ]
    dsimp only
    have bitSmall (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
    have h := bitSmall (decide (count (pcxRestrict (pcxRun M index row count k).mask (row k) (fun _=>false)) x ≤ (pcxRun M index row count k).rank x))
    omega

lemma pcxOutputSpec {N t : ℕ} {Ω : Type} [Fintype Ω] (M : PcxMask N t) (index : (Fin N→Bool)→ℕ)
    (row : ℕ→Fin t→Sig N) (count : PcxMask N t→(Fin N→Bool)→ℕ)
    (raw : Ω→ℕ) (σ : Ω→Fin t→Bool) (order : ℕ→Fin t) (x : Fin N→Bool)
    (hot : ∀ k j, row k j x = decide (order k=j)) (countSpec : ∀ P, count P x =
      ∑ ω, if pcxFits P x (σ ω) then raw ω else 0) :
    let p := pcxPicked index count M row x
    let code := fun ω=>∑ i : Fin t,(σ ω (order i.val)).toNat * 2^(t-1-i.val)
    let μ := fun ω=> if pcxFits M x (σ ω) then raw ω else 0
    if index x < count M x then ((∑ ω, if code ω < p then μ ω else 0) ≤ index x ∧
      index x < (∑ ω, if code ω ≤ p then μ ω else 0)) else p=0 := by
  classical
  dsimp only
  split
  next h =>
    have tot := pcxRunQuantile M index row count raw σ order x hot countSpec h t
    let p := (pcxRun M index row count t).chosen x
    let code := fun ω=>pcxKey (fun k=>σ ω (order k)) t
    let μ := fun ω=>if pcxFits M x (σ ω) then raw ω else 0
    have low := tot.2.1
    have high := tot.2.2
    change index x = pcxBelow μ code p + _ at low
    change _ < pcxTied μ code p at high
    have eq : (∑ ω, if code ω ≤ p then μ ω else 0) = pcxBelow μ code p + pcxTied μ code p := by
      unfold pcxBelow pcxTied; rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro ω _
      by_cases h : code ω < p
      · simp [h,h.le,h.ne]
      · by_cases e : code ω = p
        · simp [e]
        · simp [h,e,show ¬code ω ≤ p by omega]
    have codeEq (ω : Ω) : (∑ i : Fin t,(σ ω (order i.val)).toNat * 2^(t-1-i.val)) = code ω := (pcxKeySum (fun k=>σ ω (order k)) t).symm
    simp only [pcxPicked,h,ite_true,codeEq]
    change pcxBelow μ code p ≤ index x ∧ index x < ∑ ω, if code ω≤p then μ ω else 0
    rw [eq];omega
  next h => simp [pcxPicked,h]

end Pcx446Arithmetic

namespace BoundaryFixed
open BoundaryPadding BoundaryPin BoundaryDet BoundarySwitch Finset
variable {X : Type*}
theorem graphWick {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (pin : Fin t → Fin n)
    (w : Fin m → Bool → ℤ) (ps : List (Fin t × Bool)) (ord : ps.Pairwise (fun i j => i.1 < j.1))
    (recM : PlanarRec pin (spin u v (fun e b => w e (bitEquiv.symm b))))
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 ≠ 0)
    (l : List (MaskLabel (Fin t))) (hl : l.Sublist (padded ps).zipIdx) :
    let M := spin u v (fun e b => w e (bitEquiv.symm b))
    (∑ x : Fin n → Bool, (rawIsing u v w x : ℚ)/ M 0 *
      monom (maskSpin (fun i => x (pin i))) l) = pf (kernel pin M) l := by
  classical
  let M := spin u v (fun e b => w e (bitEquiv.symm b))
  change _ = pf (kernel pin M) l
  by_cases hr : ∀ z ∈ l, z.1.isSome = true
  · have he (x : Fin n → Bool) : monom (maskSpin (fun i => x (pin i))) l =
        monom (fun i => spinSign (x (pin (atSite i)))) l := by
      unfold monom
      congr 1
      apply List.map_congr_left
      intro z hz
      have := hr z hz
      obtain ⟨o,k⟩ := z
      cases o <;> simp_all [maskSpin,atSite]
    let f := fun z : MaskLabel (Fin t) => edgeSource (pin (atSite z))
    calc
      _ = ratio M (listSrc f l) := by
        simp_rw [he,div_mul_eq_mul_div]
        rw [←Finset.sum_div]
        unfold ratio
        rw [spinMonom u v w (fun z => pin (atSite z)) l]
      _ = pf (fun i j => ratio M (f j-f i)) l :=
        wickGraph pin M recM hz atSite l (realOrder ps ord l hl hr)
      _ = _ := by
        apply pf_congr
        intro i hi j hj
        simp [kernel,hr i hi,hr j hj,f]
  · push Not at hr
    obtain ⟨z,hz,hz'⟩ := hr
    have hnone : z.1 = none := by cases h : z.1 <;> simp_all
    rw [pf_dead (kernel pin M) z (by simp [kernel,hnone]) (by simp [kernel,hnone]) l hz]
    apply sum_eq_zero
    intro x _
    have hmon : (0:ℚ) ∈ l.map (maskSpin (fun i => x (pin i))) :=
      List.mem_map.mpr ⟨z,hz,by simp [maskSpin,hnone]⟩
    simp [monom, List.prod_eq_zero hmon]

theorem eraseProd (f : X → ℚ) (l : List X) (i : Fin l.length) :
    f l[i.val] * ((l.eraseIdx i.val).map f).prod = (l.map f).prod := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa [mul_left_comm] using congrArg (fun a => f x * a) (ih j)

theorem pf_scale_rows (a : X → X → ℚ) (g : X → ℚ) (l : List X) :
    pf (fun x y => g x * g y * a x y) l = (l.map g).prod * pf a l := by
  cases l with
  | nil => simp [pf]
  | cons x xs =>
    rw [pf_step,pf_step,co_indices,co_indices,Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pf_scale_rows a g (xs.eraseIdx i.val)]
    simp only [List.map_cons,List.prod_cons]
    rw [←eraseProd g xs i]
    ring
termination_by l.length
decreasing_by subst l; simp [List.length_eraseIdx_of_lt i.isLt]

def bitI (b : Bool) : ℤ := if b then 1 else 0
def alpha (p : X → Bool → Bool) (q : Option (X × Bool)) : ℤ :=
  q.elim 1 (fun z => bitI (p z.1 false) + bitI (p z.1 true))
def beta (p : X → Bool → Bool) (q : Option (X × Bool)) : ℤ :=
  q.elim 0 (fun z => bitI (p z.1 false) - bitI (p z.1 true))
def betaSign (p : X → Bool → Bool) (z : MaskLabel X) : ℤ :=
  (-1:ℤ)^z.2 * beta p z.1
def maskCoeff (p : X → Bool → Bool) (z : MaskLabel X) : ℚ :=
  (betaSign p z : ℚ)/(alpha p z.1 : ℚ)
theorem scaledCoeff (p : X → Bool → Bool) (z : MaskLabel X) :
    (alpha p z.1 : ℚ) * maskCoeff p z = betaSign p z := by
  obtain ⟨q,k⟩ := z
  cases q with
  | none => simp [alpha,beta,betaSign,maskCoeff]
  | some z =>
    cases ha : p z.1 false <;> cases hb : p z.1 true <;>
      simp [alpha,beta,betaSign,maskCoeff,ha,hb,bitI]

def hit (p : X → Bool → Bool) (σ : X → Bool) (q : Option (X × Bool)) : ℤ :=
  q.elim 1 (fun z => 2 * bitI (p z.1 (σ z.1)))

theorem evalHit (p : X → Bool → Bool) (σ : X → Bool) (l : List (Option (X × Bool))) (k : ℕ) :
    ((l.zipIdx k).map (fun z => (alpha p z.1 : ℚ))).prod *
      prodAlt (maskCoeff p) (maskSpin σ) (l.zipIdx k) ((-1:ℚ)^k) =
      (l.map (fun z => (hit p σ z : ℚ))).prod := by
  induction l generalizing k with
  | nil => simp [prodAlt]
  | cons q qs ih =>
    rw [List.zipIdx_cons,List.map_cons,List.prod_cons,prodAlt,List.map_cons,List.prod_cons]
    have hs : -((-1:ℚ)^k) = (-1:ℚ)^(k+1) := by simp [pow_succ]
    rw [hs]
    have hq : (alpha p q : ℚ) * (1 + (-1:ℚ)^k * maskCoeff p (q,k) * maskSpin σ (q,k)) =
        (hit p σ q : ℚ) := by
      have hc := scaledCoeff p (q,k)
      change (alpha p q : ℚ) * maskCoeff p (q,k) = _ at hc
      rw [mul_add,mul_one,show (alpha p q : ℚ) * ((-1:ℚ)^k * maskCoeff p (q,k) * maskSpin σ (q,k)) =
        (-1:ℚ)^k * ((alpha p q : ℚ)*maskCoeff p (q,k)) * maskSpin σ (q,k) by ring,hc]
      have hpow : (-1:ℚ)^k * (-1:ℚ)^k = 1 := by rw [←mul_pow]; simp
      cases q with
      | none => simp [alpha,beta,betaSign,hit,maskSpin]
      | some z =>
        cases ha : p z.1 false <;> cases hb : p z.1 true <;> cases hc : σ z.1 <;>
          simp [alpha,beta,betaSign,hit,maskSpin,spinSign,bitI,ha,hb,hc,hpow] <;> norm_num
    rw [←hq,←ih (k+1)]
    ring
end BoundaryFixed
namespace BoundaryFixed
open BoundaryPadding BoundaryPin BoundarySwitch BoundaryDet Finset

def pinList (t : ℕ) := List.ofFn (fun i : Fin t => (i,false))
def slotList (t : ℕ) := (padded (pinList t)).zipIdx
def fixedEntry {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (Z : ℤ) (p : Fin t → Bool → Bool) (i j : MaskLabel (Fin t)) : ℤ :=
  Z * alpha p i.1 * alpha p j.1 -
    betaSign p i * betaSign p j * (4 * falsePair u v w pin (atSite j) (atSite i) - Z)

theorem entry_eq {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (p : Fin t → Bool → Bool)
    (hz : spin u v (fun e b => w e (bitEquiv.symm b)) 0 ≠ 0) :
    let M := spin u v (fun e b => w e (bitEquiv.symm b))
    let Z := M 0
    (fun i j => (fixedEntry u v w pin Z p i j : ℚ)) =
    (fun i j => (Z:ℚ) * ((alpha p i.1 : ℚ) * alpha p j.1 * padK (kernel pin M) (maskCoeff p) i j)) := by
  classical
  let M := spin u v (fun e b => w e (bitEquiv.symm b))
  let Z := M 0
  have hn : (Z:ℚ) ≠ 0 := by exact_mod_cast hz
  funext i j
  change (fixedEntry u v w pin Z p i j : ℚ) = (Z:ℚ) * _
  unfold fixedEntry padK
  push_cast
  rw [show (alpha p i.1 : ℚ) * alpha p j.1 *
      (1 + -maskCoeff p i * (maskCoeff p j * kernel pin M i j)) =
      (alpha p i.1 : ℚ) * alpha p j.1 - ((alpha p i.1 : ℚ)*maskCoeff p i) *
        ((alpha p j.1 : ℚ)*maskCoeff p j) * kernel pin M i j by ring,
      scaledCoeff,scaledCoeff]
  by_cases h : (i.1.isSome && j.1.isSome) = true
  · have hobs := (observablesAtGrid u v w (pin (atSite j)) (pin (atSite i))).2
    change Z + M (edgeSource (pin (atSite j))-edgeSource (pin (atSite i))) =
      4 * falsePair u v w pin (atSite j) (atSite i) at hobs
    have hc : (Z:ℚ) + M (edgeSource (pin (atSite j))-edgeSource (pin (atSite i))) =
      4 * (falsePair u v w pin (atSite j) (atSite i):ℚ) := by exact_mod_cast hobs
    simp only [kernel,ite_eq_left h,ratio]
    rw [←hc]
    change _ = (Z:ℚ) * (_ - _ * (_ / (Z:ℚ)))
    field_simp
    ring
  · have h0 : betaSign p i = 0 ∨ betaSign p j = 0 := by
      cases hi : i.1 <;> cases hj : j.1 <;> simp_all [betaSign,beta]
    rw [show kernel pin M i j = 0 by simp [kernel,h]]
    rcases h0 with hi|hj <;> simp [*] <;> ring

def weightMask {n t : ℕ} (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) (x : Fin n → Bool) : ℤ :=
  ∏ i, bitI (p i (x (pin i)))

theorem allHits {n t : ℕ} (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) (x : Fin n → Bool) :
    ((padded (pinList t)).map (fun z => (hit p (fun i => x (pin i)) z : ℚ))).prod =
      (2:ℚ)^t * (weightMask pin p x : ℚ) := by
  unfold padded
  have he : (((pinList t).map some).map (fun z => (hit p (fun i => x (pin i)) z : ℚ))).prod =
      (2:ℚ)^t * (weightMask pin p x : ℚ) := by
    simp only [pinList,List.map_ofFn,List.prod_ofFn,Function.comp_apply,hit,Option.elim_some,
      weightMask,Int.cast_mul,Int.cast_ofNat,Int.cast_prod,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
  split <;> simp only [List.map_append,List.prod_append,List.map_nil,List.prod_nil,List.map_cons,List.prod_cons,hit,Option.elim_none,Int.cast_one,mul_one] <;> exact he

end BoundaryFixed
namespace BoundaryFixed
open BoundaryPadding BoundaryPin BoundarySwitch BoundaryDet Finset

def allowedMass {n m t : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) : ℤ :=
  ∑ x, rawIsing u v w x * weightMask pin p x

def intMatrix {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (Z : ℤ) (p : Fin t → Bool → Bool) :
    Matrix (Fin (slotList t).length) (Fin (slotList t).length) ℤ :=
  skew (fun i j => fixedEntry u v w pin Z p ((slotList t).get i) ((slotList t).get j))

theorem fixedSquare {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (p : Fin t → Bool → Bool)
    (recM : PlanarRec pin (spin u v (fun e b => w e (bitEquiv.symm b)))) :
    let Z := spin u v (fun e b => w e (bitEquiv.symm b)) 0
    (2^t * Z^((slotList t).length/2) * allowedMass u v w pin p)^2 =
      Z^2 * (intMatrix u v w pin Z p).det := by
  classical
  let M := spin u v (fun e b => w e (bitEquiv.symm b))
  let Z := M 0
  let L := slotList t
  let G := ((L.map (fun z => (alpha p z.1 : ℚ))).prod)
  let W := allowedMass u v w pin p
  let E := fixedEntry u v w pin Z p
  change ((2:ℤ)^t * Z^(L.length/2) * W)^2 = Z^2 * _
  have evenL : Even L.length := by simpa [L,slotList] using padded_even (pinList t)
  by_cases hZ : Z = 0
  · have len : 0 < L.length := by
      unfold L slotList padded
      split <;> simp [pinList,NeZero.pos]
    obtain ⟨k,hk⟩ := evenL
    have hdiv : L.length/2 ≠ 0 := by omega
    simp [hZ,zero_pow hdiv]
  have hq : (Z:ℚ) ≠ 0 := by exact_mod_cast hZ
  have ord : (pinList t).Pairwise (fun i j => i.1 < j.1) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa [pinList] using hij
  have hh := histogram_pf univ (fun x => (rawIsing u v w x : ℚ)/Z)
    (fun x => maskSpin (fun i => x (pin i))) (kernel pin M) (maskCoeff p) L evenL
    (graphWick u v pin w (pinList t) ord recM hZ)
  have hfun : G * pf (padK (kernel pin M) (maskCoeff p)) L = (2:ℚ)^t * (W:ℚ)/Z := by
    rw [←hh,Finset.mul_sum]
    unfold W allowedMass
    push_cast
    rw [Finset.mul_sum,Finset.sum_div]
    apply sum_congr rfl
    intro x _
    have hx := evalHit p (fun i => x (pin i)) (padded (pinList t)) 0
    rw [allHits] at hx
    simp only [pow_zero] at hx
    change G * prodAlt (maskCoeff p) (maskSpin (fun i => x (pin i))) L 1 = _ at hx
    calc
      _ = ((rawIsing u v w x : ℚ)/Z) * (G * prodAlt (maskCoeff p) (maskSpin (fun i => x (pin i))) L 1) := by ring
      _ = _ := by rw [hx]; ring
  have hpf : pf (fun i j => (E i j : ℚ)) L = (Z:ℚ)^(L.length/2) * ((2:ℚ)^t * (W:ℚ)/Z) := by
    change pf (fun i j => (fixedEntry u v w pin Z p i j : ℚ)) L = _
    rw [entry_eq u v w pin p hZ,pf_scale _ _ _ evenL,pf_scale_rows]
    rw [←hfun]
  have hd := skew_det_sq E L.get
  rw [List.ofFn_get,hpf] at hd
  change (((intMatrix u v w pin Z p).det : ℤ) : ℚ) = _ at hd
  have ans : ((2:ℚ)^t * (Z:ℚ)^(L.length/2) * W)^2 = (Z:ℚ)^2 *
      (((intMatrix u v w pin Z p).det : ℤ):ℚ) := by
    rw [hd]; field_simp
  exact_mod_cast ans
end BoundaryFixed
namespace BoundaryFixed
open BoundaryPadding BoundaryPin BoundarySwitch BoundaryDet Finset

theorem slotLen (t : ℕ) : (slotList t).length = t + (if Even t then 0 else 1) := by
  unfold slotList padded pinList
  split <;> simp_all

theorem slotGet (t : ℕ) (i : Fin (slotList t).length) :
    (slotList t).get i = (if h : i.val < t then some (⟨i.val,h⟩,false) else none, i.val) := by
  change ((padded (pinList t)).zipIdx)[i.val] = _
  simp only [List.getElem_zipIdx,Nat.zero_add,Prod.mk.injEq,and_true]
  unfold padded
  by_cases h : i.val < t
  · rw [dite_eq_left h,List.getElem_append_left (by simpa [pinList] using h)]
    simp [pinList]
  · rw [dite_eq_right h,List.getElem_append_right (by simpa [pinList] using Nat.le_of_not_gt h)]
    have hi := lt_of_lt_of_eq i.isLt (slotLen t)
    by_cases hE : Even t
    · simp [hE] at hi; omega
    · have hix : i.val = t := by simp [hE] at hi; omega
      simp [pinList,hE,hix]

theorem allowedMass_eq {n m t : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) :
    allowedMass u v w pin p =
    ∑ x : Fin n → Bool, if ∀ i, p i (x (pin i)) = true then rawIsing u v w x else 0 := by
  classical
  unfold allowedMass
  apply sum_congr rfl; intro x _
  by_cases ha : ∀ i, p i (x (pin i)) = true
  · simp [weightMask,ha,bitI]
  · push Not at ha
    obtain ⟨i,hi⟩ := ha
    have hz : weightMask pin p x = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [bitI,hi])
    simp [hz,show ¬(∀ i, p i (x (pin i)) = true) from fun h => by simpa [hi] using h i]

end BoundaryFixed

namespace BoundaryPacked
open Pcx446Arithmetic
open BoundaryFixed BoundaryPin BoundarySwitch Finset
private theorem packed_monomial (m d : ℕ) (w : Fin m → Bool → ℕ) (col : Fin m → Fin 3)
    (diff : Fin m → Bool) :
    let s := m + 1
    let B := 2^d
    let tally (k : Fin 3) := (Finset.univ.filter (fun e => col e = k ∧ diff e = true)).card
    let digit (k : Fin 3) := if k = 0 then s*s else if k = 1 then s else 1
    (∏ e, w e (diff e) * B^(if diff e then digit (col e) else 0)) =
      (∏ e, w e (diff e)) * B^(tally 0 * (s*s) + tally 1 * s + tally 2) := by
  classical
  intro s B tally digit
  let ind (e : Fin m) (k : Fin 3) : ℕ := if col e = k ∧ diff e = true then 1 else 0
  have hs (e : Fin m) : (if diff e then digit (col e) else 0) =
      ind e 0 * (s*s) + ind e 1 * s + ind e 2 := by
    cases h : diff e <;> rcases (show col e = 0 ∨ col e = 1 ∨ col e = 2 by
      generalize col e = c
      fin_cases c <;> decide) with hcol|hcol|hcol <;> simp [ind,digit,h,hcol]
  have hc (k : Fin 3) : (∑ e, ind e k) = tally k := by
    simp [ind,tally,Finset.sum_boole]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  simp_rw [hs, Finset.sum_add_distrib, ← Finset.sum_mul, hc]
private theorem partition_by_histogram {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (cell : X → J) (v : X → ℕ) (B : ℕ) (slot : J → ℕ) :
    (∑ j, (∑ x, if cell x = j then v x else 0)*B^(slot j)) =
    ∑ x, v x * B^(slot (cell x)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

private theorem partition_positive_iff {X : Type*} [Fintype X] (v : X → ℕ)
    (B : ℕ) (hB : 0 < B) (slot : X → ℕ) :
    (∑ x, v x * B^(slot x)) = 0 ↔ ∀ x, v x = 0 := by
  simp [Nat.ne_of_gt hB]

private theorem cell_fits (n m b : ℕ)
    (spin : (Fin n → Bool) → Fin m → Bool)
    (w : Fin m → Bool → Fin (2^b))
    (keep : (Fin n → Bool) → Prop) [DecidablePred keep] :
    (∑ x : Fin n → Bool, if keep x then ∏ e : Fin m, (w e (spin x e)).val else 0)
      < 2^(n+m*b+1) := by
  classical
  have hp (x : Fin n → Bool) : (∏ e : Fin m, (w e (spin x e)).val) ≤ (2^b)^m := by
    calc
      _ ≤ ∏ _e : Fin m, (2^b) := by
        apply Finset.prod_le_prod

        intro e _; exact Nat.le_of_lt (w e (spin x e)).isLt
      _ = _ := by simp
  have hs : (∑ x : Fin n → Bool, if keep x then ∏ e : Fin m, (w e (spin x e)).val else 0)
      ≤ ∑ _x : Fin n → Bool, (2^b)^m := by
    apply Finset.sum_le_sum
    intro x _
    split <;> first | exact hp x | exact Nat.zero_le _
  have hsum : (∑ _x : Fin n → Bool, (2^b)^m) = 2^(n+m*b) := by
    rw [pow_add, Nat.mul_comm m b, pow_mul]; simp
  rw [hsum] at hs
  have hpos := Nat.two_pow_pos (n+m*b)
  rw [pow_succ]
  omega

abbrev Cell (m : ℕ) := Fin (m+1) × Fin (m+1) × Fin (m+1)
def diff {n m : ℕ} (u v : Fin m → Fin n) (x : Fin n → Bool) (e : Fin m) := xor (x (u e)) (x (v e))
def tally {n m : ℕ} (u v : Fin m → Fin n) (col : Fin m → Fin 3) (x : Fin n → Bool)
    (j : Fin 3) : Fin (m+1) :=
  ⟨(univ.filter (fun e => col e=j ∧ diff u v x e=true)).card,
    Nat.lt_succ_of_le (by simpa using (card_filter_le univ (fun e => col e=j ∧ diff u v x e=true)))⟩
def cell {n m : ℕ} (u v : Fin m → Fin n) (col : Fin m → Fin 3) (x : Fin n → Bool) : Cell m :=
  (tally u v col x 0,tally u v col x 1,tally u v col x 2)
def rawWeight {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (x : Fin n → Bool) :=
  ∏ e, (w e (diff u v x e)).val
def rawCell {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (x : Fin n → Bool) (l r h : Fin (m+1)) :=
  if (tally u v col x 0).val=l.val ∧ (tally u v col x 1).val=r.val ∧ (tally u v col x 2).val=h.val
  then rawWeight u v w x else 0
def countCell {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] (l r h : Fin (m+1)) :=
  ∑ x, if P x then rawCell u v w col x l r h else 0

def kronecker {m b : ℕ} (d : ℕ) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (e : Fin m) (a : Bool) : ℕ :=
  (w e a).val * (2^d)^(if a then if col e = 0 then (m+1)*(m+1) else if col e = 1 then m+1 else 1 else 0)

def packed {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] : ℕ :=
  pcxGridPack (fun q : Fin (m+1) × Fin (m+1) × Fin (m+1) × Fin (n+m*b+1) =>
    (countCell u v w col P q.1 q.2.1 q.2.2.1).testBit q.2.2.2.val)

theorem countCell_lt {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] (l r h : Fin (m+1)) :
    countCell u v w col P l r h < 2^(n+m*b+1) := by
  classical
  have he := cell_fits n m b (diff u v) w (fun x =>
    P x ∧ (tally u v col x 0).val=l.val ∧ (tally u v col x 1).val=r.val ∧ (tally u v col x 2).val=h.val)
  convert he using 1
  apply sum_congr rfl
  intro x _
  simp [rawCell,rawWeight,ite_and]

theorem packed_raw {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    (packed u v w col P : ℤ) = ∑ x, if P x then
      rawIsing u v (fun e a => (kronecker (n+m*b+1) w col e a : ℤ)) x else 0 := by
  classical
  let d := n+m*b+1
  let c := cell u v col
  let V := fun x => if P x then rawWeight u v w x else 0
  let slot := fun j : Cell m => pcxGridCode j.1 j.2.1 j.2.2
  have ht (l r h) : countCell u v w col P l r h =
      ∑ x, if c x = (l,r,h) then V x else 0 := by
    apply sum_congr rfl;intro x _
    simp only [c,cell,Prod.mk.injEq,Fin.ext_iff,V,rawCell]
    split <;> split <;> simp_all
  have he := partition_by_histogram c V (2^d) slot
  simp only [Fintype.sum_prod_type] at he
  have hpack : packed u v w col P = ∑ x, V x * (2^d)^(slot (c x)) := by
    rw [packed,pcxGridPack_sum _ (countCell_lt u v w col P),←he]
    apply sum_congr rfl;intro l _
    apply sum_congr rfl;intro r _
    apply sum_congr rfl;intro h _
    rw [ht,pow_mul]
  rw [hpack,Nat.cast_sum]
  apply sum_congr rfl
  intro x _
  have hm := packed_monomial m d (fun e a => (w e a).val) col (diff u v x)
  have hp : (∏ e, kronecker d w col e (diff u v x e)) = rawWeight u v w x * (2^d)^(slot (c x)) := by
    simpa [kronecker,rawWeight,slot,c,cell,tally,pcxGridCode,mul_assoc] using hm
  by_cases hx : P x
  · simp only [V,ite_eq_left hx]
    rw [←hp,Nat.cast_prod];rfl
  · simp [V,hx]

end BoundaryPacked
namespace BoundaryPacked
open Pcx446Arithmetic
open BoundaryFixed BoundaryPin BoundarySwitch BoundaryDet BoundaryPadding Finset

def weighted {n m b : ℕ} (_u : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (e : Fin m) (a : Bool) : ℤ := (kronecker (n+m*b+1) w col e a : ℤ)

def pinned {n t : ℕ} (pin : Fin t → Fin n) (P : Finset (Fin t)) (x : Fin n → Bool) : Prop :=
  ∀ i ∈ P, x (pin i) = false
instance {n t : ℕ} (pin : Fin t → Fin n) (P : Finset (Fin t)) : DecidablePred (pinned pin P) :=
  fun x => inferInstanceAs (Decidable (∀ i ∈ P, x (pin i) = false))
def permit {n t : ℕ} (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) (x : Fin n → Bool) : Prop :=
  ∀ i, p i (x (pin i)) = true
instance {n t : ℕ} (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) : DecidablePred (permit pin p) :=
  fun x => inferInstanceAs (Decidable (∀ i, p i (x (pin i)) = true))

theorem packed_Z {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (pin : Fin t → Fin n) :
    (packed u v w col (pinned pin ∅) : ℤ) =
      spin u v (fun e b => weighted u w col e (bitEquiv.symm b)) 0 := by
  rw [packed_raw,spinBool]
  simp [pinned,sgn,dot]; rfl
theorem packed_falsePair {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (pin : Fin t → Fin n) (i j : Fin t) :
    (packed u v w col (pinned pin {i,j}) : ℤ) = falsePair u v (weighted u w col) pin i j := by
  rw [packed_raw]
  unfold falsePair
  apply sum_congr rfl;intro x _
  simp [pinned]; rfl

theorem packed_allowed {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) :
    (packed u v w col (permit pin p) : ℤ) = allowedMass u v (weighted u w col) pin p := by
  rw [packed_raw,allowedMass_eq];rfl

theorem allowed_bit {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (pin : Fin t → Fin n) (p : Fin t → Bool → Bool) (l r h : Fin (m+1))
    (j : Fin (n+m*b+1)) :
    (allowedMass u v (weighted u w col) pin p).toNat.testBit ((n+m*b+1)*pcxGridCode l r h+j.val) =
    (countCell u v w col (permit pin p) l r h).testBit j.val := by
  rw [←packed_allowed,Int.toNat_natCast,packed,pcxGridPack_read]

def observed (Z : ℤ) {t : ℕ} [NeZero t] (H : Fin t → Fin t → ℤ) (p : Fin t → Bool → Bool) :
    Matrix (Fin (slotList t).length) (Fin (slotList t).length) ℤ :=
  skew (fun i j =>
    let a := (slotList t).get i
    let b := (slotList t).get j
    Z * alpha p a.1 * alpha p b.1 -
      betaSign p a * betaSign p b * (4 * H (atSite b) (atSite a) - Z))

theorem observed_ext {n m t : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → ℤ)
    (pin : Fin t → Fin n) (Z : ℤ) (H : Fin t → Fin t → ℤ) (p : Fin t → Bool → Bool)
    (hH : ∀ i j, i ≠ j → H i j = falsePair u v w pin i j) :
    observed Z H p = intMatrix u v w pin Z p := by
  have he (i j : Fin (slotList t).length) (hij : i ≠ j) :
      let a := (slotList t).get i
      let b := (slotList t).get j
      Z * alpha p a.1 * alpha p b.1 - betaSign p a * betaSign p b * (4 * H (atSite b) (atSite a) - Z) =
        fixedEntry u v w pin Z p a b := by
    dsimp only
    unfold fixedEntry
    by_cases hi : i.val < t <;> by_cases hj : j.val < t
    · rw [slotGet, slotGet, dite_eq_left hi,dite_eq_left hj]
      simp only [atSite,Option.elim_some]
      rw [hH _ _ (by intro h; apply hij; exact Fin.ext (congrArg Fin.val h).symm)]
    all_goals rw [slotGet t i,slotGet t j]; simp [hi,hj,betaSign,beta]
  ext i j
  change skew _ i j = skew _ i j
  unfold skew
  split
  · exact he i j (ne_of_lt (by assumption))
  · split
    · exact congrArg Neg.neg (he j i (ne_of_lt (by assumption)))
    · rfl

theorem packedFixedSquare {n m t b : ℕ} [NeZero t] (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (pin : Fin t → Fin n) (p : Fin t → Bool → Bool)
    (recM : PlanarRec pin (spin u v (fun e b => weighted u w col e (bitEquiv.symm b)))) :
    let Z : ℤ := packed u v w col (pinned pin ∅)
    let H := fun i j => (packed u v w col (pinned pin (if i=j then ∅ else {i,j})) : ℤ)
    let W : ℤ := packed u v w col (permit pin p)
    (2^t * Z^((slotList t).length/2) * W)^2 = Z^2 * (observed Z H p).det := by
  dsimp only
  rw [observed_ext u v (weighted u w col) pin _ _ p (by
    intro i j hij
    rw [ite_eq_right hij]
    exact packed_falsePair u v w col pin i j),packed_Z,packed_allowed]
  exact fixedSquare u v (weighted u w col) pin p recM

end BoundaryPacked
namespace BoundaryPacked
open Pcx446Arithmetic
open BoundaryFixed BoundarySwitch Finset
theorem packed_width {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    packed u v w col P < 2^((m+1)^3*(n+m*b+1)) := pcxGridPack_width _

theorem packed_le_Z {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (pin : Fin t → Fin n) (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    packed u v w col P ≤ packed u v w col (pinned pin ∅) := by
  have he : (packed u v w col P : ℤ) ≤ (packed u v w col (pinned pin ∅) : ℤ) := by
    rw [packed_raw,packed_raw]
    apply sum_le_sum
    intro x _
    have hn : 0 ≤ rawIsing u v (fun e a => (kronecker (n+m*b+1) w col e a : ℤ)) x :=
      prod_nonneg (by intro e _; positivity)
    simp [pinned]
    split <;> simp_all
  exact_mod_cast he

theorem pack_read {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] (l r h : Fin (m+1)) (j : Fin (n+m*b+1)) :
    (packed u v w col P).testBit ((n+m*b+1)*pcxGridCode l r h+j.val) =
      (countCell u v w col P l r h).testBit j.val := pcxGridPack_read _ _ _ _ _

theorem pack_decode {n m b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b))
    (col : Fin m → Fin 3) (P : (Fin n → Bool) → Prop) [DecidablePred P] (l r h : Fin (m+1)) :
    (∑ j : Fin (n+m*b+1), ((packed u v w col P).testBit
        ((n+m*b+1)*pcxGridCode l r h+j.val)).toNat * 2^j.val) = countCell u v w col P l r h := by
  simp_rw [pack_read]
  exact decode _ _ (countCell_lt u v w col P l r h)
end BoundaryPacked

namespace Pcx446Arithmetic
open BoundaryFixed BoundaryPadding

lemma pcxTermSub {N W : ℕ} {A : Set (Sig N)} {F G : (Fin N→Bool)→ℤ} {a b : ℕ}
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A)
    (hf : Build A (pcxSet W F) a) (hg : Build A (pcxSet W G) b) :
    Build A (pcxSet W (fun x=>F x-G x)) (a+b+19*W) := by
  have ab := unionB hf hg
  have op := pcxSubWordB (A:=A∪(pcxSet W F∪pcxSet W G)) W F G (Or.inl h0) (Or.inl h1)
    (fun _ h=>Or.inr (Or.inl h)) (fun _ h=>Or.inr (Or.inr h))
  exact seq2B ab op

lemma pcxTermMul {N W : ℕ} {A : Set (Sig N)} {F G : (Fin N→Bool)→ℤ} {a b : ℕ}
    (h0 : (fun _=>false)∈A) (hf : Build A (pcxSet W F) a) (hg : Build A (pcxSet W G) b) :
    Build A (pcxSet W (fun x=>F x*G x)) (a+b+10*W^2) := by
  exact seq2B (unionB hf hg) (pcxMulWordB W F G (Or.inl h0)
    (fun _ h=>Or.inr (Or.inl h)) (fun _ h=>Or.inr (Or.inr h)))

lemma pcxBitWords {N W : ℕ} {A : Set (Sig N)} (b : Sig N) (h0 : (fun _=>false)∈A) (hb : b∈A) :
    pcxSet W (fun x=>bitI (b x)) ⊆ A := by
  rintro _ ⟨i,rfl⟩
  have e : bitsOf W (fun x=>pcxWord W (bitI (b x))) i = if i.val=0 then b else fun _=>false := by
    funext x
    have nword (c : Bool) : pcxWord W (bitI c) = c.toNat % 2^W := by
      cases c <;> simp [pcxWord,bitI,ZMod.val_one_eq_one_mod]
    change ((pcxWord W (bitI (b x))).testBit i.val) = _
    rw [nword,Nat.testBit_mod_two_pow];simp only [i.isLt,decide_true,Bool.true_and]
    by_cases z : i.val=0 <;> cases e : b x <;> simp [z,e]
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le (by decide : 1<2^1) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [e]; split <;> assumption

lemma pcxMaskAlpha {N t W : ℕ} {A : Set (Sig N)} (p : PcxMask N t) (q : Option (Fin t × Bool))
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) (hm : pcxMaskSigs p⊆A) :
    Build A (pcxSet W (fun x=>alpha (fun i b=>p i b x) q)) (9*W) := by
  cases q with
  | none =>
    exact relaxB (idleB (pcxConstWires W 1 h0 h1)) le_rfl Set.subset_union_right (by omega)
  | some k =>
    apply pcxSumWordB W _ _ h0 <;> apply pcxBitWords _ h0 <;>
      apply hm <;> exact Set.mem_iUnion.mpr ⟨k.1,⟨_,rfl⟩⟩

lemma pcxMaskBeta {N t W : ℕ} {A : Set (Sig N)} (p : PcxMask N t) (q : MaskLabel (Fin t))
    (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A) (hm : pcxMaskSigs p⊆A) :
    Build A (pcxSet W (fun x=>betaSign (fun i b=>p i b x) q)) (19*W+10*W^2) := by
  have b : Build A (pcxSet W (fun x=>beta (fun i v=>p i v x) q.1)) (19*W) := by
    rcases q with ⟨_|k,n⟩
    · exact relaxB (idleB (pcxConstWires W 0 h0 h1)) le_rfl Set.subset_union_right (by omega)
    · apply pcxSubWordB W _ _ h0 h1 <;> apply pcxBitWords _ h0 <;> apply hm <;>
        exact Set.mem_iUnion.mpr ⟨k.1,⟨_,rfl⟩⟩
  exact relaxB (pcxTermMul h0 (idleB (pcxConstWires W ((-1:ℤ)^q.2) h0 h1)) b)
    le_rfl Set.subset_union_right (by omega)

def pcxUpper {t : ℕ} [NeZero t] (z : ℤ) (h : Fin t→Fin t→ℤ) (p : Fin t→Bool→Bool)
    (i j : MaskLabel (Fin t)) : ℤ :=
  z*alpha p i.1*alpha p j.1 - betaSign p i*betaSign p j*(4*h (BoundaryPin.atSite j) (BoundaryPin.atSite i)-z)

lemma pcxUpperB {N t W : ℕ} [NeZero t] {A : Set (Sig N)}
    (z : (Fin N→Bool)→ℤ) (h : Fin t→Fin t→(Fin N→Bool)→ℤ) (p : PcxMask N t)
    (i j : MaskLabel (Fin t)) (h0 : (fun _=>false)∈A) (h1 : (fun _=>true)∈A)
    (hm : pcxMaskSigs p⊆A) (hz : pcxSet W z⊆A) (hh : ∀ i j,pcxSet W (h i j)⊆A) :
    Build A (pcxSet W (fun x=>pcxUpper (z x) (fun i j=>h i j x) (fun i b=>p i b x) i j))
      (70*W^2+94*W) := by
  let four := idleB (pcxConstWires W 4 h0 h1)
  have l := pcxTermMul h0 (pcxTermMul h0 (idleB hz) (pcxMaskAlpha p i.1 h0 h1 hm)) (pcxMaskAlpha p j.1 h0 h1 hm)
  have s := pcxTermMul (W:=W) h0 (pcxMaskBeta p i h0 h1 hm) (pcxMaskBeta p j h0 h1 hm)
  have r := pcxTermSub h0 h1 (pcxTermMul h0 four (idleB (hh (BoundaryPin.atSite j) (BoundaryPin.atSite i)))) (idleB hz)
  exact relaxB (pcxTermSub h0 h1 l (pcxTermMul h0 s r)) le_rfl Set.subset_union_right (by nlinarith)

lemma pcxAlphaAbs {X : Type} (p : X→Bool→Bool) (q : Option (X×Bool)) : |alpha p q|≤2 := by
  cases q with
  | none=>norm_num [alpha]
  | some q=>cases h:p q.1 false <;> cases k:p q.1 true <;> simp [alpha,bitI,h,k]

lemma pcxBetaAbs {X : Type} (p : X→Bool→Bool) (q : MaskLabel X) : |betaSign p q|≤1 := by
  rw [betaSign,abs_mul,abs_pow];simp only [abs_neg,abs_one,one_pow,one_mul]
  rcases q with ⟨_|q,n⟩
  · simp [beta]
  · cases h:p q.1 false <;> cases k:p q.1 true <;> simp [beta,bitI,h,k]

lemma pcxUpperAbs {t : ℕ} [NeZero t] (L : ℕ) (z : ℤ) (h : Fin t→Fin t→ℤ)
    (p : Fin t→Bool→Bool) (i j : MaskLabel (Fin t)) (hz : |z|≤2^L) (hh : ∀ i j, |h i j|≤2^L) :
    |pcxUpper z h p i j| ≤ (2:ℤ)^(L+4) := by
  unfold pcxUpper
  apply (abs_sub _ _).trans
  simp only [abs_mul]
  have a1 := pcxAlphaAbs p i.1;have a2 := pcxAlphaAbs p j.1
  have b1 := pcxBetaAbs p i;have b2 := pcxBetaAbs p j
  have dif : |4*h (BoundaryPin.atSite j) (BoundaryPin.atSite i)-z| ≤ 5 * 2^L := by
    apply (abs_sub _ _).trans
    rw [abs_mul];norm_num;have := hh (BoundaryPin.atSite j) (BoundaryPin.atSite i);omega
  calc
    |z| * |alpha p i.1| * |alpha p j.1| + |betaSign p i| * |betaSign p j| * |4*h (BoundaryPin.atSite j) (BoundaryPin.atSite i)-z| ≤ 2^L*2*2+1*1*(5*2^L) := by gcongr
    _ ≤ (2:ℤ)^(L+4) := by
      rw [pow_add]
      norm_num
      have hpow : 0≤(2:ℤ)^L := by positivity
      omega

end Pcx446Arithmetic

namespace Pcx446Arithmetic
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

lemma startSched (N : Nat) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma constB {N : Nat} {A : Set (Sig N)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

abbrev PcxWidth (t s d : ℕ) := 2+(1+t*t)*s^3*d+2*t+t*t+3*s+d

def pcxInputAt {t s d : ℕ} (data : pcxDomain (pcxFrame t s d)→Bool) (i : Fin (PcxWidth t s d)) :=
  data ((pcxFrame t s d).pos.symm (Fin.cast (pcxFrameSize t s d).symm i))

lemma pcxInputAt_read {t s d : ℕ} (data : pcxDomain (pcxFrame t s d)→Bool) (key) :
    pcxInputData t s d key (pcxInputAt data) = data key := by exact congrArg data ((pcxFrame t s d).pos.symm_apply_apply key)

lemma pcxInputAt_vec {t s d : ℕ} (data : pcxDomain (pcxFrame t s d)→Bool) :
    List.ofFn (pcxInputAt data) = pcxVec (pcxFrame t s d) data := by
  unfold pcxInputAt pcxVec
  exact (List.ofFn_congr (pcxFrameSize t s d) (fun i=>data ((pcxFrame t s d).pos.symm i))).symm

def pcxRawZ {t s d : ℕ} (x : Fin (PcxWidth t s d)→Bool) :=
  pcxGridPack (fun q=>pcxInputData t s d (pcxInputKey q) x)
def pcxRawPair {t s d : ℕ} (i j : Fin t) (x : Fin (PcxWidth t s d)→Bool) :=
  pcxGridPack (fun q=>pcxInputData t s d (pcxPairKey i j q) x)

def pcxBase (N : ℕ) : Set (Sig N) := Set.range (fun i : Fin N => fun x : Fin N→Bool=>x i) ∪
  {(fun _=>false),(fun _=>true)}

lemma pcxRawWords {N s d W : ℕ} {A : Set (Sig N)} (f : Fin s × Fin s × Fin s × Fin d →Sig N)
    (h0 : (fun _=>false) ∈ A) (hf : ∀ q, f q ∈ A) :
    pcxSet W (fun x=>(pcxGridPack (fun q=>f q x):ℤ)) ⊆ A := by
  rintro _ ⟨i,rfl⟩
  let data := fun x=>pcxGridPack (fun q=>f q x)
  have eq : bitsOf W (fun x=>pcxWord W (data x:ℤ)) i = (fun x=>(data x).testBit i.val) := by
    funext x
    change ((↑(↑(data x):ℤ) : ZMod (2^W)).val).testBit i.val = _
    simp [ZMod.val_natCast,Nat.testBit_mod_two_pow,i.isLt]
  change bitsOf W (fun x=>pcxWord W (data x:ℤ)) i ∈ A
  rw [eq]
  by_cases small : i.val<(pcxGrid s d).size
  · let j : Fin (pcxGrid s d).size := ⟨i.val,small⟩
    have e : (fun x=>(data x).testBit i.val) = f ((pcxGrid s d).pos.symm j) := by
      funext x;exact pcxBitsRead_test _ _ j
    rw [e];exact hf _
  · have e : (fun x=>(data x).testBit i.val) = (fun _=>false) := by
      funext x
      apply Nat.testBit_eq_false_of_lt
      exact (pcxBitsRead_lt (pcxGrid s d).size _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    rw [e];exact h0

def pcxHitKey {t s d : ℕ} (a : Fin 3) (i : Fin s) : pcxDomain (pcxFrame t s d) :=
  if a=0 then .inl (.inl (.inl (.inr i))) else if a=1 then .inl (.inl (.inr i)) else .inl (.inr i)

def pcxIdx {t s d : ℕ} (x : Fin (PcxWidth t s d)→Bool) :=
  pcxBitsRead d (fun i=>pcxInputData t s d (.inr i) x)

lemma pcxIdx_avail {t s d : ℕ} (i : Fin d) : bitsOf d (pcxIdx (t:=t) (s:=s)) i ∈ pcxBase (PcxWidth t s d) := by
  apply Or.inl;refine ⟨pcxAddress t s d (.inr i),?_⟩
  funext x;exact (pcxBitsRead_test d (fun j=>pcxInputData t s d (.inr j) x) i).symm

lemma pcxIdx_read {t s d : ℕ} (Z : Fin s→Fin s→Fin s→Fin d→Bool)
    (H : Fin t→Fin t→Fin s→Fin s→Fin s→Fin d→Bool) (m : Fin t→Bool→Bool)
    (r : Fin t→Fin t→Bool) (a b c : Fin s→Bool) (idx : Fin (2^d)) :
    pcxIdx (pcxInputAt (pcxFrameValues Z H m r a b c (fun i=>idx.val.testBit i.val))) = idx.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<d
  · have e := pcxBitsRead_test d (fun i=>pcxInputData t s d (.inr i)
        (pcxInputAt (pcxFrameValues Z H m r a b c (fun i=>idx.val.testBit i.val)))) ⟨j,hj⟩
    exact e.trans (pcxInputAt_read _ (.inr ⟨j,hj⟩))
  · have a0 : (pcxIdx (t:=t) (s:=s) (pcxInputAt (pcxFrameValues Z H m r a b c (fun i=>idx.val.testBit i.val)))).testBit j = false :=
      Nat.testBit_eq_false_of_lt ((pcxBitsRead_lt d _).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [a0,Nat.testBit_eq_false_of_lt (idx.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

lemma pcxAnyListB {N : ℕ} {A : Set (Sig N)} {X : Type} (f : X→Sig N) (xs : List X)
    (cost : ℕ) (zero : (fun _=>false)∈A) (bits : ∀ a∈xs,Build A {f a} cost) :
    Build A {fun x=> xs.any (fun a=>f a x)} (xs.length*(cost+1)) := by
  induction xs with
  | nil =>
    simpa using idleB (Set.singleton_subset_iff.mpr zero)
  | cons a xs ih =>
    have h := bits a (by simp)
    have tail := ih (fun b hb=> bits b (List.mem_cons_of_mem _ hb))
    have op : Build (A ∪ ({f a} ∪ {fun x=>xs.any (fun b=>f b x)}))
        {fun x=>f a x || xs.any (fun b=>f b x)} 1 := orB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    simpa only [List.any_cons,List.length_cons] using
      (relaxB (seq2B (unionB h tail) op) le_rfl Set.subset_union_right (b':=(xs.length+1)*(cost+1)) (by nlinarith))

abbrev PcxCell (s : ℕ) := Fin s × Fin s × Fin s

noncomputable def pcxSelBit {N s : ℕ} (hot : Fin 3→Fin s→Sig N) (bit : PcxCell s→Sig N) : Sig N :=
  fun x=> (Finset.univ : Finset (PcxCell s)).toList.any (fun q=>
    ((hot 0 q.1 x && hot 1 q.2.1 x) && hot 2 q.2.2 x) && bit q x)

lemma pcxSelBitB {N s : ℕ} {A : Set (Sig N)} (hot : Fin 3→Fin s→Sig N) (bit : PcxCell s→Sig N)
    (hh : ∀ i j,hot i j∈A) (hb : ∀ q,bit q∈A) (h0 : (fun _=>false)∈A) :
    Build A {pcxSelBit hot bit} (4*s^3) := by
  let gate := fun (q:PcxCell s) (x:Fin N→Bool)=> ((hot 0 q.1 x && hot 1 q.2.1 x) && hot 2 q.2.2 x) && bit q x
  have g (q : PcxCell s) : Build A {gate q} 3 := by
    have g0 := andB (hh 0 q.1) (hh 1 q.2.1)
    have g1 : Build (A∪{fun x=>hot 0 q.1 x && hot 1 q.2.1 x})
        {fun x=>(hot 0 q.1 x && hot 1 q.2.1 x) && hot 2 q.2.2 x} 1 :=
      andB (Or.inr rfl) (Or.inl (hh 2 q.2.2))
    have g2 : Build (A∪{fun x=>(hot 0 q.1 x && hot 1 q.2.1 x) && hot 2 q.2.2 x}) {gate q} 1 :=
      andB (Or.inr rfl) (Or.inl (hb q))
    exact seq2B (seq2B g0 g1) g2
  have all := pcxAnyListB gate (Finset.univ : Finset (PcxCell s)).toList 3 h0 (fun q _=>g q)
  exact relaxB all le_rfl Set.subset_union_right (by simp [PcxCell];ring_nf;omega)

lemma pcxSelBit_spec {N s : ℕ} (hot : Fin 3→Fin s→Sig N) (bit : PcxCell s→Sig N)
    (x : Fin N→Bool) (target : Fin 3→Fin s) (hh : ∀ i j,hot i j x = decide (target i=j)) :
    pcxSelBit hot bit x = bit (target 0,target 1,target 2) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [pcxSelBit,List.any_eq_true,Finset.mem_toList,Finset.mem_univ,true_and,
    Bool.and_eq_true,hh,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,b,c⟩,⟨⟨⟨ha,hb⟩,hc⟩,h⟩⟩
    simpa [ha,hb,hc] using h
  · intro h;exact ⟨(target 0,target 1,target 2),⟨⟨rfl,rfl⟩,rfl⟩,h⟩

noncomputable def pcxSelectWord {N s d : ℕ} (hot : Fin 3→Fin s→Sig N) (Z : (Fin N→Bool)→ℕ) (x) :=
  pcxBitsRead d fun j=> pcxSelBit hot (fun q y=>(Z y).testBit (d*pcxGridCode q.1 q.2.1 q.2.2+j.val)) x

lemma pcxSelectWordB {N s d : ℕ} {A : Set (Sig N)} (hot : Fin 3→Fin s→Sig N) (Z : (Fin N→Bool)→ℕ)
    (hh : ∀ i j,hot i j∈A) (h0 : (fun _=>false)∈A)
    (hz : Set.range (bitsOf (s^3*d) Z) ⊆ A) :
    Build A (Set.range (bitsOf d (pcxSelectWord (d:=d) hot Z))) (d*(4*s^3)) := by
  apply finSigB _ (4*s^3)
  intro j
  have eq : bitsOf d (pcxSelectWord (d:=d) hot Z) j =
      pcxSelBit hot (fun q y=>(Z y).testBit (d*pcxGridCode q.1 q.2.1 q.2.2+j.val)) := by
    funext x; exact pcxBitsRead_test _ _ _
  rw [eq];apply pcxSelBitB _ _ hh _ h0
  intro q
  have bound := ((pcxGrid s d).pos (q.1,q.2.1,q.2.2,j)).isLt
  rw [pcxGridPos] at bound
  have width : (pcxGrid s d).size = s^3*d := by dsimp [pcxGrid,pcxGroup,pcxLeaf];ring
  refine hz ⟨⟨_,width ▸ bound⟩,rfl⟩

end Pcx446Arithmetic

namespace BoundaryExtract
open Pcx446Arithmetic
def extract (t k z d : ℕ) : ℕ := z * (d.sqrt + 1) / (2^t * z^k + 1)
def width (t k K T : ℕ) := 2*T + K*(k+1) + t + 5
def budget (t k K T : ℕ) :=
  let L := width t k K T
  T*(10*L^2+5*L+1) + 9*L + 10*L^2 + (k*(10*L^2) + 9*L) + L*(28*L+1)

theorem extract_legal (t k z mass T : ℕ) (d : ℤ) (hk : 0<k) (hm : mass ≤ z)
    (small : d < (2:ℤ)^T)
    (eqn : ((2:ℤ)^t * (z:ℤ)^k * mass)^2 = (z:ℤ)^2*d) :
    extract t k z (pcxWord T d) = mass := by
  cases k with
  | zero => omega
  | succ k =>
    by_cases hz : z = 0
    · have hm0 : mass = 0 := by omega
      simp [extract,hz,hm0]
    let r := 2^t * z^k * mass
    have hzI : (z:ℤ) ≠ 0 := by exact_mod_cast hz
    have he : (r:ℤ)^2 = d := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hzI)
      rw [←eqn]
      dsimp [r]
      ring
    have hd : pcxWord T d = r^2 := by
      rw [←he] at small ⊢
      rw [pcxWord_small T _ (sq_nonneg _) small]
      rw [←Nat.cast_pow,Int.toNat_natCast]
    rw [extract,hd,Nat.sqrt_eq']
    let a := 2^t * z^(k+1)
    have hr : z*r = a*mass := by dsimp [a,r]; ring
    have ha : z ≤ a := by
      have h : 1 ≤ 2^t * z^k := by
        have hp : 0 < 2^t * z^k := by positivity
        omega
      dsimp [a]; rw [pow_succ,←mul_assoc]; simpa using Nat.mul_le_mul_right z h
    change z*(r+1)/(a+1) = mass
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < a+1)).mpr
      nlinarith
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < a+1)).mpr
      nlinarith

def wires {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) := Set.range (bitsOf L F)

lemma widen {N : ℕ} {A : Set (Sig N)} {K : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ)
    (h0 : (fun _ => false) ∈ A) (hF : wires K F ⊆ A) (small : ∀ x, F x < 2^K) :
    wires L F ⊆ A := by
  rintro _ ⟨i,rfl⟩
  by_cases h : i.val < K
  · exact hF ⟨⟨i.val,h⟩,rfl⟩
  · have he : bitsOf L F i = fun _ => false := funext fun x =>
      Nat.testBit_eq_false_of_lt ((small x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [he]; exact h0

lemma constants {N : ℕ} {A : Set (Sig N)} (L a : ℕ) (h0 : (fun _ => false)∈A)
    (h1 : (fun _ => true)∈A) : wires L (fun _ => a) ⊆ A := by
  rintro _ ⟨i,rfl⟩
  change (fun _ => a.testBit i.val) ∈ A
  cases a.testBit i.val <;> assumption

lemma powerBuild {N L : ℕ} {A : Set (Sig N)} (t k : ℕ) (Z : (Fin N → Bool) → ℕ)
    (h0 : (fun _ => false)∈A) (h1 : (fun _ => true)∈A) (hZ : wires L Z ⊆ A) (sz : ∀ x, Z x < 2^L) :
    Build A (wires L (fun x => 2^t * (Z x)^k)) (k*(10*L^2)) := by
  induction k with
  | zero => simpa using idleB (constants L (2^t) h0 h1)
  | succ k ih =>
    let F := fun x => 2^t * (Z x)^k
    have m := pcxMulBuild (A:=A ∪ wires L F) L F Z (Or.inl h0)
      (fun i => Or.inr ⟨i,rfl⟩) (fun i => Or.inl (hZ ⟨i,rfl⟩))
      (fun x => decode _ L (sz x))
    simpa only [F,wires,pow_succ,Nat.succ_mul,mul_assoc] using seq2B ih m
end BoundaryExtract
namespace BoundaryExtract
open Pcx446Arithmetic
lemma widths (t k K T z d : ℕ) (hz : z < 2^K) (hd : d < 2^T) :
    z*(d.sqrt+1) < 2^(width t k K T) ∧ 2*(2^t*z^k+1) ≤ 2^(width t k K T) := by
  have hnum : z*(d.sqrt+1) < 2^(K+T) := by
    rw [pow_add]
    have hs := Nat.sqrt_le_self d
    exact Nat.mul_lt_mul_of_lt_of_le hz (by omega) (by omega)
  have hs : z^k ≤ 2^(K*k) := by rw [pow_mul]; gcongr
  have hp : 2^t*z^k ≤ 2^(t+K*k) := by rw [pow_add]; gcongr
  have hden : 2*(2^t*z^k+1) ≤ 2^(t+K*k+2) := by
    rw [pow_add]; have hh := Nat.two_pow_pos (t+K*k); norm_num; omega
  have a : K+T ≤ width t k K T := by unfold width; rw [Nat.mul_succ]; omega
  have b : t+K*k+2 ≤ width t k K T := by unfold width; rw [Nat.mul_succ]; omega
  exact ⟨hnum.trans_le (Nat.pow_le_pow_right (by decide) a), hden.trans (Nat.pow_le_pow_right (by decide) b)⟩

theorem extractBuild {N : ℕ} {A : Set (Sig N)} (t k K T : ℕ) (Z D : (Fin N → Bool) → ℕ)
    (h0 : (fun _ => false)∈A) (h1 : (fun _ => true)∈A)
    (zw : wires K Z ⊆ A) (dw : wires T D ⊆ A)
    (zs : ∀ x, Z x < 2^K) (ds : ∀ x, D x < 2^T) :
    Build A (wires K (fun x => extract t k (Z x) (D x))) (budget t k K T) := by
  let L := width t k K T
  let root := fun x => (D x).sqrt
  let num := fun x => Z x * (root x + 1)
  let den := fun x => 2^t * (Z x)^k + 1
  have hzt : K ≤ L := by unfold L width; rw [Nat.mul_succ]; omega
  have hdt : 2*T ≤ L := by unfold L width; omega
  have zL := widen L Z h0 zw zs
  have dL := widen L D h0 dw ds
  have zsL x := (zs x).trans_le (Nat.pow_le_pow_right (by decide) hzt)
  have hw x := widths t k K T (Z x) (D x) (zs x) (ds x)
  have hr : Build A (wires L root) (T*(10*L^2+5*L+1)) :=
    pcxSqrtB T D h0 h1 (fun i => dL ⟨i,rfl⟩) hdt
      (fun x => (ds x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have plus {S : Set (Sig N)} (F : (Fin N → Bool) → ℕ) (Fbits : wires L F ⊆ S)
      (z0 : (fun _ => false)∈S) (z1 : (fun _ => true)∈S) :
      Build S (wires L (fun x => F x + 1)) (9*L) :=
    sumTwoB L F (fun _ => 1) z0 (fun i => Fbits ⟨i,rfl⟩)
      (fun i => constants L 1 z0 z1 ⟨i,rfl⟩)
  have hplus := seq2B hr (plus root Set.subset_union_right (Or.inl h0) (Or.inl h1))
  have hnum : Build A (wires L num) (T*(10*L^2+5*L+1)+9*L+10*L^2) := by
    apply seq2B hplus
    have m := pcxMulBuild (A:=A ∪ wires L (fun x => root x+1)) L (fun x => root x + 1) Z (Or.inl h0)
      (fun i => Or.inr ⟨i,rfl⟩) (fun i => Or.inl (zL ⟨i,rfl⟩))
      (fun x => decode _ _ (zsL x))
    simpa only [num,wires,mul_comm] using m
  have hp := powerBuild t k Z h0 h1 zL zsL
  have hden := seq2B hp (plus (fun x => 2^t * (Z x)^k) Set.subset_union_right (Or.inl h0) (Or.inl h1))
  have both := unionB hnum hden
  let S := A ∪ (wires L num ∪ wires L den)
  have div := pcxDivideBuild (A:=S) (W:=L) L num den (Or.inl h0) (Or.inl h1)
    (fun i => Or.inr (Or.inl ⟨i,rfl⟩)) (fun x => (hw x).1)
    (fun i => Or.inr (Or.inr ⟨i,rfl⟩)) (fun _ => Nat.zero_lt_succ _) (fun x => (hw x).2)
  apply relaxB (seq2B both div) le_rfl _ le_rfl
  rintro _ ⟨i,rfl⟩
  exact Or.inr (Or.inl ⟨⟨i.val,lt_of_lt_of_le i.isLt hzt⟩,rfl⟩)
end BoundaryExtract

namespace BoundaryFinish
open Pcx446Arithmetic PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def inputs (N : ℕ) : Set (Sig N) := Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)

theorem finishExact {N C : ℕ} {α : Type*} (hn : 1 < N) (out : α → Sig N)
    (built : Build (inputs N ∪ {fun _ => false,fun _ => true}) (Set.range out) C) :
    ∃ (g : Circuit) (wire : α → Fin (N+g.size)),
      ReadsBack N g ∧ g.size ≤ C+2 ∧
      (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length=2) ∨
        (gate.op = .not ∧ gate.inputs.length=1)) ∧
      ∀ (x : Fin N → Bool), x ⟨0,by omega⟩ = false → x ⟨1,hn⟩ = true →
        ∀ a, (g.wires (List.ofFn x)).getD (wire a).val false = out a x := by
  classical
  have cst : Build (inputs N) ({fun _ => false, fun _ => true} : Set (Sig N)) 2 := by
    have h := unionB (constB (A:=inputs N) false) (constB (A:=inputs N) true)
    exact relaxB h le_rfl (by intro f hf; rcases hf with rfl|hf <;> aesop) le_rfl
  have hw := seq2B cst built
  obtain ⟨sz,hsz,hs⟩ := hw 0 (inputs N) (startSched N) le_rfl
  rw [Nat.zero_add] at hs
  obtain ⟨gs,hgs,hback,hfan,hout⟩ := hs
  let c := Circuit.mk gs 0
  let g := pcxExactCircuit c
  have hsize : g.size = sz := by simpa [g,pcxExactCircuit,c,Circuit.size] using hgs
  have hwire (a : α) := hout (out a) (Or.inr ⟨a,rfl⟩)
  choose i hi hw using hwire
  refine ⟨g,fun a => ⟨i a,by rw [hsize]; exact hi a⟩,pcxExactCircuit_back N c hn hback,
    by rw [hsize]; omega,?_,?_⟩
  · intro gate hgate
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hgate
    exact pcxExactGate_shape q
  · intro x hx0 hx1 a
    have get0 : (List.ofFn x).getD 0 false = false := by rw [List.getD_eq_getElem _ _ (by simp; omega)]; simpa using hx0
    have get1 : (List.ofFn x).getD 1 false = true := by rw [List.getD_eq_getElem _ _ (by simp; omega)]; simpa using hx1
    change ((Circuit.mk (gs.map pcxExactGate) 0).wires _).getD (i a) false = _
    rw [pcxExactFold gs hfan _ (by simpa using hn) get0 get1]
    exact hw a x
end BoundaryFinish

namespace Pcx446Arithmetic
open BoundaryFixed

def pcxObs {t s d : ℕ} [NeZero t] (mask : PcxMask (PcxWidth t s d) t) (x : Fin (PcxWidth t s d)→Bool) :=
  BoundaryPacked.observed (pcxRawZ x : ℤ) (fun i j=>(pcxRawPair i j x:ℤ)) (fun i b=>mask i b x)

def pcxDetBudget (q W : ℕ) := q*(q*(9*W))+q*(q*(q*(78*W^2+48*W)))
def pcxRecoveryBudget (t s d : ℕ) :=
  let q := (slotList t).length
  let K := s^3*d
  let W := pcxDetWork q (K+4)
  let T := pcxDetShiftBits q (K+4)
  q*(q*(80*W^2+120*W)) + pcxDetBudget q W + BoundaryExtract.budget t (q/2) K T

noncomputable def pcxMassWord {t s d : ℕ} [NeZero t] (mask : PcxMask (PcxWidth t s d) t)
    (x : Fin (PcxWidth t s d)→Bool) :=
  let q := (slotList t).length
  let T := pcxDetShiftBits q (s^3*d+4)
  BoundaryExtract.extract t (q/2) (pcxRawZ x) (pcxWord T (pcxObs mask x).det)

lemma pcxObsBound {t s d : ℕ} [NeZero t] (mask : PcxMask (PcxWidth t s d) t)
    (x : Fin (PcxWidth t s d)→Bool) (i j : Fin (slotList t).length) :
    |pcxObs mask x i j| ≤ (2:ℤ)^(s^3*d+4) := by
  let K := s^3*d
  have hz : |(pcxRawZ x:ℤ)|≤(2:ℤ)^K := by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast (pcxGridPack_width _ : pcxRawZ x < 2^K).le
  have hh (i j : Fin t) : |(pcxRawPair i j x:ℤ)|≤(2:ℤ)^K := by
    rw [abs_of_nonneg (Int.natCast_nonneg _)];exact_mod_cast (pcxGridPack_width _ : pcxRawPair i j x < 2^K).le
  let U := fun a b : Fin (slotList t).length => pcxUpper (pcxRawZ x) (fun i j=>pcxRawPair i j x) (fun i b=>mask i b x) ((slotList t).get a) ((slotList t).get b)
  have upper (a b) : |U a b| ≤ (2:ℤ)^(K+4) := pcxUpperAbs K _ _ _ _ _ hz hh
  change |if i < j then U i j else if j < i then -U j i else 0| ≤ _
  split
  · exact upper i j
  · split
    · rw [abs_neg];exact upper j i
    · simp

lemma pcxObsDetBound {t s d : ℕ} [NeZero t] (mask : PcxMask (PcxWidth t s d) t) (x) :
    (pcxObs mask x).det < (2:ℤ)^(pcxDetShiftBits (slotList t).length (s^3*d+4)) := by
  let q := (slotList t).length
  have le := pcxDetBound q (s^3*d+4) (pcxObs mask x) (pcxObsBound mask x)
  apply lt_of_le_of_lt ((le_abs_self _).trans le)
  apply pow_lt_pow_right₀ (by norm_num)
  change q*(q+(s^3*d+4)) < (q+1)*(q+1+(s^3*d+4))+2
  generalize s^3*d+4 = L; nlinarith

lemma pcxMatrixCost (W : ℕ) : 70*W^2+94*W≤80*W^2+120*W ∧ 0+(70*W^2+94*W)+19*W≤80*W^2+120*W := by constructor <;> nlinarith

lemma pcxMassWordB {t s d : ℕ} [NeZero t] {S : Set (Sig (PcxWidth t s d))}
    (mask : PcxMask (PcxWidth t s d) t) (base : pcxBase (PcxWidth t s d)⊆S) (hm : pcxMaskSigs mask⊆S) :
    Build S (Set.range (bitsOf (s^3*d) (pcxMassWord mask))) (pcxRecoveryBudget t s d) := by
  let q := (slotList t).length
  let K := s^3*d
  let W := pcxDetWork q (K+4)
  let T := pcxDetShiftBits q (K+4)
  let A := pcxObs mask
  have h0 : (fun _=>false)∈S := base (Or.inr (by simp))
  have h1 : (fun _=>true)∈S := base (Or.inr (by simp))
  have z (L) : pcxSet L (fun x=>(pcxRawZ (t:=t) (s:=s) (d:=d) x:ℤ)) ⊆ S :=
    pcxRawWords (fun q=>pcxInputData t s d (pcxInputKey q)) h0 (fun q=>base (Or.inl ⟨_,rfl⟩))
  have h (L) (i j : Fin t) : pcxSet L (fun x=>(pcxRawPair (s:=s) (d:=d) i j x:ℤ)) ⊆ S :=
    pcxRawWords (fun q=>pcxInputData t s d (pcxPairKey i j q)) h0 (fun q=>base (Or.inl ⟨_,rfl⟩))
  have upper (i j : Fin q) := pcxUpperB (W:=W) _ _ mask ((slotList t).get i) ((slotList t).get j) h0 h1 hm (z W) (h W)
  have entry (i j : Fin q) : Build S (pcxSet W (fun x=>A x i j)) (80*W^2+120*W) := by
    by_cases hlt : i < j
    · have eq : (fun x=>A x i j) = _ := funext fun x=>
        ite_eq_left (α:=ℤ) (t:=pcxUpper (pcxRawZ x) (fun a b=>pcxRawPair a b x) (fun a b=>mask a b x) ((slotList t).get i) ((slotList t).get j)) hlt
      exact relaxB (upper i j) le_rfl (by rw [eq];exact Set.subset_union_right) (pcxMatrixCost W).1
    · by_cases hgt : j < i
      · let e := fun x=>pcxUpper (pcxRawZ x) (fun a b=>pcxRawPair a b x)
          (fun a b=>mask a b x) ((slotList t).get j) ((slotList t).get i)
        have eq : (fun x=>A x i j) = fun x=> (0:ℤ)-e x := by
          funext x;simp [A,pcxObs,BoundaryPacked.observed,BoundaryDet.skew,hlt,hgt,e,pcxUpper]
        rw [eq]; exact relaxB (pcxTermSub h0 h1 (idleB (pcxConstWires W 0 h0 h1)) (upper j i))
          le_rfl Set.subset_union_right (pcxMatrixCost W).2
      · have eq : (fun x=>A x i j) = fun _=>(0:ℤ) := by funext x;simp [A,pcxObs,BoundaryPacked.observed,BoundaryDet.skew,hlt,hgt]
        rw [eq];exact relaxB (idleB (pcxConstWires W 0 h0 h1)) le_rfl Set.subset_union_right (by omega)
  let grid := ⋃ i, ⋃ j, pcxSet W (fun x=>A x i j)
  have buildGrid : Build S grid (q*(q*(80*W^2+120*W))) :=
    finB _ (q*(80*W^2+120*W)) (fun i=>finB _ (80*W^2+120*W) (entry i))
  have det := pcxShiftGate (S:=S∪grid) (K+4) A (pcxObsBound mask) (Or.inl h0) (Or.inl h1)
    (fun i j a ha=>Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,ha⟩⟩))
  have ready := seq2B buildGrid det
  let DS := pcxSet T (fun x=>(A x).det)
  have zs (x) : pcxRawZ (t:=t) (s:=s) (d:=d) x < 2^K := pcxGridPack_width _
  have zw : BoundaryExtract.wires K pcxRawZ ⊆ S ∪ DS := by
    rintro a ⟨i,rfl⟩
    apply Or.inl
    apply z K
    refine ⟨i,?_⟩;funext x
    change (pcxWord K (pcxRawZ x:ℤ)).testBit i.val = (pcxRawZ x).testBit i.val
    rw [pcxWord_small K _ (by positivity) (by exact_mod_cast zs x),Int.toNat_natCast]
  have ext := BoundaryExtract.extractBuild t (q/2) K T pcxRawZ (fun x=>pcxWord T (A x).det)
    (Or.inl h0) (Or.inl h1) zw Set.subset_union_right zs (fun _=>pcxWord_bound _ _)
  exact seq2B ready ext

end Pcx446Arithmetic

namespace BoundaryExtract
theorem budget_bound (t k K T : ℕ) : budget t k K T ≤ (t+k+K+T+10)^7 := by
  let s := t+k+K+T
  have ht : t ≤ s := by dsimp [s]; omega
  have hk : k ≤ s := by dsimp [s]; omega
  have hK : K ≤ s := by dsimp [s]; omega
  have hT : T ≤ s := by dsimp [s]; omega
  have hw : width t k K T ≤ (s+10)^2 := by
    calc
      _ ≤ 2*s+s*(s+1)+s+5 := by unfold width; gcongr
      _ ≤ _ := by nlinarith
  calc
    _ ≤ s*(10*((s+10)^2)^2+5*((s+10)^2)+1)+9*((s+10)^2)+10*((s+10)^2)^2+
        (s*(10*((s+10)^2)^2)+9*((s+10)^2)) + ((s+10)^2)*(28*((s+10)^2)+1) := by
      dsimp only [budget]; gcongr
    _ ≤ (s+10)^7 := by ring_nf; omega
end BoundaryExtract
namespace BoundaryBudget
open Pcx446Arithmetic
private theorem plus {B a b i j : ℕ} (hB : 2 ≤ B) (ha : a ≤ B^i) (hb : b ≤ B^j) :
    a+b ≤ B^(max i j+1) := by
  have hl := Nat.pow_le_pow_right (by omega : 0<B) (Nat.le_max_left i j)
  have hr := Nat.pow_le_pow_right (by omega : 0<B) (Nat.le_max_right i j)
  rw [pow_succ]
  calc
    _ ≤ B^(max i j)+B^(max i j) := Nat.add_le_add (ha.trans hl) (hb.trans hr)
    _ = B^(max i j)*2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hB
private theorem times {B a b i j : ℕ} (ha : a ≤ B^i) (hb : b ≤ B^j) :
    a*b ≤ B^(i+j) := by rw [pow_add]; exact Nat.mul_le_mul ha hb
private theorem power {B a i : ℕ} (k : ℕ) (ha : a ≤ B^i) :
    a^k ≤ B^(i*k) := by rw [pow_mul]; exact Nat.pow_le_pow_left ha k

def P (q W t k K T : ℕ) :=
  q*(q*(80*W^2+120*W)) + (q*(q*(9*W))+q*(q*(q*(78*W^2+48*W)))) + BoundaryExtract.budget t k K T
def M (P d s : ℕ) := P+d*(4*s^3)
def total (P M t d : ℕ) := P + (t*(16*t+28*d+1+M)+M+5*d+t) + 2

set_option maxHeartbeats 3000000 in
theorem bound (n m t b q k : ℕ) (hq : q ≤ t+1) (hk : k ≤ q) :
    let s := m+1
    let d := n+m*b+1
    let K := s^3*d
    let L := K+4
    let T := pcxDetShiftBits q L
    let W := pcxDetWork q L
    let p := P q W t k K T
    total p (M p d s) t d ≤ (n+m+t+b+2)^128 := by
  let B := n+m+t+b+2
  have hB : 2 ≤ B := by unfold B; omega
  have hn1 : n ≤ B^1 := by simp [B]; omega
  have hm1 : m ≤ B^1 := by simp [B]; omega
  have ht1 : t ≤ B^1 := by simp [B]; omega
  have hb1 : b ≤ B^1 := by simp [B]; omega
  have hq1 : q ≤ B^1 := by simp [B]; omega
  have hk1 : k ≤ B^1 := by simp [B]; omega
  have hc1 : 1 ≤ B^0 := (show 1 ≤ 2^0 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc2 : 2 ≤ B^1 := (show 2 ≤ 2^1 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc3 : 3 ≤ B^2 := (show 3 ≤ 2^2 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc4 : 4 ≤ B^2 := (show 4 ≤ 2^2 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc5 : 5 ≤ B^3 := (show 5 ≤ 2^3 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc9 : 9 ≤ B^4 := (show 9 ≤ 2^4 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc10 : 10 ≤ B^4 := (show 10 ≤ 2^4 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc16 : 16 ≤ B^4 := (show 16 ≤ 2^4 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc28 : 28 ≤ B^5 := (show 28 ≤ 2^5 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc48 : 48 ≤ B^6 := (show 48 ≤ 2^6 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc78 : 78 ≤ B^7 := (show 78 ≤ 2^7 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc80 : 80 ≤ B^7 := (show 80 ≤ 2^7 by decide).trans (Nat.pow_le_pow_left hB _)
  have hc120 : 120 ≤ B^7 := (show 120 ≤ 2^7 by decide).trans (Nat.pow_le_pow_left hB _)
  let s := m+1
  have hs_raw := (plus hB hm1 hc1)
  have hs : s ≤ B^2 := hs_raw
  let d := n+m*b+1
  have hd_raw := (plus hB (plus hB hn1 (times hm1 hb1)) hc1)
  have hd : d ≤ B^4 := hd_raw
  let K := s^3*d
  have hK_raw := (times (power 3 hs) hd)
  have hK : K ≤ B^10 := hK_raw
  let L := K+4
  have hL_raw := (plus hB hK hc4)
  have hL : L ≤ B^11 := hL_raw
  let T := pcxDetShiftBits q L
  have hT_raw := (plus hB (times (plus hB hq1 hc1) (plus hB (plus hB hq1 hc1) hL)) hc2)
  have hT : T ≤ B^15 := hT_raw
  let W := pcxDetWork q L
  have hW_raw := (plus hB (times hc3 (times (plus hB hq1 hc1) (plus hB (plus hB hq1 hc1) (plus hB hT hc1)))) hc2)
  have hW : W ≤ B^22 := hW_raw
  let arg := t+k+K+T+10
  have harg_raw := (plus hB (plus hB (plus hB (plus hB ht1 hk1) hK) hT) hc10)
  have harg : arg ≤ B^17 := harg_raw
  have h7 := power 7 harg
  have hh := (BoundaryExtract.budget_bound t k K T).trans h7
  have hbudget : BoundaryExtract.budget t k K T ≤ B^119 := hh
  let p := P q W t k K T
  have hp_raw := (plus hB (plus hB (times hq1 (times hq1 (plus hB (times hc80 (power 2 hW)) (times hc120 hW)))) (plus hB (times hq1 (times hq1 (times hc9 hW))) (times hq1 (times hq1 (times hq1 (plus hB (times hc78 (power 2 hW)) (times hc48 hW))))))) hbudget)
  have hp : p ≤ B^120 := hp_raw
  let oracle := M p d s
  have horacle_raw := (plus hB hp (times hd (times hc4 (power 3 hs))))
  have horacle : oracle ≤ B^121 := horacle_raw
  let out := total p oracle t d
  have hout_raw := (plus hB (plus hB hp (plus hB (plus hB (plus hB (times ht1 (plus hB (plus hB (plus hB (times hc16 ht1) (times hc28 hd)) hc1) horacle)) horacle) (times hc5 hd)) ht1)) hc2)
  have hout : out ≤ B^128 := hout_raw
  exact hout
end BoundaryBudget

namespace Pcx446Arithmetic
open BoundaryPacked BoundaryFixed

abbrev PcxOut (t s d : ℕ) := (Fin s × Fin s × Fin s × Fin d) ⊕ (Unit ⊕ Fin t)

def pcxReadMask (t s d : ℕ) : PcxMask (PcxWidth t s d) t := fun i b=>pcxInputData t s d (pcxMaskKey i b)

def pcxReadRow (t s d : ℕ) [NeZero t] (k : ℕ) (j : Fin t) :=
  pcxInputData t s d (pcxOrderKey (⟨k%t,Nat.mod_lt _ (NeZero.pos t)⟩ : Fin t) j)

def pcxReadHot (t s d : ℕ) (a : Fin 3) (j : Fin s) := pcxInputData t s d (pcxHitKey a j)

noncomputable def pcxOneCount {t s d : ℕ} [NeZero t] (M : PcxMask (PcxWidth t s d) t) :=
  pcxSelectWord (d:=d) (pcxReadHot t s d) (pcxMassWord M)

noncomputable def pcxOutSignal (t s d : ℕ) [NeZero t] : PcxOut t s d → Sig (PcxWidth t s d)
  | .inl ⟨l,r,h,j⟩ => fun x=>(pcxMassWord (pcxReadMask t s d) x).testBit (d*pcxGridCode l r h+j.val)
  | .inr (.inl _) => fun x=>decide (pcxIdx x < pcxOneCount (pcxReadMask t s d) x)
  | .inr (.inr i) => fun x=>(pcxPicked pcxIdx pcxOneCount (pcxReadMask t s d) (pcxReadRow t s d) x).testBit (t-1-i.val)

def pcxWholeCost (t s d : ℕ) :=
  let P := pcxRecoveryBudget t s d
  let C := P+d*(4*s^3)
  P+(t*(16*t+28*d+1+C)+C+5*d+t)

lemma pcxOneCountB {t s d : ℕ} [NeZero t] (M : PcxMask (PcxWidth t s d) t)
    (S : Set (Sig (PcxWidth t s d))) (base : pcxBase (PcxWidth t s d)⊆S) (hm : pcxMaskSigs M⊆S) :
    Build S (Set.range (bitsOf d (pcxOneCount M))) (pcxRecoveryBudget t s d + d*(4*s^3)) := by
  let G := Set.range (bitsOf (s^3*d) (pcxMassWord M))
  have first := pcxMassWordB M base hm
  have out : Build (S∪G) (Set.range (bitsOf d (pcxOneCount M))) (d*(4*s^3)) :=
    pcxSelectWordB (pcxReadHot t s d) _ (fun i j=>Or.inl (base (Or.inl ⟨_,rfl⟩)))
      (Or.inl (base (Or.inr (by simp)))) Set.subset_union_right
  exact seq2B first out

lemma pcxAllOutB (t s d : ℕ) [NeZero t] :
    Build (pcxBase (PcxWidth t s d)) (Set.range (pcxOutSignal t s d)) (pcxWholeCost t s d) := by
  let A := pcxBase (PcxWidth t s d)
  let M := pcxReadMask t s d
  let C := pcxRecoveryBudget t s d + d*(4*s^3)
  have h0 : (fun _=>false) ∈ A := Or.inr (by simp)
  have h1 : (fun _=>true) ∈ A := Or.inr (by simp)
  have hm : pcxMaskSigs M ⊆ A := by
    intro f hf;obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp hf;exact Or.inl ⟨_,rfl⟩
  have idx : Set.range (bitsOf d (pcxIdx (t:=t) (s:=s))) ⊆ A := by
    rintro _ ⟨i,rfl⟩;exact pcxIdx_avail i
  have sw (m : PcxMask (PcxWidth t s d) t) (x) : pcxOneCount m x < 2^d := pcxBitsRead_lt _ _
  have scan := pcxOutputsB M pcxIdx (pcxReadRow t s d) pcxOneCount C h0 h1 hm idx
    (fun k i=>Or.inl ⟨_,rfl⟩) (fun x=>pcxBitsRead_lt _ _) sw (fun m S hs hv=>pcxOneCountB m S hs hv)
  have all := unionB (pcxMassWordB M le_rfl hm) scan
  apply relaxB all le_rfl _ le_rfl
  rintro _ ⟨(⟨l,r,h,j⟩|_|i),rfl⟩
  · have bd := ((pcxGrid s d).pos (l,r,h,j)).isLt
    rw [pcxGridPos] at bd
    have width : (pcxGrid s d).size = s^3*d := by dsimp [pcxGrid,pcxGroup,pcxLeaf];ring
    exact Or.inr (Or.inl ⟨⟨_,width ▸ bd⟩,rfl⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · apply Or.inr;apply Or.inr;apply Or.inr
    refine ⟨i.rev,?_⟩;funext x; simp [pcxOutSignal,bitsOf,Fin.rev,Nat.sub_sub,Nat.add_comm,M]

lemma pcxAllCircuit (n m t b : ℕ) [NeZero t] :
    let s:=m+1
    let d:=n+m*b+1
    let N:=PcxWidth t s d
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (addr : PcxOut t s d→Fin (N+g.size)),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack N g ∧ g.size ≤ (n+m+t+b+2)^128 ∧
      (∀ gate∈g.gates, ((gate.op=.and ∨ gate.op=.or) ∧ gate.inputs.length=2) ∨
        (gate.op=.not ∧ gate.inputs.length=1)) ∧
      ∀ x : Fin N→Bool, x ⟨0,by dsimp [N,PcxWidth];omega⟩=false →
        x ⟨1,by dsimp [N,PcxWidth];omega⟩=true →
        ∀ a,(g.wires (List.ofFn x)).getD (addr a).val false = pcxOutSignal t s d a x := by
  dsimp only
  let s:=m+1;let d:=n+m*b+1
  have hn : 1 < PcxWidth t s d := by unfold PcxWidth;omega
  obtain ⟨g,addr,back,sz,shape,obs⟩ := BoundaryFinish.finishExact hn (pcxOutSignal t s d) (pcxAllOutB t s d)
  refine ⟨g,addr,back,sz.trans ?_,shape,obs⟩
  let q := (slotList t).length
  have hq : q ≤ t+1 := by dsimp [q];rw [slotLen];split <;> omega
  exact BoundaryBudget.bound n m t b q (q/2) hq (Nat.div_le_self ..)

lemma pcxMeaning {n m t b : ℕ} [NeZero t]
    (u v : Fin m→Fin n) (w : Fin m→Bool→Fin (2^b)) (col : Fin m→Fin 3)
    (pin : Fin t→Fin n) (per : Fin t→Bool→Bool) (order : Equiv.Perm (Fin t))
    (a y z : Fin (m+1)) (index : Fin (2^(n+m*b+1)))
    (x : Fin (PcxWidth t (m+1) (n+m*b+1)) → Bool)
    (mask : ∀ i b', pcxReadMask t (m+1) (n+m*b+1) i b' x = per i b')
    (rot : ∀ k j, pcxReadRow t (m+1) (n+m*b+1) k j x =
      decide (order ⟨k%t,Nat.mod_lt _ (NeZero.pos t)⟩ = j))
    (idx : pcxIdx x = index.val)
    (mass : ∀ M,pcxMassWord M x = BoundaryPacked.packed u v w col (permit pin (fun i b'=>M i b' x)))
    (pick : ∀ M,pcxOneCount M x = countCell u v w col (permit pin (fun i b'=>M i b' x)) a y z) :
    let s:=m+1
    let d:=n+m*b+1
    let out := fun key=>pcxOutSignal t s d key x
    let weight := fun (l r h : Fin s) (ω : Fin n→Bool)=>if permit pin per ω then rawCell u v w col ω l r h else 0
    let code := fun (ω : Fin n→Bool)=>∑ i : Fin t,(ω (pin (order i))).toNat*2^(t-1-i.val)
    let chosen := ∑ i : Fin t,(out (.inr (.inr i))).toNat*2^(t-1-i.val)
    (∀ l r h,(∑ j : Fin d, (out (.inl (l,r,h,j))).toNat*2^j.val) = ∑ ω,weight l r h ω) ∧
      out (.inr (.inl ())) = decide (index.val < ∑ ω,weight a y z ω) ∧
      if index.val < ∑ ω,weight a y z ω then (∑ ω,if code ω<chosen then weight a y z ω else 0) ≤ index.val ∧
        index.val < (∑ ω,if code ω≤chosen then weight a y z ω else 0) else chosen=0 := by
  classical
  let s:=m+1;let d:=n+m*b+1
  let M:=pcxReadMask t s d
  let rows:=pcxReadRow t s d
  have eqPer : (fun i b'=>M i b' x) = per := funext fun i=>funext fun b'=>mask i b'
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro l r h
    change (∑ j : Fin d, ((pcxMassWord M x).testBit (d*pcxGridCode l r h+j.val)).toNat*2^j.val) = _
    rw [mass,eqPer]
    exact pack_decode u v w col (permit pin per) l r h
  · change decide (pcxIdx x < pcxOneCount M x) = _
    rw [idx,pick,eqPer]
    rfl
  · let ordN := fun k=>order ⟨k%t,Nat.mod_lt _ (NeZero.pos t)⟩
    let p := pcxPicked pcxIdx pcxOneCount M rows x
    have sz : p < 2^t := by
      unfold p pcxPicked
      split
      · exact pcxChosenSmall ..
      · positivity
    have choose : (∑ i : Fin t, (pcxOutSignal t s d (.inr (.inr i)) x).toNat*2^(t-1-i.val)) = p :=
      word_encode sz
    have co (P) : pcxOneCount P x = ∑ ω, if pcxFits P x (fun i=>ω (pin i)) then rawCell u v w col ω a y z else 0 := pick P
    have spec := pcxOutputSpec M pcxIdx rows pcxOneCount (fun ω=>rawCell u v w col ω a y z)
      (fun ω i=>ω (pin i)) ordN x rot co
    dsimp only at spec
    have eqOrd (i:Fin t) : ordN i.val = order i := congrArg order (Fin.ext (Nat.mod_eq_of_lt i.isLt))
    have fits (ω) : pcxFits M x (fun j=>ω (pin j)) ↔ permit pin per ω := by
      change (∀ j,M j (ω (pin j)) x=true) ↔ (∀ j,per j (ω (pin j))=true)
      constructor
      · intro h j; exact (mask j _).symm.trans (h j)
      · intro h j; exact (mask j _).trans (h j)
    simp_rw [eqOrd,fits] at spec
    rw [choose]
    change (if index.val<countCell u v w col (permit pin per) a y z then _ else _)
    have total : pcxOneCount M x = countCell u v w col (permit pin per) a y z := by rw [pick,eqPer]
    rw [idx,total] at spec
    exact spec

end Pcx446Arithmetic

namespace BoundaryPhysical
open BoundaryPacked BoundaryFixed BoundaryPin BoundarySwitch Pcx446Arithmetic
variable {n m t b : ℕ} (u v : Fin m → Fin n) (w : Fin m → Bool → Fin (2^b)) (col : Fin m → Fin 3)
    (pin : Fin t → Fin n) (per : Fin t → Bool → Bool) (order : Equiv.Perm (Fin t))
    (a y z : Fin (m+1)) (index : Fin (2^(n+m*b+1)))

def grid (P : Finset (Fin t)) (l r h : Fin (m+1)) (j : Fin (n+m*b+1)) :=
  (countCell u v w col (pinned pin P) l r h).testBit j.val

def data : pcxDomain (pcxFrame t (m+1) (n+m*b+1)) → Bool :=
  pcxFrameValues (grid u v w col pin ∅) (fun i j => grid u v w col pin (if i=j then ∅ else {i,j}))
    per (fun i j => decide (order i=j)) (fun j => decide (a=j)) (fun j => decide (y=j))
    (fun j => decide (z=j)) (fun j => index.val.testBit j.val)

def input := pcxInputAt (data u v w col pin per order a y z index)

theorem vec : List.ofFn (input u v w col pin per order a y z index) = [false,true] ++ pcxGridList (grid u v w col pin ∅) ++
    (List.ofFn (fun i : Fin t => (List.ofFn (fun j : Fin t => pcxGridList (grid u v w col pin (if i=j then ∅ else {i,j})))).flatten)).flatten ++
    (List.ofFn (fun i : Fin t => [per i false,per i true])).flatten ++
    (List.ofFn (fun i : Fin t => List.ofFn (fun j : Fin t => decide (order i=j)))).flatten ++
    List.ofFn (fun j => decide (a=j)) ++ List.ofFn (fun j => decide (y=j)) ++
    List.ofFn (fun j => decide (z=j)) ++ List.ofFn (fun j : Fin (n+m*b+1) => index.val.testBit j.val) := by
  rw [input,pcxInputAt_vec]; apply pcxFrameList
theorem constants : (input u v w col pin per order a y z index) ⟨0,by unfold PcxWidth; omega⟩ = false ∧
    (input u v w col pin per order a y z index) ⟨1,by unfold PcxWidth; omega⟩ = true := by
  have he := vec u v w col pin per order a y z index
  have h0 := congrArg (fun l => l.getD 0 false) he
  have h1 := congrArg (fun l => l.getD 1 false) he
  simp only [List.cons_append] at h0 h1
  have hn0 : 0 < (PcxWidth t (m+1) (n+m*b+1)) := by unfold PcxWidth; omega
  have hn1 : 1 < (PcxWidth t (m+1) (n+m*b+1)) := by unfold PcxWidth; omega
  simpa only [dite_eq_left hn0,dite_eq_left hn1,List.getD_eq_getElem?_getD,List.getElem?_ofFn,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some] using And.intro h0 h1

theorem mask_read (i : Fin t) (c : Bool) : pcxInputData t (m+1) (n+m*b+1) (pcxMaskKey i c) (input u v w col pin per order a y z index) = per i c := by
  rw [input,pcxInputAt_read]
  cases c <;> rfl
theorem order_read (i j : Fin t) : pcxInputData t (m+1) (n+m*b+1) (pcxOrderKey i j) (input u v w col pin per order a y z index) = decide (order i=j) := by
  rw [input,pcxInputAt_read];rfl
def target (a y z : Fin (m+1)) (i : Fin 3) := if i=0 then a else if i=1 then y else z
theorem hot_read (i : Fin 3) (j : Fin (m+1)) :
    pcxInputData t (m+1) (n+m*b+1) (pcxHitKey i j) (input u v w col pin per order a y z index) = decide (target a y z i = j) := by
  rw [input,pcxInputAt_read]
  fin_cases i <;> rfl
theorem idx_read : pcxIdx (input u v w col pin per order a y z index) = index.val := pcxIdx_read ..

theorem z_read : pcxRawZ (input u v w col pin per order a y z index) = BoundaryPacked.packed u v w col (pinned pin ∅) := by
  unfold pcxRawZ BoundaryPacked.packed
  congr 1; funext q; rw [input,pcxInputAt_read]; rfl
theorem pair_read (i j : Fin t) :
    pcxRawPair i j (input u v w col pin per order a y z index) = BoundaryPacked.packed u v w col (pinned pin (if i=j then ∅ else {i,j})) := by
  unfold pcxRawPair BoundaryPacked.packed
  congr 1; funext q; rw [input,pcxInputAt_read]; rfl

variable [NeZero t] (M : PcxMask (PcxWidth t (m+1) (n+m*b+1)) t)

theorem mass (recM : (PlanarRec pin (spin u v (fun e c => weighted u w col e (bitEquiv.symm c))))) : pcxMassWord (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M (input u v w col pin per order a y z index) = BoundaryPacked.packed u v w col (permit pin (fun i c => M i c (input u v w col pin per order a y z index))) := by
  have hz := z_read u v w col pin per order a y z index
  have hp := pair_read u v w col pin per order a y z index
  unfold pcxMassWord
  apply BoundaryExtract.extract_legal t ((slotList t).length/2) (pcxRawZ (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) (input u v w col pin per order a y z index)) _ _ _
  · have he := slotLen t
    have ht : 0<t := NeZero.pos t
    by_cases hd : Even t
    · have hk : 2 ≤ t := by obtain ⟨j,hj⟩ := hd; omega
      simp [hd] at he; omega
    · simp [hd] at he; omega
  · rw [hz]; apply packed_le_Z
  · exact pcxObsDetBound (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M (input u v w col pin per order a y z index)
  · change _ = _ * (pcxObs (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M (input u v w col pin per order a y z index)).det
    unfold pcxObs
    rw [hz]
    simp_rw [hp]
    exact packedFixedSquare u v w col pin (fun i c => M i c (input u v w col pin per order a y z index)) recM

theorem select (recM : (PlanarRec pin (spin u v (fun e c => weighted u w col e (bitEquiv.symm c))))) :
    pcxSelectWord (d:=(n+m*b+1)) (fun i j => pcxInputData t (m+1) (n+m*b+1) (pcxHitKey i j)) (pcxMassWord (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M) (input u v w col pin per order a y z index) =
      countCell u v w col (permit pin (fun i c => M i c (input u v w col pin per order a y z index))) a y z := by
  let C := countCell u v w col (permit pin (fun i c => M i c (input u v w col pin per order a y z index))) a y z
  let H := fun i j => pcxInputData t (m+1) (n+m*b+1) (pcxHitKey i j)
  have hC : C < 2^(n+m*b+1) := countCell_lt u v w col (permit pin (fun i c => M i c (input u v w col pin per order a y z index))) a y z
  let sel := pcxSelectWord (d:=(n+m*b+1)) H (pcxMassWord (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M) (input u v w col pin per order a y z index)
  have hs : sel < 2^(n+m*b+1) := pcxBitsRead_lt (n+m*b+1) _
  change sel = C
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j<(n+m*b+1)
  · let i : Fin (n+m*b+1) := ⟨j,h⟩
    have he := pcxBitsRead_test (n+m*b+1) (fun h => pcxSelBit (N:=(PcxWidth t (m+1) (n+m*b+1))) (s:=(m+1)) H
      (fun q x => (pcxMassWord (t:=t) (s:=(m+1)) (d:=(n+m*b+1)) M x).testBit ((n+m*b+1)*pcxGridCode q.1 q.2.1 q.2.2+h.val)) (input u v w col pin per order a y z index)) i
    change sel.testBit j = _ at he
    rw [he,pcxSelBit_spec H _ (input u v w col pin per order a y z index) (target a y z) (hot_read u v w col pin per order a y z index),
      mass u v w col pin per order a y z index M recM]
    exact pack_read u v w col (permit pin (fun i c => M i c (input u v w col pin per order a y z index))) a y z i
  · rw [Nat.testBit_eq_false_of_lt (hs.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_eq_false_of_lt (hC.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
end BoundaryPhysical

open Pcx446Arithmetic BoundaryPacked BoundaryPin BoundarySwitch

theorem pcxCompleteLease : (∃ C : ℕ, 0 < C ∧ ∀ (n m t b : ℕ), 0 < t →
  let I := Fin n
  let T := Fin t
  let E := Fin m
  let J := Fin (m+1)
  let d := n+m*b+1
  let N := 2+(1+t*t)*(m+1)^3*d+2*t+t*t+3*(m+1)+d
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit)
    (count : J → J → J → Fin d → Fin (N+g.size))
    (flag : Fin (N+g.size)) (word : T → Fin (N+g.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N g ∧ g.size ≤ (n+m+t+b+2)^C ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
       (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (u v : E → I) (pin : T ↪ I),
    let G := Option I
    let edge := fun x y : I => ∃ e : Fin m, (u e = x ∧ v e = y) ∨ (u e = y ∧ v e = x)
    let adj := fun x y : I => decide (edge x y)
    let rim := fun i : I => decide (∃ j, pin j = i)
    let inc := fun (x y : G) => x.elim (y.elim false rim) (fun i => y.elim (rim i) (adj i))
    (∀ e, u e ≠ v e) → (∀ i j : I, Relation.ReflTransGen edge i j) →
    (∃ (l : ℕ) (src dst : Fin l → G) (rot rev : Equiv.Perm (Fin l)) (spoke : T → Fin l),
      Function.Injective (fun d => (src d,dst d)) ∧
      (∀ x y : G, inc x y = true ↔ ∃ d, src d = x ∧ dst d = y) ∧
      (∀ d, src (rev d) = dst d ∧ dst (rev d) = src d ∧ src (rot d) = src d) ∧
      (∀ d e, src d = src e → ∃ j : ℕ, (rot^j) d = e) ∧
      (∀ i, src (spoke i) = none ∧ dst (spoke i) = some (pin i) ∧
        ∀ j : T, j.val = (i.val+1) % t → rot (spoke i) = spoke j) ∧
      let walk := fun d : Fin l => rot (rev d)
      let faces := (Finset.univ : Finset (Fin l)).image (fun d =>
        (Finset.range l).image (fun j => walk^[j] d))
      2*(n+1)+2*faces.card = 4+l) →
    ∀ (w : E → Bool → Fin (2^b)) (color : E → Fin 3)
        (per : T → Bool → Bool) (order : Equiv.Perm T) (a y z : J) (index : Fin (2^d)),
      let raw := fun (x : I → Bool) (l r h : J) =>
        let diff := fun e : E => xor (x (u e)) (x (v e))
        let tally := fun j : Fin 3 => (Finset.univ.filter (fun e : E => color e = j ∧ diff e = true)).card
        if tally 0 = l.val ∧ tally 1 = r.val ∧ tally 2 = h.val then ∏ e, (w e (diff e)).val else 0
      let obs := fun (P : Finset T) (l r h : J) => ∑ x : I → Bool,
        if ∀ i ∈ P, x (pin i) = false then raw x l r h else 0
      let bits := fun (v' : ℕ) => List.ofFn (fun i : Fin d => v'.testBit i.val)
      let block := fun (P : Finset T) => (List.ofFn (fun l : J => (List.ofFn (fun r : J =>
        (List.ofFn (fun h : J => bits (obs P l r h))).flatten)).flatten)).flatten
      let pairs := (List.ofFn (fun i : T => (List.ofFn (fun j : T => block (if i = j then ∅ else {i,j}))).flatten)).flatten
      let mask := (List.ofFn (fun i : T => [per i false,per i true])).flatten
      let perm := (List.ofFn (fun i : T => List.ofFn (fun j : T => decide (order i = j)))).flatten
      let hot := fun (i : J) => List.ofFn (fun j : J => decide (i = j))
      let ws := g.wires ([false,true] ++ block ∅ ++ pairs ++ mask ++ perm ++ hot a ++ hot y ++ hot z ++ bits index.val)
      let mass := fun (l r h : J) (x : I → Bool) =>
        if ∀ i : T, per i (x (pin i)) = true then raw x l r h else 0
      let code := fun (x : I → Bool) => ∑ i : T, (x (pin (order i))).toNat * 2^(t-1-i.val)
      let picked := ∑ i : T, (ws.getD (word i).val false).toNat * 2^(t-1-i.val)
      (∀ l r h, (∑ j : Fin d, (ws.getD (count l r h j).val false).toNat*2^j.val) =
        ∑ x : I → Bool, mass l r h x) ∧
      ws.getD flag.val false = decide (index.val < ∑ x : I → Bool, mass a y z x) ∧
      if index.val < ∑ x : I → Bool, mass a y z x then
        (∑ x : I → Bool, if code x < picked then mass a y z x else 0) ≤ index.val ∧
        index.val < (∑ x : I → Bool, if code x ≤ picked then mass a y z x else 0)
      else picked = 0) := by
  classical
  refine ⟨128,by decide,?_⟩
  intro n m t b ht
  letI : NeZero t := ⟨Nat.ne_of_gt ht⟩
  dsimp only
  let s := m+1
  let d := n+m*b+1
  obtain ⟨g,addr,hback,hsize,hshape,hwires⟩ := pcxAllCircuit n m t b
  refine ⟨g,(fun l r h j=>addr (.inl (l,r,h,j))),addr (.inr (.inl ())), (fun i=>addr (.inr (.inr i))),
    hback,hsize,hshape,?_⟩
  intro u v pin noLoop connected embedding w col per order a y z index
  obtain ⟨l,src,dst,rot,rev,sp,uniq,support,revrot,cycle,spoke,euler⟩ := embedding
  have recM : PlanarRec pin (spin u v (fun e c=>weighted u w col e (bitEquiv.symm c))) := by
    intro h inst sel
    exact planarSpinRecurrence u v pin noLoop connected src dst rot rev sp uniq support revrot cycle spoke euler sel
      (fun e c=>weighted u w col e (bitEquiv.symm c))
  let x := BoundaryPhysical.input u v w col pin per order a y z index
  have constants := BoundaryPhysical.constants u v w col pin per order a y z index
  have reads := hwires x constants.1 constants.2
  have vec := BoundaryPhysical.vec u v w col pin per order a y z index
  change List.ofFn x = _ at vec
  rw [vec] at reads
  have decoded := pcxMeaning u v w col pin per order a y z index x
    (BoundaryPhysical.mask_read u v w col pin per order a y z index)
    (fun k j=>BoundaryPhysical.order_read u v w col pin per order a y z index _ j)
    (BoundaryPhysical.idx_read u v w col pin per order a y z index)
    (fun M=>BoundaryPhysical.mass u v w col pin per order a y z index M recM)
    (fun M=>BoundaryPhysical.select u v w col pin per order a y z index M recM)
  let wireRead := fun key => (g.wires ([false,true] ++ pcxGridList (BoundaryPhysical.grid u v w col pin ∅) ++
    (List.ofFn (fun i : Fin t=> (List.ofFn (fun j : Fin t=>pcxGridList
      (BoundaryPhysical.grid u v w col pin (if i=j then ∅ else {i,j})))).flatten)).flatten ++
    (List.ofFn (fun i : Fin t=>[per i false,per i true])).flatten ++
    (List.ofFn (fun i : Fin t=>List.ofFn (fun j : Fin t=>decide (order i=j)))).flatten ++
    List.ofFn (fun j=>decide (a=j)) ++ List.ofFn (fun j=>decide (y=j)) ++
    List.ofFn (fun j=>decide (z=j)) ++ List.ofFn (fun j : Fin d=>index.val.testBit j.val))).getD (addr key).val false
  have e : wireRead = fun key=>pcxOutSignal t s d key x := funext reads
  let mass := fun (l r h : Fin s) (ω : Fin n→Bool)=>if permit pin per ω then rawCell u v w col ω l r h else 0
  let code := fun (ω : Fin n→Bool)=>∑ i : Fin t, (ω (pin (order i))).toNat*2^(t-1-i.val)
  let picked := fun (read : PcxOut t s d→Bool)=>∑ i : Fin t,(read (.inr (.inr i))).toNat*2^(t-1-i.val)
  change (∀ l r h, (∑ j : Fin d,(wireRead (.inl (l,r,h,j))).toNat * 2^j.val) = ∑ ω,mass l r h ω) ∧
    wireRead (.inr (.inl ())) = decide (index.val < ∑ ω,mass a y z ω) ∧
    if index.val < ∑ ω,mass a y z ω then
      (∑ ω,if code ω < picked wireRead then mass a y z ω else 0) ≤ index.val ∧
      index.val < (∑ ω,if code ω ≤ picked wireRead then mass a y z ω else 0) else picked wireRead=0
  rw [e]
  exact decoded

end PEqualNP.Outside.L_pcx_446

theorem PEqualNP.Outside.L_pcx_446 : (∃ C : ℕ, 0 < C ∧ ∀ (n m t b : ℕ), 0 < t →
  let I := Fin n
  let T := Fin t
  let E := Fin m
  let J := Fin (m+1)
  let d := n+m*b+1
  let N := 2+(1+t*t)*(m+1)^3*d+2*t+t*t+3*(m+1)+d
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit)
    (count : J → J → J → Fin d → Fin (N+g.size))
    (flag : Fin (N+g.size)) (word : T → Fin (N+g.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N g ∧ g.size ≤ (n+m+t+b+2)^C ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
       (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (u v : E → I) (pin : T ↪ I),
    let G := Option I
    let edge := fun x y : I => ∃ e : Fin m, (u e = x ∧ v e = y) ∨ (u e = y ∧ v e = x)
    let adj := fun x y : I => decide (edge x y)
    let rim := fun i : I => decide (∃ j, pin j = i)
    let inc := fun (x y : G) => x.elim (y.elim false rim) (fun i => y.elim (rim i) (adj i))
    (∀ e, u e ≠ v e) → (∀ i j : I, Relation.ReflTransGen edge i j) →
    (∃ (l : ℕ) (src dst : Fin l → G) (rot rev : Equiv.Perm (Fin l)) (spoke : T → Fin l),
      Function.Injective (fun d => (src d,dst d)) ∧
      (∀ x y : G, inc x y = true ↔ ∃ d, src d = x ∧ dst d = y) ∧
      (∀ d, src (rev d) = dst d ∧ dst (rev d) = src d ∧ src (rot d) = src d) ∧
      (∀ d e, src d = src e → ∃ j : ℕ, (rot^j) d = e) ∧
      (∀ i, src (spoke i) = none ∧ dst (spoke i) = some (pin i) ∧
        ∀ j : T, j.val = (i.val+1) % t → rot (spoke i) = spoke j) ∧
      let walk := fun d : Fin l => rot (rev d)
      let faces := (Finset.univ : Finset (Fin l)).image (fun d =>
        (Finset.range l).image (fun j => walk^[j] d))
      2*(n+1)+2*faces.card = 4+l) →
    ∀ (w : E → Bool → Fin (2^b)) (color : E → Fin 3)
        (per : T → Bool → Bool) (order : Equiv.Perm T) (a y z : J) (index : Fin (2^d)),
      let raw := fun (x : I → Bool) (l r h : J) =>
        let diff := fun e : E => xor (x (u e)) (x (v e))
        let tally := fun j : Fin 3 => (Finset.univ.filter (fun e : E => color e = j ∧ diff e = true)).card
        if tally 0 = l.val ∧ tally 1 = r.val ∧ tally 2 = h.val then ∏ e, (w e (diff e)).val else 0
      let obs := fun (P : Finset T) (l r h : J) => ∑ x : I → Bool,
        if ∀ i ∈ P, x (pin i) = false then raw x l r h else 0
      let bits := fun (v' : ℕ) => List.ofFn (fun i : Fin d => v'.testBit i.val)
      let block := fun (P : Finset T) => (List.ofFn (fun l : J => (List.ofFn (fun r : J =>
        (List.ofFn (fun h : J => bits (obs P l r h))).flatten)).flatten)).flatten
      let pairs := (List.ofFn (fun i : T => (List.ofFn (fun j : T => block (if i = j then ∅ else {i,j}))).flatten)).flatten
      let mask := (List.ofFn (fun i : T => [per i false,per i true])).flatten
      let perm := (List.ofFn (fun i : T => List.ofFn (fun j : T => decide (order i = j)))).flatten
      let hot := fun (i : J) => List.ofFn (fun j : J => decide (i = j))
      let ws := g.wires ([false,true] ++ block ∅ ++ pairs ++ mask ++ perm ++ hot a ++ hot y ++ hot z ++ bits index.val)
      let mass := fun (l r h : J) (x : I → Bool) =>
        if ∀ i : T, per i (x (pin i)) = true then raw x l r h else 0
      let code := fun (x : I → Bool) => ∑ i : T, (x (pin (order i))).toNat * 2^(t-1-i.val)
      let picked := ∑ i : T, (ws.getD (word i).val false).toNat * 2^(t-1-i.val)
      (∀ l r h, (∑ j : Fin d, (ws.getD (count l r h j).val false).toNat*2^j.val) =
        ∑ x : I → Bool, mass l r h x) ∧
      ws.getD flag.val false = decide (index.val < ∑ x : I → Bool, mass a y z x) ∧
      if index.val < ∑ x : I → Bool, mass a y z x then
        (∑ x : I → Bool, if code x < picked then mass a y z x else 0) ≤ index.val ∧
        index.val < (∑ x : I → Bool, if code x ≤ picked then mass a y z x else 0)
      else picked = 0) := by
  exact PEqualNP.Outside.L_pcx_446.pcxCompleteLease
