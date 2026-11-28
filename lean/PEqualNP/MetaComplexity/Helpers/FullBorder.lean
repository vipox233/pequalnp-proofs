import PEqualNP.MetaComplexity.L7872
import PEqualNP.MetaComplexity.Helpers.OneNotRelabel

/-! Exact budget for adding full rows and columns under the one-hot input promise. -/

namespace PEqualNP.BorderLower

open Represents (RepSizeAtMost)

private theorem charge {n m : Nat} (A : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (miss : ∀ j ∈ K, ∃ i ∈ R, A i j = false)
    (cross : ∀ i ∉ R, ∃ j ∈ K, A i j = true) :
    (R.filter (fun i => ∃ j ∈ K, A i j = true)).card + (n - R.card) ≤
      (Finset.univ.filter (fun i => ∃ j, A i j = true ∧ ∃ i', A i' j = false)).card := by
  classical
  let core := R.filter (fun i => ∃ j ∈ K, A i j = true)
  let extra := Finset.univ \ R
  have dis : Disjoint core extra := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mp hi).1
  have sub : core ∪ extra ⊆
      Finset.univ.filter (fun i => ∃ j, A i j = true ∧ ∃ i', A i' j = false) := by
    intro i hi
    have hit : ∃ j ∈ K, A i j = true := by
      rcases Finset.mem_union.mp hi with inside | outside
      · exact (Finset.mem_filter.mp inside).2
      · exact cross i (Finset.mem_sdiff.mp outside).2
    obtain ⟨j, hj, one⟩ := hit
    obtain ⟨i', _, zero⟩ := miss j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, one, i', zero⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at count
  simpa [core, extra, Finset.card_sdiff_of_subset (Finset.subset_univ R)] using count

/-- Every discarded row and column that meets the opposite retained bank
pays one gate when the retained rectangle has an edge and no full line. -/
theorem restrictWithSavings {n m s : Nat} (A : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (missR : ∀ i ∈ R, ∃ j ∈ K, A i j = false)
    (missK : ∀ j ∈ K, ∃ i ∈ R, A i j = false)
    (hit : ∃ i ∈ R, ∃ j ∈ K, A i j = true)
    (crossR : ∀ i ∉ R, ∃ j ∈ K, A i j = true)
    (crossK : ∀ j ∉ K, ∃ i ∈ R, A i j = true)
    (source : RepSizeAtMost A s) :
    ∃ t, RepSizeAtMost (fun i j => A i j && decide (i ∈ R) && decide (j ∈ K)) t ∧
      t + (n - R.card) + (m - K.card) ≤ s := by
  obtain ⟨t, smaller, cost⟩ := MetaComplexity.L7872 n m s A R K missR missK hit source
  have rows := charge A R K missK crossR
  have cols := charge (fun j i => A i j) K R missR crossK
  exact ⟨t, smaller, by omega⟩

end PEqualNP.BorderLower

namespace PEqualNP.BorderUpper

open CircuitLowerBounds MetaComplexity.Helpers MetaComplexity.OneNot
open Represents (RepSizeAtMost oneEach)

private def liftWire (a b n m w : Nat) : Nat :=
  if w < a then w else if w < a+b then n+(w-a) else n+m+(w-(a+b))

private theorem rawBit {n m : Nat} (i : Fin n) (j : Fin m) (w : Nat) :
    (oneEach i j).getD w false = decide (w=i.val ∨ w=n+j.val) := by
  rw [MetaComplexity.RepReads.oneEach_eq, MetaComplexity.RepReads.inp_getD]
  simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
  have hi := i.isLt
  have hj := j.isLt
  omega

private theorem simulate {a b n m : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (gs : List Gate) (i : Fin a) (j : Fin b) (w : Nat) :
    (wiresFrom (gs.map (on1_relabel (liftWire a b n m)))
      (oneEach (Fin.castLE ha i) (Fin.castLE hb j))).getD (liftWire a b n m w) false =
      (wiresFrom gs (oneEach i j)).getD w false := by
  apply on1_relabel_sim
  · intro k hk
    simp only [oneEach, List.length_append, List.length_ofFn] at hk
    rw [rawBit,rawBit]
    simp only [Fin.val_castLE, liftWire, if_pos hk, decide_eq_decide]
    have hi := i.isLt
    have hj := j.isLt
    split <;> omega
  · intro k hk
    left
    simp only [oneEach, List.length_append, List.length_ofFn] at hk ⊢
    simp only [liftWire, if_pos hk]
    split <;> omega
  · intro k _
    simp only [oneEach, List.length_append, List.length_ofFn, liftWire]
    split_ifs <;> omega
  · intro k hk
    simp only [oneEach, List.length_append, List.length_ofFn] at hk ⊢
    simp only [liftWire]
    split_ifs <;> omega

private def orGates (next out : Nat) : List Nat → List Gate
  | [] => []
  | w :: ws => ⟨.or,[out,w]⟩ :: orGates (next+1) next ws

private def orOutput (next out : Nat) : List Nat → Nat
  | [] => out
  | _ :: ws => orOutput (next+1) next ws

private theorem orLength (next out : Nat) (ws : List Nat) :
    (orGates next out ws).length = ws.length := by
  induction ws generalizing next out with
  | nil => rfl
  | cons _ _ ih => simp [orGates, ih]

private theorem orPositive (next out : Nat) (ws : List Nat) :
    ∀ g ∈ orGates next out ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing next out with
  | nil => simp [orGates]
  | cons w ws ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | keep
    · simp
    · exact ih (next+1) next g keep

private theorem orEval (xs : List Bool) (next out : Nat) (ws : List Nat)
    (len : xs.length = next) (early : ∀ k ∈ ws, k < next) :
    (wiresFrom (orGates next out ws) xs).getD (orOutput next out ws) false =
      (xs.getD out false || ws.any (fun k => xs.getD k false)) := by
  induction ws generalizing xs next out with
  | nil => simp [orGates, orOutput, wiresFrom]
  | cons w ws ih =>
    let bit := xs.getD out false || xs.getD w false
    have keep (k) (hk : k ∈ ws) : k < xs.length := by
      rw [len]
      exact early k (List.mem_cons_of_mem _ hk)
    have same : ws.any (fun k => (xs ++ [bit]).getD k false) =
        ws.any (fun k => xs.getD k false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨k,hk,found⟩ <;>
        exact ⟨k,hk,by simpa only [List.getD_append _ _ _ _ (keep k hk)] using found⟩
    have newBit : (xs ++ [bit]).getD next false = bit := len ▸ getD_snoc_eq xs bit false
    simp only [orGates, orOutput, on1_wiresFrom_cons]
    have gate : GateOp.or.eval ([out,w].map fun k => xs.getD k false) = bit := by
      simp [GateOp.eval,bit]
    rw [gate]
    rw [ih (xs ++ [bit]) (next+1) next (by simp [len])
      (by intro k hk; have := keep k hk; omega), newBit, same, List.any_cons]
    exact Bool.or_assoc _ _ _

private def added (a b n m : Nat) : List Nat :=
  ((List.range (n-a)).map (a+·)) ++ ((List.range (m-b)).map (n+b+·))

private theorem addedMem (a b n m k : Nat) :
    k ∈ added a b n m ↔ (a ≤ k ∧ k < n) ∨ (n+b ≤ k ∧ k < n+m) := by
  simp only [added, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; exact ⟨k-a,by omega,by omega⟩
    · right; exact ⟨k-(n+b),by omega,by omega⟩

/-- Extend any representation by one binary OR per new full row or column. -/
theorem extendFull {a b n m t : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool)
    (border : ∀ i j, a ≤ i.val ∨ b ≤ j.val → A i j = true)
    (base : RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) t) :
    RepSizeAtMost A (t+(n-a)+(m-b)) := by
  obtain ⟨C,pos,size,rep⟩ := base
  let r := liftWire a b n m
  let gs := C.gates.map (on1_relabel r)
  let next := n+m+gs.length
  let ws := added a b n m
  let D : Circuit := ⟨gs ++ orGates next (r C.output) ws, orOutput next (r C.output) ws⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old | new
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp old
      simpa [on1_relabel] using pos f hf
    · exact orPositive _ _ _ g new
  · change (gs ++ orGates next (r C.output) ws).length ≤ _
    simp only [List.length_append, orLength, ws, added, List.length_map, List.length_range, gs]
    change C.gates.length ≤ t at size
    omega
  · intro i j
    let X := oneEach i j
    let V := wiresFrom gs X
    have hlen : X.length = n+m := by simp [X,oneEach]
    have len : V.length = next := by simp only [V,length_wiresFrom,hlen,next]
    have raw (k) (hk : k ∈ ws) : k < n+m := by
      have := (addedMem a b n m k).mp hk
      omega
    have agree (k) (hk : k ∈ ws) : V.getD k false = decide (k=i.val ∨ k=n+j.val) := by
      change (wiresFrom gs X).getD k false = _
      rw [getD_wiresFrom _ _ _ (by rw [hlen]; exact raw k hk)]
      exact rawBit i j k
    have flag : ws.any (fun k => V.getD k false) = decide (a ≤ i.val ∨ b ≤ j.val) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨k,hk,one⟩
        rw [agree k hk, decide_eq_true_eq] at one
        have := (addedMem a b n m k).mp hk
        have hi := i.isLt
        omega
      · rintro (hi | hj)
        · have hk : i.val ∈ ws := (addedMem _ _ _ _ _).mpr (Or.inl ⟨hi,i.isLt⟩)
          exact ⟨_,hk,(agree _ hk).trans (by simp)⟩
        · have hk : n+j.val ∈ ws := (addedMem _ _ _ _ _).mpr (Or.inr ⟨by omega,by have := j.isLt; omega⟩)
          exact ⟨_,hk,(agree _ hk).trans (by simp)⟩
    change (wiresFrom (gs ++ orGates next (r C.output) ws) X).getD _ false = _
    rw [wiresFrom_append, orEval V next (r C.output) ws len
      (by intro k hk; have := raw k hk; dsimp [next]; omega), flag]
    by_cases cross : a ≤ i.val ∨ b ≤ j.val
    · simp [cross,border i j cross]
    · let u : Fin a := ⟨i.val,by omega⟩
      let v : Fin b := ⟨j.val,by omega⟩
      have eqn := simulate ha hb C.gates u v C.output
      have baseVal := rep u v
      change (wiresFrom _ _).getD _ false = A (Fin.castLE ha u) (Fin.castLE hb v) at baseVal
      have same := eqn.trans baseVal
      rw [show Fin.castLE ha u = i from Fin.ext rfl,
        show Fin.castLE hb v = j from Fin.ext rfl] at same
      simpa only [decide_eq_false cross, Bool.or_false] using same

end PEqualNP.BorderUpper

namespace PEqualNP.FullBorder

open Represents (RepSizeAtMost)

def table {a b : Nat} (p q : Nat) (A : Fin a → Fin b → Bool)
    (i : Fin (a+p)) (j : Fin (b+q)) : Bool :=
  if hi : i.val < a then
    if hj : j.val < b then A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else true
  else true

private def bankPrefix {a n : Nat} (h : a ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem memPrefix {a n : Nat} (h : a ≤ n) (i : Fin n) :
    i ∈ bankPrefix h ↔ i.val < a := by
  simp only [bankPrefix, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,rfl⟩

private theorem embed {a n : Nat} (h : a ≤ n) (i : Fin a) : Fin.castLE h i ∈ bankPrefix h :=
  (memPrefix h _).mpr i.isLt

private theorem cell {a b p q : Nat} (A : Fin a → Fin b → Bool) (i : Fin a) (j : Fin b) :
    table p q A (Fin.castLE (Nat.le_add_right a p) i) (Fin.castLE (Nat.le_add_right b q) j) =
      A i j := by simp [table,i.isLt,j.isLt]

theorem exactFromRestriction
    (shrink : ∀ {n m a b s : Nat} (ha : a ≤ n) (hb : b ≤ m)
      (A : Fin n → Fin m → Bool), RepSizeAtMost A s →
      RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) s)
    (a b p q s : Nat) (A : Fin a → Fin b → Bool)
    (missRow : ∀ i, ∃ j, A i j = false) (missCol : ∀ j, ∃ i, A i j = false)
    (hit : ∃ i j, A i j = true) :
    RepSizeAtMost (table p q A) s ↔ ∃ t, RepSizeAtMost A t ∧ t+p+q ≤ s := by
  let ha := Nat.le_add_right a p
  let hb := Nat.le_add_right b q
  let R := bankPrefix ha
  let K := bankPrefix hb
  have inside (i : Fin (a+p)) (j : Fin (b+q)) (hi : i.val < a) (hj : j.val < b) :
      table p q A i j = A ⟨i.val,hi⟩ ⟨j.val,hj⟩ := by simp [table,hi,hj]
  have full (i : Fin (a+p)) (j : Fin (b+q)) (h : a ≤ i.val ∨ b ≤ j.val) :
      table p q A i j = true := by
    rcases h with left | right
    · simp [table,show ¬ i.val < a by omega]
    · simp [table,show ¬ j.val < b by omega]
  obtain ⟨u,v,one⟩ := hit
  constructor
  · intro source
    have noRow (i) (hi : i ∈ R) : ∃ j ∈ K, table p q A i j = false := by
      have small := (memPrefix ha i).mp hi
      obtain ⟨j,z⟩ := missRow ⟨i.val,small⟩
      exact ⟨Fin.castLE hb j,embed hb j,(inside _ _ small j.isLt).trans z⟩
    have noCol (j) (hj : j ∈ K) : ∃ i ∈ R, table p q A i j = false := by
      have small := (memPrefix hb j).mp hj
      obtain ⟨i,z⟩ := missCol ⟨j.val,small⟩
      exact ⟨Fin.castLE ha i,embed ha i,(inside _ _ i.isLt small).trans z⟩
    obtain ⟨t,core,cost⟩ := BorderLower.restrictWithSavings (table p q A) R K noRow noCol
      ⟨Fin.castLE ha u,embed ha u,Fin.castLE hb v,embed hb v,(cell A u v).trans one⟩
      (fun i hi => ⟨Fin.castLE hb v,embed hb v,full _ _ (.inl (Nat.le_of_not_gt (hi ∘ (memPrefix ha i).mpr)))⟩)
      (fun j hj => ⟨Fin.castLE ha u,embed ha u,full _ _ (.inr (Nat.le_of_not_gt (hj ∘ (memPrefix hb j).mpr)))⟩)
      source
    have narrow := shrink ha hb _ core
    have cardR : R.card = a := by simp [R,bankPrefix]
    have cardK : K.card = b := by simp [K,bankPrefix]
    refine ⟨t,?_,by omega⟩
    simpa only [R,K,embed,decide_true,Bool.and_true,cell] using narrow
  · rintro ⟨t,base,budget⟩
    have wide := BorderUpper.extendFull ha hb (table p q A) full (t := t) (by simpa only [cell] using base)
    obtain ⟨C,mono,cost,rep⟩ := wide
    exact ⟨C,mono,by omega,rep⟩

end PEqualNP.FullBorder

-- Prefix restriction from the first-party CLB-1 desk proof in PrefixRestriction.lean.
namespace PEqualNP.PrefixRestriction

open CircuitLowerBounds
open Represents (oneEach Represents RepSizeAtMost)
open MetaComplexity (Monotone2)

/-- Raw inputs outside the retained banks go to a wire beyond the whole new circuit.
Gate indices keep their offset from the end of the raw inputs. -/
private def wire (n m a b dead w : Nat) : Nat :=
  if w < n then (if w < a then w else dead)
  else if w < n + m then (if w - n < b then a + (w - n) else dead)
  else a + b + (w - (n + m))

private def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

private def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

private theorem lengthInput {a b : Nat} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

private theorem readInput {a b : Nat} (u : Fin a) (v : Fin b) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < a
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, show i ≠ a + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
    by_cases hj : i - a < b
    · simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, show i ≠ u.val by omega,
        show i - a = v.val ↔ i = a + v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [show i ≠ u.val by omega, show i ≠ a + v.val by omega]

private theorem readPrefix {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (tail : List Bool) (ht : tail.length ≤ N) (w : Nat) :
    (oneEach u v ++ tail).getD (wire n m a b (a + b + N) w) false =
    (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail).getD w false := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases raw : w < n + m
  · conv_rhs => rw [List.getD_append _ _ _ _ (by rwa [lengthInput]), readInput]
    simp only [Fin.val_castLE]
    by_cases left : w < n
    · by_cases kept : w < a
      · simp only [wire, if_pos left, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show w ≠ a + v.val by omega, show w ≠ n + v.val by omega]
      · simp only [wire, if_pos left, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
    · by_cases kept : w - n < b
      · simp only [wire, if_neg left, if_pos raw, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show a + (w - n) ≠ u.val by omega, show w ≠ u.val by omega,
          show a + (w - n) = a + v.val ↔ w = n + v.val by omega] <;> omega
      · simp only [wire, if_neg left, if_pos raw, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
  · simp only [wire, if_neg (show ¬ w < n by omega), if_neg raw]
    rw [List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega),
      List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega), lengthInput, lengthInput]
    congr 1
    omega

private theorem simulation {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (gs : List Gate) (tail : List Bool) (h : tail.length + gs.length ≤ N) :
    let r := wire n m a b (a + b + N)
    ∃ out : List Bool, out.length ≤ N ∧
      (gs.map (rename r)).foldl step (oneEach u v ++ tail) = oneEach u v ++ out ∧
      gs.foldl step (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail) =
        oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, by simpa using h, rfl, rfl⟩
  | cons g rest ih =>
    let old := oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail
    let bit := g.op.eval (g.inputs.map fun k => old.getD k false)
    have ht : tail.length ≤ N := by omega
    have same : (rename (wire n m a b (a + b + N)) g).op.eval
        ((rename (wire n m a b (a + b + N)) g).inputs.map fun k =>
          (oneEach u v ++ tail).getD k false) = bit := by
      simp only [rename, List.map_map, Function.comp_def, readPrefix ha hb u v tail ht, bit, old]
    have bound : (tail ++ [bit]).length + rest.length ≤ N := by
      simp only [List.length_cons] at h
      simp; omega
    simpa only [List.map_cons, List.foldl_cons, step, same, List.append_assoc, bit, old]
      using ih (tail ++ [bit]) bound

/-- Keeping an initial segment of each bank costs no gates, including for forward or missing reads. -/
theorem restrictPrefix {n m a b s : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) s := by
  obtain ⟨C, mono, size, rep⟩ := h
  let r := wire n m a b (a + b + C.size)
  let D : Circuit := ⟨C.gates.map (rename r), r C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using mono f hf
  · simpa [D, Circuit.size] using size
  · intro u v
    obtain ⟨out, len, hnew, hold⟩ :=
      simulation (N := C.size) ha hb u v C.gates [] (by simp [Circuit.size])
    simp only [List.append_nil] at hnew hold
    have val := rep (Fin.castLE ha u) (Fin.castLE hb v)
    change (C.gates.foldl step _).getD C.output false = _ at val
    change ((C.gates.map (rename r)).foldl step _).getD (r C.output) false = _
    rw [hnew, readPrefix ha hb u v out len, ← hold, val]

end PEqualNP.PrefixRestriction

theorem PEqualNP.FullBorder.exact (a b p q s : Nat) (A : Fin a → Fin b → Bool)
    (mr : ∀ i, ∃ j, A i j = false) (mc : ∀ j, ∃ i, A i j = false) (edge : ∃ i j, A i j = true) :
    Represents.RepSizeAtMost (table p q A) s ↔ ∃ t, Represents.RepSizeAtMost A t ∧ t+p+q ≤ s :=
  exactFromRestriction (fun ha hb A h => PrefixRestriction.restrictPrefix ha hb A h) a b p q s A mr mc edge
