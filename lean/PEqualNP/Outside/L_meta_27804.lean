import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L7872
import PEqualNP.Outside.L_meta_6158
namespace PEqualNP.Outside.L_meta_27804
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents


def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def relabel (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) := rfl

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : Nat) (h : j ≠ L.length) :
    (L++[S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L++[S]).getD L.length d = S := by simp

theorem relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (run (gs.map (relabel r)) v).getD (r i) false
      = (run gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (relabel r g).op.eval
          ((relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, run_cons, run_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega


theorem relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (run (gs.map (relabel r)) v).getD (r i) false
      = (run gs w).getD i false := by
  apply relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]


lemma relabel_monotone (r : Nat→Nat) (C : Circuit) (h : Monotone2 C) :
    Monotone2 ⟨C.gates.map (relabel r),r C.output⟩ := by
  rintro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  obtain ⟨ho,hl⟩ := h a ha
  exact ⟨ho,by simpa [relabel] using hl⟩


def rowInput (n : Nat) {m : Nat} (r : Nat) (j : Fin m) : List Bool :=
  List.ofFn (fun i : Fin n=>decide (i.val=r)) ++
    List.ofFn (fun i : Fin m=>decide (i=j))

lemma rowInput_length (n r : Nat) {m : Nat} (j : Fin m) :
    (rowInput n r j).length=n+m := by simp [rowInput]

lemma getD_ofFn {n : Nat} (x : Fin n→Bool) (i : Nat) (hi : i<n) :
    (List.ofFn x).getD i false=x ⟨i,hi⟩ := by
  simp [List.getD_eq_getElem?_getD,hi]

lemma rowInput_getD (n r i : Nat) {m : Nat} (j : Fin m) :
    (rowInput n r j).getD i false=
      if i<n then decide (i=r) else decide (i=n+j.val) := by
  by_cases hi : i<n
  · rw [if_pos hi]
    unfold rowInput
    rw [List.getD_append _ _ _ _ (by simpa using hi),getD_ofFn _ _ hi]
  · rw [if_neg hi]
    by_cases him : i<n+m
    · unfold rowInput
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp only [List.length_ofFn]
      rw [getD_ofFn _ _ (by omega)]
      simp only [Fin.ext_iff]
      apply decide_eq_decide.mpr
      omega
    · rw [List.getD_eq_default _ _ (by rw [rowInput_length];omega)]
      simp [show i≠n+j.val by have := j.isLt;omega]

lemma rowInput_oneEach {n m : Nat} (i : Fin n) (j : Fin m) :
    rowInput n i.val j=oneEach i j := by
  unfold rowInput oneEach
  congr 1

def mergeMap (n m : Nat) (u : Fin n) (i : Nat) : Nat :=
  if i<n then (if i=u.val then (n+1)+m else i)
  else if i<n+m then i+1 else i+2

def mergeGate {n : Nat} (u : Fin n) : Gate := ⟨GateOp.or,[u.val,n]⟩

def mergeCircuit {n : Nat} (m : Nat) (u : Fin n) (C : Circuit) : Circuit :=
  ⟨mergeGate u::C.gates.map (relabel (mergeMap n m u)),mergeMap n m u C.output⟩

def mergeStart {n m : Nat} (u : Fin n) (r : Nat) (j : Fin m) : List Bool :=
  rowInput (n+1) r j++[decide (u.val=r)||decide (n=r)]

lemma mergeStart_length {n m : Nat} (u : Fin n) (r : Nat) (j : Fin m) :
    (mergeStart u r j).length=n+m+2 := by simp [mergeStart,rowInput_length];omega

lemma mergeStart_lookup {n m : Nat} (u : Fin n) (r : Nat) (hr : r<n+1) (j : Fin m)
    (i : Nat) (hi : i<n+m) :
    (mergeStart u r j).getD (mergeMap n m u i) false=
      (rowInput n (if r<n then r else u.val) j).getD i false := by
  by_cases hin : i<n
  · by_cases hiu : i=u.val
    · subst i
      have start : (mergeStart u r j).getD ((n+1)+m) false=
          (decide (u.val=r)||decide (n=r)) := by
        simpa only [mergeStart,rowInput_length] using
          (getD_snoc_eq (rowInput (n+1) r j) (decide (u.val=r)||decide (n=r)) false)
      rw [mergeMap,if_pos u.isLt,if_pos rfl,start,rowInput_getD,if_pos u.isLt]
      by_cases hrn : r<n
      · simp [hrn,show n≠r by omega]
      · have re : r=n := by omega
        simp [hrn,re]
    · rw [mergeMap,if_pos hin,if_neg hiu]
      unfold mergeStart
      rw [List.getD_append _ _ _ _ (by rw [rowInput_length];omega),
        rowInput_getD,rowInput_getD,if_pos (by omega),if_pos hin]
      by_cases hrn : r<n
      · simp [hrn]
      · simp [hrn,show i≠r by omega,hiu]
  · rw [mergeMap,if_neg hin,if_pos hi]
    unfold mergeStart
    rw [List.getD_append _ _ _ _ (by rw [rowInput_length];omega),
      rowInput_getD,rowInput_getD,if_neg (by omega),if_neg hin]
    apply decide_eq_decide.mpr
    omega

lemma merge_eval {n m : Nat} (C : Circuit) (u : Fin n) (r : Nat) (hr : r<n+1) (j : Fin m) :
    (mergeCircuit m u C).eval (rowInput (n+1) r j)=
      C.eval (rowInput n (if r<n then r else u.val) j) := by
  change (run (mergeGate u::C.gates.map (relabel (mergeMap n m u)))
      (rowInput (n+1) r j)).getD (mergeMap n m u C.output) false=
    (run C.gates (rowInput n (if r<n then r else u.val) j)).getD C.output false
  rw [run_cons]
  have gateval : (mergeGate u).op.eval
      ((mergeGate u).inputs.map (fun i=>(rowInput (n+1) r j).getD i false))=
        (decide (u.val=r)||decide (n=r)) := by
    simp only [mergeGate,GateOp.eval,List.map_cons,List.map_nil,
      List.any_cons,List.any_nil,id_eq,Bool.or_false]
    rw [rowInput_getD,rowInput_getD]
    simp [show u.val<n+1 by omega]
  rw [gateval]
  change (run (C.gates.map (relabel (mergeMap n m u))) (mergeStart u r j)).getD
      (mergeMap n m u C.output) false=_
  apply relabel_sim
  · intro i hi
    apply mergeStart_lookup u r hr j i
    simpa only [rowInput_length] using hi
  · intro i hi
    simp only [rowInput_length,mergeStart_length] at hi ⊢
    left
    by_cases hin : i<n
    · by_cases hiu : i=u.val <;> simp [mergeMap,hin,hiu] <;> omega
    · simp [mergeMap,hin,hi];omega
  · intro k hk
    simp only [rowInput_length,mergeStart_length]
    rw [mergeMap,if_neg (by omega),if_neg (by omega)]
    omega
  · intro i hi
    simp only [rowInput_length,mergeStart_length] at hi ⊢
    rw [mergeMap,if_neg (by omega),if_neg (by omega)]
    omega

lemma merge_monotone {n m : Nat} (C : Circuit) (u : Fin n) (mono : Monotone2 C) :
    Monotone2 (mergeCircuit m u C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|hg
  · simp [mergeGate]
  · exact relabel_monotone (mergeMap n m u) C mono g hg


theorem one_copy_upper {n m b : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (rep : RepSizeAtMost A b) :
    RepSizeAtMost
      (fun i : Fin (n+1)=>fun j=>if h : i.val<n then A ⟨i.val,h⟩ j else A u j) (b+1) := by
  obtain ⟨C,mono,size,repC⟩ := rep
  refine ⟨mergeCircuit m u C,merge_monotone C u mono,?_,?_⟩
  · simpa [mergeCircuit,Circuit.size] using Nat.add_le_add_right size 1
  · intro i j
    rw [←rowInput_oneEach,merge_eval C u i.val i.isLt j]
    change C.eval (rowInput n (if i.val<n then i.val else u.val) j)=
      (if h : i.val<n then A ⟨i.val,h⟩ j else A u j)
    by_cases hin : i.val<n
    · rw [if_pos hin,dif_pos hin,rowInput_oneEach (⟨i.val,hin⟩ : Fin n) j]
      exact repC _ _
    · rw [if_neg hin,dif_neg hin,rowInput_oneEach u j]
      exact repC _ _


private def graph (n m : Nat) (u : Fin n) (v : Fin m) :=
  decide (u.val ≠ v.val ∨ 3 ≤ u.val)

private theorem table (i j : Nat) :
    (64478 : Nat).testBit (4 * min i 3 + min j 3) = decide (i ≠ j ∨ 3 ≤ i) := by
  have h : ∀ a b : Fin 4, (64478 : Nat).testBit (4*a.val+b.val) =
      decide (a.val ≠ b.val ∨ 3 ≤ a.val) := by decide
  rw [h ⟨min i 3, by omega⟩ ⟨min j 3, by omega⟩]
  apply decide_eq_decide.mpr
  dsimp
  omega

private theorem olen {n m : Nat} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n+m := by simp [oneEach]

private theorem lookup {n m : Nat} (u : Fin n) (v : Fin m) (i : Nat) :
    (oneEach u v).getD i false = decide (i=u.val ∨ i=n+v.val) := by
  rw [←rowInput_oneEach, rowInput_getD]
  split <;> apply decide_eq_decide.mpr <;> have := u.isLt <;> omega

private theorem transport {n m a b s : Nat} {A : Fin n → Fin m → Bool}
    (p : Fin a → Fin n) (q : Fin b → Fin m) (h : RepSizeAtMost A s)
    (r : ℕ → ℕ)
    (inp : ∀ u v i, i < n+m → ((r i=(u : Fin a).val ∨ r i=a+(v : Fin b).val) ↔
       (i=(p u).val ∨ i=n+(q v).val)))
    (bound : ∀ i < n+m, r i < a+b ∨ a+b+s ≤ r i)
    (idx : ∀ i, n+m ≤ i → r i = a+b+(i-(n+m))) :
    RepSizeAtMost (fun u v => A (p u) (q v)) s := by
  obtain ⟨C,mono,sz,rep⟩ := h
  refine ⟨⟨C.gates.map (relabel r),r C.output⟩,relabel_monotone r C mono,by simpa [Circuit.size] using sz,?_⟩
  intro u v
  dsimp only
  rw [←rep (p u) (q v)]
  apply relabel_sim
  · intro i hi
    rw [lookup,lookup]
    exact decide_eq_decide.mpr (inp u v i (by simpa only [olen] using hi))
  · simp only [olen]
    intro i hi
    exact (bound i hi).imp_right (fun h => by change C.gates.length ≤ s at sz; omega)
  · simp only [olen]
    intro k _
    rw [idx _ (by omega)]
    omega
  · simp only [olen]
    intro i hi
    rw [idx _ (by omega)]
    omega

private theorem swap {n m s : Nat} {A : Fin n → Fin m → Bool} (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun v u => A u v) s := by
  obtain ⟨C,mono,sz,rep⟩ := h
  let r := fun i : Nat => if i<n then m+i else if i<n+m then i-n else i
  refine ⟨⟨C.gates.map (relabel r),r C.output⟩,relabel_monotone r C mono,by simpa [Circuit.size] using sz,?_⟩
  intro v u
  dsimp only
  rw [←rep u v]
  apply relabel_sim
  · intro i hi
    rw [lookup,lookup]
    simp only [olen] at hi
    apply decide_eq_decide.mpr
    have := u.isLt
    have := v.isLt
    dsimp [r]
    split_ifs <;> omega
  · simp only [olen]
    intro i hi
    left
    dsimp [r]
    split_ifs <;> omega
  · simp only [olen]
    intro k _
    dsimp [r]
    split_ifs <;> omega
  · simp only [olen]
    intro i hi
    dsimp [r]
    split_ifs <;> omega

private def c4 : Circuit :=
  ⟨[⟨.or,[0,4]⟩, ⟨.or,[1,5]⟩, ⟨.or,[2,6]⟩, ⟨.or,[8,9]⟩, ⟨.and,[8,9]⟩,
     ⟨.or,[10,12]⟩, ⟨.and,[11,13]⟩, ⟨.or,[14,3]⟩, ⟨.or,[15,7]⟩],16⟩

private theorem base4 : RepSizeAtMost (graph 4 4) 9 := by
  refine ⟨c4, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [c4,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

private theorem symmGraph {n m : Nat} (i : Fin n) (j : Fin m) :
    graph n m i j = graph m n j i := by
  unfold graph
  apply decide_eq_decide.mpr
  omega

private theorem swapGraph {n m s : Nat} (h : RepSizeAtMost (graph n m) s) :
    RepSizeAtMost (graph m n) s := by
  convert swap h using 1
  funext i j
  exact symmGraph i j

private theorem grow {m b : Nat} (h : RepSizeAtMost (graph 4 m) b) (n : Nat) (hn : 4 ≤ n) :
    RepSizeAtMost (graph n m) (b+(n-4)) := by
  induction n,hn using Nat.le_induction with
  | base => simpa using h
  | succ n hn ih =>
    have H := one_copy_upper (graph n m) (⟨3,by omega⟩ : Fin n) ih
    convert H using 1
    · funext i j
      split
      · rfl
      · unfold graph
        simp
        omega
    · omega

private theorem upper (n m : Nat) (hn : 4 ≤ n) (hm : 4 ≤ m) :
    RepSizeAtMost (graph n m) (n+m+1) := by
  have h := grow (swapGraph (grow base4 m hm)) n hn
  convert h using 1 <;> omega

private def first3 (n : Nat) (h : 3 ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem in3 {n : Nat} (h : 3 ≤ n) (u : Fin n) : u ∈ first3 n h ↔ u.val < 3 := by
  simp only [first3, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v,rfl⟩
    exact v.isLt
  · intro hv
    exact ⟨⟨u.val,hv⟩,Fin.ext rfl⟩

private theorem touched {n m : Nat} (hn : 4 ≤ n) (hm : 4 ≤ m) (u : Fin n) :
    ∃ v : Fin m, graph n m u v = true ∧ ∃ x : Fin n, graph n m x v = false := by
  by_cases e : u.val=0
  · exact ⟨⟨1,by omega⟩, by simp [graph,e], ⟨1,by omega⟩, by simp [graph]⟩
  · exact ⟨⟨0,by omega⟩, by simp [graph,e], ⟨0,by omega⟩, by simp [graph]⟩

private theorem lower (n m : Nat) (hn : 4 ≤ n) (hm : 4 ≤ m) :
    ¬ RepSizeAtMost (graph n m) (n+m) := by
  intro rep
  let R := first3 n (by omega)
  let K := first3 m (by omega)
  have rmem (u : Fin n) : u ∈ R ↔ u.val < 3 := in3 _ _
  have kmem (v : Fin m) : v ∈ K ↔ v.val < 3 := in3 _ _
  obtain ⟨t, ht, cost⟩ := PEqualNP.MetaComplexity.L7872 n m (n+m) (graph n m) R K
    (by intro u hu; have h := (rmem u).1 hu
        exact ⟨⟨u.val,by omega⟩,(kmem _).2 h,by simp [graph]; omega⟩)
    (by intro v hv; have h := (kmem v).1 hv
        exact ⟨⟨v.val,by omega⟩,(rmem _).2 h,by simp [graph]; omega⟩)
    ⟨⟨0,by omega⟩,(rmem _).2 (by change 0 < 3; decide),⟨1,by omega⟩,(kmem _).2 (by change 1 < 3; decide),by simp [graph]⟩ rep
  have leftAll : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, graph n m a b = true ∧
      ∃ a' : Fin n, graph n m a' b = false)) = Finset.univ :=
    Finset.filter_true_of_mem (fun a _ => touched hn hm a)
  have rightAll : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, graph n m a b = true ∧
      ∃ b' : Fin m, graph n m a b' = false)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro b _
    obtain ⟨a,ha,b',hb⟩ := touched hm hn b
    exact ⟨a,(symmGraph a b).trans ha,b',(symmGraph a b').trans hb⟩
  rw [leftAll,rightAll] at cost
  simp only [Finset.card_univ,Fintype.card_fin] at cost
  have rc : R.card = 3 := by simp [R,first3]
  have kc : K.card = 3 := by simp [K,first3]
  have rle := Finset.card_filter_le R (fun a => ∃ b ∈ K, graph n m a b = true)
  have kle := Finset.card_filter_le K (fun b => ∃ a ∈ R, graph n m a b = true)
  have lim : t ≤ 6 := by omega
  let p : Fin 4 → Fin n := Fin.castLE hn
  let q : Fin 4 → Fin m := Fin.castLE hm
  let r := fun i : Nat =>
    if i < n then (if i < 4 then i else 8+t)
    else if i < n+m then (if i-n < 4 then 4+(i-n) else 8+t)
    else 8+(i-(n+m))
  have small := transport p q ht r (by
    intro u v i hi
    have := u.isLt
    have := v.isLt
    dsimp [r,p,q]
    split_ifs <;> omega) (by
    intro i hi
    dsimp [r]
    split_ifs <;> omega) (by
    intro i hi
    dsimp [r]
    split_ifs <;> omega)
  apply PEqualNP.Outside.L_meta_6158.2
  obtain ⟨D,mono,sz,eval⟩ := small
  refine ⟨D,mono,sz.trans lim,?_⟩
  intro u v
  rw [eval u v]
  simp only [p,q,rmem,kmem,graph,Fin.coe_castLE]
  exact (by decide : ∀ u v : Fin 4,
    (decide (u.val ≠ v.val ∨ 3 ≤ u.val) && decide (u.val < 3) && decide (v.val < 3)) =
      (854 : Nat).testBit (4*u.val+v.val)) u v

end PEqualNP.Outside.L_meta_27804

theorem PEqualNP.Outside.L_meta_27804 : (∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  dsimp only
  simp_rw [PEqualNP.Outside.L_meta_27804.table]
  exact ⟨PEqualNP.Outside.L_meta_27804.upper n m hn hm, PEqualNP.Outside.L_meta_27804.lower n m hn hm⟩
