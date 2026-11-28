import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1429.FixedBook

open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket (notCount)

noncomputable def conj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d && g d
noncomputable def disj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d || g d
noncomputable def inv {α : Type*} (f : α → Bool) : α → Bool := fun d => !(f d)

def WVal {α : Type*} (x : α → List Bool) (gs : List Gate) (p : Nat) : α → Bool :=
  fun d => ((Circuit.mk gs 0).wires (x d)).getD p false

noncomputable def Built {α : Type*} (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool)) : Prop :=
  (∀ d, (x d).length = N) ∧ ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack N ⟨gs,0⟩ ∧
    gs.length - notCount ⟨gs,0⟩ ≤ p ∧ notCount ⟨gs,0⟩ ≤ b ∧
    ∀ f ∈ S, ∃ i < N+gs.length, WVal x gs i = f

private theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

private theorem old {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) {i} (hi : i < N+gs.length) :
    WVal x (gs++[g]) i = WVal x gs i := by
  funext d
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD i false = _
  exact List.getD_append _ _ _ _ (by omega)

private theorem fresh {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) (d : α) :
    WVal x (gs++[g]) (N+gs.length) d = g.op.eval (g.inputs.map fun i => WVal x gs i d) := by
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD (N+gs.length) false = _
  rw [← len, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private theorem extendBack {N : Nat} (gs : List Gate) (g : Gate) (h : ReadsBack N ⟨gs,0⟩)
    (ok : ∀ i ∈ g.inputs, i < N+gs.length) : ReadsBack N ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

section Compiler
variable {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}

theorem Built.start (hlen : ∀ d, (x d).length = N) :
    Built x N 0 0 {f | ∃ i < N, f = fun d => (x d).getD i false} := by
  refine ⟨hlen, [], by simp [FanInTwo], by simp [ReadsBack], by simp, by simp [notCount], ?_⟩
  rintro f ⟨i, hi, rfl⟩
  exact ⟨i, by simpa using hi, rfl⟩

theorem Built.relax {P B : Nat} {T : Set (α → Bool)} (H : Built x N p b S)
    (hp : p ≤ P) (hb : b ≤ B) (hst : T ⊆ S) : Built x N P B T := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  exact ⟨hlen, gs, fan, back, pc.trans hp, nc.trans hb, fun u hu => sig u (hst hu)⟩

private theorem Built.push (H : Built x N p b S) (op : GateOp) (arity : Nat)
    (allowed : op = .and ∨ op = .or ∨ op = .not) (ha : arity ≤ 2)
    (fs : List (α → Bool)) (hfs : fs.length = arity) (hf : ∀ f ∈ fs, f ∈ S) :
    Built x N (p + if op = .not then 0 else 1) (b + if op = .not then 1 else 0)
      (insert (fun d => op.eval (fs.map fun f => f d)) S) := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  have choose (f : α → Bool) (h : f ∈ fs) := sig f (hf f h)
  let is := fs.attach.map (fun f => (choose f.val f.property).choose)
  let g : Gate := ⟨op, is⟩
  have hcount : notCount ⟨gs++[g],0⟩ = notCount ⟨gs,0⟩ + (if op = .not then 1 else 0) := by
    by_cases h : op = .not <;> simp [notCount, List.filter_append, g, h]
  have hnc : notCount ⟨gs,0⟩ ≤ gs.length := List.length_filter_le _ _
  refine ⟨hlen, gs++[g], ?_, ?_, ?_, by rw [hcount]; exact Nat.add_le_add_right nc _, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact fan j hj
    · obtain rfl := List.mem_singleton.mp hj
      exact ⟨allowed, by simpa [g, is, hfs] using ha⟩
  · apply extendBack _ _ back
    intro i hi
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hi
    exact (choose f.val f.property).choose_spec.1
  · rw [hcount]
    simp only [List.length_append, List.length_singleton]
    split <;> omega
  · intro f hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · refine ⟨N+gs.length, by simp, ?_⟩
      funext d
      rw [fresh _ hlen]
      congr 1
      change is.map (fun i => WVal x gs i d) = _
      simp only [is, List.map_map]
      calc
        _ = fs.attach.map (fun f => f.val d) := by
          apply List.map_congr_left
          intro f _
          exact congrFun (choose f.val f.property).choose_spec.2 d
        _ = _ := List.attach_map_val (f := fun f : α → Bool => f d)
    · obtain ⟨i, hi, he⟩ := sig f hm
      exact ⟨i, by simp; omega, (old x hlen gs g hi).trans he⟩

theorem Built.andGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (conj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d && g d) S)
  simpa [GateOp.eval] using H.push .and 2 (Or.inl rfl) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.orGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (disj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d || g d) S)
  simpa [GateOp.eval] using H.push .or 2 (Or.inr (Or.inl rfl)) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.notGate {f : α → Bool} (H : Built x N p b S) (hf : f ∈ S) :
    Built x N p (b+1) (insert (inv f) S) := by
  change Built x N p (b+1) (insert (fun d => !f d) S)
  simpa [GateOp.eval] using H.push .not 1 (Or.inr (Or.inr rfl)) (by decide) [f] rfl (by simpa)

theorem boolOfIff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  cases hP : decide P <;> cases hQ : decide Q <;> simp_all

noncomputable def Grow (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool))
    (c : Nat) (f : α → Bool) := ∃ T, Built x N (p+c) b T ∧ S ⊆ T ∧ f ∈ T

theorem batch {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (c : Nat) (H : Built x N p b S)
    (make : ∀ {P T}, Built x N P b T → S ⊆ T → ∀ a ∈ s, Grow x N P b T c (F a)) :
    ∃ T, Built x N (p+s.card*c) b T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fr ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fr,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

end Compiler

noncomputable def bits {r : Nat} (X : Finset (Fin r)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun j : Fin r => decide (j ∈ X))

noncomputable def labelBit {m : Nat} (i j : Fin m) : Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  decide (i=j)

def Valid (n : Nat) (D : Circuit) : Prop :=
  FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size

noncomputable def Possible {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) : Prop :=
  ∃ (D : Circuit) (out : Fin m → Nat), Valid r D ∧
    (∀ j, out j < r+2+D.size) ∧ notCount D ≤ b ∧
    ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = labelBit i j

def Adj {m l : Nat} (w : Fin l → Fin m) : Prop :=
  ∀ i j : Fin l, i.val + 1 = j.val → w i ≠ w j

def WordTrace {r m l : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r))
    (w : Fin l → Fin m) : Prop :=
  ∃ Y : Fin l → Finset (Fin r), Monotone Y ∧ (∀ i, Y i ⊆ T) ∧ ∀ i, lab (Y i) (w i)

def Trace {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (l : Nat) : Prop :=
  ∃ w : Fin l → Fin m, Adj w ∧ WordTrace lab T w

def Bucket {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (k : Nat)
    (j : Fin m) : Prop :=
  ∃ w : Fin (k+1) → Fin m, Adj w ∧ WordTrace lab T w ∧ w (Fin.last k) = j

private theorem bits_getD {r : Nat} (Y : Finset (Fin r)) (j : Fin r) :
    (bits Y).getD j.val false = decide (j ∈ Y) := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  exact Bool.eq_iff_iff.mpr (by simp)

private theorem trace_mono {r m l : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T U : Finset (Fin r)} (sub : T ⊆ U) : Trace lab T l → Trace lab U l := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  exact ⟨w,adj,Y,mono,fun i => (top i).trans sub,ok⟩

private theorem trace_prefix {r m i j : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T : Finset (Fin r)} (le : i ≤ j) : Trace lab T j → Trace lab T i := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  refine ⟨w ∘ Fin.castLE le, fun a b h => adj _ _ h,
    Y ∘ Fin.castLE le, fun a b h => mono h, fun a => top _, fun a => ok _⟩

private theorem trace_one {r m : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i : Fin m} (h : lab X i) : Trace lab X 1 := by
  refine ⟨fun _ => i, fun j k adj => ?_, fun _ => X, fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ => h⟩
  have hj := j.isLt
  have hk := k.isLt
  omega

private theorem trace_extend {r m k : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (diff : j ≠ i) (hi : lab X i) (h : Bucket lab X k j) :
    Trace lab X (k+2) := by
  obtain ⟨w,adj,⟨Y,mono,top,ok⟩,last⟩ := h
  let w' : Fin (k+2) → Fin m := Fin.lastCases i w
  let Y' : Fin (k+2) → Finset (Fin r) := Fin.lastCases X Y
  refine ⟨w', ?_, Y', ?_, ?_, ?_⟩
  · intro a b step
    revert step
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro step
      have hb := b.isLt
      change k+1+1 = b.val at step
      omega
    · refine Fin.lastCases ?_ (fun b step => ?_) b
      · intro step
        have ha : a = Fin.last k := Fin.ext (by change a.val+1 = k+1 at step; exact Nat.add_right_cancel step)
        simpa [w', ha, last] using diff
      · simpa [w'] using adj a b step
  · intro a b le
    revert le
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro le
      have hb : b = Fin.last (k+1) := le_antisymm (Fin.le_last b) le
      simp [hb]
    · refine Fin.lastCases ?_ (fun b le => ?_) b
      · intro _; simpa [Y'] using top a
      · simpa [Y'] using mono (show a ≤ b from le)
  · intro a; exact Fin.lastCases (by simp [Y']) (fun a => by simpa [Y'] using top a) a
  · intro a; exact Fin.lastCases (by simpa [Y',w'] using hi) (fun a => by simpa [Y',w'] using ok a) a

noncomputable def rank {r m : Nat} (K : Nat) (lab : Finset (Fin r) → Fin m → Prop)
    (X : Finset (Fin r)) : Nat := ((Finset.range K).filter (fun k => Trace lab X (k+1))).sup id

private theorem rank_lt {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hk : 0 < K) : rank K lab X < K := by
  have h : rank K lab X ≤ K-1 := Finset.sup_le (fun i hi => by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    dsimp; omega)
  omega

private theorem le_rank_iff {r m K i : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hi : i < K) : i ≤ rank K lab X ↔ i = 0 ∨ Trace lab X (i+1) := by
  by_cases iz : i = 0
  · simp [iz]
  constructor
  · intro h
    right
    by_contra no
    have small : rank K lab X ≤ i-1 := Finset.sup_le (fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).2
      change j ≤ i-1
      by_contra hn
      exact no (trace_prefix (by omega) hj'))
    omega
  · rintro (h | h)
    · exact (iz h).elim
    · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,h⟩)

private theorem correct_bucket {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (hK : 0 < K) (hi : lab X i)
    (good : ¬ Trace lab Finset.univ (K+1)) : Bucket lab X (rank K lab X) j ↔ i = j := by
  let u := rank K lab X
  have ltK : u < K := rank_lt hK
  constructor
  · intro buck
    by_contra diff
    have ext := trace_extend (Ne.symm diff) hi buck
    change Trace lab X (u+2) at ext
    by_cases top : u+1 = K
    · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
    · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
      change u+1 ≤ u at lev
      omega
  · rintro rfl
    have existsTrace : Trace lab X (u+1) := by
      rcases (le_rank_iff (lab := lab) (X := X) ltK).mp (le_refl u) with z | yes
      · simpa [z] using trace_one hi
      · exact yes
    obtain ⟨w,adj,tr⟩ := existsTrace
    let j := w (Fin.last u)
    have buck : Bucket lab X u j := ⟨w,adj,tr,rfl⟩
    have eq : i = j := by
      by_contra diff
      have ext := trace_extend (Ne.symm diff) hi buck
      change Trace lab X (u+2) at ext
      by_cases top : u+1 = K
      · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
      · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
        change u+1 ≤ u at lev
        omega
    exact eq ▸ buck

namespace RankDecoder

private theorem one {α : Type*} {x : α → List Bool} {N p nb b : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hR : ∀ d, R d < 1) :
    ∃ T, Built x N (p + 16 * (1 + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < 1 → (fun d => decide (R d = i)) ∈ T := by
  refine ⟨S, H.relax (by omega) (by omega) (fun _ h => h), fun _ h => h, ?_⟩
  intro i hi
  have eq : (fun d => decide (R d = i)) = (fun _ => true) := by
    funext d
    have : R d = i := by have := hR d; omega
    simp [this]
  rw [eq]
  exact ht

theorem decode {α : Type*} {x : α → List Bool} {N p nb b K : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (hR : ∀ d, R d < K) (hK : 0 < K) (hpow : K ≤ 2^b)
    (threshold : ∀ i : Nat, i < K → (fun d => decide (i ≤ R d)) ∈ S) :
    ∃ T, Built x N (p + 16 * (K + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < K → (fun d => decide (R d = i)) ∈ T := by
  classical
  induction b generalizing p nb K S R with
  | zero =>
    have : K = 1 := by simp at hpow; omega
    subst K
    exact one H ht hR
  | succ b ih =>
    by_cases small : K = 1
    · subst K
      exact one H ht hR
    let h := (K + 1) / 2
    have hh : 0 < h := by dsimp [h]; omega
    have hlt : h < K := by dsimp [h]; omega
    have hsplit : K ≤ 2 * h := by dsimp [h]; omega
    have hhpow : h ≤ 2^b := by rw [pow_succ] at hpow; dsimp [h]; omega
    let U : Nat → α → Bool := fun i d => decide (i ≤ R d)
    let Q : α → Nat := fun d => if R d < h then R d else R d - h
    have qbound (d : α) : Q d < h := by
      have hd := hR d
      dsimp [Q]
      split <;> omega
    have uget (i : Nat) : U i ∈ S := by
      by_cases hi : i < K
      · exact threshold i hi
      · have eq : U i = (fun _ => false) := by
          funext d
          have hn : ¬ i ≤ R d := by have := hR d; omega
          simp [U, hn]
        rw [eq]
        exact hf
    let S₀ := insert (inv (U h)) S
    have H₀ : Built x N p (nb + 1) S₀ := H.notGate (uget h)
    have s₀ : S ⊆ S₀ := Set.subset_insert _ _
    have lower₀ : inv (U h) ∈ S₀ := Set.mem_insert _ _
    have foldStep {P : Nat} {V : Set (α → Bool)} (HV : Built x N P (nb + 1) V)
        (sV : S₀ ⊆ V) (i : Nat) (_ : i ∈ Finset.range h) :
        Grow x N P (nb + 1) V 2 (fun d => decide (i ≤ Q d)) := by
      let g := disj (inv (U h)) (U (h + i))
      have Hg : Built x N (P + 1) (nb + 1) (insert g V) :=
        HV.orGate (sV lower₀) (sV (s₀ (uget (h + i))))
      have vsub : V ⊆ insert g V := Set.subset_insert _ _
      have Hf := Hg.andGate (vsub (sV (s₀ (uget i)))) (Set.mem_insert g V)
      have f_eq : conj (U i) g = (fun d => decide (i ≤ Q d)) := by
        funext d
        by_cases hd : R d < h
        · have hn : ¬ h ≤ R d := by omega
          simp [conj, g, disj, inv, U, Q, hd, hn]
        · have hu : h ≤ R d := by omega
          have ieq : (h + i ≤ R d) ↔ (i ≤ R d - h) := by omega
          by_cases hi : i ≤ R d
          · simp [conj, g, disj, inv, U, Q, hd, hu, hi, ieq]
          · have hnot : ¬ i ≤ R d - h := by omega
            simp [conj, U, Q, hd, hi, hnot]
      refine ⟨_, Hf, vsub.trans (Set.subset_insert _ _), ?_⟩
      rw [← f_eq]
      exact Set.mem_insert _ _
    obtain ⟨A, HA, sA, getA⟩ := batch (Finset.range h)
      (fun i d => decide (i ≤ Q d)) 2 H₀ foldStep
    obtain ⟨C, HC, sC, getC⟩ := ih HA (sA (s₀ ht)) (sA (s₀ hf)) qbound hh hhpow
      (fun i hi => getA i (Finset.mem_range.mpr hi))
    have exactStep {P : Nat} {V : Set (α → Bool)}
        (HV : Built x N P (nb + 1 + b) V) (sV : C ⊆ V)
        (i : Nat) (hi : i ∈ Finset.range K) :
        Grow x N P (nb + 1 + b) V 1 (fun d => decide (R d = i)) := by
      have hiK := Finset.mem_range.mp hi
      let j := if i < h then i else i - h
      let flag := if i < h then inv (U h) else U h
      have hj : j < h := by dsimp [j]; split <;> omega
      have hflag : flag ∈ V := by
        by_cases il : i < h
        · simpa only [flag, ite_eq_left il] using sV (sC (sA lower₀))
        · simpa only [flag, ite_eq_right il] using sV (sC (sA (s₀ (uget h))))
      have HM := HV.andGate (sV (getC j hj)) hflag
      have eq : conj (fun d => decide (Q d = j)) flag = (fun d => decide (R d = i)) := by
        funext d
        by_cases il : i < h <;> by_cases dl : R d < h
        · have dn : ¬ h ≤ R d := by omega
          simp [conj, flag, inv, U, Q, j, il, dl, dn]
        · have du : h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, inv, U, il, du, ne]
        · have dn : ¬ h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, U, il, dn, ne]
        · have du : h ≤ R d := by omega
          have eq' : (R d - h = i - h) ↔ R d = i := by omega
          simp [conj, flag, U, Q, j, il, dl, du, eq']
      refine ⟨_, HM, Set.subset_insert _ _, ?_⟩
      rw [← eq]
      exact Set.mem_insert _ _
    obtain ⟨T, HT, sT, getT⟩ := batch (Finset.range K)
      (fun i d => decide (R d = i)) 1 HC exactStep
    refine ⟨T, HT.relax ?_ (by omega) (fun _ m => m),
      s₀.trans (sA.trans (sC.trans sT)), fun i hi => getT i (Finset.mem_range.mpr hi)⟩
    simp only [Finset.card_range, Nat.mul_one]
    have hs : (h + 1)^2 ≤ K^2 := by
      have le : h + 1 ≤ K := by omega
      simpa only [pow_two] using Nat.mul_le_mul le le
    nlinarith

end RankDecoder

private def InputSet {α : Type*} (x : α → List Bool) (N : Nat) : Set (α → Bool) :=
  {f | ∃ i < N, f = fun d => (x d).getD i false}

private theorem input_mem {α : Type*} {x : α → List Bool} {N i : Nat} {f : α → Bool}
    (hi : i < N) (eq : ∀ d, (x d).getD i false = f d) : f ∈ InputSet x N :=
  ⟨i,hi,(funext eq).symm⟩

private theorem suffix_const {α : Type*} {w : α → List Bool} {n : Nat} (L : ∀ d, (w d).length = n) :
    (fun _ => false) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) ∧
    (fun _ => true) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) := by
  constructor
  · apply input_mem (i := n) (by omega)
    intro d; simp [L]
  · apply input_mem (i := n+1) (by omega)
    intro d; simp [L]

private theorem some_taps {α : Type*} {x : α → List Bool} {n m p b : Nat} {S : Set (α → Bool)}
    {bad : α → Bool} {tap : Fin m → α → Bool} (H : Built x (n+2) p b S)
    (hb : bad ∈ S) (ht : ∀ j, tap j ∈ S) :
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧ (∀ j, out j < n+2+D.size) ∧
      notCount D ≤ b ∧ D.size - notCount D ≤ p ∧
      (∀ d, D.eval (x d) = bad d) ∧ ∀ d j, (D.wires (x d)).getD (out j) false = tap j d := by
  obtain ⟨_,gs,fan,back,pc,nc,sigs⟩ := H
  obtain ⟨o,ho,eo⟩ := sigs _ hb
  choose out hout eout using (fun j => sigs (tap j) (ht j))
  exact ⟨⟨gs,o⟩,out,⟨fan,back,ho⟩,hout,nc,pc,congrFun eo,fun d j => congrFun (eout j) d⟩

private theorem fixed_X {r : Nat} (j : Fin r) :
    (fun d : Finset (Fin r) => decide (j ∈ d)) ∈ InputSet (fun d => bits d ++ [false,true]) (r+2) := by
  apply input_mem (i := j.val) (by have := j.isLt; omega)
  intro d
  rw [List.getD_append _ _ _ _ (by simp [bits])]
  exact bits_getD _ _

theorem noTracePossible {r m b : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    (good : ¬ Trace lab Finset.univ (2^b+1)) : Possible b lab := by
  classical
  let K := 2^b
  let x : Finset (Fin r) → List Bool := fun X => bits X ++ [false,true]
  let S := InputSet x (r+2)
  let P := Finset (Fin r)
  have hK : 0<K := by dsimp [K]; positivity
  have H : Built x (r+2) 0 0 S := Built.start (fun d => by simp [x,bits])
  obtain ⟨hf,ht⟩ := suffix_const (n:=r) (w:=bits (r:=r)) (fun d => by simp [bits])
  let term (u : P) (X : P) : Bool := decide (u ⊆ X)
  obtain ⟨T,bt,st,ts⟩ := batch (Finset.univ : Finset P) term r H (by
    intro p U bu su u _
    obtain ⟨V,bv,uv,hit⟩ := allFold u (fun i X => decide (i∈X)) bu (su ht)
      (fun i _ => su (fixed_X i))
    refine ⟨V,bv.relax (Nat.add_le_add_left (by simpa [P] using u.card_le_univ) p) le_rfl Set.Subset.rfl,uv,?_⟩
    convert hit using 1
    funext X
    apply Bool.eq_iff_iff.mpr
    simp only [term,decide_eq_true_eq]
    exact ⟨fun h _ ha => h ha,fun h _ ha => h _ ha⟩)
  let dnf (u : Finset P) (X : P) : Bool := decide (∃ y∈u, y⊆X)
  obtain ⟨V,bv,tv,ds⟩ := batch (Finset.univ : Finset (Finset P)) dnf (Fintype.card P) bt (by
    intro p U bu tu u _
    obtain ⟨W,bw,uw,hit⟩ := anyFold u term bu (tu (st hf))
      (fun i _ => tu (ts i (Finset.mem_univ _)))
    refine ⟨W,bw.relax (Nat.add_le_add_left u.card_le_univ p) le_rfl Set.Subset.rfl,uw,?_⟩
    convert hit using 1
    funext X
    apply boolOfIff
    simp [term])
  have up (f : P → Prop) (mono : ∀ {A B : P}, A ⊆ B → f A → f B) :
      (fun X => decide (f X)) ∈ V := by
    let cols := Finset.univ.filter f
    have eq : (fun X => decide (f X)) = dnf cols := by
      funext X
      apply boolOfIff
      constructor
      · intro h; exact ⟨X,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,le_rfl⟩
      · rintro ⟨y,mem,sub⟩; exact mono sub (Finset.mem_filter.mp mem).2
    rw [eq]
    exact ds cols (Finset.mem_univ _)
  let R (X : P) := rank K lab X
  have threshold (i : Nat) (hi : i<K) : (fun d => decide (i ≤ R d)) ∈ V := by
    have monot : ∀ {A B : P}, A ⊆ B → i ≤ R A → i ≤ R B := by
      intro A B h hA
      apply (le_rank_iff hi).mpr
      exact ((le_rank_iff hi).mp hA).imp_right (trace_mono h)
    convert up (fun X => i ≤ R X) monot using 1
    funext X
    exact Bool.eq_iff_iff.mpr (by simp)
  have buck (k : Fin K) (j : Fin m) : (fun d => decide (Bucket lab d k.val j)) ∈ V := by
    apply up
    rintro A B sub ⟨w,ne,⟨Y,ord,le,tag⟩,last⟩
    exact ⟨w,ne,⟨Y,ord,fun i => (le i).trans sub,tag⟩,last⟩
  obtain ⟨W,bw,vw,ranks⟩ := RankDecoder.decode bv (tv (st ht)) (tv (st hf)) (R:=R)
    (fun _ => rank_lt hK) hK (le_rfl : K ≤ 2^b) threshold
  let signal (j : Fin m) (X : P) := decide (Bucket lab X (R X) j)
  obtain ⟨A,bA,wa,taps⟩ := batch (Finset.univ : Finset (Fin m)) signal (2*K) bw (by
    intro p Q h wq j _
    let c (k : Fin K) := conj (fun X => decide (R X=k.val)) (fun X => decide (Bucket lab X k.val j))
    obtain ⟨Q',hq,qq,terms⟩ := batch (Finset.univ : Finset (Fin K)) c 1 h (by
      intro p' A h' qa k _
      exact ⟨_,h'.andGate (qa (wq (ranks k.val k.isLt))) (qa (wq (vw (buck k j)))),
        Set.subset_insert _ _,Set.mem_insert _ _⟩)
    obtain ⟨A,ba,qa,out⟩ := anyFold (Finset.univ : Finset (Fin K)) c hq (qq (wq (vw (tv (st hf))))) terms
    refine ⟨A,ba.relax (by simp; omega) le_rfl Set.Subset.rfl,qq.trans qa,?_⟩
    convert out using 1
    funext X
    symm
    apply Bool.eq_iff_iff.mpr
    simp only [Finset.mem_univ,true_and,c,conj,Bool.and_eq_true,decide_eq_true_eq,signal]
    constructor
    · rintro ⟨k,hk,ok⟩; simpa only [← hk] using ok
    · intro yes; exact ⟨⟨R X,rank_lt hK⟩,rfl,yes⟩)
  obtain ⟨D,out,v,lt,nn,_,_,hit⟩ := some_taps bA (wa (vw (tv (st hf)))) (fun j => taps j (Finset.mem_univ _))
  refine ⟨D,out,v,lt,by simpa using nn,?_⟩
  intro X i hi j
  rw [hit]
  apply Bool.eq_iff_iff.mpr
  simp [signal,labelBit,R,correct_bucket hK hi good]

end PEqualNP.Outside.L_lib_1429.FixedBook

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds

def val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun bank g => bank ++ [val g bank]) w
def negs (gs : List Gate) : Nat :=
  (gs.filter fun g => @decide (g.op = .not) (lineDegreeGateOpDecEq _ _)).length

def rank : List Gate → List Bool → Nat
  | [], _ => 0
  | g :: gs, w =>
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    let v := val g w
    (if g.op = .not ∧ v = true then 2 ^ negs gs else 0) + rank gs (w ++ [v])

def force (g : Gate) : Gate :=
  @ite Gate (g.op = .not) (lineDegreeGateOpDecEq _ _) ⟨.and,[]⟩ g
def ordered (a b : List Bool) : Prop := a.length = b.length ∧ ∀ i, a.getD i false ≤ b.getD i false
def legal (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not

theorem nextNeg (g : Gate) (gs : List Gate) : negs (g :: gs) = negs gs + (@ite Nat (g.op = .not) (lineDegreeGateOpDecEq _ _) 1 0) := by
  by_cases h : g.op = .not <;> simp [negs,h]

theorem rankBound (gs : List Gate) (w : List Bool) : rank gs w < 2 ^ negs gs := by
  induction gs generalizing w with
  | nil => simp [rank,negs]
  | cons g gs ih =>
    have h := ih (w ++ [val g w])
    by_cases e : g.op = .not
    · rw [nextNeg,ite_eq_left e,pow_succ]
      simp only [rank,e,true_and]
      split <;> omega
    · simpa [rank,nextNeg,e] using h

theorem orderedSnoc {a b : List Bool} {x y : Bool} (h : ordered a b) (xy : x ≤ y) :
    ordered (a ++ [x]) (b ++ [y]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by rwa [← h.1])]
    exact h.2 i
  · by_cases eq : i = a.length
    · rw [eq]
      simpa [h.1] using xy
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; have := h.1; omega)]

theorem monoVal (g : Gate) {a b : List Bool} (h : ordered a b) (op : g.op = .and ∨ g.op = .or) :
    val g a ≤ val g b := by
  rcases op with eq | eq
  · simp only [val,eq,GateOp.eval,List.all_map,Function.id_comp]
    exact Bool.le_iff_imp.mpr fun ok => List.all_eq_true.mpr fun i hi =>
      Bool.le_iff_imp.mp (h.2 i) (List.all_eq_true.mp ok i hi)
  · simp only [val,eq,GateOp.eval,List.any_map,Function.id_comp]
    apply Bool.le_iff_imp.mpr
    rintro ok
    obtain ⟨i,hi,hv⟩ := List.any_eq_true.mp ok
    exact List.any_eq_true.mpr ⟨i,hi,Bool.le_iff_imp.mp (h.2 i) hv⟩

theorem antiVal (g : Gate) {a b : List Bool} (h : ordered a b) (op : g.op = .not) : val g b ≤ val g a := by
  cases ins : g.inputs with
  | nil => simp [val,op,ins]
  | cons i is =>
    have hi := h.2 i
    simp only [val,op,ins,List.map_cons,GateOp.eval,List.headD_cons]
    revert hi
    cases a.getD i false <;> cases b.getD i false <;> decide

theorem rankOrOrdered (gs : List Gate) (ok : legal gs) {a b : List Bool} (h : ordered a b) :
    rank gs b < rank gs a ∨ (rank gs b = rank gs a ∧ ordered (run gs a) (run gs b)) := by
  induction gs generalizing a b with
  | nil => exact Or.inr ⟨rfl,h⟩
  | cons g gs ih =>
    have ht : legal gs := fun u hu => ok u (by simp [hu])
    by_cases e : g.op = .not
    · have le := antiVal g h e
      by_cases eq : val g a = val g b
      · have r := ih ht (orderedSnoc h (le_of_eq eq))
        change _ ∨ (_ ∧ ordered (run gs (a ++ [val g a])) (run gs (b ++ [val g b])))
        simpa only [rank,e,true_and,eq,Nat.add_lt_add_iff_left,Nat.add_right_inj] using r
      · have ha : val g a = true := by
          cases p : val g a <;> cases q : val g b <;> simp_all
          exact ((by decide : ¬ ((true : Bool) ≤ false)) le).elim
        have hb : val g b = false := by cases p : val g b <;> simp_all
        left
        have lim := rankBound gs (b ++ [false])
        simp only [rank,e,ha,hb,true_and,ite_true,Bool.false_eq_true,ite_false,Nat.zero_add]
        omega
    · have op := ok g (by simp)
      have m := monoVal g h (op.imp_right (fun pair => pair.resolve_right e))
      simpa only [rank,e,false_and,ite_false,Nat.zero_add,run,List.foldl_cons] using ih ht (orderedSnoc h m)

theorem forceUpper (gs : List Gate) (ok : legal gs) {a b : List Bool} (h : ordered a b) :
    ordered (run gs a) (run (gs.map force) b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun u hu => ok u (by simp [hu])) (orderedSnoc h _)
    by_cases e : g.op = .not
    · simp [force,e,val,GateOp.eval]
    · simpa [force,e] using monoVal g h ((ok g (by simp)).imp_right (fun pair => pair.resolve_right e))

theorem forceExact (gs : List Gate) (w : List Bool) (full : rank gs w + 1 = 2 ^ negs gs) :
    run (gs.map force) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have lim := rankBound gs (w ++ [val g w])
    have ht : rank gs (w ++ [val g w]) + 1 = 2 ^ negs gs := by
      by_cases e : g.op = .not
      · rw [nextNeg,ite_eq_left e,pow_succ] at full
        simp only [rank,e,true_and] at full
        split at full <;> omega
      · simpa [rank,nextNeg,e] using full
    have hv : val (force g) w = val g w := by
      by_cases e : g.op = .not
      · have v : val g w = true := by
          by_contra hf
          rw [nextNeg,ite_eq_left e,pow_succ] at full
          simp only [rank,e,true_and,ite_eq_right hf,Nat.zero_add] at full
          omega
        simp [force,e,val,GateOp.eval,← v]
      · simp [force,e]
    change run (gs.map force) (w ++ [val (force g) w]) = run gs (w ++ [val g w])
    rw [hv,ih _ ht]

theorem fallingStep (gs : List Gate) (ok : legal gs) {a b : List Bool} (h : ordered a b)
    (fall : ∃ o, (run gs a).getD o false = true ∧ (run gs b).getD o false = false) :
    rank gs b < rank gs a := by
  obtain ⟨o,hi,lo⟩ := fall
  rcases rankOrOrdered gs ok h with lt | ⟨_,mono⟩
  · exact lt
  · have bad := mono.2 o
    rw [hi,lo] at bad
    exact ((by decide : ¬ ((true : Bool) ≤ false)) bad).elim

theorem saturates {gs : List Gate} (ok : legal gs) {b : Nat} (bound : negs gs ≤ b)
    (start : List Bool) (w : Nat → List Bool) (lower : ordered start (w 0))
    (steps : ∀ i, i + 1 < 2^b → ordered (w i) (w (i+1)) ∧
      ∃ o, (run gs (w i)).getD o false = true ∧ (run gs (w (i+1))).getD o false = false) :
    run (gs.map force) start = run gs start := by
  have loss (i : Nat) (hi : i < 2^b) : rank gs (w i) + i ≤ rank gs (w 0) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have z := steps i hi
      have st := fallingStep gs ok z.1 z.2
      have prev := ih (by omega)
      omega
  have pos : 0 < 2^b := by positivity
  have big := loss (2^b-1) (by omega)
  have smaller := rankBound gs start
  have order := rankOrOrdered gs ok lower
  have budget : 2^negs gs ≤ 2^b := Nat.pow_le_pow_right (by decide) bound
  apply forceExact
  rcases order with lt | ⟨eq, _⟩ <;> omega

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

def validAt (n : Nat) (D : Circuit) : Prop := FanInTwo D ∧ ReadsBack n D ∧ D.output < n + D.size

def address (p q : Nat) (src : Fin p → Fin q) (i : Nat) : Nat :=
  if h : i < p then (src ⟨i,h⟩).val else q + (i-p)

def projectGate (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def projected (p q : Nat) (src : Fin p → Fin q) (D : Circuit) : Circuit :=
  ⟨D.gates.map (projectGate (address p q src)), address p q src D.output⟩

theorem addressLt (p q : Nat) (src : Fin p → Fin q) {i k : Nat} (h : i < p+k) :
    address p q src i < q+k := by
  unfold address
  split
  · rename_i hi
    have := (src ⟨i,hi⟩).isLt
    omega
  · omega

theorem projectValid (p q : Nat) (src : Fin p → Fin q) {D : Circuit} (h : validAt p D) :
    validAt q (projected p q src D) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    simpa [projectGate] using h.1 t ht
  · intro j hj i hi
    have hj' : j < D.gates.length := by simpa [projected] using hj
    have eq : gateAt (projected p q src D) j = projectGate (address p q src) (gateAt D j) := by
      simp only [gateAt,projected,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases D.gates[j]? <;> simp [projectGate]
    rw [eq] at hi
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
    exact addressLt p q src (h.2.1 j hj' t ht)
  · simpa [projected,Circuit.size] using addressLt p q src h.2.2

private theorem tailAddress (p q : Nat) (src : Fin p → Fin q) (k : Nat) :
    address p q src (p+k) = q+k := by simp [address]
private theorem atSnoc {α : Type} (l : List α) (v d : α) (i : Nat) (hne : i ≠ l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

theorem projectWires (p q : Nat) (src : Fin p → Fin q) (gs : List Gate)
    (k : Nat) (a b : List Bool) (la : a.length = p+k) (lb : b.length = q+k)
    (agree : ∀ i, a.getD i false = b.getD (address p q src i) false) :
    ∀ i, (run gs a).getD i false =
      (run (gs.map (projectGate (address p q src))) b).getD (address p q src i) false := by
  induction gs generalizing k a b with
  | nil => exact agree
  | cons g gs ih =>
    have ev : val g a = val (projectGate (address p q src) g) b := by
      simp only [val,projectGate,List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => agree i
    intro i
    apply ih (k+1) (a ++ [val g a]) (b ++ [val (projectGate (address p q src) g) b])
      (by simp [la,Nat.add_assoc]) (by simp [lb,Nat.add_assoc]) _ i
    intro j
    by_cases eq : j = p+k
    · rw [eq,tailAddress,← la,← lb]
      simpa using ev
    · have ne : address p q src j ≠ q+k := by
        by_cases hj : j < p+k
        · exact Nat.ne_of_lt (addressLt _ _ _ hj)
        · have h : ¬ j < p := by omega
          simp [address,h]
          omega
      rw [atSnoc a _ _ _ (by rwa [la]),atSnoc b _ _ _ (by rwa [lb])]
      exact agree j

theorem projectEval (p q : Nat) (src : Fin p → Fin q) (D : Circuit)
    (old new : List Bool) (lo : old.length=p) (ln : new.length=q)
    (raw : ∀ i : Fin p, old.getD i.val false = new.getD (src i).val false) :
    (projected p q src D).eval new = D.eval old := by
  symm
  apply projectWires p q src D.gates 0 old new (by simpa using lo) (by simpa using ln) _ D.output
  intro i
  by_cases h : i < p
  · simpa [address,h] using raw ⟨i,h⟩
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [address,h]; omega)]

def forced (D : Circuit) : Circuit := ⟨D.gates.map force,D.output⟩

theorem forcedValid (p : Nat) (D : Circuit) (hv : validAt p D) : validAt p (forced D) := by
  refine ⟨?_,?_,by simpa [forced,Circuit.size] using hv.2.2⟩
  · intro g hg
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
    by_cases e : u.op = .not
    · simp [force,e]
    · simpa [force,e] using hv.1 u hu
  · intro j hj i hi
    have hj' : j < D.gates.length := by simpa [forced] using hj
    have atj : gateAt (forced D) j = force (gateAt D j) := by
      simp only [gateAt,forced,List.getD_eq_getElem?_getD,List.getElem?_map]
      rw [List.getElem?_eq_getElem hj']
      rfl
    rw [atj] at hi
    by_cases op : (gateAt D j).op = .not
    · simp [force,op] at hi
    · exact hv.2.1 j hj' i (by simpa [force,op] using hi)

theorem projectedForcedZero (p q : Nat) (src : Fin p → Fin q) (D : Circuit) :
    NotBracket.notCount (projected p q src (forced D)) = 0 := by
  unfold NotBracket.notCount
  rw [List.length_eq_zero_iff,List.filter_eq_nil_iff]
  intro g hg
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
  by_cases e : v.op = .not <;> simp [projectGate,force,e]

theorem projectForDecision {p q b : Nat} (src : Fin p → Fin q) (D : Circuit) (hv : validAt p D)
    (budget : NotBracket.notCount D ≤ b) :
    ∃ S : Circuit, validAt q S ∧ NotBracket.notCount S = 0 ∧ S.size ≤ D.size - NotBracket.notCount D + b ∧
      ∀ old new : List Bool, old.length = p → new.length = q →
        (∀ i : Fin p, old.getD i.val false = new.getD (src i).val false) →
        S.eval new = (forced D).eval old := by
  refine ⟨projected p q src (forced D),projectValid p q src (forcedValid p D hv),
    projectedForcedZero p q src D,?_,fun a b => projectEval p q src _ a b⟩
  have eq : (projected p q src (forced D)).size = D.size := by simp [projected,forced,Circuit.size]
  rw [eq]
  omega

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open Classical
noncomputable def valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
noncomputable def bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y))
noncomputable def adj := fun (n : Nat) (E : Finset Nat) (u v : Nat) => u≠v ∧ min u v*n+max u v ∈ E
noncomputable def clq := fun (n k : Nat) (E : Finset Nat) => ∃ v : Fin k → Fin n,
  ∀ i j, i<j → adj n E (v i).val (v j).val
noncomputable def fit := fun {m : Nat} (r b : Nat) (A B : Fin m → Finset Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → Nat), valid r D ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, o j < r+2+D.size) ∧
    ∀ Y ⊆ Finset.range r, ∀ i, A i ⊆ Y → Y ⊆ B i →
      ∀ j, (D.wires (bits r Y ++ [false,true])).getD (o j) false = decide (i=j)
noncomputable def serve := fun (m r b : Nat) (sepOnly : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat) =>
  let t := 2*m*r+r
  valid t D ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, out j < t+2+D.size) ∧
    ∀ (Z O : Fin m → Finset Nat), (∀ i, Z i ⊆ Finset.range r ∧ O i ⊆ Finset.range r) →
      let A := fun i => Finset.range r \ Z i
      let sep := ∀ i j Y, A i ⊆ Y → Y ⊆ O i → A j ⊆ Y → Y ⊆ O j → i=j
      (sepOnly=true → sep) → ∀ X ⊆ Finset.range r,
        let I := (List.ofFn (fun i => bits r (Z i))).flatten ++
          (List.ofFn (fun i => bits r (O i))).flatten ++ bits r X ++ [false,true]
        (D.eval I = false ↔ fit r b A O) ∧ (fit r b A O →
          ∀ i, A i ⊆ X → X ⊆ O i → ∀ j, (D.wires I).getD (out j) false = decide (i=j))
noncomputable def solves := fun (n k : Nat) (S : PEqualNP.CircuitLowerBounds.Circuit) =>
  valid (n*n) S ∧ PEqualNP.NotBracket.notCount S=0 ∧ ∀ E ⊆ Finset.range (n*n),
    S.eval (bits (n*n) E ++ [false,true]) = decide (clq n k E)
noncomputable def R := fun (K n : Nat) => 2+K+(K+1)*n
noncomputable def M := fun (K n : Nat) => K+(K+1)*n
noncomputable def base := fun (i : Nat) => insert 0 (Finset.Ico 2 (2+i))
noncomputable def lower := fun (K n : Nat) (j : Fin (M K n)) =>
  if j.val<K then base j.val else {1,2+K+(j.val-K)}
noncomputable def upper := fun (K n : Nat) (E : Finset Nat) (j : Fin (M K n)) =>
  if j.val<K then base j.val else
    (Finset.range (R K n)).filter (fun x => x=1 ∨ x=2+K+(j.val-K) ∨
      (2+K≤x ∧ (x-(2+K))/n < (j.val-K)/n ∧ adj n E ((x-(2+K)) % n) ((j.val-K) % n)))

noncomputable def rows {m : Nat} (r : Nat) (s : Fin m → Finset Nat) : List Bool :=
  (List.ofFn (fun i => bits r (s i))).flatten
noncomputable def inp {m : Nat} (r : Nat) (Z O : Fin m → Finset Nat) (X : Finset Nat) : List Bool :=
    rows r Z ++ rows r O ++ bits r X ++ [false,true]

theorem orderedAppend {a b c d : List Bool} (h : ordered a b) (k : ordered c d) : ordered (a++c) (b++d) := by
  refine ⟨by simp [h.1,k.1],?_⟩
  intro i
  by_cases hi : i<a.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by rwa [← h.1])]
    exact h.2 _
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by have := h.1; omega),h.1]
    exact k.2 _

theorem bitsGet (r : Nat) (X : Finset Nat) (j : Fin r) : (bits r X).getD j.val false = decide (j.val ∈ X) := by
  simp only [bits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]

theorem inpOrder {m r : Nat} (Z O : Fin m → Finset Nat) {X Y : Finset Nat} (h : X ⊆ Y) :
    ordered (inp r Z O X) (inp r Z O Y) := by
  apply orderedAppend _ ⟨rfl,fun _ => le_rfl⟩
  apply orderedAppend ⟨rfl,fun _ => le_rfl⟩
  refine ⟨by simp [bits],?_⟩
  intro i
  by_cases hi : i<r
  · rw [bitsGet r X ⟨i,hi⟩,bitsGet r Y ⟨i,hi⟩]
    apply Bool.le_iff_imp.mpr
    simpa using (fun hi : i ∈ X => h hi)
  · rw [List.getD_eq_default _ _ (by simp [bits]; omega),List.getD_eq_default _ _ (by simp [bits]; omega)]

theorem baseMono : Monotone base := by
  intro i j hij z hz
  simp [base] at hz ⊢
  omega

theorem baseline {K n : Nat} (i : Nat) (hi : i<K) : ∃ j : Fin (M K n),
    j.val=i ∧ lower K n j = base i ∧ ∀ E, upper K n E j = base i := by
  exact ⟨⟨i,by unfold M; omega⟩,rfl,by simp [lower,hi],fun E => by simp [upper,hi]⟩

noncomputable def bookZ (K n : Nat) (j : Fin (M K n)) := Finset.range (R K n) \ lower K n j

theorem baselineWithin {K n i : Nat} (hi : i<K) : base i ⊆ Finset.range (R K n) := by
  intro x hx
  simp [base] at hx
  simp [R]
  omega

theorem forcedVerdict (n b : Nat) (E : Finset Nat) (D : Circuit) (out : Fin (M (2^b) n) → Nat)
    (served : serve (M (2^b) n) (R (2^b) n) b true D out)
    (bound : ∀ i, lower (2^b) n i ⊆ upper (2^b) n E i ∧ upper (2^b) n E i ⊆ Finset.range (R (2^b) n))
    (sep : ∀ i j Y, lower (2^b) n i ⊆ Y → Y ⊆ upper (2^b) n E i →
      lower (2^b) n j ⊆ Y → Y ⊆ upper (2^b) n E j → i=j)
    (book : fit (R (2^b) n) b (lower (2^b) n) (upper (2^b) n E) ↔ ¬clq n (2^b+1) E) :
    (forced D).eval (inp (R (2^b) n) (bookZ (2^b) n) (upper (2^b) n E) ∅) = decide (clq n (2^b+1) E) := by
  let K := 2^b
  let r := R K n
  let Z := bookZ K n
  let O := upper K n E
  let a := inp r Z O
  obtain ⟨v,nb,_,decoder⟩ := served
  have hz : (fun i => Finset.range r \ Z i) = lower K n := by
    funext i
    exact Finset.sdiff_sdiff_eq_self ((bound i).1.trans (bound i).2)
  have all (X : Finset Nat) (hX : X ⊆ Finset.range r) :=
    decoder Z O (fun i => ⟨Finset.sdiff_subset,(bound i).2⟩) (by
      intro _
      rw [hz]
      exact sep) X hX
  have serves (X : Finset Nat) (hX : X ⊆ Finset.range r) :
      (D.eval (a X) = false ↔ fit r b (lower K n) O) ∧
        (fit r b (lower K n) O → ∀ i, lower K n i ⊆ X → X ⊆ O i → ∀ j,
        (D.wires (a X)).getD (out j) false = decide (i=j)) := by
    have hh := all X hX
    rw [← hz]
    exact hh
  have ops : legal D.gates := fun g hg => (v.1 g hg).1
  by_cases feasible : fit r b (lower K n) O
  · have no := book.mp feasible
    rw [decide_eq_false no]
    have fall (i : Nat) (hi : i+1<K) : ∃ o,
        (run D.gates (a (base i))).getD o false = true ∧
        (run D.gates (a (base (i+1)))).getD o false = false := by
      obtain ⟨p,hp,lp,up⟩ := baseline (n:=n) i (by omega : i<K)
      obtain ⟨q,hq,lq,uq⟩ := baseline (n:=n) (i+1) hi
      have pq : q ≠ p := fun h => by have := congrArg Fin.val h; omega
      refine ⟨out p,?_,?_⟩
      · have z := (serves _ (baselineWithin (n:=n) (by omega : i<K))).2 feasible p
          (by rw [lp]) (by change base i ⊆ upper K n E p; rw [up]) p
        simpa [Circuit.wires,run,val] using z
      · have z := (serves _ (baselineWithin (n:=n) hi)).2 feasible q
          (by rw [lq]) (by change base (i+1) ⊆ upper K n E q; rw [uq]) p
        simpa [Circuit.wires,run,val,pq] using z
    have eq := saturates ops nb (a ∅) (fun i => a (base i))
      (inpOrder _ _ (Finset.empty_subset _))
      (fun i hi => ⟨inpOrder _ _ (baseMono (Nat.le_succ i)),fall i hi⟩)
    have hv := (serves ∅ (Finset.empty_subset _)).1.mpr feasible
    change (run (D.gates.map force) (a ∅)).getD D.output false = _
    rw [eq]
    exact hv
  · have yes := Classical.byContradiction fun h => feasible (book.mpr h)
    rw [decide_eq_true yes]
    have hv : D.eval (a ∅) = true := by
      cases eq : D.eval (a ∅) with
      | true => rfl
      | false => exact (feasible ((serves _ (Finset.empty_subset _)).1.mp eq)).elim
    have ord := (forceUpper D.gates ops (show ordered (a ∅) (a ∅) from ⟨rfl,fun _ => le_rfl⟩)).2 D.output
    exact Bool.le_iff_imp.mp ord hv

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds
open Classical

noncomputable def constAddr (p : Nat) (b : Bool) : Fin (p+2) := ⟨if b then p+1 else p,by split <;> omega⟩
noncomputable def edgeAddr (n e : Nat) : Fin (n*n+2) := if h : e<n*n then ⟨e,by omega⟩ else constAddr _ false
noncomputable def graphInput (n : Nat) (E : Finset Nat) := bits (n*n) E ++ [false,true]
noncomputable def read (n : Nat) (E : Finset Nat) (j : Fin (n*n+2)) := (graphInput n E).getD j.val false

theorem readConst (n : Nat) (E : Finset Nat) (b : Bool) : read n E (constAddr (n*n) b) = b := by
  cases b <;> simp [read,constAddr,graphInput,bits]

theorem readEdge (n e : Nat) (E : Finset Nat) (hE : E ⊆ Finset.range (n*n)) :
    read n E (edgeAddr n e) = decide (e∈E) := by
  by_cases h : e<n*n
  · simp only [read,edgeAddr,h,dite_true,graphInput]
    rw [List.getD_append _ _ _ _ (by simpa [bits] using h),bitsGet (n*n) E ⟨e,h⟩]
  · have no : e∉E := fun he => h (Finset.mem_range.mp (hE he))
    simp [edgeAddr,h,no,readConst]

noncomputable def permAddr (K n : Nat) (j : Fin (M K n)) (x : Fin (R K n)) : Fin (n*n+2) :=
  if j.val < K then constAddr _ (decide (x.val ∈ base j.val))
  else if x.val=1 ∨ x.val=2+K+(j.val-K) then constAddr _ true
  else if 2+K ≤ x.val ∧ (x.val-(2+K))/n < (j.val-K)/n ∧ (x.val-(2+K))%n ≠ (j.val-K)%n then
    edgeAddr n (min ((x.val-(2+K))%n) ((j.val-K)%n) * n + max ((x.val-(2+K))%n) ((j.val-K)%n))
  else constAddr _ false

theorem readPerm (K n : Nat) (E : Finset Nat) (hE : E ⊆ Finset.range (n*n))
    (j : Fin (M K n)) (x : Fin (R K n)) :
    read n E (permAddr K n j x) = decide (x.val ∈ upper K n E j) := by
  unfold permAddr upper
  split
  · exact readConst _ _ _
  · split
    · rename_i a
      rw [readConst]
      symm
      apply decide_eq_true
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, a.elim Or.inl (Or.inr ∘ Or.inl)⟩
    · rename_i a
      split
      · rename_i d
        rw [readEdge _ _ _ hE]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro yes
          apply decide_eq_true
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt,Or.inr (Or.inr ⟨d.1,d.2.1,d.2.2,of_decide_eq_true yes⟩)⟩
        · intro ht
          obtain ⟨_, e | e | ⟨_,_,_,yes⟩⟩ := Finset.mem_filter.mp (of_decide_eq_true ht)
          · exact (a (Or.inl e)).elim
          · exact (a (Or.inr e)).elim
          · exact decide_eq_true yes
      · rename_i d
        rw [readConst]
        symm
        apply decide_eq_false
        intro yes
        obtain ⟨_, e | e | ⟨v,w,z,_⟩⟩ := Finset.mem_filter.mp yes
        · exact a (Or.inl e)
        · exact a (Or.inr e)
        · exact d ⟨v,w,z⟩

noncomputable def rowCodes {m r q : Nat} (f : Fin m → Fin r → Fin q) : List (Fin q) :=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem rowCodeLen {m r q : Nat} (f : Fin m → Fin r → Fin q) : (rowCodes f).length = m*r := by
  rw [rowCodes,List.length_flatten,List.map_ofFn]
  have eq : (List.length ∘ (fun i => List.ofFn (f i))) = fun _ => r := funext fun _ => List.length_ofFn
  simp [eq,List.ofFn_const]

theorem readRows {m r n : Nat} (E : Finset Nat) (P : Fin m → Finset Nat)
    (f : Fin m → Fin r → Fin (n*n+2)) (hf : ∀ i j, read n E (f i j) = decide (j.val ∈ P i)) :
    (rowCodes f).map (read n E) = rows r P := by
  simp only [rowCodes,rows,List.map_flatten,List.map_ofFn,Function.comp_def,bits]
  simp only [hf]

noncomputable def codes (K n : Nat) : List (Fin (n*n+2)) :=
  rowCodes (fun i (j : Fin (R K n)) => constAddr (n*n) (decide (j.val ∈ bookZ K n i))) ++
  rowCodes (permAddr K n) ++ List.replicate (R K n) (constAddr _ false) ++ [constAddr _ false,constAddr _ true]

theorem codesLength (K n : Nat) : (codes K n).length = 2*M K n*R K n+R K n+2 := by
  simp [codes,rowCodeLen]
  ring

theorem codesAgree (K n : Nat) (E : Finset Nat) (hE : E ⊆ Finset.range (n*n)) :
    (codes K n).map (read n E) = inp (R K n) (bookZ K n) (upper K n E) ∅ := by
  unfold codes inp
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_replicate,readConst]
  rw [readRows E (bookZ K n) _ (fun _ _ => readConst _ _ _), readRows E (upper K n E) _ (readPerm K n E hE)]
  simp [bits,List.ofFn_const]

noncomputable def src (K n : Nat) (i : Fin (2*M K n*R K n+R K n+2)) : Fin (n*n+2) :=
  (codes K n).get ⟨i.val,by rw [codesLength]; exact i.isLt⟩

theorem rawAgreement (K n : Nat) (E : Finset Nat) (hE : E ⊆ Finset.range (n*n))
    (i : Fin (2*M K n*R K n+R K n+2)) :
    (inp (R K n) (bookZ K n) (upper K n E) ∅).getD i.val false =
      (graphInput n E).getD (src K n i).val false := by
  rw [← codesAgree K n E hE]
  have hi : i.val < (codes K n).length := by rw [codesLength]; exact i.isLt
  simp [src,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi,read]

theorem fromBoxes
    (hboxes : ∀ n b E, E ⊆ Finset.range (n*n) →
      (∀ i, lower (2^b) n i ⊆ upper (2^b) n E i ∧ upper (2^b) n E i ⊆ Finset.range (R (2^b) n)) ∧
      (∀ i j Y, lower (2^b) n i ⊆ Y → Y ⊆ upper (2^b) n E i →
        lower (2^b) n j ⊆ Y → Y ⊆ upper (2^b) n E j → i=j) ∧
      (fit (R (2^b) n) b (lower (2^b) n) (upper (2^b) n E) ↔ ¬clq n (2^b+1) E))
    (n b : Nat) (D : Circuit) (out : Fin (M (2^b) n) → Nat)
    (h : serve (M (2^b) n) (R (2^b) n) b true D out) :
    ∃ S : Circuit, solves n (2^b+1) S ∧ S.size ≤ D.size-NotBracket.notCount D+b := by
  let K := 2^b
  obtain ⟨S,v,nn,size,sem⟩ := projectForDecision (src K n) D h.1 h.2.1
  refine ⟨S,⟨v,nn,?_⟩,size⟩
  intro E hE
  obtain ⟨bound,sep,book⟩ := hboxes n b E hE
  have eq := sem (inp (R K n) (bookZ K n) (upper K n E) ∅) (graphInput n E)
    (by rw [← codesAgree K n E hE,List.length_map,codesLength])
    (by simp [graphInput,bits]) (rawAgreement K n E hE)
  exact eq.trans (forcedVerdict n b E D out h bound sep book)

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open Classical

theorem boxBound (K n : Nat) (E : Finset Nat) (j : Fin (M K n)) :
    lower K n j ⊆ upper K n E j ∧ upper K n E j ⊆ Finset.range (R K n) := by
  by_cases h : j.val<K
  · simp only [lower,upper,h,ite_true]
    exact ⟨Finset.Subset.rfl,baselineWithin h⟩
  · simp only [lower,upper,h,ite_false]
    refine ⟨?_,Finset.filter_subset _ _⟩
    intro x hx
    have lt := j.isLt
    unfold M at lt
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by unfold R; omega),?_⟩
    tauto

theorem baseCard (i : Nat) : (base i).card = i+1 := by
  rw [base,Finset.card_insert_of_notMem (by simp),Nat.card_Ico]
  omega

private theorem compatible {K n : Nat} {E : Finset Nat} {i j : Fin (M K n)}
    (h : lower K n i ⊆ upper K n E j) :
    (i.val<K ∧ j.val<K ∧ i.val ≤ j.val) ∨
    (K ≤ i.val ∧ K ≤ j.val ∧ (i=j ∨
      ((i.val-K)/n < (j.val-K)/n ∧ adj n E ((i.val-K)%n) ((j.val-K)%n)))) := by
  by_cases hi : i.val<K <;> by_cases hj : j.val<K
  · left
    have card := Finset.card_le_card h
    simp only [lower,upper,hi,hj,ite_true,baseCard] at card
    exact ⟨hi,hj,by omega⟩
  · have hx := h (show 0 ∈ lower K n i by simp [lower,hi,base])
    simp [upper,hj] at hx
    omega
  · have hx := h (show 1 ∈ lower K n i by simp [lower,hi])
    simp [upper,hj,base] at hx
  · right
    refine ⟨by omega,by omega,?_⟩
    have hx := h (show 2+K+(i.val-K) ∈ lower K n i by simp [lower,hi])
    simp only [upper,hj,ite_false,Finset.mem_filter] at hx
    obtain ⟨_, eq | eq | ⟨_,lev,edge⟩⟩ := hx
    · omega
    · left; apply Fin.ext; omega
    · right
      simpa using And.intro lev edge

theorem boxesSep {K n : Nat} {E : Finset Nat} (i j : Fin (M K n)) (Y : Finset Nat)
    (il : lower K n i ⊆ Y) (iu : Y ⊆ upper K n E i)
    (jl : lower K n j ⊆ Y) (ju : Y ⊆ upper K n E j) : i=j := by
  have x := compatible (il.trans ju)
  have y := compatible (jl.trans iu)
  rcases x with ⟨_,_,ij⟩ | ⟨_,_,eq | ⟨lv,_⟩⟩
  · apply Fin.ext; rcases y with ⟨_,_,_⟩ | ⟨_,_,_⟩ <;> omega
  · exact eq
  · rcases y with ⟨_,_,_⟩ | ⟨_,_,eq | ⟨_,_⟩⟩
    · omega
    · exact eq.symm
    · omega

def word (K n : Nat) (E : Finset Nat) : Prop :=
  ∃ (h : Fin (K+1) → Fin (M K n)) (Y : Fin (K+1) → Finset Nat), Monotone Y ∧
    (∀ i j, i.val+1=j.val → h i ≠ h j) ∧
    ∀ i, lower K n (h i) ⊆ Y i ∧ Y i ⊆ upper K n E (h i)

theorem wordClique {K n : Nat} {E : Finset Nat} (w : word K n E) : clq n (K+1) E := by
  obtain ⟨f,Y,inc,diff,yes⟩ := w
  have cp (i j : Fin (K+1)) (le : i ≤ j) := compatible (((yes i).1.trans (inc le)).trans (yes j).2)
  by_cases hb : (f 0).val<K
  · have bs (i : Fin (K+1)) : (f i).val<K := by
      have := cp 0 i (Fin.zero_le _)
      omega
    have st : StrictMono (fun i => (f i).val) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have cs := cp i.castSucc i.succ (by exact Fin.le_iff_val_le_val.mpr (by simp))
      have ne := diff i.castSucc i.succ rfl
      have vn : (f i.castSucc).val ≠ (f i.succ).val := fun h => ne (Fin.ext h)
      have := bs i.castSucc
      omega
    have upto (j : Nat) (hj : j<K+1) : j  ≤  (f ⟨j,hj⟩).val := by
      induction j with
      | zero => omega
      | succ j ih =>
        have hj' : j<K+1 := by omega
        have grow := st (show (⟨j,hj'⟩ : Fin (K+1)) < ⟨j+1,hj⟩ by exact Nat.lt_succ_self _)
        change (f ⟨j,hj'⟩).val < (f ⟨j+1,hj⟩).val at grow
        have := ih hj'
        omega
    have ha := upto K (by omega)
    have hb' := bs ⟨K,by omega⟩
    omega
  · have high (i : Fin (K+1)) : K ≤ (f i).val := by have := cp 0 i (Fin.zero_le _); omega
    have npos : 0<n := by
      by_contra! no
      have hn : n=0 := by omega
      have hh := (f 0).isLt
      simp [M,hn] at hh
      omega
    let level (i : Fin (K+1)) := ((f i).val-K)/n
    have st : StrictMono level := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have cs := cp i.castSucc i.succ (by exact Fin.le_iff_val_le_val.mpr (by simp))
      have ne := diff i.castSucc i.succ rfl
      have := high i.castSucc
      exact cs.elim (fun h => False.elim (by omega)) (fun h => (h.2.2.resolve_left ne).1)
    refine ⟨fun i => ⟨((f i).val-K)%n,Nat.mod_lt _ npos⟩,?_⟩
    intro i j lt
    have l := st lt
    have ne : f i ≠ f j := fun eq => by simp [level,eq] at l
    have hi := high i
    exact (cp i j lt.le).elim (fun h => False.elim (by omega)) (fun h => (h.2.2.resolve_left ne).2)

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open Classical

theorem cliqueWord {K n : Nat} {E : Finset Nat} (clique : clq n (K+1) E) : word K n E := by
  obtain ⟨v,edges⟩ := clique
  have npos : 0<n := Nat.zero_lt_of_lt (v 0).isLt
  let idx (i : Fin (K+1)) := i.val*n+(v i).val
  have idxBound (i : Fin (K+1)) : idx i < (K+1)*n := by
    have upper := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    have vlt := (v i).isLt
    rw [Nat.succ_mul] at upper
    dsimp [idx]
    omega
  have quotient (i : Fin (K+1)) : idx i/n=i.val := by
    dsimp [idx]
    rw [Nat.mul_comm i.val n,Nat.mul_add_div npos,Nat.div_eq_of_lt (v i).isLt,Nat.add_zero]
  have rem (i : Fin (K+1)) : idx i%n=(v i).val := by
    simp [idx,Nat.mod_eq_of_lt (v i).isLt]
  let h (i : Fin (K+1)) : Fin (M K n) := ⟨K+idx i, by have := idxBound i; unfold M; omega⟩
  let tag (i : Fin (K+1)) := 2+K+idx i
  let Y (i : Fin (K+1)) := insert 1 ((Finset.Iic i).image tag)
  have ymem (i : Fin (K+1)) (x : Nat) : x∈Y i ↔ x=1 ∨ ∃ s, s ≤ i ∧ tag s=x := by
    simp [Y]
  refine ⟨h,Y,?_,?_,?_⟩
  · intro i j le x hx
    rcases (ymem i x).mp hx with one | ⟨s,si,rfl⟩
    · exact (ymem j x).mpr (Or.inl one)
    · exact (ymem j _).mpr (Or.inr ⟨s,si.trans le,rfl⟩)
  · intro i j nxt eq
    have ix : idx i = idx j := by simpa [h] using congrArg Fin.val eq
    have ij : i.val = j.val := (quotient i).symm.trans ((congrArg (fun z => z/n) ix).trans (quotient j))
    omega
  · intro i
    have hi : ¬ (h i).val<K := by simp [h]
    have stage : (h i).val-K = idx i := by simp [h]
    refine ⟨?_,?_⟩
    · intro x hx
      simp only [lower,hi,ite_false,stage,Finset.mem_insert,Finset.mem_singleton] at hx
      exact (ymem i x).mpr (hx.imp_right fun eq => ⟨i,le_rfl,eq.symm⟩)
    · intro x hx
      simp only [upper,hi,ite_false,stage]
      rcases (ymem i x).mp hx with rfl | ⟨s,si,rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by unfold R; omega),Or.inl rfl⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by have := idxBound s; unfold tag R; omega),?_⟩
        rcases lt_or_eq_of_le si with lt | rfl
        · right; right
          have lo : 2+K  ≤  tag s := by simp [tag]
          have off : tag s-(2+K) = idx s := by simp [tag]
          exact ⟨lo,by simpa only [off,quotient] using (Fin.lt_def.mp lt),by simpa only [off,rem] using edges s i lt⟩
        · exact Or.inr (Or.inl rfl)

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds
open Classical

noncomputable def forget {r : Nat} (X : Finset (Fin r)) := X.map Fin.valEmbedding
noncomputable def liftSet (r : Nat) (X : Finset Nat) := Finset.univ.filter (fun i : Fin r => i.val ∈ X)

theorem forgetLift {r : Nat} {X : Finset Nat} (h : X ⊆ Finset.range r) : forget (liftSet r X) = X := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i,Finset.mem_range.mp (h hi)⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩

theorem liftBits (r : Nat) (X : Finset Nat) : FixedBook.bits (liftSet r X) = bits r X := by
  unfold FixedBook.bits bits
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [liftSet]

theorem wordNotFit {n b : Nat} {E : Finset Nat} (ww : word (2^b) n E) :
    ¬ fit (R (2^b) n) b (lower (2^b) n) (upper (2^b) n E) := by
  obtain ⟨f,Y,inc,ne,inBox⟩ := ww
  rintro ⟨D,out,valid,nb,_,works⟩
  let r := R (2^b) n
  let w (i : Fin (2^b+1)) := bits r (Y i) ++ [false,true]
  have ord {i j : Fin (2^b+1)} (h : i ≤ j) : ordered (w i) (w j) := by
    apply orderedAppend _ ⟨rfl,fun _ => le_rfl⟩
    refine ⟨by simp [bits],?_⟩
    intro k
    by_cases hk : k<r
    · rw [bitsGet r _ ⟨k,hk⟩,bitsGet r _ ⟨k,hk⟩]
      apply Bool.le_iff_imp.mpr
      simpa using (fun hmem : k∈Y i => inc h hmem)
    · rw [List.getD_eq_default _ _ (by simp [bits]; omega),List.getD_eq_default _ _ (by simp [bits]; omega)]
  have ok : legal D.gates := fun g hg => (valid.1 g hg).1
  have point (i j : Fin (2^b+1)) : (run D.gates (w i)).getD (out (f j)) false = decide (f i=f j) := by
    have hit := works (Y i) ((inBox i).2.trans (boxBound _ n E _).2) (f i) (inBox i).1 (inBox i).2 (f j)
    exact hit
  have loss (j : Nat) (hj : j<2^b+1) :
      rank D.gates (w ⟨j,hj⟩) + j ≤ rank D.gates (w 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      let i : Fin (2^b+1) := ⟨j,by omega⟩
      let k : Fin (2^b+1) := ⟨j+1,hj⟩
      have hk := fallingStep D.gates ok (ord (show i ≤ k from Nat.le_succ _)) (by
        refine ⟨out (f i),by simpa using point i i,?_⟩
        simpa [Ne.symm (ne i k rfl)] using point k i)
      have old := ih i.isLt
      change rank D.gates (w ⟨j+1,hj⟩) < rank D.gates (w ⟨j,_⟩) at hk
      omega
  have big := loss (2^b) (by omega)
  have lim := rankBound D.gates (w 0)
  have cut : 2^(negs D.gates) ≤ 2^b := Nat.pow_le_pow_right (by decide) nb
  omega

theorem noWordFit {n b : Nat} {E : Finset Nat} (no : ¬ word (2^b) n E) :
    fit (R (2^b) n) b (lower (2^b) n) (upper (2^b) n E) := by
  let K := 2^b
  let r := R K n
  let lab (X : Finset (Fin r)) (i : Fin (M K n)) := lower K n i ⊆ forget X ∧ forget X ⊆ upper K n E i
  have negative : ¬ FixedBook.Trace lab Finset.univ (2^b+1) := by
    rintro ⟨w,ne,Y,mono,_,fits⟩
    apply no
    refine ⟨w,fun i => forget (Y i),?_,ne,fits⟩
    intro i j h y hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨v,mono h hv,rfl⟩
  obtain ⟨D,out,vd,lt,neg,hD⟩ := FixedBook.noTracePossible negative
  refine ⟨D,out,vd,neg,lt,?_⟩
  intro X within i left right j
  have box : lab (liftSet r X) i := by
    change lower K n i ⊆ forget (liftSet r X) ∧ forget (liftSet r X) ⊆ upper K n E i
    rw [forgetLift (show X ⊆ Finset.range r from within)]
    exact ⟨left,right⟩
  have hot := hD _ i box j
  rw [liftBits] at hot
  exact hot.trans (Bool.eq_iff_iff.mpr (by simp [FixedBook.labelBit]))

theorem boxFit (n b : Nat) (E : Finset Nat) :
    fit (R (2^b) n) b (lower (2^b) n) (upper (2^b) n E) ↔ ¬clq n (2^b+1) E := by
  exact ⟨fun fitted clique => wordNotFit (cliqueWord clique) fitted,
    fun free => noWordFit fun w => free (wordClique w)⟩

end PEqualNP.Outside.L_lib_1429

namespace PEqualNP.Outside.L_lib_1429
open CircuitLowerBounds
private noncomputable def truth (p : Prop) : Bool := @decide p (Classical.propDecidable p)
private theorem canonicalTruth (p : Prop) (d : Decidable p) : @decide p d = truth p := by
  unfold truth
  rw [Subsingleton.elim d (Classical.propDecidable p)]
private theorem canonicalDiff (a b : Finset Nat) :
    @SDiff.sdiff (Finset Nat) (@Finset.instSDiff Nat (fun u v => Classical.propDecidable (u=v))) a b = a \ b := by
  ext i
  simp only [Finset.mem_sdiff]
end PEqualNP.Outside.L_lib_1429

open PEqualNP.Outside.L_lib_1429

theorem PEqualNP.Outside.L_lib_1429 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y))
let adj := fun (n : Nat) (E : Finset Nat) (u v : Nat) => u≠v ∧ min u v*n+max u v ∈ E
let clq := fun (n k : Nat) (E : Finset Nat) => ∃ v : Fin k → Fin n,
  ∀ i j, i<j → adj n E (v i).val (v j).val
let fit := fun {m : Nat} (r b : Nat) (A B : Fin m → Finset Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → Nat), valid r D ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, o j < r+2+D.size) ∧
    ∀ Y ⊆ Finset.range r, ∀ i, A i ⊆ Y → Y ⊆ B i →
      ∀ j, (D.wires (bits r Y ++ [false,true])).getD (o j) false = decide (i=j)
let serve := fun (m r b : Nat) (sepOnly : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat) =>
  let t := 2*m*r+r
  valid t D ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, out j < t+2+D.size) ∧
    ∀ (Z O : Fin m → Finset Nat), (∀ i, Z i ⊆ Finset.range r ∧ O i ⊆ Finset.range r) →
      let A := fun i => Finset.range r \ Z i
      let sep := ∀ i j Y, A i ⊆ Y → Y ⊆ O i → A j ⊆ Y → Y ⊆ O j → i=j
      (sepOnly=true → sep) → ∀ X ⊆ Finset.range r,
        let I := (List.ofFn (fun i => bits r (Z i))).flatten ++
          (List.ofFn (fun i => bits r (O i))).flatten ++ bits r X ++ [false,true]
        (D.eval I = false ↔ fit r b A O) ∧ (fit r b A O →
          ∀ i, A i ⊆ X → X ⊆ O i → ∀ j, (D.wires I).getD (out j) false = decide (i=j))
let solves := fun (n k : Nat) (S : PEqualNP.CircuitLowerBounds.Circuit) =>
  valid (n*n) S ∧ PEqualNP.NotBracket.notCount S=0 ∧ ∀ E ⊆ Finset.range (n*n),
    S.eval (bits (n*n) E ++ [false,true]) = decide (clq n k E)
∀ (n b : Nat),
  let K := 2^b
  let r := 2+K+(K+1)*n
  let m := K+(K+1)*n
  ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), serve m r b true D out →
    ∃ S : PEqualNP.CircuitLowerBounds.Circuit, solves n (K+1) S ∧ S.size ≤ D.size-PEqualNP.NotBracket.notCount D+b) := by
  have H := fromBoxes (fun n b E _ => ⟨boxBound (2^b) n E, boxesSep, boxFit n b E⟩)
  dsimp only
  unfold serve valid fit solves bits clq adj R M at H
  dsimp only at H
  simp only [canonicalTruth,canonicalDiff] at H ⊢
  exact H
