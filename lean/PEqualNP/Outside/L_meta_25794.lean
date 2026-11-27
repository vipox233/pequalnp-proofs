import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.ZMod.Basic
import PEqualNP.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

namespace PEqualNP.Outside.L_meta_25794

namespace AffineLabels

theorem squareFromLabels {n m : Nat} {L : Type} [AddCommMonoid L] [DecidableEq L]
    (cancel : ∀ l : L, l + l = 0) (R : Fin n → L) (K : Fin m → L)
    (ri : Function.Injective R) (ci : Function.Injective K)
    (G : Fin n → Fin m → Bool) (F : L → Bool) (rep : ∀ i j, G i j = F (R i + K j)) :
    ∃ (q : Nat) (row : Fin q → Fin n) (col : Fin q → Fin m),
      Function.Injective row ∧ Function.Injective col ∧
      (∀ i j, G (row i) (col j) = G (row j) (col i)) ∧
      (∀ i j, G (row i) (col i) = G (row j) (col j)) ∧
      n + m = q + (Finset.univ.image R ∪ Finset.univ.image K).card := by
  classical
  let A := Finset.univ.image R
  let B := Finset.univ.image K
  let both := A ∩ B
  have rchoice (v : ↥both) : ∃ i, R i = v.val := by
    obtain ⟨i,_,h⟩ := Finset.mem_image.mp (Finset.mem_inter.mp v.property).1
    exact ⟨i,h⟩
  have cchoice (v : ↥both) : ∃ j, K j = v.val := by
    obtain ⟨j,_,h⟩ := Finset.mem_image.mp (Finset.mem_inter.mp v.property).2
    exact ⟨j,h⟩
  choose r hr using rchoice
  choose c hc using cchoice
  let e := (Fintype.equivFin ↥both).symm
  refine ⟨_,fun i => r (e i),fun i => c (e i),?_,?_,?_,?_,?_⟩
  · intro i j h
    apply e.injective
    exact Subtype.ext ((hr _).symm.trans ((congrArg R h).trans (hr _)))
  · intro i j h
    apply e.injective
    exact Subtype.ext ((hc _).symm.trans ((congrArg K h).trans (hc _)))
  · intro i j
    rw [rep,rep,hr,hc,hr,hc,add_comm]
  · intro i j
    rw [rep,rep,hr,hc,hr,hc,cancel,cancel]
  · have ar : A.card=n := by simp [A,Finset.card_image_of_injective _ ri]
    have br : B.card=m := by simp [B,Finset.card_image_of_injective _ ci]
    have eq := Finset.card_union_add_card_inter A B
    change n + m = Fintype.card ↥both + (A∪B).card
    simp only [Fintype.card_coe]
    change n + m = (A∩B).card + (A∪B).card
    omega
end AffineLabels

namespace ReverseWireCount
variable {L : Type*} [AddMonoid L] [DecidableEq L]

def tally (bank : Finset L) (xs : List L) : Nat :=
  xs.countP (fun w => decide (w ≠ 0)) + (bank ∪ xs.toFinset).card

theorem head (bank : Finset L) (x : L) (xs : List L) :
    tally bank (x :: xs) = (if x = 0 then 0 else 1) + tally (insert x bank) xs := by
  have sets : bank ∪ (x :: xs).toFinset = insert x bank ∪ xs.toFinset := by
    ext w
    simp
  by_cases h : x=0 <;> simp [tally,sets,h,List.countP_cons] <;> omega

theorem bankMono {A B : Finset L} (h : A ⊆ B) (xs : List L) : tally A xs ≤ tally B xs :=
  Nat.add_le_add_left (Finset.card_le_card (Finset.union_subset_union_left h)) _

theorem bankOne (A : Finset L) (v : L) (xs : List L) : tally (insert v A) xs ≤ tally A xs + 1 := by
  have eq : insert v A ∪ xs.toFinset = insert v (A ∪ xs.toFinset) := by ext; simp
  have h := Finset.card_insert_le v (A ∪ xs.toFinset)
  simp only [tally,eq]
  omega

theorem send (v : L) (xs : List L) (i : Nat) (A : Finset L) (hz : (0:L)∈A) (hv : v∈A) :
    tally A (xs.modify i (fun x => x+v)) ≤ tally A xs + 1 := by
  induction xs generalizing i A with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons,head]
      by_cases hx : x=0
      · subst x
        simp [hv,hz]
        split <;> omega
      · have h := (bankMono (B := insert (x+v) (insert x A)) (A := insert (x+v) A)
            (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) xs).trans (bankOne (insert x A) _ xs)
        simp only [if_neg hx]
        split <;> omega
    | succ i =>
      simp only [List.modify_succ_cons,head]
      have h := ih i (insert x A) (Finset.mem_insert_of_mem hz) (Finset.mem_insert_of_mem hv)
      omega

private theorem modifySame (xs : List L) (i : Nat) : xs.modify i (fun x => x) = xs := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih => cases i <;> simp [ih]

theorem binaryStep (v : L) (xs : List L) (i j : Nat) (A : Finset L) (hz : (0:L) ∈ A) :
    tally A ((xs.modify i (·+v)).modify j (·+v)) ≤ tally A (v::xs) + 1 := by
  by_cases h : v=0
  · subst v
    simp [head,hz,modifySame]
  · let B := insert v A
    have h0 : (0:L) ∈ B := Finset.mem_insert_of_mem hz
    have hv : v∈B := Finset.mem_insert_self _ _
    have one := send v xs i B h0 hv
    have two := send v (xs.modify i (·+v)) j B h0 hv
    have incl := bankMono (Finset.subset_insert v A) ((xs.modify i (·+v)).modify j (·+v))
    change tally A _ ≤ tally B _ at incl
    rw [head,if_neg h]
    change tally A _ ≤ 1 + tally B xs + 1
    omega

theorem singleStep (v : L) (xs : List L) (i : Nat) (A : Finset L) (hz : (0:L) ∈ A) :
    tally A (xs.modify i (·+v)) ≤ tally A (v::xs) := by
  by_cases h : v=0
  · subst v
    simp [head,hz,modifySame]
  · let B := insert v A
    have keep : tally A (xs.modify i (·+v)) ≤ tally B (xs.modify i (·+v)) :=
      bankMono (Finset.subset_insert v A) _
    have move := send v xs i B (Finset.mem_insert_of_mem hz) (Finset.mem_insert_self _ _)
    rw [head,if_neg h]
    change _ ≤ 1 + tally B xs
    omega

theorem sendFresh (v : L) (xs : List L) (i : Nat) (A : Finset L) (hz : (0:L) ∈ A) :
    tally A (xs.modify i (·+v)) ≤ tally A xs + 2 := by
  let B := insert v A
  have keep : tally A (xs.modify i (·+v)) ≤ tally B (xs.modify i (·+v)) :=
    bankMono (Finset.subset_insert v A) _
  have move := send v xs i B (Finset.mem_insert_of_mem hz) (Finset.mem_insert_self _ _)
  have budget : tally B xs ≤ tally A xs + 1 := bankOne A v xs
  omega

theorem nonlinearStep (v u w : L) (xs : List L) (i j : Nat) (A : Finset L) (hz : (0:L) ∈ A) :
    tally A (v :: (xs.modify i (·+u)).modify j (·+w)) ≤ tally A (v::xs) + 4 := by
  let B := insert v A
  have h0 : (0:L) ∈ B := Finset.mem_insert_of_mem hz
  have one := sendFresh u xs i B h0
  have two := sendFresh w (xs.modify i (·+u)) j B h0
  rw [head,head]
  change _ + tally B _ ≤ _ + tally B xs + 4
  omega
end ReverseWireCount

namespace ReverseWireCount
variable {L : Type*} [AddMonoid L] [DecidableEq L]

theorem mass (xs : List L) (hn : xs.Nodup) :
    xs.countP (fun w => decide (w ≠ 0)) + (if (0:L) ∈ xs then 1 else 0) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    have count := ih hn'.2
    by_cases h : x=0
    · subst x
      have no := hn'.1
      simp [List.countP_cons,no] at count ⊢
      omega
    · by_cases z : (0:L) ∈ xs <;> simp [List.countP_cons,h,z,Ne.symm h] at count ⊢ <;> omega

theorem rawCharge (R K saved : List L) (final : L) (hr : R.Nodup) (hk : K.Nodup)
    (savedNonzero : ∀ s ∈ saved, s ≠ 0)
    (extra : (0:L)∈R → (0:L)∈K → final ∈ saved ∧ final ∉ R ∧ final ∉ K) :
    R.length + K.length + (R.toFinset ∪ K.toFinset).card + saved.length ≤
      tally ({0} : Finset L) (R ++ K ++ saved) + 1 := by
  classical
  let A := R.toFinset ∪ K.toFinset
  let B := ({0} : Finset L) ∪ (R ++ K ++ saved).toFinset
  have incl : A ⊆ B := by intro i hi; simp [A] at hi; simp [B]; tauto
  have card := Finset.card_le_card incl
  have all : saved.countP (fun w => decide (w ≠ 0)) = saved.length := by
    rw [List.countP_eq_length_filter]
    rw [List.filter_eq_self.mpr (fun a h => by simpa using savedNonzero a h)]
  have r := mass R hr
  have k := mass K hk
  change R.length + K.length + A.card + saved.length ≤ (R ++ K ++ saved).countP _ + B.card + 1
  rw [List.countP_append,List.countP_append,all]
  by_cases zr : (0:L)∈R <;> by_cases zk : (0:L)∈K
  · obtain ⟨inS,outR,outK⟩ := extra zr zk
    have mem : final ∈ B := by simp [B,inS]
    have out : final ∉ A := by simp [A,outR,outK]
    have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨incl,fun eq => out (eq ▸ mem)⟩)
    simp only [if_pos zr,if_pos zk] at r k
    omega
  · simp only [if_pos zr] at r
    simp only [if_neg zk] at k
    omega
  · simp only [if_neg zr] at r
    simp only [if_pos zk] at k
    omega
  · simp only [if_neg zr] at r
    simp only [if_neg zk] at k
    omega
end ReverseWireCount

namespace BackwardAffine
abbrev Label := Nat → ZMod 2

def atom (j : Nat) : Label := fun i => if i=j then 1 else 0
def pick (b : Bool) (v : Label) : Label := if b then v else 0

private theorem cancelZ (z : ZMod 2) : z+z=0 := by revert z; decide
theorem cancel (v : Label) : v+v=0 := by funext i; exact cancelZ _

def score : List Label → List Bool → Label
  | a::xs,b::bs => pick b a + score xs bs
  | _, _ => 0

theorem scoreMove (xs : List Label) (bs : List Bool) (len : xs.length=bs.length) (i : Nat) (v : Label) :
    score (xs.modify i (·+v)) bs = score xs bs + pick (bs.getD i false) v := by
  induction xs generalizing bs i with
  | nil =>
    have h : bs=[] := List.length_eq_zero_iff.mp len.symm
    subst bs
    simp [score,pick,List.getD_eq_getElem?_getD]
  | cons x xs ih =>
    cases bs with
    | nil => simp at len
    | cons b bs =>
      have hl : xs.length=bs.length := by simpa using len
      cases i with
      | zero =>
        cases b <;> simp [score,pick,List.getD_eq_getElem?_getD] <;> abel
      | succ i =>
        simp only [List.modify_succ_cons,score,ih bs hl]
        rw [show (b::bs).getD (i+1) false = bs.getD i false by rfl]
        abel

theorem scoreAppend (xs : List Label) (bs : List Bool) (h : xs.length=bs.length)
    (ys : List Label) (cs : List Bool) : score (xs++ys) (bs++cs) = score xs bs + score ys cs := by
  induction xs generalizing bs with
  | nil =>
    have h : bs=[] := List.length_eq_zero_iff.mp h.symm
    subst bs
    simp [score]
  | cons x xs ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.cons_append,score]
      rw [ih bs (by simpa using h)]
      abel

theorem pickAdd (a b : Bool) (v : Label) : pick a v + pick b v = pick (xor a b) v := by
  cases a <;> cases b <;> simp [pick,cancel]

def diff (xs : List Label) (w z : List Bool) : Label := score xs w + score xs z

theorem diffMove (xs : List Label) (w z : List Bool) (wx : xs.length=w.length)
    (zx : xs.length=z.length) (i : Nat) (v : Label) :
    diff (xs.modify i (·+v)) w z = diff xs w z + pick (xor (w.getD i false) (z.getD i false)) v := by
  simp only [diff,scoreMove _ _ wx,scoreMove _ _ zx,← pickAdd]
  abel

theorem diffAppendBit (xs : List Label) (w z : List Bool) (wx : xs.length=w.length)
    (zx : xs.length=z.length) (v : Label) (a b : Bool) :
    diff (xs++[v]) (w++[a]) (z++[b]) = diff xs w z + pick (xor a b) v := by
  simp only [diff,scoreAppend _ _ wx,scoreAppend _ _ zx,score,add_zero,← pickAdd]
  abel
end BackwardAffine

namespace BackwardAffine

def bounded (cut : Nat) (v : Label) := ∀ i, cut ≤ i → v i = 0
def bankBound (cut : Nat) (xs : List Label) := ∀ v ∈ xs, bounded cut v

theorem atomBound (i cut : Nat) (h : i<cut) : bounded cut (atom i) := by
  intro j hj
  simp [atom, show j ≠ i by omega]

theorem zeroBound (cut : Nat) : bounded cut 0 := fun _ _ => rfl

theorem addBound {cut : Nat} {a b : Label} (ha : bounded cut a) (hb : bounded cut b) : bounded cut (a+b) := by
  intro j hj
  change a j + b j = 0
  rw [ha j hj,hb j hj,add_zero]

theorem looser {a b : Nat} {xs : List Label} (ha : bankBound a xs) (hle : a≤b) : bankBound b xs :=
  fun v h i hi => ha v h i (hle.trans hi)

theorem moveBound (cut : Nat) (xs : List Label) (i : Nat) (v : Label)
    (h : bankBound cut xs) (hv : bounded cut v) : bankBound cut (xs.modify i (·+v)) := by
  induction xs generalizing i with
  | nil => simp [bankBound]
  | cons x xs ih =>
    have tail : bankBound cut xs := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hx := h x List.mem_cons_self
    cases i with
    | zero =>
      simpa [bankBound] using
        (show bankBound cut ((x+v)::xs) from fun a ha => (List.mem_cons.mp ha).elim
          (fun he => he ▸ addBound hx hv) (fun he => tail a he))
    | succ i =>
      intro a ha
      simp only [List.modify_succ_cons,List.mem_cons] at ha
      exact ha.elim (fun he => he ▸ hx) (fun he => ih i tail a he)

theorem scoreBound {cut : Nat} (xs : List Label) (w : List Bool) (h : bankBound cut xs) :
    bounded cut (score xs w) := by
  induction xs generalizing w with
  | nil => cases w <;> exact zeroBound _
  | cons x xs ih =>
    cases w with
    | nil => exact zeroBound _
    | cons b bs =>
      have hx := h x List.mem_cons_self
      have tail : bankBound cut xs := fun a ha => h a (List.mem_cons_of_mem _ ha)
      change bounded cut (pick b x + score xs bs)
      apply addBound _ (ih bs tail)
      cases b
      · exact zeroBound _
      · exact hx

theorem diffBound {cut : Nat} (xs : List Label) (w z : List Bool) (h : bankBound cut xs) :
    bounded cut (diff xs w z) := addBound (scoreBound _ _ h) (scoreBound _ _ h)

theorem firstLabel (v : Label) (hv : bounded 1 v) (ne : v ≠ 0) : v = atom 0 := by
  have bit : v 0 ≠ 0 := by
    intro h
    apply ne
    funext i
    cases i with
    | zero => exact h
    | succ i => exact hv (i+1) (by omega)
  have one : v 0 = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z=1) (v 0) bit
  funext i
  cases i with
  | zero => simpa [atom] using one
  | succ i => simpa [atom] using hv (i+1) (by omega)

theorem freshPair {v : Label} {k : Nat} (hk : 0 < k) (bound : bounded k v) (a b f : Bool)
    (eq : v + pick a (atom k) + pick b (atom (k+1)) = pick f (atom 0)) :
    a = false ∧ b = false ∧ v = pick f (atom 0) := by
  have h₁ := congrFun eq k
  have h₂ := congrFun eq (k+1)
  have neq : k≠0 := by omega
  cases a <;> cases b <;> cases f <;>
    simp [pick,atom,Pi.add_apply,bound k (by omega),bound (k+1) (by omega),neq] at h₁ h₂ eq ⊢ <;>
    assumption
end BackwardAffine

namespace BackwardAffine
open PEqualNP.CircuitLowerBounds

inductive Mode where
  | silent
  | one (i : Nat)
  | two (i j : Nat)
  | nonlinear (i j : Nat)

def read (w : List Bool) (i : Nat) := w.getD i false
def output (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map (read w))
def difbit (w z : List Bool) (i : Nat) := xor (read w i) (read z i)
def isBinary (g : Gate) := g.inputs.length == 2
def isNonlin (g : Gate) := isBinary g && xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
    (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def mode (g : Gate) : Mode :=
  match g.inputs with
  | [i] => if g.op.eval [false] == g.op.eval [true] then .silent else .one i
  | [i,j] =>
    if isNonlin g then .nonlinear i j else
    match xor (g.op.eval [false,false]) (g.op.eval [true,false]),
          xor (g.op.eval [false,false]) (g.op.eval [false,true]) with
    | false,false => .silent
    | true,false => .one i
    | false,true => .one j
    | true,true => .two i j
  | _ => .silent

private theorem unaryTruth (F : Bool → Bool) (a b : Bool) :
    xor (F a) (F b) = (if F false == F true then false else xor a b) := by
  revert F a b
  decide

private theorem binaryTruth (F : Bool → Bool → Bool) (a b c d : Bool)
    (lin : xor (xor (F false false) (F false true)) (xor (F true false) (F true true)) = false) :
    xor (F a b) (F c d) =
      xor ((xor (F false false) (F true false)) && xor a c)
          ((xor (F false false) (F false true)) && xor b d) := by
  revert F a b c d
  decide

theorem modeSpec (g : Gate) (hg : g.inputs.length ≤ 2) (w z : List Bool) :
    match mode g with
    | .silent => xor (output g w) (output g z) = false
    | .one i => xor (output g w) (output g z) = difbit w z i
    | .two i j => isBinary g = true ∧ xor (output g w) (output g z) = xor (difbit w z i) (difbit w z j)
    | .nonlinear i j => isNonlin g = true ∧ isBinary g = true ∧
        (difbit w z i = false → difbit w z j = false → output g w = output g z) := by
  rcases g with ⟨op,args⟩
  cases args with
  | nil => simp [mode,output]
  | cons i tail =>
    cases tail with
    | nil =>
      have h := unaryTruth (fun a => op.eval [a]) (read w i) (read z i)
      by_cases e : (op.eval [false] == op.eval [true]) = true <;>
        simpa [mode,output,difbit,e] using h
    | cons j rest =>
      have nil : rest=[] := List.length_eq_zero_iff.mp (by change rest.length+1+1 ≤ 2 at hg; omega)
      subst rest
      let f (a b : Bool) := op.eval [a,b]
      by_cases nl : xor (xor (f false false) (f false true)) (xor (f true false) (f true true)) = true
      · have h : isNonlin (⟨op,[i,j]⟩ : Gate) = true := by simpa [isNonlin,isBinary,f] using nl
        simp only [mode,h,if_true,isBinary,List.length_cons,List.length_nil,beq_self_eq_true,true_and]
        intro x y
        have ex : read w i = read z i := (by decide : ∀ a b : Bool, xor a b=false → a=b) _ _ x
        have ey : read w j = read z j := (by decide : ∀ a b : Bool, xor a b=false → a=b) _ _ y
        simp [output,ex,ey]
      · have h : isNonlin (⟨op,[i,j]⟩ : Gate) = false := by simpa [isNonlin,isBinary,f] using (Bool.eq_false_iff.mpr nl)
        have spec := binaryTruth f (read w i) (read w j) (read z i) (read z j) (Bool.eq_false_iff.mpr nl)
        simp only [mode,h,Bool.false_eq_true,ite_false]
        cases a : xor (f false false) (f true false) <;> cases b : xor (f false false) (f false true) <;>
          first | (dsimp only [f] at a b; rw [a,b]; rw [a,b] at spec; simpa [output,difbit,isBinary,f] using spec) | (rw [a,b] at spec; simpa [output,difbit,isBinary,f] using spec)
end BackwardAffine

namespace BackwardAffine
open PEqualNP.CircuitLowerBounds
noncomputable section
open Classical

noncomputable def evolve (m : Mode) (v : Label) (xs saved : List Label) : List Label × List Label :=
  match m with
  | .silent => (xs,saved)
  | .one i => (xs.modify i (·+v),saved)
  | .two i j => ((xs.modify i (·+v)).modify j (·+v),saved)
  | .nonlinear i j =>
    if v=0 then (xs,saved) else
    let k := 1+2*saved.length
    ((xs.modify i (·+atom k)).modify j (·+atom (k+1)),v::saved)

theorem evolveLength (m : Mode) (v : Label) (xs saved : List Label) :
    (evolve m v xs saved).1.length = xs.length := by
  classical
  cases m <;> simp [evolve] <;> split <;> simp

private theorem pickZero (b : Bool) : pick b (0 : Label) = 0 := by cases b <;> rfl

private theorem diffMoves (xs : List Label) (w z : List Bool) (wx : xs.length=w.length)
    (zx : xs.length=z.length) (i j : Nat) (a b : Label) :
    diff ((xs.modify i (·+a)).modify j (·+b)) w z =
      diff xs w z + pick (difbit w z i) a + pick (difbit w z j) b := by
  rw [diffMove (xs.modify i (·+a)) w z (by simpa using wx) (by simpa using zx), diffMove xs w z wx zx]
  rfl

theorem retreatDiff (g : Gate) (hg : g.inputs.length ≤ 2) (v : Label) (xs saved : List Label)
    (low : bankBound (1+2*saved.length) xs)
    (w z : List Bool) (wx : xs.length=w.length) (zx : xs.length=z.length) (bit : Bool)
    (eq : diff (evolve (mode g) v xs saved).1 w z = pick bit (atom 0)) :
    diff (xs++[v]) (w++[output g w]) (z++[output g z]) = pick bit (atom 0) := by
  classical
  rw [diffAppendBit _ _ _ wx zx]
  have spec := modeSpec g hg w z
  cases m : mode g with
  | silent =>
    simp only [m] at spec
    rw [spec]
    simpa [m,evolve,pick] using eq
  | one i =>
    simp only [m] at spec
    rw [spec]
    simpa only [m,evolve,diffMove _ _ _ wx zx,difbit,read] using eq
  | two i j =>
    simp only [m] at spec
    rw [spec.2,← pickAdd]
    change diff xs w z + (pick _ v + pick _ v) = _
    rw [← add_assoc]
    simpa only [m,evolve,diffMoves xs w z wx zx] using eq
  | nonlinear i j =>
    simp only [m] at spec
    by_cases dead : v=0
    · subst v
      simpa [m,evolve,pickZero] using eq
    · let k := 1+2*saved.length
      have d : diff xs w z + pick (difbit w z i) (atom k) + pick (difbit w z j) (atom (k+1)) =
          pick bit (atom 0) := by
        simpa only [m,evolve,if_neg dead,diffMoves xs w z wx zx,k] using eq
      obtain ⟨hi,hj,rest⟩ := freshPair (k := k) (by dsimp [k]; omega) (diffBound xs w z low) _ _ _ d
      rw [spec.2.2 hi hj,Bool.xor_self]
      simpa [pick] using rest

end
end BackwardAffine

namespace BackwardAffine
open PEqualNP.CircuitLowerBounds ReverseWireCount
noncomputable section
open Classical

def reserve (s : List Label) : Finset Label := insert 0 s.toFinset
def accounts (s xs : List Label) : Nat := s.length + tally (reserve s) xs

theorem rotateLast (s xs : List Label) (v : Label) : accounts s (xs++[v]) = accounts s (v::xs) := by
  have sets : (xs++[v]).toFinset=(v::xs).toFinset := by ext; simp
  simp only [accounts,tally,sets,List.countP_append,List.countP_cons,List.countP_nil]
  split <;> omega

theorem saveLabel (s xs : List Label) (v : Label) (hv : v≠0) :
    accounts (v::s) xs = accounts s (v::xs) := by
  have eq : reserve (v::s)=insert v (reserve s) := by ext; simp [reserve]; tauto
  simp [accounts,head,hv,eq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem forget (s xs : List Label) (v : Label) : accounts s xs ≤ accounts s (v::xs) := by
  have h := bankMono (Finset.subset_insert v (reserve s)) xs
  simp only [accounts,head]
  omega

structure Shape (xs s : List Label) : Prop where
  low : bankBound (1+2*s.length) xs
  kept : ∀ v∈s, v ≠ 0
  unit_kept : s ≠ [] → atom 0 ∈ s

theorem evolveShape {xs s : List Label} {v : Label} (st : Shape (xs++[v]) s) (m : Mode) :
    Shape (evolve m v xs s).1 (evolve m v xs s).2 := by
  classical
  have low : bankBound (1+2*s.length) xs := fun a ha => st.low a (List.mem_append_left _ ha)
  have last : bounded (1+2*s.length) v := st.low _ (by simp)
  cases m with
  | silent => exact ⟨low,st.kept,st.unit_kept⟩
  | one i => exact ⟨moveBound _ _ _ _ low last,st.kept,st.unit_kept⟩
  | two i j => exact ⟨moveBound _ _ _ _ (moveBound _ _ _ _ low last) last,st.kept,st.unit_kept⟩
  | nonlinear i j =>
    by_cases dead : v=0
    · simpa only [evolve,if_pos dead] using (show Shape xs s from ⟨low,st.kept,st.unit_kept⟩)
    · simp only [evolve,if_neg dead]
      constructor
      · have newcap : 1+2*s.length+2=1+2*(v::s).length := by simp; omega
        apply moveBound _ _ _ _ _ (atomBound _ _ (by omega))
        apply moveBound _ _ _ _ _ (atomBound _ _ (by omega))
        exact looser low (by omega)
      · intro a ha
        exact (List.mem_cons.mp ha).elim (fun eq => eq ▸ dead) (st.kept a)
      · intro _
        by_cases nil : s=[]
        · have cap : bounded 1 v := by simpa [nil] using last
          simp [firstLabel v cap dead]
        · exact List.mem_cons_of_mem _ (st.unit_kept nil)

theorem evolveCost (g : Gate) (hg : g.inputs.length≤2) (xs s : List Label) (v : Label) :
    let next := evolve (mode g) v xs s
    s.length ≤ next.2.length ∧ next.2.length ≤ s.length + (isNonlin g).toNat ∧
    accounts next.2 next.1 ≤ accounts s (xs++[v]) + (isBinary g).toNat +
      3*(next.2.length-s.length) := by
  classical
  rw [rotateLast]
  have hz : (0 : Label) ∈ reserve s := Finset.mem_insert_self _ _
  have spec := modeSpec g hg [] []
  cases m : mode g with
  | silent =>
    simp [evolve]
    have h := forget s xs v
    omega
  | one i =>
    simp [evolve]
    have h := singleStep v xs i (reserve s) hz
    simp only [accounts]
    omega
  | two i j =>
    simp only [m] at spec
    simp [evolve,spec.1]
    have h := binaryStep v xs i j (reserve s) hz
    simp only [accounts]
    omega
  | nonlinear i j =>
    simp only [m] at spec
    by_cases dead : v=0
    · simp [evolve,dead,spec.1,spec.2.1]
      have h := forget s xs 0
      omega
    · simp only [evolve,if_neg dead,List.length_cons,spec.1,spec.2.1,Bool.toNat_true]
      refine ⟨by omega,by omega,?_⟩
      rw [saveLabel _ _ _ dead]
      have h := nonlinearStep v (atom (1+2*s.length)) (atom (1+2*s.length+1)) xs i j (reserve s) hz
      simp only [accounts]
      omega
end
end BackwardAffine

namespace BackwardAffine
open PEqualNP.CircuitLowerBounds ReverseWireCount
noncomputable section
open Classical

def evaluate (gates : List Gate) (o : Nat) (w : List Bool) : Bool :=
  (gates.foldl (fun bits g => bits ++ [output g bits]) w).getD o false

theorem blankScore (a : Nat) (w : List Bool) : score (List.replicate a 0) w = 0 := by
  induction a generalizing w with
  | zero => cases w <;> rfl
  | succ a ih => cases w with
    | nil => rfl
    | cons b bs => cases b <;> simp [List.replicate_succ,score,pick,ih]

theorem finalBit (a b : Bool) (h : pick a (atom 0) = pick b (atom 0)) : a=b := by
  have q := congrFun h 0
  cases a <;> cases b <;> simp [pick,atom] at q ⊢

structure Certificate (width : Nat) (gates : List Gate) (o : Nat) where
  xs : List Label
  saved : List Label
  length_eq : xs.length=width
  shape : Shape xs saved
  uses : saved.length ≤ gates.countP isNonlin
  cost : accounts saved xs ≤ gates.countP isBinary + 3*saved.length + 3
  value : ∀ (w z : List Bool), width=w.length → width=z.length → ∀ bit,
    diff xs w z = pick bit (atom 0) → xor (evaluate gates o w) (evaluate gates o z) = bit

private theorem initial (width o : Nat) : Nonempty (Certificate width [] o) := by
  let raw := List.replicate width (0 : Label)
  let xs := raw.modify o (·+atom 0)
  have hr : raw.length=width := List.length_replicate
  have low : bankBound 1 raw := by
    intro a ha
    exact (List.eq_of_mem_replicate ha) ▸ zeroBound _
  have cost : tally (reserve []) raw = 1 := by
    clear low
    induction width with
    | zero => simp [raw,tally,reserve]
    | succ n ih => simpa [raw,List.replicate_succ,head,reserve] using ih
  refine ⟨⟨xs,[],by simpa [xs] using hr,⟨?_,by simp,by simp⟩,by simp,?_,?_⟩⟩
  · exact moveBound 1 raw o _ low (atomBound 0 1 (by decide))
  · have h := sendFresh (atom 0) raw o (reserve []) (Finset.mem_insert_self _ _)
    simp only [accounts,xs,List.length_nil,Nat.zero_add,List.countP_nil,Nat.mul_zero]
    omega
  · intro w z wx zx bit eq
    apply finalBit
    change diff (raw.modify o (·+atom 0)) w z = _ at eq
    rw [diffMove raw w z (hr.trans wx) (hr.trans zx)] at eq
    simpa [raw,diff,blankScore,evaluate] using eq

theorem certify (gs : List Gate) (width o : Nat) (fan : ∀ g∈gs, g.inputs.length ≤ 2) :
    Nonempty (Certificate width gs o) := by
  induction gs generalizing width with
  | nil => exact initial width o
  | cons g gs ih =>
    obtain ⟨tail⟩ := ih (width+1) (fun k hk => fan k (List.mem_cons_of_mem _ hk))
    have hg := fan g List.mem_cons_self
    have nonempty : tail.xs ≠ [] := by intro h; have := tail.length_eq; rw [h] at this; simp at this
    let xs := tail.xs.dropLast
    let v := tail.xs.getLast nonempty
    have last : xs++[v] = tail.xs := List.dropLast_concat_getLast nonempty
    have wide : xs.length=width := by have := tail.length_eq; rw [← last] at this; simpa using this
    let next := evolve (mode g) v xs tail.saved
    have shape : Shape (xs++[v]) tail.saved := last ▸ tail.shape
    have δ := evolveCost g hg xs tail.saved v
    change tail.saved.length ≤ next.2.length ∧ next.2.length ≤ _ ∧ accounts next.2 next.1 ≤ _ at δ
    rcases δ with ⟨mono,extra,cost⟩
    rw [last] at cost
    change accounts next.2 next.1 ≤ accounts tail.saved tail.xs + (isBinary g).toNat + 3*(next.2.length-tail.saved.length) at cost
    refine ⟨⟨next.1,next.2,(evolveLength _ _ _ _).trans wide,evolveShape shape _,?_,?_,?_⟩⟩
    · have used := tail.uses
      simp only [List.countP_cons]
      cases h : isNonlin g <;> simp [h] at extra ⊢ <;> omega
    · have lower := tail.cost
      simp only [List.countP_cons]
      cases h : isBinary g <;> simp [h] at cost ⊢ <;> omega
    · intro w z wx zx bit eq
      apply tail.value (w++[output g w]) (z++[output g z]) (by simp [wx]) (by simp [zx]) bit
      rw [← last]
      exact retreatDiff g hg v xs tail.saved (fun a ha => shape.low a (List.mem_append_left _ ha)) w z (wide.trans wx) (wide.trans zx) bit eq
end
end BackwardAffine

namespace BackwardAffine
open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem scoreBlankBits (xs : List Label) (n : Nat) : score xs (List.replicate n false) = 0 := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih => cases n <;> simp [List.replicate_succ,score,pick,ih]

theorem oneScore {n : Nat} (f : Fin n → Label) (i : Fin n) :
    score (List.ofFn f) (List.ofFn (fun k : Fin n => decide (k=i))) = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [List.ofFn_succ,List.ofFn_succ]
      simp [score,pick,scoreBlankBits]
    · rw [List.ofFn_succ,List.ofFn_succ]
      simpa [score,pick,Ne.symm (Fin.succ_ne_zero j)] using ih (fun k => f k.succ) j

theorem divide {n m : Nat} (xs : List Label) (hw : xs.length=n+m) :
    ∃ (R : Fin n → Label) (K : Fin m → Label), xs=List.ofFn R ++ List.ofFn K := by
  let a := xs.take n
  let b := xs.drop n
  have ha : a.length=n := by simp [a,hw]
  have hb : b.length=m := by simp [b,hw]
  let r (i : Fin n) := a[i.val]'(by rw [ha]; exact i.isLt)
  let c (j : Fin m) := b[j.val]'(by rw [hb]; exact j.isLt)
  have h₁ : List.ofFn r = a := by
    apply List.ext_getElem <;> simp [ha,r]
  have h₂ : List.ofFn c = b := by
    apply List.ext_getElem <;> simp [hb,c]
  exact ⟨r,c,by rw [h₁,h₂]; exact (List.take_append_drop _ _).symm⟩

theorem wirePair {n m : Nat} (R : Fin n → Label) (K : Fin m → Label) (i : Fin n) (j : Fin m) :
    score (List.ofFn R ++ List.ofFn K) (oneEach i j) = R i + K j := by
  unfold oneEach
  rw [scoreAppend _ _ (by simp),oneScore,oneScore]

theorem accountsAsTally (s xs : List Label) (nonzero : ∀ v∈s, v ≠ 0) :
    accounts s xs = ReverseWireCount.tally ({0} : Finset Label) (xs++s) := by
  classical
  have mass : s.countP (fun w => decide (w ≠ 0)) = s.length := by
    rw [List.countP_eq_length_filter,List.filter_eq_self.mpr (fun a ha => by simpa using nonzero a ha)]
  have eq : reserve s ∪ xs.toFinset = ({0}:Finset Label) ∪ (xs++s).toFinset := by
    ext; simp [reserve]; tauto
  simp only [accounts,ReverseWireCount.tally,List.countP_append,mass,eq]
  omega
end BackwardAffine

namespace BackwardAffine
open PEqualNP.CircuitLowerBounds PEqualNP.Represents AffineLabels ReverseWireCount
open Classical

private theorem xorSolve (a b f : Bool) (h : xor a b = f) : a = xor f b := by
  revert a b f
  decide

private theorem fourCancel (a b c : Label) : (a+c)+(b+c)=a+b := by
  calc
    _ = (a+b)+(c+c) := by abel
    _ = _ := by rw [cancel,add_zero]

private theorem flipRow {n m : Nat} (R : Fin n → Label) (K : Fin m → Label)
    (G : Fin n → Fin m → Bool)
    (separate : ∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, G i y ≠ xor f (G j y))
    (law : ∀ i i' j j' f, (R i + K j) + (R i' + K j') = pick f (atom 0) →
      xor (G i j) (G i' j') = f)
    {i i' : Fin n} {f : Bool} (same : R i + R i' = pick f (atom 0)) : i=i' := by
  by_contra ne
  obtain ⟨y,bad⟩ := separate i i' ne f
  exact bad (xorSolve _ _ _ (law i i' y y f ((fourCancel _ _ _).trans same)))

private theorem factor {n m : Nat} (R : Fin n → Label) (K : Fin m → Label)
    (G : Fin n → Fin m → Bool)
    (law : ∀ i i' j j' f, (R i + K j) + (R i' + K j') = pick f (atom 0) →
      xor (G i j) (G i' j') = f) :
    ∃ F : Label → Bool, ∀ i j, G i j = F (R i+K j) := by
  classical
  let F (v : Label) : Bool := decide (∃ i j, R i+K j=v ∧ G i j=true)
  refine ⟨F,fun i j => ?_⟩
  cases h : G i j with
  | true => exact (decide_eq_true (p := ∃ a b, R a+K b=R i+K j ∧ G a b=true) ⟨i,j,rfl,h⟩).symm
  | false =>
    apply Eq.symm
    apply decide_eq_false
    rintro ⟨a,b,e,one⟩
    have z := law a i b j false (by rw [e,cancel]; rfl)
    simp [one,h] at z

private theorem noFinal {n : Nat} (R : Fin n → Label)
    (modInj : ∀ {i j} {f : Bool}, R i + R j = pick f (atom 0) → i=j)
    (zero : (0:Label)∈List.ofFn R) : atom 0 ∉ List.ofFn R := by
  intro one
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp zero
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp one
  have eq : i=j := modInj (f := true) (by rw [hi,hj,zero_add]; rfl)
  subst j
  have impossible : (0:Label) = atom 0 := hi.symm.trans hj
  have := congrFun impossible 0
  simp [atom] at this

theorem full (n m : Nat) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 2≤n) (_hm : 2≤m)
    (ra : ∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, G i y ≠ xor f (G j y))
    (ca : ∀ i j : Fin m, i ≠ j → ∀ f : Bool, ∃ x, G x i ≠ xor f (G x j))
    (fan : ∀ g∈C.gates, g.inputs.length ≤ 2) (hr : Represents G C) :
    ∃ (q : Nat) (row : Fin q → Fin n) (col : Fin q → Fin m),
      Function.Injective row ∧ Function.Injective col ∧
      (∀ i j, G (row i) (col j) = G (row j) (col i)) ∧
      (∀ i j, G (row i) (col i) = G (row j) (col j)) ∧
      2*(n+m) ≤ C.gates.countP isBinary + 2*C.gates.countP isNonlin + q + 4 := by
  classical
  obtain ⟨cert⟩ := certify C.gates (n+m) C.output fan
  obtain ⟨R,K,codes⟩ := divide cert.xs cert.length_eq
  have law (i i' : Fin n) (j j' : Fin m) (f : Bool)
      (eq : (R i+K j)+(R i'+K j') = pick f (atom 0)) : xor (G i j) (G i' j')=f := by
    rw [← hr i j,← hr i' j']
    apply cert.value (oneEach i j) (oneEach i' j') (by simp [oneEach]) (by simp [oneEach]) f
    rwa [diff,codes,wirePair,wirePair]
  have rowSep := @flipRow n m R K G ra law
  have colSep := @flipRow m n K R (fun j i => G i j) ca (by
    intro j j' i i' f h
    exact law i i' j j' f (by simpa only [add_comm (K j),add_comm (K j')] using h))
  have ri : Function.Injective R := fun i j eq => rowSep (f:=false) (by rw [eq,cancel]; rfl)
  have ci : Function.Injective K := fun i j eq => colSep (f:=false) (by rw [eq,cancel]; rfl)
  obtain ⟨F,values⟩ := factor R K G law
  obtain ⟨q,row,col,r,c,s,d,size⟩ := squareFromLabels cancel R K ri ci G F values
  refine ⟨q,row,col,r,c,s,d,?_⟩
  have extra (r0 : (0:Label)∈List.ofFn R) (c0 : (0:Label)∈List.ofFn K) :
      atom 0 ∈ cert.saved ∧ atom 0 ∉ List.ofFn R ∧ atom 0 ∉ List.ofFn K := by
    have nr := noFinal R (fun h => rowSep h) r0
    have nc := noFinal K (fun h => colSep h) c0
    refine ⟨cert.shape.unit_kept ?_,nr,nc⟩
    intro empty
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp r0
    obtain ⟨j,ne⟩ : ∃ j : Fin n, j≠i := by
      by_cases h : i.val=0
      · exact ⟨⟨1,by omega⟩,fun eq => by have := congrArg Fin.val eq; simp [h] at this⟩
      · exact ⟨⟨0,by omega⟩,fun eq => h (congrArg Fin.val eq).symm⟩
    have mem : R j ∈ List.ofFn R := List.mem_ofFn.mpr ⟨j,rfl⟩
    have low := cert.shape.low (R j) (codes ▸ List.mem_append_left _ mem)
    have pure := firstLabel (R j) (by simpa [empty] using low)
      (fun z => ne (ri (z.trans hi.symm)))
    exact nr (pure ▸ mem)
  have cap := rawCharge (List.ofFn R) (List.ofFn K) cert.saved (atom 0)
    (List.nodup_ofFn.mpr ri) (List.nodup_ofFn.mpr ci) cert.shape.kept extra
  have images {p : Nat} (r : Fin p → Label) : (List.ofFn r).toFinset = Finset.univ.image r := by
    ext; simp
  rw [images,images,List.length_ofFn,List.length_ofFn,← codes,← accountsAsTally _ _ cert.shape.kept] at cap
  have used := cert.uses
  have budget := cert.cost
  omega
end BackwardAffine

end PEqualNP.Outside.L_meta_25794

open PEqualNP.Outside.L_meta_25794 in
theorem PEqualNP.Outside.L_meta_25794 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ n → 2 ≤ m →
  (∀ i j : Fin n, i ≠ j → ∀ f : Bool, ∃ y, G i y ≠ xor f (G j y)) →
  (∀ i j : Fin m, i ≠ j → ∀ f : Bool, ∃ x, G x i ≠ xor f (G x j)) →
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
  PEqualNP.Represents.Represents G C →
  let b := C.gates.countP (fun g => g.inputs.length == 2)
  let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
  ∃ (q : ℕ) (row : Fin q → Fin n) (col : Fin q → Fin m),
    Function.Injective row ∧ Function.Injective col ∧
    (∀ i j, G (row i) (col j) = G (row j) (col i)) ∧
    (∀ i j, G (row i) (col i) = G (row j) (col j)) ∧
    2*(n+m) ≤ b + 2*t + q + 4) := by
  intro n m G C hn hm ra ca fan _ rep
  exact BackwardAffine.full n m G C hn hm ra ca fan rep
