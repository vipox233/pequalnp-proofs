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
import Mathlib.LinearAlgebra.Pi

namespace PEqualNP.Outside.L_meta_25795

namespace Matching

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

abbrev Mode := Unit ⊕ (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)))

def read (w : List Bool) (i : Nat) := w.getD i false
def output (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map (read w))
def difbit (w z : List Bool) (i : Nat) := xor (read w i) (read z i)
def isBinary (g : Gate) := g.inputs.length == 2
def isNonlin (g : Gate) := isBinary g && xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
    (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def mode (g : Gate) : Mode :=
  match g.inputs with
  | [i] => if g.op.eval [false] == g.op.eval [true] then (Sum.inl ()) else (Sum.inr (Sum.inl i))
  | [i,j] =>
    if isNonlin g then (Sum.inr (Sum.inr (Sum.inr (i,j)))) else
    match xor (g.op.eval [false,false]) (g.op.eval [true,false]),
          xor (g.op.eval [false,false]) (g.op.eval [false,true]) with
    | false,false => (Sum.inl ())
    | true,false => (Sum.inr (Sum.inl i))
    | false,true => (Sum.inr (Sum.inl j))
    | true,true => (Sum.inr (Sum.inr (Sum.inl (i,j))))
  | _ => (Sum.inl ())

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
    | (Sum.inl ()) => xor (output g w) (output g z) = false
    | (Sum.inr (Sum.inl i)) => xor (output g w) (output g z) = difbit w z i
    | (Sum.inr (Sum.inr (Sum.inl (i,j)))) => isBinary g = true ∧ xor (output g w) (output g z) = xor (difbit w z i) (difbit w z j)
    | (Sum.inr (Sum.inr (Sum.inr (i,j)))) => isNonlin g = true ∧ isBinary g = true ∧
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
  | (Sum.inl ()) => (xs,saved)
  | (Sum.inr (Sum.inl i)) => (xs.modify i (·+v),saved)
  | (Sum.inr (Sum.inr (Sum.inl (i,j)))) => ((xs.modify i (·+v)).modify j (·+v),saved)
  | (Sum.inr (Sum.inr (Sum.inr (i,j)))) =>
    if v=0 then (xs,saved) else
    let k := 1+2*saved.length
    ((xs.modify i (·+atom k)).modify j (·+atom (k+1)),v::saved)

theorem evolveLength (m : Mode) (v : Label) (xs saved : List Label) :
    (evolve m v xs saved).1.length = xs.length := by
  classical
  rcases m with ⟨⟩ | (i | (⟨i,j⟩ | ⟨i,j⟩)) <;> simp [evolve] <;> split <;> simp

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
  rcases m : mode g with ⟨⟩ | (i | (⟨i,j⟩ | ⟨i,j⟩))
  ·
    simp only [m] at spec
    rw [spec]
    simpa [m,evolve,pick] using eq
  ·
    simp only [m] at spec
    rw [spec]
    simpa only [m,evolve,diffMove _ _ _ wx zx,difbit,read] using eq
  ·
    simp only [m] at spec
    rw [spec.2,← pickAdd]
    change diff xs w z + (pick _ v + pick _ v) = _
    rw [← add_assoc]
    simpa only [m,evolve,diffMoves xs w z wx zx] using eq
  ·
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

def Shape (xs s : List Label) : Prop :=
  bankBound (1+2*s.length) xs ∧ (∀ v∈s, v ≠ 0) ∧ (s ≠ [] → atom 0 ∈ s)

namespace Shape
theorem low {xs s : List Label} (h : Shape xs s) : bankBound (1+2*s.length) xs := h.1
theorem kept {xs s : List Label} (h : Shape xs s) : ∀ v∈s, v ≠ 0 := h.2.1
theorem unit_kept {xs s : List Label} (h : Shape xs s) : s ≠ [] → atom 0 ∈ s := h.2.2
end Shape

theorem evolveShape {xs s : List Label} {v : Label} (st : Shape (xs++[v]) s) (m : Mode) :
    Shape (evolve m v xs s).1 (evolve m v xs s).2 := by
  classical
  have low : bankBound (1+2*s.length) xs := fun a ha => st.low a (List.mem_append_left _ ha)
  have last : bounded (1+2*s.length) v := st.low _ (by simp)
  rcases m with ⟨⟩ | (i | (⟨i,j⟩ | ⟨i,j⟩))
  · exact ⟨low,st.kept,st.unit_kept⟩
  · exact ⟨moveBound _ _ _ _ low last,st.kept,st.unit_kept⟩
  · exact ⟨moveBound _ _ _ _ (moveBound _ _ _ _ low last) last,st.kept,st.unit_kept⟩
  ·
    by_cases dead : v=0
    · simpa only [evolve,if_pos dead] using (show Shape xs s from ⟨low,st.kept,st.unit_kept⟩)
    · simp only [evolve,if_neg dead]
      refine ⟨?_,?_,?_⟩
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
  rcases m : mode g with ⟨⟩ | (i | (⟨i,j⟩ | ⟨i,j⟩))
  ·
    simp [evolve]
    have h := forget s xs v
    omega
  ·
    simp [evolve]
    have h := singleStep v xs i (reserve s) hz
    simp only [accounts]
    omega
  ·
    simp only [m] at spec
    simp [evolve,spec.1]
    have h := binaryStep v xs i j (reserve s) hz
    simp only [accounts]
    omega
  ·
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

def Certificate (width : Nat) (gates : List Gate) (o : Nat) :=
  {p : List Label × List Label //
    p.1.length=width ∧ Shape p.1 p.2 ∧ p.2.length ≤ gates.countP isNonlin ∧
    accounts p.2 p.1 ≤ gates.countP isBinary + 3*p.2.length + 3 ∧
    ∀ (w z : List Bool), width=w.length → width=z.length → ∀ bit,
      diff p.1 w z = pick bit (atom 0) → xor (evaluate gates o w) (evaluate gates o z) = bit}

namespace Certificate
def xs {width o : Nat} {gates : List Gate} (c : Certificate width gates o) : List Label := c.val.1
def saved {width o : Nat} {gates : List Gate} (c : Certificate width gates o) : List Label := c.val.2
theorem length_eq {width o : Nat} {gates : List Gate} (c : Certificate width gates o) :
    c.xs.length=width := c.property.1
theorem shape {width o : Nat} {gates : List Gate} (c : Certificate width gates o) :
    Shape c.xs c.saved := c.property.2.1
theorem uses {width o : Nat} {gates : List Gate} (c : Certificate width gates o) :
    c.saved.length ≤ gates.countP isNonlin := c.property.2.2.1
theorem cost {width o : Nat} {gates : List Gate} (c : Certificate width gates o) :
    accounts c.saved c.xs ≤ gates.countP isBinary+3*c.saved.length+3 := c.property.2.2.2.1
theorem value {width o : Nat} {gates : List Gate} (c : Certificate width gates o) :
    ∀ (w z : List Bool), width=w.length → width=z.length → ∀ bit,
      diff c.xs w z=pick bit (atom 0) → xor (evaluate gates o w) (evaluate gates o z)=bit :=
    c.property.2.2.2.2
end Certificate

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
  refine ⟨⟨(xs,[]),by simpa [xs] using hr,⟨?_,by simp,by simp⟩,by simp,?_,?_⟩⟩
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
    refine ⟨⟨next,(evolveLength _ _ _ _).trans wide,evolveShape shape _,?_,?_,?_⟩⟩
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

end Matching

abbrev F := ZMod 2
abbrev Vec (k : ℕ) := Fin k → F

def dot {k : ℕ} (x y : Vec k) : F := ∑ i, x i * y i

lemma fadd (x : F) : x + x = 0 := by fin_cases x <;> decide

lemma vadd {k : ℕ} (x : Vec k) : x + x = 0 := by
  ext i
  exact fadd (x i)

lemma fneg (x : F) : -x = x := by
  calc -x = -x + (x+x) := by rw [fadd, add_zero]
       _ = x := by abel

lemma vneg {k : ℕ} (x : Vec k) : -x = x := by
  ext i
  exact fneg (x i)

lemma dot_comm {k : ℕ} (x y : Vec k) : dot x y = dot y x := by
  simp only [dot, mul_comm]

lemma dot_add_left {k : ℕ} (x y z : Vec k) :
    dot (x+y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {k : ℕ} (x y z : Vec k) :
    dot x (y+z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_zero_left {k : ℕ} (x : Vec k) : dot 0 x = 0 := by simp [dot]
lemma dot_zero_right {k : ℕ} (x : Vec k) : dot x 0 = 0 := by simp [dot]

lemma dot_separates {k : ℕ} (x : Vec k) (h : ∀ y, dot y x = 0) : x = 0 := by
  ext i
  have hi := h (Pi.single i 1)
  simpa [dot, Pi.single_apply, eq_comm] using hi

lemma dense_pairs {W : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    {q : ℕ} (r : Fin q → W) (hr : Function.Injective r)
    (hq : Fintype.card W < 2*q) (x : W) :
    ∃ i j, r i + r j = x := by
  let A := Finset.univ.image r
  let B := Finset.univ.image (fun j => x - r j)
  have ha : A.card = q := by
    simp [A, Finset.card_image_of_injective _ hr]
  have hb : B.card = q := by
    have hinj : Function.Injective (fun j => x-r j) := by
      intro i j hij
      apply hr
      exact sub_right_inj.mp hij
    simp [B, Finset.card_image_of_injective _ hinj]
  have hle : (A ∪ B).card ≤ Fintype.card W := Finset.card_le_univ _
  have hc := Finset.card_union_add_card_inter A B
  have hn : (A ∩ B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hn
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
  refine ⟨i,j,?_⟩
  have hh : r i = x-r j := hi.trans hj.symm
  exact (eq_sub_iff_add_eq).mp hh

lemma dense_dot_zero {k q : ℕ} (r : Fin q → Vec k) (hr : Function.Injective r)
    (hq : Fintype.card (Vec k) < 2*q) (x : Vec k)
    (h : ∀ i, dot (r i) x = 0) : x = 0 := by
  apply dot_separates
  intro y
  obtain ⟨i,j,hij⟩ := dense_pairs r hr hq y
  rw [← hij, dot_add_left, h, h, add_zero]

lemma dense_linear_constant {k q : ℕ} (r : Fin q → Vec k)
    (hr : Function.Injective r) (hq : Fintype.card (Vec k) < 2*q)
    (f : Vec k →ₗ[F] F) (e : F) (he : ∀ i, f (r i) = e) :
    f = 0 ∧ e = 0 := by
  have hz : ∀ y, f y = 0 := by
    intro y
    obtain ⟨i,j,hij⟩ := dense_pairs r hr hq y
    rw [← hij, map_add, he, he, fadd]
  have hqp : 0 < q := by
    have hc : 0 < Fintype.card (Vec k) := Fintype.card_pos
    omega
  constructor
  · apply LinearMap.ext
    intro y
    exact hz y
  · exact (he ⟨0,hqp⟩).symm.trans (hz _)


lemma dense_dot_eq {k q : ℕ} (p : Fin q → Vec k) (hp : Function.Injective p)
    (hq : Fintype.card (Vec k) < 2*q) (x y : Vec k)
    (h : ∀ i, dot (p i) x = dot (p i) y) : x = y := by
  have hz : x+y = 0 := dense_dot_zero p hp hq (x+y) (by
    intro i
    rw [dot_add_right, h, fadd])
  have := congrArg (fun z => z+y) hz
  simpa [add_assoc, vadd] using this

lemma dot_smul_left {k : ℕ} (a : F) (x y : Vec k) :
    dot (a • x) y = a * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

lemma dot_smul_right {k : ℕ} (a : F) (x y : Vec k) :
    dot x (a • y) = a * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

lemma add_zero_iff {k : ℕ} (x y : Vec k) : x+y=0 ↔ x=y := by
  rw [add_eq_zero_iff_eq_neg, vneg]

lemma dense_symmetric_extension {k q : ℕ}
    (p z : Fin q → Vec k) (hp : Function.Injective p)
    (hq : Fintype.card (Vec k) < 2*q)
    (hs : ∀ i j, dot (p i) (z j) = dot (p j) (z i)) :
    ∃ T : Vec k →ₗ[F] Vec k,
      (∀ i, T (p i) = z i) ∧
      (∀ x y, dot x (T y) = dot y (T x)) := by
  classical
  have hex : ∀ x : Vec k, ∃ y : Vec k,
      ∀ i, dot (p i) y = dot x (z i) := by
    intro x
    obtain ⟨a,b,hab⟩ := dense_pairs p hp hq x
    refine ⟨z a + z b, ?_⟩
    intro i
    rw [dot_add_right, hs i a, hs i b, ← dot_add_left, hab]
  let f : Vec k → Vec k := fun x => Classical.choose (hex x)
  have hf : ∀ x i, dot (p i) (f x) = dot x (z i) :=
    fun x => Classical.choose_spec (hex x)
  let T : Vec k →ₗ[F] Vec k := {
    toFun := f
    map_add' := by
      intro x y
      apply dense_dot_eq p hp hq
      intro i
      rw [hf, dot_add_left, dot_add_right, hf, hf]
    map_smul' := by
      intro a x
      apply dense_dot_eq p hp hq
      intro i
      change dot (p i) (f (a • x)) = dot (p i) (a • f x)
      rw [hf, dot_smul_left, dot_smul_right, hf] }
  have hon : ∀ i, T (p i) = z i := by
    intro i
    apply dense_dot_eq p hp hq
    intro j
    change dot (p j) (f (p i)) = _
    rw [hf, hs]
  refine ⟨T, hon, ?_⟩
  intro x y
  obtain ⟨i,j,hij⟩ := dense_pairs p hp hq y
  rw [← hij, map_add, hon i, hon j, dot_add_right, dot_add_left]
  exact congrArg₂ (·+·) (hf x i).symm (hf x j).symm

lemma dense_extension_injective {k q : ℕ}
    (p z : Fin q → Vec k) (hp : Function.Injective p) (hz : Function.Injective z)
    (hq : Fintype.card (Vec k) < 2*q)
    (T : Vec k →ₗ[F] Vec k) (hon : ∀ i, T (p i) = z i) :
    Function.Injective T := by
  intro x y hxy
  obtain ⟨i,j,hij⟩ := dense_pairs p hp hq (x+y)
  have ht : T (x+y) = 0 := by rw [map_add, hxy, vadd]
  rw [← hij, map_add, hon, hon] at ht
  have he : i=j := hz ((add_zero_iff _ _).mp ht)
  apply (add_zero_iff x y).mp
  rw [← hij, he, vadd]

lemma center_symmetry {k q : ℕ} (r c : Fin q → Vec k) (B : Fin q → F)
    (hs : ∀ i j, dot (r i) (c j) + B i = dot (r j) (c i) + B j)
    (o i j : Fin q) :
    dot (r i+r o) (c j+c o) = dot (r j+r o) (c i+c o) := by
  simp only [dot_add_left, dot_add_right]
  have h1 := hs i j
  have h2 := hs j o
  have h3 := hs o i
  have htwo : (2 : F) = 0 := by decide
  linear_combination (norm := (ring_nf; simp [htwo])) h1 + h2 + h3


lemma fsquare (a : F) : a*a=a := by
  fin_cases a
  · change (0:F)*(0:F)=0
    simp
  · change (1:F)*(1:F)=1
    simp

lemma large_matching_affine {k q : ℕ}
    (r c : Fin q → Vec k) (hr : Function.Injective r) (hc : Function.Injective c)
    (hq : Fintype.card (Vec k) < 2*q) (B : Fin q → F) (d : F)
    (hs : ∀ i j, dot (r i) (c j)+B i = dot (r j) (c i)+B j)
    (hd : ∀ i, dot (r i) (c i)+B i=d) :
    ∃ (T : Vec k ≃ₗ[F] Vec k) (a : Vec k) (e : F),
      (∀ x, dot x (T x)=0) ∧
      (∀ i, c i=T (r i)+a) ∧
      (∀ i, B i=dot a (r i)+e) := by
  classical
  have htwo : (2 : F)=0 := by decide
  have hqp : 0<q := by
    have hpos : 0<Fintype.card (Vec k) := Fintype.card_pos
    omega
  let o : Fin q := ⟨0,hqp⟩
  let p : Fin q → Vec k := fun i => r i+r o
  let z : Fin q → Vec k := fun i => c i+c o
  have hp : Function.Injective p := by
    intro i j hij
    apply hr
    exact add_right_cancel hij
  have hz : Function.Injective z := by
    intro i j hij
    apply hc
    exact add_right_cancel hij
  have hsym : ∀ i j, dot (p i) (z j)=dot (p j) (z i) :=
    fun i j => center_symmetry r c B hs o i j
  obtain ⟨L,hon,hself⟩ := dense_symmetric_extension p z hp hq hsym
  have hLinj := dense_extension_injective p z hp hz hq L hon
  let T : Vec k ≃ₗ[F] Vec k :=
    LinearEquiv.ofBijective L ⟨hLinj,Finite.surjective_of_injective hLinj⟩
  let a : Vec k := L (r o)+c o
  let e : F := B o+dot a (r o)
  have hcol : ∀ i, c i=L (r i)+a := by
    intro i
    have ht := hon i
    change L (r i+r o)=c i+c o at ht
    rw [map_add] at ht
    have hh := congrArg (fun w => w+c o) ht
    simpa only [a,add_assoc,vadd,add_zero] using hh.symm
  have hB : ∀ i, B i=dot a (r i)+e := by
    intro i
    have h := hs i o
    rw [hcol i,hcol o] at h
    rw [dot_add_right (r i) (L (r o)) a, dot_add_right (r o) (L (r i)) a,
      hself (r i) (r o),dot_comm (r i) a,dot_comm (r o) a] at h
    dsimp [e]
    linear_combination (norm := (ring_nf; simp [htwo])) h
  let form : Vec k →ₗ[F] F := {
    toFun := fun x => dot x (L x)
    map_add' := by
      intro x y
      change dot (x+y) (L (x+y)) = dot x (L x)+dot y (L y)
      rw [map_add,dot_add_left,dot_add_right,dot_add_right,← hself x y]
      ring_nf
      simp [htwo]
    map_smul' := by
      intro a x
      change dot (a • x) (L (a • x)) = a*dot x (L x)
      rw [map_smul,dot_smul_left,dot_smul_right,←mul_assoc,fsquare] }
  have hform : ∀ i, form (r i)=d+e := by
    intro i
    have h := hd i
    rw [hcol i,dot_add_right,hB i,dot_comm (r i) a] at h
    change dot (r i) (L (r i))=d+e
    linear_combination (norm := (ring_nf; simp [htwo])) h
  have hzero := (dense_linear_constant r hr hq form (d+e) hform).1
  refine ⟨T,a,e,?_,hcol,hB⟩
  intro x
  have hx := congrArg (fun f : Vec k →ₗ[F] F => f x) hzero
  exact hx


lemma fcases (a : F) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

def bit (a : F) : Bool := decide (a=1)

lemma bit_inj (a b : F) : bit a=bit b ↔ a=b := by
  rcases fcases a with rfl|rfl <;>
    rcases fcases b with rfl|rfl <;> simp [bit]

lemma bit_add (a b : F) : bit (a+b)=xor (bit a) (bit b) := by
  rcases fcases a with rfl|rfl <;>
    rcases fcases b with rfl|rfl <;> simp [bit,fadd]

def swapHalf (s : ℕ) : Vec (s+s) ≃ₗ[F] Vec (s+s) where
  toFun x := Fin.addCases (fun i => x (Fin.natAdd s i)) (fun i => x (Fin.castAdd s i))
  invFun x := Fin.addCases (fun i => x (Fin.natAdd s i)) (fun i => x (Fin.castAdd s i))
  left_inv x := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
  right_inv x := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
  map_add' x y := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right,Pi.add_apply]
  map_smul' a x := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

lemma swapHalf_apply (s : ℕ) (x : Vec (s+s)) (i : Fin (s+s)) :
    swapHalf s x i = Fin.addCases (fun j => x (Fin.natAdd s j))
      (fun j => x (Fin.castAdd s j)) i := rfl

lemma swapHalf_alt (s : ℕ) (x : Vec (s+s)) :
    dot x (swapHalf s x)=0 := by
  unfold dot
  rw [Fin.sum_univ_add]
  simp only [swapHalf_apply,Fin.addCases_left,Fin.addCases_right]
  change (∑ i : Fin s, x (Fin.castAdd s i) * x (Fin.natAdd s i))+
    (∑ i : Fin s, x (Fin.natAdd s i) * x (Fin.castAdd s i))=0
  have hh : (∑ i : Fin s, x (Fin.natAdd s i) * x (Fin.castAdd s i))=
      ∑ i : Fin s, x (Fin.castAdd s i) * x (Fin.natAdd s i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [hh,fadd]

lemma exists_alternating (s : ℕ) :
    ∃ T : Vec (2*s) ≃ₗ[F] Vec (2*s), ∀ x, dot x (T x)=0 := by
  rw [show 2*s=s+s by omega]
  exact ⟨swapHalf s,swapHalf_alt s⟩

lemma matching_discrepancy_bound {k q : ℕ} (Q R : Vec k → F)
    (r c : Fin q → Vec k) (hr : Function.Injective r)
    (T : Vec k ≃ₗ[F] Vec k) (a : Vec k) (e : F)
    (hc : ∀ i, c i=T (r i)+a)
    (hB : ∀ i, Q (r i)+R (c i)=dot a (r i)+e) :
    ((Finset.univ : Finset (Vec k)).filter
      (fun x => Q x+R (T x+a) ≠ dot a x+e)).card+q ≤ Fintype.card (Vec k) := by
  classical
  let bad := (Finset.univ : Finset (Vec k)).filter
    (fun x => Q x+R (T x+a) ≠ dot a x+e)
  let good := Finset.univ.image r
  have hg : good.card=q := by
    simp [good,Finset.card_image_of_injective _ hr]
  have hd : Disjoint bad good := by
    apply Finset.disjoint_left.mpr
    intro x hx hxg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hxg
    have hb := (Finset.mem_filter.mp hx).2
    rw [←hc i] at hb
    exact hb (hB i)
  have hcard := Finset.card_union_of_disjoint hd
  have hle : (bad ∪ good).card ≤ Fintype.card (Vec k) := Finset.card_le_univ _
  change bad.card+q ≤ _
  omega

lemma balanced_constant {W : Type*} [Fintype W] [DecidableEq W] (f : W → F) :
    ∃ e : F, 2*((Finset.univ : Finset W).filter (fun x => f x≠e)).card ≤ Fintype.card W := by
  classical
  let A := (Finset.univ : Finset W).filter (fun x => f x≠0)
  let B := (Finset.univ : Finset W).filter (fun x => f x≠1)
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases fcases (f x) with h|h
    · exact hx' h
    · exact hy' h
  have hu : A ∪ B=Finset.univ := by
    ext x
    simp only [A,B,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases fcases (f x) with h|h <;> simp [h]
  have hc := Finset.card_union_of_disjoint hd
  rw [hu,Finset.card_univ] at hc
  by_cases ha : 2*A.card ≤ Fintype.card W
  · exact ⟨0,ha⟩
  · exact ⟨1,by change 2*B.card ≤ Fintype.card W; omega⟩


lemma from_square (s q b t : ℕ) (Q R : Vec (2*s) → F)
    (r c : Fin q → Vec (2*s)) (hr : Function.Injective r) (hc : Function.Injective c)
    (hs : ∀ i j, bit (dot (r i) (c j)+Q (r i)+R (c j))=
      bit (dot (r j) (c i)+Q (r j)+R (c i)))
    (hd : ∀ i j, bit (dot (r i) (c i)+Q (r i)+R (c i))=
      bit (dot (r j) (c j)+Q (r j)+R (c j)))
    (hcharge : 4*Fintype.card (Vec (2*s)) ≤ b+2*t+q+4) :
    ∃ (T : Vec (2*s) ≃ₗ[F] Vec (2*s)) (a : Vec (2*s)) (e : F),
      (∀ x, dot x (T x)=0) ∧
      3*Fintype.card (Vec (2*s))+
        ((Finset.univ : Finset (Vec (2*s))).filter
          (fun x => Q x+R (T x+a) ≠ dot a x+e)).card ≤ b+2*t+4 := by
  classical
  have htwo : (2:F)=0 := by decide
  obtain ⟨T,a,e,halt,hcount⟩ :
      ∃ (T : Vec (2*s) ≃ₗ[F] Vec (2*s)) (a : Vec (2*s)) (e : F),
        (∀ x, dot x (T x)=0) ∧
        ((Finset.univ : Finset (Vec (2*s))).filter
          (fun x => Q x+R (T x+a) ≠ dot a x+e)).card+q ≤ Fintype.card (Vec (2*s)) := by
    by_cases hlarge : Fintype.card (Vec (2*s)) < 2*q
    · have hqp : 0<q := by
        have hpos : 0<Fintype.card (Vec (2*s)) := Fintype.card_pos
        omega
      let o : Fin q := ⟨0,hqp⟩
      let B : Fin q → F := fun i => Q (r i)+R (c i)
      let d : F := dot (r o) (c o)+B o
      have hsym : ∀ i j, dot (r i) (c j)+B i=dot (r j) (c i)+B j := by
        intro i j
        have h := (bit_inj _ _).mp (hs i j)
        dsimp [B]
        linear_combination (norm := (ring_nf; simp [htwo])) h
      have hdiag : ∀ i, dot (r i) (c i)+B i=d := by
        intro i
        have h := (bit_inj _ _).mp (hd i o)
        simpa only [B,d,add_assoc] using h
      obtain ⟨T,a,e,ha,hcol,hB⟩ := large_matching_affine r c hr hc hlarge B d hsym hdiag
      refine ⟨T,a,e,ha,?_⟩
      exact matching_discrepancy_bound Q R r c hr T a e hcol hB
    · have hq : 2*q ≤ Fintype.card (Vec (2*s)) := by omega
      obtain ⟨T,ha⟩ := exists_alternating s
      obtain ⟨e,he⟩ := balanced_constant (fun x => Q x+R (T x))
      refine ⟨T,0,e,ha,?_⟩
      simp only [add_zero,dot_zero_left,zero_add]
      omega
  exact ⟨T,a,e,halt,by omega⟩

lemma bit_bool (b : Bool) : bit (if b then 1 else 0)=b := by
  cases b <;> simp [bit]

lemma profiles_distinct {k n : ℕ} (label : Fin n ≃ Vec k) (Q R : Vec k → F) :
    ∀ i j : Fin n, i≠j → ∀ f : Bool, ∃ y,
      bit (dot (label i) (label y)+Q (label i)+R (label y)) ≠
        xor f (bit (dot (label j) (label y)+Q (label j)+R (label y))) := by
  classical
  intro i j hij f
  by_contra hn
  push Not at hn
  let a : F := if f then 1 else 0
  have ha : bit a=f := bit_bool f
  have heq : ∀ y : Vec k,
      dot (label i) y+Q (label i)+R y=
      a+(dot (label j) y+Q (label j)+R y) := by
    intro y
    apply (bit_inj _ _).mp
    rw [bit_add a (dot (label j) y+Q (label j)+R y),ha]
    simpa only [Equiv.apply_symm_apply] using hn (label.symm y)
  have hzero := heq 0
  simp only [dot_zero_right,zero_add] at hzero
  have htwo : (2:F)=0 := by decide
  have hv : label i+label j=0 := by
    apply dot_separates
    intro y
    rw [dot_add_right,dot_comm y (label i),dot_comm y (label j)]
    have hy := heq y
    linear_combination (norm := (ring_nf; simp [htwo])) hy-hzero
  exact hij (label.injective ((add_zero_iff _ _).mp hv))

lemma cube_card (k : ℕ) : Fintype.card (Vec k)=2^k := by
  simp [Vec,F]

lemma from_charged_matching (s b t : ℕ) (Q R : Vec (2*s) → F)
    (label : Fin (2^(2*s)) ≃ Vec (2*s))
    (hmatch : ∃ (q : ℕ) (row col : Fin q → Fin (2^(2*s))),
      Function.Injective row ∧ Function.Injective col ∧
      (∀ i j, bit (dot (label (row i)) (label (col j))+Q (label (row i))+R (label (col j)))=
        bit (dot (label (row j)) (label (col i))+Q (label (row j))+R (label (col i)))) ∧
      (∀ i j, bit (dot (label (row i)) (label (col i))+Q (label (row i))+R (label (col i)))=
        bit (dot (label (row j)) (label (col j))+Q (label (row j))+R (label (col j)))) ∧
      2*((2^(2*s))+(2^(2*s))) ≤ b+2*t+q+4) :
    ∃ (T : Vec (2*s) ≃ₗ[F] Vec (2*s)) (a : Vec (2*s)) (e : F),
      (∀ x, dot x (T x)=0) ∧
      3*(2^(2*s))+
        ((Finset.univ : Finset (Vec (2*s))).filter
          (fun x => Q x+R (T x+a) ≠ dot a x+e)).card ≤ b+2*t+4 := by
  obtain ⟨q,row,col,hr,hc,hs,hd,hch⟩ := hmatch
  have hcharge : 4*Fintype.card (Vec (2*s)) ≤ b+2*t+q+4 := by
    rw [cube_card]
    omega
  obtain ⟨T,a,e,ha,hbound⟩ := from_square s q b t Q R
    (label ∘ row) (label ∘ col) (label.injective.comp hr) (label.injective.comp hc)
    hs hd hcharge
  exact ⟨T,a,e,ha,by simpa only [cube_card] using hbound⟩


def MatchingBound : Prop := ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
    2*(n+m) ≤ b + 2*t + q + 4

lemma solve_from_matching_bound (hmatching : MatchingBound) : ∀ s : ℕ, 1 ≤ s →
  let k := 2*s
  let N := 2^k
  let V := Fin k → ZMod 2
  let dot := fun (x y : V) => ∑ j : Fin k, x j * y j
  ∀ (label : Fin N ≃ V) (Q R : V → ZMod 2) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
    PEqualNP.Represents.Represents (fun i j =>
      decide (dot (label i) (label j) + Q (label i) + R (label j) = 1)) C →
    let b := C.gates.countP (fun g => g.inputs.length == 2)
    let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    ∃ (T : V ≃ₗ[ZMod 2] V) (a : V) (e : ZMod 2),
      (∀ x : V, dot x (T x) = 0) ∧
      3*N + ((Finset.univ : Finset V).filter (fun x =>
        Q x + R (T x + a) ≠ dot a x + e)).card ≤ b + 2*t + 4 := by

  intro s hs
  dsimp only
  intro label Q R C hfan hread hrep
  let N := 2^(2*s)
  let G : Fin N → Fin N → Bool := fun i j =>
    bit (dot (label i) (label j)+Q (label i)+R (label j))
  let b := C.gates.countP (fun g => g.inputs.length == 2)
  let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
  change ∃ (T : Vec (2*s) ≃ₗ[F] Vec (2*s)) (a : Vec (2*s)) (e : F),
    (∀ x, dot x (T x)=0) ∧
    3*N+((Finset.univ : Finset (Vec (2*s))).filter
      (fun x => Q x+R (T x+a) ≠ dot a x+e)).card ≤ b+2*t+4
  have hN : 2≤N := by
    dsimp [N]
    have hn : 1≤2*s := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0<2) hn
    simpa using hp
  have hrow : ∀ i j : Fin N, i≠j → ∀ f : Bool, ∃ y, G i y≠xor f (G j y) :=
    profiles_distinct label Q R
  have hcol : ∀ i j : Fin N, i≠j → ∀ f : Bool, ∃ x, G x i≠xor f (G x j) := by
    intro i j hij f
    obtain ⟨x,hx⟩ := profiles_distinct label R Q i j hij f
    refine ⟨x,?_⟩
    simpa only [G,dot_comm,add_comm,add_left_comm,add_assoc] using hx
  have hm := hmatching N N G C hN hN hrow hcol hfan hread hrep
  exact from_charged_matching s b t Q R label hm

lemma matching_bound : MatchingBound := by
  intro n m G C hn hm ra ca fan _ rep
  exact Matching.BackwardAffine.full n m G C hn hm ra ca fan rep

end PEqualNP.Outside.L_meta_25795

theorem PEqualNP.Outside.L_meta_25795 : ∀ s : ℕ, 1 ≤ s →
  let k := 2*s
  let N := 2^k
  let V := Fin k → ZMod 2
  let dot := fun (x y : V) => ∑ j : Fin k, x j * y j
  ∀ (label : Fin N ≃ V) (Q R : V → ZMod 2) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
    PEqualNP.Represents.Represents (fun i j =>
      decide (dot (label i) (label j) + Q (label i) + R (label j) = 1)) C →
    let b := C.gates.countP (fun g => g.inputs.length == 2)
    let t := C.gates.countP (fun g => (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    ∃ (T : V ≃ₗ[ZMod 2] V) (a : V) (e : ZMod 2),
      (∀ x : V, dot x (T x) = 0) ∧
      3*N + ((Finset.univ : Finset V).filter (fun x =>
        Q x + R (T x + a) ≠ dot a x + e)).card ≤ b + 2*t + 4 :=
  PEqualNP.Outside.L_meta_25795.solve_from_matching_bound PEqualNP.Outside.L_meta_25795.matching_bound
