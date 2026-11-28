import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36839

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
end Live

abbrev W := BitVec 2048
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := (-1 : BitVec 1024) ++ (0 : BitVec 1024)
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 2048 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 2048)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 2048) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 2048) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 2048) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 2048 0)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


section Fast

def nP : ℕ := 1024
def fullM : ℕ := 2 ^ nP - 1
def hiM : ℕ := Nat.shiftLeft (2 ^ nP - 1) nP
def allM : ℕ := 2 ^ (nP + nP) - 1
def sp (x : ℕ) : ℕ := Nat.xor (Nat.shiftRight x nP) x
def cutN (l : List ℕ) : ℕ := List.rec 0 (fun w _ ih => Nat.lor (Nat.xor (Nat.shiftRight w nP) w) ih) l
def memN (z : ℕ) (l : List ℕ) : Bool := List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
def app (l r : List ℕ) : List ℕ := List.rec r (fun w _ ih => w :: ih) l
def isGoal (ws : List ℕ) : Bool :=
  List.rec false (fun w t _ => List.rec (Bool.rec (Nat.beq w fullM) true (Nat.beq w hiM)) (fun _ _ _ => false) t) ws
def anyK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) : Bool :=
  List.rec false (fun c _ ih => Bool.rec ih true (f c.1 c.2)) l
def hdK (l : List (ℕ × List ℕ)) : ℕ × List ℕ := List.rec (0, []) (fun c _ _ => c) l
def dz (base z : ℕ) : ℕ := Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight z nP) z) base)
def keep2 (e1 a b : ℕ) (r : List ℕ) (z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec tail (fun e2 _ => (e2, z :: a :: b :: r) :: tail) e1
def keepB (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keep2 e1 a b r z tail) ((e1, z :: b :: r) :: keep2 e1 a b r z tail)
    (Nat.beq (dz (Nat.lor base (sp b)) z) 0)
def keepA (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keepB e1 a b r base z tail) ((e1, z :: a :: r) :: keepB e1 a b r base z tail)
    (Nat.beq (dz (Nat.lor base (sp a)) z) 0)
def keeps (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec tail (fun e1 _ => keepA e1 a b r base z tail) e
def cand0 (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keeps e a b r base z tail) ((e, z :: r) :: keeps e a b r base z tail) (Nat.beq (dz base z) 0)
def cand (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec tail (Bool.rec (cand0 e a b r base z tail) tail (memN z ws)) (Nat.ble thr z)
def opsN (a b : ℕ) : List ℕ := [Nat.land a b, Nat.lor a b, Nat.xor a (Nat.land a b), Nat.xor b (Nat.land a b)]
def pairKS (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  cand e thr a b ws r base (Nat.land a b) (cand e thr a b ws r base (Nat.lor a b)
    (cand e thr a b ws r base (Nat.xor a (Nat.land a b)) (cand e thr a b ws r base (Nat.xor b (Nat.land a b)) tail)))
def forceN (z : ℕ) (k : ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) := Nat.rec (k Nat.zero) (fun m _ => k (Nat.succ m)) z
def revK (pre acc : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  List.rec (fun acc => k acc) (fun p _ ih acc => ih (p :: acc)) pre acc
def insK (x : ℕ) (l : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List ℕ → List (ℕ × List ℕ) :=
  List.rec (fun pre => revK pre [x] k)
    (fun y ys ih pre => Bool.rec (ih (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y)) l
def mkR (thr : ℕ) (sk rest : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec (revK sk rest k) (fun _ _ => revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L)) thr
def sortK (l : List ℕ) : (List ℕ → List (ℕ × List ℕ)) → List (ℕ × List ℕ) :=
  List.rec (fun k => k []) (fun x _ ih k => ih (fun s => forceN x (fun x' => insK x' s k []))) l
def canonMap (l : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  List.rec [] (fun c _ ih => Nat.rec
    (List.rec ih (fun z t _ => sortK t (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: ih))) c.2)
    (fun _ _ => c :: ih) c.1) l
def prodN (z : ℕ) (l : List ℕ) : ℕ := List.rec 1 (fun w _ ih => Nat.mul ih (Nat.xor z w)) l
def candZ (thr : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec tail (Bool.rec (forceN z (fun z' => (Nat.zero, z' :: r) :: tail)) tail (Nat.beq (prodN z ws) 0))
    (Nat.beq (Nat.add (dz base z) (Nat.sub thr z)) 0)
def pairZ (thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  candZ thr ws r base (Nat.land a b) (candZ thr ws r base (Nat.lor a b)
    (candZ thr ws r base (Nat.xor a (Nat.land a b)) (candZ thr ws r base (Nat.xor b (Nat.land a b)) tail)))
def pairK (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec (pairZ thr a b ws r base tail) (fun _ _ => pairKS e thr a b ws r base tail) e
def flt0 (a b base : ℕ) : Bool :=
  Nat.beq (Nat.mul
    (Nat.mul (Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b)) base))
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a) (Nat.xor (Nat.shiftRight b nP) b))
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base)))
    (Nat.mul
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base))
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight b nP) b)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base)))) 0
def fltT (_ _ _ : ℕ) : Bool := true
def innerK (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a : ℕ) (post : List ℕ) :
    ℕ → List ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) :=
  List.rec (fun _ _ tail => tail)
    (fun b rest ih acc sk tail =>
      Bool.rec (ih (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)
        (mkR thr sk rest (fun r => pairK e thr a b ws r (Nat.lor acc (cutN rest))
          (ih (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)))
        (flt a b (Nat.lor acc (cutN rest))))
    post
def outerK (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (post : List ℕ) :
    ℕ → List ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) :=
  List.rec (fun _ _ tail => tail)
    (fun a post ih acc pre tail =>
      innerK flt e thr ws a post acc pre (ih (Nat.lor acc (Nat.xor (Nat.shiftRight a nP) a)) (a :: pre) tail))
    post
def kidsG (flt : ℕ → ℕ → ℕ → Bool) (e h : ℕ) (t ws : List ℕ) : List (ℕ × List ℕ) :=
  innerK flt e 0 ws h t hiM []
    (outerK flt e h ws t (Nat.lor hiM (Nat.xor (Nat.shiftRight h nP) h)) [h] [])
def kids (e : ℕ) (ws : List ℕ) : List (ℕ × List ℕ) :=
  List.rec [] (fun h t _ => Nat.rec (kidsG flt0 e h t ws) (fun _ _ => canonMap (kidsG fltT e h t ws)) e) ws
def kidsRoot (e : ℕ) (ws : List ℕ) : List (ℕ × List ℕ) :=
  canonMap (Nat.rec (outerK flt0 e 0 ws ws hiM [] []) (fun _ _ => outerK fltT e 0 ws ws hiM [] []) e)
def crossC (l : List ℕ) : ℕ → ℕ → Bool :=
  List.rec (fun p q => Bool.rec (Bool.rec true false (Nat.beq q 0)) false (Nat.beq p 0))
    (fun w _ ih p q =>
      Bool.rec (Bool.rec (Bool.rec (ih (Nat.xor p (Nat.land p w)) (Nat.xor q (Nat.land q (Nat.shiftRight w nP))))
        true (ih (Nat.land p w) (Nat.land q (Nat.shiftRight w nP)))) false (Nat.beq q 0)) false (Nat.beq p 0))
    l
def collOK (c : ℕ) (ws : List ℕ) : Bool := Nat.rec true (fun _ _ => Bool.rec true false (crossC ws fullM fullM)) c
def node (c k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (fun _ ws => isGoal ws)
    (fun _ ih e ws => Bool.rec (Bool.rec false (anyK ih (kids e ws)) (collOK c ws)) true (isGoal ws)) k
def root (c k e : ℕ) (ws : List ℕ) : Bool := Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws)
def cutFull (ws : List ℕ) : Bool := Nat.beq (Nat.sub allM (Nat.lor (cutN ws) hiM)) 0
def searchN (c k : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws => decide (ws.length ≤ k + 2) && cutFull ws && root c k (k + 2 - ws.length) ws

set_option maxRecDepth 100000 in
theorem brec_eq {α : Type} (x y : α) (c : Bool) : (Bool.rec x y c : α) = if c = true then y else x := by
  cases c <;> rfl

set_option maxRecDepth 100000 in
theorem sp_bit (x i : ℕ) : (sp x).testBit i = Bool.xor (x.testBit (nP + i)) (x.testBit i) := by
  rw [show sp x = (x >>> nP) ^^^ x from rfl, Nat.testBit_xor, Nat.testBit_shiftRight]

set_option maxRecDepth 100000 in
theorem cutN_bit (l : List ℕ) (i : ℕ) : (cutN l).testBit i = true ↔ ∃ w ∈ l, (sp w).testBit i = true := by
  induction l with
  | nil => simp [show cutN [] = 0 from rfl]
  | cons w l ih =>
    rw [show cutN (w :: l) = sp w ||| cutN l from rfl, Nat.testBit_or, Bool.or_eq_true, ih]
    simp

set_option maxRecDepth 100000 in
theorem ge_of_bits (m x : ℕ) (h : ∀ i < m, x.testBit i = true) : 2 ^ m - 1 ≤ x := by
  have e : x % 2 ^ m = 2 ^ m - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi, h i hi]
    · simp [hi]
  rw [← e]
  exact Nat.mod_le _ _

set_option maxRecDepth 100000 in
theorem hiM_bit (i : ℕ) (h1 : nP ≤ i) (h2 : i < nP + nP) : hiM.testBit i = true := by
  rw [show hiM = (2 ^ nP - 1) <<< nP from rfl, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

set_option maxRecDepth 100000 in
theorem pass_of (base z : ℕ) (hlo : ∀ i < nP, (sp z).testBit i = true ∨ base.testBit i = true)
    (hhi : ∀ i, nP ≤ i → i < nP + nP → base.testBit i = true) : Nat.beq (dz base z) 0 = true := by
  have le : allM ≤ sp z ||| base := by
    apply ge_of_bits
    intro i hi
    rw [Nat.testBit_or, Bool.or_eq_true]
    by_cases c : i < nP
    · exact hlo i c
    · exact Or.inr (hhi i (by omega) hi)
  have z0 : dz base z = 0 := Nat.sub_eq_zero_of_le le
  rw [z0]
  rfl

def accOK (acc : ℕ) (sk : List ℕ) : Prop :=
  (∀ i, nP ≤ i → i < nP + nP → acc.testBit i = true) ∧
  (∀ w ∈ sk, ∀ i, (sp w).testBit i = true → acc.testBit i = true)

set_option maxRecDepth 100000 in
theorem accOK_nil : accOK hiM [] := ⟨hiM_bit, by simp⟩

set_option maxRecDepth 100000 in
theorem accOK_cons {acc : ℕ} {sk : List ℕ} (h : accOK acc sk) (b : ℕ) :
    accOK (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) := by
  change accOK (acc ||| sp b) (b :: sk)
  refine ⟨fun i h1 h2 => ?_, fun w hw i hi => ?_⟩
  · rw [Nat.testBit_or, h.1 i h1 h2]; rfl
  · rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr hi
    · exact Or.inl (h.2 w hw i hi)

set_option maxRecDepth 100000 in
theorem app_eq (l r : List ℕ) : app l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w l ih => change w :: app l r = w :: (l ++ r); rw [ih]

set_option maxRecDepth 100000 in
theorem forceN_eq (z : ℕ) (k : ℕ → List (ℕ × List ℕ)) : forceN z k = k z := by
  cases z <;> rfl

set_option maxRecDepth 100000 in
theorem revK_eq (k : List ℕ → List (ℕ × List ℕ)) : ∀ (pre acc : List ℕ), revK pre acc k = k (pre.reverse ++ acc) := by
  intro pre
  induction pre with
  | nil => intro acc; rfl
  | cons p pre ih =>
    intro acc
    change revK pre (p :: acc) k = k ((p :: pre).reverse ++ acc)
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

set_option maxRecDepth 100000 in
theorem insK_eq (x : ℕ) : ∀ l : List ℕ, ∃ r : List ℕ, r.Perm (x :: l) ∧
    ∀ (k : List ℕ → List (ℕ × List ℕ)) (pre : List ℕ), insK x l k pre = k (pre.reverse ++ r) := by
  intro l
  induction l with
  | nil => exact ⟨[x], List.Perm.refl _, fun k pre => revK_eq k pre [x]⟩
  | cons y ys ih =>
    obtain ⟨r, hr, hk⟩ := ih
    cases hb : Nat.ble x y
    · refine ⟨y :: r, (hr.cons y).trans (List.Perm.swap x y ys), fun k pre => ?_⟩
      change (Bool.rec (insK x ys k (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y) : List (ℕ × List ℕ)) = _
      rw [hb]
      change insK x ys k (y :: pre) = _
      rw [hk, List.reverse_cons, List.append_assoc]
      rfl
    · refine ⟨x :: y :: ys, List.Perm.refl _, fun k pre => ?_⟩
      change (Bool.rec (insK x ys k (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y) : List (ℕ × List ℕ)) = _
      rw [hb]
      exact revK_eq k pre _

set_option maxRecDepth 100000 in
theorem mkR_eq (thr : ℕ) (sk rest : List ℕ) : ∃ r : List ℕ, r.Perm (sk ++ rest) ∧
    ∀ k : List ℕ → List (ℕ × List ℕ), mkR thr sk rest k = k r := by
  have p0 : (sk.reverse ++ rest).Perm (sk ++ rest) := (List.reverse_perm sk).append_right rest
  cases thr with
  | zero => exact ⟨sk.reverse ++ rest, p0, fun k => revK_eq k sk rest⟩
  | succ t =>
    cases hL : sk.reverse ++ rest with
    | nil =>
      rw [hL] at p0
      refine ⟨[], p0, fun k => ?_⟩
      change revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L) = k []
      rw [revK_eq, hL]
    | cons h tl =>
      rw [hL] at p0
      obtain ⟨r, hr, hk⟩ := insK_eq h tl
      refine ⟨r, hr.trans p0, fun k => ?_⟩
      change revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L) = k r
      rw [revK_eq, hL]
      exact hk k []

set_option maxRecDepth 100000 in
theorem sortK_eq : ∀ l : List ℕ, ∃ s : List ℕ, s.Perm l ∧
    ∀ k : List ℕ → List (ℕ × List ℕ), sortK l k = k s := by
  intro l
  induction l with
  | nil => exact ⟨[], List.Perm.refl _, fun k => rfl⟩
  | cons x xs ih =>
    obtain ⟨s, hs, hk⟩ := ih
    obtain ⟨r, hr, hi⟩ := insK_eq x s
    refine ⟨r, hr.trans (hs.cons x), fun k => ?_⟩
    change sortK xs (fun s => forceN x (fun x' => insK x' s k [])) = k r
    rw [hk, forceN_eq]
    exact hi k []

set_option maxRecDepth 100000 in
theorem canonMap_hit : ∀ (l : List (ℕ × List ℕ)) (e' z : ℕ) (kept : List ℕ), (e', z :: kept) ∈ l →
    ∃ kept' : List ℕ, kept'.Perm kept ∧ (e', z :: kept') ∈ canonMap l := by
  intro l
  induction l with
  | nil => intro e' z kept h; simp at h
  | cons c l ih =>
    intro e' z kept h
    have unf : canonMap (c :: l) = (Nat.rec
        (List.rec (canonMap l) (fun z t _ => sortK t (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: canonMap l))) c.2)
        (fun _ _ => c :: canonMap l) c.1 : List (ℕ × List ℕ)) := rfl
    have mono : ∀ c', c' ∈ canonMap l → c' ∈ canonMap (c :: l) := by
      intro c' hc'
      rw [unf]
      obtain ⟨e0, ws0⟩ := c
      cases e0 with
      | zero =>
        cases ws0 with
        | nil => exact hc'
        | cons z0 t0 =>
          obtain ⟨s, _, hk⟩ := sortK_eq t0
          change c' ∈ sortK t0 (fun s => forceN z0 (fun z' => (Nat.zero, z' :: s) :: canonMap l))
          rw [hk, forceN_eq]
          exact List.mem_cons_of_mem _ hc'
      | succ e1 => exact List.mem_cons_of_mem _ hc'
    rcases List.mem_cons.mp h with hc | h
    · subst hc
      cases e' with
      | zero =>
        obtain ⟨s, hs, hk⟩ := sortK_eq kept
        refine ⟨s, hs, ?_⟩
        rw [unf]
        change (0, z :: s) ∈ sortK kept (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: canonMap l))
        rw [hk, forceN_eq]
        exact List.mem_cons_self
      | succ e1 =>
        refine ⟨kept, List.Perm.refl _, ?_⟩
        rw [unf]
        exact List.mem_cons_self
    · obtain ⟨kept', hp, hm⟩ := ih e' z kept h
      exact ⟨kept', hp, mono _ hm⟩

set_option maxRecDepth 100000 in
theorem memN_false (z : ℕ) (l : List ℕ) (h : z ∉ l) : memN z l = false := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change (Bool.rec (memN z l) true (Nat.beq z w) : Bool) = false
    cases hb : Nat.beq z w
    · exact ih (fun hm => h (List.mem_cons_of_mem _ hm))
    · exact absurd (Nat.eq_of_beq_eq_true hb) (fun e => h (e ▸ List.mem_cons_self))

set_option maxRecDepth 100000 in
theorem keep2_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keep2 e1 a b r z tail := by
  cases e1 with
  | zero => exact h
  | succ e2 => exact List.mem_cons_of_mem _ h

set_option maxRecDepth 100000 in
theorem keepB_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keepB e1 a b r base z tail := by
  unfold keepB
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keep2_mono e1 a b r z h)
  · exact keep2_mono e1 a b r z h

set_option maxRecDepth 100000 in
theorem keepA_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keepA e1 a b r base z tail := by
  unfold keepA
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keepB_mono e1 a b r base z h)
  · exact keepB_mono e1 a b r base z h

set_option maxRecDepth 100000 in
theorem keeps_mono {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keeps e a b r base z tail := by
  cases e with
  | zero => exact h
  | succ e1 => exact keepA_mono e1 a b r base z h

set_option maxRecDepth 100000 in
theorem cand0_mono {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keeps_mono e a b r base z h)
  · exact keeps_mono e a b r base z h

set_option maxRecDepth 100000 in
theorem cand_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ cand e thr a b ws r base z tail := by
  unfold cand
  rw [brec_eq, brec_eq]
  split
  · split
    · exact h
    · exact cand0_mono e a b r base z h
  · exact h

set_option maxRecDepth 100000 in
theorem cand_eq (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hthr : thr ≤ z) (hfresh : z ∉ ws) :
    cand e thr a b ws r base z tail = cand0 e a b r base z tail := by
  unfold cand
  rw [Nat.ble_eq_true_of_le hthr, memN_false z ws hfresh]

set_option maxRecDepth 100000 in
theorem cand0_none (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz base z) 0 = true) : (e, z :: r) ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_of_keeps {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keeps e a b r base z tail) : c ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem keepA_of_keepB {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keepB e1 a b r base z tail) : c ∈ keepA e1 a b r base z tail := by
  unfold keepA
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem keepB_of_keep2 {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keep2 e1 a b r z tail) : c ∈ keepB e1 a b r base z tail := by
  unfold keepB
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem cand0_a (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz (Nat.lor base (sp a)) z) 0 = true) :
    (e1, z :: a :: r) ∈ cand0 (e1 + 1) a b r base z tail := by
  apply cand0_of_keeps
  change (e1, z :: a :: r) ∈ keepA e1 a b r base z tail
  unfold keepA
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_b (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz (Nat.lor base (sp b)) z) 0 = true) :
    (e1, z :: b :: r) ∈ cand0 (e1 + 1) a b r base z tail := by
  apply cand0_of_keeps
  change (e1, z :: b :: r) ∈ keepA e1 a b r base z tail
  apply keepA_of_keepB
  unfold keepB
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_ab (e2 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) :
    (e2, z :: a :: b :: r) ∈ cand0 (e2 + 2) a b r base z tail := by
  apply cand0_of_keeps
  change (e2, z :: a :: b :: r) ∈ keepA (e2 + 1) a b r base z tail
  apply keepA_of_keepB
  apply keepB_of_keep2
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem pairKS_hit {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hz : z ∈ opsN a b) (h : ∀ tail', c ∈ cand e thr a b ws r base z tail') :
    c ∈ pairKS e thr a b ws r base tail := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold pairKS
  rcases hz with rfl | rfl | rfl | rfl
  · exact h _
  · exact cand_mono _ _ _ _ _ _ _ _ (h _)
  · exact cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (h _))
  · exact cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (h _)))

set_option maxRecDepth 100000 in
theorem pairKS_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairKS e thr a b ws r base tail :=
  cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ h)))

set_option maxRecDepth 100000 in
theorem xor_zero_eq (z w : ℕ) (h : Nat.xor z w = 0) : z = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (fun y => Nat.testBit y i) h
  change (z ^^^ w).testBit i = (0 : ℕ).testBit i at e
  rw [Nat.testBit_xor, Nat.zero_testBit] at e
  revert e
  cases z.testBit i <;> cases w.testBit i <;> decide

set_option maxRecDepth 100000 in
theorem prodN_ne (z : ℕ) (l : List ℕ) (h : z ∉ l) : prodN z l ≠ 0 := by
  induction l with
  | nil => exact Nat.one_ne_zero
  | cons w l ih =>
    change Nat.mul (prodN z l) (Nat.xor z w) ≠ 0
    exact Nat.mul_ne_zero (ih (fun hm => h (List.mem_cons_of_mem _ hm)))
      (fun e0 => h (xor_zero_eq z w e0 ▸ List.mem_cons_self))

set_option maxRecDepth 100000 in
theorem candZ_mono {c : ℕ × List ℕ} (thr : ℕ) (ws r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ candZ thr ws r base z tail := by
  unfold candZ
  cases Nat.beq (Nat.add (dz base z) (Nat.sub thr z)) 0
  · exact h
  · cases Nat.beq (prodN z ws) 0
    · rw [forceN_eq]
      exact List.mem_cons_of_mem _ h
    · exact h

set_option maxRecDepth 100000 in
theorem candZ_hit (thr : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) (hthr : thr ≤ z)
    (hfresh : z ∉ ws) (hp : Nat.beq (dz base z) 0 = true) : (0, z :: r) ∈ candZ thr ws r base z tail := by
  have e0 : Nat.add (dz base z) (Nat.sub thr z) = 0 := by
    rw [Nat.eq_of_beq_eq_true hp]
    change 0 + (thr - z) = 0
    rw [Nat.sub_eq_zero_of_le hthr]
  have e1 : Nat.beq (prodN z ws) 0 = false := by
    cases hb : Nat.beq (prodN z ws) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (prodN_ne z ws hfresh)
  unfold candZ
  rw [e0, e1, forceN_eq]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem pairZ_mono {c : ℕ × List ℕ} (thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairZ thr a b ws r base tail :=
  candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ h)))

set_option maxRecDepth 100000 in
theorem pairZ_hit (thr a b z : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) (hz : z ∈ opsN a b)
    (hthr : thr ≤ z) (hfresh : z ∉ ws) (hp : Nat.beq (dz base z) 0 = true) :
    (0, z :: r) ∈ pairZ thr a b ws r base tail := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold pairZ
  rcases hz with rfl | rfl | rfl | rfl
  · exact candZ_hit _ _ _ _ _ _ hthr hfresh hp
  · exact candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp)
  · exact candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp))
  · exact candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp)))

set_option maxRecDepth 100000 in
theorem pairK_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairK e thr a b ws r base tail := by
  cases e with
  | zero => exact pairZ_mono thr a b ws r base h
  | succ e1 => exact pairKS_mono (e1 + 1) thr a b ws r base h

set_option maxRecDepth 100000 in
theorem opsN_swap {a b z : ℕ} (h : z ∈ opsN a b) : z ∈ opsN b a := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  have c1 : Nat.land b a = Nat.land a b := Nat.land_comm b a
  have c2 : Nat.lor b a = Nat.lor a b := Nat.lor_comm b a
  rw [c1, c2]
  tauto

set_option maxRecDepth 100000 in
theorem sp_xor (a b : ℕ) : sp (Nat.xor a b) = Nat.xor (sp a) (sp b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (sp (a ^^^ b)).testBit i = (sp a ^^^ sp b).testBit i
  rw [sp_bit, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, sp_bit, sp_bit]
  cases a.testBit (nP + i) <;> cases a.testBit i <;> cases b.testBit (nP + i) <;> cases b.testBit i <;> rfl

set_option maxRecDepth 100000 in
theorem lor_eq (a b : ℕ) : Nat.lor a b = Nat.xor (Nat.xor a b) (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (a ||| b).testBit i = ((a ^^^ b) ^^^ (a &&& b)).testBit i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

set_option maxRecDepth 100000 in
theorem flt0_ok (a b base z : ℕ) (hz : z ∈ opsN a b) (hp : Nat.beq (dz base z) 0 = true) :
    flt0 a b base = true := by
  have hd : dz base z = 0 := Nat.eq_of_beq_eq_true hp
  have e1 : dz base (Nat.land a b) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b)) base) := rfl
  have e2 : dz base (Nat.lor a b) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a) (Nat.xor (Nat.shiftRight b nP) b))
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.lor a b)) base) = Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (sp a) (sp b)) (sp (Nat.land a b))) base)
    rw [show Nat.lor a b = Nat.xor (Nat.xor a b) (Nat.land a b) from lor_eq a b, sp_xor, sp_xor]
  have e3 : dz base (Nat.xor a (Nat.land a b)) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.xor a (Nat.land a b))) base) = Nat.sub allM (Nat.lor (Nat.xor (sp a) (sp (Nat.land a b))) base)
    rw [sp_xor]
  have e4 : dz base (Nat.xor b (Nat.land a b)) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight b nP) b)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.xor b (Nat.land a b))) base) = Nat.sub allM (Nat.lor (Nat.xor (sp b) (sp (Nat.land a b))) base)
    rw [sp_xor]
  unfold flt0
  rw [← e1, ← e2, ← e3, ← e4]
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  have prod : Nat.mul (Nat.mul (dz base (Nat.land a b)) (dz base (Nat.lor a b)))
      (Nat.mul (dz base (Nat.xor a (Nat.land a b))) (dz base (Nat.xor b (Nat.land a b)))) = 0 := by
    change dz base (Nat.land a b) * dz base (Nat.lor a b) *
      (dz base (Nat.xor a (Nat.land a b)) * dz base (Nat.xor b (Nat.land a b))) = 0
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hd, Nat.zero_mul, Nat.zero_mul]
    · rw [hd, Nat.mul_zero, Nat.zero_mul]
    · rw [hd, Nat.zero_mul, Nat.mul_zero]
    · rw [hd, Nat.mul_zero, Nat.mul_zero]
  rw [prod]
  rfl

def fltOK (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) : Prop :=
  ∀ a b base z, z ∈ opsN a b → (Nat.beq (dz base z) 0 = true ∨ 0 < e) → flt a b base = true

set_option maxRecDepth 100000 in
theorem innerK_mono {c : ℕ × List ℕ} (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a : ℕ) :
    ∀ (post : List ℕ) (acc : ℕ) (sk : List ℕ) (tail : List (ℕ × List ℕ)), c ∈ tail →
      c ∈ innerK flt e thr ws a post acc sk tail := by
  intro post
  induction post with
  | nil => intro acc sk tail h; exact h
  | cons b rest ih =>
    intro acc sk tail h
    change c ∈ (Bool.rec (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)
      (mkR thr sk rest (fun r => pairK e thr a b ws r (Nat.lor acc (cutN rest))
        (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)))
      (flt a b (Nat.lor acc (cutN rest))) : List (ℕ × List ℕ))
    rw [brec_eq]
    split
    · obtain ⟨r, _, hk⟩ := mkR_eq thr sk rest
      rw [hk]
      exact pairK_mono _ _ _ _ _ _ _ (ih _ _ _ h)
    · exact ih _ _ _ h

set_option maxRecDepth 100000 in
theorem inner_hit (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a b : ℕ) (Q : ℕ × List ℕ → Prop) :
    ∀ (post : List ℕ) (acc : ℕ) (sk : List ℕ) (tail : List (ℕ × List ℕ)), b ∈ post → accOK acc sk →
      (∀ sk' rest' acc', (b :: (sk' ++ rest')).Perm (sk ++ post) → accOK acc' sk' →
        flt a b (Nat.lor acc' (cutN rest')) = true ∧
        ∀ r : List ℕ, r.Perm (sk' ++ rest') →
          ∃ c, Q c ∧ ∀ tail', c ∈ pairK e thr a b ws r (Nat.lor acc' (cutN rest')) tail') →
      ∃ c, Q c ∧ c ∈ innerK flt e thr ws a post acc sk tail := by
  intro post
  induction post with
  | nil => intro acc sk tail hb; simp at hb
  | cons b0 rest ih =>
    intro acc sk tail hb hacc cb
    have unf : innerK flt e thr ws a (b0 :: rest) acc sk tail =
        (Bool.rec (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail)
          (mkR thr sk rest (fun r => pairK e thr a b0 ws r (Nat.lor acc (cutN rest))
            (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail)))
          (flt a b0 (Nat.lor acc (cutN rest))) : List (ℕ × List ℕ)) := rfl
    by_cases hbb : b = b0
    · subst hbb
      obtain ⟨hf, hall⟩ := cb sk rest acc List.perm_middle.symm hacc
      obtain ⟨r, hr, hk⟩ := mkR_eq thr sk rest
      obtain ⟨c, hq, hc⟩ := hall r hr
      refine ⟨c, hq, ?_⟩
      rw [unf, hf, hk]
      exact hc _
    · have hb' : b ∈ rest := (List.mem_cons.mp hb).resolve_left hbb
      obtain ⟨c, hq, hc⟩ := ih (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail hb'
        (accOK_cons hacc b0) (fun sk' rest' acc' hp ha => cb sk' rest' acc'
          (hp.trans (by simpa using (List.perm_middle (a := b0) (l₁ := sk) (l₂ := rest)).symm)) ha)
      refine ⟨c, hq, ?_⟩
      rw [unf, brec_eq]
      split
      · obtain ⟨r, _, hk⟩ := mkR_eq thr sk rest
        rw [hk]
        exact pairK_mono _ _ _ _ _ _ _ hc
      · exact hc

set_option maxRecDepth 100000 in
theorem outerK_mono {c : ℕ × List ℕ} (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) :
    ∀ (post : List ℕ) (acc : ℕ) (pre : List ℕ) (tail : List (ℕ × List ℕ)), c ∈ tail →
      c ∈ outerK flt e thr ws post acc pre tail := by
  intro post
  induction post with
  | nil => intro acc pre tail h; exact h
  | cons a post ih =>
    intro acc pre tail h
    exact innerK_mono flt e thr ws a post acc pre _ (ih _ _ _ h)

set_option maxRecDepth 100000 in
theorem outer_hit (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a b : ℕ) (Q : ℕ × List ℕ → Prop) :
    ∀ (post : List ℕ) (acc : ℕ) (pre : List ℕ) (tail : List (ℕ × List ℕ)), a ∈ post → b ∈ post → a ≠ b →
      accOK acc pre →
      (∀ x y sk' rest' acc', ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) → (x :: y :: (sk' ++ rest')).Perm (pre ++ post) →
        accOK acc' sk' →
        flt x y (Nat.lor acc' (cutN rest')) = true ∧
        ∀ r : List ℕ, r.Perm (sk' ++ rest') →
          ∃ c, Q c ∧ ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc' (cutN rest')) tail') →
      ∃ c, Q c ∧ c ∈ outerK flt e thr ws post acc pre tail := by
  intro post
  induction post with
  | nil => intro acc pre tail ha; simp at ha
  | cons x0 post ih =>
    intro acc pre tail ha hb hab hacc cb
    have unf : outerK flt e thr ws (x0 :: post) acc pre tail =
        innerK flt e thr ws x0 post acc pre
          (outerK flt e thr ws post (Nat.lor acc (Nat.xor (Nat.shiftRight x0 nP) x0)) (x0 :: pre) tail) := rfl
    rw [unf]
    have pm : ∀ (y : ℕ) (l : List ℕ), (y :: l).Perm (pre ++ post) → (x0 :: y :: l).Perm (pre ++ x0 :: post) :=
      fun y l hp => (hp.cons x0).trans List.perm_middle.symm
    by_cases hax : a = x0
    · subst hax
      have hb' : b ∈ post := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      exact inner_hit flt e thr ws a b Q post acc pre _ hb' hacc
        (fun sk' rest' acc' hp hk => cb a b sk' rest' acc' (Or.inl ⟨rfl, rfl⟩) (pm b _ hp) hk)
    · by_cases hbx : b = x0
      · subst hbx
        have ha' : a ∈ post := (List.mem_cons.mp ha).resolve_left hax
        exact inner_hit flt e thr ws b a Q post acc pre _ ha' hacc
          (fun sk' rest' acc' hp hk => cb b a sk' rest' acc' (Or.inr ⟨rfl, rfl⟩) (pm a _ hp) hk)
      · have ha' : a ∈ post := (List.mem_cons.mp ha).resolve_left hax
        have hb' : b ∈ post := (List.mem_cons.mp hb).resolve_left hbx
        obtain ⟨c, hq, hc⟩ := ih (Nat.lor acc (Nat.xor (Nat.shiftRight x0 nP) x0)) (x0 :: pre) tail ha' hb' hab
          (accOK_cons hacc x0) (fun x y sk' rest' acc' hxy hp hk => cb x y sk' rest' acc' hxy
            (hp.trans (by simpa using (List.perm_middle (a := x0) (l₁ := pre) (l₂ := post)).symm)) hk)
        exact ⟨c, hq, innerK_mono flt e thr ws x0 post acc pre _ hc⟩

def goodKid (e z x y : ℕ) (ws : List ℕ) (kx ky : Bool) (c : ℕ × List ℕ) : Prop :=
  ∃ kept : List ℕ, c = (e - kx.toNat - ky.toNat, z :: kept) ∧ kept.Nodup ∧
    (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) ∧
    kept.length + 2 = ws.length + kx.toNat + ky.toNat

set_option maxRecDepth 100000 in
theorem pair_hit (e thr x y z : ℕ) (ws sk rest : List ℕ) (acc : ℕ) (kx ky : Bool)
    (hz : z ∈ opsN x y) (hthr : thr ≤ z) (hfresh : z ∉ ws) (hnd : ws.Nodup)
    (hperm : (x :: y :: (sk ++ rest)).Perm ws) (hacc : accOK acc sk)
    (slack : kx.toNat + ky.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true)
    (r : List ℕ) (hr : r.Perm (sk ++ rest)) :
    (Nat.beq (dz (Nat.lor acc (cutN rest)) z) 0 = true ∨ 0 < e) ∧
    ∃ c, goodKid e z x y ws kx ky c ∧
      ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc (cutN rest)) tail' := by
  have hperm' : (x :: y :: r).Perm ws := ((hr.cons y).cons x).trans hperm
  have nd := hperm'.nodup_iff.mpr hnd
  have mem : ∀ v, v ∈ ws ↔ v = x ∨ v = y ∨ v ∈ r := by
    intro v; rw [← hperm'.mem_iff]; simp
  have hxy : x ≠ y := by
    intro h; subst h; simp at nd
  have hxr : x ∉ r := by
    intro h; simp only [List.nodup_cons, List.mem_cons, not_or] at nd; exact nd.1.2 h
  have hyr : y ∉ r := by
    intro h; simp only [List.nodup_cons, List.mem_cons, not_or] at nd; exact nd.2.1 h
  have ndr : r.Nodup := by
    simp only [List.nodup_cons] at nd; exact nd.2.2
  have len : ws.length = r.length + 2 := by
    rw [← hperm'.length_eq]; simp
  have rmem : ∀ v, v ∈ r ↔ v ∈ ws ∧ v ≠ x ∧ v ≠ y := by
    intro v
    rw [mem]
    constructor
    · intro h; exact ⟨Or.inr (Or.inr h), fun e => hxr (e ▸ h), fun e => hyr (e ▸ h)⟩
    · rintro ⟨h | h | h, h1, h2⟩
      · exact absurd h h1
      · exact absurd h h2
      · exact h
  have basebit : ∀ (extra : ℕ) (kept : List ℕ),
      (∀ v ∈ kept, v ∈ r ∨ ∀ i, (sp v).testBit i = true → extra.testBit i = true) →
      (∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) →
      Nat.beq (dz (Nat.lor (Nat.lor acc (cutN rest)) extra) z) 0 = true := by
    intro extra kept hk hc
    apply pass_of
    · intro i hi
      obtain ⟨w, hw, hb⟩ := hc i hi
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inl hb
      · right
        change ((acc ||| cutN rest) ||| extra).testBit i = true
        rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true]
        rcases hk w hw with h | h
        · rcases List.mem_append.mp (hr.mem_iff.mp h) with h | h
          · exact Or.inl (Or.inl (hacc.2 w h i hb))
          · exact Or.inl (Or.inr ((cutN_bit rest i).mpr ⟨w, h, hb⟩))
        · exact Or.inr (h i hb)
    · intro i h1 h2
      change ((acc ||| cutN rest) ||| extra).testBit i = true
      rw [Nat.testBit_or, Nat.testBit_or, hacc.1 i h1 h2]
      rfl
  have base0 : ∀ kept : List ℕ, (∀ v ∈ kept, v ∈ r) →
      (∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) →
      Nat.beq (dz (Nat.lor acc (cutN rest)) z) 0 = true := by
    intro kept hk hc
    have h := basebit 0 kept (fun v hv => Or.inl (hk v hv)) hc
    have e0 : Nat.lor (Nat.lor acc (cutN rest)) 0 = Nat.lor acc (cutN rest) := Nat.or_zero _
    rw [e0] at h
    exact h
  cases kx <;> cases ky
  · have kmem : ∀ v, v ∈ r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ false = true) ∨ (v = y ∧ false = true) := by
      intro v; rw [rmem]; simp
    have hp := base0 r (fun v hv => hv) (cut _ kmem)
    refine ⟨Or.inl hp, (e, z :: r), ⟨r, rfl, ndr, kmem, by simp [len]⟩, fun tail' => ?_⟩
    cases e with
    | zero => exact pairZ_hit thr x y z ws r _ tail' hz hthr hfresh hp
    | succ e1 =>
      change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
      apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
      intro t
      rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
      exact cand0_none _ _ _ _ _ _ _ hp
  · obtain ⟨e1, rfl⟩ : ∃ e1, e = e1 + 1 := ⟨e - 1, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ y :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ false = true) ∨ (v = y ∧ true = true) := by
      intro v; rw [List.mem_cons, rmem]; simp; tauto
    have hp := basebit (sp y) (y :: r)
      (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inr (fun i h => h)
        · exact Or.inl hv) (cut _ kmem)
    refine ⟨Or.inr (by omega), (e1, z :: y :: r),
      ⟨y :: r, by simp, List.nodup_cons.mpr ⟨hyr, ndr⟩, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_b _ _ _ _ _ _ _ hp
  · obtain ⟨e1, rfl⟩ : ∃ e1, e = e1 + 1 := ⟨e - 1, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ x :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ true = true) ∨ (v = y ∧ false = true) := by
      intro v; rw [List.mem_cons, rmem]; simp; tauto
    have hp := basebit (sp x) (x :: r)
      (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inr (fun i h => h)
        · exact Or.inl hv) (cut _ kmem)
    refine ⟨Or.inr (by omega), (e1, z :: x :: r),
      ⟨x :: r, by simp, List.nodup_cons.mpr ⟨hxr, ndr⟩, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_a _ _ _ _ _ _ _ hp
  · obtain ⟨e2, rfl⟩ : ∃ e2, e = e2 + 2 := ⟨e - 2, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ x :: y :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ true = true) ∨ (v = y ∧ true = true) := by
      intro v; rw [List.mem_cons, List.mem_cons, rmem]; simp; tauto
    refine ⟨Or.inr (by omega), (e2, z :: x :: y :: r),
      ⟨x :: y :: r, by simp, nd, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_ab _ _ _ _ _ _ _


def run (t : ℕ) : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop
  | av, [] => t ∈ av
  | av, g :: L => g.1 ∈ av ∧ g.2.1 ∈ av ∧ g.1 ≠ g.2.1 ∧ g.2.2 ∈ opsN g.1 g.2.1 ∧ run t (insert g.2.2 av) L

def used (t : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → Prop
  | [], v => v = t
  | g :: L, v => v = g.1 ∨ v = g.2.1 ∨ used t L v

def normal : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop
  | _, [] => True
  | av, g :: L => (∀ g2 ∈ L.head?, ¬(g2.1 ∈ av ∧ g2.2.1 ∈ av ∧ g2.2.2 < g.2.2)) ∧ normal (insert g.2.2 av) L

def tight (t : ℕ) (av : Finset ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  run t av L ∧ ∀ L', run t av L' → L.length ≤ L'.length

set_option maxRecDepth 100000 in
theorem run_drop (t z : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t (insert z av) L → ¬ used t L z →
    run t av L := by
  intro L
  induction L with
  | nil =>
    intro av h hu
    exact (Finset.mem_insert.mp h).resolve_left (fun e => hu e.symm)
  | cons g L ih =>
    intro av h hu
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have u1 : z ≠ g.1 := fun e => hu (Or.inl e)
    have u2 : z ≠ g.2.1 := fun e => hu (Or.inr (Or.inl e))
    refine ⟨(Finset.mem_insert.mp h1).resolve_left (Ne.symm u1), (Finset.mem_insert.mp h2).resolve_left (Ne.symm u2),
      h3, h4, ih _ ?_ (fun u => hu (Or.inr (Or.inr u)))⟩
    rw [Finset.insert_comm]
    exact h5

set_option maxRecDepth 100000 in
theorem tight_tail {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    tight t (insert g.2.2 av) L := by
  refine ⟨h.1.2.2.2.2, fun L' h' => ?_⟩
  have := h.2 (g :: L') ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h'⟩
  simpa using this

set_option maxRecDepth 100000 in
theorem tight_fresh {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    g.2.2 ∉ av := by
  intro hm
  have hr : run t av L := by
    have := h.1.2.2.2.2
    rwa [Finset.insert_eq_of_mem hm] at this
  have := h.2 L hr
  simp at this

set_option maxRecDepth 100000 in
theorem tight_used {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    used t L g.2.2 := by
  by_contra hu
  have := h.2 L (run_drop t g.2.2 L av h.1.2.2.2.2 hu)
  simp at this

set_option maxRecDepth 100000 in
theorem exists_tight {t : ℕ} {av : Finset ℕ} {L : List (ℕ × ℕ × ℕ)} (h : run t av L) :
    ∃ L0, tight t av L0 ∧ L0.length ≤ L.length := by
  classical
  have ex : ∃ n, ∃ L' : List (ℕ × ℕ × ℕ), L'.length = n ∧ run t av L' := ⟨_, L, rfl, h⟩
  obtain ⟨L0, hl, hr⟩ := Nat.find_spec ex
  refine ⟨L0, ⟨hr, fun L' h' => ?_⟩, ?_⟩
  · rw [hl]; exact Nat.find_min' ex ⟨L', rfl, h'⟩
  · rw [hl]; exact Nat.find_min' ex ⟨L, rfl, h⟩

set_option maxRecDepth 100000 in
theorem ins_normal (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (g : ℕ × ℕ × ℕ), g.1 ∈ av → g.2.1 ∈ av →
    g.1 ≠ g.2.1 → g.2.2 ∈ opsN g.1 g.2.1 → run t (insert g.2.2 av) L → normal (insert g.2.2 av) L →
    ∃ L' : List (ℕ × ℕ × ℕ), L'.length = L.length + 1 ∧ run t av L' ∧ normal av L' ∧
      (L'.head? = some g ∨ L'.head? = L.head?) := by
  intro L
  induction L with
  | nil =>
    intro av g h1 h2 h3 h4 hr hn
    exact ⟨[g], rfl, ⟨h1, h2, h3, h4, hr⟩, ⟨by simp, trivial⟩, Or.inl rfl⟩
  | cons g2 Lt ih =>
    intro av g h1 h2 h3 h4 hr hn
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    obtain ⟨n1, n2⟩ := hn
    by_cases c : g2.1 ∈ av ∧ g2.2.1 ∈ av ∧ g2.2.2 < g.2.2
    · have r5' : run t (insert g.2.2 (insert g2.2.2 av)) Lt := by rw [Finset.insert_comm]; exact r5
      have n2' : normal (insert g.2.2 (insert g2.2.2 av)) Lt := by rw [Finset.insert_comm]; exact n2
      obtain ⟨L'', hl, hr'', hn'', hh⟩ := ih (insert g2.2.2 av) g (Finset.mem_insert_of_mem h1)
        (Finset.mem_insert_of_mem h2) h3 h4 r5' n2'
      refine ⟨g2 :: L'', by simp [hl], ⟨c.1, c.2.1, r3, r4, hr''⟩, ⟨?_, hn''⟩, Or.inr rfl⟩
      intro g3 hg3
      rcases hh with hh | hh
      · rw [hh] at hg3
        simp only [Option.mem_def, Option.some.injEq] at hg3
        subst hg3
        exact fun hx => absurd hx.2.2 (Nat.lt_asymm c.2.2)
      · rw [hh] at hg3
        have := n1 g3 hg3
        exact fun hx => this ⟨Finset.mem_insert_of_mem hx.1, Finset.mem_insert_of_mem hx.2.1, hx.2.2⟩
    · refine ⟨g :: g2 :: Lt, rfl, ⟨h1, h2, h3, h4, r1, r2, r3, r4, r5⟩, ⟨?_, n1, n2⟩, Or.inl rfl⟩
      intro g3 hg3
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg3
      subst hg3
      exact c

set_option maxRecDepth 100000 in
theorem sort_normal (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t av L →
    ∃ L' : List (ℕ × ℕ × ℕ), L'.length = L.length ∧ run t av L' ∧ normal av L' := by
  intro L
  induction L with
  | nil => intro av h; exact ⟨[], rfl, h, trivial⟩
  | cons g L ih =>
    intro av h
    obtain ⟨L1, l1, r1, n1⟩ := ih _ h.2.2.2.2
    obtain ⟨L', l', r', n', _⟩ := ins_normal t L1 av g h.1 h.2.1 h.2.2.1 h.2.2.2.1 r1 n1
    exact ⟨L', by simp [l', l1], r', n'⟩

set_option maxRecDepth 100000 in
theorem run_sep (t : ℕ) (D : ℕ → Prop) (hd : D t) (hops : ∀ a b z, z ∈ opsN a b → D z → D a ∨ D b) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t av L → ∃ w ∈ av, used t L w ∧ D w := by
  intro L
  induction L with
  | nil => intro av h; exact ⟨t, h, rfl, hd⟩
  | cons g L ih =>
    intro av h
    obtain ⟨w, hw, hu, hD⟩ := ih _ h.2.2.2.2
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops _ _ _ h.2.2.2.1 hD with d | d
      · exact ⟨g.1, h.1, Or.inl rfl, d⟩
      · exact ⟨g.2.1, h.2.1, Or.inr (Or.inl rfl), d⟩
    · exact ⟨w, hw, Or.inr (Or.inr hu), hD⟩

set_option maxRecDepth 100000 in
theorem ops_sep (i a b z : ℕ) (hz : z ∈ opsN a b) (h : (sp z).testBit i = true) :
    (sp a).testBit i = true ∨ (sp b).testBit i = true := by
  have e1 : ∀ x y : ℕ, Nat.land x y = x &&& y := fun _ _ => rfl
  have e2 : ∀ x y : ℕ, Nat.lor x y = x ||| y := fun _ _ => rfl
  have e3 : ∀ x y : ℕ, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> revert h <;>
    simp only [sp_bit, e1, e2, e3, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit (nP + i) <;> cases a.testBit i <;> cases b.testBit (nP + i) <;> cases b.testBit i <;> decide

set_option maxRecDepth 100000 in
theorem single_of {t : ℕ} {ws : List ℕ} (hn : ws.Nodup) (ht : t ∈ ws) (h : ∀ v ∈ ws, v = t) : ws = [t] := by
  have sub : ws.toFinset ⊆ {t} := by
    intro v hv
    exact Finset.mem_singleton.mpr (h v (List.mem_toFinset.mp hv))
  have c := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn, Finset.card_singleton] at c
  match ws, ht, h, c with
  | [w], _, h, _ => rw [h w (by simp)]
  | w :: w2 :: l, _, _, c => simp at c

set_option maxRecDepth 100000 in
theorem short_of {a b : ℕ} {ws : List ℕ} (ka kb : Bool) (hn : ws.Nodup)
    (h : ∀ v ∈ ws, (v = a ∧ ka = false) ∨ (v = b ∧ kb = false)) : ws.length + ka.toNat + kb.toNat ≤ 2 := by
  have sub : ws.toFinset ⊆ (if ka = false then {a} else ∅) ∪ (if kb = false then {b} else ∅) := by
    intro v hv
    rcases h v (List.mem_toFinset.mp hv) with ⟨rfl, k⟩ | ⟨rfl, k⟩ <;> simp [k]
  have c := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn] at c
  have u := Finset.card_union_le (if ka = false then ({a} : Finset ℕ) else ∅) (if kb = false then {b} else ∅)
  cases ka <;> cases kb <;> simp at c u ⊢ <;> omega

set_option maxRecDepth 100000 in
theorem frontier_card (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ), tight t av L → ws.Nodup →
    (∀ v ∈ ws, v ∈ av ∧ used t L v) → ws.length ≤ L.length + 1 := by
  intro L
  induction L with
  | nil =>
    intro av ws _ hn hm
    cases ws with
    | nil => simp
    | cons w l =>
      have e := single_of hn ((hm w (by simp)).2 ▸ List.mem_cons_self) (fun v hv => (hm v hv).2)
      rw [e]; simp
  | cons g L ih =>
    intro av ws ht hn hm
    classical
    have hz : g.2.2 ∉ ws := fun h => tight_fresh ht (hm _ h).1
    have c1 := ih (insert g.2.2 av) (g.2.2 :: ws.filter (fun v => decide (used t L v))) (tight_tail ht)
      (List.nodup_cons.mpr ⟨fun h => hz (List.mem_filter.mp h).1, hn.filter _⟩)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨Finset.mem_insert_self _ _, tight_used ht⟩
        · have := List.mem_filter.mp hv
          exact ⟨Finset.mem_insert_of_mem (hm v this.1).1, of_decide_eq_true this.2⟩)
    have c2 := short_of (a := g.1) (b := g.2.1) false false
      (hn.filter (fun v => !decide (used t L v)))
      (by
        intro v hv
        have hv' := List.mem_filter.mp hv
        have nu : ¬ used t L v := by simpa using hv'.2
        rcases (hm v hv'.1).2 with e | e | e
        · exact Or.inl ⟨e, rfl⟩
        · exact Or.inr ⟨e, rfl⟩
        · exact absurd e nu)
    have c3 := List.length_eq_length_filter_add (l := ws) (fun v => decide (used t L v))
    simp only [List.length_cons, Bool.toNat_false] at c1 c2 ⊢
    omega

set_option maxRecDepth 100000 in
theorem step_child (t : ℕ) (hD : ∀ i < nP, (sp t).testBit i = true) (av : Finset ℕ) (g : ℕ × ℕ × ℕ)
    (L' : List (ℕ × ℕ × ℕ)) (ws : List ℕ) (e k : ℕ) (ht : tight t av (g :: L')) (hl : L'.length ≤ k)
    (hn : ws.Nodup) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t (g :: L') v) (he : e + ws.length = k + 2) :
    ∃ ka kb : Bool, ka.toNat + kb.toNat ≤ e ∧ g.1 ∈ ws ∧ g.2.1 ∈ ws ∧ g.2.2 ∉ ws ∧
      ∀ kept : List ℕ,
        (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ g.1 ∧ v ≠ g.2.1) ∨ (v = g.1 ∧ ka = true) ∨ (v = g.2.1 ∧ kb = true)) →
        (∀ i < nP, ∃ w ∈ g.2.2 :: kept, (sp w).testBit i = true) ∧
        (kept.Nodup → (g.2.2 :: kept).Nodup) ∧
        (∀ v, v ∈ g.2.2 :: kept ↔ v ∈ insert g.2.2 av ∧ used t L' v) := by
  classical
  have ha : g.1 ∈ ws := (hm _).mpr ⟨ht.1.1, Or.inl rfl⟩
  have hb : g.2.1 ∈ ws := (hm _).mpr ⟨ht.1.2.1, Or.inr (Or.inl rfl)⟩
  have hz : g.2.2 ∉ ws := fun h => tight_fresh ht ((hm _).mp h).1
  refine ⟨decide (used t L' g.1), decide (used t L' g.2.1), ?_, ha, hb, hz, ?_⟩
  · have c1 := frontier_card t L' (insert g.2.2 av) (g.2.2 :: ws.filter (fun v => decide (used t L' v)))
      (tight_tail ht) (List.nodup_cons.mpr ⟨fun h => hz (List.mem_filter.mp h).1, hn.filter _⟩)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨Finset.mem_insert_self _ _, tight_used ht⟩
        · have := List.mem_filter.mp hv
          exact ⟨Finset.mem_insert_of_mem ((hm v).mp this.1).1, of_decide_eq_true this.2⟩)
    have c2 := short_of (a := g.1) (b := g.2.1) (decide (used t L' g.1)) (decide (used t L' g.2.1))
      (hn.filter (fun v => !decide (used t L' v)))
      (by
        intro v hv
        have hv' := List.mem_filter.mp hv
        have nu : ¬ used t L' v := by simpa using hv'.2
        rcases ((hm v).mp hv'.1).2 with e | e | e
        · exact Or.inl ⟨e, by rw [← e]; simpa using nu⟩
        · exact Or.inr ⟨e, by rw [← e]; simpa using nu⟩
        · exact absurd e nu)
    have c3 := List.length_eq_length_filter_add (l := ws) (fun v => decide (used t L' v))
    simp only [List.length_cons] at c1
    omega
  · intro kept hk
    have key : ∀ v, v ∈ kept ↔ v ∈ av ∧ used t L' v := by
      intro v
      rw [hk v]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
        · have := (hm v).mp h1
          rcases this.2 with e | e | e
          · exact absurd e h2
          · exact absurd e h3
          · exact ⟨this.1, e⟩
        · exact ⟨ht.1.1, of_decide_eq_true h⟩
        · exact ⟨ht.1.2.1, of_decide_eq_true h⟩
      · rintro ⟨h1, h2⟩
        by_cases e1 : v = g.1
        · exact Or.inr (Or.inl ⟨e1, by rw [← e1]; exact decide_eq_true h2⟩)
        · by_cases e2 : v = g.2.1
          · exact Or.inr (Or.inr ⟨e2, by rw [← e2]; exact decide_eq_true h2⟩)
          · exact Or.inl ⟨(hm v).mpr ⟨h1, Or.inr (Or.inr h2)⟩, e1, e2⟩
    have mem : ∀ v, v ∈ g.2.2 :: kept ↔ v ∈ insert g.2.2 av ∧ used t L' v := by
      intro v
      rw [List.mem_cons, key v, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, tight_used ht⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun hkn => List.nodup_cons.mpr ⟨fun h => tight_fresh ht ((key _).mp h).1, hkn⟩, mem⟩
    obtain ⟨w, hw, hu, hb⟩ := run_sep t (fun w => (sp w).testBit i = true) (hD i hi)
      (fun a b z hz h => ops_sep i a b z hz h) L' _ ht.1.2.2.2.2
    exact ⟨w, (mem w).mpr ⟨hw, hu⟩, hb⟩

set_option maxRecDepth 100000 in
theorem goodKid_swap {e z x y : ℕ} {ws : List ℕ} {kx ky : Bool} {c : ℕ × List ℕ}
    (h : goodKid e z y x ws ky kx c) : goodKid e z x y ws kx ky c := by
  obtain ⟨kept, rfl, h1, h2, h3⟩ := h
  refine ⟨kept, by rw [Nat.sub_right_comm], h1, fun v => (h2 v).trans (by tauto), by omega⟩

set_option maxRecDepth 100000 in
theorem cut_swap {z x y : ℕ} {ws : List ℕ} {kx ky : Bool}
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ y ∧ v ≠ x) ∨ (v = y ∧ ky = true) ∨ (v = x ∧ kx = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true :=
  fun kept hk => cut kept (fun v => (hk v).trans (by tauto))

set_option maxRecDepth 100000 in
theorem flt0_OK : fltOK flt0 0 := fun a b base z hz hp => flt0_ok a b base z hz (hp.resolve_right (by simp))

set_option maxRecDepth 100000 in
theorem fltT_OK (e : ℕ) : fltOK fltT e := fun _ _ _ _ _ _ => rfl

set_option maxRecDepth 100000 in
theorem pair_cb {e : ℕ} (flt : ℕ → ℕ → ℕ → Bool) (hflt : fltOK flt e) (thr x y z : ℕ) (ws sk rest : List ℕ) (acc : ℕ)
    (kx ky : Bool) (hz : z ∈ opsN x y) (hthr : thr ≤ z) (hfresh : z ∉ ws) (hnd : ws.Nodup)
    (hperm : (x :: y :: (sk ++ rest)).Perm ws) (hacc : accOK acc sk) (slack : kx.toNat + ky.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    flt x y (Nat.lor acc (cutN rest)) = true ∧
    ∀ r : List ℕ, r.Perm (sk ++ rest) →
      ∃ c, goodKid e z x y ws kx ky c ∧
        ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc (cutN rest)) tail' :=
  ⟨hflt x y _ z hz (pair_hit e thr x y z ws sk rest acc kx ky hz hthr hfresh hnd hperm hacc slack cut (sk ++ rest)
      (List.Perm.refl _)).1,
    fun r hr => (pair_hit e thr x y z ws sk rest acc kx ky hz hthr hfresh hnd hperm hacc slack cut r hr).2⟩

set_option maxRecDepth 100000 in
theorem bit_of_ne (p : ℕ) (hp : p ≠ 0) : ∃ i, p.testBit i = true := by
  by_contra hn
  apply hp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  cases hb : p.testBit i
  · rfl
  · exact absurd ⟨i, hb⟩ hn

set_option maxRecDepth 100000 in
theorem crossC_wit : ∀ (ws : List ℕ) (p q : ℕ), crossC ws p q = true →
    ∃ i j, p.testBit i = true ∧ q.testBit j = true ∧ ∀ w ∈ ws, w.testBit i = w.testBit (nP + j) := by
  intro ws
  induction ws with
  | nil =>
    intro p q h
    change (Bool.rec (Bool.rec true false (Nat.beq q 0)) false (Nat.beq p 0) : Bool) = true at h
    have hp : p ≠ 0 := by
      intro e
      subst e
      exact Bool.noConfusion (show false = true from h)
    have hq : q ≠ 0 := by
      intro e
      subst e
      cases hb : Nat.beq p 0
      · rw [hb] at h
        exact Bool.noConfusion (show false = true from h)
      · rw [hb] at h
        exact Bool.noConfusion (show false = true from h)
    obtain ⟨i, hi⟩ := bit_of_ne p hp
    obtain ⟨j, hj⟩ := bit_of_ne q hq
    exact ⟨i, j, hi, hj, by simp⟩
  | cons w ws ih =>
    intro p q h
    change (Bool.rec (Bool.rec (Bool.rec (crossC ws (Nat.xor p (Nat.land p w))
      (Nat.xor q (Nat.land q (Nat.shiftRight w nP)))) true (crossC ws (Nat.land p w) (Nat.land q (Nat.shiftRight w nP))))
      false (Nat.beq q 0)) false (Nat.beq p 0) : Bool) = true at h
    cases hp : Nat.beq p 0
    · rw [hp] at h
      cases hq : Nat.beq q 0
      · rw [hq] at h
        cases h1 : crossC ws (Nat.land p w) (Nat.land q (Nat.shiftRight w nP))
        · rw [h1] at h
          have h0 : crossC ws (Nat.xor p (Nat.land p w)) (Nat.xor q (Nat.land q (Nat.shiftRight w nP))) = true := h
          obtain ⟨i, j, pi, qj, hall⟩ := ih _ _ h0
          change (p ^^^ (p &&& w)).testBit i = true at pi
          change (q ^^^ (q &&& (w >>> nP))).testBit j = true at qj
          rw [Nat.testBit_xor, Nat.testBit_and] at pi
          rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight] at qj
          have pi' : p.testBit i = true ∧ w.testBit i = false := by
            revert pi; cases p.testBit i <;> cases w.testBit i <;> decide
          have qj' : q.testBit j = true ∧ w.testBit (nP + j) = false := by
            revert qj; cases q.testBit j <;> cases w.testBit (nP + j) <;> decide
          refine ⟨i, j, pi'.1, qj'.1, fun v hv => ?_⟩
          rcases List.mem_cons.mp hv with ev | hv
          · rw [ev, pi'.2, qj'.2]
          · exact hall v hv
        · obtain ⟨i, j, pi, qj, hall⟩ := ih _ _ h1
          change (p &&& w).testBit i = true at pi
          change (q &&& (w >>> nP)).testBit j = true at qj
          rw [Nat.testBit_and, Bool.and_eq_true] at pi
          rw [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true] at qj
          refine ⟨i, j, pi.1, qj.1, fun v hv => ?_⟩
          rcases List.mem_cons.mp hv with ev | hv
          · rw [ev, pi.2, qj.2]
          · exact hall v hv
      · rw [hq] at h
        exact Bool.noConfusion (show false = true from h)
    · rw [hp] at h
      exact Bool.noConfusion (show false = true from h)

set_option maxRecDepth 100000 in
theorem ops_diff (i j a b z : ℕ) (hz : z ∈ opsN a b) (h : z.testBit i ≠ z.testBit j) :
    a.testBit i ≠ a.testBit j ∨ b.testBit i ≠ b.testBit j := by
  have e1 : ∀ x y : ℕ, Nat.land x y = x &&& y := fun _ _ => rfl
  have e2 : ∀ x y : ℕ, Nat.lor x y = x ||| y := fun _ _ => rfl
  have e3 : ∀ x y : ℕ, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> revert h <;>
    simp only [e1, e2, e3, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases a.testBit j <;> cases b.testBit i <;> cases b.testBit j <;> decide

set_option maxRecDepth 100000 in
theorem coll_ok (c t : ℕ) (ht : t = hiM ∨ t = fullM) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ)
    (hr : run t av L) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t L v) : collOK c ws = true := by
  cases c with
  | zero => rfl
  | succ c =>
    change (Bool.rec true false (crossC ws fullM fullM) : Bool) = true
    cases hc : crossC ws fullM fullM
    · rfl
    · exfalso
      obtain ⟨i, j, pi, qj, hall⟩ := crossC_wit ws fullM fullM hc
      have hi : i < nP := by
        rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one] at pi
        exact of_decide_eq_true pi
      have hj : j < nP := by
        rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one] at qj
        exact of_decide_eq_true qj
      have hd : t.testBit i ≠ t.testBit (nP + j) := by
        rcases ht with rfl | rfl
        · rw [hiM_bit (nP + j) (Nat.le_add_right _ _) (by omega),
            show hiM = (2 ^ nP - 1) <<< nP from rfl, Nat.testBit_shiftLeft]
          have : ¬ (i ≥ nP) := by omega
          simp [this]
        · rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
          have : ¬ (nP + j < nP) := by omega
          simp [hi, this]
      obtain ⟨w, hw, hu, hD⟩ := run_sep t (fun w => w.testBit i ≠ w.testBit (nP + j)) hd
        (fun a b z hz h => ops_diff i (nP + j) a b z hz h) L av hr
      exact hD (hall w ((hm w).mpr ⟨hw, hu⟩))

set_option maxRecDepth 100000 in
theorem kidsG_hit (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) (hflt : fltOK flt e) (h : ℕ) (tl : List ℕ) (a b z : ℕ)
    (ka kb : Bool) (hn : (h :: tl).Nodup)
    (ha : a ∈ h :: tl) (hb : b ∈ h :: tl) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (ord : a = h ∨ b = h ∨ h ≤ z) (fresh : z ∉ h :: tl) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ h :: tl ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b (h :: tl) ka kb c ∧ c ∈ kidsG flt e h tl (h :: tl) := by
  unfold kidsG
  by_cases hah : a = h
  · subst hah
    have hb' : b ∈ tl := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
    exact inner_hit flt e 0 (a :: tl) a b _ tl hiM [] _ hb' accOK_nil
      (fun sk' rest' acc' hp hk => pair_cb flt hflt 0 a b z (a :: tl) sk' rest' acc' ka kb hz (Nat.zero_le _)
        fresh hn (by simpa using hp.cons a) hk slack cut)
  · by_cases hbh : b = h
    · subst hbh
      have ha' : a ∈ tl := (List.mem_cons.mp ha).resolve_left hah
      obtain ⟨c, hq, hc⟩ := inner_hit flt e 0 (b :: tl) b a (goodKid e z b a (b :: tl) kb ka) tl hiM [] _ ha'
        accOK_nil
        (fun sk' rest' acc' hp hk => pair_cb flt hflt 0 b a z (b :: tl) sk' rest' acc' kb ka (opsN_swap hz)
          (Nat.zero_le _) fresh hn (by simpa using hp.cons b) hk (by omega) (cut_swap cut))
      exact ⟨c, goodKid_swap hq, hc⟩
    · have ha' : a ∈ tl := (List.mem_cons.mp ha).resolve_left hah
      have hb' : b ∈ tl := (List.mem_cons.mp hb).resolve_left hbh
      have hz' : h ≤ z := by
        rcases ord with o | o | o
        · exact absurd o hah
        · exact absurd o hbh
        · exact o
      obtain ⟨c, hq, hc⟩ := outer_hit flt e h (h :: tl) a b (goodKid e z a b (h :: tl) ka kb) tl
        (Nat.lor hiM (Nat.xor (Nat.shiftRight h nP) h)) [h] [] ha' hb' hab (accOK_cons accOK_nil h)
        (fun x y sk' rest' acc' hxy hp hk => by
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact pair_cb flt hflt h x y z (h :: tl) sk' rest' acc' ka kb hz hz' fresh hn (by simpa using hp) hk
              slack cut
          · obtain ⟨f1, hall⟩ := pair_cb flt hflt h x y z (h :: tl) sk' rest' acc' kb ka (opsN_swap hz) hz'
              fresh hn (by simpa using hp) hk (by omega) (cut_swap cut)
            exact ⟨f1, fun r hr => by
              obtain ⟨c, hq, hc⟩ := hall r hr
              exact ⟨c, goodKid_swap hq, hc⟩⟩)
      exact ⟨c, hq, innerK_mono flt e 0 (h :: tl) h tl hiM [] _ hc⟩

set_option maxRecDepth 100000 in
theorem kids_hit (e h : ℕ) (tl : List ℕ) (a b z : ℕ) (ka kb : Bool) (hn : (h :: tl).Nodup)
    (ha : a ∈ h :: tl) (hb : b ∈ h :: tl) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (ord : a = h ∨ b = h ∨ h ≤ z) (fresh : z ∉ h :: tl) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ h :: tl ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b (h :: tl) ka kb c ∧ c ∈ kids e (h :: tl) := by
  cases e with
  | zero => exact kidsG_hit flt0 0 flt0_OK h tl a b z ka kb hn ha hb hab hz ord fresh slack cut
  | succ e1 =>
    obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ :=
      kidsG_hit fltT (e1 + 1) (fltT_OK _) h tl a b z ka kb hn ha hb hab hz ord fresh slack cut
    obtain ⟨kept', hp, hm⟩ := canonMap_hit _ _ _ _ hc
    exact ⟨_, ⟨kept', rfl, hp.nodup_iff.mpr hkn, fun v => hp.mem_iff.trans (hkm v), by rw [hp.length_eq]; exact hkl⟩, hm⟩

set_option maxRecDepth 100000 in
theorem rootRaw_hit (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) (hflt : fltOK flt e) (ws : List ℕ) (a b z : ℕ) (ka kb : Bool)
    (hn : ws.Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (fresh : z ∉ ws) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b ws ka kb c ∧ c ∈ outerK flt e 0 ws ws hiM [] [] := by
  exact outer_hit flt e 0 ws a b (goodKid e z a b ws ka kb) ws hiM [] [] ha hb hab accOK_nil
    (fun x y sk' rest' acc' hxy hp hk => by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact pair_cb flt hflt 0 x y z ws sk' rest' acc' ka kb hz (Nat.zero_le _) fresh hn (by simpa using hp) hk
          slack cut
      · obtain ⟨f1, hall⟩ := pair_cb flt hflt 0 x y z ws sk' rest' acc' kb ka (opsN_swap hz) (Nat.zero_le _)
          fresh hn (by simpa using hp) hk (by omega) (cut_swap cut)
        exact ⟨f1, fun r hr => by
          obtain ⟨c, hq, hc⟩ := hall r hr
          exact ⟨c, goodKid_swap hq, hc⟩⟩)

set_option maxRecDepth 100000 in
theorem kidsRoot_hit (e : ℕ) (ws : List ℕ) (a b z : ℕ) (ka kb : Bool) (hn : ws.Nodup)
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (fresh : z ∉ ws) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b ws ka kb c ∧ c ∈ kidsRoot e ws := by
  have key : ∃ flt : ℕ → ℕ → ℕ → Bool, fltOK flt e ∧ kidsRoot e ws = canonMap (outerK flt e 0 ws ws hiM [] []) := by
    cases e with
    | zero => exact ⟨flt0, flt0_OK, rfl⟩
    | succ e1 => exact ⟨fltT, fltT_OK _, rfl⟩
  obtain ⟨flt, hflt, hk⟩ := key
  rw [hk]
  obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := rootRaw_hit flt e hflt ws a b z ka kb hn ha hb hab hz fresh slack cut
  obtain ⟨kept', hp, hm⟩ := canonMap_hit _ _ _ _ hc
  exact ⟨_, ⟨kept', rfl, hp.nodup_iff.mpr hkn, fun v => hp.mem_iff.trans (hkm v), by rw [hp.length_eq]; exact hkl⟩, hm⟩

set_option maxRecDepth 100000 in
theorem isGoal_single (t : ℕ) (h : t = hiM ∨ t = fullM) : isGoal [t] = true := by
  change (Bool.rec (Nat.beq t fullM) true (Nat.beq t hiM) : Bool) = true
  rcases h with rfl | rfl
  · rw [Nat.beq_refl]
  · rw [Nat.beq_refl]; cases Nat.beq fullM hiM <;> rfl

set_option maxRecDepth 100000 in
theorem anyK_of_mem (f : ℕ → List ℕ → Bool) : ∀ (l : List (ℕ × List ℕ)) (c : ℕ × List ℕ), c ∈ l →
    f c.1 c.2 = true → anyK f l = true := by
  intro l
  induction l with
  | nil => intro c hc; simp at hc
  | cons d l ih =>
    intro c hc h
    change (Bool.rec (anyK f l) true (f d.1 d.2) : Bool) = true
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [h]
    · cases f d.1 d.2
      · exact ih c hc h
      · rfl

set_option maxRecDepth 100000 in
theorem node_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true) :
    ∀ (k : ℕ) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (h : ℕ) (tl : List ℕ) (e : ℕ), tight t av L → normal av L →
      L.length ≤ k → (h :: tl).Nodup → (∀ v, v ∈ h :: tl ↔ v ∈ av ∧ used t L v) → e + (tl.length + 1) = k + 1 →
      (∀ g ∈ L.head?, g.1 = h ∨ g.2.1 = h ∨ h ≤ g.2.2) → node c k e (h :: tl) = true := by
  intro k
  induction k with
  | zero =>
    intro L av h tl e hti _ hl hn hm _ _
    have hL : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst hL
    have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
    rw [e1]
    exact isGoal_single t ht
  | succ k ih =>
    intro L av h tl e hti hno hl hn hm he ho
    change (Bool.rec (Bool.rec false (anyK (node c k) (kids e (h :: tl))) (collOK c (h :: tl))) true
      (isGoal (h :: tl)) : Bool) = true
    cases hg : isGoal (h :: tl)
    · rw [coll_ok c t ht L av (h :: tl) hti.1 hm]
      change anyK (node c k) (kids e (h :: tl)) = true
      cases L with
      | nil =>
        have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
        rw [e1, isGoal_single t ht] at hg
        exact absurd hg (by simp)
      | cons g L' =>
        obtain ⟨ka, kb, slack, ha, hb, hz, hkept⟩ := step_child t hD av g L' (h :: tl) e k hti
          (by simpa using hl) hn hm (by simp only [List.length_cons]; omega)
        obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := kids_hit e h tl g.1 g.2.1 g.2.2 ka kb hn ha hb hti.1.2.2.1
          hti.1.2.2.2.1 (ho g (by simp)) hz slack (fun kept hk => (hkept kept hk).1)
        apply anyK_of_mem _ _ _ hc
        obtain ⟨_, hnd, hmem⟩ := hkept kept hkm
        apply ih L' (insert g.2.2 av) g.2.2 kept _ (tight_tail hti) hno.2 (by simpa using hl) (hnd hkn) hmem
        · simp only [List.length_cons] at hkl
          omega
        · intro g2 hg2
          have nn := hno.1 g2 hg2
          cases L' with
          | nil => simp at hg2
          | cons g2' L'' =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg2
            subst hg2
            have r := hti.1.2.2.2.2
            by_cases c1 : g2'.1 = g.2.2
            · exact Or.inl c1
            · by_cases c2 : g2'.2.1 = g.2.2
              · exact Or.inr (Or.inl c2)
              · right; right
                apply Nat.le_of_not_lt
                intro lt
                exact nn ⟨(Finset.mem_insert.mp r.1).resolve_left c1, (Finset.mem_insert.mp r.2.1).resolve_left c2, lt⟩
    · rfl

set_option maxRecDepth 100000 in
theorem root_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true)
    (k : ℕ) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ) (e : ℕ) (hti : tight t av L) (hno : normal av L)
    (hl : L.length ≤ k + 1) (hn : ws.Nodup) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t L v)
    (he : e + ws.length = k + 2) : root c k e ws = true := by
  change (Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws) : Bool) = true
  cases hg : isGoal ws
  · change anyK (node c k) (kidsRoot e ws) = true
    cases L with
    | nil =>
      have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
      rw [e1, isGoal_single t ht] at hg
      exact absurd hg (by simp)
    | cons g L' =>
      obtain ⟨ka, kb, slack, ha, hb, hz, hkept⟩ := step_child t hD av g L' ws e k hti
        (by simpa using hl) hn hm he
      obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := kidsRoot_hit e ws g.1 g.2.1 g.2.2 ka kb hn ha hb hti.1.2.2.1
        hti.1.2.2.2.1 hz slack (fun kept hk => (hkept kept hk).1)
      apply anyK_of_mem _ _ _ hc
      obtain ⟨_, hnd, hmem⟩ := hkept kept hkm
      apply node_complete c t ht hD k L' (insert g.2.2 av) g.2.2 kept _ (tight_tail hti) hno.2 (by simpa using hl)
        (hnd hkn) hmem
      · omega
      · intro g2 hg2
        have nn := hno.1 g2 hg2
        cases L' with
        | nil => simp at hg2
        | cons g2' L'' =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg2
          subst hg2
          have r := hti.1.2.2.2.2
          by_cases c1 : g2'.1 = g.2.2
          · exact Or.inl c1
          · by_cases c2 : g2'.2.1 = g.2.2
            · exact Or.inr (Or.inl c2)
            · right; right
              apply Nat.le_of_not_lt
              intro lt
              exact nn ⟨(Finset.mem_insert.mp r.1).resolve_left c1, (Finset.mem_insert.mp r.2.1).resolve_left c2, lt⟩
  · rfl

set_option maxRecDepth 100000 in
theorem searchN_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true)
    (k : ℕ) (inputs : List ℕ) (hn : inputs.Nodup) (L : List (ℕ × ℕ × ℕ)) (hr : run t inputs.toFinset L)
    (hl : L.length ≤ k + 1) : searchN c k inputs = true := by
  classical
  obtain ⟨L0, ht0, hl0⟩ := exists_tight hr
  obtain ⟨L1, l1, r1, n1⟩ := sort_normal t L0 _ ht0.1
  have ht1 : tight t inputs.toFinset L1 := ⟨r1, fun L' h' => l1 ▸ ht0.2 L' h'⟩
  let ws := inputs.filter (fun v => decide (used t L1 v))
  have hm : ∀ v, v ∈ ws ↔ v ∈ inputs.toFinset ∧ used t L1 v := by
    intro v; simp [ws]
  have hnd : ws.Nodup := hn.filter _
  have hc := frontier_card t L1 _ ws ht1 hnd (fun v hv => (hm v).mp hv)
  have hcut : cutFull ws = true := by
    have le : allM ≤ cutN ws ||| hiM := by
      apply ge_of_bits
      intro i hi
      rw [Nat.testBit_or, Bool.or_eq_true]
      by_cases c : i < nP
      · left
        obtain ⟨w, hw, hu, hb⟩ := run_sep t (fun w => (sp w).testBit i = true) (hD i c)
          (fun a b z hz h => ops_sep i a b z hz h) L1 _ r1
        exact (cutN_bit ws i).mpr ⟨w, (hm w).mpr ⟨hw, hu⟩, hb⟩
      · exact Or.inr (hiM_bit i (by omega) hi)
    have z0 : Nat.sub allM (Nat.lor (cutN ws) hiM) = 0 := Nat.sub_eq_zero_of_le le
    unfold cutFull
    rw [z0]
    rfl
  have hroot := root_complete c t ht hD k L1 _ ws (k + 2 - ws.length) ht1 n1 (by omega) hnd hm (by omega)
  unfold searchN
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr List.filter_sublist,
    by simp [hcut, hroot]; omega⟩

set_option maxRecDepth 100000 in
theorem anyK_append_false (f : ℕ → List ℕ → Bool) : ∀ l1 l2 : List (ℕ × List ℕ), anyK f l1 = false →
    anyK f l2 = false → anyK f (l1 ++ l2) = false := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2; exact h2
  | cons d l1 ih =>
    intro l2 h1 h2
    change (Bool.rec (anyK f l1) true (f d.1 d.2) : Bool) = false at h1
    change (Bool.rec (anyK f (l1 ++ l2)) true (f d.1 d.2) : Bool) = false
    cases hd : f d.1 d.2
    · rw [hd] at h1
      exact ih l2 h1 h2
    · rw [hd] at h1
      exact absurd h1 (by simp)

set_option maxRecDepth 100000 in
theorem chainK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (i d j : ℕ) (hj : i + d = j)
    (h1 : anyK f ((l.drop i).take d) = false) (h2 : anyK f (l.drop j) = false) : anyK f (l.drop i) = false := by
  subst hj
  have h := anyK_append_false f ((l.drop i).take d) ((l.drop i).drop d) h1 (by rw [List.drop_drop]; exact h2)
  rwa [List.take_append_drop] at h

set_option maxRecDepth 100000 in
theorem startK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (h : anyK f (l.drop 0) = false) :
    anyK f l = false := by
  simpa using h

set_option maxRecDepth 100000 in
theorem takeOneK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (h : f (hdK l).1 (hdK l).2 = false) :
    anyK f (l.take 1) = false := by
  cases l with
  | nil => rfl
  | cons c l =>
    change f c.1 c.2 = false at h
    change (Bool.rec false true (f c.1 c.2) : Bool) = false
    rw [h]

set_option maxRecDepth 100000 in
theorem node_split (c k e : ℕ) (ws : List ℕ) (hg : isGoal ws = false) (h : anyK (node c k) (kids e ws) = false) :
    node c (k + 1) e ws = false := by
  change (Bool.rec (Bool.rec false (anyK (node c k) (kids e ws)) (collOK c ws)) true (isGoal ws) : Bool) = false
  rw [hg, h]
  cases collOK c ws <;> rfl

set_option maxRecDepth 100000 in
theorem root_split (c k e : ℕ) (ws : List ℕ) (hg : isGoal ws = false) (h : anyK (node c k) (kidsRoot e ws) = false) :
    root c k e ws = false := by
  change (Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws) : Bool) = false
  rw [hg]
  exact h

set_option maxRecDepth 100000 in
theorem toNat_ops (a b z : W) (hz : z ∈ ops a b) : z.toNat ∈ opsN a.toNat b.toNat := by
  have e : ∀ x y : W, x &&& ~~~y = x ^^^ (x &&& y) := by
    intro x y
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false]
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (BitVec.toNat_and a b)
  · exact Or.inr (Or.inl (BitVec.toNat_or a b))
  · right; right; left
    rw [e, BitVec.toNat_xor, BitVec.toNat_and]; rfl
  · right; right; right
    rw [e, BitVec.toNat_xor, BitVec.toNat_and, Nat.and_comm]; rfl

set_option maxRecDepth 100000 in
theorem run_of_build (t : W) : ∀ (k : ℕ) (av : Finset W), build basicOps t k av →
    ∃ L : List (ℕ × ℕ × ℕ), L.length ≤ k ∧ run t.toNat (av.image BitVec.toNat) L := by
  intro k
  induction k with
  | zero => intro av h; exact ⟨[], Nat.le_refl _, Finset.mem_image_of_mem _ h⟩
  | succ k ih =>
    intro av h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨L, hl, hr⟩ := ih av skip
      exact ⟨L, by omega, hr⟩
    · obtain ⟨L, hl, hr⟩ := ih _ tail
      rw [Finset.image_insert] at hr
      exact ⟨(a.toNat, b.toNat, z.toNat) :: L, by simp only [List.length_cons]; omega,
        Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, fun e => hab (BitVec.eq_of_toNat_eq e),
        toNat_ops a b z (List.mem_toFinset.mp hz), hr⟩

set_option maxRecDepth 100000 in
theorem low_bits (x : ℕ) (h : Nat.land x fullM = fullM) : ∀ i < nP, x.testBit i = true := by
  intro i hi
  have e := congrArg (fun y => Nat.testBit y i) h
  change (x &&& (2 ^ nP - 1)).testBit i = (2 ^ nP - 1).testBit i at e
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one] at e
  simpa [hi] using e

end Fast

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem bound_from_searchN (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : searchN 0 8 (inputs.map BitVec.toNat) = false)
    (g1 : goal.toNat = hiM) (g2 : (~~~goal).toNat = fullM)
    (d1 : Nat.land (sp hiM) fullM = fullM) (d2 : Nat.land (sp fullM) fullM = fullM)
    (sample : ∀ k : Fin 2048, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 2048) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run0⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  obtain ⟨L, hl, hr⟩ := run_of_build t 9 _ (lift low run0)
  have himg : inputs.toFinset.image BitVec.toNat = (inputs.map BitVec.toNat).toFinset := by
    ext v; simp
  rw [himg] at hr
  have ht' : t.toNat = hiM ∨ t.toNat = fullM := by
    rcases ht with rfl | rfl
    · exact Or.inl g1
    · exact Or.inr g2
  have hD : ∀ i < nP, (sp t.toNat).testBit i = true := by
    rcases ht' with e | e <;> rw [e]
    · exact low_bits _ d1
    · exact low_bits _ d2
  have fin := searchN_complete 0 t.toNat ht' hD 8 (inputs.map BitVec.toNat)
    ((List.nodup_map_iff (fun _ _ h => BitVec.eq_of_toNat_eq h)).mpr nd) L hr hl
  exact Bool.noConfusion (reject.symm.trans fin)

def r0 : W := 0x11004000104040#64 ++ 0x538100020c00924d#64 ++ 0x1020001048c22#64 ++ 0x1021060402062402#64 ++ 0x51001014001d0488#64 ++ 0x1401400a02232#64 ++ 0x2242900000022#64 ++ 0x2504005811487028#64 ++ 0x4268c000a400041#64 ++ 0x2000028301458001#64 ++ 0x404009804200006#64 ++ 0xb8800d0041900200#64 ++ 0x801008040008#64 ++ 0xc100c303010c001#64 ++ 0x2003000880200#64 ++ 0x11004000104040#64 ++ 0xfbffe78d3fafdf8e#64 ++ 0xd7e4dfadc7dc7eff#64 ++ 0xea7f7f1d579c5cb9#64 ++ 0xd7ddfdfe14fcc7fb#64 ++ 0xdd2fcd6bfbe49eb7#64 ++ 0xfd9f2f7f79cff5ff#64 ++ 0xd9fdecfdaef7c476#64 ++ 0x3ff9bdb7bffb76db#64 ++ 0xb6bfe85e6a41ebc#64 ++ 0x1df7574d9fbddf93#64 ++ 0xefebb4dedff7affc#64 ++ 0xbf7b1b2bfefdfbf7#64 ++ 0x38e7af3c8fce35ff#64 ++ 0xcd7fef277df06f7f#64 ++ 0x7dfe6eaee84ef2de#64 ++ 0xfbffe78d3fafdf8e#64
def r1 : W := 0x842c21a024a00028#64 ++ 0x8848134001042400#64 ++ 0x5200048810002104#64 ++ 0x22004962ac6050cc#64 ++ 0x8004078034008001#64 ++ 0x9124180224021444#64 ++ 0xd845088021000910#64 ++ 0x800a2000040004c0#64 ++ 0x4908010880083824#64 ++ 0x21082400a20024#64 ++ 0x9a022400e01b8c01#64 ++ 0x1204c16029042#64 ++ 0x20103400021a0422#64 ++ 0x1000c184010b2088#64 ++ 0x108138c08d00d004#64 ++ 0x842c21a024a00028#64 ++ 0x8fcdbe73fdf3f773#64 ++ 0x2adba77f3933b1df#64 ++ 0xc7d9f27bf2fbf75f#64 ++ 0x69ea53cbfb0b78ef#64 ++ 0xc5d3f2d66effbded#64 ++ 0xbee9dd4f9ef6bb8b#64 ++ 0xe77adfaf7f19bfb9#64 ++ 0xe9c756d1a7ceb1e6#64 ++ 0xfd366dfffdcfefe7#64 ++ 0xf677f7277f6ffafc#64 ++ 0x75dbff6330ae73b7#64 ++ 0x451cbedc6de735d9#64 ++ 0xf7f95ce766f7fd7f#64 ++ 0x6eb2bedfa51fb2a2#64 ++ 0x933bf1fbb3b7eff3#64 ++ 0x8fcdbe73fdf3f773#64
def r2 : W := 0x4b005e17184a8091#64 ++ 0x12442430fb4082#64 ++ 0xd3a0157403102c1#64 ++ 0x444b08901880120#64 ++ 0x20428841cb006802#64 ++ 0x448000e9884d4009#64 ++ 0x261052028e9266c4#64 ++ 0x18f143248aa10a07#64 ++ 0xa2c152a21403c000#64 ++ 0xc5964400f6184550#64 ++ 0x29180012807108#64 ++ 0x63c52a180440018#64 ++ 0xd46c488004805b00#64 ++ 0xc2ea024a40c01370#64 ++ 0x2078060612152808#64 ++ 0x4b005e17184a8091#64 ++ 0xa3a3cd94c6676eeb#64 ++ 0xefff089f7afd823a#64 ++ 0x3caacfd93dfef77e#64 ++ 0x3d045f7d2e7bbbd6#64 ++ 0x7bf6bbffabc9cbf2#64 ++ 0x6b4df3fabfca77d8#64 ++ 0x2d4e3f426a7d356e#64 ++ 0x1f33c67e53d39df7#64 ++ 0xbcd9bf3e2b1ef5ef#64 ++ 0xeb6abede40f774bc#64 ++ 0x4bb64bbebdbcd19b#64 ++ 0xafebf6ffbf690e9c#64 ++ 0x8df8d903bb6d5b63#64 ++ 0xf799d1ecff7f5bcc#64 ++ 0xf991a7d42d19bca9#64 ++ 0xa3a3cd94c6676eeb#64
def r3 : W := 0x5880132800070fa7#64 ++ 0x28502a8440994880#64 ++ 0x64327808829852c8#64 ++ 0xca1410c25d011831#64 ++ 0xc23e94899206b04#64 ++ 0x31ce23a2cb110c09#64 ++ 0x418d0441acf3690#64 ++ 0x60518648b18b15#64 ++ 0x794111fc50040682#64 ++ 0xc22c91186000561a#64 ++ 0x2059d9230a85b321#64 ++ 0x482012a867cd08#64 ++ 0x1d2100c1216329b1#64 ++ 0x91a40003c2203020#64 ++ 0x6ecc8106626081d8#64 ++ 0x5880132800070fa7#64 ++ 0xd59ad7ef38da9bbf#64 ++ 0x72417972ecfe6f3a#64 ++ 0x7fc7f0b7af615cd5#64 ++ 0xd7f3afc8f58c8ffe#64 ++ 0x236f3671fddf7a0e#64 ++ 0xf037e99a563778fe#64 ++ 0x1add9b94d5feeab1#64 ++ 0xed4eff997e35ea3c#64 ++ 0x52bdb5eb1bff7c58#64 ++ 0x46982ef3b1a889eb#64 ++ 0xb0dfd0e7d2cdfdc2#64 ++ 0x52cf6d4900befe36#64 ++ 0xc6a636ff7852e7e2#64 ++ 0x765e6c7cbafc9755#64 ++ 0x2f6738ffffe0172c#64 ++ 0xd59ad7ef38da9bbf#64
def r4 : W := 0x2b5725e229c7c9e#64 ++ 0x832b90f8a2a0361f#64 ++ 0x9f4ff7436deec1b1#64 ++ 0x8d7bd638c2fd8c80#64 ++ 0x4c8430d7227f0fa1#64 ++ 0xae0bb3191e462ae5#64 ++ 0x1d90f7d131497045#64 ++ 0x8e0b6e1118e4ad1#64 ++ 0xb6a260d29e81a188#64 ++ 0xa91d09e4fcfaa732#64 ++ 0x214465cca66c4a40#64 ++ 0x28190ade24381e82#64 ++ 0x790a5a3752186386#64 ++ 0xcd17049523f81b4e#64 ++ 0x8a507639818033ff#64 ++ 0x2b5725e229c7c9e#64 ++ 0x5731b0aa19b4bf6f#64 ++ 0xc8fbf866afbf617c#64 ++ 0x79d10ecbf81b3f82#64 ++ 0xb71e76d395c3a2db#64 ++ 0x76de860ea09aca47#64 ++ 0xc85878c14ff5e2c#64 ++ 0x839cebe2011daa29#64 ++ 0xbb67282de7a8385f#64 ++ 0xd6c6207576f32a72#64 ++ 0xe59ad8d55c94e108#64 ++ 0xb05de6bf9b15463d#64 ++ 0xf9a66c1d9e3d56c3#64 ++ 0x93367b929112bf40#64 ++ 0x7d092bb9be863160#64 ++ 0x2b99c3d54fdecf98#64 ++ 0x5731b0aa19b4bf6f#64
def r5 : W := 0x92bc8cc0d0cec41#64 ++ 0x7717748bb41cc255#64 ++ 0x9b99a0b5fa9c6747#64 ++ 0x105d0d35d1dccad8#64 ++ 0x45ec349acf5e91c1#64 ++ 0xe05b59f861c8cab2#64 ++ 0xd268829f409c4e84#64 ++ 0x939281e3a032b0f0#64 ++ 0x7ea4381db9e5a#64 ++ 0x60db92b51e41dbc9#64 ++ 0x209ebb6c8c83cb4#64 ++ 0x7b87c099cbe058be#64 ++ 0x497153724278f211#64 ++ 0x31511d6602dcaf2#64 ++ 0x91352eab410e5071#64 ++ 0x92bc8cc0d0cec41#64 ++ 0xb0dd2bde92f1bdb7#64 ++ 0x53fd5ec0a46808da#64 ++ 0x16112fa4a951b8a7#64 ++ 0x25a5179044f8380c#64 ++ 0x2719994f7f15ecea#64 ++ 0x606b57f9072d78bd#64 ++ 0xebbea53716ffdfb1#64 ++ 0x453a965c467ffd42#64 ++ 0xf8b6483bf5b39342#64 ++ 0xa35a1df8aca8387a#64 ++ 0x5655b155a1033dcb#64 ++ 0x89c35e3a75831b7c#64 ++ 0x56a5fd6052da8a64#64 ++ 0xd3c0db8b1b8cf4c7#64 ++ 0x19defec5f6268d6d#64 ++ 0xb0dd2bde92f1bdb7#64
def rows : List W := [r0, r1, r2, r3, r4, r5]
def n0 : ℕ := (((((((((((((((((((((((((((((((0x11004000104040 * 2 ^ 64 + 0x538100020c00924d) * 2 ^ 64 + 0x1020001048c22) * 2 ^ 64 + 0x1021060402062402) * 2 ^ 64 + 0x51001014001d0488) * 2 ^ 64 + 0x1401400a02232) * 2 ^ 64 + 0x2242900000022) * 2 ^ 64 + 0x2504005811487028) * 2 ^ 64 + 0x4268c000a400041) * 2 ^ 64 + 0x2000028301458001) * 2 ^ 64 + 0x404009804200006) * 2 ^ 64 + 0xb8800d0041900200) * 2 ^ 64 + 0x801008040008) * 2 ^ 64 + 0xc100c303010c001) * 2 ^ 64 + 0x2003000880200) * 2 ^ 64 + 0x11004000104040) * 2 ^ 64 + 0xfbffe78d3fafdf8e) * 2 ^ 64 + 0xd7e4dfadc7dc7eff) * 2 ^ 64 + 0xea7f7f1d579c5cb9) * 2 ^ 64 + 0xd7ddfdfe14fcc7fb) * 2 ^ 64 + 0xdd2fcd6bfbe49eb7) * 2 ^ 64 + 0xfd9f2f7f79cff5ff) * 2 ^ 64 + 0xd9fdecfdaef7c476) * 2 ^ 64 + 0x3ff9bdb7bffb76db) * 2 ^ 64 + 0xb6bfe85e6a41ebc) * 2 ^ 64 + 0x1df7574d9fbddf93) * 2 ^ 64 + 0xefebb4dedff7affc) * 2 ^ 64 + 0xbf7b1b2bfefdfbf7) * 2 ^ 64 + 0x38e7af3c8fce35ff) * 2 ^ 64 + 0xcd7fef277df06f7f) * 2 ^ 64 + 0x7dfe6eaee84ef2de) * 2 ^ 64 + 0xfbffe78d3fafdf8e)
def n1 : ℕ := (((((((((((((((((((((((((((((((0x842c21a024a00028 * 2 ^ 64 + 0x8848134001042400) * 2 ^ 64 + 0x5200048810002104) * 2 ^ 64 + 0x22004962ac6050cc) * 2 ^ 64 + 0x8004078034008001) * 2 ^ 64 + 0x9124180224021444) * 2 ^ 64 + 0xd845088021000910) * 2 ^ 64 + 0x800a2000040004c0) * 2 ^ 64 + 0x4908010880083824) * 2 ^ 64 + 0x21082400a20024) * 2 ^ 64 + 0x9a022400e01b8c01) * 2 ^ 64 + 0x1204c16029042) * 2 ^ 64 + 0x20103400021a0422) * 2 ^ 64 + 0x1000c184010b2088) * 2 ^ 64 + 0x108138c08d00d004) * 2 ^ 64 + 0x842c21a024a00028) * 2 ^ 64 + 0x8fcdbe73fdf3f773) * 2 ^ 64 + 0x2adba77f3933b1df) * 2 ^ 64 + 0xc7d9f27bf2fbf75f) * 2 ^ 64 + 0x69ea53cbfb0b78ef) * 2 ^ 64 + 0xc5d3f2d66effbded) * 2 ^ 64 + 0xbee9dd4f9ef6bb8b) * 2 ^ 64 + 0xe77adfaf7f19bfb9) * 2 ^ 64 + 0xe9c756d1a7ceb1e6) * 2 ^ 64 + 0xfd366dfffdcfefe7) * 2 ^ 64 + 0xf677f7277f6ffafc) * 2 ^ 64 + 0x75dbff6330ae73b7) * 2 ^ 64 + 0x451cbedc6de735d9) * 2 ^ 64 + 0xf7f95ce766f7fd7f) * 2 ^ 64 + 0x6eb2bedfa51fb2a2) * 2 ^ 64 + 0x933bf1fbb3b7eff3) * 2 ^ 64 + 0x8fcdbe73fdf3f773)
def n2 : ℕ := (((((((((((((((((((((((((((((((0x4b005e17184a8091 * 2 ^ 64 + 0x12442430fb4082) * 2 ^ 64 + 0xd3a0157403102c1) * 2 ^ 64 + 0x444b08901880120) * 2 ^ 64 + 0x20428841cb006802) * 2 ^ 64 + 0x448000e9884d4009) * 2 ^ 64 + 0x261052028e9266c4) * 2 ^ 64 + 0x18f143248aa10a07) * 2 ^ 64 + 0xa2c152a21403c000) * 2 ^ 64 + 0xc5964400f6184550) * 2 ^ 64 + 0x29180012807108) * 2 ^ 64 + 0x63c52a180440018) * 2 ^ 64 + 0xd46c488004805b00) * 2 ^ 64 + 0xc2ea024a40c01370) * 2 ^ 64 + 0x2078060612152808) * 2 ^ 64 + 0x4b005e17184a8091) * 2 ^ 64 + 0xa3a3cd94c6676eeb) * 2 ^ 64 + 0xefff089f7afd823a) * 2 ^ 64 + 0x3caacfd93dfef77e) * 2 ^ 64 + 0x3d045f7d2e7bbbd6) * 2 ^ 64 + 0x7bf6bbffabc9cbf2) * 2 ^ 64 + 0x6b4df3fabfca77d8) * 2 ^ 64 + 0x2d4e3f426a7d356e) * 2 ^ 64 + 0x1f33c67e53d39df7) * 2 ^ 64 + 0xbcd9bf3e2b1ef5ef) * 2 ^ 64 + 0xeb6abede40f774bc) * 2 ^ 64 + 0x4bb64bbebdbcd19b) * 2 ^ 64 + 0xafebf6ffbf690e9c) * 2 ^ 64 + 0x8df8d903bb6d5b63) * 2 ^ 64 + 0xf799d1ecff7f5bcc) * 2 ^ 64 + 0xf991a7d42d19bca9) * 2 ^ 64 + 0xa3a3cd94c6676eeb)
def n3 : ℕ := (((((((((((((((((((((((((((((((0x5880132800070fa7 * 2 ^ 64 + 0x28502a8440994880) * 2 ^ 64 + 0x64327808829852c8) * 2 ^ 64 + 0xca1410c25d011831) * 2 ^ 64 + 0xc23e94899206b04) * 2 ^ 64 + 0x31ce23a2cb110c09) * 2 ^ 64 + 0x418d0441acf3690) * 2 ^ 64 + 0x60518648b18b15) * 2 ^ 64 + 0x794111fc50040682) * 2 ^ 64 + 0xc22c91186000561a) * 2 ^ 64 + 0x2059d9230a85b321) * 2 ^ 64 + 0x482012a867cd08) * 2 ^ 64 + 0x1d2100c1216329b1) * 2 ^ 64 + 0x91a40003c2203020) * 2 ^ 64 + 0x6ecc8106626081d8) * 2 ^ 64 + 0x5880132800070fa7) * 2 ^ 64 + 0xd59ad7ef38da9bbf) * 2 ^ 64 + 0x72417972ecfe6f3a) * 2 ^ 64 + 0x7fc7f0b7af615cd5) * 2 ^ 64 + 0xd7f3afc8f58c8ffe) * 2 ^ 64 + 0x236f3671fddf7a0e) * 2 ^ 64 + 0xf037e99a563778fe) * 2 ^ 64 + 0x1add9b94d5feeab1) * 2 ^ 64 + 0xed4eff997e35ea3c) * 2 ^ 64 + 0x52bdb5eb1bff7c58) * 2 ^ 64 + 0x46982ef3b1a889eb) * 2 ^ 64 + 0xb0dfd0e7d2cdfdc2) * 2 ^ 64 + 0x52cf6d4900befe36) * 2 ^ 64 + 0xc6a636ff7852e7e2) * 2 ^ 64 + 0x765e6c7cbafc9755) * 2 ^ 64 + 0x2f6738ffffe0172c) * 2 ^ 64 + 0xd59ad7ef38da9bbf)
def n4 : ℕ := (((((((((((((((((((((((((((((((0x2b5725e229c7c9e * 2 ^ 64 + 0x832b90f8a2a0361f) * 2 ^ 64 + 0x9f4ff7436deec1b1) * 2 ^ 64 + 0x8d7bd638c2fd8c80) * 2 ^ 64 + 0x4c8430d7227f0fa1) * 2 ^ 64 + 0xae0bb3191e462ae5) * 2 ^ 64 + 0x1d90f7d131497045) * 2 ^ 64 + 0x8e0b6e1118e4ad1) * 2 ^ 64 + 0xb6a260d29e81a188) * 2 ^ 64 + 0xa91d09e4fcfaa732) * 2 ^ 64 + 0x214465cca66c4a40) * 2 ^ 64 + 0x28190ade24381e82) * 2 ^ 64 + 0x790a5a3752186386) * 2 ^ 64 + 0xcd17049523f81b4e) * 2 ^ 64 + 0x8a507639818033ff) * 2 ^ 64 + 0x2b5725e229c7c9e) * 2 ^ 64 + 0x5731b0aa19b4bf6f) * 2 ^ 64 + 0xc8fbf866afbf617c) * 2 ^ 64 + 0x79d10ecbf81b3f82) * 2 ^ 64 + 0xb71e76d395c3a2db) * 2 ^ 64 + 0x76de860ea09aca47) * 2 ^ 64 + 0xc85878c14ff5e2c) * 2 ^ 64 + 0x839cebe2011daa29) * 2 ^ 64 + 0xbb67282de7a8385f) * 2 ^ 64 + 0xd6c6207576f32a72) * 2 ^ 64 + 0xe59ad8d55c94e108) * 2 ^ 64 + 0xb05de6bf9b15463d) * 2 ^ 64 + 0xf9a66c1d9e3d56c3) * 2 ^ 64 + 0x93367b929112bf40) * 2 ^ 64 + 0x7d092bb9be863160) * 2 ^ 64 + 0x2b99c3d54fdecf98) * 2 ^ 64 + 0x5731b0aa19b4bf6f)
def n5 : ℕ := (((((((((((((((((((((((((((((((0x92bc8cc0d0cec41 * 2 ^ 64 + 0x7717748bb41cc255) * 2 ^ 64 + 0x9b99a0b5fa9c6747) * 2 ^ 64 + 0x105d0d35d1dccad8) * 2 ^ 64 + 0x45ec349acf5e91c1) * 2 ^ 64 + 0xe05b59f861c8cab2) * 2 ^ 64 + 0xd268829f409c4e84) * 2 ^ 64 + 0x939281e3a032b0f0) * 2 ^ 64 + 0x7ea4381db9e5a) * 2 ^ 64 + 0x60db92b51e41dbc9) * 2 ^ 64 + 0x209ebb6c8c83cb4) * 2 ^ 64 + 0x7b87c099cbe058be) * 2 ^ 64 + 0x497153724278f211) * 2 ^ 64 + 0x31511d6602dcaf2) * 2 ^ 64 + 0x91352eab410e5071) * 2 ^ 64 + 0x92bc8cc0d0cec41) * 2 ^ 64 + 0xb0dd2bde92f1bdb7) * 2 ^ 64 + 0x53fd5ec0a46808da) * 2 ^ 64 + 0x16112fa4a951b8a7) * 2 ^ 64 + 0x25a5179044f8380c) * 2 ^ 64 + 0x2719994f7f15ecea) * 2 ^ 64 + 0x606b57f9072d78bd) * 2 ^ 64 + 0xebbea53716ffdfb1) * 2 ^ 64 + 0x453a965c467ffd42) * 2 ^ 64 + 0xf8b6483bf5b39342) * 2 ^ 64 + 0xa35a1df8aca8387a) * 2 ^ 64 + 0x5655b155a1033dcb) * 2 ^ 64 + 0x89c35e3a75831b7c) * 2 ^ 64 + 0x56a5fd6052da8a64) * 2 ^ 64 + 0xd3c0db8b1b8cf4c7) * 2 ^ 64 + 0x19defec5f6268d6d) * 2 ^ 64 + 0xb0dd2bde92f1bdb7)
def rowsN : List ℕ := [n0, n1, n2, n3, n4, n5]

theorem rows_eq : rows.map BitVec.toNat = rowsN := by
  decide +kernel

theorem only_full : ∀ ws ∈ rowsN.sublists, (decide (ws.length ≤ 8 + 2) && cutFull ws) = true → ws = rowsN := by
  decide +kernel

def kR : List (ℕ × List ℕ) := kidsRoot 4 rowsN

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rq68 : anyK (node 0 8) (kR.drop 68) = false := by decide +kernel
def kid67 := kids (hdK (kR.drop 67)).1 (hdK (kR.drop 67)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c67_81 : anyK (node 0 7) (kid67.drop 81) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_80 : anyK (node 0 7) ((kid67.drop 80).take 1) = false := by decide +kernel
theorem c67_80 : anyK (node 0 7) (kid67.drop 80) = false := chainK _ _ 80 1 81 rfl t67_80 c67_81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_70 : anyK (node 0 7) ((kid67.drop 70).take 10) = false := by decide +kernel
theorem c67_70 : anyK (node 0 7) (kid67.drop 70) = false := chainK _ _ 70 10 80 rfl t67_70 c67_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_60 : anyK (node 0 7) ((kid67.drop 60).take 10) = false := by decide +kernel
theorem c67_60 : anyK (node 0 7) (kid67.drop 60) = false := chainK _ _ 60 10 70 rfl t67_60 c67_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_50 : anyK (node 0 7) ((kid67.drop 50).take 10) = false := by decide +kernel
theorem c67_50 : anyK (node 0 7) (kid67.drop 50) = false := chainK _ _ 50 10 60 rfl t67_50 c67_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_40 : anyK (node 0 7) ((kid67.drop 40).take 10) = false := by decide +kernel
theorem c67_40 : anyK (node 0 7) (kid67.drop 40) = false := chainK _ _ 40 10 50 rfl t67_40 c67_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_30 : anyK (node 0 7) ((kid67.drop 30).take 10) = false := by decide +kernel
theorem c67_30 : anyK (node 0 7) (kid67.drop 30) = false := chainK _ _ 30 10 40 rfl t67_30 c67_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_20 : anyK (node 0 7) ((kid67.drop 20).take 10) = false := by decide +kernel
theorem c67_20 : anyK (node 0 7) (kid67.drop 20) = false := chainK _ _ 20 10 30 rfl t67_20 c67_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_10 : anyK (node 0 7) ((kid67.drop 10).take 10) = false := by decide +kernel
theorem c67_10 : anyK (node 0 7) (kid67.drop 10) = false := chainK _ _ 10 10 20 rfl t67_10 c67_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t67_0 : anyK (node 0 7) ((kid67.drop 0).take 10) = false := by decide +kernel
theorem c67_0 : anyK (node 0 7) (kid67.drop 0) = false := chainK _ _ 0 10 10 rfl t67_0 c67_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc67 : anyK (node 0 8) ((kR.drop 67).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid67 c67_0))
theorem rq67 : anyK (node 0 8) (kR.drop 67) = false := chainK _ _ 67 1 68 rfl sc67 rq68
def kid66 := kids (hdK (kR.drop 66)).1 (hdK (kR.drop 66)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c66_93 : anyK (node 0 7) (kid66.drop 93) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_90 : anyK (node 0 7) ((kid66.drop 90).take 3) = false := by decide +kernel
theorem c66_90 : anyK (node 0 7) (kid66.drop 90) = false := chainK _ _ 90 3 93 rfl t66_90 c66_93
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_80 : anyK (node 0 7) ((kid66.drop 80).take 10) = false := by decide +kernel
theorem c66_80 : anyK (node 0 7) (kid66.drop 80) = false := chainK _ _ 80 10 90 rfl t66_80 c66_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_70 : anyK (node 0 7) ((kid66.drop 70).take 10) = false := by decide +kernel
theorem c66_70 : anyK (node 0 7) (kid66.drop 70) = false := chainK _ _ 70 10 80 rfl t66_70 c66_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_60 : anyK (node 0 7) ((kid66.drop 60).take 10) = false := by decide +kernel
theorem c66_60 : anyK (node 0 7) (kid66.drop 60) = false := chainK _ _ 60 10 70 rfl t66_60 c66_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_50 : anyK (node 0 7) ((kid66.drop 50).take 10) = false := by decide +kernel
theorem c66_50 : anyK (node 0 7) (kid66.drop 50) = false := chainK _ _ 50 10 60 rfl t66_50 c66_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_40 : anyK (node 0 7) ((kid66.drop 40).take 10) = false := by decide +kernel
theorem c66_40 : anyK (node 0 7) (kid66.drop 40) = false := chainK _ _ 40 10 50 rfl t66_40 c66_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_30 : anyK (node 0 7) ((kid66.drop 30).take 10) = false := by decide +kernel
theorem c66_30 : anyK (node 0 7) (kid66.drop 30) = false := chainK _ _ 30 10 40 rfl t66_30 c66_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_20 : anyK (node 0 7) ((kid66.drop 20).take 10) = false := by decide +kernel
theorem c66_20 : anyK (node 0 7) (kid66.drop 20) = false := chainK _ _ 20 10 30 rfl t66_20 c66_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_10 : anyK (node 0 7) ((kid66.drop 10).take 10) = false := by decide +kernel
theorem c66_10 : anyK (node 0 7) (kid66.drop 10) = false := chainK _ _ 10 10 20 rfl t66_10 c66_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t66_0 : anyK (node 0 7) ((kid66.drop 0).take 10) = false := by decide +kernel
theorem c66_0 : anyK (node 0 7) (kid66.drop 0) = false := chainK _ _ 0 10 10 rfl t66_0 c66_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc66 : anyK (node 0 8) ((kR.drop 66).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid66 c66_0))
theorem rq66 : anyK (node 0 8) (kR.drop 66) = false := chainK _ _ 66 1 67 rfl sc66 rq67
def kid65 := kids (hdK (kR.drop 65)).1 (hdK (kR.drop 65)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c65_75 : anyK (node 0 7) (kid65.drop 75) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_70 : anyK (node 0 7) ((kid65.drop 70).take 5) = false := by decide +kernel
theorem c65_70 : anyK (node 0 7) (kid65.drop 70) = false := chainK _ _ 70 5 75 rfl t65_70 c65_75
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_60 : anyK (node 0 7) ((kid65.drop 60).take 10) = false := by decide +kernel
theorem c65_60 : anyK (node 0 7) (kid65.drop 60) = false := chainK _ _ 60 10 70 rfl t65_60 c65_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_50 : anyK (node 0 7) ((kid65.drop 50).take 10) = false := by decide +kernel
theorem c65_50 : anyK (node 0 7) (kid65.drop 50) = false := chainK _ _ 50 10 60 rfl t65_50 c65_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_40 : anyK (node 0 7) ((kid65.drop 40).take 10) = false := by decide +kernel
theorem c65_40 : anyK (node 0 7) (kid65.drop 40) = false := chainK _ _ 40 10 50 rfl t65_40 c65_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_30 : anyK (node 0 7) ((kid65.drop 30).take 10) = false := by decide +kernel
theorem c65_30 : anyK (node 0 7) (kid65.drop 30) = false := chainK _ _ 30 10 40 rfl t65_30 c65_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_20 : anyK (node 0 7) ((kid65.drop 20).take 10) = false := by decide +kernel
theorem c65_20 : anyK (node 0 7) (kid65.drop 20) = false := chainK _ _ 20 10 30 rfl t65_20 c65_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_10 : anyK (node 0 7) ((kid65.drop 10).take 10) = false := by decide +kernel
theorem c65_10 : anyK (node 0 7) (kid65.drop 10) = false := chainK _ _ 10 10 20 rfl t65_10 c65_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t65_0 : anyK (node 0 7) ((kid65.drop 0).take 10) = false := by decide +kernel
theorem c65_0 : anyK (node 0 7) (kid65.drop 0) = false := chainK _ _ 0 10 10 rfl t65_0 c65_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc65 : anyK (node 0 8) ((kR.drop 65).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid65 c65_0))
theorem rq65 : anyK (node 0 8) (kR.drop 65) = false := chainK _ _ 65 1 66 rfl sc65 rq66
def kid64 := kids (hdK (kR.drop 64)).1 (hdK (kR.drop 64)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c64_110 : anyK (node 0 7) (kid64.drop 110) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_100 : anyK (node 0 7) ((kid64.drop 100).take 10) = false := by decide +kernel
theorem c64_100 : anyK (node 0 7) (kid64.drop 100) = false := chainK _ _ 100 10 110 rfl t64_100 c64_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_90 : anyK (node 0 7) ((kid64.drop 90).take 10) = false := by decide +kernel
theorem c64_90 : anyK (node 0 7) (kid64.drop 90) = false := chainK _ _ 90 10 100 rfl t64_90 c64_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_80 : anyK (node 0 7) ((kid64.drop 80).take 10) = false := by decide +kernel
theorem c64_80 : anyK (node 0 7) (kid64.drop 80) = false := chainK _ _ 80 10 90 rfl t64_80 c64_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_70 : anyK (node 0 7) ((kid64.drop 70).take 10) = false := by decide +kernel
theorem c64_70 : anyK (node 0 7) (kid64.drop 70) = false := chainK _ _ 70 10 80 rfl t64_70 c64_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_60 : anyK (node 0 7) ((kid64.drop 60).take 10) = false := by decide +kernel
theorem c64_60 : anyK (node 0 7) (kid64.drop 60) = false := chainK _ _ 60 10 70 rfl t64_60 c64_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_50 : anyK (node 0 7) ((kid64.drop 50).take 10) = false := by decide +kernel
theorem c64_50 : anyK (node 0 7) (kid64.drop 50) = false := chainK _ _ 50 10 60 rfl t64_50 c64_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_40 : anyK (node 0 7) ((kid64.drop 40).take 10) = false := by decide +kernel
theorem c64_40 : anyK (node 0 7) (kid64.drop 40) = false := chainK _ _ 40 10 50 rfl t64_40 c64_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_30 : anyK (node 0 7) ((kid64.drop 30).take 10) = false := by decide +kernel
theorem c64_30 : anyK (node 0 7) (kid64.drop 30) = false := chainK _ _ 30 10 40 rfl t64_30 c64_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_20 : anyK (node 0 7) ((kid64.drop 20).take 10) = false := by decide +kernel
theorem c64_20 : anyK (node 0 7) (kid64.drop 20) = false := chainK _ _ 20 10 30 rfl t64_20 c64_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_10 : anyK (node 0 7) ((kid64.drop 10).take 10) = false := by decide +kernel
theorem c64_10 : anyK (node 0 7) (kid64.drop 10) = false := chainK _ _ 10 10 20 rfl t64_10 c64_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t64_0 : anyK (node 0 7) ((kid64.drop 0).take 10) = false := by decide +kernel
theorem c64_0 : anyK (node 0 7) (kid64.drop 0) = false := chainK _ _ 0 10 10 rfl t64_0 c64_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc64 : anyK (node 0 8) ((kR.drop 64).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid64 c64_0))
theorem rq64 : anyK (node 0 8) (kR.drop 64) = false := chainK _ _ 64 1 65 rfl sc64 rq65
def kid63 := kids (hdK (kR.drop 63)).1 (hdK (kR.drop 63)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c63_99 : anyK (node 0 7) (kid63.drop 99) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_90 : anyK (node 0 7) ((kid63.drop 90).take 9) = false := by decide +kernel
theorem c63_90 : anyK (node 0 7) (kid63.drop 90) = false := chainK _ _ 90 9 99 rfl t63_90 c63_99
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_80 : anyK (node 0 7) ((kid63.drop 80).take 10) = false := by decide +kernel
theorem c63_80 : anyK (node 0 7) (kid63.drop 80) = false := chainK _ _ 80 10 90 rfl t63_80 c63_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_70 : anyK (node 0 7) ((kid63.drop 70).take 10) = false := by decide +kernel
theorem c63_70 : anyK (node 0 7) (kid63.drop 70) = false := chainK _ _ 70 10 80 rfl t63_70 c63_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_60 : anyK (node 0 7) ((kid63.drop 60).take 10) = false := by decide +kernel
theorem c63_60 : anyK (node 0 7) (kid63.drop 60) = false := chainK _ _ 60 10 70 rfl t63_60 c63_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_50 : anyK (node 0 7) ((kid63.drop 50).take 10) = false := by decide +kernel
theorem c63_50 : anyK (node 0 7) (kid63.drop 50) = false := chainK _ _ 50 10 60 rfl t63_50 c63_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_40 : anyK (node 0 7) ((kid63.drop 40).take 10) = false := by decide +kernel
theorem c63_40 : anyK (node 0 7) (kid63.drop 40) = false := chainK _ _ 40 10 50 rfl t63_40 c63_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_30 : anyK (node 0 7) ((kid63.drop 30).take 10) = false := by decide +kernel
theorem c63_30 : anyK (node 0 7) (kid63.drop 30) = false := chainK _ _ 30 10 40 rfl t63_30 c63_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_20 : anyK (node 0 7) ((kid63.drop 20).take 10) = false := by decide +kernel
theorem c63_20 : anyK (node 0 7) (kid63.drop 20) = false := chainK _ _ 20 10 30 rfl t63_20 c63_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_10 : anyK (node 0 7) ((kid63.drop 10).take 10) = false := by decide +kernel
theorem c63_10 : anyK (node 0 7) (kid63.drop 10) = false := chainK _ _ 10 10 20 rfl t63_10 c63_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t63_0 : anyK (node 0 7) ((kid63.drop 0).take 10) = false := by decide +kernel
theorem c63_0 : anyK (node 0 7) (kid63.drop 0) = false := chainK _ _ 0 10 10 rfl t63_0 c63_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc63 : anyK (node 0 8) ((kR.drop 63).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid63 c63_0))
theorem rq63 : anyK (node 0 8) (kR.drop 63) = false := chainK _ _ 63 1 64 rfl sc63 rq64
def kid62 := kids (hdK (kR.drop 62)).1 (hdK (kR.drop 62)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c62_64 : anyK (node 0 7) (kid62.drop 64) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_60 : anyK (node 0 7) ((kid62.drop 60).take 4) = false := by decide +kernel
theorem c62_60 : anyK (node 0 7) (kid62.drop 60) = false := chainK _ _ 60 4 64 rfl t62_60 c62_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_50 : anyK (node 0 7) ((kid62.drop 50).take 10) = false := by decide +kernel
theorem c62_50 : anyK (node 0 7) (kid62.drop 50) = false := chainK _ _ 50 10 60 rfl t62_50 c62_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_40 : anyK (node 0 7) ((kid62.drop 40).take 10) = false := by decide +kernel
theorem c62_40 : anyK (node 0 7) (kid62.drop 40) = false := chainK _ _ 40 10 50 rfl t62_40 c62_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_30 : anyK (node 0 7) ((kid62.drop 30).take 10) = false := by decide +kernel
theorem c62_30 : anyK (node 0 7) (kid62.drop 30) = false := chainK _ _ 30 10 40 rfl t62_30 c62_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_20 : anyK (node 0 7) ((kid62.drop 20).take 10) = false := by decide +kernel
theorem c62_20 : anyK (node 0 7) (kid62.drop 20) = false := chainK _ _ 20 10 30 rfl t62_20 c62_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_10 : anyK (node 0 7) ((kid62.drop 10).take 10) = false := by decide +kernel
theorem c62_10 : anyK (node 0 7) (kid62.drop 10) = false := chainK _ _ 10 10 20 rfl t62_10 c62_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t62_0 : anyK (node 0 7) ((kid62.drop 0).take 10) = false := by decide +kernel
theorem c62_0 : anyK (node 0 7) (kid62.drop 0) = false := chainK _ _ 0 10 10 rfl t62_0 c62_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc62 : anyK (node 0 8) ((kR.drop 62).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid62 c62_0))
theorem rq62 : anyK (node 0 8) (kR.drop 62) = false := chainK _ _ 62 1 63 rfl sc62 rq63
def kid61 := kids (hdK (kR.drop 61)).1 (hdK (kR.drop 61)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c61_37 : anyK (node 0 7) (kid61.drop 37) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t61_30 : anyK (node 0 7) ((kid61.drop 30).take 7) = false := by decide +kernel
theorem c61_30 : anyK (node 0 7) (kid61.drop 30) = false := chainK _ _ 30 7 37 rfl t61_30 c61_37
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t61_20 : anyK (node 0 7) ((kid61.drop 20).take 10) = false := by decide +kernel
theorem c61_20 : anyK (node 0 7) (kid61.drop 20) = false := chainK _ _ 20 10 30 rfl t61_20 c61_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t61_10 : anyK (node 0 7) ((kid61.drop 10).take 10) = false := by decide +kernel
theorem c61_10 : anyK (node 0 7) (kid61.drop 10) = false := chainK _ _ 10 10 20 rfl t61_10 c61_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t61_0 : anyK (node 0 7) ((kid61.drop 0).take 10) = false := by decide +kernel
theorem c61_0 : anyK (node 0 7) (kid61.drop 0) = false := chainK _ _ 0 10 10 rfl t61_0 c61_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc61 : anyK (node 0 8) ((kR.drop 61).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid61 c61_0))
theorem rq61 : anyK (node 0 8) (kR.drop 61) = false := chainK _ _ 61 1 62 rfl sc61 rq62
def kid60 := kids (hdK (kR.drop 60)).1 (hdK (kR.drop 60)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c60_59 : anyK (node 0 7) (kid60.drop 59) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_50 : anyK (node 0 7) ((kid60.drop 50).take 9) = false := by decide +kernel
theorem c60_50 : anyK (node 0 7) (kid60.drop 50) = false := chainK _ _ 50 9 59 rfl t60_50 c60_59
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_40 : anyK (node 0 7) ((kid60.drop 40).take 10) = false := by decide +kernel
theorem c60_40 : anyK (node 0 7) (kid60.drop 40) = false := chainK _ _ 40 10 50 rfl t60_40 c60_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_30 : anyK (node 0 7) ((kid60.drop 30).take 10) = false := by decide +kernel
theorem c60_30 : anyK (node 0 7) (kid60.drop 30) = false := chainK _ _ 30 10 40 rfl t60_30 c60_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_20 : anyK (node 0 7) ((kid60.drop 20).take 10) = false := by decide +kernel
theorem c60_20 : anyK (node 0 7) (kid60.drop 20) = false := chainK _ _ 20 10 30 rfl t60_20 c60_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_10 : anyK (node 0 7) ((kid60.drop 10).take 10) = false := by decide +kernel
theorem c60_10 : anyK (node 0 7) (kid60.drop 10) = false := chainK _ _ 10 10 20 rfl t60_10 c60_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t60_0 : anyK (node 0 7) ((kid60.drop 0).take 10) = false := by decide +kernel
theorem c60_0 : anyK (node 0 7) (kid60.drop 0) = false := chainK _ _ 0 10 10 rfl t60_0 c60_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc60 : anyK (node 0 8) ((kR.drop 60).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid60 c60_0))
theorem rq60 : anyK (node 0 8) (kR.drop 60) = false := chainK _ _ 60 1 61 rfl sc60 rq61
def kid59 := kids (hdK (kR.drop 59)).1 (hdK (kR.drop 59)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c59_94 : anyK (node 0 7) (kid59.drop 94) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_90 : anyK (node 0 7) ((kid59.drop 90).take 4) = false := by decide +kernel
theorem c59_90 : anyK (node 0 7) (kid59.drop 90) = false := chainK _ _ 90 4 94 rfl t59_90 c59_94
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_80 : anyK (node 0 7) ((kid59.drop 80).take 10) = false := by decide +kernel
theorem c59_80 : anyK (node 0 7) (kid59.drop 80) = false := chainK _ _ 80 10 90 rfl t59_80 c59_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_70 : anyK (node 0 7) ((kid59.drop 70).take 10) = false := by decide +kernel
theorem c59_70 : anyK (node 0 7) (kid59.drop 70) = false := chainK _ _ 70 10 80 rfl t59_70 c59_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_60 : anyK (node 0 7) ((kid59.drop 60).take 10) = false := by decide +kernel
theorem c59_60 : anyK (node 0 7) (kid59.drop 60) = false := chainK _ _ 60 10 70 rfl t59_60 c59_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_50 : anyK (node 0 7) ((kid59.drop 50).take 10) = false := by decide +kernel
theorem c59_50 : anyK (node 0 7) (kid59.drop 50) = false := chainK _ _ 50 10 60 rfl t59_50 c59_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_40 : anyK (node 0 7) ((kid59.drop 40).take 10) = false := by decide +kernel
theorem c59_40 : anyK (node 0 7) (kid59.drop 40) = false := chainK _ _ 40 10 50 rfl t59_40 c59_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_30 : anyK (node 0 7) ((kid59.drop 30).take 10) = false := by decide +kernel
theorem c59_30 : anyK (node 0 7) (kid59.drop 30) = false := chainK _ _ 30 10 40 rfl t59_30 c59_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_20 : anyK (node 0 7) ((kid59.drop 20).take 10) = false := by decide +kernel
theorem c59_20 : anyK (node 0 7) (kid59.drop 20) = false := chainK _ _ 20 10 30 rfl t59_20 c59_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_10 : anyK (node 0 7) ((kid59.drop 10).take 10) = false := by decide +kernel
theorem c59_10 : anyK (node 0 7) (kid59.drop 10) = false := chainK _ _ 10 10 20 rfl t59_10 c59_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t59_0 : anyK (node 0 7) ((kid59.drop 0).take 10) = false := by decide +kernel
theorem c59_0 : anyK (node 0 7) (kid59.drop 0) = false := chainK _ _ 0 10 10 rfl t59_0 c59_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc59 : anyK (node 0 8) ((kR.drop 59).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid59 c59_0))
theorem rq59 : anyK (node 0 8) (kR.drop 59) = false := chainK _ _ 59 1 60 rfl sc59 rq60
def kid58 := kids (hdK (kR.drop 58)).1 (hdK (kR.drop 58)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c58_46 : anyK (node 0 7) (kid58.drop 46) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t58_40 : anyK (node 0 7) ((kid58.drop 40).take 6) = false := by decide +kernel
theorem c58_40 : anyK (node 0 7) (kid58.drop 40) = false := chainK _ _ 40 6 46 rfl t58_40 c58_46
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t58_30 : anyK (node 0 7) ((kid58.drop 30).take 10) = false := by decide +kernel
theorem c58_30 : anyK (node 0 7) (kid58.drop 30) = false := chainK _ _ 30 10 40 rfl t58_30 c58_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t58_20 : anyK (node 0 7) ((kid58.drop 20).take 10) = false := by decide +kernel
theorem c58_20 : anyK (node 0 7) (kid58.drop 20) = false := chainK _ _ 20 10 30 rfl t58_20 c58_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t58_10 : anyK (node 0 7) ((kid58.drop 10).take 10) = false := by decide +kernel
theorem c58_10 : anyK (node 0 7) (kid58.drop 10) = false := chainK _ _ 10 10 20 rfl t58_10 c58_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t58_0 : anyK (node 0 7) ((kid58.drop 0).take 10) = false := by decide +kernel
theorem c58_0 : anyK (node 0 7) (kid58.drop 0) = false := chainK _ _ 0 10 10 rfl t58_0 c58_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc58 : anyK (node 0 8) ((kR.drop 58).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid58 c58_0))
theorem rq58 : anyK (node 0 8) (kR.drop 58) = false := chainK _ _ 58 1 59 rfl sc58 rq59
def kid57 := kids (hdK (kR.drop 57)).1 (hdK (kR.drop 57)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c57_97 : anyK (node 0 7) (kid57.drop 97) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_90 : anyK (node 0 7) ((kid57.drop 90).take 7) = false := by decide +kernel
theorem c57_90 : anyK (node 0 7) (kid57.drop 90) = false := chainK _ _ 90 7 97 rfl t57_90 c57_97
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_80 : anyK (node 0 7) ((kid57.drop 80).take 10) = false := by decide +kernel
theorem c57_80 : anyK (node 0 7) (kid57.drop 80) = false := chainK _ _ 80 10 90 rfl t57_80 c57_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_70 : anyK (node 0 7) ((kid57.drop 70).take 10) = false := by decide +kernel
theorem c57_70 : anyK (node 0 7) (kid57.drop 70) = false := chainK _ _ 70 10 80 rfl t57_70 c57_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_60 : anyK (node 0 7) ((kid57.drop 60).take 10) = false := by decide +kernel
theorem c57_60 : anyK (node 0 7) (kid57.drop 60) = false := chainK _ _ 60 10 70 rfl t57_60 c57_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_50 : anyK (node 0 7) ((kid57.drop 50).take 10) = false := by decide +kernel
theorem c57_50 : anyK (node 0 7) (kid57.drop 50) = false := chainK _ _ 50 10 60 rfl t57_50 c57_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_40 : anyK (node 0 7) ((kid57.drop 40).take 10) = false := by decide +kernel
theorem c57_40 : anyK (node 0 7) (kid57.drop 40) = false := chainK _ _ 40 10 50 rfl t57_40 c57_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_30 : anyK (node 0 7) ((kid57.drop 30).take 10) = false := by decide +kernel
theorem c57_30 : anyK (node 0 7) (kid57.drop 30) = false := chainK _ _ 30 10 40 rfl t57_30 c57_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_20 : anyK (node 0 7) ((kid57.drop 20).take 10) = false := by decide +kernel
theorem c57_20 : anyK (node 0 7) (kid57.drop 20) = false := chainK _ _ 20 10 30 rfl t57_20 c57_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_10 : anyK (node 0 7) ((kid57.drop 10).take 10) = false := by decide +kernel
theorem c57_10 : anyK (node 0 7) (kid57.drop 10) = false := chainK _ _ 10 10 20 rfl t57_10 c57_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t57_0 : anyK (node 0 7) ((kid57.drop 0).take 10) = false := by decide +kernel
theorem c57_0 : anyK (node 0 7) (kid57.drop 0) = false := chainK _ _ 0 10 10 rfl t57_0 c57_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc57 : anyK (node 0 8) ((kR.drop 57).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid57 c57_0))
theorem rq57 : anyK (node 0 8) (kR.drop 57) = false := chainK _ _ 57 1 58 rfl sc57 rq58
def kid56 := kids (hdK (kR.drop 56)).1 (hdK (kR.drop 56)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c56_62 : anyK (node 0 7) (kid56.drop 62) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_60 : anyK (node 0 7) ((kid56.drop 60).take 2) = false := by decide +kernel
theorem c56_60 : anyK (node 0 7) (kid56.drop 60) = false := chainK _ _ 60 2 62 rfl t56_60 c56_62
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_50 : anyK (node 0 7) ((kid56.drop 50).take 10) = false := by decide +kernel
theorem c56_50 : anyK (node 0 7) (kid56.drop 50) = false := chainK _ _ 50 10 60 rfl t56_50 c56_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_40 : anyK (node 0 7) ((kid56.drop 40).take 10) = false := by decide +kernel
theorem c56_40 : anyK (node 0 7) (kid56.drop 40) = false := chainK _ _ 40 10 50 rfl t56_40 c56_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_30 : anyK (node 0 7) ((kid56.drop 30).take 10) = false := by decide +kernel
theorem c56_30 : anyK (node 0 7) (kid56.drop 30) = false := chainK _ _ 30 10 40 rfl t56_30 c56_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_20 : anyK (node 0 7) ((kid56.drop 20).take 10) = false := by decide +kernel
theorem c56_20 : anyK (node 0 7) (kid56.drop 20) = false := chainK _ _ 20 10 30 rfl t56_20 c56_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_10 : anyK (node 0 7) ((kid56.drop 10).take 10) = false := by decide +kernel
theorem c56_10 : anyK (node 0 7) (kid56.drop 10) = false := chainK _ _ 10 10 20 rfl t56_10 c56_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t56_0 : anyK (node 0 7) ((kid56.drop 0).take 10) = false := by decide +kernel
theorem c56_0 : anyK (node 0 7) (kid56.drop 0) = false := chainK _ _ 0 10 10 rfl t56_0 c56_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc56 : anyK (node 0 8) ((kR.drop 56).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid56 c56_0))
theorem rq56 : anyK (node 0 8) (kR.drop 56) = false := chainK _ _ 56 1 57 rfl sc56 rq57
def kid55 := kids (hdK (kR.drop 55)).1 (hdK (kR.drop 55)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c55_35 : anyK (node 0 7) (kid55.drop 35) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t55_30 : anyK (node 0 7) ((kid55.drop 30).take 5) = false := by decide +kernel
theorem c55_30 : anyK (node 0 7) (kid55.drop 30) = false := chainK _ _ 30 5 35 rfl t55_30 c55_35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t55_20 : anyK (node 0 7) ((kid55.drop 20).take 10) = false := by decide +kernel
theorem c55_20 : anyK (node 0 7) (kid55.drop 20) = false := chainK _ _ 20 10 30 rfl t55_20 c55_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t55_10 : anyK (node 0 7) ((kid55.drop 10).take 10) = false := by decide +kernel
theorem c55_10 : anyK (node 0 7) (kid55.drop 10) = false := chainK _ _ 10 10 20 rfl t55_10 c55_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t55_0 : anyK (node 0 7) ((kid55.drop 0).take 10) = false := by decide +kernel
theorem c55_0 : anyK (node 0 7) (kid55.drop 0) = false := chainK _ _ 0 10 10 rfl t55_0 c55_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc55 : anyK (node 0 8) ((kR.drop 55).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid55 c55_0))
theorem rq55 : anyK (node 0 8) (kR.drop 55) = false := chainK _ _ 55 1 56 rfl sc55 rq56
def kid54 := kids (hdK (kR.drop 54)).1 (hdK (kR.drop 54)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c54_58 : anyK (node 0 7) (kid54.drop 58) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_50 : anyK (node 0 7) ((kid54.drop 50).take 8) = false := by decide +kernel
theorem c54_50 : anyK (node 0 7) (kid54.drop 50) = false := chainK _ _ 50 8 58 rfl t54_50 c54_58
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_40 : anyK (node 0 7) ((kid54.drop 40).take 10) = false := by decide +kernel
theorem c54_40 : anyK (node 0 7) (kid54.drop 40) = false := chainK _ _ 40 10 50 rfl t54_40 c54_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_30 : anyK (node 0 7) ((kid54.drop 30).take 10) = false := by decide +kernel
theorem c54_30 : anyK (node 0 7) (kid54.drop 30) = false := chainK _ _ 30 10 40 rfl t54_30 c54_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_20 : anyK (node 0 7) ((kid54.drop 20).take 10) = false := by decide +kernel
theorem c54_20 : anyK (node 0 7) (kid54.drop 20) = false := chainK _ _ 20 10 30 rfl t54_20 c54_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_10 : anyK (node 0 7) ((kid54.drop 10).take 10) = false := by decide +kernel
theorem c54_10 : anyK (node 0 7) (kid54.drop 10) = false := chainK _ _ 10 10 20 rfl t54_10 c54_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t54_0 : anyK (node 0 7) ((kid54.drop 0).take 10) = false := by decide +kernel
theorem c54_0 : anyK (node 0 7) (kid54.drop 0) = false := chainK _ _ 0 10 10 rfl t54_0 c54_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc54 : anyK (node 0 8) ((kR.drop 54).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid54 c54_0))
theorem rq54 : anyK (node 0 8) (kR.drop 54) = false := chainK _ _ 54 1 55 rfl sc54 rq55
def kid53 := kids (hdK (kR.drop 53)).1 (hdK (kR.drop 53)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c53_110 : anyK (node 0 7) (kid53.drop 110) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_100 : anyK (node 0 7) ((kid53.drop 100).take 10) = false := by decide +kernel
theorem c53_100 : anyK (node 0 7) (kid53.drop 100) = false := chainK _ _ 100 10 110 rfl t53_100 c53_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_90 : anyK (node 0 7) ((kid53.drop 90).take 10) = false := by decide +kernel
theorem c53_90 : anyK (node 0 7) (kid53.drop 90) = false := chainK _ _ 90 10 100 rfl t53_90 c53_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_80 : anyK (node 0 7) ((kid53.drop 80).take 10) = false := by decide +kernel
theorem c53_80 : anyK (node 0 7) (kid53.drop 80) = false := chainK _ _ 80 10 90 rfl t53_80 c53_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_70 : anyK (node 0 7) ((kid53.drop 70).take 10) = false := by decide +kernel
theorem c53_70 : anyK (node 0 7) (kid53.drop 70) = false := chainK _ _ 70 10 80 rfl t53_70 c53_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_60 : anyK (node 0 7) ((kid53.drop 60).take 10) = false := by decide +kernel
theorem c53_60 : anyK (node 0 7) (kid53.drop 60) = false := chainK _ _ 60 10 70 rfl t53_60 c53_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_50 : anyK (node 0 7) ((kid53.drop 50).take 10) = false := by decide +kernel
theorem c53_50 : anyK (node 0 7) (kid53.drop 50) = false := chainK _ _ 50 10 60 rfl t53_50 c53_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_40 : anyK (node 0 7) ((kid53.drop 40).take 10) = false := by decide +kernel
theorem c53_40 : anyK (node 0 7) (kid53.drop 40) = false := chainK _ _ 40 10 50 rfl t53_40 c53_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_30 : anyK (node 0 7) ((kid53.drop 30).take 10) = false := by decide +kernel
theorem c53_30 : anyK (node 0 7) (kid53.drop 30) = false := chainK _ _ 30 10 40 rfl t53_30 c53_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_20 : anyK (node 0 7) ((kid53.drop 20).take 10) = false := by decide +kernel
theorem c53_20 : anyK (node 0 7) (kid53.drop 20) = false := chainK _ _ 20 10 30 rfl t53_20 c53_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_10 : anyK (node 0 7) ((kid53.drop 10).take 10) = false := by decide +kernel
theorem c53_10 : anyK (node 0 7) (kid53.drop 10) = false := chainK _ _ 10 10 20 rfl t53_10 c53_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t53_0 : anyK (node 0 7) ((kid53.drop 0).take 10) = false := by decide +kernel
theorem c53_0 : anyK (node 0 7) (kid53.drop 0) = false := chainK _ _ 0 10 10 rfl t53_0 c53_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc53 : anyK (node 0 8) ((kR.drop 53).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid53 c53_0))
theorem rq53 : anyK (node 0 8) (kR.drop 53) = false := chainK _ _ 53 1 54 rfl sc53 rq54
def kid52 := kids (hdK (kR.drop 52)).1 (hdK (kR.drop 52)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c52_56 : anyK (node 0 7) (kid52.drop 56) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_50 : anyK (node 0 7) ((kid52.drop 50).take 6) = false := by decide +kernel
theorem c52_50 : anyK (node 0 7) (kid52.drop 50) = false := chainK _ _ 50 6 56 rfl t52_50 c52_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_40 : anyK (node 0 7) ((kid52.drop 40).take 10) = false := by decide +kernel
theorem c52_40 : anyK (node 0 7) (kid52.drop 40) = false := chainK _ _ 40 10 50 rfl t52_40 c52_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_30 : anyK (node 0 7) ((kid52.drop 30).take 10) = false := by decide +kernel
theorem c52_30 : anyK (node 0 7) (kid52.drop 30) = false := chainK _ _ 30 10 40 rfl t52_30 c52_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_20 : anyK (node 0 7) ((kid52.drop 20).take 10) = false := by decide +kernel
theorem c52_20 : anyK (node 0 7) (kid52.drop 20) = false := chainK _ _ 20 10 30 rfl t52_20 c52_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_10 : anyK (node 0 7) ((kid52.drop 10).take 10) = false := by decide +kernel
theorem c52_10 : anyK (node 0 7) (kid52.drop 10) = false := chainK _ _ 10 10 20 rfl t52_10 c52_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t52_0 : anyK (node 0 7) ((kid52.drop 0).take 10) = false := by decide +kernel
theorem c52_0 : anyK (node 0 7) (kid52.drop 0) = false := chainK _ _ 0 10 10 rfl t52_0 c52_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc52 : anyK (node 0 8) ((kR.drop 52).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid52 c52_0))
theorem rq52 : anyK (node 0 8) (kR.drop 52) = false := chainK _ _ 52 1 53 rfl sc52 rq53
def kid51 := kids (hdK (kR.drop 51)).1 (hdK (kR.drop 51)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c51_105 : anyK (node 0 7) (kid51.drop 105) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_100 : anyK (node 0 7) ((kid51.drop 100).take 5) = false := by decide +kernel
theorem c51_100 : anyK (node 0 7) (kid51.drop 100) = false := chainK _ _ 100 5 105 rfl t51_100 c51_105
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_90 : anyK (node 0 7) ((kid51.drop 90).take 10) = false := by decide +kernel
theorem c51_90 : anyK (node 0 7) (kid51.drop 90) = false := chainK _ _ 90 10 100 rfl t51_90 c51_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_80 : anyK (node 0 7) ((kid51.drop 80).take 10) = false := by decide +kernel
theorem c51_80 : anyK (node 0 7) (kid51.drop 80) = false := chainK _ _ 80 10 90 rfl t51_80 c51_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_70 : anyK (node 0 7) ((kid51.drop 70).take 10) = false := by decide +kernel
theorem c51_70 : anyK (node 0 7) (kid51.drop 70) = false := chainK _ _ 70 10 80 rfl t51_70 c51_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_60 : anyK (node 0 7) ((kid51.drop 60).take 10) = false := by decide +kernel
theorem c51_60 : anyK (node 0 7) (kid51.drop 60) = false := chainK _ _ 60 10 70 rfl t51_60 c51_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_50 : anyK (node 0 7) ((kid51.drop 50).take 10) = false := by decide +kernel
theorem c51_50 : anyK (node 0 7) (kid51.drop 50) = false := chainK _ _ 50 10 60 rfl t51_50 c51_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_40 : anyK (node 0 7) ((kid51.drop 40).take 10) = false := by decide +kernel
theorem c51_40 : anyK (node 0 7) (kid51.drop 40) = false := chainK _ _ 40 10 50 rfl t51_40 c51_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_30 : anyK (node 0 7) ((kid51.drop 30).take 10) = false := by decide +kernel
theorem c51_30 : anyK (node 0 7) (kid51.drop 30) = false := chainK _ _ 30 10 40 rfl t51_30 c51_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_20 : anyK (node 0 7) ((kid51.drop 20).take 10) = false := by decide +kernel
theorem c51_20 : anyK (node 0 7) (kid51.drop 20) = false := chainK _ _ 20 10 30 rfl t51_20 c51_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_10 : anyK (node 0 7) ((kid51.drop 10).take 10) = false := by decide +kernel
theorem c51_10 : anyK (node 0 7) (kid51.drop 10) = false := chainK _ _ 10 10 20 rfl t51_10 c51_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t51_0 : anyK (node 0 7) ((kid51.drop 0).take 10) = false := by decide +kernel
theorem c51_0 : anyK (node 0 7) (kid51.drop 0) = false := chainK _ _ 0 10 10 rfl t51_0 c51_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc51 : anyK (node 0 8) ((kR.drop 51).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid51 c51_0))
theorem rq51 : anyK (node 0 8) (kR.drop 51) = false := chainK _ _ 51 1 52 rfl sc51 rq52
def kid50 := kids (hdK (kR.drop 50)).1 (hdK (kR.drop 50)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c50_79 : anyK (node 0 7) (kid50.drop 79) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_70 : anyK (node 0 7) ((kid50.drop 70).take 9) = false := by decide +kernel
theorem c50_70 : anyK (node 0 7) (kid50.drop 70) = false := chainK _ _ 70 9 79 rfl t50_70 c50_79
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_60 : anyK (node 0 7) ((kid50.drop 60).take 10) = false := by decide +kernel
theorem c50_60 : anyK (node 0 7) (kid50.drop 60) = false := chainK _ _ 60 10 70 rfl t50_60 c50_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_50 : anyK (node 0 7) ((kid50.drop 50).take 10) = false := by decide +kernel
theorem c50_50 : anyK (node 0 7) (kid50.drop 50) = false := chainK _ _ 50 10 60 rfl t50_50 c50_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_40 : anyK (node 0 7) ((kid50.drop 40).take 10) = false := by decide +kernel
theorem c50_40 : anyK (node 0 7) (kid50.drop 40) = false := chainK _ _ 40 10 50 rfl t50_40 c50_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_30 : anyK (node 0 7) ((kid50.drop 30).take 10) = false := by decide +kernel
theorem c50_30 : anyK (node 0 7) (kid50.drop 30) = false := chainK _ _ 30 10 40 rfl t50_30 c50_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_20 : anyK (node 0 7) ((kid50.drop 20).take 10) = false := by decide +kernel
theorem c50_20 : anyK (node 0 7) (kid50.drop 20) = false := chainK _ _ 20 10 30 rfl t50_20 c50_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_10 : anyK (node 0 7) ((kid50.drop 10).take 10) = false := by decide +kernel
theorem c50_10 : anyK (node 0 7) (kid50.drop 10) = false := chainK _ _ 10 10 20 rfl t50_10 c50_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t50_0 : anyK (node 0 7) ((kid50.drop 0).take 10) = false := by decide +kernel
theorem c50_0 : anyK (node 0 7) (kid50.drop 0) = false := chainK _ _ 0 10 10 rfl t50_0 c50_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc50 : anyK (node 0 8) ((kR.drop 50).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid50 c50_0))
theorem rq50 : anyK (node 0 8) (kR.drop 50) = false := chainK _ _ 50 1 51 rfl sc50 rq51
def kid49 := kids (hdK (kR.drop 49)).1 (hdK (kR.drop 49)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c49_64 : anyK (node 0 7) (kid49.drop 64) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_60 : anyK (node 0 7) ((kid49.drop 60).take 4) = false := by decide +kernel
theorem c49_60 : anyK (node 0 7) (kid49.drop 60) = false := chainK _ _ 60 4 64 rfl t49_60 c49_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_50 : anyK (node 0 7) ((kid49.drop 50).take 10) = false := by decide +kernel
theorem c49_50 : anyK (node 0 7) (kid49.drop 50) = false := chainK _ _ 50 10 60 rfl t49_50 c49_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_40 : anyK (node 0 7) ((kid49.drop 40).take 10) = false := by decide +kernel
theorem c49_40 : anyK (node 0 7) (kid49.drop 40) = false := chainK _ _ 40 10 50 rfl t49_40 c49_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_30 : anyK (node 0 7) ((kid49.drop 30).take 10) = false := by decide +kernel
theorem c49_30 : anyK (node 0 7) (kid49.drop 30) = false := chainK _ _ 30 10 40 rfl t49_30 c49_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_20 : anyK (node 0 7) ((kid49.drop 20).take 10) = false := by decide +kernel
theorem c49_20 : anyK (node 0 7) (kid49.drop 20) = false := chainK _ _ 20 10 30 rfl t49_20 c49_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_10 : anyK (node 0 7) ((kid49.drop 10).take 10) = false := by decide +kernel
theorem c49_10 : anyK (node 0 7) (kid49.drop 10) = false := chainK _ _ 10 10 20 rfl t49_10 c49_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t49_0 : anyK (node 0 7) ((kid49.drop 0).take 10) = false := by decide +kernel
theorem c49_0 : anyK (node 0 7) (kid49.drop 0) = false := chainK _ _ 0 10 10 rfl t49_0 c49_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc49 : anyK (node 0 8) ((kR.drop 49).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid49 c49_0))
theorem rq49 : anyK (node 0 8) (kR.drop 49) = false := chainK _ _ 49 1 50 rfl sc49 rq50
def kid48 := kids (hdK (kR.drop 48)).1 (hdK (kR.drop 48)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c48_84 : anyK (node 0 7) (kid48.drop 84) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_80 : anyK (node 0 7) ((kid48.drop 80).take 4) = false := by decide +kernel
theorem c48_80 : anyK (node 0 7) (kid48.drop 80) = false := chainK _ _ 80 4 84 rfl t48_80 c48_84
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_70 : anyK (node 0 7) ((kid48.drop 70).take 10) = false := by decide +kernel
theorem c48_70 : anyK (node 0 7) (kid48.drop 70) = false := chainK _ _ 70 10 80 rfl t48_70 c48_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_60 : anyK (node 0 7) ((kid48.drop 60).take 10) = false := by decide +kernel
theorem c48_60 : anyK (node 0 7) (kid48.drop 60) = false := chainK _ _ 60 10 70 rfl t48_60 c48_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_50 : anyK (node 0 7) ((kid48.drop 50).take 10) = false := by decide +kernel
theorem c48_50 : anyK (node 0 7) (kid48.drop 50) = false := chainK _ _ 50 10 60 rfl t48_50 c48_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_40 : anyK (node 0 7) ((kid48.drop 40).take 10) = false := by decide +kernel
theorem c48_40 : anyK (node 0 7) (kid48.drop 40) = false := chainK _ _ 40 10 50 rfl t48_40 c48_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_30 : anyK (node 0 7) ((kid48.drop 30).take 10) = false := by decide +kernel
theorem c48_30 : anyK (node 0 7) (kid48.drop 30) = false := chainK _ _ 30 10 40 rfl t48_30 c48_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_20 : anyK (node 0 7) ((kid48.drop 20).take 10) = false := by decide +kernel
theorem c48_20 : anyK (node 0 7) (kid48.drop 20) = false := chainK _ _ 20 10 30 rfl t48_20 c48_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_10 : anyK (node 0 7) ((kid48.drop 10).take 10) = false := by decide +kernel
theorem c48_10 : anyK (node 0 7) (kid48.drop 10) = false := chainK _ _ 10 10 20 rfl t48_10 c48_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t48_0 : anyK (node 0 7) ((kid48.drop 0).take 10) = false := by decide +kernel
theorem c48_0 : anyK (node 0 7) (kid48.drop 0) = false := chainK _ _ 0 10 10 rfl t48_0 c48_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc48 : anyK (node 0 8) ((kR.drop 48).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid48 c48_0))
theorem rq48 : anyK (node 0 8) (kR.drop 48) = false := chainK _ _ 48 1 49 rfl sc48 rq49
def kid47 := kids (hdK (kR.drop 47)).1 (hdK (kR.drop 47)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c47_102 : anyK (node 0 7) (kid47.drop 102) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_100 : anyK (node 0 7) ((kid47.drop 100).take 2) = false := by decide +kernel
theorem c47_100 : anyK (node 0 7) (kid47.drop 100) = false := chainK _ _ 100 2 102 rfl t47_100 c47_102
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_90 : anyK (node 0 7) ((kid47.drop 90).take 10) = false := by decide +kernel
theorem c47_90 : anyK (node 0 7) (kid47.drop 90) = false := chainK _ _ 90 10 100 rfl t47_90 c47_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_80 : anyK (node 0 7) ((kid47.drop 80).take 10) = false := by decide +kernel
theorem c47_80 : anyK (node 0 7) (kid47.drop 80) = false := chainK _ _ 80 10 90 rfl t47_80 c47_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_70 : anyK (node 0 7) ((kid47.drop 70).take 10) = false := by decide +kernel
theorem c47_70 : anyK (node 0 7) (kid47.drop 70) = false := chainK _ _ 70 10 80 rfl t47_70 c47_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_60 : anyK (node 0 7) ((kid47.drop 60).take 10) = false := by decide +kernel
theorem c47_60 : anyK (node 0 7) (kid47.drop 60) = false := chainK _ _ 60 10 70 rfl t47_60 c47_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_50 : anyK (node 0 7) ((kid47.drop 50).take 10) = false := by decide +kernel
theorem c47_50 : anyK (node 0 7) (kid47.drop 50) = false := chainK _ _ 50 10 60 rfl t47_50 c47_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_40 : anyK (node 0 7) ((kid47.drop 40).take 10) = false := by decide +kernel
theorem c47_40 : anyK (node 0 7) (kid47.drop 40) = false := chainK _ _ 40 10 50 rfl t47_40 c47_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_30 : anyK (node 0 7) ((kid47.drop 30).take 10) = false := by decide +kernel
theorem c47_30 : anyK (node 0 7) (kid47.drop 30) = false := chainK _ _ 30 10 40 rfl t47_30 c47_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_20 : anyK (node 0 7) ((kid47.drop 20).take 10) = false := by decide +kernel
theorem c47_20 : anyK (node 0 7) (kid47.drop 20) = false := chainK _ _ 20 10 30 rfl t47_20 c47_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_10 : anyK (node 0 7) ((kid47.drop 10).take 10) = false := by decide +kernel
theorem c47_10 : anyK (node 0 7) (kid47.drop 10) = false := chainK _ _ 10 10 20 rfl t47_10 c47_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t47_0 : anyK (node 0 7) ((kid47.drop 0).take 10) = false := by decide +kernel
theorem c47_0 : anyK (node 0 7) (kid47.drop 0) = false := chainK _ _ 0 10 10 rfl t47_0 c47_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc47 : anyK (node 0 8) ((kR.drop 47).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid47 c47_0))
theorem rq47 : anyK (node 0 8) (kR.drop 47) = false := chainK _ _ 47 1 48 rfl sc47 rq48
def kid46 := kids (hdK (kR.drop 46)).1 (hdK (kR.drop 46)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c46_77 : anyK (node 0 7) (kid46.drop 77) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_70 : anyK (node 0 7) ((kid46.drop 70).take 7) = false := by decide +kernel
theorem c46_70 : anyK (node 0 7) (kid46.drop 70) = false := chainK _ _ 70 7 77 rfl t46_70 c46_77
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_60 : anyK (node 0 7) ((kid46.drop 60).take 10) = false := by decide +kernel
theorem c46_60 : anyK (node 0 7) (kid46.drop 60) = false := chainK _ _ 60 10 70 rfl t46_60 c46_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_50 : anyK (node 0 7) ((kid46.drop 50).take 10) = false := by decide +kernel
theorem c46_50 : anyK (node 0 7) (kid46.drop 50) = false := chainK _ _ 50 10 60 rfl t46_50 c46_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_40 : anyK (node 0 7) ((kid46.drop 40).take 10) = false := by decide +kernel
theorem c46_40 : anyK (node 0 7) (kid46.drop 40) = false := chainK _ _ 40 10 50 rfl t46_40 c46_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_30 : anyK (node 0 7) ((kid46.drop 30).take 10) = false := by decide +kernel
theorem c46_30 : anyK (node 0 7) (kid46.drop 30) = false := chainK _ _ 30 10 40 rfl t46_30 c46_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_20 : anyK (node 0 7) ((kid46.drop 20).take 10) = false := by decide +kernel
theorem c46_20 : anyK (node 0 7) (kid46.drop 20) = false := chainK _ _ 20 10 30 rfl t46_20 c46_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_10 : anyK (node 0 7) ((kid46.drop 10).take 10) = false := by decide +kernel
theorem c46_10 : anyK (node 0 7) (kid46.drop 10) = false := chainK _ _ 10 10 20 rfl t46_10 c46_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t46_0 : anyK (node 0 7) ((kid46.drop 0).take 10) = false := by decide +kernel
theorem c46_0 : anyK (node 0 7) (kid46.drop 0) = false := chainK _ _ 0 10 10 rfl t46_0 c46_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc46 : anyK (node 0 8) ((kR.drop 46).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid46 c46_0))
theorem rq46 : anyK (node 0 8) (kR.drop 46) = false := chainK _ _ 46 1 47 rfl sc46 rq47
def kid45 := kids (hdK (kR.drop 45)).1 (hdK (kR.drop 45)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c45_63 : anyK (node 0 7) (kid45.drop 63) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_60 : anyK (node 0 7) ((kid45.drop 60).take 3) = false := by decide +kernel
theorem c45_60 : anyK (node 0 7) (kid45.drop 60) = false := chainK _ _ 60 3 63 rfl t45_60 c45_63
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_50 : anyK (node 0 7) ((kid45.drop 50).take 10) = false := by decide +kernel
theorem c45_50 : anyK (node 0 7) (kid45.drop 50) = false := chainK _ _ 50 10 60 rfl t45_50 c45_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_40 : anyK (node 0 7) ((kid45.drop 40).take 10) = false := by decide +kernel
theorem c45_40 : anyK (node 0 7) (kid45.drop 40) = false := chainK _ _ 40 10 50 rfl t45_40 c45_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_30 : anyK (node 0 7) ((kid45.drop 30).take 10) = false := by decide +kernel
theorem c45_30 : anyK (node 0 7) (kid45.drop 30) = false := chainK _ _ 30 10 40 rfl t45_30 c45_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_20 : anyK (node 0 7) ((kid45.drop 20).take 10) = false := by decide +kernel
theorem c45_20 : anyK (node 0 7) (kid45.drop 20) = false := chainK _ _ 20 10 30 rfl t45_20 c45_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_10 : anyK (node 0 7) ((kid45.drop 10).take 10) = false := by decide +kernel
theorem c45_10 : anyK (node 0 7) (kid45.drop 10) = false := chainK _ _ 10 10 20 rfl t45_10 c45_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t45_0 : anyK (node 0 7) ((kid45.drop 0).take 10) = false := by decide +kernel
theorem c45_0 : anyK (node 0 7) (kid45.drop 0) = false := chainK _ _ 0 10 10 rfl t45_0 c45_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc45 : anyK (node 0 8) ((kR.drop 45).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid45 c45_0))
theorem rq45 : anyK (node 0 8) (kR.drop 45) = false := chainK _ _ 45 1 46 rfl sc45 rq46
def kid44 := kids (hdK (kR.drop 44)).1 (hdK (kR.drop 44)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c44_95 : anyK (node 0 7) (kid44.drop 95) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_90 : anyK (node 0 7) ((kid44.drop 90).take 5) = false := by decide +kernel
theorem c44_90 : anyK (node 0 7) (kid44.drop 90) = false := chainK _ _ 90 5 95 rfl t44_90 c44_95
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_80 : anyK (node 0 7) ((kid44.drop 80).take 10) = false := by decide +kernel
theorem c44_80 : anyK (node 0 7) (kid44.drop 80) = false := chainK _ _ 80 10 90 rfl t44_80 c44_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_70 : anyK (node 0 7) ((kid44.drop 70).take 10) = false := by decide +kernel
theorem c44_70 : anyK (node 0 7) (kid44.drop 70) = false := chainK _ _ 70 10 80 rfl t44_70 c44_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_60 : anyK (node 0 7) ((kid44.drop 60).take 10) = false := by decide +kernel
theorem c44_60 : anyK (node 0 7) (kid44.drop 60) = false := chainK _ _ 60 10 70 rfl t44_60 c44_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_50 : anyK (node 0 7) ((kid44.drop 50).take 10) = false := by decide +kernel
theorem c44_50 : anyK (node 0 7) (kid44.drop 50) = false := chainK _ _ 50 10 60 rfl t44_50 c44_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_40 : anyK (node 0 7) ((kid44.drop 40).take 10) = false := by decide +kernel
theorem c44_40 : anyK (node 0 7) (kid44.drop 40) = false := chainK _ _ 40 10 50 rfl t44_40 c44_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_30 : anyK (node 0 7) ((kid44.drop 30).take 10) = false := by decide +kernel
theorem c44_30 : anyK (node 0 7) (kid44.drop 30) = false := chainK _ _ 30 10 40 rfl t44_30 c44_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_20 : anyK (node 0 7) ((kid44.drop 20).take 10) = false := by decide +kernel
theorem c44_20 : anyK (node 0 7) (kid44.drop 20) = false := chainK _ _ 20 10 30 rfl t44_20 c44_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_10 : anyK (node 0 7) ((kid44.drop 10).take 10) = false := by decide +kernel
theorem c44_10 : anyK (node 0 7) (kid44.drop 10) = false := chainK _ _ 10 10 20 rfl t44_10 c44_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t44_0 : anyK (node 0 7) ((kid44.drop 0).take 10) = false := by decide +kernel
theorem c44_0 : anyK (node 0 7) (kid44.drop 0) = false := chainK _ _ 0 10 10 rfl t44_0 c44_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc44 : anyK (node 0 8) ((kR.drop 44).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid44 c44_0))
theorem rq44 : anyK (node 0 8) (kR.drop 44) = false := chainK _ _ 44 1 45 rfl sc44 rq45
def kid43 := kids (hdK (kR.drop 43)).1 (hdK (kR.drop 43)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c43_76 : anyK (node 0 7) (kid43.drop 76) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_70 : anyK (node 0 7) ((kid43.drop 70).take 6) = false := by decide +kernel
theorem c43_70 : anyK (node 0 7) (kid43.drop 70) = false := chainK _ _ 70 6 76 rfl t43_70 c43_76
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_60 : anyK (node 0 7) ((kid43.drop 60).take 10) = false := by decide +kernel
theorem c43_60 : anyK (node 0 7) (kid43.drop 60) = false := chainK _ _ 60 10 70 rfl t43_60 c43_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_50 : anyK (node 0 7) ((kid43.drop 50).take 10) = false := by decide +kernel
theorem c43_50 : anyK (node 0 7) (kid43.drop 50) = false := chainK _ _ 50 10 60 rfl t43_50 c43_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_40 : anyK (node 0 7) ((kid43.drop 40).take 10) = false := by decide +kernel
theorem c43_40 : anyK (node 0 7) (kid43.drop 40) = false := chainK _ _ 40 10 50 rfl t43_40 c43_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_30 : anyK (node 0 7) ((kid43.drop 30).take 10) = false := by decide +kernel
theorem c43_30 : anyK (node 0 7) (kid43.drop 30) = false := chainK _ _ 30 10 40 rfl t43_30 c43_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_20 : anyK (node 0 7) ((kid43.drop 20).take 10) = false := by decide +kernel
theorem c43_20 : anyK (node 0 7) (kid43.drop 20) = false := chainK _ _ 20 10 30 rfl t43_20 c43_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_10 : anyK (node 0 7) ((kid43.drop 10).take 10) = false := by decide +kernel
theorem c43_10 : anyK (node 0 7) (kid43.drop 10) = false := chainK _ _ 10 10 20 rfl t43_10 c43_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t43_0 : anyK (node 0 7) ((kid43.drop 0).take 10) = false := by decide +kernel
theorem c43_0 : anyK (node 0 7) (kid43.drop 0) = false := chainK _ _ 0 10 10 rfl t43_0 c43_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc43 : anyK (node 0 8) ((kR.drop 43).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid43 c43_0))
theorem rq43 : anyK (node 0 8) (kR.drop 43) = false := chainK _ _ 43 1 44 rfl sc43 rq44
def kid42 := kids (hdK (kR.drop 42)).1 (hdK (kR.drop 42)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c42_95 : anyK (node 0 7) (kid42.drop 95) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_90 : anyK (node 0 7) ((kid42.drop 90).take 5) = false := by decide +kernel
theorem c42_90 : anyK (node 0 7) (kid42.drop 90) = false := chainK _ _ 90 5 95 rfl t42_90 c42_95
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_80 : anyK (node 0 7) ((kid42.drop 80).take 10) = false := by decide +kernel
theorem c42_80 : anyK (node 0 7) (kid42.drop 80) = false := chainK _ _ 80 10 90 rfl t42_80 c42_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_70 : anyK (node 0 7) ((kid42.drop 70).take 10) = false := by decide +kernel
theorem c42_70 : anyK (node 0 7) (kid42.drop 70) = false := chainK _ _ 70 10 80 rfl t42_70 c42_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_60 : anyK (node 0 7) ((kid42.drop 60).take 10) = false := by decide +kernel
theorem c42_60 : anyK (node 0 7) (kid42.drop 60) = false := chainK _ _ 60 10 70 rfl t42_60 c42_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_50 : anyK (node 0 7) ((kid42.drop 50).take 10) = false := by decide +kernel
theorem c42_50 : anyK (node 0 7) (kid42.drop 50) = false := chainK _ _ 50 10 60 rfl t42_50 c42_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_40 : anyK (node 0 7) ((kid42.drop 40).take 10) = false := by decide +kernel
theorem c42_40 : anyK (node 0 7) (kid42.drop 40) = false := chainK _ _ 40 10 50 rfl t42_40 c42_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_30 : anyK (node 0 7) ((kid42.drop 30).take 10) = false := by decide +kernel
theorem c42_30 : anyK (node 0 7) (kid42.drop 30) = false := chainK _ _ 30 10 40 rfl t42_30 c42_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_20 : anyK (node 0 7) ((kid42.drop 20).take 10) = false := by decide +kernel
theorem c42_20 : anyK (node 0 7) (kid42.drop 20) = false := chainK _ _ 20 10 30 rfl t42_20 c42_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_10 : anyK (node 0 7) ((kid42.drop 10).take 10) = false := by decide +kernel
theorem c42_10 : anyK (node 0 7) (kid42.drop 10) = false := chainK _ _ 10 10 20 rfl t42_10 c42_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t42_0 : anyK (node 0 7) ((kid42.drop 0).take 10) = false := by decide +kernel
theorem c42_0 : anyK (node 0 7) (kid42.drop 0) = false := chainK _ _ 0 10 10 rfl t42_0 c42_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc42 : anyK (node 0 8) ((kR.drop 42).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid42 c42_0))
theorem rq42 : anyK (node 0 8) (kR.drop 42) = false := chainK _ _ 42 1 43 rfl sc42 rq43
def kid41 := kids (hdK (kR.drop 41)).1 (hdK (kR.drop 41)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c41_61 : anyK (node 0 7) (kid41.drop 61) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_60 : anyK (node 0 7) ((kid41.drop 60).take 1) = false := by decide +kernel
theorem c41_60 : anyK (node 0 7) (kid41.drop 60) = false := chainK _ _ 60 1 61 rfl t41_60 c41_61
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_50 : anyK (node 0 7) ((kid41.drop 50).take 10) = false := by decide +kernel
theorem c41_50 : anyK (node 0 7) (kid41.drop 50) = false := chainK _ _ 50 10 60 rfl t41_50 c41_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_40 : anyK (node 0 7) ((kid41.drop 40).take 10) = false := by decide +kernel
theorem c41_40 : anyK (node 0 7) (kid41.drop 40) = false := chainK _ _ 40 10 50 rfl t41_40 c41_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_30 : anyK (node 0 7) ((kid41.drop 30).take 10) = false := by decide +kernel
theorem c41_30 : anyK (node 0 7) (kid41.drop 30) = false := chainK _ _ 30 10 40 rfl t41_30 c41_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_20 : anyK (node 0 7) ((kid41.drop 20).take 10) = false := by decide +kernel
theorem c41_20 : anyK (node 0 7) (kid41.drop 20) = false := chainK _ _ 20 10 30 rfl t41_20 c41_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_10 : anyK (node 0 7) ((kid41.drop 10).take 10) = false := by decide +kernel
theorem c41_10 : anyK (node 0 7) (kid41.drop 10) = false := chainK _ _ 10 10 20 rfl t41_10 c41_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t41_0 : anyK (node 0 7) ((kid41.drop 0).take 10) = false := by decide +kernel
theorem c41_0 : anyK (node 0 7) (kid41.drop 0) = false := chainK _ _ 0 10 10 rfl t41_0 c41_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc41 : anyK (node 0 8) ((kR.drop 41).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid41 c41_0))
theorem rq41 : anyK (node 0 8) (kR.drop 41) = false := chainK _ _ 41 1 42 rfl sc41 rq42
def kid40 := kids (hdK (kR.drop 40)).1 (hdK (kR.drop 40)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c40_70 : anyK (node 0 7) (kid40.drop 70) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_60 : anyK (node 0 7) ((kid40.drop 60).take 10) = false := by decide +kernel
theorem c40_60 : anyK (node 0 7) (kid40.drop 60) = false := chainK _ _ 60 10 70 rfl t40_60 c40_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_50 : anyK (node 0 7) ((kid40.drop 50).take 10) = false := by decide +kernel
theorem c40_50 : anyK (node 0 7) (kid40.drop 50) = false := chainK _ _ 50 10 60 rfl t40_50 c40_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_40 : anyK (node 0 7) ((kid40.drop 40).take 10) = false := by decide +kernel
theorem c40_40 : anyK (node 0 7) (kid40.drop 40) = false := chainK _ _ 40 10 50 rfl t40_40 c40_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_30 : anyK (node 0 7) ((kid40.drop 30).take 10) = false := by decide +kernel
theorem c40_30 : anyK (node 0 7) (kid40.drop 30) = false := chainK _ _ 30 10 40 rfl t40_30 c40_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_20 : anyK (node 0 7) ((kid40.drop 20).take 10) = false := by decide +kernel
theorem c40_20 : anyK (node 0 7) (kid40.drop 20) = false := chainK _ _ 20 10 30 rfl t40_20 c40_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_10 : anyK (node 0 7) ((kid40.drop 10).take 10) = false := by decide +kernel
theorem c40_10 : anyK (node 0 7) (kid40.drop 10) = false := chainK _ _ 10 10 20 rfl t40_10 c40_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t40_0 : anyK (node 0 7) ((kid40.drop 0).take 10) = false := by decide +kernel
theorem c40_0 : anyK (node 0 7) (kid40.drop 0) = false := chainK _ _ 0 10 10 rfl t40_0 c40_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc40 : anyK (node 0 8) ((kR.drop 40).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid40 c40_0))
theorem rq40 : anyK (node 0 8) (kR.drop 40) = false := chainK _ _ 40 1 41 rfl sc40 rq41
def kid39 := kids (hdK (kR.drop 39)).1 (hdK (kR.drop 39)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c39_83 : anyK (node 0 7) (kid39.drop 83) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_80 : anyK (node 0 7) ((kid39.drop 80).take 3) = false := by decide +kernel
theorem c39_80 : anyK (node 0 7) (kid39.drop 80) = false := chainK _ _ 80 3 83 rfl t39_80 c39_83
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_70 : anyK (node 0 7) ((kid39.drop 70).take 10) = false := by decide +kernel
theorem c39_70 : anyK (node 0 7) (kid39.drop 70) = false := chainK _ _ 70 10 80 rfl t39_70 c39_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_60 : anyK (node 0 7) ((kid39.drop 60).take 10) = false := by decide +kernel
theorem c39_60 : anyK (node 0 7) (kid39.drop 60) = false := chainK _ _ 60 10 70 rfl t39_60 c39_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_50 : anyK (node 0 7) ((kid39.drop 50).take 10) = false := by decide +kernel
theorem c39_50 : anyK (node 0 7) (kid39.drop 50) = false := chainK _ _ 50 10 60 rfl t39_50 c39_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_40 : anyK (node 0 7) ((kid39.drop 40).take 10) = false := by decide +kernel
theorem c39_40 : anyK (node 0 7) (kid39.drop 40) = false := chainK _ _ 40 10 50 rfl t39_40 c39_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_30 : anyK (node 0 7) ((kid39.drop 30).take 10) = false := by decide +kernel
theorem c39_30 : anyK (node 0 7) (kid39.drop 30) = false := chainK _ _ 30 10 40 rfl t39_30 c39_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_20 : anyK (node 0 7) ((kid39.drop 20).take 10) = false := by decide +kernel
theorem c39_20 : anyK (node 0 7) (kid39.drop 20) = false := chainK _ _ 20 10 30 rfl t39_20 c39_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_10 : anyK (node 0 7) ((kid39.drop 10).take 10) = false := by decide +kernel
theorem c39_10 : anyK (node 0 7) (kid39.drop 10) = false := chainK _ _ 10 10 20 rfl t39_10 c39_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_0 : anyK (node 0 7) ((kid39.drop 0).take 10) = false := by decide +kernel
theorem c39_0 : anyK (node 0 7) (kid39.drop 0) = false := chainK _ _ 0 10 10 rfl t39_0 c39_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc39 : anyK (node 0 8) ((kR.drop 39).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid39 c39_0))
theorem rq39 : anyK (node 0 8) (kR.drop 39) = false := chainK _ _ 39 1 40 rfl sc39 rq40
def kid38 := kids (hdK (kR.drop 38)).1 (hdK (kR.drop 38)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c38_52 : anyK (node 0 7) (kid38.drop 52) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_50 : anyK (node 0 7) ((kid38.drop 50).take 2) = false := by decide +kernel
theorem c38_50 : anyK (node 0 7) (kid38.drop 50) = false := chainK _ _ 50 2 52 rfl t38_50 c38_52
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_40 : anyK (node 0 7) ((kid38.drop 40).take 10) = false := by decide +kernel
theorem c38_40 : anyK (node 0 7) (kid38.drop 40) = false := chainK _ _ 40 10 50 rfl t38_40 c38_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_30 : anyK (node 0 7) ((kid38.drop 30).take 10) = false := by decide +kernel
theorem c38_30 : anyK (node 0 7) (kid38.drop 30) = false := chainK _ _ 30 10 40 rfl t38_30 c38_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_20 : anyK (node 0 7) ((kid38.drop 20).take 10) = false := by decide +kernel
theorem c38_20 : anyK (node 0 7) (kid38.drop 20) = false := chainK _ _ 20 10 30 rfl t38_20 c38_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_10 : anyK (node 0 7) ((kid38.drop 10).take 10) = false := by decide +kernel
theorem c38_10 : anyK (node 0 7) (kid38.drop 10) = false := chainK _ _ 10 10 20 rfl t38_10 c38_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_0 : anyK (node 0 7) ((kid38.drop 0).take 10) = false := by decide +kernel
theorem c38_0 : anyK (node 0 7) (kid38.drop 0) = false := chainK _ _ 0 10 10 rfl t38_0 c38_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc38 : anyK (node 0 8) ((kR.drop 38).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid38 c38_0))
theorem rq38 : anyK (node 0 8) (kR.drop 38) = false := chainK _ _ 38 1 39 rfl sc38 rq39
def kid37 := kids (hdK (kR.drop 37)).1 (hdK (kR.drop 37)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c37_48 : anyK (node 0 7) (kid37.drop 48) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_40 : anyK (node 0 7) ((kid37.drop 40).take 8) = false := by decide +kernel
theorem c37_40 : anyK (node 0 7) (kid37.drop 40) = false := chainK _ _ 40 8 48 rfl t37_40 c37_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_30 : anyK (node 0 7) ((kid37.drop 30).take 10) = false := by decide +kernel
theorem c37_30 : anyK (node 0 7) (kid37.drop 30) = false := chainK _ _ 30 10 40 rfl t37_30 c37_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_20 : anyK (node 0 7) ((kid37.drop 20).take 10) = false := by decide +kernel
theorem c37_20 : anyK (node 0 7) (kid37.drop 20) = false := chainK _ _ 20 10 30 rfl t37_20 c37_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_10 : anyK (node 0 7) ((kid37.drop 10).take 10) = false := by decide +kernel
theorem c37_10 : anyK (node 0 7) (kid37.drop 10) = false := chainK _ _ 10 10 20 rfl t37_10 c37_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_0 : anyK (node 0 7) ((kid37.drop 0).take 10) = false := by decide +kernel
theorem c37_0 : anyK (node 0 7) (kid37.drop 0) = false := chainK _ _ 0 10 10 rfl t37_0 c37_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc37 : anyK (node 0 8) ((kR.drop 37).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid37 c37_0))
theorem rq37 : anyK (node 0 8) (kR.drop 37) = false := chainK _ _ 37 1 38 rfl sc37 rq38
def kid36 := kids (hdK (kR.drop 36)).1 (hdK (kR.drop 36)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c36_106 : anyK (node 0 7) (kid36.drop 106) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_100 : anyK (node 0 7) ((kid36.drop 100).take 6) = false := by decide +kernel
theorem c36_100 : anyK (node 0 7) (kid36.drop 100) = false := chainK _ _ 100 6 106 rfl t36_100 c36_106
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_90 : anyK (node 0 7) ((kid36.drop 90).take 10) = false := by decide +kernel
theorem c36_90 : anyK (node 0 7) (kid36.drop 90) = false := chainK _ _ 90 10 100 rfl t36_90 c36_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_80 : anyK (node 0 7) ((kid36.drop 80).take 10) = false := by decide +kernel
theorem c36_80 : anyK (node 0 7) (kid36.drop 80) = false := chainK _ _ 80 10 90 rfl t36_80 c36_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_70 : anyK (node 0 7) ((kid36.drop 70).take 10) = false := by decide +kernel
theorem c36_70 : anyK (node 0 7) (kid36.drop 70) = false := chainK _ _ 70 10 80 rfl t36_70 c36_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_60 : anyK (node 0 7) ((kid36.drop 60).take 10) = false := by decide +kernel
theorem c36_60 : anyK (node 0 7) (kid36.drop 60) = false := chainK _ _ 60 10 70 rfl t36_60 c36_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_50 : anyK (node 0 7) ((kid36.drop 50).take 10) = false := by decide +kernel
theorem c36_50 : anyK (node 0 7) (kid36.drop 50) = false := chainK _ _ 50 10 60 rfl t36_50 c36_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_40 : anyK (node 0 7) ((kid36.drop 40).take 10) = false := by decide +kernel
theorem c36_40 : anyK (node 0 7) (kid36.drop 40) = false := chainK _ _ 40 10 50 rfl t36_40 c36_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_30 : anyK (node 0 7) ((kid36.drop 30).take 10) = false := by decide +kernel
theorem c36_30 : anyK (node 0 7) (kid36.drop 30) = false := chainK _ _ 30 10 40 rfl t36_30 c36_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_20 : anyK (node 0 7) ((kid36.drop 20).take 10) = false := by decide +kernel
theorem c36_20 : anyK (node 0 7) (kid36.drop 20) = false := chainK _ _ 20 10 30 rfl t36_20 c36_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_10 : anyK (node 0 7) ((kid36.drop 10).take 10) = false := by decide +kernel
theorem c36_10 : anyK (node 0 7) (kid36.drop 10) = false := chainK _ _ 10 10 20 rfl t36_10 c36_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_0 : anyK (node 0 7) ((kid36.drop 0).take 10) = false := by decide +kernel
theorem c36_0 : anyK (node 0 7) (kid36.drop 0) = false := chainK _ _ 0 10 10 rfl t36_0 c36_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc36 : anyK (node 0 8) ((kR.drop 36).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid36 c36_0))
theorem rq36 : anyK (node 0 8) (kR.drop 36) = false := chainK _ _ 36 1 37 rfl sc36 rq37
def kid35 := kids (hdK (kR.drop 35)).1 (hdK (kR.drop 35)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c35_93 : anyK (node 0 7) (kid35.drop 93) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_90 : anyK (node 0 7) ((kid35.drop 90).take 3) = false := by decide +kernel
theorem c35_90 : anyK (node 0 7) (kid35.drop 90) = false := chainK _ _ 90 3 93 rfl t35_90 c35_93
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_80 : anyK (node 0 7) ((kid35.drop 80).take 10) = false := by decide +kernel
theorem c35_80 : anyK (node 0 7) (kid35.drop 80) = false := chainK _ _ 80 10 90 rfl t35_80 c35_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_70 : anyK (node 0 7) ((kid35.drop 70).take 10) = false := by decide +kernel
theorem c35_70 : anyK (node 0 7) (kid35.drop 70) = false := chainK _ _ 70 10 80 rfl t35_70 c35_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_60 : anyK (node 0 7) ((kid35.drop 60).take 10) = false := by decide +kernel
theorem c35_60 : anyK (node 0 7) (kid35.drop 60) = false := chainK _ _ 60 10 70 rfl t35_60 c35_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_50 : anyK (node 0 7) ((kid35.drop 50).take 10) = false := by decide +kernel
theorem c35_50 : anyK (node 0 7) (kid35.drop 50) = false := chainK _ _ 50 10 60 rfl t35_50 c35_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_40 : anyK (node 0 7) ((kid35.drop 40).take 10) = false := by decide +kernel
theorem c35_40 : anyK (node 0 7) (kid35.drop 40) = false := chainK _ _ 40 10 50 rfl t35_40 c35_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_30 : anyK (node 0 7) ((kid35.drop 30).take 10) = false := by decide +kernel
theorem c35_30 : anyK (node 0 7) (kid35.drop 30) = false := chainK _ _ 30 10 40 rfl t35_30 c35_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_20 : anyK (node 0 7) ((kid35.drop 20).take 10) = false := by decide +kernel
theorem c35_20 : anyK (node 0 7) (kid35.drop 20) = false := chainK _ _ 20 10 30 rfl t35_20 c35_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_10 : anyK (node 0 7) ((kid35.drop 10).take 10) = false := by decide +kernel
theorem c35_10 : anyK (node 0 7) (kid35.drop 10) = false := chainK _ _ 10 10 20 rfl t35_10 c35_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_0 : anyK (node 0 7) ((kid35.drop 0).take 10) = false := by decide +kernel
theorem c35_0 : anyK (node 0 7) (kid35.drop 0) = false := chainK _ _ 0 10 10 rfl t35_0 c35_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc35 : anyK (node 0 8) ((kR.drop 35).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid35 c35_0))
theorem rq35 : anyK (node 0 8) (kR.drop 35) = false := chainK _ _ 35 1 36 rfl sc35 rq36
def kid34 := kids (hdK (kR.drop 34)).1 (hdK (kR.drop 34)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c34_51 : anyK (node 0 7) (kid34.drop 51) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_50 : anyK (node 0 7) ((kid34.drop 50).take 1) = false := by decide +kernel
theorem c34_50 : anyK (node 0 7) (kid34.drop 50) = false := chainK _ _ 50 1 51 rfl t34_50 c34_51
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_40 : anyK (node 0 7) ((kid34.drop 40).take 10) = false := by decide +kernel
theorem c34_40 : anyK (node 0 7) (kid34.drop 40) = false := chainK _ _ 40 10 50 rfl t34_40 c34_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_30 : anyK (node 0 7) ((kid34.drop 30).take 10) = false := by decide +kernel
theorem c34_30 : anyK (node 0 7) (kid34.drop 30) = false := chainK _ _ 30 10 40 rfl t34_30 c34_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_20 : anyK (node 0 7) ((kid34.drop 20).take 10) = false := by decide +kernel
theorem c34_20 : anyK (node 0 7) (kid34.drop 20) = false := chainK _ _ 20 10 30 rfl t34_20 c34_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_10 : anyK (node 0 7) ((kid34.drop 10).take 10) = false := by decide +kernel
theorem c34_10 : anyK (node 0 7) (kid34.drop 10) = false := chainK _ _ 10 10 20 rfl t34_10 c34_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_0 : anyK (node 0 7) ((kid34.drop 0).take 10) = false := by decide +kernel
theorem c34_0 : anyK (node 0 7) (kid34.drop 0) = false := chainK _ _ 0 10 10 rfl t34_0 c34_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc34 : anyK (node 0 8) ((kR.drop 34).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid34 c34_0))
theorem rq34 : anyK (node 0 8) (kR.drop 34) = false := chainK _ _ 34 1 35 rfl sc34 rq35
def kid33 := kids (hdK (kR.drop 33)).1 (hdK (kR.drop 33)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c33_49 : anyK (node 0 7) (kid33.drop 49) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_40 : anyK (node 0 7) ((kid33.drop 40).take 9) = false := by decide +kernel
theorem c33_40 : anyK (node 0 7) (kid33.drop 40) = false := chainK _ _ 40 9 49 rfl t33_40 c33_49
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_30 : anyK (node 0 7) ((kid33.drop 30).take 10) = false := by decide +kernel
theorem c33_30 : anyK (node 0 7) (kid33.drop 30) = false := chainK _ _ 30 10 40 rfl t33_30 c33_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_20 : anyK (node 0 7) ((kid33.drop 20).take 10) = false := by decide +kernel
theorem c33_20 : anyK (node 0 7) (kid33.drop 20) = false := chainK _ _ 20 10 30 rfl t33_20 c33_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_10 : anyK (node 0 7) ((kid33.drop 10).take 10) = false := by decide +kernel
theorem c33_10 : anyK (node 0 7) (kid33.drop 10) = false := chainK _ _ 10 10 20 rfl t33_10 c33_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_0 : anyK (node 0 7) ((kid33.drop 0).take 10) = false := by decide +kernel
theorem c33_0 : anyK (node 0 7) (kid33.drop 0) = false := chainK _ _ 0 10 10 rfl t33_0 c33_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc33 : anyK (node 0 8) ((kR.drop 33).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid33 c33_0))
theorem rq33 : anyK (node 0 8) (kR.drop 33) = false := chainK _ _ 33 1 34 rfl sc33 rq34
def kid32 := kids (hdK (kR.drop 32)).1 (hdK (kR.drop 32)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c32_107 : anyK (node 0 7) (kid32.drop 107) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_100 : anyK (node 0 7) ((kid32.drop 100).take 7) = false := by decide +kernel
theorem c32_100 : anyK (node 0 7) (kid32.drop 100) = false := chainK _ _ 100 7 107 rfl t32_100 c32_107
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_90 : anyK (node 0 7) ((kid32.drop 90).take 10) = false := by decide +kernel
theorem c32_90 : anyK (node 0 7) (kid32.drop 90) = false := chainK _ _ 90 10 100 rfl t32_90 c32_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_80 : anyK (node 0 7) ((kid32.drop 80).take 10) = false := by decide +kernel
theorem c32_80 : anyK (node 0 7) (kid32.drop 80) = false := chainK _ _ 80 10 90 rfl t32_80 c32_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_70 : anyK (node 0 7) ((kid32.drop 70).take 10) = false := by decide +kernel
theorem c32_70 : anyK (node 0 7) (kid32.drop 70) = false := chainK _ _ 70 10 80 rfl t32_70 c32_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_60 : anyK (node 0 7) ((kid32.drop 60).take 10) = false := by decide +kernel
theorem c32_60 : anyK (node 0 7) (kid32.drop 60) = false := chainK _ _ 60 10 70 rfl t32_60 c32_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_50 : anyK (node 0 7) ((kid32.drop 50).take 10) = false := by decide +kernel
theorem c32_50 : anyK (node 0 7) (kid32.drop 50) = false := chainK _ _ 50 10 60 rfl t32_50 c32_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_40 : anyK (node 0 7) ((kid32.drop 40).take 10) = false := by decide +kernel
theorem c32_40 : anyK (node 0 7) (kid32.drop 40) = false := chainK _ _ 40 10 50 rfl t32_40 c32_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_30 : anyK (node 0 7) ((kid32.drop 30).take 10) = false := by decide +kernel
theorem c32_30 : anyK (node 0 7) (kid32.drop 30) = false := chainK _ _ 30 10 40 rfl t32_30 c32_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_20 : anyK (node 0 7) ((kid32.drop 20).take 10) = false := by decide +kernel
theorem c32_20 : anyK (node 0 7) (kid32.drop 20) = false := chainK _ _ 20 10 30 rfl t32_20 c32_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_10 : anyK (node 0 7) ((kid32.drop 10).take 10) = false := by decide +kernel
theorem c32_10 : anyK (node 0 7) (kid32.drop 10) = false := chainK _ _ 10 10 20 rfl t32_10 c32_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_0 : anyK (node 0 7) ((kid32.drop 0).take 10) = false := by decide +kernel
theorem c32_0 : anyK (node 0 7) (kid32.drop 0) = false := chainK _ _ 0 10 10 rfl t32_0 c32_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc32 : anyK (node 0 8) ((kR.drop 32).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid32 c32_0))
theorem rq32 : anyK (node 0 8) (kR.drop 32) = false := chainK _ _ 32 1 33 rfl sc32 rq33
def kid31 := kids (hdK (kR.drop 31)).1 (hdK (kR.drop 31)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c31_63 : anyK (node 0 7) (kid31.drop 63) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_60 : anyK (node 0 7) ((kid31.drop 60).take 3) = false := by decide +kernel
theorem c31_60 : anyK (node 0 7) (kid31.drop 60) = false := chainK _ _ 60 3 63 rfl t31_60 c31_63
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_50 : anyK (node 0 7) ((kid31.drop 50).take 10) = false := by decide +kernel
theorem c31_50 : anyK (node 0 7) (kid31.drop 50) = false := chainK _ _ 50 10 60 rfl t31_50 c31_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_40 : anyK (node 0 7) ((kid31.drop 40).take 10) = false := by decide +kernel
theorem c31_40 : anyK (node 0 7) (kid31.drop 40) = false := chainK _ _ 40 10 50 rfl t31_40 c31_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_30 : anyK (node 0 7) ((kid31.drop 30).take 10) = false := by decide +kernel
theorem c31_30 : anyK (node 0 7) (kid31.drop 30) = false := chainK _ _ 30 10 40 rfl t31_30 c31_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_20 : anyK (node 0 7) ((kid31.drop 20).take 10) = false := by decide +kernel
theorem c31_20 : anyK (node 0 7) (kid31.drop 20) = false := chainK _ _ 20 10 30 rfl t31_20 c31_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_10 : anyK (node 0 7) ((kid31.drop 10).take 10) = false := by decide +kernel
theorem c31_10 : anyK (node 0 7) (kid31.drop 10) = false := chainK _ _ 10 10 20 rfl t31_10 c31_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_0 : anyK (node 0 7) ((kid31.drop 0).take 10) = false := by decide +kernel
theorem c31_0 : anyK (node 0 7) (kid31.drop 0) = false := chainK _ _ 0 10 10 rfl t31_0 c31_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc31 : anyK (node 0 8) ((kR.drop 31).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid31 c31_0))
theorem rq31 : anyK (node 0 8) (kR.drop 31) = false := chainK _ _ 31 1 32 rfl sc31 rq32
def kid30 := kids (hdK (kR.drop 30)).1 (hdK (kR.drop 30)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c30_60 : anyK (node 0 7) (kid30.drop 60) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_50 : anyK (node 0 7) ((kid30.drop 50).take 10) = false := by decide +kernel
theorem c30_50 : anyK (node 0 7) (kid30.drop 50) = false := chainK _ _ 50 10 60 rfl t30_50 c30_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_40 : anyK (node 0 7) ((kid30.drop 40).take 10) = false := by decide +kernel
theorem c30_40 : anyK (node 0 7) (kid30.drop 40) = false := chainK _ _ 40 10 50 rfl t30_40 c30_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_30 : anyK (node 0 7) ((kid30.drop 30).take 10) = false := by decide +kernel
theorem c30_30 : anyK (node 0 7) (kid30.drop 30) = false := chainK _ _ 30 10 40 rfl t30_30 c30_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_20 : anyK (node 0 7) ((kid30.drop 20).take 10) = false := by decide +kernel
theorem c30_20 : anyK (node 0 7) (kid30.drop 20) = false := chainK _ _ 20 10 30 rfl t30_20 c30_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_10 : anyK (node 0 7) ((kid30.drop 10).take 10) = false := by decide +kernel
theorem c30_10 : anyK (node 0 7) (kid30.drop 10) = false := chainK _ _ 10 10 20 rfl t30_10 c30_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_0 : anyK (node 0 7) ((kid30.drop 0).take 10) = false := by decide +kernel
theorem c30_0 : anyK (node 0 7) (kid30.drop 0) = false := chainK _ _ 0 10 10 rfl t30_0 c30_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc30 : anyK (node 0 8) ((kR.drop 30).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid30 c30_0))
theorem rq30 : anyK (node 0 8) (kR.drop 30) = false := chainK _ _ 30 1 31 rfl sc30 rq31
def kid29 := kids (hdK (kR.drop 29)).1 (hdK (kR.drop 29)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c29_50 : anyK (node 0 7) (kid29.drop 50) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_40 : anyK (node 0 7) ((kid29.drop 40).take 10) = false := by decide +kernel
theorem c29_40 : anyK (node 0 7) (kid29.drop 40) = false := chainK _ _ 40 10 50 rfl t29_40 c29_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_30 : anyK (node 0 7) ((kid29.drop 30).take 10) = false := by decide +kernel
theorem c29_30 : anyK (node 0 7) (kid29.drop 30) = false := chainK _ _ 30 10 40 rfl t29_30 c29_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_20 : anyK (node 0 7) ((kid29.drop 20).take 10) = false := by decide +kernel
theorem c29_20 : anyK (node 0 7) (kid29.drop 20) = false := chainK _ _ 20 10 30 rfl t29_20 c29_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_10 : anyK (node 0 7) ((kid29.drop 10).take 10) = false := by decide +kernel
theorem c29_10 : anyK (node 0 7) (kid29.drop 10) = false := chainK _ _ 10 10 20 rfl t29_10 c29_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_0 : anyK (node 0 7) ((kid29.drop 0).take 10) = false := by decide +kernel
theorem c29_0 : anyK (node 0 7) (kid29.drop 0) = false := chainK _ _ 0 10 10 rfl t29_0 c29_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc29 : anyK (node 0 8) ((kR.drop 29).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid29 c29_0))
theorem rq29 : anyK (node 0 8) (kR.drop 29) = false := chainK _ _ 29 1 30 rfl sc29 rq30
def kid28 := kids (hdK (kR.drop 28)).1 (hdK (kR.drop 28)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c28_108 : anyK (node 0 7) (kid28.drop 108) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_100 : anyK (node 0 7) ((kid28.drop 100).take 8) = false := by decide +kernel
theorem c28_100 : anyK (node 0 7) (kid28.drop 100) = false := chainK _ _ 100 8 108 rfl t28_100 c28_108
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_90 : anyK (node 0 7) ((kid28.drop 90).take 10) = false := by decide +kernel
theorem c28_90 : anyK (node 0 7) (kid28.drop 90) = false := chainK _ _ 90 10 100 rfl t28_90 c28_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_80 : anyK (node 0 7) ((kid28.drop 80).take 10) = false := by decide +kernel
theorem c28_80 : anyK (node 0 7) (kid28.drop 80) = false := chainK _ _ 80 10 90 rfl t28_80 c28_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_70 : anyK (node 0 7) ((kid28.drop 70).take 10) = false := by decide +kernel
theorem c28_70 : anyK (node 0 7) (kid28.drop 70) = false := chainK _ _ 70 10 80 rfl t28_70 c28_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_60 : anyK (node 0 7) ((kid28.drop 60).take 10) = false := by decide +kernel
theorem c28_60 : anyK (node 0 7) (kid28.drop 60) = false := chainK _ _ 60 10 70 rfl t28_60 c28_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_50 : anyK (node 0 7) ((kid28.drop 50).take 10) = false := by decide +kernel
theorem c28_50 : anyK (node 0 7) (kid28.drop 50) = false := chainK _ _ 50 10 60 rfl t28_50 c28_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_40 : anyK (node 0 7) ((kid28.drop 40).take 10) = false := by decide +kernel
theorem c28_40 : anyK (node 0 7) (kid28.drop 40) = false := chainK _ _ 40 10 50 rfl t28_40 c28_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_30 : anyK (node 0 7) ((kid28.drop 30).take 10) = false := by decide +kernel
theorem c28_30 : anyK (node 0 7) (kid28.drop 30) = false := chainK _ _ 30 10 40 rfl t28_30 c28_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_20 : anyK (node 0 7) ((kid28.drop 20).take 10) = false := by decide +kernel
theorem c28_20 : anyK (node 0 7) (kid28.drop 20) = false := chainK _ _ 20 10 30 rfl t28_20 c28_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_10 : anyK (node 0 7) ((kid28.drop 10).take 10) = false := by decide +kernel
theorem c28_10 : anyK (node 0 7) (kid28.drop 10) = false := chainK _ _ 10 10 20 rfl t28_10 c28_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_0 : anyK (node 0 7) ((kid28.drop 0).take 10) = false := by decide +kernel
theorem c28_0 : anyK (node 0 7) (kid28.drop 0) = false := chainK _ _ 0 10 10 rfl t28_0 c28_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc28 : anyK (node 0 8) ((kR.drop 28).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid28 c28_0))
theorem rq28 : anyK (node 0 8) (kR.drop 28) = false := chainK _ _ 28 1 29 rfl sc28 rq29
def kid27 := kids (hdK (kR.drop 27)).1 (hdK (kR.drop 27)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c27_69 : anyK (node 0 7) (kid27.drop 69) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_60 : anyK (node 0 7) ((kid27.drop 60).take 9) = false := by decide +kernel
theorem c27_60 : anyK (node 0 7) (kid27.drop 60) = false := chainK _ _ 60 9 69 rfl t27_60 c27_69
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_50 : anyK (node 0 7) ((kid27.drop 50).take 10) = false := by decide +kernel
theorem c27_50 : anyK (node 0 7) (kid27.drop 50) = false := chainK _ _ 50 10 60 rfl t27_50 c27_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_40 : anyK (node 0 7) ((kid27.drop 40).take 10) = false := by decide +kernel
theorem c27_40 : anyK (node 0 7) (kid27.drop 40) = false := chainK _ _ 40 10 50 rfl t27_40 c27_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_30 : anyK (node 0 7) ((kid27.drop 30).take 10) = false := by decide +kernel
theorem c27_30 : anyK (node 0 7) (kid27.drop 30) = false := chainK _ _ 30 10 40 rfl t27_30 c27_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_20 : anyK (node 0 7) ((kid27.drop 20).take 10) = false := by decide +kernel
theorem c27_20 : anyK (node 0 7) (kid27.drop 20) = false := chainK _ _ 20 10 30 rfl t27_20 c27_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_10 : anyK (node 0 7) ((kid27.drop 10).take 10) = false := by decide +kernel
theorem c27_10 : anyK (node 0 7) (kid27.drop 10) = false := chainK _ _ 10 10 20 rfl t27_10 c27_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_0 : anyK (node 0 7) ((kid27.drop 0).take 10) = false := by decide +kernel
theorem c27_0 : anyK (node 0 7) (kid27.drop 0) = false := chainK _ _ 0 10 10 rfl t27_0 c27_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc27 : anyK (node 0 8) ((kR.drop 27).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid27 c27_0))
theorem rq27 : anyK (node 0 8) (kR.drop 27) = false := chainK _ _ 27 1 28 rfl sc27 rq28
def kid26 := kids (hdK (kR.drop 26)).1 (hdK (kR.drop 26)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c26_49 : anyK (node 0 7) (kid26.drop 49) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_40 : anyK (node 0 7) ((kid26.drop 40).take 9) = false := by decide +kernel
theorem c26_40 : anyK (node 0 7) (kid26.drop 40) = false := chainK _ _ 40 9 49 rfl t26_40 c26_49
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_30 : anyK (node 0 7) ((kid26.drop 30).take 10) = false := by decide +kernel
theorem c26_30 : anyK (node 0 7) (kid26.drop 30) = false := chainK _ _ 30 10 40 rfl t26_30 c26_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_20 : anyK (node 0 7) ((kid26.drop 20).take 10) = false := by decide +kernel
theorem c26_20 : anyK (node 0 7) (kid26.drop 20) = false := chainK _ _ 20 10 30 rfl t26_20 c26_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_10 : anyK (node 0 7) ((kid26.drop 10).take 10) = false := by decide +kernel
theorem c26_10 : anyK (node 0 7) (kid26.drop 10) = false := chainK _ _ 10 10 20 rfl t26_10 c26_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_0 : anyK (node 0 7) ((kid26.drop 0).take 10) = false := by decide +kernel
theorem c26_0 : anyK (node 0 7) (kid26.drop 0) = false := chainK _ _ 0 10 10 rfl t26_0 c26_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc26 : anyK (node 0 8) ((kR.drop 26).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid26 c26_0))
theorem rq26 : anyK (node 0 8) (kR.drop 26) = false := chainK _ _ 26 1 27 rfl sc26 rq27
def kid25 := kids (hdK (kR.drop 25)).1 (hdK (kR.drop 25)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c25_51 : anyK (node 0 7) (kid25.drop 51) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_50 : anyK (node 0 7) ((kid25.drop 50).take 1) = false := by decide +kernel
theorem c25_50 : anyK (node 0 7) (kid25.drop 50) = false := chainK _ _ 50 1 51 rfl t25_50 c25_51
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_40 : anyK (node 0 7) ((kid25.drop 40).take 10) = false := by decide +kernel
theorem c25_40 : anyK (node 0 7) (kid25.drop 40) = false := chainK _ _ 40 10 50 rfl t25_40 c25_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_30 : anyK (node 0 7) ((kid25.drop 30).take 10) = false := by decide +kernel
theorem c25_30 : anyK (node 0 7) (kid25.drop 30) = false := chainK _ _ 30 10 40 rfl t25_30 c25_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_20 : anyK (node 0 7) ((kid25.drop 20).take 10) = false := by decide +kernel
theorem c25_20 : anyK (node 0 7) (kid25.drop 20) = false := chainK _ _ 20 10 30 rfl t25_20 c25_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_10 : anyK (node 0 7) ((kid25.drop 10).take 10) = false := by decide +kernel
theorem c25_10 : anyK (node 0 7) (kid25.drop 10) = false := chainK _ _ 10 10 20 rfl t25_10 c25_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_0 : anyK (node 0 7) ((kid25.drop 0).take 10) = false := by decide +kernel
theorem c25_0 : anyK (node 0 7) (kid25.drop 0) = false := chainK _ _ 0 10 10 rfl t25_0 c25_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc25 : anyK (node 0 8) ((kR.drop 25).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid25 c25_0))
theorem rq25 : anyK (node 0 8) (kR.drop 25) = false := chainK _ _ 25 1 26 rfl sc25 rq26
def kid24 := kids (hdK (kR.drop 24)).1 (hdK (kR.drop 24)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24_129 : anyK (node 0 7) (kid24.drop 129) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_120 : anyK (node 0 7) ((kid24.drop 120).take 9) = false := by decide +kernel
theorem c24_120 : anyK (node 0 7) (kid24.drop 120) = false := chainK _ _ 120 9 129 rfl t24_120 c24_129
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_110 : anyK (node 0 7) ((kid24.drop 110).take 10) = false := by decide +kernel
theorem c24_110 : anyK (node 0 7) (kid24.drop 110) = false := chainK _ _ 110 10 120 rfl t24_110 c24_120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_100 : anyK (node 0 7) ((kid24.drop 100).take 10) = false := by decide +kernel
theorem c24_100 : anyK (node 0 7) (kid24.drop 100) = false := chainK _ _ 100 10 110 rfl t24_100 c24_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_90 : anyK (node 0 7) ((kid24.drop 90).take 10) = false := by decide +kernel
theorem c24_90 : anyK (node 0 7) (kid24.drop 90) = false := chainK _ _ 90 10 100 rfl t24_90 c24_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_80 : anyK (node 0 7) ((kid24.drop 80).take 10) = false := by decide +kernel
theorem c24_80 : anyK (node 0 7) (kid24.drop 80) = false := chainK _ _ 80 10 90 rfl t24_80 c24_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_70 : anyK (node 0 7) ((kid24.drop 70).take 10) = false := by decide +kernel
theorem c24_70 : anyK (node 0 7) (kid24.drop 70) = false := chainK _ _ 70 10 80 rfl t24_70 c24_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_60 : anyK (node 0 7) ((kid24.drop 60).take 10) = false := by decide +kernel
theorem c24_60 : anyK (node 0 7) (kid24.drop 60) = false := chainK _ _ 60 10 70 rfl t24_60 c24_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_50 : anyK (node 0 7) ((kid24.drop 50).take 10) = false := by decide +kernel
theorem c24_50 : anyK (node 0 7) (kid24.drop 50) = false := chainK _ _ 50 10 60 rfl t24_50 c24_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_40 : anyK (node 0 7) ((kid24.drop 40).take 10) = false := by decide +kernel
theorem c24_40 : anyK (node 0 7) (kid24.drop 40) = false := chainK _ _ 40 10 50 rfl t24_40 c24_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_30 : anyK (node 0 7) ((kid24.drop 30).take 10) = false := by decide +kernel
theorem c24_30 : anyK (node 0 7) (kid24.drop 30) = false := chainK _ _ 30 10 40 rfl t24_30 c24_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_20 : anyK (node 0 7) ((kid24.drop 20).take 10) = false := by decide +kernel
theorem c24_20 : anyK (node 0 7) (kid24.drop 20) = false := chainK _ _ 20 10 30 rfl t24_20 c24_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_10 : anyK (node 0 7) ((kid24.drop 10).take 10) = false := by decide +kernel
theorem c24_10 : anyK (node 0 7) (kid24.drop 10) = false := chainK _ _ 10 10 20 rfl t24_10 c24_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_0 : anyK (node 0 7) ((kid24.drop 0).take 10) = false := by decide +kernel
theorem c24_0 : anyK (node 0 7) (kid24.drop 0) = false := chainK _ _ 0 10 10 rfl t24_0 c24_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc24 : anyK (node 0 8) ((kR.drop 24).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid24 c24_0))
theorem rq24 : anyK (node 0 8) (kR.drop 24) = false := chainK _ _ 24 1 25 rfl sc24 rq25
def kid23 := kids (hdK (kR.drop 23)).1 (hdK (kR.drop 23)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c23_83 : anyK (node 0 7) (kid23.drop 83) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_80 : anyK (node 0 7) ((kid23.drop 80).take 3) = false := by decide +kernel
theorem c23_80 : anyK (node 0 7) (kid23.drop 80) = false := chainK _ _ 80 3 83 rfl t23_80 c23_83
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_70 : anyK (node 0 7) ((kid23.drop 70).take 10) = false := by decide +kernel
theorem c23_70 : anyK (node 0 7) (kid23.drop 70) = false := chainK _ _ 70 10 80 rfl t23_70 c23_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_60 : anyK (node 0 7) ((kid23.drop 60).take 10) = false := by decide +kernel
theorem c23_60 : anyK (node 0 7) (kid23.drop 60) = false := chainK _ _ 60 10 70 rfl t23_60 c23_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_50 : anyK (node 0 7) ((kid23.drop 50).take 10) = false := by decide +kernel
theorem c23_50 : anyK (node 0 7) (kid23.drop 50) = false := chainK _ _ 50 10 60 rfl t23_50 c23_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_40 : anyK (node 0 7) ((kid23.drop 40).take 10) = false := by decide +kernel
theorem c23_40 : anyK (node 0 7) (kid23.drop 40) = false := chainK _ _ 40 10 50 rfl t23_40 c23_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_30 : anyK (node 0 7) ((kid23.drop 30).take 10) = false := by decide +kernel
theorem c23_30 : anyK (node 0 7) (kid23.drop 30) = false := chainK _ _ 30 10 40 rfl t23_30 c23_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_20 : anyK (node 0 7) ((kid23.drop 20).take 10) = false := by decide +kernel
theorem c23_20 : anyK (node 0 7) (kid23.drop 20) = false := chainK _ _ 20 10 30 rfl t23_20 c23_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_10 : anyK (node 0 7) ((kid23.drop 10).take 10) = false := by decide +kernel
theorem c23_10 : anyK (node 0 7) (kid23.drop 10) = false := chainK _ _ 10 10 20 rfl t23_10 c23_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_0 : anyK (node 0 7) ((kid23.drop 0).take 10) = false := by decide +kernel
theorem c23_0 : anyK (node 0 7) (kid23.drop 0) = false := chainK _ _ 0 10 10 rfl t23_0 c23_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc23 : anyK (node 0 8) ((kR.drop 23).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid23 c23_0))
theorem rq23 : anyK (node 0 8) (kR.drop 23) = false := chainK _ _ 23 1 24 rfl sc23 rq24
def kid22 := kids (hdK (kR.drop 22)).1 (hdK (kR.drop 22)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c22_44 : anyK (node 0 7) (kid22.drop 44) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_40 : anyK (node 0 7) ((kid22.drop 40).take 4) = false := by decide +kernel
theorem c22_40 : anyK (node 0 7) (kid22.drop 40) = false := chainK _ _ 40 4 44 rfl t22_40 c22_44
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_30 : anyK (node 0 7) ((kid22.drop 30).take 10) = false := by decide +kernel
theorem c22_30 : anyK (node 0 7) (kid22.drop 30) = false := chainK _ _ 30 10 40 rfl t22_30 c22_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_20 : anyK (node 0 7) ((kid22.drop 20).take 10) = false := by decide +kernel
theorem c22_20 : anyK (node 0 7) (kid22.drop 20) = false := chainK _ _ 20 10 30 rfl t22_20 c22_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_10 : anyK (node 0 7) ((kid22.drop 10).take 10) = false := by decide +kernel
theorem c22_10 : anyK (node 0 7) (kid22.drop 10) = false := chainK _ _ 10 10 20 rfl t22_10 c22_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_0 : anyK (node 0 7) ((kid22.drop 0).take 10) = false := by decide +kernel
theorem c22_0 : anyK (node 0 7) (kid22.drop 0) = false := chainK _ _ 0 10 10 rfl t22_0 c22_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc22 : anyK (node 0 8) ((kR.drop 22).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid22 c22_0))
theorem rq22 : anyK (node 0 8) (kR.drop 22) = false := chainK _ _ 22 1 23 rfl sc22 rq23
def kid21 := kids (hdK (kR.drop 21)).1 (hdK (kR.drop 21)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c21_108 : anyK (node 0 7) (kid21.drop 108) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_100 : anyK (node 0 7) ((kid21.drop 100).take 8) = false := by decide +kernel
theorem c21_100 : anyK (node 0 7) (kid21.drop 100) = false := chainK _ _ 100 8 108 rfl t21_100 c21_108
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_90 : anyK (node 0 7) ((kid21.drop 90).take 10) = false := by decide +kernel
theorem c21_90 : anyK (node 0 7) (kid21.drop 90) = false := chainK _ _ 90 10 100 rfl t21_90 c21_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_80 : anyK (node 0 7) ((kid21.drop 80).take 10) = false := by decide +kernel
theorem c21_80 : anyK (node 0 7) (kid21.drop 80) = false := chainK _ _ 80 10 90 rfl t21_80 c21_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_70 : anyK (node 0 7) ((kid21.drop 70).take 10) = false := by decide +kernel
theorem c21_70 : anyK (node 0 7) (kid21.drop 70) = false := chainK _ _ 70 10 80 rfl t21_70 c21_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_60 : anyK (node 0 7) ((kid21.drop 60).take 10) = false := by decide +kernel
theorem c21_60 : anyK (node 0 7) (kid21.drop 60) = false := chainK _ _ 60 10 70 rfl t21_60 c21_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_50 : anyK (node 0 7) ((kid21.drop 50).take 10) = false := by decide +kernel
theorem c21_50 : anyK (node 0 7) (kid21.drop 50) = false := chainK _ _ 50 10 60 rfl t21_50 c21_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_40 : anyK (node 0 7) ((kid21.drop 40).take 10) = false := by decide +kernel
theorem c21_40 : anyK (node 0 7) (kid21.drop 40) = false := chainK _ _ 40 10 50 rfl t21_40 c21_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_30 : anyK (node 0 7) ((kid21.drop 30).take 10) = false := by decide +kernel
theorem c21_30 : anyK (node 0 7) (kid21.drop 30) = false := chainK _ _ 30 10 40 rfl t21_30 c21_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_20 : anyK (node 0 7) ((kid21.drop 20).take 10) = false := by decide +kernel
theorem c21_20 : anyK (node 0 7) (kid21.drop 20) = false := chainK _ _ 20 10 30 rfl t21_20 c21_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_10 : anyK (node 0 7) ((kid21.drop 10).take 10) = false := by decide +kernel
theorem c21_10 : anyK (node 0 7) (kid21.drop 10) = false := chainK _ _ 10 10 20 rfl t21_10 c21_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_0 : anyK (node 0 7) ((kid21.drop 0).take 10) = false := by decide +kernel
theorem c21_0 : anyK (node 0 7) (kid21.drop 0) = false := chainK _ _ 0 10 10 rfl t21_0 c21_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc21 : anyK (node 0 8) ((kR.drop 21).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid21 c21_0))
theorem rq21 : anyK (node 0 8) (kR.drop 21) = false := chainK _ _ 21 1 22 rfl sc21 rq22
def kid20 := kids (hdK (kR.drop 20)).1 (hdK (kR.drop 20)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c20_79 : anyK (node 0 7) (kid20.drop 79) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_70 : anyK (node 0 7) ((kid20.drop 70).take 9) = false := by decide +kernel
theorem c20_70 : anyK (node 0 7) (kid20.drop 70) = false := chainK _ _ 70 9 79 rfl t20_70 c20_79
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_60 : anyK (node 0 7) ((kid20.drop 60).take 10) = false := by decide +kernel
theorem c20_60 : anyK (node 0 7) (kid20.drop 60) = false := chainK _ _ 60 10 70 rfl t20_60 c20_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_50 : anyK (node 0 7) ((kid20.drop 50).take 10) = false := by decide +kernel
theorem c20_50 : anyK (node 0 7) (kid20.drop 50) = false := chainK _ _ 50 10 60 rfl t20_50 c20_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_40 : anyK (node 0 7) ((kid20.drop 40).take 10) = false := by decide +kernel
theorem c20_40 : anyK (node 0 7) (kid20.drop 40) = false := chainK _ _ 40 10 50 rfl t20_40 c20_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_30 : anyK (node 0 7) ((kid20.drop 30).take 10) = false := by decide +kernel
theorem c20_30 : anyK (node 0 7) (kid20.drop 30) = false := chainK _ _ 30 10 40 rfl t20_30 c20_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_20 : anyK (node 0 7) ((kid20.drop 20).take 10) = false := by decide +kernel
theorem c20_20 : anyK (node 0 7) (kid20.drop 20) = false := chainK _ _ 20 10 30 rfl t20_20 c20_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_10 : anyK (node 0 7) ((kid20.drop 10).take 10) = false := by decide +kernel
theorem c20_10 : anyK (node 0 7) (kid20.drop 10) = false := chainK _ _ 10 10 20 rfl t20_10 c20_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_0 : anyK (node 0 7) ((kid20.drop 0).take 10) = false := by decide +kernel
theorem c20_0 : anyK (node 0 7) (kid20.drop 0) = false := chainK _ _ 0 10 10 rfl t20_0 c20_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc20 : anyK (node 0 8) ((kR.drop 20).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid20 c20_0))
theorem rq20 : anyK (node 0 8) (kR.drop 20) = false := chainK _ _ 20 1 21 rfl sc20 rq21
def kid19 := kids (hdK (kR.drop 19)).1 (hdK (kR.drop 19)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c19_44 : anyK (node 0 7) (kid19.drop 44) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_40 : anyK (node 0 7) ((kid19.drop 40).take 4) = false := by decide +kernel
theorem c19_40 : anyK (node 0 7) (kid19.drop 40) = false := chainK _ _ 40 4 44 rfl t19_40 c19_44
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_30 : anyK (node 0 7) ((kid19.drop 30).take 10) = false := by decide +kernel
theorem c19_30 : anyK (node 0 7) (kid19.drop 30) = false := chainK _ _ 30 10 40 rfl t19_30 c19_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_20 : anyK (node 0 7) ((kid19.drop 20).take 10) = false := by decide +kernel
theorem c19_20 : anyK (node 0 7) (kid19.drop 20) = false := chainK _ _ 20 10 30 rfl t19_20 c19_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_10 : anyK (node 0 7) ((kid19.drop 10).take 10) = false := by decide +kernel
theorem c19_10 : anyK (node 0 7) (kid19.drop 10) = false := chainK _ _ 10 10 20 rfl t19_10 c19_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_0 : anyK (node 0 7) ((kid19.drop 0).take 10) = false := by decide +kernel
theorem c19_0 : anyK (node 0 7) (kid19.drop 0) = false := chainK _ _ 0 10 10 rfl t19_0 c19_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc19 : anyK (node 0 8) ((kR.drop 19).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid19 c19_0))
theorem rq19 : anyK (node 0 8) (kR.drop 19) = false := chainK _ _ 19 1 20 rfl sc19 rq20
def kid18 := kids (hdK (kR.drop 18)).1 (hdK (kR.drop 18)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c18_110 : anyK (node 0 7) (kid18.drop 110) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_100 : anyK (node 0 7) ((kid18.drop 100).take 10) = false := by decide +kernel
theorem c18_100 : anyK (node 0 7) (kid18.drop 100) = false := chainK _ _ 100 10 110 rfl t18_100 c18_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_90 : anyK (node 0 7) ((kid18.drop 90).take 10) = false := by decide +kernel
theorem c18_90 : anyK (node 0 7) (kid18.drop 90) = false := chainK _ _ 90 10 100 rfl t18_90 c18_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_80 : anyK (node 0 7) ((kid18.drop 80).take 10) = false := by decide +kernel
theorem c18_80 : anyK (node 0 7) (kid18.drop 80) = false := chainK _ _ 80 10 90 rfl t18_80 c18_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_70 : anyK (node 0 7) ((kid18.drop 70).take 10) = false := by decide +kernel
theorem c18_70 : anyK (node 0 7) (kid18.drop 70) = false := chainK _ _ 70 10 80 rfl t18_70 c18_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_60 : anyK (node 0 7) ((kid18.drop 60).take 10) = false := by decide +kernel
theorem c18_60 : anyK (node 0 7) (kid18.drop 60) = false := chainK _ _ 60 10 70 rfl t18_60 c18_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_50 : anyK (node 0 7) ((kid18.drop 50).take 10) = false := by decide +kernel
theorem c18_50 : anyK (node 0 7) (kid18.drop 50) = false := chainK _ _ 50 10 60 rfl t18_50 c18_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_40 : anyK (node 0 7) ((kid18.drop 40).take 10) = false := by decide +kernel
theorem c18_40 : anyK (node 0 7) (kid18.drop 40) = false := chainK _ _ 40 10 50 rfl t18_40 c18_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_30 : anyK (node 0 7) ((kid18.drop 30).take 10) = false := by decide +kernel
theorem c18_30 : anyK (node 0 7) (kid18.drop 30) = false := chainK _ _ 30 10 40 rfl t18_30 c18_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_20 : anyK (node 0 7) ((kid18.drop 20).take 10) = false := by decide +kernel
theorem c18_20 : anyK (node 0 7) (kid18.drop 20) = false := chainK _ _ 20 10 30 rfl t18_20 c18_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_10 : anyK (node 0 7) ((kid18.drop 10).take 10) = false := by decide +kernel
theorem c18_10 : anyK (node 0 7) (kid18.drop 10) = false := chainK _ _ 10 10 20 rfl t18_10 c18_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_0 : anyK (node 0 7) ((kid18.drop 0).take 10) = false := by decide +kernel
theorem c18_0 : anyK (node 0 7) (kid18.drop 0) = false := chainK _ _ 0 10 10 rfl t18_0 c18_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc18 : anyK (node 0 8) ((kR.drop 18).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid18 c18_0))
theorem rq18 : anyK (node 0 8) (kR.drop 18) = false := chainK _ _ 18 1 19 rfl sc18 rq19
def kid17 := kids (hdK (kR.drop 17)).1 (hdK (kR.drop 17)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17_94 : anyK (node 0 7) (kid17.drop 94) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_90 : anyK (node 0 7) ((kid17.drop 90).take 4) = false := by decide +kernel
theorem c17_90 : anyK (node 0 7) (kid17.drop 90) = false := chainK _ _ 90 4 94 rfl t17_90 c17_94
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_80 : anyK (node 0 7) ((kid17.drop 80).take 10) = false := by decide +kernel
theorem c17_80 : anyK (node 0 7) (kid17.drop 80) = false := chainK _ _ 80 10 90 rfl t17_80 c17_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_70 : anyK (node 0 7) ((kid17.drop 70).take 10) = false := by decide +kernel
theorem c17_70 : anyK (node 0 7) (kid17.drop 70) = false := chainK _ _ 70 10 80 rfl t17_70 c17_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_60 : anyK (node 0 7) ((kid17.drop 60).take 10) = false := by decide +kernel
theorem c17_60 : anyK (node 0 7) (kid17.drop 60) = false := chainK _ _ 60 10 70 rfl t17_60 c17_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_50 : anyK (node 0 7) ((kid17.drop 50).take 10) = false := by decide +kernel
theorem c17_50 : anyK (node 0 7) (kid17.drop 50) = false := chainK _ _ 50 10 60 rfl t17_50 c17_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_40 : anyK (node 0 7) ((kid17.drop 40).take 10) = false := by decide +kernel
theorem c17_40 : anyK (node 0 7) (kid17.drop 40) = false := chainK _ _ 40 10 50 rfl t17_40 c17_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_30 : anyK (node 0 7) ((kid17.drop 30).take 10) = false := by decide +kernel
theorem c17_30 : anyK (node 0 7) (kid17.drop 30) = false := chainK _ _ 30 10 40 rfl t17_30 c17_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_20 : anyK (node 0 7) ((kid17.drop 20).take 10) = false := by decide +kernel
theorem c17_20 : anyK (node 0 7) (kid17.drop 20) = false := chainK _ _ 20 10 30 rfl t17_20 c17_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_10 : anyK (node 0 7) ((kid17.drop 10).take 10) = false := by decide +kernel
theorem c17_10 : anyK (node 0 7) (kid17.drop 10) = false := chainK _ _ 10 10 20 rfl t17_10 c17_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_0 : anyK (node 0 7) ((kid17.drop 0).take 10) = false := by decide +kernel
theorem c17_0 : anyK (node 0 7) (kid17.drop 0) = false := chainK _ _ 0 10 10 rfl t17_0 c17_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc17 : anyK (node 0 8) ((kR.drop 17).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid17 c17_0))
theorem rq17 : anyK (node 0 8) (kR.drop 17) = false := chainK _ _ 17 1 18 rfl sc17 rq18
def kid16 := kids (hdK (kR.drop 16)).1 (hdK (kR.drop 16)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_53 : anyK (node 0 7) (kid16.drop 53) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_50 : anyK (node 0 7) ((kid16.drop 50).take 3) = false := by decide +kernel
theorem c16_50 : anyK (node 0 7) (kid16.drop 50) = false := chainK _ _ 50 3 53 rfl t16_50 c16_53
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_40 : anyK (node 0 7) ((kid16.drop 40).take 10) = false := by decide +kernel
theorem c16_40 : anyK (node 0 7) (kid16.drop 40) = false := chainK _ _ 40 10 50 rfl t16_40 c16_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_30 : anyK (node 0 7) ((kid16.drop 30).take 10) = false := by decide +kernel
theorem c16_30 : anyK (node 0 7) (kid16.drop 30) = false := chainK _ _ 30 10 40 rfl t16_30 c16_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_20 : anyK (node 0 7) ((kid16.drop 20).take 10) = false := by decide +kernel
theorem c16_20 : anyK (node 0 7) (kid16.drop 20) = false := chainK _ _ 20 10 30 rfl t16_20 c16_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_10 : anyK (node 0 7) ((kid16.drop 10).take 10) = false := by decide +kernel
theorem c16_10 : anyK (node 0 7) (kid16.drop 10) = false := chainK _ _ 10 10 20 rfl t16_10 c16_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_0 : anyK (node 0 7) ((kid16.drop 0).take 10) = false := by decide +kernel
theorem c16_0 : anyK (node 0 7) (kid16.drop 0) = false := chainK _ _ 0 10 10 rfl t16_0 c16_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc16 : anyK (node 0 8) ((kR.drop 16).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid16 c16_0))
theorem rq16 : anyK (node 0 8) (kR.drop 16) = false := chainK _ _ 16 1 17 rfl sc16 rq17
def kid15 := kids (hdK (kR.drop 15)).1 (hdK (kR.drop 15)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c15_112 : anyK (node 0 7) (kid15.drop 112) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_110 : anyK (node 0 7) ((kid15.drop 110).take 2) = false := by decide +kernel
theorem c15_110 : anyK (node 0 7) (kid15.drop 110) = false := chainK _ _ 110 2 112 rfl t15_110 c15_112
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_100 : anyK (node 0 7) ((kid15.drop 100).take 10) = false := by decide +kernel
theorem c15_100 : anyK (node 0 7) (kid15.drop 100) = false := chainK _ _ 100 10 110 rfl t15_100 c15_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_90 : anyK (node 0 7) ((kid15.drop 90).take 10) = false := by decide +kernel
theorem c15_90 : anyK (node 0 7) (kid15.drop 90) = false := chainK _ _ 90 10 100 rfl t15_90 c15_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_80 : anyK (node 0 7) ((kid15.drop 80).take 10) = false := by decide +kernel
theorem c15_80 : anyK (node 0 7) (kid15.drop 80) = false := chainK _ _ 80 10 90 rfl t15_80 c15_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_70 : anyK (node 0 7) ((kid15.drop 70).take 10) = false := by decide +kernel
theorem c15_70 : anyK (node 0 7) (kid15.drop 70) = false := chainK _ _ 70 10 80 rfl t15_70 c15_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_60 : anyK (node 0 7) ((kid15.drop 60).take 10) = false := by decide +kernel
theorem c15_60 : anyK (node 0 7) (kid15.drop 60) = false := chainK _ _ 60 10 70 rfl t15_60 c15_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_50 : anyK (node 0 7) ((kid15.drop 50).take 10) = false := by decide +kernel
theorem c15_50 : anyK (node 0 7) (kid15.drop 50) = false := chainK _ _ 50 10 60 rfl t15_50 c15_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_40 : anyK (node 0 7) ((kid15.drop 40).take 10) = false := by decide +kernel
theorem c15_40 : anyK (node 0 7) (kid15.drop 40) = false := chainK _ _ 40 10 50 rfl t15_40 c15_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_30 : anyK (node 0 7) ((kid15.drop 30).take 10) = false := by decide +kernel
theorem c15_30 : anyK (node 0 7) (kid15.drop 30) = false := chainK _ _ 30 10 40 rfl t15_30 c15_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_20 : anyK (node 0 7) ((kid15.drop 20).take 10) = false := by decide +kernel
theorem c15_20 : anyK (node 0 7) (kid15.drop 20) = false := chainK _ _ 20 10 30 rfl t15_20 c15_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_10 : anyK (node 0 7) ((kid15.drop 10).take 10) = false := by decide +kernel
theorem c15_10 : anyK (node 0 7) (kid15.drop 10) = false := chainK _ _ 10 10 20 rfl t15_10 c15_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_0 : anyK (node 0 7) ((kid15.drop 0).take 10) = false := by decide +kernel
theorem c15_0 : anyK (node 0 7) (kid15.drop 0) = false := chainK _ _ 0 10 10 rfl t15_0 c15_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc15 : anyK (node 0 8) ((kR.drop 15).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid15 c15_0))
theorem rq15 : anyK (node 0 8) (kR.drop 15) = false := chainK _ _ 15 1 16 rfl sc15 rq16
def kid14 := kids (hdK (kR.drop 14)).1 (hdK (kR.drop 14)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c14_90 : anyK (node 0 7) (kid14.drop 90) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_80 : anyK (node 0 7) ((kid14.drop 80).take 10) = false := by decide +kernel
theorem c14_80 : anyK (node 0 7) (kid14.drop 80) = false := chainK _ _ 80 10 90 rfl t14_80 c14_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_70 : anyK (node 0 7) ((kid14.drop 70).take 10) = false := by decide +kernel
theorem c14_70 : anyK (node 0 7) (kid14.drop 70) = false := chainK _ _ 70 10 80 rfl t14_70 c14_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_60 : anyK (node 0 7) ((kid14.drop 60).take 10) = false := by decide +kernel
theorem c14_60 : anyK (node 0 7) (kid14.drop 60) = false := chainK _ _ 60 10 70 rfl t14_60 c14_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_50 : anyK (node 0 7) ((kid14.drop 50).take 10) = false := by decide +kernel
theorem c14_50 : anyK (node 0 7) (kid14.drop 50) = false := chainK _ _ 50 10 60 rfl t14_50 c14_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_40 : anyK (node 0 7) ((kid14.drop 40).take 10) = false := by decide +kernel
theorem c14_40 : anyK (node 0 7) (kid14.drop 40) = false := chainK _ _ 40 10 50 rfl t14_40 c14_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_30 : anyK (node 0 7) ((kid14.drop 30).take 10) = false := by decide +kernel
theorem c14_30 : anyK (node 0 7) (kid14.drop 30) = false := chainK _ _ 30 10 40 rfl t14_30 c14_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_20 : anyK (node 0 7) ((kid14.drop 20).take 10) = false := by decide +kernel
theorem c14_20 : anyK (node 0 7) (kid14.drop 20) = false := chainK _ _ 20 10 30 rfl t14_20 c14_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_10 : anyK (node 0 7) ((kid14.drop 10).take 10) = false := by decide +kernel
theorem c14_10 : anyK (node 0 7) (kid14.drop 10) = false := chainK _ _ 10 10 20 rfl t14_10 c14_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_0 : anyK (node 0 7) ((kid14.drop 0).take 10) = false := by decide +kernel
theorem c14_0 : anyK (node 0 7) (kid14.drop 0) = false := chainK _ _ 0 10 10 rfl t14_0 c14_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc14 : anyK (node 0 8) ((kR.drop 14).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid14 c14_0))
theorem rq14 : anyK (node 0 8) (kR.drop 14) = false := chainK _ _ 14 1 15 rfl sc14 rq15
def kid13 := kids (hdK (kR.drop 13)).1 (hdK (kR.drop 13)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c13_53 : anyK (node 0 7) (kid13.drop 53) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_50 : anyK (node 0 7) ((kid13.drop 50).take 3) = false := by decide +kernel
theorem c13_50 : anyK (node 0 7) (kid13.drop 50) = false := chainK _ _ 50 3 53 rfl t13_50 c13_53
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_40 : anyK (node 0 7) ((kid13.drop 40).take 10) = false := by decide +kernel
theorem c13_40 : anyK (node 0 7) (kid13.drop 40) = false := chainK _ _ 40 10 50 rfl t13_40 c13_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_30 : anyK (node 0 7) ((kid13.drop 30).take 10) = false := by decide +kernel
theorem c13_30 : anyK (node 0 7) (kid13.drop 30) = false := chainK _ _ 30 10 40 rfl t13_30 c13_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_20 : anyK (node 0 7) ((kid13.drop 20).take 10) = false := by decide +kernel
theorem c13_20 : anyK (node 0 7) (kid13.drop 20) = false := chainK _ _ 20 10 30 rfl t13_20 c13_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_10 : anyK (node 0 7) ((kid13.drop 10).take 10) = false := by decide +kernel
theorem c13_10 : anyK (node 0 7) (kid13.drop 10) = false := chainK _ _ 10 10 20 rfl t13_10 c13_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_0 : anyK (node 0 7) ((kid13.drop 0).take 10) = false := by decide +kernel
theorem c13_0 : anyK (node 0 7) (kid13.drop 0) = false := chainK _ _ 0 10 10 rfl t13_0 c13_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc13 : anyK (node 0 8) ((kR.drop 13).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid13 c13_0))
theorem rq13 : anyK (node 0 8) (kR.drop 13) = false := chainK _ _ 13 1 14 rfl sc13 rq14
def kid12 := kids (hdK (kR.drop 12)).1 (hdK (kR.drop 12)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c12_107 : anyK (node 0 7) (kid12.drop 107) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_100 : anyK (node 0 7) ((kid12.drop 100).take 7) = false := by decide +kernel
theorem c12_100 : anyK (node 0 7) (kid12.drop 100) = false := chainK _ _ 100 7 107 rfl t12_100 c12_107
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_90 : anyK (node 0 7) ((kid12.drop 90).take 10) = false := by decide +kernel
theorem c12_90 : anyK (node 0 7) (kid12.drop 90) = false := chainK _ _ 90 10 100 rfl t12_90 c12_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_80 : anyK (node 0 7) ((kid12.drop 80).take 10) = false := by decide +kernel
theorem c12_80 : anyK (node 0 7) (kid12.drop 80) = false := chainK _ _ 80 10 90 rfl t12_80 c12_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_70 : anyK (node 0 7) ((kid12.drop 70).take 10) = false := by decide +kernel
theorem c12_70 : anyK (node 0 7) (kid12.drop 70) = false := chainK _ _ 70 10 80 rfl t12_70 c12_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_60 : anyK (node 0 7) ((kid12.drop 60).take 10) = false := by decide +kernel
theorem c12_60 : anyK (node 0 7) (kid12.drop 60) = false := chainK _ _ 60 10 70 rfl t12_60 c12_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_50 : anyK (node 0 7) ((kid12.drop 50).take 10) = false := by decide +kernel
theorem c12_50 : anyK (node 0 7) (kid12.drop 50) = false := chainK _ _ 50 10 60 rfl t12_50 c12_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_40 : anyK (node 0 7) ((kid12.drop 40).take 10) = false := by decide +kernel
theorem c12_40 : anyK (node 0 7) (kid12.drop 40) = false := chainK _ _ 40 10 50 rfl t12_40 c12_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_30 : anyK (node 0 7) ((kid12.drop 30).take 10) = false := by decide +kernel
theorem c12_30 : anyK (node 0 7) (kid12.drop 30) = false := chainK _ _ 30 10 40 rfl t12_30 c12_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_20 : anyK (node 0 7) ((kid12.drop 20).take 10) = false := by decide +kernel
theorem c12_20 : anyK (node 0 7) (kid12.drop 20) = false := chainK _ _ 20 10 30 rfl t12_20 c12_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_10 : anyK (node 0 7) ((kid12.drop 10).take 10) = false := by decide +kernel
theorem c12_10 : anyK (node 0 7) (kid12.drop 10) = false := chainK _ _ 10 10 20 rfl t12_10 c12_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_0 : anyK (node 0 7) ((kid12.drop 0).take 10) = false := by decide +kernel
theorem c12_0 : anyK (node 0 7) (kid12.drop 0) = false := chainK _ _ 0 10 10 rfl t12_0 c12_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc12 : anyK (node 0 8) ((kR.drop 12).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid12 c12_0))
theorem rq12 : anyK (node 0 8) (kR.drop 12) = false := chainK _ _ 12 1 13 rfl sc12 rq13
def kid11 := kids (hdK (kR.drop 11)).1 (hdK (kR.drop 11)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c11_67 : anyK (node 0 7) (kid11.drop 67) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_60 : anyK (node 0 7) ((kid11.drop 60).take 7) = false := by decide +kernel
theorem c11_60 : anyK (node 0 7) (kid11.drop 60) = false := chainK _ _ 60 7 67 rfl t11_60 c11_67
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_50 : anyK (node 0 7) ((kid11.drop 50).take 10) = false := by decide +kernel
theorem c11_50 : anyK (node 0 7) (kid11.drop 50) = false := chainK _ _ 50 10 60 rfl t11_50 c11_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_40 : anyK (node 0 7) ((kid11.drop 40).take 10) = false := by decide +kernel
theorem c11_40 : anyK (node 0 7) (kid11.drop 40) = false := chainK _ _ 40 10 50 rfl t11_40 c11_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_30 : anyK (node 0 7) ((kid11.drop 30).take 10) = false := by decide +kernel
theorem c11_30 : anyK (node 0 7) (kid11.drop 30) = false := chainK _ _ 30 10 40 rfl t11_30 c11_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_20 : anyK (node 0 7) ((kid11.drop 20).take 10) = false := by decide +kernel
theorem c11_20 : anyK (node 0 7) (kid11.drop 20) = false := chainK _ _ 20 10 30 rfl t11_20 c11_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_10 : anyK (node 0 7) ((kid11.drop 10).take 10) = false := by decide +kernel
theorem c11_10 : anyK (node 0 7) (kid11.drop 10) = false := chainK _ _ 10 10 20 rfl t11_10 c11_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_0 : anyK (node 0 7) ((kid11.drop 0).take 10) = false := by decide +kernel
theorem c11_0 : anyK (node 0 7) (kid11.drop 0) = false := chainK _ _ 0 10 10 rfl t11_0 c11_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc11 : anyK (node 0 8) ((kR.drop 11).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid11 c11_0))
theorem rq11 : anyK (node 0 8) (kR.drop 11) = false := chainK _ _ 11 1 12 rfl sc11 rq12
def kid10 := kids (hdK (kR.drop 10)).1 (hdK (kR.drop 10)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c10_111 : anyK (node 0 7) (kid10.drop 111) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_110 : anyK (node 0 7) ((kid10.drop 110).take 1) = false := by decide +kernel
theorem c10_110 : anyK (node 0 7) (kid10.drop 110) = false := chainK _ _ 110 1 111 rfl t10_110 c10_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_100 : anyK (node 0 7) ((kid10.drop 100).take 10) = false := by decide +kernel
theorem c10_100 : anyK (node 0 7) (kid10.drop 100) = false := chainK _ _ 100 10 110 rfl t10_100 c10_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_90 : anyK (node 0 7) ((kid10.drop 90).take 10) = false := by decide +kernel
theorem c10_90 : anyK (node 0 7) (kid10.drop 90) = false := chainK _ _ 90 10 100 rfl t10_90 c10_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_80 : anyK (node 0 7) ((kid10.drop 80).take 10) = false := by decide +kernel
theorem c10_80 : anyK (node 0 7) (kid10.drop 80) = false := chainK _ _ 80 10 90 rfl t10_80 c10_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_70 : anyK (node 0 7) ((kid10.drop 70).take 10) = false := by decide +kernel
theorem c10_70 : anyK (node 0 7) (kid10.drop 70) = false := chainK _ _ 70 10 80 rfl t10_70 c10_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_60 : anyK (node 0 7) ((kid10.drop 60).take 10) = false := by decide +kernel
theorem c10_60 : anyK (node 0 7) (kid10.drop 60) = false := chainK _ _ 60 10 70 rfl t10_60 c10_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_50 : anyK (node 0 7) ((kid10.drop 50).take 10) = false := by decide +kernel
theorem c10_50 : anyK (node 0 7) (kid10.drop 50) = false := chainK _ _ 50 10 60 rfl t10_50 c10_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_40 : anyK (node 0 7) ((kid10.drop 40).take 10) = false := by decide +kernel
theorem c10_40 : anyK (node 0 7) (kid10.drop 40) = false := chainK _ _ 40 10 50 rfl t10_40 c10_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_30 : anyK (node 0 7) ((kid10.drop 30).take 10) = false := by decide +kernel
theorem c10_30 : anyK (node 0 7) (kid10.drop 30) = false := chainK _ _ 30 10 40 rfl t10_30 c10_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_20 : anyK (node 0 7) ((kid10.drop 20).take 10) = false := by decide +kernel
theorem c10_20 : anyK (node 0 7) (kid10.drop 20) = false := chainK _ _ 20 10 30 rfl t10_20 c10_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_10 : anyK (node 0 7) ((kid10.drop 10).take 10) = false := by decide +kernel
theorem c10_10 : anyK (node 0 7) (kid10.drop 10) = false := chainK _ _ 10 10 20 rfl t10_10 c10_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_0 : anyK (node 0 7) ((kid10.drop 0).take 10) = false := by decide +kernel
theorem c10_0 : anyK (node 0 7) (kid10.drop 0) = false := chainK _ _ 0 10 10 rfl t10_0 c10_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc10 : anyK (node 0 8) ((kR.drop 10).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid10 c10_0))
theorem rq10 : anyK (node 0 8) (kR.drop 10) = false := chainK _ _ 10 1 11 rfl sc10 rq11
def kid9 := kids (hdK (kR.drop 9)).1 (hdK (kR.drop 9)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c9_65 : anyK (node 0 7) (kid9.drop 65) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_60 : anyK (node 0 7) ((kid9.drop 60).take 5) = false := by decide +kernel
theorem c9_60 : anyK (node 0 7) (kid9.drop 60) = false := chainK _ _ 60 5 65 rfl t9_60 c9_65
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_50 : anyK (node 0 7) ((kid9.drop 50).take 10) = false := by decide +kernel
theorem c9_50 : anyK (node 0 7) (kid9.drop 50) = false := chainK _ _ 50 10 60 rfl t9_50 c9_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_40 : anyK (node 0 7) ((kid9.drop 40).take 10) = false := by decide +kernel
theorem c9_40 : anyK (node 0 7) (kid9.drop 40) = false := chainK _ _ 40 10 50 rfl t9_40 c9_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_30 : anyK (node 0 7) ((kid9.drop 30).take 10) = false := by decide +kernel
theorem c9_30 : anyK (node 0 7) (kid9.drop 30) = false := chainK _ _ 30 10 40 rfl t9_30 c9_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_20 : anyK (node 0 7) ((kid9.drop 20).take 10) = false := by decide +kernel
theorem c9_20 : anyK (node 0 7) (kid9.drop 20) = false := chainK _ _ 20 10 30 rfl t9_20 c9_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_10 : anyK (node 0 7) ((kid9.drop 10).take 10) = false := by decide +kernel
theorem c9_10 : anyK (node 0 7) (kid9.drop 10) = false := chainK _ _ 10 10 20 rfl t9_10 c9_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_0 : anyK (node 0 7) ((kid9.drop 0).take 10) = false := by decide +kernel
theorem c9_0 : anyK (node 0 7) (kid9.drop 0) = false := chainK _ _ 0 10 10 rfl t9_0 c9_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc9 : anyK (node 0 8) ((kR.drop 9).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid9 c9_0))
theorem rq9 : anyK (node 0 8) (kR.drop 9) = false := chainK _ _ 9 1 10 rfl sc9 rq10
def kid8 := kids (hdK (kR.drop 8)).1 (hdK (kR.drop 8)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c8_126 : anyK (node 0 7) (kid8.drop 126) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_120 : anyK (node 0 7) ((kid8.drop 120).take 6) = false := by decide +kernel
theorem c8_120 : anyK (node 0 7) (kid8.drop 120) = false := chainK _ _ 120 6 126 rfl t8_120 c8_126
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_110 : anyK (node 0 7) ((kid8.drop 110).take 10) = false := by decide +kernel
theorem c8_110 : anyK (node 0 7) (kid8.drop 110) = false := chainK _ _ 110 10 120 rfl t8_110 c8_120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_100 : anyK (node 0 7) ((kid8.drop 100).take 10) = false := by decide +kernel
theorem c8_100 : anyK (node 0 7) (kid8.drop 100) = false := chainK _ _ 100 10 110 rfl t8_100 c8_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_90 : anyK (node 0 7) ((kid8.drop 90).take 10) = false := by decide +kernel
theorem c8_90 : anyK (node 0 7) (kid8.drop 90) = false := chainK _ _ 90 10 100 rfl t8_90 c8_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_80 : anyK (node 0 7) ((kid8.drop 80).take 10) = false := by decide +kernel
theorem c8_80 : anyK (node 0 7) (kid8.drop 80) = false := chainK _ _ 80 10 90 rfl t8_80 c8_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_70 : anyK (node 0 7) ((kid8.drop 70).take 10) = false := by decide +kernel
theorem c8_70 : anyK (node 0 7) (kid8.drop 70) = false := chainK _ _ 70 10 80 rfl t8_70 c8_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_60 : anyK (node 0 7) ((kid8.drop 60).take 10) = false := by decide +kernel
theorem c8_60 : anyK (node 0 7) (kid8.drop 60) = false := chainK _ _ 60 10 70 rfl t8_60 c8_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_50 : anyK (node 0 7) ((kid8.drop 50).take 10) = false := by decide +kernel
theorem c8_50 : anyK (node 0 7) (kid8.drop 50) = false := chainK _ _ 50 10 60 rfl t8_50 c8_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_40 : anyK (node 0 7) ((kid8.drop 40).take 10) = false := by decide +kernel
theorem c8_40 : anyK (node 0 7) (kid8.drop 40) = false := chainK _ _ 40 10 50 rfl t8_40 c8_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_30 : anyK (node 0 7) ((kid8.drop 30).take 10) = false := by decide +kernel
theorem c8_30 : anyK (node 0 7) (kid8.drop 30) = false := chainK _ _ 30 10 40 rfl t8_30 c8_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_20 : anyK (node 0 7) ((kid8.drop 20).take 10) = false := by decide +kernel
theorem c8_20 : anyK (node 0 7) (kid8.drop 20) = false := chainK _ _ 20 10 30 rfl t8_20 c8_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_10 : anyK (node 0 7) ((kid8.drop 10).take 10) = false := by decide +kernel
theorem c8_10 : anyK (node 0 7) (kid8.drop 10) = false := chainK _ _ 10 10 20 rfl t8_10 c8_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_0 : anyK (node 0 7) ((kid8.drop 0).take 10) = false := by decide +kernel
theorem c8_0 : anyK (node 0 7) (kid8.drop 0) = false := chainK _ _ 0 10 10 rfl t8_0 c8_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc8 : anyK (node 0 8) ((kR.drop 8).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid8 c8_0))
theorem rq8 : anyK (node 0 8) (kR.drop 8) = false := chainK _ _ 8 1 9 rfl sc8 rq9
def kid7 := kids (hdK (kR.drop 7)).1 (hdK (kR.drop 7)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c7_70 : anyK (node 0 7) (kid7.drop 70) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_60 : anyK (node 0 7) ((kid7.drop 60).take 10) = false := by decide +kernel
theorem c7_60 : anyK (node 0 7) (kid7.drop 60) = false := chainK _ _ 60 10 70 rfl t7_60 c7_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_50 : anyK (node 0 7) ((kid7.drop 50).take 10) = false := by decide +kernel
theorem c7_50 : anyK (node 0 7) (kid7.drop 50) = false := chainK _ _ 50 10 60 rfl t7_50 c7_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_40 : anyK (node 0 7) ((kid7.drop 40).take 10) = false := by decide +kernel
theorem c7_40 : anyK (node 0 7) (kid7.drop 40) = false := chainK _ _ 40 10 50 rfl t7_40 c7_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_30 : anyK (node 0 7) ((kid7.drop 30).take 10) = false := by decide +kernel
theorem c7_30 : anyK (node 0 7) (kid7.drop 30) = false := chainK _ _ 30 10 40 rfl t7_30 c7_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_20 : anyK (node 0 7) ((kid7.drop 20).take 10) = false := by decide +kernel
theorem c7_20 : anyK (node 0 7) (kid7.drop 20) = false := chainK _ _ 20 10 30 rfl t7_20 c7_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_10 : anyK (node 0 7) ((kid7.drop 10).take 10) = false := by decide +kernel
theorem c7_10 : anyK (node 0 7) (kid7.drop 10) = false := chainK _ _ 10 10 20 rfl t7_10 c7_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_0 : anyK (node 0 7) ((kid7.drop 0).take 10) = false := by decide +kernel
theorem c7_0 : anyK (node 0 7) (kid7.drop 0) = false := chainK _ _ 0 10 10 rfl t7_0 c7_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc7 : anyK (node 0 8) ((kR.drop 7).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid7 c7_0))
theorem rq7 : anyK (node 0 8) (kR.drop 7) = false := chainK _ _ 7 1 8 rfl sc7 rq8
def kid6 := kids (hdK (kR.drop 6)).1 (hdK (kR.drop 6)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c6_112 : anyK (node 0 7) (kid6.drop 112) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_110 : anyK (node 0 7) ((kid6.drop 110).take 2) = false := by decide +kernel
theorem c6_110 : anyK (node 0 7) (kid6.drop 110) = false := chainK _ _ 110 2 112 rfl t6_110 c6_112
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_100 : anyK (node 0 7) ((kid6.drop 100).take 10) = false := by decide +kernel
theorem c6_100 : anyK (node 0 7) (kid6.drop 100) = false := chainK _ _ 100 10 110 rfl t6_100 c6_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_90 : anyK (node 0 7) ((kid6.drop 90).take 10) = false := by decide +kernel
theorem c6_90 : anyK (node 0 7) (kid6.drop 90) = false := chainK _ _ 90 10 100 rfl t6_90 c6_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_80 : anyK (node 0 7) ((kid6.drop 80).take 10) = false := by decide +kernel
theorem c6_80 : anyK (node 0 7) (kid6.drop 80) = false := chainK _ _ 80 10 90 rfl t6_80 c6_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_70 : anyK (node 0 7) ((kid6.drop 70).take 10) = false := by decide +kernel
theorem c6_70 : anyK (node 0 7) (kid6.drop 70) = false := chainK _ _ 70 10 80 rfl t6_70 c6_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_60 : anyK (node 0 7) ((kid6.drop 60).take 10) = false := by decide +kernel
theorem c6_60 : anyK (node 0 7) (kid6.drop 60) = false := chainK _ _ 60 10 70 rfl t6_60 c6_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_50 : anyK (node 0 7) ((kid6.drop 50).take 10) = false := by decide +kernel
theorem c6_50 : anyK (node 0 7) (kid6.drop 50) = false := chainK _ _ 50 10 60 rfl t6_50 c6_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_40 : anyK (node 0 7) ((kid6.drop 40).take 10) = false := by decide +kernel
theorem c6_40 : anyK (node 0 7) (kid6.drop 40) = false := chainK _ _ 40 10 50 rfl t6_40 c6_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_30 : anyK (node 0 7) ((kid6.drop 30).take 10) = false := by decide +kernel
theorem c6_30 : anyK (node 0 7) (kid6.drop 30) = false := chainK _ _ 30 10 40 rfl t6_30 c6_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_20 : anyK (node 0 7) ((kid6.drop 20).take 10) = false := by decide +kernel
theorem c6_20 : anyK (node 0 7) (kid6.drop 20) = false := chainK _ _ 20 10 30 rfl t6_20 c6_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_10 : anyK (node 0 7) ((kid6.drop 10).take 10) = false := by decide +kernel
theorem c6_10 : anyK (node 0 7) (kid6.drop 10) = false := chainK _ _ 10 10 20 rfl t6_10 c6_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_0 : anyK (node 0 7) ((kid6.drop 0).take 10) = false := by decide +kernel
theorem c6_0 : anyK (node 0 7) (kid6.drop 0) = false := chainK _ _ 0 10 10 rfl t6_0 c6_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc6 : anyK (node 0 8) ((kR.drop 6).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid6 c6_0))
theorem rq6 : anyK (node 0 8) (kR.drop 6) = false := chainK _ _ 6 1 7 rfl sc6 rq7
def kid5 := kids (hdK (kR.drop 5)).1 (hdK (kR.drop 5)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_67 : anyK (node 0 7) (kid5.drop 67) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_60 : anyK (node 0 7) ((kid5.drop 60).take 7) = false := by decide +kernel
theorem c5_60 : anyK (node 0 7) (kid5.drop 60) = false := chainK _ _ 60 7 67 rfl t5_60 c5_67
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_50 : anyK (node 0 7) ((kid5.drop 50).take 10) = false := by decide +kernel
theorem c5_50 : anyK (node 0 7) (kid5.drop 50) = false := chainK _ _ 50 10 60 rfl t5_50 c5_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_40 : anyK (node 0 7) ((kid5.drop 40).take 10) = false := by decide +kernel
theorem c5_40 : anyK (node 0 7) (kid5.drop 40) = false := chainK _ _ 40 10 50 rfl t5_40 c5_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_30 : anyK (node 0 7) ((kid5.drop 30).take 10) = false := by decide +kernel
theorem c5_30 : anyK (node 0 7) (kid5.drop 30) = false := chainK _ _ 30 10 40 rfl t5_30 c5_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_20 : anyK (node 0 7) ((kid5.drop 20).take 10) = false := by decide +kernel
theorem c5_20 : anyK (node 0 7) (kid5.drop 20) = false := chainK _ _ 20 10 30 rfl t5_20 c5_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_10 : anyK (node 0 7) ((kid5.drop 10).take 10) = false := by decide +kernel
theorem c5_10 : anyK (node 0 7) (kid5.drop 10) = false := chainK _ _ 10 10 20 rfl t5_10 c5_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_0 : anyK (node 0 7) ((kid5.drop 0).take 10) = false := by decide +kernel
theorem c5_0 : anyK (node 0 7) (kid5.drop 0) = false := chainK _ _ 0 10 10 rfl t5_0 c5_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc5 : anyK (node 0 8) ((kR.drop 5).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid5 c5_0))
theorem rq5 : anyK (node 0 8) (kR.drop 5) = false := chainK _ _ 5 1 6 rfl sc5 rq6
def kid4 := kids (hdK (kR.drop 4)).1 (hdK (kR.drop 4)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4_127 : anyK (node 0 7) (kid4.drop 127) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_120 : anyK (node 0 7) ((kid4.drop 120).take 7) = false := by decide +kernel
theorem c4_120 : anyK (node 0 7) (kid4.drop 120) = false := chainK _ _ 120 7 127 rfl t4_120 c4_127
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_110 : anyK (node 0 7) ((kid4.drop 110).take 10) = false := by decide +kernel
theorem c4_110 : anyK (node 0 7) (kid4.drop 110) = false := chainK _ _ 110 10 120 rfl t4_110 c4_120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_100 : anyK (node 0 7) ((kid4.drop 100).take 10) = false := by decide +kernel
theorem c4_100 : anyK (node 0 7) (kid4.drop 100) = false := chainK _ _ 100 10 110 rfl t4_100 c4_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_90 : anyK (node 0 7) ((kid4.drop 90).take 10) = false := by decide +kernel
theorem c4_90 : anyK (node 0 7) (kid4.drop 90) = false := chainK _ _ 90 10 100 rfl t4_90 c4_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_80 : anyK (node 0 7) ((kid4.drop 80).take 10) = false := by decide +kernel
theorem c4_80 : anyK (node 0 7) (kid4.drop 80) = false := chainK _ _ 80 10 90 rfl t4_80 c4_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_70 : anyK (node 0 7) ((kid4.drop 70).take 10) = false := by decide +kernel
theorem c4_70 : anyK (node 0 7) (kid4.drop 70) = false := chainK _ _ 70 10 80 rfl t4_70 c4_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_60 : anyK (node 0 7) ((kid4.drop 60).take 10) = false := by decide +kernel
theorem c4_60 : anyK (node 0 7) (kid4.drop 60) = false := chainK _ _ 60 10 70 rfl t4_60 c4_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_50 : anyK (node 0 7) ((kid4.drop 50).take 10) = false := by decide +kernel
theorem c4_50 : anyK (node 0 7) (kid4.drop 50) = false := chainK _ _ 50 10 60 rfl t4_50 c4_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_40 : anyK (node 0 7) ((kid4.drop 40).take 10) = false := by decide +kernel
theorem c4_40 : anyK (node 0 7) (kid4.drop 40) = false := chainK _ _ 40 10 50 rfl t4_40 c4_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_30 : anyK (node 0 7) ((kid4.drop 30).take 10) = false := by decide +kernel
theorem c4_30 : anyK (node 0 7) (kid4.drop 30) = false := chainK _ _ 30 10 40 rfl t4_30 c4_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_20 : anyK (node 0 7) ((kid4.drop 20).take 10) = false := by decide +kernel
theorem c4_20 : anyK (node 0 7) (kid4.drop 20) = false := chainK _ _ 20 10 30 rfl t4_20 c4_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_10 : anyK (node 0 7) ((kid4.drop 10).take 10) = false := by decide +kernel
theorem c4_10 : anyK (node 0 7) (kid4.drop 10) = false := chainK _ _ 10 10 20 rfl t4_10 c4_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_0 : anyK (node 0 7) ((kid4.drop 0).take 10) = false := by decide +kernel
theorem c4_0 : anyK (node 0 7) (kid4.drop 0) = false := chainK _ _ 0 10 10 rfl t4_0 c4_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc4 : anyK (node 0 8) ((kR.drop 4).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid4 c4_0))
theorem rq4 : anyK (node 0 8) (kR.drop 4) = false := chainK _ _ 4 1 5 rfl sc4 rq5
def kid3 := kids (hdK (kR.drop 3)).1 (hdK (kR.drop 3)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3_52 : anyK (node 0 7) (kid3.drop 52) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_50 : anyK (node 0 7) ((kid3.drop 50).take 2) = false := by decide +kernel
theorem c3_50 : anyK (node 0 7) (kid3.drop 50) = false := chainK _ _ 50 2 52 rfl t3_50 c3_52
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_40 : anyK (node 0 7) ((kid3.drop 40).take 10) = false := by decide +kernel
theorem c3_40 : anyK (node 0 7) (kid3.drop 40) = false := chainK _ _ 40 10 50 rfl t3_40 c3_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_30 : anyK (node 0 7) ((kid3.drop 30).take 10) = false := by decide +kernel
theorem c3_30 : anyK (node 0 7) (kid3.drop 30) = false := chainK _ _ 30 10 40 rfl t3_30 c3_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_20 : anyK (node 0 7) ((kid3.drop 20).take 10) = false := by decide +kernel
theorem c3_20 : anyK (node 0 7) (kid3.drop 20) = false := chainK _ _ 20 10 30 rfl t3_20 c3_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_10 : anyK (node 0 7) ((kid3.drop 10).take 10) = false := by decide +kernel
theorem c3_10 : anyK (node 0 7) (kid3.drop 10) = false := chainK _ _ 10 10 20 rfl t3_10 c3_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_0 : anyK (node 0 7) ((kid3.drop 0).take 10) = false := by decide +kernel
theorem c3_0 : anyK (node 0 7) (kid3.drop 0) = false := chainK _ _ 0 10 10 rfl t3_0 c3_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc3 : anyK (node 0 8) ((kR.drop 3).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid3 c3_0))
theorem rq3 : anyK (node 0 8) (kR.drop 3) = false := chainK _ _ 3 1 4 rfl sc3 rq4
def kid2 := kids (hdK (kR.drop 2)).1 (hdK (kR.drop 2)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2_110 : anyK (node 0 7) (kid2.drop 110) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_100 : anyK (node 0 7) ((kid2.drop 100).take 10) = false := by decide +kernel
theorem c2_100 : anyK (node 0 7) (kid2.drop 100) = false := chainK _ _ 100 10 110 rfl t2_100 c2_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_90 : anyK (node 0 7) ((kid2.drop 90).take 10) = false := by decide +kernel
theorem c2_90 : anyK (node 0 7) (kid2.drop 90) = false := chainK _ _ 90 10 100 rfl t2_90 c2_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_80 : anyK (node 0 7) ((kid2.drop 80).take 10) = false := by decide +kernel
theorem c2_80 : anyK (node 0 7) (kid2.drop 80) = false := chainK _ _ 80 10 90 rfl t2_80 c2_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_70 : anyK (node 0 7) ((kid2.drop 70).take 10) = false := by decide +kernel
theorem c2_70 : anyK (node 0 7) (kid2.drop 70) = false := chainK _ _ 70 10 80 rfl t2_70 c2_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_60 : anyK (node 0 7) ((kid2.drop 60).take 10) = false := by decide +kernel
theorem c2_60 : anyK (node 0 7) (kid2.drop 60) = false := chainK _ _ 60 10 70 rfl t2_60 c2_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_50 : anyK (node 0 7) ((kid2.drop 50).take 10) = false := by decide +kernel
theorem c2_50 : anyK (node 0 7) (kid2.drop 50) = false := chainK _ _ 50 10 60 rfl t2_50 c2_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_40 : anyK (node 0 7) ((kid2.drop 40).take 10) = false := by decide +kernel
theorem c2_40 : anyK (node 0 7) (kid2.drop 40) = false := chainK _ _ 40 10 50 rfl t2_40 c2_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_30 : anyK (node 0 7) ((kid2.drop 30).take 10) = false := by decide +kernel
theorem c2_30 : anyK (node 0 7) (kid2.drop 30) = false := chainK _ _ 30 10 40 rfl t2_30 c2_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_20 : anyK (node 0 7) ((kid2.drop 20).take 10) = false := by decide +kernel
theorem c2_20 : anyK (node 0 7) (kid2.drop 20) = false := chainK _ _ 20 10 30 rfl t2_20 c2_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_10 : anyK (node 0 7) ((kid2.drop 10).take 10) = false := by decide +kernel
theorem c2_10 : anyK (node 0 7) (kid2.drop 10) = false := chainK _ _ 10 10 20 rfl t2_10 c2_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_0 : anyK (node 0 7) ((kid2.drop 0).take 10) = false := by decide +kernel
theorem c2_0 : anyK (node 0 7) (kid2.drop 0) = false := chainK _ _ 0 10 10 rfl t2_0 c2_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc2 : anyK (node 0 8) ((kR.drop 2).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid2 c2_0))
theorem rq2 : anyK (node 0 8) (kR.drop 2) = false := chainK _ _ 2 1 3 rfl sc2 rq3
def kid1 := kids (hdK (kR.drop 1)).1 (hdK (kR.drop 1)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1_48 : anyK (node 0 7) (kid1.drop 48) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_40 : anyK (node 0 7) ((kid1.drop 40).take 8) = false := by decide +kernel
theorem c1_40 : anyK (node 0 7) (kid1.drop 40) = false := chainK _ _ 40 8 48 rfl t1_40 c1_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_30 : anyK (node 0 7) ((kid1.drop 30).take 10) = false := by decide +kernel
theorem c1_30 : anyK (node 0 7) (kid1.drop 30) = false := chainK _ _ 30 10 40 rfl t1_30 c1_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_20 : anyK (node 0 7) ((kid1.drop 20).take 10) = false := by decide +kernel
theorem c1_20 : anyK (node 0 7) (kid1.drop 20) = false := chainK _ _ 20 10 30 rfl t1_20 c1_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_10 : anyK (node 0 7) ((kid1.drop 10).take 10) = false := by decide +kernel
theorem c1_10 : anyK (node 0 7) (kid1.drop 10) = false := chainK _ _ 10 10 20 rfl t1_10 c1_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_0 : anyK (node 0 7) ((kid1.drop 0).take 10) = false := by decide +kernel
theorem c1_0 : anyK (node 0 7) (kid1.drop 0) = false := chainK _ _ 0 10 10 rfl t1_0 c1_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc1 : anyK (node 0 8) ((kR.drop 1).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid1 c1_0))
theorem rq1 : anyK (node 0 8) (kR.drop 1) = false := chainK _ _ 1 1 2 rfl sc1 rq2
def kid0 := kids (hdK (kR.drop 0)).1 (hdK (kR.drop 0)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0_128 : anyK (node 0 7) (kid0.drop 128) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_120 : anyK (node 0 7) ((kid0.drop 120).take 8) = false := by decide +kernel
theorem c0_120 : anyK (node 0 7) (kid0.drop 120) = false := chainK _ _ 120 8 128 rfl t0_120 c0_128
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_110 : anyK (node 0 7) ((kid0.drop 110).take 10) = false := by decide +kernel
theorem c0_110 : anyK (node 0 7) (kid0.drop 110) = false := chainK _ _ 110 10 120 rfl t0_110 c0_120
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_100 : anyK (node 0 7) ((kid0.drop 100).take 10) = false := by decide +kernel
theorem c0_100 : anyK (node 0 7) (kid0.drop 100) = false := chainK _ _ 100 10 110 rfl t0_100 c0_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_90 : anyK (node 0 7) ((kid0.drop 90).take 10) = false := by decide +kernel
theorem c0_90 : anyK (node 0 7) (kid0.drop 90) = false := chainK _ _ 90 10 100 rfl t0_90 c0_100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_80 : anyK (node 0 7) ((kid0.drop 80).take 10) = false := by decide +kernel
theorem c0_80 : anyK (node 0 7) (kid0.drop 80) = false := chainK _ _ 80 10 90 rfl t0_80 c0_90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_70 : anyK (node 0 7) ((kid0.drop 70).take 10) = false := by decide +kernel
theorem c0_70 : anyK (node 0 7) (kid0.drop 70) = false := chainK _ _ 70 10 80 rfl t0_70 c0_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_60 : anyK (node 0 7) ((kid0.drop 60).take 10) = false := by decide +kernel
theorem c0_60 : anyK (node 0 7) (kid0.drop 60) = false := chainK _ _ 60 10 70 rfl t0_60 c0_70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_50 : anyK (node 0 7) ((kid0.drop 50).take 10) = false := by decide +kernel
theorem c0_50 : anyK (node 0 7) (kid0.drop 50) = false := chainK _ _ 50 10 60 rfl t0_50 c0_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_40 : anyK (node 0 7) ((kid0.drop 40).take 10) = false := by decide +kernel
theorem c0_40 : anyK (node 0 7) (kid0.drop 40) = false := chainK _ _ 40 10 50 rfl t0_40 c0_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_30 : anyK (node 0 7) ((kid0.drop 30).take 10) = false := by decide +kernel
theorem c0_30 : anyK (node 0 7) (kid0.drop 30) = false := chainK _ _ 30 10 40 rfl t0_30 c0_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_20 : anyK (node 0 7) ((kid0.drop 20).take 10) = false := by decide +kernel
theorem c0_20 : anyK (node 0 7) (kid0.drop 20) = false := chainK _ _ 20 10 30 rfl t0_20 c0_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_10 : anyK (node 0 7) ((kid0.drop 10).take 10) = false := by decide +kernel
theorem c0_10 : anyK (node 0 7) (kid0.drop 10) = false := chainK _ _ 10 10 20 rfl t0_10 c0_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_0 : anyK (node 0 7) ((kid0.drop 0).take 10) = false := by decide +kernel
theorem c0_0 : anyK (node 0 7) (kid0.drop 0) = false := chainK _ _ 0 10 10 rfl t0_0 c0_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sc0 : anyK (node 0 8) ((kR.drop 0).take 1) = false := takeOneK _ _ (node_split 0 7 _ _ (by decide +kernel) (startK _ kid0 c0_0))
theorem rq0 : anyK (node 0 8) (kR.drop 0) = false := chainK _ _ 0 1 1 rfl sc0 rq1
theorem pr : anyK (node 0 8) kR = false := startK _ _ rq0

theorem root_goal : isGoal rowsN = false := by
  decide +kernel

theorem root_false : root 0 8 4 rowsN = false := root_split 0 8 4 rowsN root_goal pr

theorem reject : searchN 0 8 rowsN = false := by
  unfold searchN
  rw [List.any_eq_false]
  intro ws hws
  cases h : (decide (ws.length ≤ 8 + 2) && cutFull ws)
  · simp
  · have heq := only_full ws hws h
    subst heq
    have e : 8 + 2 - rowsN.length = 4 := by decide
    rw [e, root_false]
    simp

theorem goal_hi : goal.toNat = hiM := by
  decide +kernel

theorem goal_lo : (~~~goal).toNat = fullM := by
  decide +kernel

theorem sep_hi : Nat.land (sp hiM) fullM = fullM := by
  decide +kernel

theorem sep_lo : Nat.land (sp fullM) fullM = fullM := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 9 < binaryCost gs :=
  bound_from_searchN rows rfl (by decide) (by rw [rows_eq]; exact reject) goal_hi goal_lo sep_hi sep_lo
    (by decide +kernel) gs o hg he

theorem bridge : ∀ x : Fin 6 → Bool, Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = F x := by
  intro x; rfl

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [10, 15]⟩]

theorem wfits : PEqualNP.MetaComplexity.Monotone2 ⟨wg, 16⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_36839

theorem PEqualNP.Outside.L_meta_36839 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_36839.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_36839.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_36839.isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_36839.legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    have hb := PEqualNP.Outside.L_meta_36839.bound C.gates C.output hleg (fun x => (heval x).trans (PEqualNP.Outside.L_meta_36839.bridge x))
    have hsz : C.size = C.gates.length := rfl
    have hl : (⟨PEqualNP.Outside.L_meta_36839.wg, 16⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 11 := rfl
    exact ⟨⟨PEqualNP.Outside.L_meta_36839.wg, 16⟩, PEqualNP.Outside.L_meta_36839.wfits, by omega, PEqualNP.Outside.L_meta_36839.weval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
