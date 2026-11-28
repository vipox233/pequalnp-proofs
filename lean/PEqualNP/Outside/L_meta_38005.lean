import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38005

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
end Live

abbrev W := BitVec 256
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 256 0)[k.val] = false; simp
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

def nP : ℕ := 128
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

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem bound_from_searchN (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : searchN 0 8 (inputs.map BitVec.toNat) = false)
    (g1 : goal.toNat = hiM) (g2 : (~~~goal).toNat = fullM)
    (d1 : Nat.land (sp hiM) fullM = fullM) (d2 : Nat.land (sp fullM) fullM = fullM)
    (sample : ∀ k : Fin 256, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
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

def r0 : W := (0x280a014012104222#64 ++ 0x51488200c050002e#64 ++ 0xf81e0fe0fe01ffff#64 ++ 0xfff88200c05fffef#64 : BitVec 256)
def r1 : W := (0x845025048cb154#64 ++ 0xaa5752200004591#64 ++ 0x1ff0ff0fffe1fe#64 ++ 0x3f575223ff04593#64 : BitVec 256)
def r2 : W := (0x52a040b6a0253519#64 ++ 0xa82659d012848ec0#64 ++ 0xffe000fff001fe1f#64 ++ 0xfc0659dfd2848ec4#64 : BitVec 256)
def r3 : W := (0x9cd76a040049d990#64 ++ 0x30c79e0d65191700#64 ++ 0xffffff000001ffe0#64 ++ 0x79efd65191708#64 : BitVec 256)
def r4 : W := (0xe7198cd8c9700000#64 ++ 0xc1080099b9ee1808#64 ++ 0xfffffffffffe0000#64 ++ 0x83f99b9ee1818#64 : BitVec 256)
def r5 : W := (0x601081081800001#64 ++ 0x20020ee3e0fe000#64 ++ 0x0#64 ++ 0xfe0ee3e0fe020#64 : BitVec 256)
def rows : List W := [r0, r1, r2, r3, r4, r5]
def n0 : ℕ := (((0x280a014012104222 * 2 ^ 64 + 0x51488200c050002e) * 2 ^ 64 + 0xf81e0fe0fe01ffff) * 2 ^ 64 + 0xfff88200c05fffef)
def n1 : ℕ := (((0x845025048cb154 * 2 ^ 64 + 0xaa5752200004591) * 2 ^ 64 + 0x1ff0ff0fffe1fe) * 2 ^ 64 + 0x3f575223ff04593)
def n2 : ℕ := (((0x52a040b6a0253519 * 2 ^ 64 + 0xa82659d012848ec0) * 2 ^ 64 + 0xffe000fff001fe1f) * 2 ^ 64 + 0xfc0659dfd2848ec4)
def n3 : ℕ := (((0x9cd76a040049d990 * 2 ^ 64 + 0x30c79e0d65191700) * 2 ^ 64 + 0xffffff000001ffe0) * 2 ^ 64 + 0x79efd65191708)
def n4 : ℕ := (((0xe7198cd8c9700000 * 2 ^ 64 + 0xc1080099b9ee1808) * 2 ^ 64 + 0xfffffffffffe0000) * 2 ^ 64 + 0x83f99b9ee1818)
def n5 : ℕ := (((0x601081081800001 * 2 ^ 64 + 0x20020ee3e0fe000) * 2 ^ 64 + 0x0) * 2 ^ 64 + 0xfe0ee3e0fe020)
def rowsN : List ℕ := [n0, n1, n2, n3, n4, n5]

theorem rows_eq : rows.map BitVec.toNat = rowsN := by
  decide +kernel

theorem only_full : ∀ ws ∈ rowsN.sublists, (decide (ws.length ≤ 8 + 2) && cutFull ws) = true → ws = rowsN := by
  decide +kernel

def kR : List (ℕ × List ℕ) := kidsRoot 4 rowsN

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem qr_60 : anyK (node 0 8) (List.drop 60 kR) = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_58 : anyK (node 0 8) (List.take 2 (List.drop 58 kR)) = false := by
  decide +kernel
theorem qr_58 : anyK (node 0 8) (List.drop 58 kR) = false :=
  chainK (node 0 8) kR 58 2 60 rfl cr_58 qr_60
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_56 : anyK (node 0 8) (List.take 2 (List.drop 56 kR)) = false := by
  decide +kernel
theorem qr_56 : anyK (node 0 8) (List.drop 56 kR) = false :=
  chainK (node 0 8) kR 56 2 58 rfl cr_56 qr_58
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_54 : anyK (node 0 8) (List.take 2 (List.drop 54 kR)) = false := by
  decide +kernel
theorem qr_54 : anyK (node 0 8) (List.drop 54 kR) = false :=
  chainK (node 0 8) kR 54 2 56 rfl cr_54 qr_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_52 : anyK (node 0 8) (List.take 2 (List.drop 52 kR)) = false := by
  decide +kernel
theorem qr_52 : anyK (node 0 8) (List.drop 52 kR) = false :=
  chainK (node 0 8) kR 52 2 54 rfl cr_52 qr_54
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_49 : anyK (node 0 8) (List.take 3 (List.drop 49 kR)) = false := by
  decide +kernel
theorem qr_49 : anyK (node 0 8) (List.drop 49 kR) = false :=
  chainK (node 0 8) kR 49 3 52 rfl cr_49 qr_52
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_47 : anyK (node 0 8) (List.take 2 (List.drop 47 kR)) = false := by
  decide +kernel
theorem qr_47 : anyK (node 0 8) (List.drop 47 kR) = false :=
  chainK (node 0 8) kR 47 2 49 rfl cr_47 qr_49
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_45 : anyK (node 0 8) (List.take 2 (List.drop 45 kR)) = false := by
  decide +kernel
theorem qr_45 : anyK (node 0 8) (List.drop 45 kR) = false :=
  chainK (node 0 8) kR 45 2 47 rfl cr_45 qr_47
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_43 : anyK (node 0 8) (List.take 2 (List.drop 43 kR)) = false := by
  decide +kernel
theorem qr_43 : anyK (node 0 8) (List.drop 43 kR) = false :=
  chainK (node 0 8) kR 43 2 45 rfl cr_43 qr_45
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_40 : anyK (node 0 8) (List.take 3 (List.drop 40 kR)) = false := by
  decide +kernel
theorem qr_40 : anyK (node 0 8) (List.drop 40 kR) = false :=
  chainK (node 0 8) kR 40 3 43 rfl cr_40 qr_43
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_37 : anyK (node 0 8) (List.take 3 (List.drop 37 kR)) = false := by
  decide +kernel
theorem qr_37 : anyK (node 0 8) (List.drop 37 kR) = false :=
  chainK (node 0 8) kR 37 3 40 rfl cr_37 qr_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_35 : anyK (node 0 8) (List.take 2 (List.drop 35 kR)) = false := by
  decide +kernel
theorem qr_35 : anyK (node 0 8) (List.drop 35 kR) = false :=
  chainK (node 0 8) kR 35 2 37 rfl cr_35 qr_37
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_34 : anyK (node 0 8) (List.take 1 (List.drop 34 kR)) = false := by
  decide +kernel
theorem qr_34 : anyK (node 0 8) (List.drop 34 kR) = false :=
  chainK (node 0 8) kR 34 1 35 rfl cr_34 qr_35
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_32 : anyK (node 0 8) (List.take 2 (List.drop 32 kR)) = false := by
  decide +kernel
theorem qr_32 : anyK (node 0 8) (List.drop 32 kR) = false :=
  chainK (node 0 8) kR 32 2 34 rfl cr_32 qr_34
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_29 : anyK (node 0 8) (List.take 3 (List.drop 29 kR)) = false := by
  decide +kernel
theorem qr_29 : anyK (node 0 8) (List.drop 29 kR) = false :=
  chainK (node 0 8) kR 29 3 32 rfl cr_29 qr_32
def kr_28 : List (ℕ × List ℕ) := kids (hdK (List.drop 28 kR)).1 (hdK (List.drop 28 kR)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem qr_28_123 : anyK (node 0 7) (List.drop 123 kr_28) = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_28_49 : anyK (node 0 7) (List.take 74 (List.drop 49 kr_28)) = false := by
  decide +kernel
theorem qr_28_49 : anyK (node 0 7) (List.drop 49 kr_28) = false :=
  chainK (node 0 7) kr_28 49 74 123 rfl cr_28_49 qr_28_123
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_28_0 : anyK (node 0 7) (List.take 49 (List.drop 0 kr_28)) = false := by
  decide +kernel
theorem qr_28_0 : anyK (node 0 7) (List.drop 0 kr_28) = false :=
  chainK (node 0 7) kr_28 0 49 49 rfl cr_28_0 qr_28_49
theorem pr_28 : anyK (node 0 7) kr_28 = false := startK _ _ qr_28_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem gr_28 : isGoal (hdK (List.drop 28 kR)).2 = false := by
  decide +kernel
theorem qr_28 : anyK (node 0 8) (List.drop 28 kR) = false :=
  chainK (node 0 8) kR 28 1 29 rfl (takeOneK _ _ (node_split 0 7 (hdK (List.drop 28 kR)).1 (hdK (List.drop 28 kR)).2 gr_28 pr_28)) qr_29
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_27 : anyK (node 0 8) (List.take 1 (List.drop 27 kR)) = false := by
  decide +kernel
theorem qr_27 : anyK (node 0 8) (List.drop 27 kR) = false :=
  chainK (node 0 8) kR 27 1 28 rfl cr_27 qr_28
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_25 : anyK (node 0 8) (List.take 2 (List.drop 25 kR)) = false := by
  decide +kernel
theorem qr_25 : anyK (node 0 8) (List.drop 25 kR) = false :=
  chainK (node 0 8) kR 25 2 27 rfl cr_25 qr_27
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_23 : anyK (node 0 8) (List.take 2 (List.drop 23 kR)) = false := by
  decide +kernel
theorem qr_23 : anyK (node 0 8) (List.drop 23 kR) = false :=
  chainK (node 0 8) kR 23 2 25 rfl cr_23 qr_25
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_21 : anyK (node 0 8) (List.take 2 (List.drop 21 kR)) = false := by
  decide +kernel
theorem qr_21 : anyK (node 0 8) (List.drop 21 kR) = false :=
  chainK (node 0 8) kR 21 2 23 rfl cr_21 qr_23
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_19 : anyK (node 0 8) (List.take 2 (List.drop 19 kR)) = false := by
  decide +kernel
theorem qr_19 : anyK (node 0 8) (List.drop 19 kR) = false :=
  chainK (node 0 8) kR 19 2 21 rfl cr_19 qr_21
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_17 : anyK (node 0 8) (List.take 2 (List.drop 17 kR)) = false := by
  decide +kernel
theorem qr_17 : anyK (node 0 8) (List.drop 17 kR) = false :=
  chainK (node 0 8) kR 17 2 19 rfl cr_17 qr_19
def kr_16 : List (ℕ × List ℕ) := kids (hdK (List.drop 16 kR)).1 (hdK (List.drop 16 kR)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem qr_16_123 : anyK (node 0 7) (List.drop 123 kr_16) = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_16_54 : anyK (node 0 7) (List.take 69 (List.drop 54 kr_16)) = false := by
  decide +kernel
theorem qr_16_54 : anyK (node 0 7) (List.drop 54 kr_16) = false :=
  chainK (node 0 7) kr_16 54 69 123 rfl cr_16_54 qr_16_123
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_16_0 : anyK (node 0 7) (List.take 54 (List.drop 0 kr_16)) = false := by
  decide +kernel
theorem qr_16_0 : anyK (node 0 7) (List.drop 0 kr_16) = false :=
  chainK (node 0 7) kr_16 0 54 54 rfl cr_16_0 qr_16_54
theorem pr_16 : anyK (node 0 7) kr_16 = false := startK _ _ qr_16_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem gr_16 : isGoal (hdK (List.drop 16 kR)).2 = false := by
  decide +kernel
theorem qr_16 : anyK (node 0 8) (List.drop 16 kR) = false :=
  chainK (node 0 8) kR 16 1 17 rfl (takeOneK _ _ (node_split 0 7 (hdK (List.drop 16 kR)).1 (hdK (List.drop 16 kR)).2 gr_16 pr_16)) qr_17
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_14 : anyK (node 0 8) (List.take 2 (List.drop 14 kR)) = false := by
  decide +kernel
theorem qr_14 : anyK (node 0 8) (List.drop 14 kR) = false :=
  chainK (node 0 8) kR 14 2 16 rfl cr_14 qr_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_12 : anyK (node 0 8) (List.take 2 (List.drop 12 kR)) = false := by
  decide +kernel
theorem qr_12 : anyK (node 0 8) (List.drop 12 kR) = false :=
  chainK (node 0 8) kR 12 2 14 rfl cr_12 qr_14
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_10 : anyK (node 0 8) (List.take 2 (List.drop 10 kR)) = false := by
  decide +kernel
theorem qr_10 : anyK (node 0 8) (List.drop 10 kR) = false :=
  chainK (node 0 8) kR 10 2 12 rfl cr_10 qr_12
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_8 : anyK (node 0 8) (List.take 2 (List.drop 8 kR)) = false := by
  decide +kernel
theorem qr_8 : anyK (node 0 8) (List.drop 8 kR) = false :=
  chainK (node 0 8) kR 8 2 10 rfl cr_8 qr_10
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_5 : anyK (node 0 8) (List.take 3 (List.drop 5 kR)) = false := by
  decide +kernel
theorem qr_5 : anyK (node 0 8) (List.drop 5 kR) = false :=
  chainK (node 0 8) kR 5 3 8 rfl cr_5 qr_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_4 : anyK (node 0 8) (List.take 1 (List.drop 4 kR)) = false := by
  decide +kernel
theorem qr_4 : anyK (node 0 8) (List.drop 4 kR) = false :=
  chainK (node 0 8) kR 4 1 5 rfl cr_4 qr_5
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_3 : anyK (node 0 8) (List.take 1 (List.drop 3 kR)) = false := by
  decide +kernel
theorem qr_3 : anyK (node 0 8) (List.drop 3 kR) = false :=
  chainK (node 0 8) kR 3 1 4 rfl cr_3 qr_4
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_1 : anyK (node 0 8) (List.take 2 (List.drop 1 kR)) = false := by
  decide +kernel
theorem qr_1 : anyK (node 0 8) (List.drop 1 kR) = false :=
  chainK (node 0 8) kR 1 2 3 rfl cr_1 qr_3
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_0 : anyK (node 0 8) (List.take 1 (List.drop 0 kR)) = false := by
  decide +kernel
theorem qr_0 : anyK (node 0 8) (List.drop 0 kR) = false :=
  chainK (node 0 8) kR 0 1 1 rfl cr_0 qr_1
theorem pr : anyK (node 0 8) kR = false := startK _ _ qr_0

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

theorem bridge : ∀ x : Fin 6 → Bool, Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = F x := by
  intro x; rfl

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 15]⟩]

theorem wfits : PEqualNP.MetaComplexity.Monotone2 ⟨wg, 16⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_38005

theorem PEqualNP.Outside.L_meta_38005 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_38005.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_38005.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_38005.isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_38005.legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    have hb := PEqualNP.Outside.L_meta_38005.bound C.gates C.output hleg (fun x => (heval x).trans (PEqualNP.Outside.L_meta_38005.bridge x))
    have hsz : C.size = C.gates.length := rfl
    have hl : (⟨PEqualNP.Outside.L_meta_38005.wg, 16⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 11 := rfl
    exact ⟨⟨PEqualNP.Outside.L_meta_38005.wg, 16⟩, PEqualNP.Outside.L_meta_38005.wfits, by omega, PEqualNP.Outside.L_meta_38005.weval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
