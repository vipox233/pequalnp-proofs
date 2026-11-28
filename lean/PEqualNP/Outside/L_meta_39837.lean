import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39837.Signed

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
end Live

abbrev W := BitVec 512
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
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
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
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

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 512 0)[k.val] = false; simp
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

def nP : ℕ := 256
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

set_option maxRecDepth 100000 in
theorem bound_from_searchN (F : (Fin 5 → Bool) → Bool) (inputs : List W) (width : inputs.length = 5)
    (nd : inputs.Nodup) (reject : searchN 0 7 (inputs.map BitVec.toNat) = false)
    (g1 : goal.toNat = hiM) (g2 : (~~~goal).toNat = fullM)
    (d1 : Nat.land (sp hiM) fullM = fullM) (d2 : Nat.land (sp fullM) fullM = fullM)
    (sample : ∀ k : Fin 512, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)
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
  obtain ⟨L, hl, hr⟩ := run_of_build t 8 _ (lift low run0)
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
  have fin := searchN_complete 0 t.toNat ht' hD 7 (inputs.map BitVec.toNat)
    ((List.nodup_map_iff (fun _ _ h => BitVec.eq_of_toNat_eq h)).mpr nd) L hr hl
  exact Bool.noConfusion (reject.symm.trans fin)

def r0 : W := 0xf22b47124cf07005#64 ++ 0x1823c100281488#64 ++ 0x34d0532840305c0c#64 ++ 0x18411b3085c101e4#64 ++ 0xeef3b19ffffeef5e#64 ++ 0xfe6fafdbbfffbaf4#64 ++ 0x9befe4ffddf77f5f#64 ++ 0xbbe7fffa9ad3f7dd#64
def n0 : ℕ := (((((((0xf22b47124cf07005 * 2 ^ 64 + 0x1823c100281488) * 2 ^ 64 + 0x34d0532840305c0c) * 2 ^ 64 + 0x18411b3085c101e4) * 2 ^ 64 + 0xeef3b19ffffeef5e) * 2 ^ 64 + 0xfe6fafdbbfffbaf4) * 2 ^ 64 + 0x9befe4ffddf77f5f) * 2 ^ 64 + 0xbbe7fffa9ad3f7dd)
def r1 : W := 0x8124858713a447a0#64 ++ 0x940c3502b516b8a8#64 ++ 0x898dd23834028f9#64 ++ 0x2434a85661848102#64 ++ 0xfddc4e739fdb97fd#64 ++ 0xcfbafabf7dd3c7eb#64 ++ 0x6d9d9f35f33cd5ea#64 ++ 0x67fe9f3d7ffd39fb#64
def n1 : ℕ := (((((((0x8124858713a447a0 * 2 ^ 64 + 0x940c3502b516b8a8) * 2 ^ 64 + 0x898dd23834028f9) * 2 ^ 64 + 0x2434a85661848102) * 2 ^ 64 + 0xfddc4e739fdb97fd) * 2 ^ 64 + 0xcfbafabf7dd3c7eb) * 2 ^ 64 + 0x6d9d9f35f33cd5ea) * 2 ^ 64 + 0x67fe9f3d7ffd39fb)
def r2 : W := 0x4c49868444805c0#64 ++ 0xe721c82d0a404116#64 ++ 0xe26102039c881513#64 ++ 0x143440c9c005409#64 ++ 0x91bf5ef3edaffbff#64 ++ 0xb3f1f6bdf6f4f52f#64 ++ 0x77bdffdfeff9dff7#64 ++ 0xfd9d7cfffffcaf23#64
def n2 : ℕ := (((((((0x4c49868444805c0 * 2 ^ 64 + 0xe721c82d0a404116) * 2 ^ 64 + 0xe26102039c881513) * 2 ^ 64 + 0x143440c9c005409) * 2 ^ 64 + 0x91bf5ef3edaffbff) * 2 ^ 64 + 0xb3f1f6bdf6f4f52f) * 2 ^ 64 + 0x77bdffdfeff9dff7) * 2 ^ 64 + 0xfd9d7cfffffcaf23)
def r3 : W := 0x9430d3da286c201#64 ++ 0x7ab8307c9ec78b21#64 ++ 0x4e9f60743e204b82#64 ++ 0xb018ce6201274a12#64 ++ 0x1affbdddb0d077af#64 ++ 0x3b051375db9efddb#64 ++ 0x9dc33eb0add73a97#64 ++ 0xcc1f37bbbdbe5435#64
def n3 : ℕ := (((((((0x9430d3da286c201 * 2 ^ 64 + 0x7ab8307c9ec78b21) * 2 ^ 64 + 0x4e9f60743e204b82) * 2 ^ 64 + 0xb018ce6201274a12) * 2 ^ 64 + 0x1affbdddb0d077af) * 2 ^ 64 + 0x3b051375db9efddb) * 2 ^ 64 + 0x9dc33eb0add73a97) * 2 ^ 64 + 0xcc1f37bbbdbe5435)
def r4 : W := 0x31881a8d23110062#64 ++ 0x6b601c90dd494110#64 ++ 0x492d005c451f2244#64 ++ 0xbac704372361c63#64 ++ 0xff51fb6d56770df6#64 ++ 0x6ddfcd4e4bef9ef5#64 ++ 0xfffff77b537ebafe#64 ++ 0x5662ebeed3e7dbfe#64
def n4 : ℕ := (((((((0x31881a8d23110062 * 2 ^ 64 + 0x6b601c90dd494110) * 2 ^ 64 + 0x492d005c451f2244) * 2 ^ 64 + 0xbac704372361c63) * 2 ^ 64 + 0xff51fb6d56770df6) * 2 ^ 64 + 0x6ddfcd4e4bef9ef5) * 2 ^ 64 + 0xfffff77b537ebafe) * 2 ^ 64 + 0x5662ebeed3e7dbfe)
def rows : List W := [r0,r1,r2,r3,r4]
def rowsN : List ℕ := [n0,n1,n2,n3,n4]
theorem rows_eq : rows.map BitVec.toNat = rowsN := by
  decide +kernel

theorem only_full : ∀ ws ∈ rowsN.sublists, (decide (ws.length ≤ 7 + 2) && cutFull ws) = true → ws = rowsN := by
  decide +kernel

def kR : List (ℕ × List ℕ) := kidsRoot 4 rowsN

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rq40 : anyK (node 0 7) (kR.drop 40) = false := by decide +kernel
def kid39 := kids (hdK (kR.drop 39)).1 (hdK (kR.drop 39)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c39_57 : anyK (node 0 6) (kid39.drop 57) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_56 : anyK (node 0 6) ((kid39.drop 56).take 1) = false := by decide +kernel
theorem c39_56 : anyK (node 0 6) (kid39.drop 56) = false := chainK _ _ 56 1 57 rfl t39_56 c39_57
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_48 : anyK (node 0 6) ((kid39.drop 48).take 8) = false := by decide +kernel
theorem c39_48 : anyK (node 0 6) (kid39.drop 48) = false := chainK _ _ 48 8 56 rfl t39_48 c39_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_40 : anyK (node 0 6) ((kid39.drop 40).take 8) = false := by decide +kernel
theorem c39_40 : anyK (node 0 6) (kid39.drop 40) = false := chainK _ _ 40 8 48 rfl t39_40 c39_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_32 : anyK (node 0 6) ((kid39.drop 32).take 8) = false := by decide +kernel
theorem c39_32 : anyK (node 0 6) (kid39.drop 32) = false := chainK _ _ 32 8 40 rfl t39_32 c39_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_24 : anyK (node 0 6) ((kid39.drop 24).take 8) = false := by decide +kernel
theorem c39_24 : anyK (node 0 6) (kid39.drop 24) = false := chainK _ _ 24 8 32 rfl t39_24 c39_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_16 : anyK (node 0 6) ((kid39.drop 16).take 8) = false := by decide +kernel
theorem c39_16 : anyK (node 0 6) (kid39.drop 16) = false := chainK _ _ 16 8 24 rfl t39_16 c39_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_8 : anyK (node 0 6) ((kid39.drop 8).take 8) = false := by decide +kernel
theorem c39_8 : anyK (node 0 6) (kid39.drop 8) = false := chainK _ _ 8 8 16 rfl t39_8 c39_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t39_0 : anyK (node 0 6) ((kid39.drop 0).take 8) = false := by decide +kernel
theorem c39_0 : anyK (node 0 6) (kid39.drop 0) = false := chainK _ _ 0 8 8 rfl t39_0 c39_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase39 : anyK (node 0 7) ((kR.drop 39).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid39 c39_0))
theorem rq39 : anyK (node 0 7) (kR.drop 39) = false := chainK _ _ 39 1 40 rfl rcase39 rq40
def kid38 := kids (hdK (kR.drop 38)).1 (hdK (kR.drop 38)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c38_67 : anyK (node 0 6) (kid38.drop 67) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_64 : anyK (node 0 6) ((kid38.drop 64).take 3) = false := by decide +kernel
theorem c38_64 : anyK (node 0 6) (kid38.drop 64) = false := chainK _ _ 64 3 67 rfl t38_64 c38_67
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_56 : anyK (node 0 6) ((kid38.drop 56).take 8) = false := by decide +kernel
theorem c38_56 : anyK (node 0 6) (kid38.drop 56) = false := chainK _ _ 56 8 64 rfl t38_56 c38_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_48 : anyK (node 0 6) ((kid38.drop 48).take 8) = false := by decide +kernel
theorem c38_48 : anyK (node 0 6) (kid38.drop 48) = false := chainK _ _ 48 8 56 rfl t38_48 c38_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_40 : anyK (node 0 6) ((kid38.drop 40).take 8) = false := by decide +kernel
theorem c38_40 : anyK (node 0 6) (kid38.drop 40) = false := chainK _ _ 40 8 48 rfl t38_40 c38_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_32 : anyK (node 0 6) ((kid38.drop 32).take 8) = false := by decide +kernel
theorem c38_32 : anyK (node 0 6) (kid38.drop 32) = false := chainK _ _ 32 8 40 rfl t38_32 c38_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_24 : anyK (node 0 6) ((kid38.drop 24).take 8) = false := by decide +kernel
theorem c38_24 : anyK (node 0 6) (kid38.drop 24) = false := chainK _ _ 24 8 32 rfl t38_24 c38_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_16 : anyK (node 0 6) ((kid38.drop 16).take 8) = false := by decide +kernel
theorem c38_16 : anyK (node 0 6) (kid38.drop 16) = false := chainK _ _ 16 8 24 rfl t38_16 c38_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_8 : anyK (node 0 6) ((kid38.drop 8).take 8) = false := by decide +kernel
theorem c38_8 : anyK (node 0 6) (kid38.drop 8) = false := chainK _ _ 8 8 16 rfl t38_8 c38_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t38_0 : anyK (node 0 6) ((kid38.drop 0).take 8) = false := by decide +kernel
theorem c38_0 : anyK (node 0 6) (kid38.drop 0) = false := chainK _ _ 0 8 8 rfl t38_0 c38_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase38 : anyK (node 0 7) ((kR.drop 38).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid38 c38_0))
theorem rq38 : anyK (node 0 7) (kR.drop 38) = false := chainK _ _ 38 1 39 rfl rcase38 rq39
def kid37 := kids (hdK (kR.drop 37)).1 (hdK (kR.drop 37)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c37_52 : anyK (node 0 6) (kid37.drop 52) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_48 : anyK (node 0 6) ((kid37.drop 48).take 4) = false := by decide +kernel
theorem c37_48 : anyK (node 0 6) (kid37.drop 48) = false := chainK _ _ 48 4 52 rfl t37_48 c37_52
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_40 : anyK (node 0 6) ((kid37.drop 40).take 8) = false := by decide +kernel
theorem c37_40 : anyK (node 0 6) (kid37.drop 40) = false := chainK _ _ 40 8 48 rfl t37_40 c37_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_32 : anyK (node 0 6) ((kid37.drop 32).take 8) = false := by decide +kernel
theorem c37_32 : anyK (node 0 6) (kid37.drop 32) = false := chainK _ _ 32 8 40 rfl t37_32 c37_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_24 : anyK (node 0 6) ((kid37.drop 24).take 8) = false := by decide +kernel
theorem c37_24 : anyK (node 0 6) (kid37.drop 24) = false := chainK _ _ 24 8 32 rfl t37_24 c37_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_16 : anyK (node 0 6) ((kid37.drop 16).take 8) = false := by decide +kernel
theorem c37_16 : anyK (node 0 6) (kid37.drop 16) = false := chainK _ _ 16 8 24 rfl t37_16 c37_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_8 : anyK (node 0 6) ((kid37.drop 8).take 8) = false := by decide +kernel
theorem c37_8 : anyK (node 0 6) (kid37.drop 8) = false := chainK _ _ 8 8 16 rfl t37_8 c37_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t37_0 : anyK (node 0 6) ((kid37.drop 0).take 8) = false := by decide +kernel
theorem c37_0 : anyK (node 0 6) (kid37.drop 0) = false := chainK _ _ 0 8 8 rfl t37_0 c37_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase37 : anyK (node 0 7) ((kR.drop 37).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid37 c37_0))
theorem rq37 : anyK (node 0 7) (kR.drop 37) = false := chainK _ _ 37 1 38 rfl rcase37 rq38
def kid36 := kids (hdK (kR.drop 36)).1 (hdK (kR.drop 36)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c36_71 : anyK (node 0 6) (kid36.drop 71) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_64 : anyK (node 0 6) ((kid36.drop 64).take 7) = false := by decide +kernel
theorem c36_64 : anyK (node 0 6) (kid36.drop 64) = false := chainK _ _ 64 7 71 rfl t36_64 c36_71
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_56 : anyK (node 0 6) ((kid36.drop 56).take 8) = false := by decide +kernel
theorem c36_56 : anyK (node 0 6) (kid36.drop 56) = false := chainK _ _ 56 8 64 rfl t36_56 c36_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_48 : anyK (node 0 6) ((kid36.drop 48).take 8) = false := by decide +kernel
theorem c36_48 : anyK (node 0 6) (kid36.drop 48) = false := chainK _ _ 48 8 56 rfl t36_48 c36_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_40 : anyK (node 0 6) ((kid36.drop 40).take 8) = false := by decide +kernel
theorem c36_40 : anyK (node 0 6) (kid36.drop 40) = false := chainK _ _ 40 8 48 rfl t36_40 c36_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_32 : anyK (node 0 6) ((kid36.drop 32).take 8) = false := by decide +kernel
theorem c36_32 : anyK (node 0 6) (kid36.drop 32) = false := chainK _ _ 32 8 40 rfl t36_32 c36_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_24 : anyK (node 0 6) ((kid36.drop 24).take 8) = false := by decide +kernel
theorem c36_24 : anyK (node 0 6) (kid36.drop 24) = false := chainK _ _ 24 8 32 rfl t36_24 c36_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_16 : anyK (node 0 6) ((kid36.drop 16).take 8) = false := by decide +kernel
theorem c36_16 : anyK (node 0 6) (kid36.drop 16) = false := chainK _ _ 16 8 24 rfl t36_16 c36_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_8 : anyK (node 0 6) ((kid36.drop 8).take 8) = false := by decide +kernel
theorem c36_8 : anyK (node 0 6) (kid36.drop 8) = false := chainK _ _ 8 8 16 rfl t36_8 c36_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t36_0 : anyK (node 0 6) ((kid36.drop 0).take 8) = false := by decide +kernel
theorem c36_0 : anyK (node 0 6) (kid36.drop 0) = false := chainK _ _ 0 8 8 rfl t36_0 c36_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase36 : anyK (node 0 7) ((kR.drop 36).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid36 c36_0))
theorem rq36 : anyK (node 0 7) (kR.drop 36) = false := chainK _ _ 36 1 37 rfl rcase36 rq37
def kid35 := kids (hdK (kR.drop 35)).1 (hdK (kR.drop 35)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c35_53 : anyK (node 0 6) (kid35.drop 53) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_48 : anyK (node 0 6) ((kid35.drop 48).take 5) = false := by decide +kernel
theorem c35_48 : anyK (node 0 6) (kid35.drop 48) = false := chainK _ _ 48 5 53 rfl t35_48 c35_53
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_40 : anyK (node 0 6) ((kid35.drop 40).take 8) = false := by decide +kernel
theorem c35_40 : anyK (node 0 6) (kid35.drop 40) = false := chainK _ _ 40 8 48 rfl t35_40 c35_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_32 : anyK (node 0 6) ((kid35.drop 32).take 8) = false := by decide +kernel
theorem c35_32 : anyK (node 0 6) (kid35.drop 32) = false := chainK _ _ 32 8 40 rfl t35_32 c35_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_24 : anyK (node 0 6) ((kid35.drop 24).take 8) = false := by decide +kernel
theorem c35_24 : anyK (node 0 6) (kid35.drop 24) = false := chainK _ _ 24 8 32 rfl t35_24 c35_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_16 : anyK (node 0 6) ((kid35.drop 16).take 8) = false := by decide +kernel
theorem c35_16 : anyK (node 0 6) (kid35.drop 16) = false := chainK _ _ 16 8 24 rfl t35_16 c35_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_8 : anyK (node 0 6) ((kid35.drop 8).take 8) = false := by decide +kernel
theorem c35_8 : anyK (node 0 6) (kid35.drop 8) = false := chainK _ _ 8 8 16 rfl t35_8 c35_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t35_0 : anyK (node 0 6) ((kid35.drop 0).take 8) = false := by decide +kernel
theorem c35_0 : anyK (node 0 6) (kid35.drop 0) = false := chainK _ _ 0 8 8 rfl t35_0 c35_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase35 : anyK (node 0 7) ((kR.drop 35).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid35 c35_0))
theorem rq35 : anyK (node 0 7) (kR.drop 35) = false := chainK _ _ 35 1 36 rfl rcase35 rq36
def kid34 := kids (hdK (kR.drop 34)).1 (hdK (kR.drop 34)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c34_68 : anyK (node 0 6) (kid34.drop 68) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_64 : anyK (node 0 6) ((kid34.drop 64).take 4) = false := by decide +kernel
theorem c34_64 : anyK (node 0 6) (kid34.drop 64) = false := chainK _ _ 64 4 68 rfl t34_64 c34_68
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_56 : anyK (node 0 6) ((kid34.drop 56).take 8) = false := by decide +kernel
theorem c34_56 : anyK (node 0 6) (kid34.drop 56) = false := chainK _ _ 56 8 64 rfl t34_56 c34_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_48 : anyK (node 0 6) ((kid34.drop 48).take 8) = false := by decide +kernel
theorem c34_48 : anyK (node 0 6) (kid34.drop 48) = false := chainK _ _ 48 8 56 rfl t34_48 c34_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_40 : anyK (node 0 6) ((kid34.drop 40).take 8) = false := by decide +kernel
theorem c34_40 : anyK (node 0 6) (kid34.drop 40) = false := chainK _ _ 40 8 48 rfl t34_40 c34_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_32 : anyK (node 0 6) ((kid34.drop 32).take 8) = false := by decide +kernel
theorem c34_32 : anyK (node 0 6) (kid34.drop 32) = false := chainK _ _ 32 8 40 rfl t34_32 c34_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_24 : anyK (node 0 6) ((kid34.drop 24).take 8) = false := by decide +kernel
theorem c34_24 : anyK (node 0 6) (kid34.drop 24) = false := chainK _ _ 24 8 32 rfl t34_24 c34_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_16 : anyK (node 0 6) ((kid34.drop 16).take 8) = false := by decide +kernel
theorem c34_16 : anyK (node 0 6) (kid34.drop 16) = false := chainK _ _ 16 8 24 rfl t34_16 c34_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_8 : anyK (node 0 6) ((kid34.drop 8).take 8) = false := by decide +kernel
theorem c34_8 : anyK (node 0 6) (kid34.drop 8) = false := chainK _ _ 8 8 16 rfl t34_8 c34_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t34_0 : anyK (node 0 6) ((kid34.drop 0).take 8) = false := by decide +kernel
theorem c34_0 : anyK (node 0 6) (kid34.drop 0) = false := chainK _ _ 0 8 8 rfl t34_0 c34_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase34 : anyK (node 0 7) ((kR.drop 34).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid34 c34_0))
theorem rq34 : anyK (node 0 7) (kR.drop 34) = false := chainK _ _ 34 1 35 rfl rcase34 rq35
def kid33 := kids (hdK (kR.drop 33)).1 (hdK (kR.drop 33)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c33_63 : anyK (node 0 6) (kid33.drop 63) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_56 : anyK (node 0 6) ((kid33.drop 56).take 7) = false := by decide +kernel
theorem c33_56 : anyK (node 0 6) (kid33.drop 56) = false := chainK _ _ 56 7 63 rfl t33_56 c33_63
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_48 : anyK (node 0 6) ((kid33.drop 48).take 8) = false := by decide +kernel
theorem c33_48 : anyK (node 0 6) (kid33.drop 48) = false := chainK _ _ 48 8 56 rfl t33_48 c33_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_40 : anyK (node 0 6) ((kid33.drop 40).take 8) = false := by decide +kernel
theorem c33_40 : anyK (node 0 6) (kid33.drop 40) = false := chainK _ _ 40 8 48 rfl t33_40 c33_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_32 : anyK (node 0 6) ((kid33.drop 32).take 8) = false := by decide +kernel
theorem c33_32 : anyK (node 0 6) (kid33.drop 32) = false := chainK _ _ 32 8 40 rfl t33_32 c33_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_24 : anyK (node 0 6) ((kid33.drop 24).take 8) = false := by decide +kernel
theorem c33_24 : anyK (node 0 6) (kid33.drop 24) = false := chainK _ _ 24 8 32 rfl t33_24 c33_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_16 : anyK (node 0 6) ((kid33.drop 16).take 8) = false := by decide +kernel
theorem c33_16 : anyK (node 0 6) (kid33.drop 16) = false := chainK _ _ 16 8 24 rfl t33_16 c33_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_8 : anyK (node 0 6) ((kid33.drop 8).take 8) = false := by decide +kernel
theorem c33_8 : anyK (node 0 6) (kid33.drop 8) = false := chainK _ _ 8 8 16 rfl t33_8 c33_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t33_0 : anyK (node 0 6) ((kid33.drop 0).take 8) = false := by decide +kernel
theorem c33_0 : anyK (node 0 6) (kid33.drop 0) = false := chainK _ _ 0 8 8 rfl t33_0 c33_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase33 : anyK (node 0 7) ((kR.drop 33).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid33 c33_0))
theorem rq33 : anyK (node 0 7) (kR.drop 33) = false := chainK _ _ 33 1 34 rfl rcase33 rq34
def kid32 := kids (hdK (kR.drop 32)).1 (hdK (kR.drop 32)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c32_79 : anyK (node 0 6) (kid32.drop 79) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_72 : anyK (node 0 6) ((kid32.drop 72).take 7) = false := by decide +kernel
theorem c32_72 : anyK (node 0 6) (kid32.drop 72) = false := chainK _ _ 72 7 79 rfl t32_72 c32_79
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_64 : anyK (node 0 6) ((kid32.drop 64).take 8) = false := by decide +kernel
theorem c32_64 : anyK (node 0 6) (kid32.drop 64) = false := chainK _ _ 64 8 72 rfl t32_64 c32_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_56 : anyK (node 0 6) ((kid32.drop 56).take 8) = false := by decide +kernel
theorem c32_56 : anyK (node 0 6) (kid32.drop 56) = false := chainK _ _ 56 8 64 rfl t32_56 c32_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_48 : anyK (node 0 6) ((kid32.drop 48).take 8) = false := by decide +kernel
theorem c32_48 : anyK (node 0 6) (kid32.drop 48) = false := chainK _ _ 48 8 56 rfl t32_48 c32_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_40 : anyK (node 0 6) ((kid32.drop 40).take 8) = false := by decide +kernel
theorem c32_40 : anyK (node 0 6) (kid32.drop 40) = false := chainK _ _ 40 8 48 rfl t32_40 c32_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_32 : anyK (node 0 6) ((kid32.drop 32).take 8) = false := by decide +kernel
theorem c32_32 : anyK (node 0 6) (kid32.drop 32) = false := chainK _ _ 32 8 40 rfl t32_32 c32_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_24 : anyK (node 0 6) ((kid32.drop 24).take 8) = false := by decide +kernel
theorem c32_24 : anyK (node 0 6) (kid32.drop 24) = false := chainK _ _ 24 8 32 rfl t32_24 c32_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_16 : anyK (node 0 6) ((kid32.drop 16).take 8) = false := by decide +kernel
theorem c32_16 : anyK (node 0 6) (kid32.drop 16) = false := chainK _ _ 16 8 24 rfl t32_16 c32_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_8 : anyK (node 0 6) ((kid32.drop 8).take 8) = false := by decide +kernel
theorem c32_8 : anyK (node 0 6) (kid32.drop 8) = false := chainK _ _ 8 8 16 rfl t32_8 c32_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t32_0 : anyK (node 0 6) ((kid32.drop 0).take 8) = false := by decide +kernel
theorem c32_0 : anyK (node 0 6) (kid32.drop 0) = false := chainK _ _ 0 8 8 rfl t32_0 c32_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase32 : anyK (node 0 7) ((kR.drop 32).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid32 c32_0))
theorem rq32 : anyK (node 0 7) (kR.drop 32) = false := chainK _ _ 32 1 33 rfl rcase32 rq33
def kid31 := kids (hdK (kR.drop 31)).1 (hdK (kR.drop 31)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c31_63 : anyK (node 0 6) (kid31.drop 63) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_56 : anyK (node 0 6) ((kid31.drop 56).take 7) = false := by decide +kernel
theorem c31_56 : anyK (node 0 6) (kid31.drop 56) = false := chainK _ _ 56 7 63 rfl t31_56 c31_63
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_48 : anyK (node 0 6) ((kid31.drop 48).take 8) = false := by decide +kernel
theorem c31_48 : anyK (node 0 6) (kid31.drop 48) = false := chainK _ _ 48 8 56 rfl t31_48 c31_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_40 : anyK (node 0 6) ((kid31.drop 40).take 8) = false := by decide +kernel
theorem c31_40 : anyK (node 0 6) (kid31.drop 40) = false := chainK _ _ 40 8 48 rfl t31_40 c31_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_32 : anyK (node 0 6) ((kid31.drop 32).take 8) = false := by decide +kernel
theorem c31_32 : anyK (node 0 6) (kid31.drop 32) = false := chainK _ _ 32 8 40 rfl t31_32 c31_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_24 : anyK (node 0 6) ((kid31.drop 24).take 8) = false := by decide +kernel
theorem c31_24 : anyK (node 0 6) (kid31.drop 24) = false := chainK _ _ 24 8 32 rfl t31_24 c31_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_16 : anyK (node 0 6) ((kid31.drop 16).take 8) = false := by decide +kernel
theorem c31_16 : anyK (node 0 6) (kid31.drop 16) = false := chainK _ _ 16 8 24 rfl t31_16 c31_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_8 : anyK (node 0 6) ((kid31.drop 8).take 8) = false := by decide +kernel
theorem c31_8 : anyK (node 0 6) (kid31.drop 8) = false := chainK _ _ 8 8 16 rfl t31_8 c31_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t31_0 : anyK (node 0 6) ((kid31.drop 0).take 8) = false := by decide +kernel
theorem c31_0 : anyK (node 0 6) (kid31.drop 0) = false := chainK _ _ 0 8 8 rfl t31_0 c31_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase31 : anyK (node 0 7) ((kR.drop 31).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid31 c31_0))
theorem rq31 : anyK (node 0 7) (kR.drop 31) = false := chainK _ _ 31 1 32 rfl rcase31 rq32
def kid30 := kids (hdK (kR.drop 30)).1 (hdK (kR.drop 30)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c30_69 : anyK (node 0 6) (kid30.drop 69) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_64 : anyK (node 0 6) ((kid30.drop 64).take 5) = false := by decide +kernel
theorem c30_64 : anyK (node 0 6) (kid30.drop 64) = false := chainK _ _ 64 5 69 rfl t30_64 c30_69
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_56 : anyK (node 0 6) ((kid30.drop 56).take 8) = false := by decide +kernel
theorem c30_56 : anyK (node 0 6) (kid30.drop 56) = false := chainK _ _ 56 8 64 rfl t30_56 c30_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_48 : anyK (node 0 6) ((kid30.drop 48).take 8) = false := by decide +kernel
theorem c30_48 : anyK (node 0 6) (kid30.drop 48) = false := chainK _ _ 48 8 56 rfl t30_48 c30_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_40 : anyK (node 0 6) ((kid30.drop 40).take 8) = false := by decide +kernel
theorem c30_40 : anyK (node 0 6) (kid30.drop 40) = false := chainK _ _ 40 8 48 rfl t30_40 c30_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_32 : anyK (node 0 6) ((kid30.drop 32).take 8) = false := by decide +kernel
theorem c30_32 : anyK (node 0 6) (kid30.drop 32) = false := chainK _ _ 32 8 40 rfl t30_32 c30_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_24 : anyK (node 0 6) ((kid30.drop 24).take 8) = false := by decide +kernel
theorem c30_24 : anyK (node 0 6) (kid30.drop 24) = false := chainK _ _ 24 8 32 rfl t30_24 c30_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_16 : anyK (node 0 6) ((kid30.drop 16).take 8) = false := by decide +kernel
theorem c30_16 : anyK (node 0 6) (kid30.drop 16) = false := chainK _ _ 16 8 24 rfl t30_16 c30_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_8 : anyK (node 0 6) ((kid30.drop 8).take 8) = false := by decide +kernel
theorem c30_8 : anyK (node 0 6) (kid30.drop 8) = false := chainK _ _ 8 8 16 rfl t30_8 c30_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t30_0 : anyK (node 0 6) ((kid30.drop 0).take 8) = false := by decide +kernel
theorem c30_0 : anyK (node 0 6) (kid30.drop 0) = false := chainK _ _ 0 8 8 rfl t30_0 c30_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase30 : anyK (node 0 7) ((kR.drop 30).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid30 c30_0))
theorem rq30 : anyK (node 0 7) (kR.drop 30) = false := chainK _ _ 30 1 31 rfl rcase30 rq31
def kid29 := kids (hdK (kR.drop 29)).1 (hdK (kR.drop 29)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c29_56 : anyK (node 0 6) (kid29.drop 56) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_48 : anyK (node 0 6) ((kid29.drop 48).take 8) = false := by decide +kernel
theorem c29_48 : anyK (node 0 6) (kid29.drop 48) = false := chainK _ _ 48 8 56 rfl t29_48 c29_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_40 : anyK (node 0 6) ((kid29.drop 40).take 8) = false := by decide +kernel
theorem c29_40 : anyK (node 0 6) (kid29.drop 40) = false := chainK _ _ 40 8 48 rfl t29_40 c29_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_32 : anyK (node 0 6) ((kid29.drop 32).take 8) = false := by decide +kernel
theorem c29_32 : anyK (node 0 6) (kid29.drop 32) = false := chainK _ _ 32 8 40 rfl t29_32 c29_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_24 : anyK (node 0 6) ((kid29.drop 24).take 8) = false := by decide +kernel
theorem c29_24 : anyK (node 0 6) (kid29.drop 24) = false := chainK _ _ 24 8 32 rfl t29_24 c29_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_16 : anyK (node 0 6) ((kid29.drop 16).take 8) = false := by decide +kernel
theorem c29_16 : anyK (node 0 6) (kid29.drop 16) = false := chainK _ _ 16 8 24 rfl t29_16 c29_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_8 : anyK (node 0 6) ((kid29.drop 8).take 8) = false := by decide +kernel
theorem c29_8 : anyK (node 0 6) (kid29.drop 8) = false := chainK _ _ 8 8 16 rfl t29_8 c29_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t29_0 : anyK (node 0 6) ((kid29.drop 0).take 8) = false := by decide +kernel
theorem c29_0 : anyK (node 0 6) (kid29.drop 0) = false := chainK _ _ 0 8 8 rfl t29_0 c29_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase29 : anyK (node 0 7) ((kR.drop 29).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid29 c29_0))
theorem rq29 : anyK (node 0 7) (kR.drop 29) = false := chainK _ _ 29 1 30 rfl rcase29 rq30
def kid28 := kids (hdK (kR.drop 28)).1 (hdK (kR.drop 28)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c28_83 : anyK (node 0 6) (kid28.drop 83) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_80 : anyK (node 0 6) ((kid28.drop 80).take 3) = false := by decide +kernel
theorem c28_80 : anyK (node 0 6) (kid28.drop 80) = false := chainK _ _ 80 3 83 rfl t28_80 c28_83
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_72 : anyK (node 0 6) ((kid28.drop 72).take 8) = false := by decide +kernel
theorem c28_72 : anyK (node 0 6) (kid28.drop 72) = false := chainK _ _ 72 8 80 rfl t28_72 c28_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_64 : anyK (node 0 6) ((kid28.drop 64).take 8) = false := by decide +kernel
theorem c28_64 : anyK (node 0 6) (kid28.drop 64) = false := chainK _ _ 64 8 72 rfl t28_64 c28_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_56 : anyK (node 0 6) ((kid28.drop 56).take 8) = false := by decide +kernel
theorem c28_56 : anyK (node 0 6) (kid28.drop 56) = false := chainK _ _ 56 8 64 rfl t28_56 c28_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_48 : anyK (node 0 6) ((kid28.drop 48).take 8) = false := by decide +kernel
theorem c28_48 : anyK (node 0 6) (kid28.drop 48) = false := chainK _ _ 48 8 56 rfl t28_48 c28_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_40 : anyK (node 0 6) ((kid28.drop 40).take 8) = false := by decide +kernel
theorem c28_40 : anyK (node 0 6) (kid28.drop 40) = false := chainK _ _ 40 8 48 rfl t28_40 c28_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_32 : anyK (node 0 6) ((kid28.drop 32).take 8) = false := by decide +kernel
theorem c28_32 : anyK (node 0 6) (kid28.drop 32) = false := chainK _ _ 32 8 40 rfl t28_32 c28_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_24 : anyK (node 0 6) ((kid28.drop 24).take 8) = false := by decide +kernel
theorem c28_24 : anyK (node 0 6) (kid28.drop 24) = false := chainK _ _ 24 8 32 rfl t28_24 c28_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_16 : anyK (node 0 6) ((kid28.drop 16).take 8) = false := by decide +kernel
theorem c28_16 : anyK (node 0 6) (kid28.drop 16) = false := chainK _ _ 16 8 24 rfl t28_16 c28_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_8 : anyK (node 0 6) ((kid28.drop 8).take 8) = false := by decide +kernel
theorem c28_8 : anyK (node 0 6) (kid28.drop 8) = false := chainK _ _ 8 8 16 rfl t28_8 c28_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t28_0 : anyK (node 0 6) ((kid28.drop 0).take 8) = false := by decide +kernel
theorem c28_0 : anyK (node 0 6) (kid28.drop 0) = false := chainK _ _ 0 8 8 rfl t28_0 c28_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase28 : anyK (node 0 7) ((kR.drop 28).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid28 c28_0))
theorem rq28 : anyK (node 0 7) (kR.drop 28) = false := chainK _ _ 28 1 29 rfl rcase28 rq29
def kid27 := kids (hdK (kR.drop 27)).1 (hdK (kR.drop 27)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c27_55 : anyK (node 0 6) (kid27.drop 55) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_48 : anyK (node 0 6) ((kid27.drop 48).take 7) = false := by decide +kernel
theorem c27_48 : anyK (node 0 6) (kid27.drop 48) = false := chainK _ _ 48 7 55 rfl t27_48 c27_55
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_40 : anyK (node 0 6) ((kid27.drop 40).take 8) = false := by decide +kernel
theorem c27_40 : anyK (node 0 6) (kid27.drop 40) = false := chainK _ _ 40 8 48 rfl t27_40 c27_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_32 : anyK (node 0 6) ((kid27.drop 32).take 8) = false := by decide +kernel
theorem c27_32 : anyK (node 0 6) (kid27.drop 32) = false := chainK _ _ 32 8 40 rfl t27_32 c27_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_24 : anyK (node 0 6) ((kid27.drop 24).take 8) = false := by decide +kernel
theorem c27_24 : anyK (node 0 6) (kid27.drop 24) = false := chainK _ _ 24 8 32 rfl t27_24 c27_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_16 : anyK (node 0 6) ((kid27.drop 16).take 8) = false := by decide +kernel
theorem c27_16 : anyK (node 0 6) (kid27.drop 16) = false := chainK _ _ 16 8 24 rfl t27_16 c27_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_8 : anyK (node 0 6) ((kid27.drop 8).take 8) = false := by decide +kernel
theorem c27_8 : anyK (node 0 6) (kid27.drop 8) = false := chainK _ _ 8 8 16 rfl t27_8 c27_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t27_0 : anyK (node 0 6) ((kid27.drop 0).take 8) = false := by decide +kernel
theorem c27_0 : anyK (node 0 6) (kid27.drop 0) = false := chainK _ _ 0 8 8 rfl t27_0 c27_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase27 : anyK (node 0 7) ((kR.drop 27).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid27 c27_0))
theorem rq27 : anyK (node 0 7) (kR.drop 27) = false := chainK _ _ 27 1 28 rfl rcase27 rq28
def kid26 := kids (hdK (kR.drop 26)).1 (hdK (kR.drop 26)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c26_47 : anyK (node 0 6) (kid26.drop 47) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_40 : anyK (node 0 6) ((kid26.drop 40).take 7) = false := by decide +kernel
theorem c26_40 : anyK (node 0 6) (kid26.drop 40) = false := chainK _ _ 40 7 47 rfl t26_40 c26_47
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_32 : anyK (node 0 6) ((kid26.drop 32).take 8) = false := by decide +kernel
theorem c26_32 : anyK (node 0 6) (kid26.drop 32) = false := chainK _ _ 32 8 40 rfl t26_32 c26_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_24 : anyK (node 0 6) ((kid26.drop 24).take 8) = false := by decide +kernel
theorem c26_24 : anyK (node 0 6) (kid26.drop 24) = false := chainK _ _ 24 8 32 rfl t26_24 c26_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_16 : anyK (node 0 6) ((kid26.drop 16).take 8) = false := by decide +kernel
theorem c26_16 : anyK (node 0 6) (kid26.drop 16) = false := chainK _ _ 16 8 24 rfl t26_16 c26_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_8 : anyK (node 0 6) ((kid26.drop 8).take 8) = false := by decide +kernel
theorem c26_8 : anyK (node 0 6) (kid26.drop 8) = false := chainK _ _ 8 8 16 rfl t26_8 c26_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t26_0 : anyK (node 0 6) ((kid26.drop 0).take 8) = false := by decide +kernel
theorem c26_0 : anyK (node 0 6) (kid26.drop 0) = false := chainK _ _ 0 8 8 rfl t26_0 c26_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase26 : anyK (node 0 7) ((kR.drop 26).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid26 c26_0))
theorem rq26 : anyK (node 0 7) (kR.drop 26) = false := chainK _ _ 26 1 27 rfl rcase26 rq27
def kid25 := kids (hdK (kR.drop 25)).1 (hdK (kR.drop 25)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c25_41 : anyK (node 0 6) (kid25.drop 41) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_40 : anyK (node 0 6) ((kid25.drop 40).take 1) = false := by decide +kernel
theorem c25_40 : anyK (node 0 6) (kid25.drop 40) = false := chainK _ _ 40 1 41 rfl t25_40 c25_41
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_32 : anyK (node 0 6) ((kid25.drop 32).take 8) = false := by decide +kernel
theorem c25_32 : anyK (node 0 6) (kid25.drop 32) = false := chainK _ _ 32 8 40 rfl t25_32 c25_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_24 : anyK (node 0 6) ((kid25.drop 24).take 8) = false := by decide +kernel
theorem c25_24 : anyK (node 0 6) (kid25.drop 24) = false := chainK _ _ 24 8 32 rfl t25_24 c25_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_16 : anyK (node 0 6) ((kid25.drop 16).take 8) = false := by decide +kernel
theorem c25_16 : anyK (node 0 6) (kid25.drop 16) = false := chainK _ _ 16 8 24 rfl t25_16 c25_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_8 : anyK (node 0 6) ((kid25.drop 8).take 8) = false := by decide +kernel
theorem c25_8 : anyK (node 0 6) (kid25.drop 8) = false := chainK _ _ 8 8 16 rfl t25_8 c25_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t25_0 : anyK (node 0 6) ((kid25.drop 0).take 8) = false := by decide +kernel
theorem c25_0 : anyK (node 0 6) (kid25.drop 0) = false := chainK _ _ 0 8 8 rfl t25_0 c25_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase25 : anyK (node 0 7) ((kR.drop 25).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid25 c25_0))
theorem rq25 : anyK (node 0 7) (kR.drop 25) = false := chainK _ _ 25 1 26 rfl rcase25 rq26
def kid24 := kids (hdK (kR.drop 24)).1 (hdK (kR.drop 24)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24_79 : anyK (node 0 6) (kid24.drop 79) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_72 : anyK (node 0 6) ((kid24.drop 72).take 7) = false := by decide +kernel
theorem c24_72 : anyK (node 0 6) (kid24.drop 72) = false := chainK _ _ 72 7 79 rfl t24_72 c24_79
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_64 : anyK (node 0 6) ((kid24.drop 64).take 8) = false := by decide +kernel
theorem c24_64 : anyK (node 0 6) (kid24.drop 64) = false := chainK _ _ 64 8 72 rfl t24_64 c24_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_56 : anyK (node 0 6) ((kid24.drop 56).take 8) = false := by decide +kernel
theorem c24_56 : anyK (node 0 6) (kid24.drop 56) = false := chainK _ _ 56 8 64 rfl t24_56 c24_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_48 : anyK (node 0 6) ((kid24.drop 48).take 8) = false := by decide +kernel
theorem c24_48 : anyK (node 0 6) (kid24.drop 48) = false := chainK _ _ 48 8 56 rfl t24_48 c24_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_40 : anyK (node 0 6) ((kid24.drop 40).take 8) = false := by decide +kernel
theorem c24_40 : anyK (node 0 6) (kid24.drop 40) = false := chainK _ _ 40 8 48 rfl t24_40 c24_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_32 : anyK (node 0 6) ((kid24.drop 32).take 8) = false := by decide +kernel
theorem c24_32 : anyK (node 0 6) (kid24.drop 32) = false := chainK _ _ 32 8 40 rfl t24_32 c24_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_24 : anyK (node 0 6) ((kid24.drop 24).take 8) = false := by decide +kernel
theorem c24_24 : anyK (node 0 6) (kid24.drop 24) = false := chainK _ _ 24 8 32 rfl t24_24 c24_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_16 : anyK (node 0 6) ((kid24.drop 16).take 8) = false := by decide +kernel
theorem c24_16 : anyK (node 0 6) (kid24.drop 16) = false := chainK _ _ 16 8 24 rfl t24_16 c24_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_8 : anyK (node 0 6) ((kid24.drop 8).take 8) = false := by decide +kernel
theorem c24_8 : anyK (node 0 6) (kid24.drop 8) = false := chainK _ _ 8 8 16 rfl t24_8 c24_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t24_0 : anyK (node 0 6) ((kid24.drop 0).take 8) = false := by decide +kernel
theorem c24_0 : anyK (node 0 6) (kid24.drop 0) = false := chainK _ _ 0 8 8 rfl t24_0 c24_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase24 : anyK (node 0 7) ((kR.drop 24).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid24 c24_0))
theorem rq24 : anyK (node 0 7) (kR.drop 24) = false := chainK _ _ 24 1 25 rfl rcase24 rq25
def kid23 := kids (hdK (kR.drop 23)).1 (hdK (kR.drop 23)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c23_64 : anyK (node 0 6) (kid23.drop 64) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_56 : anyK (node 0 6) ((kid23.drop 56).take 8) = false := by decide +kernel
theorem c23_56 : anyK (node 0 6) (kid23.drop 56) = false := chainK _ _ 56 8 64 rfl t23_56 c23_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_48 : anyK (node 0 6) ((kid23.drop 48).take 8) = false := by decide +kernel
theorem c23_48 : anyK (node 0 6) (kid23.drop 48) = false := chainK _ _ 48 8 56 rfl t23_48 c23_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_40 : anyK (node 0 6) ((kid23.drop 40).take 8) = false := by decide +kernel
theorem c23_40 : anyK (node 0 6) (kid23.drop 40) = false := chainK _ _ 40 8 48 rfl t23_40 c23_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_32 : anyK (node 0 6) ((kid23.drop 32).take 8) = false := by decide +kernel
theorem c23_32 : anyK (node 0 6) (kid23.drop 32) = false := chainK _ _ 32 8 40 rfl t23_32 c23_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_24 : anyK (node 0 6) ((kid23.drop 24).take 8) = false := by decide +kernel
theorem c23_24 : anyK (node 0 6) (kid23.drop 24) = false := chainK _ _ 24 8 32 rfl t23_24 c23_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_16 : anyK (node 0 6) ((kid23.drop 16).take 8) = false := by decide +kernel
theorem c23_16 : anyK (node 0 6) (kid23.drop 16) = false := chainK _ _ 16 8 24 rfl t23_16 c23_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_8 : anyK (node 0 6) ((kid23.drop 8).take 8) = false := by decide +kernel
theorem c23_8 : anyK (node 0 6) (kid23.drop 8) = false := chainK _ _ 8 8 16 rfl t23_8 c23_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t23_0 : anyK (node 0 6) ((kid23.drop 0).take 8) = false := by decide +kernel
theorem c23_0 : anyK (node 0 6) (kid23.drop 0) = false := chainK _ _ 0 8 8 rfl t23_0 c23_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase23 : anyK (node 0 7) ((kR.drop 23).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid23 c23_0))
theorem rq23 : anyK (node 0 7) (kR.drop 23) = false := chainK _ _ 23 1 24 rfl rcase23 rq24
def kid22 := kids (hdK (kR.drop 22)).1 (hdK (kR.drop 22)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c22_49 : anyK (node 0 6) (kid22.drop 49) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_48 : anyK (node 0 6) ((kid22.drop 48).take 1) = false := by decide +kernel
theorem c22_48 : anyK (node 0 6) (kid22.drop 48) = false := chainK _ _ 48 1 49 rfl t22_48 c22_49
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_40 : anyK (node 0 6) ((kid22.drop 40).take 8) = false := by decide +kernel
theorem c22_40 : anyK (node 0 6) (kid22.drop 40) = false := chainK _ _ 40 8 48 rfl t22_40 c22_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_32 : anyK (node 0 6) ((kid22.drop 32).take 8) = false := by decide +kernel
theorem c22_32 : anyK (node 0 6) (kid22.drop 32) = false := chainK _ _ 32 8 40 rfl t22_32 c22_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_24 : anyK (node 0 6) ((kid22.drop 24).take 8) = false := by decide +kernel
theorem c22_24 : anyK (node 0 6) (kid22.drop 24) = false := chainK _ _ 24 8 32 rfl t22_24 c22_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_16 : anyK (node 0 6) ((kid22.drop 16).take 8) = false := by decide +kernel
theorem c22_16 : anyK (node 0 6) (kid22.drop 16) = false := chainK _ _ 16 8 24 rfl t22_16 c22_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_8 : anyK (node 0 6) ((kid22.drop 8).take 8) = false := by decide +kernel
theorem c22_8 : anyK (node 0 6) (kid22.drop 8) = false := chainK _ _ 8 8 16 rfl t22_8 c22_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t22_0 : anyK (node 0 6) ((kid22.drop 0).take 8) = false := by decide +kernel
theorem c22_0 : anyK (node 0 6) (kid22.drop 0) = false := chainK _ _ 0 8 8 rfl t22_0 c22_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase22 : anyK (node 0 7) ((kR.drop 22).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid22 c22_0))
theorem rq22 : anyK (node 0 7) (kR.drop 22) = false := chainK _ _ 22 1 23 rfl rcase22 rq23
def kid21 := kids (hdK (kR.drop 21)).1 (hdK (kR.drop 21)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c21_44 : anyK (node 0 6) (kid21.drop 44) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_40 : anyK (node 0 6) ((kid21.drop 40).take 4) = false := by decide +kernel
theorem c21_40 : anyK (node 0 6) (kid21.drop 40) = false := chainK _ _ 40 4 44 rfl t21_40 c21_44
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_32 : anyK (node 0 6) ((kid21.drop 32).take 8) = false := by decide +kernel
theorem c21_32 : anyK (node 0 6) (kid21.drop 32) = false := chainK _ _ 32 8 40 rfl t21_32 c21_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_24 : anyK (node 0 6) ((kid21.drop 24).take 8) = false := by decide +kernel
theorem c21_24 : anyK (node 0 6) (kid21.drop 24) = false := chainK _ _ 24 8 32 rfl t21_24 c21_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_16 : anyK (node 0 6) ((kid21.drop 16).take 8) = false := by decide +kernel
theorem c21_16 : anyK (node 0 6) (kid21.drop 16) = false := chainK _ _ 16 8 24 rfl t21_16 c21_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_8 : anyK (node 0 6) ((kid21.drop 8).take 8) = false := by decide +kernel
theorem c21_8 : anyK (node 0 6) (kid21.drop 8) = false := chainK _ _ 8 8 16 rfl t21_8 c21_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t21_0 : anyK (node 0 6) ((kid21.drop 0).take 8) = false := by decide +kernel
theorem c21_0 : anyK (node 0 6) (kid21.drop 0) = false := chainK _ _ 0 8 8 rfl t21_0 c21_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase21 : anyK (node 0 7) ((kR.drop 21).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid21 c21_0))
theorem rq21 : anyK (node 0 7) (kR.drop 21) = false := chainK _ _ 21 1 22 rfl rcase21 rq22
def kid20 := kids (hdK (kR.drop 20)).1 (hdK (kR.drop 20)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c20_72 : anyK (node 0 6) (kid20.drop 72) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_64 : anyK (node 0 6) ((kid20.drop 64).take 8) = false := by decide +kernel
theorem c20_64 : anyK (node 0 6) (kid20.drop 64) = false := chainK _ _ 64 8 72 rfl t20_64 c20_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_56 : anyK (node 0 6) ((kid20.drop 56).take 8) = false := by decide +kernel
theorem c20_56 : anyK (node 0 6) (kid20.drop 56) = false := chainK _ _ 56 8 64 rfl t20_56 c20_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_48 : anyK (node 0 6) ((kid20.drop 48).take 8) = false := by decide +kernel
theorem c20_48 : anyK (node 0 6) (kid20.drop 48) = false := chainK _ _ 48 8 56 rfl t20_48 c20_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_40 : anyK (node 0 6) ((kid20.drop 40).take 8) = false := by decide +kernel
theorem c20_40 : anyK (node 0 6) (kid20.drop 40) = false := chainK _ _ 40 8 48 rfl t20_40 c20_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_32 : anyK (node 0 6) ((kid20.drop 32).take 8) = false := by decide +kernel
theorem c20_32 : anyK (node 0 6) (kid20.drop 32) = false := chainK _ _ 32 8 40 rfl t20_32 c20_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_24 : anyK (node 0 6) ((kid20.drop 24).take 8) = false := by decide +kernel
theorem c20_24 : anyK (node 0 6) (kid20.drop 24) = false := chainK _ _ 24 8 32 rfl t20_24 c20_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_16 : anyK (node 0 6) ((kid20.drop 16).take 8) = false := by decide +kernel
theorem c20_16 : anyK (node 0 6) (kid20.drop 16) = false := chainK _ _ 16 8 24 rfl t20_16 c20_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_8 : anyK (node 0 6) ((kid20.drop 8).take 8) = false := by decide +kernel
theorem c20_8 : anyK (node 0 6) (kid20.drop 8) = false := chainK _ _ 8 8 16 rfl t20_8 c20_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t20_0 : anyK (node 0 6) ((kid20.drop 0).take 8) = false := by decide +kernel
theorem c20_0 : anyK (node 0 6) (kid20.drop 0) = false := chainK _ _ 0 8 8 rfl t20_0 c20_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase20 : anyK (node 0 7) ((kR.drop 20).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid20 c20_0))
theorem rq20 : anyK (node 0 7) (kR.drop 20) = false := chainK _ _ 20 1 21 rfl rcase20 rq21
def kid19 := kids (hdK (kR.drop 19)).1 (hdK (kR.drop 19)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c19_69 : anyK (node 0 6) (kid19.drop 69) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_64 : anyK (node 0 6) ((kid19.drop 64).take 5) = false := by decide +kernel
theorem c19_64 : anyK (node 0 6) (kid19.drop 64) = false := chainK _ _ 64 5 69 rfl t19_64 c19_69
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_56 : anyK (node 0 6) ((kid19.drop 56).take 8) = false := by decide +kernel
theorem c19_56 : anyK (node 0 6) (kid19.drop 56) = false := chainK _ _ 56 8 64 rfl t19_56 c19_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_48 : anyK (node 0 6) ((kid19.drop 48).take 8) = false := by decide +kernel
theorem c19_48 : anyK (node 0 6) (kid19.drop 48) = false := chainK _ _ 48 8 56 rfl t19_48 c19_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_40 : anyK (node 0 6) ((kid19.drop 40).take 8) = false := by decide +kernel
theorem c19_40 : anyK (node 0 6) (kid19.drop 40) = false := chainK _ _ 40 8 48 rfl t19_40 c19_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_32 : anyK (node 0 6) ((kid19.drop 32).take 8) = false := by decide +kernel
theorem c19_32 : anyK (node 0 6) (kid19.drop 32) = false := chainK _ _ 32 8 40 rfl t19_32 c19_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_24 : anyK (node 0 6) ((kid19.drop 24).take 8) = false := by decide +kernel
theorem c19_24 : anyK (node 0 6) (kid19.drop 24) = false := chainK _ _ 24 8 32 rfl t19_24 c19_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_16 : anyK (node 0 6) ((kid19.drop 16).take 8) = false := by decide +kernel
theorem c19_16 : anyK (node 0 6) (kid19.drop 16) = false := chainK _ _ 16 8 24 rfl t19_16 c19_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_8 : anyK (node 0 6) ((kid19.drop 8).take 8) = false := by decide +kernel
theorem c19_8 : anyK (node 0 6) (kid19.drop 8) = false := chainK _ _ 8 8 16 rfl t19_8 c19_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t19_0 : anyK (node 0 6) ((kid19.drop 0).take 8) = false := by decide +kernel
theorem c19_0 : anyK (node 0 6) (kid19.drop 0) = false := chainK _ _ 0 8 8 rfl t19_0 c19_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase19 : anyK (node 0 7) ((kR.drop 19).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid19 c19_0))
theorem rq19 : anyK (node 0 7) (kR.drop 19) = false := chainK _ _ 19 1 20 rfl rcase19 rq20
def kid18 := kids (hdK (kR.drop 18)).1 (hdK (kR.drop 18)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c18_50 : anyK (node 0 6) (kid18.drop 50) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_48 : anyK (node 0 6) ((kid18.drop 48).take 2) = false := by decide +kernel
theorem c18_48 : anyK (node 0 6) (kid18.drop 48) = false := chainK _ _ 48 2 50 rfl t18_48 c18_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_40 : anyK (node 0 6) ((kid18.drop 40).take 8) = false := by decide +kernel
theorem c18_40 : anyK (node 0 6) (kid18.drop 40) = false := chainK _ _ 40 8 48 rfl t18_40 c18_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_32 : anyK (node 0 6) ((kid18.drop 32).take 8) = false := by decide +kernel
theorem c18_32 : anyK (node 0 6) (kid18.drop 32) = false := chainK _ _ 32 8 40 rfl t18_32 c18_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_24 : anyK (node 0 6) ((kid18.drop 24).take 8) = false := by decide +kernel
theorem c18_24 : anyK (node 0 6) (kid18.drop 24) = false := chainK _ _ 24 8 32 rfl t18_24 c18_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_16 : anyK (node 0 6) ((kid18.drop 16).take 8) = false := by decide +kernel
theorem c18_16 : anyK (node 0 6) (kid18.drop 16) = false := chainK _ _ 16 8 24 rfl t18_16 c18_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_8 : anyK (node 0 6) ((kid18.drop 8).take 8) = false := by decide +kernel
theorem c18_8 : anyK (node 0 6) (kid18.drop 8) = false := chainK _ _ 8 8 16 rfl t18_8 c18_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t18_0 : anyK (node 0 6) ((kid18.drop 0).take 8) = false := by decide +kernel
theorem c18_0 : anyK (node 0 6) (kid18.drop 0) = false := chainK _ _ 0 8 8 rfl t18_0 c18_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase18 : anyK (node 0 7) ((kR.drop 18).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid18 c18_0))
theorem rq18 : anyK (node 0 7) (kR.drop 18) = false := chainK _ _ 18 1 19 rfl rcase18 rq19
def kid17 := kids (hdK (kR.drop 17)).1 (hdK (kR.drop 17)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17_43 : anyK (node 0 6) (kid17.drop 43) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_40 : anyK (node 0 6) ((kid17.drop 40).take 3) = false := by decide +kernel
theorem c17_40 : anyK (node 0 6) (kid17.drop 40) = false := chainK _ _ 40 3 43 rfl t17_40 c17_43
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_32 : anyK (node 0 6) ((kid17.drop 32).take 8) = false := by decide +kernel
theorem c17_32 : anyK (node 0 6) (kid17.drop 32) = false := chainK _ _ 32 8 40 rfl t17_32 c17_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_24 : anyK (node 0 6) ((kid17.drop 24).take 8) = false := by decide +kernel
theorem c17_24 : anyK (node 0 6) (kid17.drop 24) = false := chainK _ _ 24 8 32 rfl t17_24 c17_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_16 : anyK (node 0 6) ((kid17.drop 16).take 8) = false := by decide +kernel
theorem c17_16 : anyK (node 0 6) (kid17.drop 16) = false := chainK _ _ 16 8 24 rfl t17_16 c17_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_8 : anyK (node 0 6) ((kid17.drop 8).take 8) = false := by decide +kernel
theorem c17_8 : anyK (node 0 6) (kid17.drop 8) = false := chainK _ _ 8 8 16 rfl t17_8 c17_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t17_0 : anyK (node 0 6) ((kid17.drop 0).take 8) = false := by decide +kernel
theorem c17_0 : anyK (node 0 6) (kid17.drop 0) = false := chainK _ _ 0 8 8 rfl t17_0 c17_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase17 : anyK (node 0 7) ((kR.drop 17).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid17 c17_0))
theorem rq17 : anyK (node 0 7) (kR.drop 17) = false := chainK _ _ 17 1 18 rfl rcase17 rq18
def kid16 := kids (hdK (kR.drop 16)).1 (hdK (kR.drop 16)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_82 : anyK (node 0 6) (kid16.drop 82) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_80 : anyK (node 0 6) ((kid16.drop 80).take 2) = false := by decide +kernel
theorem c16_80 : anyK (node 0 6) (kid16.drop 80) = false := chainK _ _ 80 2 82 rfl t16_80 c16_82
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_72 : anyK (node 0 6) ((kid16.drop 72).take 8) = false := by decide +kernel
theorem c16_72 : anyK (node 0 6) (kid16.drop 72) = false := chainK _ _ 72 8 80 rfl t16_72 c16_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_64 : anyK (node 0 6) ((kid16.drop 64).take 8) = false := by decide +kernel
theorem c16_64 : anyK (node 0 6) (kid16.drop 64) = false := chainK _ _ 64 8 72 rfl t16_64 c16_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_56 : anyK (node 0 6) ((kid16.drop 56).take 8) = false := by decide +kernel
theorem c16_56 : anyK (node 0 6) (kid16.drop 56) = false := chainK _ _ 56 8 64 rfl t16_56 c16_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_48 : anyK (node 0 6) ((kid16.drop 48).take 8) = false := by decide +kernel
theorem c16_48 : anyK (node 0 6) (kid16.drop 48) = false := chainK _ _ 48 8 56 rfl t16_48 c16_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_40 : anyK (node 0 6) ((kid16.drop 40).take 8) = false := by decide +kernel
theorem c16_40 : anyK (node 0 6) (kid16.drop 40) = false := chainK _ _ 40 8 48 rfl t16_40 c16_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_32 : anyK (node 0 6) ((kid16.drop 32).take 8) = false := by decide +kernel
theorem c16_32 : anyK (node 0 6) (kid16.drop 32) = false := chainK _ _ 32 8 40 rfl t16_32 c16_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_24 : anyK (node 0 6) ((kid16.drop 24).take 8) = false := by decide +kernel
theorem c16_24 : anyK (node 0 6) (kid16.drop 24) = false := chainK _ _ 24 8 32 rfl t16_24 c16_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_16 : anyK (node 0 6) ((kid16.drop 16).take 8) = false := by decide +kernel
theorem c16_16 : anyK (node 0 6) (kid16.drop 16) = false := chainK _ _ 16 8 24 rfl t16_16 c16_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_8 : anyK (node 0 6) ((kid16.drop 8).take 8) = false := by decide +kernel
theorem c16_8 : anyK (node 0 6) (kid16.drop 8) = false := chainK _ _ 8 8 16 rfl t16_8 c16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t16_0 : anyK (node 0 6) ((kid16.drop 0).take 8) = false := by decide +kernel
theorem c16_0 : anyK (node 0 6) (kid16.drop 0) = false := chainK _ _ 0 8 8 rfl t16_0 c16_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase16 : anyK (node 0 7) ((kR.drop 16).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid16 c16_0))
theorem rq16 : anyK (node 0 7) (kR.drop 16) = false := chainK _ _ 16 1 17 rfl rcase16 rq17
def kid15 := kids (hdK (kR.drop 15)).1 (hdK (kR.drop 15)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c15_73 : anyK (node 0 6) (kid15.drop 73) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_72 : anyK (node 0 6) ((kid15.drop 72).take 1) = false := by decide +kernel
theorem c15_72 : anyK (node 0 6) (kid15.drop 72) = false := chainK _ _ 72 1 73 rfl t15_72 c15_73
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_64 : anyK (node 0 6) ((kid15.drop 64).take 8) = false := by decide +kernel
theorem c15_64 : anyK (node 0 6) (kid15.drop 64) = false := chainK _ _ 64 8 72 rfl t15_64 c15_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_56 : anyK (node 0 6) ((kid15.drop 56).take 8) = false := by decide +kernel
theorem c15_56 : anyK (node 0 6) (kid15.drop 56) = false := chainK _ _ 56 8 64 rfl t15_56 c15_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_48 : anyK (node 0 6) ((kid15.drop 48).take 8) = false := by decide +kernel
theorem c15_48 : anyK (node 0 6) (kid15.drop 48) = false := chainK _ _ 48 8 56 rfl t15_48 c15_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_40 : anyK (node 0 6) ((kid15.drop 40).take 8) = false := by decide +kernel
theorem c15_40 : anyK (node 0 6) (kid15.drop 40) = false := chainK _ _ 40 8 48 rfl t15_40 c15_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_32 : anyK (node 0 6) ((kid15.drop 32).take 8) = false := by decide +kernel
theorem c15_32 : anyK (node 0 6) (kid15.drop 32) = false := chainK _ _ 32 8 40 rfl t15_32 c15_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_24 : anyK (node 0 6) ((kid15.drop 24).take 8) = false := by decide +kernel
theorem c15_24 : anyK (node 0 6) (kid15.drop 24) = false := chainK _ _ 24 8 32 rfl t15_24 c15_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_16 : anyK (node 0 6) ((kid15.drop 16).take 8) = false := by decide +kernel
theorem c15_16 : anyK (node 0 6) (kid15.drop 16) = false := chainK _ _ 16 8 24 rfl t15_16 c15_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_8 : anyK (node 0 6) ((kid15.drop 8).take 8) = false := by decide +kernel
theorem c15_8 : anyK (node 0 6) (kid15.drop 8) = false := chainK _ _ 8 8 16 rfl t15_8 c15_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t15_0 : anyK (node 0 6) ((kid15.drop 0).take 8) = false := by decide +kernel
theorem c15_0 : anyK (node 0 6) (kid15.drop 0) = false := chainK _ _ 0 8 8 rfl t15_0 c15_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase15 : anyK (node 0 7) ((kR.drop 15).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid15 c15_0))
theorem rq15 : anyK (node 0 7) (kR.drop 15) = false := chainK _ _ 15 1 16 rfl rcase15 rq16
def kid14 := kids (hdK (kR.drop 14)).1 (hdK (kR.drop 14)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c14_41 : anyK (node 0 6) (kid14.drop 41) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_40 : anyK (node 0 6) ((kid14.drop 40).take 1) = false := by decide +kernel
theorem c14_40 : anyK (node 0 6) (kid14.drop 40) = false := chainK _ _ 40 1 41 rfl t14_40 c14_41
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_32 : anyK (node 0 6) ((kid14.drop 32).take 8) = false := by decide +kernel
theorem c14_32 : anyK (node 0 6) (kid14.drop 32) = false := chainK _ _ 32 8 40 rfl t14_32 c14_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_24 : anyK (node 0 6) ((kid14.drop 24).take 8) = false := by decide +kernel
theorem c14_24 : anyK (node 0 6) (kid14.drop 24) = false := chainK _ _ 24 8 32 rfl t14_24 c14_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_16 : anyK (node 0 6) ((kid14.drop 16).take 8) = false := by decide +kernel
theorem c14_16 : anyK (node 0 6) (kid14.drop 16) = false := chainK _ _ 16 8 24 rfl t14_16 c14_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_8 : anyK (node 0 6) ((kid14.drop 8).take 8) = false := by decide +kernel
theorem c14_8 : anyK (node 0 6) (kid14.drop 8) = false := chainK _ _ 8 8 16 rfl t14_8 c14_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t14_0 : anyK (node 0 6) ((kid14.drop 0).take 8) = false := by decide +kernel
theorem c14_0 : anyK (node 0 6) (kid14.drop 0) = false := chainK _ _ 0 8 8 rfl t14_0 c14_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase14 : anyK (node 0 7) ((kR.drop 14).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid14 c14_0))
theorem rq14 : anyK (node 0 7) (kR.drop 14) = false := chainK _ _ 14 1 15 rfl rcase14 rq15
def kid13 := kids (hdK (kR.drop 13)).1 (hdK (kR.drop 13)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c13_36 : anyK (node 0 6) (kid13.drop 36) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_32 : anyK (node 0 6) ((kid13.drop 32).take 4) = false := by decide +kernel
theorem c13_32 : anyK (node 0 6) (kid13.drop 32) = false := chainK _ _ 32 4 36 rfl t13_32 c13_36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_24 : anyK (node 0 6) ((kid13.drop 24).take 8) = false := by decide +kernel
theorem c13_24 : anyK (node 0 6) (kid13.drop 24) = false := chainK _ _ 24 8 32 rfl t13_24 c13_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_16 : anyK (node 0 6) ((kid13.drop 16).take 8) = false := by decide +kernel
theorem c13_16 : anyK (node 0 6) (kid13.drop 16) = false := chainK _ _ 16 8 24 rfl t13_16 c13_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_8 : anyK (node 0 6) ((kid13.drop 8).take 8) = false := by decide +kernel
theorem c13_8 : anyK (node 0 6) (kid13.drop 8) = false := chainK _ _ 8 8 16 rfl t13_8 c13_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t13_0 : anyK (node 0 6) ((kid13.drop 0).take 8) = false := by decide +kernel
theorem c13_0 : anyK (node 0 6) (kid13.drop 0) = false := chainK _ _ 0 8 8 rfl t13_0 c13_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase13 : anyK (node 0 7) ((kR.drop 13).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid13 c13_0))
theorem rq13 : anyK (node 0 7) (kR.drop 13) = false := chainK _ _ 13 1 14 rfl rcase13 rq14
def kid12 := kids (hdK (kR.drop 12)).1 (hdK (kR.drop 12)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c12_60 : anyK (node 0 6) (kid12.drop 60) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_56 : anyK (node 0 6) ((kid12.drop 56).take 4) = false := by decide +kernel
theorem c12_56 : anyK (node 0 6) (kid12.drop 56) = false := chainK _ _ 56 4 60 rfl t12_56 c12_60
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_48 : anyK (node 0 6) ((kid12.drop 48).take 8) = false := by decide +kernel
theorem c12_48 : anyK (node 0 6) (kid12.drop 48) = false := chainK _ _ 48 8 56 rfl t12_48 c12_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_40 : anyK (node 0 6) ((kid12.drop 40).take 8) = false := by decide +kernel
theorem c12_40 : anyK (node 0 6) (kid12.drop 40) = false := chainK _ _ 40 8 48 rfl t12_40 c12_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_32 : anyK (node 0 6) ((kid12.drop 32).take 8) = false := by decide +kernel
theorem c12_32 : anyK (node 0 6) (kid12.drop 32) = false := chainK _ _ 32 8 40 rfl t12_32 c12_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_24 : anyK (node 0 6) ((kid12.drop 24).take 8) = false := by decide +kernel
theorem c12_24 : anyK (node 0 6) (kid12.drop 24) = false := chainK _ _ 24 8 32 rfl t12_24 c12_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_16 : anyK (node 0 6) ((kid12.drop 16).take 8) = false := by decide +kernel
theorem c12_16 : anyK (node 0 6) (kid12.drop 16) = false := chainK _ _ 16 8 24 rfl t12_16 c12_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_8 : anyK (node 0 6) ((kid12.drop 8).take 8) = false := by decide +kernel
theorem c12_8 : anyK (node 0 6) (kid12.drop 8) = false := chainK _ _ 8 8 16 rfl t12_8 c12_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t12_0 : anyK (node 0 6) ((kid12.drop 0).take 8) = false := by decide +kernel
theorem c12_0 : anyK (node 0 6) (kid12.drop 0) = false := chainK _ _ 0 8 8 rfl t12_0 c12_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase12 : anyK (node 0 7) ((kR.drop 12).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid12 c12_0))
theorem rq12 : anyK (node 0 7) (kR.drop 12) = false := chainK _ _ 12 1 13 rfl rcase12 rq13
def kid11 := kids (hdK (kR.drop 11)).1 (hdK (kR.drop 11)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c11_64 : anyK (node 0 6) (kid11.drop 64) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_56 : anyK (node 0 6) ((kid11.drop 56).take 8) = false := by decide +kernel
theorem c11_56 : anyK (node 0 6) (kid11.drop 56) = false := chainK _ _ 56 8 64 rfl t11_56 c11_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_48 : anyK (node 0 6) ((kid11.drop 48).take 8) = false := by decide +kernel
theorem c11_48 : anyK (node 0 6) (kid11.drop 48) = false := chainK _ _ 48 8 56 rfl t11_48 c11_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_40 : anyK (node 0 6) ((kid11.drop 40).take 8) = false := by decide +kernel
theorem c11_40 : anyK (node 0 6) (kid11.drop 40) = false := chainK _ _ 40 8 48 rfl t11_40 c11_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_32 : anyK (node 0 6) ((kid11.drop 32).take 8) = false := by decide +kernel
theorem c11_32 : anyK (node 0 6) (kid11.drop 32) = false := chainK _ _ 32 8 40 rfl t11_32 c11_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_24 : anyK (node 0 6) ((kid11.drop 24).take 8) = false := by decide +kernel
theorem c11_24 : anyK (node 0 6) (kid11.drop 24) = false := chainK _ _ 24 8 32 rfl t11_24 c11_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_16 : anyK (node 0 6) ((kid11.drop 16).take 8) = false := by decide +kernel
theorem c11_16 : anyK (node 0 6) (kid11.drop 16) = false := chainK _ _ 16 8 24 rfl t11_16 c11_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_8 : anyK (node 0 6) ((kid11.drop 8).take 8) = false := by decide +kernel
theorem c11_8 : anyK (node 0 6) (kid11.drop 8) = false := chainK _ _ 8 8 16 rfl t11_8 c11_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t11_0 : anyK (node 0 6) ((kid11.drop 0).take 8) = false := by decide +kernel
theorem c11_0 : anyK (node 0 6) (kid11.drop 0) = false := chainK _ _ 0 8 8 rfl t11_0 c11_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase11 : anyK (node 0 7) ((kR.drop 11).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid11 c11_0))
theorem rq11 : anyK (node 0 7) (kR.drop 11) = false := chainK _ _ 11 1 12 rfl rcase11 rq12
def kid10 := kids (hdK (kR.drop 10)).1 (hdK (kR.drop 10)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c10_40 : anyK (node 0 6) (kid10.drop 40) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_32 : anyK (node 0 6) ((kid10.drop 32).take 8) = false := by decide +kernel
theorem c10_32 : anyK (node 0 6) (kid10.drop 32) = false := chainK _ _ 32 8 40 rfl t10_32 c10_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_24 : anyK (node 0 6) ((kid10.drop 24).take 8) = false := by decide +kernel
theorem c10_24 : anyK (node 0 6) (kid10.drop 24) = false := chainK _ _ 24 8 32 rfl t10_24 c10_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_16 : anyK (node 0 6) ((kid10.drop 16).take 8) = false := by decide +kernel
theorem c10_16 : anyK (node 0 6) (kid10.drop 16) = false := chainK _ _ 16 8 24 rfl t10_16 c10_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_8 : anyK (node 0 6) ((kid10.drop 8).take 8) = false := by decide +kernel
theorem c10_8 : anyK (node 0 6) (kid10.drop 8) = false := chainK _ _ 8 8 16 rfl t10_8 c10_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t10_0 : anyK (node 0 6) ((kid10.drop 0).take 8) = false := by decide +kernel
theorem c10_0 : anyK (node 0 6) (kid10.drop 0) = false := chainK _ _ 0 8 8 rfl t10_0 c10_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase10 : anyK (node 0 7) ((kR.drop 10).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid10 c10_0))
theorem rq10 : anyK (node 0 7) (kR.drop 10) = false := chainK _ _ 10 1 11 rfl rcase10 rq11
def kid9 := kids (hdK (kR.drop 9)).1 (hdK (kR.drop 9)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c9_34 : anyK (node 0 6) (kid9.drop 34) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_32 : anyK (node 0 6) ((kid9.drop 32).take 2) = false := by decide +kernel
theorem c9_32 : anyK (node 0 6) (kid9.drop 32) = false := chainK _ _ 32 2 34 rfl t9_32 c9_34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_24 : anyK (node 0 6) ((kid9.drop 24).take 8) = false := by decide +kernel
theorem c9_24 : anyK (node 0 6) (kid9.drop 24) = false := chainK _ _ 24 8 32 rfl t9_24 c9_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_16 : anyK (node 0 6) ((kid9.drop 16).take 8) = false := by decide +kernel
theorem c9_16 : anyK (node 0 6) (kid9.drop 16) = false := chainK _ _ 16 8 24 rfl t9_16 c9_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_8 : anyK (node 0 6) ((kid9.drop 8).take 8) = false := by decide +kernel
theorem c9_8 : anyK (node 0 6) (kid9.drop 8) = false := chainK _ _ 8 8 16 rfl t9_8 c9_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t9_0 : anyK (node 0 6) ((kid9.drop 0).take 8) = false := by decide +kernel
theorem c9_0 : anyK (node 0 6) (kid9.drop 0) = false := chainK _ _ 0 8 8 rfl t9_0 c9_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase9 : anyK (node 0 7) ((kR.drop 9).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid9 c9_0))
theorem rq9 : anyK (node 0 7) (kR.drop 9) = false := chainK _ _ 9 1 10 rfl rcase9 rq10
def kid8 := kids (hdK (kR.drop 8)).1 (hdK (kR.drop 8)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c8_86 : anyK (node 0 6) (kid8.drop 86) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_80 : anyK (node 0 6) ((kid8.drop 80).take 6) = false := by decide +kernel
theorem c8_80 : anyK (node 0 6) (kid8.drop 80) = false := chainK _ _ 80 6 86 rfl t8_80 c8_86
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_72 : anyK (node 0 6) ((kid8.drop 72).take 8) = false := by decide +kernel
theorem c8_72 : anyK (node 0 6) (kid8.drop 72) = false := chainK _ _ 72 8 80 rfl t8_72 c8_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_64 : anyK (node 0 6) ((kid8.drop 64).take 8) = false := by decide +kernel
theorem c8_64 : anyK (node 0 6) (kid8.drop 64) = false := chainK _ _ 64 8 72 rfl t8_64 c8_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_56 : anyK (node 0 6) ((kid8.drop 56).take 8) = false := by decide +kernel
theorem c8_56 : anyK (node 0 6) (kid8.drop 56) = false := chainK _ _ 56 8 64 rfl t8_56 c8_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_48 : anyK (node 0 6) ((kid8.drop 48).take 8) = false := by decide +kernel
theorem c8_48 : anyK (node 0 6) (kid8.drop 48) = false := chainK _ _ 48 8 56 rfl t8_48 c8_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_40 : anyK (node 0 6) ((kid8.drop 40).take 8) = false := by decide +kernel
theorem c8_40 : anyK (node 0 6) (kid8.drop 40) = false := chainK _ _ 40 8 48 rfl t8_40 c8_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_32 : anyK (node 0 6) ((kid8.drop 32).take 8) = false := by decide +kernel
theorem c8_32 : anyK (node 0 6) (kid8.drop 32) = false := chainK _ _ 32 8 40 rfl t8_32 c8_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_24 : anyK (node 0 6) ((kid8.drop 24).take 8) = false := by decide +kernel
theorem c8_24 : anyK (node 0 6) (kid8.drop 24) = false := chainK _ _ 24 8 32 rfl t8_24 c8_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_16 : anyK (node 0 6) ((kid8.drop 16).take 8) = false := by decide +kernel
theorem c8_16 : anyK (node 0 6) (kid8.drop 16) = false := chainK _ _ 16 8 24 rfl t8_16 c8_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_8 : anyK (node 0 6) ((kid8.drop 8).take 8) = false := by decide +kernel
theorem c8_8 : anyK (node 0 6) (kid8.drop 8) = false := chainK _ _ 8 8 16 rfl t8_8 c8_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t8_0 : anyK (node 0 6) ((kid8.drop 0).take 8) = false := by decide +kernel
theorem c8_0 : anyK (node 0 6) (kid8.drop 0) = false := chainK _ _ 0 8 8 rfl t8_0 c8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase8 : anyK (node 0 7) ((kR.drop 8).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid8 c8_0))
theorem rq8 : anyK (node 0 7) (kR.drop 8) = false := chainK _ _ 8 1 9 rfl rcase8 rq9
def kid7 := kids (hdK (kR.drop 7)).1 (hdK (kR.drop 7)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c7_64 : anyK (node 0 6) (kid7.drop 64) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_56 : anyK (node 0 6) ((kid7.drop 56).take 8) = false := by decide +kernel
theorem c7_56 : anyK (node 0 6) (kid7.drop 56) = false := chainK _ _ 56 8 64 rfl t7_56 c7_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_48 : anyK (node 0 6) ((kid7.drop 48).take 8) = false := by decide +kernel
theorem c7_48 : anyK (node 0 6) (kid7.drop 48) = false := chainK _ _ 48 8 56 rfl t7_48 c7_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_40 : anyK (node 0 6) ((kid7.drop 40).take 8) = false := by decide +kernel
theorem c7_40 : anyK (node 0 6) (kid7.drop 40) = false := chainK _ _ 40 8 48 rfl t7_40 c7_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_32 : anyK (node 0 6) ((kid7.drop 32).take 8) = false := by decide +kernel
theorem c7_32 : anyK (node 0 6) (kid7.drop 32) = false := chainK _ _ 32 8 40 rfl t7_32 c7_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_24 : anyK (node 0 6) ((kid7.drop 24).take 8) = false := by decide +kernel
theorem c7_24 : anyK (node 0 6) (kid7.drop 24) = false := chainK _ _ 24 8 32 rfl t7_24 c7_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_16 : anyK (node 0 6) ((kid7.drop 16).take 8) = false := by decide +kernel
theorem c7_16 : anyK (node 0 6) (kid7.drop 16) = false := chainK _ _ 16 8 24 rfl t7_16 c7_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_8 : anyK (node 0 6) ((kid7.drop 8).take 8) = false := by decide +kernel
theorem c7_8 : anyK (node 0 6) (kid7.drop 8) = false := chainK _ _ 8 8 16 rfl t7_8 c7_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t7_0 : anyK (node 0 6) ((kid7.drop 0).take 8) = false := by decide +kernel
theorem c7_0 : anyK (node 0 6) (kid7.drop 0) = false := chainK _ _ 0 8 8 rfl t7_0 c7_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase7 : anyK (node 0 7) ((kR.drop 7).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid7 c7_0))
theorem rq7 : anyK (node 0 7) (kR.drop 7) = false := chainK _ _ 7 1 8 rfl rcase7 rq8
def kid6 := kids (hdK (kR.drop 6)).1 (hdK (kR.drop 6)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c6_39 : anyK (node 0 6) (kid6.drop 39) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_32 : anyK (node 0 6) ((kid6.drop 32).take 7) = false := by decide +kernel
theorem c6_32 : anyK (node 0 6) (kid6.drop 32) = false := chainK _ _ 32 7 39 rfl t6_32 c6_39
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_24 : anyK (node 0 6) ((kid6.drop 24).take 8) = false := by decide +kernel
theorem c6_24 : anyK (node 0 6) (kid6.drop 24) = false := chainK _ _ 24 8 32 rfl t6_24 c6_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_16 : anyK (node 0 6) ((kid6.drop 16).take 8) = false := by decide +kernel
theorem c6_16 : anyK (node 0 6) (kid6.drop 16) = false := chainK _ _ 16 8 24 rfl t6_16 c6_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_8 : anyK (node 0 6) ((kid6.drop 8).take 8) = false := by decide +kernel
theorem c6_8 : anyK (node 0 6) (kid6.drop 8) = false := chainK _ _ 8 8 16 rfl t6_8 c6_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t6_0 : anyK (node 0 6) ((kid6.drop 0).take 8) = false := by decide +kernel
theorem c6_0 : anyK (node 0 6) (kid6.drop 0) = false := chainK _ _ 0 8 8 rfl t6_0 c6_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase6 : anyK (node 0 7) ((kR.drop 6).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid6 c6_0))
theorem rq6 : anyK (node 0 7) (kR.drop 6) = false := chainK _ _ 6 1 7 rfl rcase6 rq7
def kid5 := kids (hdK (kR.drop 5)).1 (hdK (kR.drop 5)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_47 : anyK (node 0 6) (kid5.drop 47) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_40 : anyK (node 0 6) ((kid5.drop 40).take 7) = false := by decide +kernel
theorem c5_40 : anyK (node 0 6) (kid5.drop 40) = false := chainK _ _ 40 7 47 rfl t5_40 c5_47
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_32 : anyK (node 0 6) ((kid5.drop 32).take 8) = false := by decide +kernel
theorem c5_32 : anyK (node 0 6) (kid5.drop 32) = false := chainK _ _ 32 8 40 rfl t5_32 c5_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_24 : anyK (node 0 6) ((kid5.drop 24).take 8) = false := by decide +kernel
theorem c5_24 : anyK (node 0 6) (kid5.drop 24) = false := chainK _ _ 24 8 32 rfl t5_24 c5_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_16 : anyK (node 0 6) ((kid5.drop 16).take 8) = false := by decide +kernel
theorem c5_16 : anyK (node 0 6) (kid5.drop 16) = false := chainK _ _ 16 8 24 rfl t5_16 c5_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_8 : anyK (node 0 6) ((kid5.drop 8).take 8) = false := by decide +kernel
theorem c5_8 : anyK (node 0 6) (kid5.drop 8) = false := chainK _ _ 8 8 16 rfl t5_8 c5_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t5_0 : anyK (node 0 6) ((kid5.drop 0).take 8) = false := by decide +kernel
theorem c5_0 : anyK (node 0 6) (kid5.drop 0) = false := chainK _ _ 0 8 8 rfl t5_0 c5_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase5 : anyK (node 0 7) ((kR.drop 5).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid5 c5_0))
theorem rq5 : anyK (node 0 7) (kR.drop 5) = false := chainK _ _ 5 1 6 rfl rcase5 rq6
def kid4 := kids (hdK (kR.drop 4)).1 (hdK (kR.drop 4)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4_81 : anyK (node 0 6) (kid4.drop 81) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_80 : anyK (node 0 6) ((kid4.drop 80).take 1) = false := by decide +kernel
theorem c4_80 : anyK (node 0 6) (kid4.drop 80) = false := chainK _ _ 80 1 81 rfl t4_80 c4_81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_72 : anyK (node 0 6) ((kid4.drop 72).take 8) = false := by decide +kernel
theorem c4_72 : anyK (node 0 6) (kid4.drop 72) = false := chainK _ _ 72 8 80 rfl t4_72 c4_80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_64 : anyK (node 0 6) ((kid4.drop 64).take 8) = false := by decide +kernel
theorem c4_64 : anyK (node 0 6) (kid4.drop 64) = false := chainK _ _ 64 8 72 rfl t4_64 c4_72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_56 : anyK (node 0 6) ((kid4.drop 56).take 8) = false := by decide +kernel
theorem c4_56 : anyK (node 0 6) (kid4.drop 56) = false := chainK _ _ 56 8 64 rfl t4_56 c4_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_48 : anyK (node 0 6) ((kid4.drop 48).take 8) = false := by decide +kernel
theorem c4_48 : anyK (node 0 6) (kid4.drop 48) = false := chainK _ _ 48 8 56 rfl t4_48 c4_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_40 : anyK (node 0 6) ((kid4.drop 40).take 8) = false := by decide +kernel
theorem c4_40 : anyK (node 0 6) (kid4.drop 40) = false := chainK _ _ 40 8 48 rfl t4_40 c4_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_32 : anyK (node 0 6) ((kid4.drop 32).take 8) = false := by decide +kernel
theorem c4_32 : anyK (node 0 6) (kid4.drop 32) = false := chainK _ _ 32 8 40 rfl t4_32 c4_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_24 : anyK (node 0 6) ((kid4.drop 24).take 8) = false := by decide +kernel
theorem c4_24 : anyK (node 0 6) (kid4.drop 24) = false := chainK _ _ 24 8 32 rfl t4_24 c4_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_16 : anyK (node 0 6) ((kid4.drop 16).take 8) = false := by decide +kernel
theorem c4_16 : anyK (node 0 6) (kid4.drop 16) = false := chainK _ _ 16 8 24 rfl t4_16 c4_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_8 : anyK (node 0 6) ((kid4.drop 8).take 8) = false := by decide +kernel
theorem c4_8 : anyK (node 0 6) (kid4.drop 8) = false := chainK _ _ 8 8 16 rfl t4_8 c4_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t4_0 : anyK (node 0 6) ((kid4.drop 0).take 8) = false := by decide +kernel
theorem c4_0 : anyK (node 0 6) (kid4.drop 0) = false := chainK _ _ 0 8 8 rfl t4_0 c4_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase4 : anyK (node 0 7) ((kR.drop 4).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid4 c4_0))
theorem rq4 : anyK (node 0 7) (kR.drop 4) = false := chainK _ _ 4 1 5 rfl rcase4 rq5
def kid3 := kids (hdK (kR.drop 3)).1 (hdK (kR.drop 3)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3_71 : anyK (node 0 6) (kid3.drop 71) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_64 : anyK (node 0 6) ((kid3.drop 64).take 7) = false := by decide +kernel
theorem c3_64 : anyK (node 0 6) (kid3.drop 64) = false := chainK _ _ 64 7 71 rfl t3_64 c3_71
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_56 : anyK (node 0 6) ((kid3.drop 56).take 8) = false := by decide +kernel
theorem c3_56 : anyK (node 0 6) (kid3.drop 56) = false := chainK _ _ 56 8 64 rfl t3_56 c3_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_48 : anyK (node 0 6) ((kid3.drop 48).take 8) = false := by decide +kernel
theorem c3_48 : anyK (node 0 6) (kid3.drop 48) = false := chainK _ _ 48 8 56 rfl t3_48 c3_56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_40 : anyK (node 0 6) ((kid3.drop 40).take 8) = false := by decide +kernel
theorem c3_40 : anyK (node 0 6) (kid3.drop 40) = false := chainK _ _ 40 8 48 rfl t3_40 c3_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_32 : anyK (node 0 6) ((kid3.drop 32).take 8) = false := by decide +kernel
theorem c3_32 : anyK (node 0 6) (kid3.drop 32) = false := chainK _ _ 32 8 40 rfl t3_32 c3_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_24 : anyK (node 0 6) ((kid3.drop 24).take 8) = false := by decide +kernel
theorem c3_24 : anyK (node 0 6) (kid3.drop 24) = false := chainK _ _ 24 8 32 rfl t3_24 c3_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_16 : anyK (node 0 6) ((kid3.drop 16).take 8) = false := by decide +kernel
theorem c3_16 : anyK (node 0 6) (kid3.drop 16) = false := chainK _ _ 16 8 24 rfl t3_16 c3_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_8 : anyK (node 0 6) ((kid3.drop 8).take 8) = false := by decide +kernel
theorem c3_8 : anyK (node 0 6) (kid3.drop 8) = false := chainK _ _ 8 8 16 rfl t3_8 c3_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t3_0 : anyK (node 0 6) ((kid3.drop 0).take 8) = false := by decide +kernel
theorem c3_0 : anyK (node 0 6) (kid3.drop 0) = false := chainK _ _ 0 8 8 rfl t3_0 c3_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase3 : anyK (node 0 7) ((kR.drop 3).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid3 c3_0))
theorem rq3 : anyK (node 0 7) (kR.drop 3) = false := chainK _ _ 3 1 4 rfl rcase3 rq4
def kid2 := kids (hdK (kR.drop 2)).1 (hdK (kR.drop 2)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2_50 : anyK (node 0 6) (kid2.drop 50) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_48 : anyK (node 0 6) ((kid2.drop 48).take 2) = false := by decide +kernel
theorem c2_48 : anyK (node 0 6) (kid2.drop 48) = false := chainK _ _ 48 2 50 rfl t2_48 c2_50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_40 : anyK (node 0 6) ((kid2.drop 40).take 8) = false := by decide +kernel
theorem c2_40 : anyK (node 0 6) (kid2.drop 40) = false := chainK _ _ 40 8 48 rfl t2_40 c2_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_32 : anyK (node 0 6) ((kid2.drop 32).take 8) = false := by decide +kernel
theorem c2_32 : anyK (node 0 6) (kid2.drop 32) = false := chainK _ _ 32 8 40 rfl t2_32 c2_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_24 : anyK (node 0 6) ((kid2.drop 24).take 8) = false := by decide +kernel
theorem c2_24 : anyK (node 0 6) (kid2.drop 24) = false := chainK _ _ 24 8 32 rfl t2_24 c2_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_16 : anyK (node 0 6) ((kid2.drop 16).take 8) = false := by decide +kernel
theorem c2_16 : anyK (node 0 6) (kid2.drop 16) = false := chainK _ _ 16 8 24 rfl t2_16 c2_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_8 : anyK (node 0 6) ((kid2.drop 8).take 8) = false := by decide +kernel
theorem c2_8 : anyK (node 0 6) (kid2.drop 8) = false := chainK _ _ 8 8 16 rfl t2_8 c2_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t2_0 : anyK (node 0 6) ((kid2.drop 0).take 8) = false := by decide +kernel
theorem c2_0 : anyK (node 0 6) (kid2.drop 0) = false := chainK _ _ 0 8 8 rfl t2_0 c2_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase2 : anyK (node 0 7) ((kR.drop 2).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid2 c2_0))
theorem rq2 : anyK (node 0 7) (kR.drop 2) = false := chainK _ _ 2 1 3 rfl rcase2 rq3
def kid1 := kids (hdK (kR.drop 1)).1 (hdK (kR.drop 1)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1_49 : anyK (node 0 6) (kid1.drop 49) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_48 : anyK (node 0 6) ((kid1.drop 48).take 1) = false := by decide +kernel
theorem c1_48 : anyK (node 0 6) (kid1.drop 48) = false := chainK _ _ 48 1 49 rfl t1_48 c1_49
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_40 : anyK (node 0 6) ((kid1.drop 40).take 8) = false := by decide +kernel
theorem c1_40 : anyK (node 0 6) (kid1.drop 40) = false := chainK _ _ 40 8 48 rfl t1_40 c1_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_32 : anyK (node 0 6) ((kid1.drop 32).take 8) = false := by decide +kernel
theorem c1_32 : anyK (node 0 6) (kid1.drop 32) = false := chainK _ _ 32 8 40 rfl t1_32 c1_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_24 : anyK (node 0 6) ((kid1.drop 24).take 8) = false := by decide +kernel
theorem c1_24 : anyK (node 0 6) (kid1.drop 24) = false := chainK _ _ 24 8 32 rfl t1_24 c1_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_16 : anyK (node 0 6) ((kid1.drop 16).take 8) = false := by decide +kernel
theorem c1_16 : anyK (node 0 6) (kid1.drop 16) = false := chainK _ _ 16 8 24 rfl t1_16 c1_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_8 : anyK (node 0 6) ((kid1.drop 8).take 8) = false := by decide +kernel
theorem c1_8 : anyK (node 0 6) (kid1.drop 8) = false := chainK _ _ 8 8 16 rfl t1_8 c1_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t1_0 : anyK (node 0 6) ((kid1.drop 0).take 8) = false := by decide +kernel
theorem c1_0 : anyK (node 0 6) (kid1.drop 0) = false := chainK _ _ 0 8 8 rfl t1_0 c1_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase1 : anyK (node 0 7) ((kR.drop 1).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid1 c1_0))
theorem rq1 : anyK (node 0 7) (kR.drop 1) = false := chainK _ _ 1 1 2 rfl rcase1 rq2
def kid0 := kids (hdK (kR.drop 0)).1 (hdK (kR.drop 0)).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0_53 : anyK (node 0 6) (kid0.drop 53) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_48 : anyK (node 0 6) ((kid0.drop 48).take 5) = false := by decide +kernel
theorem c0_48 : anyK (node 0 6) (kid0.drop 48) = false := chainK _ _ 48 5 53 rfl t0_48 c0_53
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_40 : anyK (node 0 6) ((kid0.drop 40).take 8) = false := by decide +kernel
theorem c0_40 : anyK (node 0 6) (kid0.drop 40) = false := chainK _ _ 40 8 48 rfl t0_40 c0_48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_32 : anyK (node 0 6) ((kid0.drop 32).take 8) = false := by decide +kernel
theorem c0_32 : anyK (node 0 6) (kid0.drop 32) = false := chainK _ _ 32 8 40 rfl t0_32 c0_40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_24 : anyK (node 0 6) ((kid0.drop 24).take 8) = false := by decide +kernel
theorem c0_24 : anyK (node 0 6) (kid0.drop 24) = false := chainK _ _ 24 8 32 rfl t0_24 c0_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_16 : anyK (node 0 6) ((kid0.drop 16).take 8) = false := by decide +kernel
theorem c0_16 : anyK (node 0 6) (kid0.drop 16) = false := chainK _ _ 16 8 24 rfl t0_16 c0_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_8 : anyK (node 0 6) ((kid0.drop 8).take 8) = false := by decide +kernel
theorem c0_8 : anyK (node 0 6) (kid0.drop 8) = false := chainK _ _ 8 8 16 rfl t0_8 c0_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0_0 : anyK (node 0 6) ((kid0.drop 0).take 8) = false := by decide +kernel
theorem c0_0 : anyK (node 0 6) (kid0.drop 0) = false := chainK _ _ 0 8 8 rfl t0_0 c0_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rcase0 : anyK (node 0 7) ((kR.drop 0).take 1) = false := takeOneK _ _ (node_split 0 6 _ _ (by decide +kernel) (startK _ kid0 c0_0))
theorem rq0 : anyK (node 0 7) (kR.drop 0) = false := chainK _ _ 0 1 1 rfl rcase0 rq1
theorem pr : anyK (node 0 7) kR = false := startK _ _ rq0

theorem root_goal : isGoal rowsN = false := by
  decide +kernel

theorem root_false : root 0 7 4 rowsN = false := root_split 0 7 4 rowsN root_goal pr

theorem reject : searchN 0 7 rowsN = false := by
  unfold searchN
  rw [List.any_eq_false]
  intro ws hws
  cases h : (decide (ws.length ≤ 7 + 2) && cutFull ws)
  · simp
  · have heq := only_full ws hws h
    subst heq
    have e : 7 + 2 - rowsN.length = 4 := by decide
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

end PEqualNP.Outside.L_meta_39837.Signed

namespace PEqualNP.Outside.L_meta_39837

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_39837.Signed (legal isBinary binaryCost)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_legal (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

theorem isBinary_and (l : List ℕ) : isBinary ⟨GateOp.and, l⟩ = true := rfl
theorem isBinary_or (l : List ℕ) : isBinary ⟨GateOp.or, l⟩ = true := rfl
theorem isBinary_not (l : List ℕ) : isBinary ⟨GateOp.not, l⟩ = false := rfl

theorem simplify_binCost_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    binaryCost (simplify op m ins).1.toList ≤ if isBinary ⟨op, []⟩ then 1 else 0 := by
  have hlen : ∀ o : Option Gate, binaryCost o.toList ≤ 1 := by
    intro o
    cases o with
    | none => simp [binaryCost]
    | some g => exact (List.length_filter_le _ _).trans (by simp)
  cases op
  · exact hlen _
  · exact hlen _
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simplify, simpNot, binaryCost, isBinary_not]
  · simp [simplify, binaryCost]
  · simp [simplify, binaryCost]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem binaryCost_append (l1 l2 : List Gate) :
    binaryCost (l1 ++ l2) = binaryCost l1 + binaryCost l2 := by
  simp [binaryCost, List.filter_append]

theorem binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = (if isBinary g then 1 else 0) + binaryCost gs := by
  simp only [binaryCost, List.filter_cons]
  cases isBinary g <;> simp [Nat.add_comm]

theorem elim_legal (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → (∀ g ∈ (elim n gs acc).2, legal g) := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_legal _ _ _ g' hg'

theorem elim_binCost_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs with
  | nil => intro acc; simp [elim, binaryCost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq] at hb
      omega
    rw [elim_cons, binaryCost_cons]
    omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def AgreeNonConst (st : List Stat) (w1 w2 : List Bool) : Prop :=
  st.length = w1.length ∧ st.length = w2.length ∧
  ∀ i : ℕ, (∃ j : ℕ, st.getD i (Sum.inl false) = Sum.inr j) → w1.getD i false = w2.getD i false

theorem elim_agree_of_eq_binCost (n : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, legal g) →
      AgreeNonConst acc.1 w1 w2 →
      binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs →
      AgreeNonConst (elim n gs acc).1 (wiresFrom gs w1) (wiresFrom gs w2) := by
  induction gs with
  | nil => intro w1 w2 acc _ hag _; exact hag
  | cons g gs ih =>
    intro w1 w2 acc hok hag heq
    have hstep_le : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq' : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq'] at hb; omega
    have htail_le := elim_binCost_le n gs (elimStep n acc g)
    rw [elim_cons, binaryCost_cons] at heq
    have hstep_eq : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + (if isBinary g then 1 else 0) := by omega
    have htail_eq : binaryCost (elim n gs (elimStep n acc g)).2 = binaryCost (elimStep n acc g).2 + binaryCost gs := by omega
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
             (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
             (elimStep n acc g)
             (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ htail_eq
    obtain ⟨hl1, hl2, hwi⟩ := hag
    refine ⟨by simp [elimStep, hl1], by simp [elimStep, hl2], ?_⟩
    intro i hi
    by_cases hil : i = acc.1.length
    · subst hil
      simp only [elimStep] at hi ⊢
      rw [getD_snoc_eq] at hi
      rw [hl1, getD_snoc_eq, ← hl1, hl2, getD_snoc_eq]
      have hgok := hok g List.mem_cons_self
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hlen⟩ := hgok
      dsimp only [elimStep] at hi hstep_eq
      rw [binaryCost_append] at hstep_eq
      rcases hop with rfl | rfl | rfl
      · rw [isBinary_and] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpAnd, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpAnd, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rw [isBinary_or] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpOr, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpOr, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rcases args with _ | ⟨k1, l⟩
        · simp [simplify, simpNot] at hi
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, h1] at hi
            simp [simplify, simpNot] at hi
          · have e1 := hwi k1 ⟨a, h1⟩
            simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 ⊢
            rw [e1]
    · simp only [elimStep] at hi ⊢
      rw [getD_snoc_ne _ _ _ _ hil] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hwi i hi

def insAt {α : Type} {n : ℕ} (idx : Fin (n + 1)) (v : α) (y : Fin n → α) (k : Fin (n + 1)) : α :=
  if h1 : k.val < idx.val then y ⟨k.val, by omega⟩
  else if h2 : k.val = idx.val then v
  else y ⟨k.val - 1, by omega⟩

theorem drop_one_var {n : ℕ} (idx : Fin (n + 1)) (v : Bool) (F : (Fin (n + 1) → Bool) → Bool)
    (y_diff y0 y1 : Fin n → Bool)
    (hdiff : F (insAt idx false y_diff) ≠ F (insAt idx true y_diff))
    (hnc : F (insAt idx v y0) ≠ F (insAt idx v y1))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin (n + 1) → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', legal g) ∧ binaryCost gs' < binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn y) = F (insAt idx v y) := by
  let initFn : Fin (n + 1) → Stat := insAt idx (Sum.inl v) (fun i : Fin n => Sum.inr i.val)
  let initSt : List Stat := List.ofFn initFn
  let res := elim n gs (initSt, [])
  have hgetFn : ∀ {α : Type} (f : Fin (n + 1) → α) (d : α) (i : ℕ) (hi : i < n + 1),
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    intro α f d i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]), Option.getD_some,
      List.getElem_ofFn]
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (List.ofFn (insAt idx v y)) (initSt, []) := by
    intro y
    refine ⟨by simp [initSt], ?_⟩
    intro i
    by_cases hi : i < n + 1
    · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi,
          hgetFn (insAt idx v y) false i hi]
      dsimp only [initFn, insAt]
      by_cases h1 : i < idx.val
      · simp only [h1, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
        refine ⟨by omega, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
          Option.getD_some, List.getElem_ofFn]
      · by_cases h2 : i = idx.val
        · simp [h2, statValid, statVal]
        · simp only [h1, h2, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
          refine ⟨by omega, ?_⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
            Option.getD_some, List.getElem_ofFn]
    · have h1 : initSt.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [initSt]; omega)
      have h2 : (List.ofFn (insAt idx v y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [h1, h2]; simp [statValid, statVal]
  have heval : ∀ y : Fin n → Bool,
      statVal (wiresFrom res.2 (List.ofFn y)) (res.1.getD o (Sum.inl false)) =
        F (insAt idx v y) := by
    intro y
    have hi := inv_elim n (List.ofFn y) (by simp) gs (List.ofFn (insAt idx v y)) (initSt, []) hg (hinv y)
    have h2 := (hi.2 o).2
    have h3 : (wiresFrom gs (List.ofFn (insAt idx v y))).getD o false =
        F (insAt idx v y) := he (insAt idx v y)
    exact h2.trans h3
  have hout_inr : ∃ o', res.1.getD o (Sum.inl false) = Sum.inr o' := by
    cases hst : res.1.getD o (Sum.inl false) with
    | inl c =>
      have e0 := heval y0; rw [hst] at e0
      have e1 := heval y1; rw [hst] at e1
      exact (hnc (e0.symm.trans e1)).elim
    | inr o' => exact ⟨o', rfl⟩
  obtain ⟨o', ho'⟩ := hout_inr
  have hlt : binaryCost res.2 < binaryCost gs := by
    have hle : binaryCost res.2 ≤ binaryCost ([] : List Gate) + binaryCost gs :=
      elim_binCost_le n gs (initSt, [])
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    by_contra hnot
    have heq : binaryCost res.2 = binaryCost ([] : List Gate) + binaryCost gs := by omega
    have hag0 : AgreeNonConst initSt
        (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff)) := by
      refine ⟨by simp [initSt], by simp [initSt], ?_⟩
      intro i ⟨j, hj⟩
      by_cases hi : i < n + 1
      · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi] at hj
        rw [hgetFn (insAt idx false y_diff) false i hi, hgetFn (insAt idx true y_diff) false i hi]
        dsimp only [initFn, insAt] at hj ⊢
        by_cases h1 : i < idx.val
        · simp [h1]
        · by_cases h2 : i = idx.val
          · simp [h2] at hj
          · simp [h1, h2]
      · rw [List.getD_eq_default _ _ (by simp [initSt]; omega)] at hj
        cases hj
    have hag := elim_agree_of_eq_binCost n gs
      (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff))
      (initSt, []) hg hag0 heq
    have hsame := hag.2.2 o ⟨o', ho'⟩
    have hf0 : (wiresFrom gs (List.ofFn (insAt idx false y_diff))).getD o false =
        F (insAt idx false y_diff) := he _
    have hf1 : (wiresFrom gs (List.ofFn (insAt idx true y_diff))).getD o false =
        F (insAt idx true y_diff) := he _
    exact hdiff (hf0.symm.trans (hsame.trans hf1))
  refine ⟨res.2, o', elim_legal n gs (initSt, []) (by simp), hlt, ?_⟩
  intro y
  have h := heval y
  rw [ho'] at h
  exact h

def targetFun6 (T : ℕ) (x : Fin 6 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)


set_option maxRecDepth 32000 in
theorem bound6 (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetFun6 (4008373480 * 2 ^ 32 + 4007718016) x) :
    9 < binaryCost gs := by
  obtain ⟨gs1, o1, hg1, hlt1, he1⟩ :=
    drop_one_var (3 : Fin 6) false (targetFun6 (4008373480 * 2 ^ 32 + 4007718016))
      (fun k => Nat.testBit 2 k.val) (fun _ => false) (fun _ => true)
      (by decide +kernel) (by decide +kernel) gs o hg he
  have hb := Signed.bound_from_searchN (fun y => targetFun6 (4008373480 * 2 ^ 32 + 4007718016) (insAt (3 : Fin 6) false y))
    Signed.rows rfl (by decide) (by rw [Signed.rows_eq]; exact Signed.reject)
    Signed.goal_hi Signed.goal_lo Signed.sep_hi Signed.sep_lo (by decide +kernel) gs1 o1 hg1 he1
  omega
def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [6, 15]⟩], 16⟩
set_option maxRecDepth 32000 in
theorem solve (s : ℕ) (hs : HasCircuitSize 6 (targetFun6 (4008373480 * 2 ^ 32 + 4007718016)) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun6 (4008373480 * 2 ^ 32 + 4007718016) x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound6 C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, by decide +kernel⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_39837

theorem PEqualNP.Outside.L_meta_39837 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4007718016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4007718016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_39837.solve
