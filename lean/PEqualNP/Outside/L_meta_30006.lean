import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30006_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def fromWords (words : List Nat) : Nat :=
  words.foldl (fun acc w => (acc <<< 64) ||| w) 0

def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem avail_mono {d:Nat} {bank:List Nat} {w:Nat} (h : Avail false d bank w) :
    Avail true d bank w:=by
  rcases h with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction
theorem reach_up {d:Nat} {roots:List Nat} {p bank} (h:NatReach false d roots p bank) :
    NatReach true d roots p bank:=by
  induction p generalizing bank with
  | zero=>exact h
  | succ p ih =>
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=h
    have hop' : allowedB true op = true:=by
      rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩ <;> first | decide | contradiction
    exact ⟨b,a,c,op,hop',rfl,ih hrb,avail_mono ha,avail_mono hc⟩
theorem lower_down {d:Nat} {roots:List Nat} {T L:Nat} (h : Lower true d roots T L) :
    Lower false d roots T L:=fun p bank hr ha=>h p bank (reach_up hr) (avail_mono ha)
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [(fromWords [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa]),
   (fromWords [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc]),
   (fromWords [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0]),
   (fromWords [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00]),
   (fromWords [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000]),
   (fromWords [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000]),
   (fromWords [0xffffffffffffffff, 0x0, 0xffffffffffffffff, 0x0]),
   (fromWords [0xffffffffffffffff, 0xffffffffffffffff, 0x0, 0x0])]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega
def dom15 : Nat := 0xffff
def goal15 : Nat := 0xeea0
def roots15 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

namespace G15
def pairsG : List (Nat × Nat) := [(8, 10), (1, 5), (8, 9), (1, 9), (6, 14), (6, 7), (3, 5)]
def xsM := roots15.map (· &&& dom15)
def goalM := goal15 &&& dom15
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xaaaa
  | 1 => 0xcccc
  | 2 => 0xf0f0
  | 3 => 0xff00
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x3d3b0
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom15 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom15 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom15 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom15 roots15 goal15 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G15

theorem low15 : Lower true dom15 roots15 goal15 4 := G15.noCircuit


def dom23 : Nat := 0xff00ff
def goal23 : Nat := 0xfc00a0
def roots23 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

namespace G23
def pairsG : List (Nat × Nat) := [(16, 18), (16, 20), (3, 19), (3, 7), (4, 20), (4, 5), (6, 5)]
def xsM := roots23.map (· &&& dom23)
def goalM := goal23 &&& dom23
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xaa00aa
  | 1 => 0xcc00cc
  | 2 => 0xf000f0
  | 3 => 0xff0000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x739f5
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom23 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom23 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom23 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom23 roots23 goal23 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G23

theorem low23 : Lower true dom23 roots23 goal23 4 := G23.noCircuit


def dom27 : Nat := 0xf0f0f0f
def goal27 : Nat := 0xe0c0e00
def roots27 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

namespace G27
def pairsG : List (Nat × Nat) := [(2, 18), (17, 19), (2, 10), (8, 9), (8, 10), (17, 25), (24, 9)]
def xsM := roots27.map (· &&& dom27)
def goalM := goal27 &&& dom27
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xa0a0a0a
  | 1 => 0xc0c0c0c
  | 2 => 0xf000f00
  | 3 => 0xf0f0000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x77db1
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom27 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom27 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom27 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom27 roots27 goal27 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G27

theorem low27 : Lower true dom27 roots27 goal27 4 := G27.noCircuit


def dom29 : Nat := 0x33333333
def goal29 : Nat := 0x32302220
def roots29 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

namespace G29
def pairsG : List (Nat × Nat) := [(1, 9), (4, 20), (24, 28), (4, 5), (24, 25), (1, 5), (17, 9)]
def xsM := roots29.map (· &&& dom29)
def goalM := goal29 &&& dom29
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x22222222
  | 1 => 0x30303030
  | 2 => 0x33003300
  | 3 => 0x33330000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x80566
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom29 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom29 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom29 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom29 roots29 goal29 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G29

theorem low29 : Lower true dom29 roots29 goal29 4 := G29.noCircuit


def dom30 : Nat := 0x55555555
def goal30 : Nat := 0x54544400
def roots30 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

namespace G30
def pairsG : List (Nat × Nat) := [(16, 20), (2, 10), (16, 18), (2, 18), (12, 28), (12, 14), (6, 10)]
def xsM := roots30.map (· &&& dom30)
def goalM := goal30 &&& dom30
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x44444444
  | 1 => 0x50505050
  | 2 => 0x55005500
  | 3 => 0x55550000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xa4c91
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom30 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom30 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom30 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom30 roots30 goal30 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G30

theorem low30 : Lower true dom30 roots30 goal30 4 := G30.noCircuit


def dom31 : Nat := 0xffffffff
def goal31 : Nat := 0xfefceea0
def roots31 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace G31
def pairsG : List (Nat × Nat) := [(3, 19), (24, 25), (17, 19), (17, 25), (1, 5), (12, 28), (6, 7), (4, 5), (12, 14), (16, 20), (2, 10), (16, 18), (1, 9), (8, 9), (3, 7), (24, 28), (2, 18), (4, 20), (8, 10), (6, 14), (6, 5), (3, 5), (17, 5), (12, 5), (12, 9), (24, 10), (6, 10), (17, 9), (3, 9), (24, 9)]
def xsM := roots31.map (· &&& dom31)
def goalM := goal31 &&& dom31
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 11
  | 5 => 11
  | 6 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 11
  | 6 => 22
  | _ => 0
def wireAtBlock : Nat → Nat
  | 0 => (fromWords [0xfcfcfcfcfcfc0000, 0xfafafafaf0f0f0f0, 0xf0f0a0a0eeeeeeee, 0xee00ee00cccccccc, 0xcccccc00aaaaaaaa, 0xaaa0aaa055505550, 0x333333000f0f0a0a, 0xee00ee0000fcfc])
  | 1 => (fromWords [0xffffff00, 0xfffff0f0ffffcccc, 0xffffaaaaffff0000, 0xfff0fff0ffccffcc, 0xffaaffaaff00ff00])
  | _ => 0
def wireAt (i : Nat) : Nat := fld (wireAtBlock (i / 16)) 32 (i % 16)
def stateWireBlock : Nat → Nat
  | 0 => (fromWords [0x29383106a4a0c41b, 0x1483106a418a41a9, 0x7b106a41883520d, 0x620d48c1883520c4, 0x1690620907310683, 0x1060520b41a8c418, 0x34830e6a41061520, 0xc41a8c4a0d4830c3])
  | 1 => (fromWords [0x520c41ad48310, 0x6bd20c41ab483106])
  | _ => 0
def stateWire (i : Nat) : Nat := fld (stateWireBlock (i / 102)) 5 (i % 102)
def stateDescriptorBlock : Nat → Nat
  | 0 => (fromWords [0x1e17936c6ccd81ad, 0x35469cd21a1abd66, 0xecc956aa8546a794, 0xca9451ea2942a805])
  | _ => 0
def stateDescriptor (i : Nat) : Nat := fld (stateDescriptorBlock (i / 46)) 11 (i % 46)
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAtBlock : Nat → Nat
  | 0 => (fromWords [0x638, 0xdfa026f0814e808, 0x6d6eb4c480eb8ff0, 0x9fc0a979bd6380d5, 0x61912bbbdf0970e1, 0x2acd6a3b78faf77f, 0x1972c2a69b7e6478, 0xc6380d3f1ac2cea8])
  | _ => 0
def hashAt (i : Nat) : Nat := fld (hashAtBlock (i / 25)) 20 (i % 25)
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 5 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptorBlock : Nat → Nat
  | _ => 0
def opDescriptor (i : Nat) : Nat := fld (opDescriptorBlock (i / 512)) 1 (i % 512)
def useMaskBlock : Nat → Nat
  | 0 => (fromWords [0x7c00000000000, 0x0])
  | _ => 0
def useMask (i : Nat) : Nat := fld (useMaskBlock (i / 102)) 5 (i % 102)
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 31), wireAt (v >>> 7)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom15, 4, runOps true dom15 (0, roots15) ops)] else []) ++
    (if pm.testBit 1 then [(dom23, 4, runOps true dom23 (0, roots23) ops)] else []) ++
    (if pm.testBit 2 then [(dom27, 4, runOps true dom27 (0, roots27) ops)] else []) ++
    (if pm.testBit 3 then [(dom29, 4, runOps true dom29 (0, roots29) ops)] else []) ++
    (if pm.testBit 4 then [(dom30, 4, runOps true dom30 (0, roots30) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom31 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low15 _ g hchk
    · exact cpcs (by decide +kernel) low23 _ g hchk
    · exact cpcs (by decide +kernel) low27 _ g hchk
    · exact cpcs (by decide +kernel) low29 _ g hchk
    · exact cpcs (by decide +kernel) low30 _ g hchk
def Z (s : Nat) := barP true dom31 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 11 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 11 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s,
    bar true dom31 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 3 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom31 roots31 goal31 7 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G31

theorem low31 : Lower true dom31 roots31 goal31 7 := G31.noCircuit


def dom37 : Nat := 0x3300000033
def goal37 : Nat := 0x3200000020
def roots37 : List Nat := [0x2200000022, 0x3000000030, 0x3300000000]

namespace G37
def pairsG : List (Nat × Nat) := [(32, 36), (32, 33), (1, 5), (4, 5), (4, 36), (1, 33)]
def xsM := roots37.map (· &&& dom37)
def goalM := goal37 &&& dom37
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | 3 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x2200000022
  | 1 => 0x3000000030
  | 2 => 0x3300000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 4 => 1
  | 5 => 2
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 3
  | 1 => 51
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xdd135
  | 1 => 0xdd135
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom37 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom37 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom37 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 2 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom37 roots37 goal37 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 2 ≤ s := by
    have hl := run_len h
    change 3 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G37

theorem low37 : Lower true dom37 roots37 goal37 4 := G37.noCircuit


def dom39 : Nat := 0xff000000ff
def goal39 : Nat := 0xfe000000a0
def roots39 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

namespace G39
def pairsG : List (Nat × Nat) := [(32, 34), (6, 7), (32, 36), (3, 7), (32, 33), (4, 36), (3, 35)]
def xsM := roots39.map (· &&& dom39)
def goalM := goal39 &&& dom39
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xaa000000aa
  | 1 => 0xcc000000cc
  | 2 => 0xf0000000f0
  | 3 => 0xff00000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x5fe7b
  | 1 => 0x5fe7b
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom37, 4, runOps true dom37 (0, roots37) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom39 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low37 _ g hchk
def Z (s : Nat) := barP true dom39 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom39 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom39 roots39 goal39 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G39

theorem low39 : Lower true dom39 roots39 goal39 5 := G39.noCircuit


def dom45 : Nat := 0x333300003333
def goal45 : Nat := 0x323200002220
def roots45 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

namespace G45
def pairsG : List (Nat × Nat) := [(1, 9), (40, 44), (12, 44), (1, 33), (1, 5), (4, 5), (40, 41)]
def xsM := roots45.map (· &&& dom45)
def goalM := goal45 &&& dom45
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x222200002222
  | 1 => 0x303000003030
  | 2 => 0x330000003300
  | 3 => 0x333300000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x2d750
  | 1 => 0x2d750
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom37, 4, runOps true dom37 (0, roots37) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom45 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low37 _ g hchk
def Z (s : Nat) := barP true dom45 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom45 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom45 roots45 goal45 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G45

theorem low45 : Lower true dom45 roots45 goal45 5 := G45.noCircuit


def dom46 : Nat := 0x555500005555
def goal46 : Nat := 0x545400004400
def roots46 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

namespace G46
def pairsG : List (Nat × Nat) := [(32, 36), (2, 10), (32, 34), (2, 34), (12, 44), (12, 14), (6, 10)]
def xsM := roots46.map (· &&& dom46)
def goalM := goal46 &&& dom46
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x444400004444
  | 1 => 0x505000005050
  | 2 => 0x550000005500
  | 3 => 0x555500000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xb7b69
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom46 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom46 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom46 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom46 roots46 goal46 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G46

theorem low46 : Lower true dom46 roots46 goal46 4 := G46.noCircuit


def dom47 : Nat := 0xffff0000ffff
def goal47 : Nat := 0xfefe0000eea0
def roots47 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace G47
def pairsG : List (Nat × Nat) := [(6, 7), (32, 34), (1, 9), (3, 7), (12, 14), (40, 44), (6, 14), (12, 44), (3, 35), (40, 41)]
def xsM := roots47.map (· &&& dom47)
def goalM := goal47 &&& dom47
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xaaaa0000aaaa
  | 1 => 0xcccc0000cccc
  | 2 => 0xf0f00000f0f0
  | 3 => 0xff000000ff00
  | 4 => 0xffff00000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | 9 => 4
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 5
  | 1 => 85
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x76e79
  | 1 => 0x76e79
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom39, 5, runOps true dom39 (0, roots39) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom47 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low39 _ g hchk
def Z (s : Nat) := barP true dom47 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s,
    bar true dom47 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom47 roots47 goal47 6 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G47

theorem low47 : Lower true dom47 roots47 goal47 6 := G47.noCircuit


def dom50 : Nat := 0x5000500050005
def goal50 : Nat := 0x5000400040000
def roots50 : List Nat := [0x4000400040004, 0x5000000050000, 0x5000500000000]

namespace G50
def pairsG : List (Nat × Nat) := [(32, 48), (32, 34), (2, 18), (16, 18), (16, 48), (2, 34)]
def xsM := roots50.map (· &&& dom50)
def goalM := goal50 &&& dom50
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | 3 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x4000400040004
  | 1 => 0x5000000050000
  | 2 => 0x5000500000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 4 => 1
  | 5 => 2
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 3
  | 1 => 51
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xee085
  | 1 => 0xee085
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom50 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom50 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom50 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 2 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom50 roots50 goal50 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 2 ≤ s := by
    have hl := run_len h
    change 3 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G50

theorem low50 : Lower true dom50 roots50 goal50 4 := G50.noCircuit


def dom51 : Nat := 0xf000f000f000f
def goal51 : Nat := 0xf000e000c0000
def roots51 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

namespace G51
def pairsG : List (Nat × Nat) := [(32, 33), (3, 19), (32, 48), (32, 34), (17, 19), (2, 34), (17, 49)]
def xsM := roots51.map (· &&& dom51)
def goalM := goal51 &&& dom51
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xa000a000a000a
  | 1 => 0xc000c000c000c
  | 2 => 0xf0000000f0000
  | 3 => 0xf000f00000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x5ac2a
  | 1 => 0x5ac2a
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom50, 4, runOps true dom50 (0, roots50) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom51 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low50 _ g hchk
def Z (s : Nat) := barP true dom51 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom51 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom51 roots51 goal51 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G51

theorem low51 : Lower true dom51 roots51 goal51 5 := G51.noCircuit


def dom52 : Nat := 0x11001100110011
def goal52 : Nat := 0x11001000100000
def roots52 : List Nat := [0x10001000100010, 0x11000000110000, 0x11001100000000]

namespace G52
def pairsG : List (Nat × Nat) := [(32, 48), (32, 36), (4, 20), (16, 20), (16, 48), (4, 36)]
def xsM := roots52.map (· &&& dom52)
def goalM := goal52 &&& dom52
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | 3 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x10001000100010
  | 1 => 0x11000000110000
  | 2 => 0x11001100000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 4 => 1
  | 5 => 2
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 3
  | 1 => 51
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x72e65
  | 1 => 0x72e65
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom52 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom52 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom52 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 2 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom52 roots52 goal52 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 2 ≤ s := by
    have hl := run_len h
    change 3 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G52

theorem low52 : Lower true dom52 roots52 goal52 4 := G52.noCircuit


def dom53 : Nat := 0x33003300330033
def goal53 : Nat := 0x33003200300020
def roots53 : List Nat := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]

namespace G53
def pairsG : List (Nat × Nat) := [(4, 5), (32, 33), (32, 48), (4, 36), (32, 36), (4, 20), (17, 21), (17, 49)]
def xsM := roots53.map (· &&& dom53)
def goalM := goal53 &&& dom53
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x22002200220022
  | 1 => 0x30003000300030
  | 2 => 0x33000000330000
  | 3 => 0x33003300000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xdb19e
  | 1 => 0xdb19e
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 0 => 1
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom37, 4, runOps true dom37 (0, roots37) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom53 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low37 _ g hchk
def Z (s : Nat) := barP true dom53 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom53 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom53 roots53 goal53 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G53

theorem low53 : Lower true dom53 roots53 goal53 5 := G53.noCircuit


def dom54 : Nat := 0x55005500550055
def goal54 : Nat := 0x55005400540000
def roots54 : List Nat := [0x44004400440044, 0x50005000500050, 0x55000000550000, 0x55005500000000]

namespace G54
def pairsG : List (Nat × Nat) := [(16, 18), (32, 34), (32, 36), (16, 20), (16, 48), (32, 48), (6, 38), (6, 22)]
def xsM := roots54.map (· &&& dom54)
def goalM := goal54 &&& dom54
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x44004400440044
  | 1 => 0x50005000500050
  | 2 => 0x55000000550000
  | 3 => 0x55005500000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x9c2f8
  | 1 => 0x9c2f8
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 0 => 1
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom50, 4, runOps true dom50 (0, roots50) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom54 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low50 _ g hchk
def Z (s : Nat) := barP true dom54 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom54 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom54 roots54 goal54 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G54

theorem low54 : Lower true dom54 roots54 goal54 5 := G54.noCircuit


def dom55 : Nat := 0xff00ff00ff00ff
def goal55 : Nat := 0xff00fe00fc00a0
def roots55 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace G55
def pairsG : List (Nat × Nat) := [(32, 34), (6, 7), (17, 19), (3, 19), (32, 33), (32, 48), (3, 7), (32, 36), (16, 48), (4, 20), (16, 20), (6, 38), (1, 33)]
def xsM := roots55.map (· &&& dom55)
def goalM := goal55 &&& dom55
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 1
  | 6 => 2
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xaa00aa00aa00aa
  | 1 => 0xcc00cc00cc00cc
  | 2 => 0xf000f000f000f0
  | 3 => 0xff000000ff0000
  | 4 => 0xff00ff00000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | 9 => 4
  | 11 => 1
  | 12 => 2
  | 13 => 3
  | 14 => 4
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 5
  | 1 => 85
  | 2 => 165
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x2e6eb
  | 1 => 0x2e6eb
  | 2 => 0x2e6eb
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | 2 => 15
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom39, 5, runOps true dom39 (0, roots39) ops)] else []) ++
    (if pm.testBit 1 then [(dom51, 5, runOps true dom51 (0, roots51) ops)] else []) ++
    (if pm.testBit 2 then [(dom53, 5, runOps true dom53 (0, roots53) ops)] else []) ++
    (if pm.testBit 3 then [(dom54, 5, runOps true dom54 (0, roots54) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom55 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low39 _ g hchk
    · exact cpcs (by decide +kernel) low51 _ g hchk
    · exact cpcs (by decide +kernel) low53 _ g hchk
    · exact cpcs (by decide +kernel) low54 _ g hchk
def Z (s : Nat) := barP true dom55 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s,
    bar true dom55 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 3 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom55 roots55 goal55 7 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G55

theorem low55 : Lower true dom55 roots55 goal55 7 := G55.noCircuit


def dom57 : Nat := 0x303030303030303
def goal57 : Nat := 0x303020202000200
def roots57 : List Nat := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]

namespace G57
def pairsG : List (Nat × Nat) := [(32, 48), (1, 9), (32, 33), (24, 56), (24, 25), (1, 33), (17, 9)]
def xsM := roots57.map (· &&& dom57)
def goalM := goal57 &&& dom57
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def offset : Nat → Nat
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x202020202020202
  | 1 => 0x300030003000300
  | 2 => 0x303000003030000
  | 3 => 0x303030300000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xaf45d
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom57 goalM s ws := by
  simp [mkCut, mkPools] at h
def Z (s : Nat) := barP true dom57 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s,
    bar true dom57 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 1 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom57 roots57 goal57 4 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G57

theorem low57 : Lower true dom57 roots57 goal57 4 := G57.noCircuit


def dom58 : Nat := 0x505050505050505
def goal58 : Nat := 0x505040404040400
def roots58 : List Nat := [0x404040404040404, 0x500050005000500, 0x505000005050000, 0x505050500000000]

namespace G58
def pairsG : List (Nat × Nat) := [(2, 10), (40, 56), (24, 56), (2, 34), (2, 18), (16, 18), (40, 42)]
def xsM := roots58.map (· &&& dom58)
def goalM := goal58 &&& dom58
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x404040404040404
  | 1 => 0x500050005000500
  | 2 => 0x505000005050000
  | 3 => 0x505050500000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 4
  | 1 => 68
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0xd553f
  | 1 => 0xd553f
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom50, 4, runOps true dom50 (0, roots50) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom58 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low50 _ g hchk
def Z (s : Nat) := barP true dom58 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s,
    bar true dom58 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom58 roots58 goal58 5 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 3 ≤ s := by
    have hl := run_len h
    change 4 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G58

theorem low58 : Lower true dom58 roots58 goal58 5 := G58.noCircuit


def dom59 : Nat := 0xf0f0f0f0f0f0f0f
def goal59 : Nat := 0xf0f0e0e0e0c0e00
def roots59 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

namespace G59
def pairsG : List (Nat × Nat) := [(17, 19), (2, 10), (32, 33), (3, 19), (24, 25), (17, 25), (40, 56), (24, 56), (3, 35), (40, 42)]
def xsM := roots59.map (· &&& dom59)
def goalM := goal59 &&& dom59
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 1
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0xa0a0a0a0a0a0a0a
  | 1 => 0xc0c0c0c0c0c0c0c
  | 2 => 0xf000f000f000f00
  | 3 => 0xf0f00000f0f0000
  | 4 => 0xf0f0f0f00000000
  | _ => 0
def stateWire : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | 9 => 4
  | _ => 0
def stateDescriptor : Nat → Nat
  | 0 => 5
  | 1 => 85
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x260ba
  | 1 => 0x260ba
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 2 0 (NN s)
def opAt (_ : Nat) : Nat := 0
def opDescriptor : Nat → Nat
  | _ => 0
def useMask : Nat → Nat
  | 1 => 1
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 7), wireAt (v >>> 5)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom51, 5, runOps true dom51 (0, roots51) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom59 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low51 _ g hchk
def Z (s : Nat) := barP true dom59 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s,
    bar true dom59 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 2 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom59 roots59 goal59 6 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G59

theorem low59 : Lower true dom59 roots59 goal59 6 := G59.noCircuit


def dom61 : Nat := 0x3333333333333333
def goal61 : Nat := 0x3333323232302220
def roots61 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

namespace G61
def pairsG : List (Nat × Nat) := [(24, 25), (17, 25), (32, 33), (32, 48), (1, 9), (4, 20), (4, 5), (17, 21), (12, 44), (17, 49), (24, 28), (12, 28), (32, 36), (40, 36), (4, 36), (24, 48)]
def xsM := roots61.map (· &&& dom61)
def goalM := goal61 &&& dom61
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 5
  | 6 => 9
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x33303330
  | 1 => 0x333300003030
  | 2 => 0x303030303000300
  | 3 => 0x2222222222222222
  | 4 => 0x3030303030303030
  | 5 => 0x3300330033003300
  | 6 => 0x3330333033303330
  | 7 => 0x3333000033330000
  | 8 => 0x3333333300000000
  | 9 => 0x3333333330303030
  | 10 => 0x3333333333003300
  | 11 => 0x3333333333303330
  | _ => 0
def stateWireBlock : Nat → Nat
  | 0 => (fromWords [0x875, 0x4398754387543876, 0x43a8743b87438543, 0x1874328754387430])
  | _ => 0
def stateWire (i : Nat) : Nat := fld (stateWireBlock (i / 128)) 4 (i % 128)
def stateDescriptor : Nat → Nat
  | 0 => 5
  | 1 => 85
  | 2 => 165
  | 3 => 245
  | 4 => 325
  | 5 => 405
  | 6 => 485
  | 7 => 565
  | 8 => 646
  | 9 => 741
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x64f70
  | 1 => 0x667d8
  | 2 => 0x913ea
  | 3 => 0x9b8c9
  | 4 => 0xc166a
  | 5 => 0xb7e4
  | 6 => 0x2c608
  | 7 => 0x667d8
  | 8 => 0xe836f
  | 9 => 0x667d8
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 4 0 (NN s)
def opAt : Nat → Nat
  | 0 => 337
  | 1 => 537
  | 2 => 533
  | 3 => 337
  | 4 => 529
  | _ => 0
def opDescriptor : Nat → Nat
  | 4 => 2
  | 5 => 33
  | 6 => 49
  | 7 => 64
  | 8 => 65
  | 9 => 80
  | _ => 0
def useMask : Nat → Nat
  | 4 => 4
  | 5 => 15
  | 6 => 14
  | 7 => 2
  | 8 => 11
  | 9 => 31
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 15), wireAt (v >>> 6)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom29, 4, runOps true dom29 (0, roots29) ops)] else []) ++
    (if pm.testBit 1 then [(dom45, 5, runOps true dom45 (0, roots45) ops)] else []) ++
    (if pm.testBit 2 then [(dom52, 4, runOps true dom52 (0, roots52) ops)] else []) ++
    (if pm.testBit 3 then [(dom53, 5, runOps true dom53 (0, roots53) ops)] else []) ++
    (if pm.testBit 4 then [(dom57, 4, runOps true dom57 (0, roots57) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom61 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low29 _ g hchk
    · exact cpcs (by decide +kernel) low45 _ g hchk
    · exact cpcs (by decide +kernel) low52 _ g hchk
    · exact cpcs (by decide +kernel) low53 _ g hchk
    · exact cpcs (by decide +kernel) low57 _ g hchk
def Z (s : Nat) := barP true dom61 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 5 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 4 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s,
    bar true dom61 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 3 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom61 roots61 goal61 7 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G61

theorem low61 : Lower true dom61 roots61 goal61 7 := G61.noCircuit


def dom62 : Nat := 0x5555555555555555
def goal62 : Nat := 0x5555545454544400
def roots62 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

namespace G62
def pairsG : List (Nat × Nat) := [(12, 14), (32, 34), (2, 10), (32, 36), (16, 20), (16, 18), (6, 14), (6, 22), (6, 38), (24, 56), (12, 36), (40, 56), (32, 48), (24, 28), (16, 48), (12, 20)]
def xsM := roots62.map (· &&& dom62)
def goalM := goal62 &&& dom62
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 4 => 5
  | 5 => 4
  | 6 => 1
  | _ => 0
def offset : Nat → Nat
  | 5 => 5
  | 6 => 9
  | _ => 0
def wireAt : Nat → Nat
  | 0 => 0x55555500
  | 1 => 0x555500005500
  | 2 => 0x505050505050000
  | 3 => 0x4444444444444444
  | 4 => 0x5050505050505050
  | 5 => 0x5500550055005500
  | 6 => 0x5555000055550000
  | 7 => 0x5555550055555500
  | 8 => 0x5555555500000000
  | 9 => 0x5555555555005500
  | 10 => 0x5555555555550000
  | 11 => 0x5555555555555500
  | _ => 0
def stateWireBlock : Nat → Nat
  | 0 => (fromWords [0x865, 0x4386543876439864, 0x3a86543864318654, 0x386430b864386532])
  | _ => 0
def stateWire (i : Nat) : Nat := fld (stateWireBlock (i / 128)) 4 (i % 128)
def stateDescriptor : Nat → Nat
  | 0 => 5
  | 1 => 85
  | 2 => 165
  | 3 => 245
  | 4 => 325
  | 5 => 406
  | 6 => 501
  | 7 => 581
  | 8 => 661
  | 9 => 741
  | _ => 0
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAt : Nat → Nat
  | 0 => 0x3b5f8
  | 1 => 0x5daf5
  | 2 => 0x8e132
  | 3 => 0x9170a
  | 4 => 0xaf04f
  | 5 => 0x307bf
  | 6 => 0x53c53
  | 7 => 0x5610b
  | 8 => 0x9170a
  | 9 => 0x9170a
  | _ => 0
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 4 0 (NN s)
def opAt : Nat → Nat
  | 0 => 405
  | 1 => 541
  | 2 => 537
  | 3 => 533
  | 4 => 405
  | _ => 0
def opDescriptor : Nat → Nat
  | 1 => 2
  | 5 => 33
  | 6 => 49
  | 7 => 65
  | 8 => 80
  | 9 => 80
  | _ => 0
def useMask : Nat → Nat
  | 1 => 4
  | 5 => 25
  | 6 => 29
  | 7 => 30
  | 8 => 8
  | 9 => 31
  | _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 15), wireAt (v >>> 6)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom30, 4, runOps true dom30 (0, roots30) ops)] else []) ++
    (if pm.testBit 1 then [(dom46, 4, runOps true dom46 (0, roots46) ops)] else []) ++
    (if pm.testBit 2 then [(dom52, 4, runOps true dom52 (0, roots52) ops)] else []) ++
    (if pm.testBit 3 then [(dom54, 5, runOps true dom54 (0, roots54) ops)] else []) ++
    (if pm.testBit 4 then [(dom58, 5, runOps true dom58 (0, roots58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom62 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low30 _ g hchk
    · exact cpcs (by decide +kernel) low46 _ g hchk
    · exact cpcs (by decide +kernel) low52 _ g hchk
    · exact cpcs (by decide +kernel) low54 _ g hchk
    · exact cpcs (by decide +kernel) low58 _ g hchk
def Z (s : Nat) := barP true dom62 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 5 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 4 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s,
    bar true dom62 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 3 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom62 roots62 goal62 7 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 4 ≤ s := by
    have hl := run_len h
    change 5 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G62

theorem low62 : Lower true dom62 roots62 goal62 7 := G62.noCircuit


def dom63 : Nat := 0xffffffffffffffff
def goal63 : Nat := 0xfffffefefefceea0
def roots63 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace G63
def pairsG : List (Nat × Nat) := [(3, 19), (12, 14), (17, 21), (17, 19), (6, 5), (6, 22), (24, 28), (12, 28), (1, 5), (3, 5), (24, 25), (12, 5), (40, 44), (16, 18), (4, 5), (24, 18), (24, 10), (32, 34), (40, 10), (17, 18), (3, 10), (12, 9), (6, 38), (40, 9), (17, 33), (3, 35), (3, 11), (6, 10), (2, 34), (12, 44), (17, 20), (3, 33), (8, 9), (6, 34), (40, 41), (6, 18), (17, 25), (24, 56), (17, 9), (32, 33), (4, 20), (2, 18), (8, 10), (32, 36), (6, 7), (40, 42), (24, 48), (4, 36), (17, 49), (3, 34), (17, 5), (12, 20), (1, 33), (24, 9), (2, 10), (16, 48), (12, 10), (3, 18), (6, 20), (24, 20), (3, 7), (3, 9), (32, 48), (40, 56), (24, 26), (12, 13), (12, 36), (1, 9), (16, 20), (6, 14), (24, 29), (17, 48), (1, 25), (6, 36), (4, 13), (32, 52), (16, 26), (2, 14), (12, 30), (1, 13), (16, 36), (4, 48), (2, 26), (2, 19), (8, 56), (1, 7), (8, 44), (2, 50), (0, 5), (0, 18), (1, 37), (0, 20)]
def xsM := roots63.map (· &&& dom63)
def goalM := goal63 &&& dom63
def mpG := maskP pairsG.length
def NN : Nat → Nat
  | 3 => 1
  | 4 => 10
  | 5 => 273
  | 6 => 770
  | 7 => 279
  | 8 => 29
  | 9 => 1
  | _ => 0
def offset : Nat → Nat
  | 4 => 1
  | 5 => 11
  | 6 => 284
  | 7 => 0x41e
  | 8 => 0x535
  | 9 => 0x552
  | _ => 0
def wireAtBlock : Nat → Nat
  | 0 => (fromWords [0xf000f0, 0x550000, 0x300030, 0xf0000, 0xfcfc, 0xf0f0, 0x3030, 0xf0])
  | 1 => (fromWords [0xf0f0000, 0x5050000, 0xff00f0, 0xff00ee, 0xff00aa, 0xff0000, 0xfe00fe, 0xfc00fc])
  | 2 => (fromWords [0xafaf0000, 0x55555050, 0x55550000, 0x54545454, 0x33333030, 0x33332222, 0x30303030, 0xf0f0a0a])
  | 3 => (fromWords [0xff00ff00, 0xfefefefe, 0xfcfcfcfc, 0xf5f5f0f0, 0xf3f3f0f0, 0xf0fff0f0, 0xf0f0f0f0, 0xc0c0f0f0])
  | 4 => (fromWords [0xfffff0f0, 0xffffeeee, 0xffffaaaa, 0xffff5050, 0xffff3030, 0xffff00f0, 0xffff0000, 0xfffcfffc])
  | 5 => (fromWords [0xf0f00000a0a, 0xff000000f0, 0xff000000aa, 0xfffffff0, 0xffffffaa, 0xfffffefe, 0xfffffcfc, 0xfffffafa])
  | 6 => (fromWords [0x545400005454, 0x44440c0c4c4c, 0x333300003300, 0x333300003030, 0x333300002222, 0x303000003030, 0xf0f00000f00, 0xf0f00000c0c])
  | 7 => (fromWords [0xf0f000f0f0f0, 0xf0f00000f0f0, 0xdddd0000dcdc, 0xcccc0c0ccccc, 0xaaaa0a0aaaaa, 0x555500005500, 0x555500005050, 0x555500004444])
  | 8 => (fromWords [0xffff0000f0f0, 0xffff0000eeee, 0xffff0000dcdc, 0xffff0000cccc, 0xffff0000aaaa, 0xff000f00ff00, 0xfefe0000fefe, 0xfcfc0000fcfc])
  | 9 => (fromWords [0xffff0000fffc, 0xffff0000fff0, 0xffff0000ffcc, 0xffff0000ffaa, 0xffff0000ff00, 0xffff0000fefe, 0xffff0000fcfc, 0xffff0000fafa])
  | 10 => (fromWords [0xcc00cc00ff00ee, 0xaa00ff00aa00ee, 0xaa00fe00aa00fe, 0xaa00aa00fe00fe, 0x55005500550000, 0x33003300300030, 0xf000f000f0000, 0xf000f000c000c])
  | 11 => (fromWords [0xff00aa00ff00aa, 0xff000000ff0000, 0xfe00fe00fe00fe, 0xfc00fc00fc00fc, 0xf000f000f000f0, 0xee00ee00ee00ee, 0xcf00cf00ce00ce, 0xcf00ce00cf00ce])
  | 12 => (fromWords [0xff00ff00fc00fc, 0xff00ff00f000f0, 0xff00ff00ee00ee, 0xff00ff00cc00cc, 0xff00ff00aa00aa, 0xff00fe00ff00fe, 0xff00f000ff00f0, 0xff00ee00ff00ee])
  | 13 => (fromWords [0x303030302020202, 0x303020203030202, 0x20202020202aaaa, 0xff00ff00ff00f0, 0xff00ff00ff00ee, 0xff00ff00ff00aa, 0xff00ff00ff0000, 0xff00ff00fe00fe])
  | 14 => (fromWords [0xa0aaaaa0a00aaaa, 0xa0a0a0a0a0aaaaa, 0x505050505050000, 0x505050505000500, 0x505050504040404, 0x505000005050000, 0x303030303030000, 0x303030303000300])
  | 15 => (fromWords [0xf0f00000f0f0000, 0xf00ff000f00ff00, 0xf000f000f00ff00, 0xc0ccccc0c0ccccc, 0xc0ccccc0c0ccc0c, 0xc0c0c0c0c0ccccc, 0xb0b0b0b0b0b0a0a, 0xa0aaaaa0a0aaaaa])
  | 16 => (fromWords [0xf0f0f0f0f000f00, 0xf0f0f0f0e0e0e0e, 0xf0f0f0f0c0c0c0c, 0xf0f0f0f0b0b0a0a, 0xf0f0f0f0a0a0a0a, 0xf0f0e0e0f0f0e0e, 0xf0f0a0a0f0f0a0a, 0xf0f00000fff0000])
  | 17 => (fromWords [0xf0f0f0f0f0f0f0a, 0xf0f0f0f0f0f0f00, 0xf0f0f0f0f0f0e0e, 0xf0f0f0f0f0f0c0c, 0xf0f0f0f0f0f0a0a, 0xf0f0f0f0f0f0000, 0xf0f0f0f0f0c0f0c, 0xf0f0f0f0f0a0f0a])
  | 18 => (fromWords [0x3303330333033300, 0x3030303030303030, 0x1111111111110000, 0x1111111111001100, 0x1111111110101010, 0x1111101011111010, 0xf0fffff0f00ff00, 0xf0fffff00000000])
  | 19 => (fromWords [0x3333323233333232, 0x3333303033333030, 0x3333222233332222, 0x3333111133331100, 0x3333101033331010, 0x33330000f3f3f0f0, 0x3333000033333030, 0x3333000033330000])
  | 20 => (fromWords [0x3333333333330000, 0x3333333333303330, 0x3333333333223322, 0x3333333333033300, 0x3333333333003300, 0x3333333332323232, 0x3333333330303030, 0x3333333322222222])
  | 21 => (fromWords [0x50505050ffff5050, 0x5050505055555050, 0x5050505050505050, 0x3333333333333330, 0x3333333333333322, 0x3333333333333300, 0x3333333333333030, 0x3333333333332222])
  | 22 => (fromWords [0x5555555544444444, 0x5555545455555454, 0x5555505055555050, 0x5555000055550000, 0x5500555555005550, 0x5454545454545454, 0x5151515151505150, 0x5151505051515050])
  | 23 => (fromWords [0x5555555555550000, 0x5555555555545554, 0x5555555555505550, 0x5555555555445544, 0x5555555555005550, 0x5555555555005500, 0x5555555554545454, 0x5555555550505050])
  | 24 => (fromWords [0xaa00aaaaaa00aaaa, 0xaa00aa00aa00ff00, 0xa2a2a2a2a2a0a2a0, 0x7373505073735050, 0x5555555555555550, 0x5555555555555500, 0x5555555555555050, 0x5555555555554444])
  | 25 => (fromWords [0xaaaaaaaaaaaaaaa0, 0xaaaaaaaaaaa8aaa8, 0xaaaaaaaaaaa0aaaa, 0xaaaaaaaaaaa0aaa0, 0xaaaaaaaaaa00aaaa, 0xaaaa0000afaf0000, 0xaaaa0000aaff0000, 0xaa00ff00aa00ff00])
  | 26 => (fromWords [0xaaaafefeaaaafefe, 0xaaaaaaaafffffafa, 0xaaaaaaaaffffaaaa, 0xaaaaaaaafefefefe, 0xaaaaaaaaafafaaaa, 0xaaaaaaaaaaffaaaa, 0xaaaaaaaaaaafaaaa, 0xaaaaaaaaaaaaaaaa])
  | 27 => (fromWords [0xafaf0000afaf0000, 0xaaffaaffaaffaaaa, 0xaaffaaaaaaffaaaa, 0xaaaaffffaaaaffaa, 0xaaaaffffaaaafafa, 0xaaaaffffaaaaeeee, 0xaaaaffffaa00ff00, 0xaaaaffffa0a0f0f0])
  | 28 => (fromWords [0xb0b0b0b0b0b0a0a0, 0xafafafafafafaaaa, 0xafafafafafaf0000, 0xafafafafafaaafaa, 0xafafafafaf00af00, 0xafafafafaeaeaeae, 0xafafafaf8c8c8c8c, 0xafafaaaaafafaaaa])
  | 29 => (fromWords [0xc0c0f0f0c0c0f0f0, 0xc0c0c0c0c0f0c0f0, 0xc0c0c0c0c0c0f0f0, 0xbbbbbbbbbbbbaaaa, 0xbbbbbbbbbbaabbaa, 0xbbbbbbbbbabababa, 0xbbbbbababbbbbaba, 0xbbbbaaaabbbbaaaa])
  | 30 => (fromWords [0xccccccccccccccc0, 0xcccccccccccccc88, 0xcccccccccccccc0c, 0xcccccccccccccc00, 0xcccccccccc0ccc0c, 0xcccc4444cccc4400, 0xcc0ccc0ccc0ccc0c, 0xcc00cc00cf00cf00])
  | 31 => (fromWords [0xccccfcfcccccfcfc, 0xccccccccfffffcfc, 0xccccccccffffeeee, 0xccccccccfcfcfcfc, 0xccccccccccfcccfc, 0xccccccccccccfcfc, 0xccccccccccccccfc, 0xcccccccccccccccc])
  | 32 => (fromWords [0xccffccffccfcccfc, 0xccfcccfcccfcccfc, 0xccccffffccccffcc, 0xccccffffccccfcfc, 0xccccffffcccceeee, 0xccccffffcc00ff00, 0xccccffffc0c0f0f0, 0xccccffff8888aaaa])
  | 33 => (fromWords [0xdcdcdcdcdcdcdcdc, 0xcfcfcfcfcfcfcccc, 0xcfcfcfcfcfcf0000, 0xcfcfcfcfcfcccfcc, 0xcfcfcfcfcf00cf00, 0xcfcfcfcfcececece, 0xcfcfcececfcfcece, 0xcf00cf00cf00cf00])
  | 34 => (fromWords [0xeeeeeeeeeeeeeeee, 0xeeeeeeeeeeeceea0, 0xee00ee00ee00ee00, 0xddddddddddddcccc, 0xddddddddddccddcc, 0xdddddddddcdcdcdc, 0xdddddcdcdddddcdc, 0xdddd0000dcdc0000])
  | 35 => (fromWords [0xf0f0f0f0c0c0c0c0, 0xf0f0f0f0b0b0a0a0, 0xf0f0f0f00000f0f0, 0xf0f00000f5f50000, 0xf0f00000f0ff0000, 0xf0f00000f0f03030, 0xf0f00000f0f000f0, 0xf0f00000f0f00000])
  | 36 => (fromWords [0xf0f0f0f0f0f0f000, 0xf0f0f0f0f0f0e0e0, 0xf0f0f0f0f0f0c0c0, 0xf0f0f0f0f0f0a0a0, 0xf0f0f0f0f0f00000, 0xf0f0f0f0f0c0f0c0, 0xf0f0f0f0f000f0f0, 0xf0f0f0f0f000f000])
  | 37 => (fromWords [0xf0f0fffff000ff00, 0xf0f0ffffa0a0aaaa, 0xf0f0f0f0fffffafa, 0xf0f0f0f0fffff0f0, 0xf0f0f0f0f5f5f0f0, 0xf0f0f0f0f0fff0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0a0])
  | 38 => (fromWords [0xf3f3f2f2f3f3f2f2, 0xf3f3f0f0f3f3f0f0, 0xf0fff0fff0fff0f0, 0xf0fff0fff0fcf0fc, 0xf0fff0f0f0fff0f0, 0xf0f0fffff0f0fff0, 0xf0f0fffff0f0fcfc, 0xf0f0fffff0f0fafa])
  | 39 => (fromWords [0xfafaaaaafafaaaaa, 0xf5f5f5f5f5f5f0f0, 0xf5f5f5f5f5f0f5f0, 0xf5f5f5f5f4f4f4f4, 0xf5f5f0f0f5f5f0f0, 0xf3f3f3f3f3f3f0f0, 0xf3f3f3f3f3f0f3f0, 0xf3f3f3f3f2f2f2f2])
  | 40 => (fromWords [0xfcfca8a8fcfca8a8, 0xfbfbfafafbfbfafa, 0xfafffafafafffafa, 0xfafafffffa00ff00, 0xfafafafafffffafa, 0xfafafafafafafafa, 0xfafafafafafaaaaa, 0xfafaaaaafaffaaaa])
  | 41 => (fromWords [0xfcfcfcfcfcfcfcfc, 0xfcfcfcfcfcfccccc, 0xfcfcfcfcfcfc0000, 0xfcfcfcfcfcccfccc, 0xfcfcfcfcfc00fc00, 0xfcfcfcfca8a8a8a8, 0xfcfcccccfcfcccfc, 0xfcfcccccfcfccccc])
  | 42 => (fromWords [0xff00ff00ff05ff00, 0xff00ff00ff00ff30, 0xff00ff00ff00ff00, 0xff00ff00cf00cf00, 0xff00ff00aa00ff00, 0xfefefefefefefefe, 0xfefefefefefeaaaa, 0xfefefefefe00fe00])
  | 43 => (fromWords [0xff00ffffaa00aaaa, 0xff00ff33ff00ff30, 0xff00ff30ff00ff30, 0xff00ff00fffffff0, 0xff00ff00ffffffaa, 0xff00ff00fffcfffc, 0xff00ff00ff55ff00, 0xff00ff00ff30ff30])
  | 44 => (fromWords [0xff0fff0fff0f0000, 0xff0fff0fff0cff0c, 0xff0fff0fcc0ccc0c, 0xff05ff05ff05ff00, 0xff05ff00ff05ff00, 0xff00ffffff00fff0, 0xff00ffffff00ffaa, 0xff00fffff000f0f0])
  | 45 => (fromWords [0xff55ff55ff55ff00, 0xff55ff00ff55ff00, 0xff33ff33ff30ff30, 0xff30ff30ff30ff30, 0xff11ff11ff11ff00, 0xff11ff11ff10ff10, 0xff11ff10ff11ff10, 0xff0fff0fff0fff00])
  | 46 => (fromWords [0xfffcfffcfffcff00, 0xfff0fff0fff0fff0, 0xfff0fff0fff0ff00, 0xfff0ff00fff5ff00, 0xfff0ff00fff0ff30, 0xfff0ff00fff0ff00, 0xffccffccffccffcc, 0xffaaffaaffaaffaa])
  | 47 => (fromWords [0xffff0000fefe0000, 0xffff0000fcfc0000, 0xffff0000fafa0000, 0xffff0000f0f00000, 0xffff0000dcdc0000, 0xffff0000aaaa0000, 0xffff00000f0f0000, 0xfffcfffcfffcfffc])
  | 48 => (fromWords [0xffff0000ffff3030, 0xffff0000ffff00f0, 0xffff0000ffff0000, 0xffff0000fffc0000, 0xffff0000fff00000, 0xffff0000ffaa0000, 0xffff0000ff0f0000, 0xffff0000ff000000])
  | 49 => (fromWords [0xffff0f0fffff0a0a, 0xffff0f0fff000f00, 0xffff0f0fcccc0c0c, 0xffff00ffffff00f0, 0xffff00ffffff00aa, 0xffff00f0ffff00f0, 0xffff0000fffffcfc, 0xffff0000fffff0f0])
  | 50 => (fromWords [0xffff5454ffff5454, 0xffff5050ffff5050, 0xffff3333ffff3300, 0xffff3333ffff3030, 0xffff3333ffff2222, 0xffff3030ffff3030, 0xffff0f0fffff0f00, 0xffff0f0fffff0c0c])
  | 51 => (fromWords [0xffffaaaaffaaaaaa, 0xffffaaaaff00aa00, 0xffffaaaafafaaaaa, 0xffffaaaaf0f0a0a0, 0xffffaaaacccc8888, 0xffff5555ffff5500, 0xffff5555ffff5050, 0xffff5555ffff4444])
  | 52 => (fromWords [0xffffeeeefcfcecec, 0xffffdcdcffffdcdc, 0xffffcfcfff00cf00, 0xffffccfcffffccfc, 0xffffccccfffffcfc, 0xffffccccffffcccc, 0xffffccccfcfccccc, 0xffffaaaaffffaaaa])
  | 53 => (fromWords [0xfffff0f0ffffc0c0, 0xfffff0f0fff0f0f0, 0xfffff0f0ff00f000, 0xfffff0f0fafaf0f0, 0xfffff0f0ccccc0c0, 0xfffff0f0aaaaa0a0, 0xffffeeeeffffeeee, 0xffffeeeeff00ee00])
  | 54 => (fromWords [0xffffff00ffffff00, 0xffffff00fff0ff00, 0xfffffefefffffefe, 0xfffffefe00000000, 0xfffffcfcfffffcfc, 0xfffffafafffffafa, 0xfffff0f0fffff0f0, 0xfffff0f0fffff000])
  | 55 => (fromWords [0xffffffff0000f0f0, 0xffffffff00003030, 0xffffffff00000f00, 0xffffffff000000f0, 0xffffffff00000000, 0xfffffff0fffffff0, 0xffffffaaffffffaa, 0xffffffaafff0ffa0])
  | 56 => (fromWords [0xffffffff00fe00fe, 0xffffffff00fc00fc, 0xffffffff00f000f0, 0xffffffff00ee00ee, 0xffffffff00550000, 0xffffffff00300030, 0xffffffff000f0000, 0xffffffff0000fcfc])
  | 57 => (fromWords [0xffffffff0f0f0a0a, 0xffffffff0f0f0000, 0xffffffff0f00ff00, 0xffffffff05050000, 0xffffffff00ff00f0, 0xffffffff00ff00ee, 0xffffffff00ff00aa, 0xffffffff00ff0000])
  | 58 => (fromWords [0xffffffff55555050, 0xffffffff55550000, 0xffffffff54545454, 0xffffffff50505050, 0xffffffff33333030, 0xffffffff33332222, 0xffffffff33330000, 0xffffffff30303030])
  | 59 => (fromWords [0xffffffffc0c0f0f0, 0xffffffffbbbbaaaa, 0xffffffffafafaaaa, 0xffffffffafaf0000, 0xffffffffaaffaaaa, 0xffffffffaaff0000, 0xffffffffaaaaaaaa, 0xffffffffaa00ff00])
  | 60 => (fromWords [0xffffffffeeeeeeee, 0xffffffffee00ee00, 0xffffffffdcdcdcdc, 0xffffffffcf00cf00, 0xffffffffccfcccfc, 0xffffffffccccfcfc, 0xffffffffcccccccc, 0xffffffffc0f0c0f0])
  | 61 => (fromWords [0xfffffffffafafafa, 0xfffffffff5f5f0f0, 0xfffffffff3f3f0f0, 0xfffffffff0fff0f0, 0xfffffffff0ff0000, 0xfffffffff0f0f0f0, 0xfffffffff0f000f0, 0xfffffffff0f00000])
  | 62 => (fromWords [0xffffffffff30ff30, 0xffffffffff0fff00, 0xffffffffff05ff00, 0xffffffffff00fff0, 0xffffffffff00ff30, 0xffffffffff00ff00, 0xfffffffffefefefe, 0xfffffffffcfcfcfc])
  | 63 => (fromWords [0xfffffffffff0fff0, 0xfffffffffff0ff00, 0xffffffffffeeffee, 0xffffffffffccffcc, 0xffffffffffaaffaa, 0xffffffffff55ff00, 0xffffffffff50ff50, 0xffffffffff33ff00])
  | 64 => (fromWords [0xffffffffffffcccc, 0xffffffffffffaaaa, 0xffffffffffff5050, 0xffffffffffff3030, 0xffffffffffff00f0, 0xffffffffffff0000, 0xfffffffffffcfffc, 0xfffffffffffafffa])
  | 65 => (fromWords [0xfffffffffffffff0, 0xffffffffffffffcc, 0xffffffffffffffaa, 0xffffffffffffff00, 0xfffffffffffffcfc, 0xfffffffffffffafa, 0xfffffffffffff0f0, 0xffffffffffffeeee])
  | _ => 0
def wireAt (i : Nat) : Nat := fld (wireAtBlock (i / 8)) 64 (i % 8)
def stateWireBlock : Nat → Nat
  | 0 => (fromWords [0x129341ea61555544, 0xf87c9e1615292c5b, 0xb6c55551d177c9d9, 0x681293d1f2785855, 0x3ccc6ed854a4f433, 0x20269d554a4d0765, 0xa8615293e1f27658, 0x54a49c6ed854a516])
  | 1 => (fromWords [0x1f2765854a4f8355, 0xbb615444a4f8341f, 0x2785854a4d0101f2, 0x6ed854a4f82edf27, 0x2d854a4f8341bb6c, 0x5a05554f45dbb615, 0x293e0d0025bb6155, 0x54a4d02ade161550])
  | 2 => (fromWords [0x14c4a4d07c9e1615, 0x293ecd07c9bb6152, 0x93e0d1809ea64955, 0x3e0d07c9d9679854, 0xa4f86ed855552945, 0xcc46eda8615293e0, 0xd07c9d9615293e0c, 0x26ed85555293e0d0])
  | 3 => (fromWords [0x1f27659a615293e2, 0x2785a955529341f, 0x2765854a4f83a1ff, 0x6ed853e0ba2b5bb6, 0x156a4a4f8341bb68, 0x15f555293e1f2785, 0x854a50f341f26ed8, 0x54a4f8339f278585])
  | 4 => (fromWords [0x1293e0d07c9e1615, 0x4f340077c9bb6152, 0x93e0b16ed7f55529, 0x3e0d07c9d9615293, 0xe0817c9e16152934, 0x356ed85554f8340, 0x846ed85555293409, 0x7791e1615293e0d0])
  | 5 => (fromWords [0x1bb615504a4f8342, 0x27a9553e0d0279b, 0xb615574a4f8341f2, 0x765a9615293e1f27, 0x857e4a4f8341bb55, 0x54f340440f9f2785, 0x854a4d0299bb5ed5, 0x54a4f8341f36ed85])
  | 6 => (fromWords [0xf8340206ed854a4, 0xf8340587c9db6152, 0x93e0d27c9293e0d0, 0x2d0277c9854a4f83, 0x40137a9d96c98555, 0x4f8831bb4a4d028c, 0x986eda7615554a4d, 0x7c9d96c9854a4f8])
  | 7 => (fromWords [0x1f2765854a517261, 0xf7785854a4f8341f, 0x2709854a4f8341f2, 0x765854a4d02a9bb5, 0xf9554a4f8341f278, 0xd854a506341f278d, 0x854a4f8341bb6157, 0x44a4f8341f261529])
  | 8 => (fromWords [0xf8340577c9db615, 0x293e0dd7e9bb6152, 0x93e0d07f9bb61529, 0x3e0d07c9e3615293, 0xecd07c9d9615293e, 0xbd7c9d9681293e0, 0x5e809ea6c9553e0d, 0x6ed85555293e0c3])
  | 9 => (fromWords [0x1f2765854a4f81d1, 0xff7c9e16154f341e, 0xa759b1554f8341bb, 0x6155551d2945e0c6, 0xed854a4f8331f276, 0x59f615293e1f2765, 0x854a4f8381f27818, 0x54a4f8341bb61529])
  | 10 => (fromWords [0x1293e0cf7c9e1615, 0x29340aa7c9c36152, 0x93e0d0831bb4a4f8, 0x364d06ed855bd293, 0xe0d06ed855dd293e, 0xd07c9bb61529340, 0xab6ed85591293e0d, 0x6eda0554f820c7f])
  | 11 => (fromWords [0x1f2785854e529341, 0xbb615293e0d0189f, 0x27858553cd016df2, 0x6ed854a4f81ddf27, 0x158553cf8341ea76, 0x5b1681553e1ea615, 0x55508f810df2765b, 0x1681293e1f26ed85])
  | 12 => (fromWords [0x14a3e0d07c9854a4, 0xf83401c7a9d96155, 0x5548f87c9e161529, 0x3e0bd809ea681555, 0x8f87c9d9615524a, 0x4f87c9d9615293e0, 0x3a809b1554f8340a, 0x1809ea659553e0d0])
  | 13 => (fromWords [0x1bb615564a4f8341, 0xf2725854a4f8341f, 0x2615293e0d00b1ea, 0x61555534f8341f26, 0xed854a4fb341bb61, 0x5554a4f82cdbb615, 0x734a4f8341bb6155, 0x53e0d023dea61555])
  | 14 => (fromWords [0x129340ac7c9e1615, 0x293fcd0809d06c55, 0x53e0d07c9e16cd85, 0x4a4d07c9d9615243, 0xe0d07c9bc615293e, 0xd07f1f2765854a5, 0x177c9c8681293e0d, 0x809f06c5553e0d0])
  | 15 => (fromWords [0x1f2705854a4f8341, 0xf2615293e0d00adf, 0x2615293e0d009df2, 0x79d8553d29341f26, 0x154f3e0d009dbb61, 0x5293e0d0155f2785, 0x854a4fc341f26ed8, 0x54a4f7341bb61555])
  | 16 => (fromWords [0x1293e0d0809ea555, 0x3b3e0d06ed854a4f, 0x83304b7c9e161529, 0x340b27c9d9615293, 0xe0d27c9e14a4f834, 0x498099b555293e0, 0xd071dbb615293e0d, 0x809ea554f8340b5])
  | 17 => (fromWords [0x1bb615553e0e7341, 0xf2615293e0d006df, 0x26ed854a4f830df2, 0x785854a4d0251bb6, 0x15293e0d01a2027a, 0x9554d8f8341f2769, 0x854a4f8341ff7c9d, 0x9615423e1f26ad85])
  | 18 => (fromWords [0x15553cd07c9854a4, 0xf8340166ed85554f, 0x83408d7c9bb61529, 0x340a47c9e16c5855, 0x3cd0809a25552934, 0x856ed554a4f8340, 0x497c9db615293e0d, 0x6eda5615293e0d0])
  | 19 => (fromWords [0x1bb615554a4f82f9, 0xf26f5854a4f8341f, 0x2765854a4f8375bb, 0x6155e4a4f8341f76, 0xed854a4f8341fb7c, 0x9e16152945df2765, 0x854a5133e1f26ed8, 0x54a4f9342027a9a2])
  | 20 => (fromWords [0x1293e0cc7c9c6615, 0x293e0d06ed554a4f, 0x8340457d5bb61529, 0x3e0d06ed85555244, 0x5cf86ed554a4f834, 0x4f7c9bb681293d0, 0xd06ed85555243e0d, 0x7c9bb615404a4f8])
  | 21 => (fromWords [0x1bb6c55551cf8341, 0xbb67585555293e1b, 0xb615293e0d0165bb, 0x6156b4a4f8341f26, 0xed854a4f5341d976, 0x1854a4f83420c7c9, 0xd9681293e1bb6155, 0x54a4f81b5f278585])
  | 22 => (fromWords [0x11e3e0d06ed854a4, 0xf8340567c9bb6152, 0x93d8d07c9bb61529, 0x3c8d07c9bb614f83, 0x408f7c9bb6152934, 0xaa6ed855554e4a4, 0xd07c9bb615283e0d, 0x7c9bb615293e0cd])
  | 23 => (fromWords [0x1f26ed854a4f82f5, 0xca6ed854a4f8341f, 0x2785a06152945dbb, 0x6e1854a4f8341bb6, 0x156d4a4f83420278, 0x5b355529341f2785, 0x8552d29341bb6152, 0x93d0d021dbb61555])
  | 24 => (fromWords [0x13d4a4f87c9d9615, 0x293d0d07c9e76818, 0x54a4f87c9e161529, 0x45cad7c9bb615293, 0x407b6ed855552934, 0x9c7c9bb61529340, 0xac7c9d9614f83408, 0xb615554a4f83402a])
  | 25 => (fromWords [0x1f2785855d94f341, 0xb4615554a4f8341b, 0xb615655554f341f2, 0x6a9854a4f8341f27, 0x65a04a4f8029bb61, 0x5553e0d01e5f2785, 0x854a4d0295bb5f95, 0x54a517341f276585])
  | 26 => (fromWords [0x1854a4d07e9d9615, 0x293e0d07a9d96155, 0x553d177c9d96154f, 0x4a517831e1615293, 0x40a3831f2785a24a, 0x4d07c9e9615293e0, 0xd07c9d9615293e0b, 0xc7c9854a4f834023])
  | 27 => (fromWords [0x1f2765a04a4f81fe, 0x27a9b3554f83420, 0x67a985555423e202, 0x785b15554f341bb6, 0x15554a4f82c5f26e, 0xd854a4f8315ff765, 0x854a4f82e9ea6c55, 0x53e0d02fdf2785a9])
  | 28 => (fromWords [0xf83408b7fdbb615, 0xb3e0d07c9bb4a4f, 0x83404f819ea6c555, 0x3e0d07c9d9615293, 0xe0947c9853e0d025, 0x8277c9bb615293e0, 0xbe6ed85555263e0d, 0x7c9a04a4f834027])
  | 29 => (fromWords [0x1f26ed8553cf8331, 0xf2615293e0d00a5b, 0xb555293e0d0129bb, 0x615694a4f8341f26, 0x15293e0d6341bb61, 0x5554a4d00d9f2615, 0x293e0d00a1bb6152, 0x93e0d0151bb61555])
  | 30 => (fromWords [0x129340707c98553d, 0x29340b78099c5552, 0x93e0d07c9854a4f8, 0x340247c9e16154f3, 0x403e7c9854a4fe3e, 0xd07c9bb611293e0, 0xd07c9e1615293acd, 0x7c9bb615494a4d0])
  | 31 => (fromWords [0x1f27859561529341, 0xf2785854a5063420, 0x27c1a255529341bb, 0x615293e0d01adbb5, 0x5529440f8341f26e, 0xd854a4f8349bb615, 0x293e0d0031f27658, 0x54a4f8275f278585])
  | 32 => (fromWords [0x1293d0d07c9d96dd, 0xa04a4f87c9bb6152, 0x93409c6ed554a4f8, 0x3403d7c9eb615293, 0xe0d07c9a0615293e, 0xa0809ea6c5553e0, 0xd06ed85555514a4f, 0x8809e1681554a517])
  | 33 => (fromWords [0xd07c9bb615293e0, 0xd0205f27a1854a4f, 0x8341f26ed855d94f, 0x3e0d0835f26ed854, 0xa4f8341d56ed8555, 0x5293e0d07c9d9689, 0x854a4f8341f27858, 0x554929341ff6ed85])
  | 34 => (fromWords [0x1554a4f834028809, 0xbb615293e0d016a0, 0x2785855552945cd0, 0x6ed855552945cf82, 0xd5bb615554b1293e, 0xd06ed855554f3e0, 0xd0009f2615293e0d, 0x2ddcd6ed854a4f8])
  | 35 => (fromWords [0xd6341f26ed854a4, 0xf8375f97c9bb6152, 0x93e0d06ed9761555, 0x4a4f83420c6ed854, 0xa4f8340a36ed8555, 0x5293e0d0831f26ed, 0xa24a4f8341e16ed8, 0x5561293e0d06ed85])
  | 36 => (fromWords [0x1293e0d3341bb615, 0x554a4f8340c0839f, 0x26ed854a4f8341bb, 0x615764a4f8340646, 0xed7e5554f4a4f834, 0x1bb615554a4f8340, 0x2d6ed85555293e0d, 0xa5bb615554a4f8])
  | 37 => (fromWords [0x1f2785855554f4a4, 0xd07c9bb61529340a, 0x3261cf6ed8555529, 0x3e0d07a9ce615554, 0xa4f8341f2765a061, 0x5293e1ea74585555, 0x293e0d07c9d96dd8, 0x54a4f8341bb61555])
  | 38 => (fromWords [0x15553cd00f9bb6c5, 0x85554f8340116edb, 0x1615553f0f8341bb, 0x615554a4fe3e0d06, 0xedb16155553d1734, 0x1f26eda9615293e0, 0xd0799854a4f8341b, 0xb615554ad293e0d0])
  | 39 => (fromWords [0x7711bb615293e0, 0xd0789bb615554a4f, 0x8341d86ed854a4f8, 0x341bb615554a4f83, 0x400d6ed85555293e, 0xd0239bb615554a4, 0xf8340246ed855552, 0x945cad261e16ed85])
  | 40 => (fromWords [0x1293e0d0821bb615, 0x554a4f8341bb6155, 0x54a4f8340c1765bb, 0x615554a4f8275f26, 0xed854a5193e0d06e, 0xd9d615554a4f8341, 0xbb6155553d29340b, 0x77c9e1615293e0d0])
  | 41 => (fromWords [0x1854a4f8390d06ed, 0x85555293e0d026df, 0x26ed854a9293e0d0, 0x7c9d9615293e0d00, 0x55ea6edb2615553e, 0xd06ed85555293e0, 0xd0041f26ed854a4f, 0x8340057c9bb6c985])
  | 42 => (fromWords [0x427c9bb615293cc, 0xd0809bb6c55553cf, 0x8341bb681854a4f8, 0x340607c9bb681854, 0xa4f82e9bb555293e, 0xd01103e6ed85555, 0x293e0d0089bb6155, 0x54a4f835cd07c9bb])
  | 43 => (fromWords [0x1bb615554a4f8341, 0xf276585509293e20, 0x26ed554a4f837cd0, 0x6ed8557d554a4f83, 0x420c7c9bb615293e, 0xd07c1bb555293e0, 0xd0125f26ed854fd2, 0x93e1bb615293e0d0])
  | 44 => (fromWords [0xf8341bb615554a4, 0xf83b4d0809bb6c55, 0x54a4f8341f26ed85, 0x4a4f82e8ad7a9d96, 0x1555508f8785bb61, 0x5554a506341bb615, 0x554a4f8340a67c9b, 0xb61529408f8341ec])
  | 45 => (fromWords [0x1a0555293e1f06ed, 0x855552945cd0815b, 0xb615554a4f8341d3, 0x6ed85555293e0d08, 0x9bb629554a4f834, 0x1bb68185555293e0, 0xa06ed85555293e0d, 0xbdff7c9d961529])
  | 46 => (fromWords [0x1bb555293e0d0275, 0xf26ed854a4f8370d, 0x7a9bb6156e4a4f8, 0x341ff6ed854a4f83, 0x404b785bb6155554, 0x9293420c7f1bb615, 0x293e0d06ed855552, 0x9400f8341d96edb7])
  | 47 => (fromWords [0x5e785bb615554a4, 0xd0101f2765854a4f, 0x83409872dbb61555, 0x4a4f8341f26ed854, 0xa51734098825bb61, 0x55553cf8341bb6cd, 0x85555293409e6ed8, 0x5555293e0d00de02])
  | 48 => (fromWords [0x1554a4f83420c6ed, 0x8555529340aa6ed8, 0x55554f3e0d020e09, 0x6ed85555293e0d07, 0xc9bb615293e0c776, 0x5bb615554a4f8355, 0xf26ed854a4f8340b, 0xd7c9bb681293e0d0])
  | 49 => (fromWords [0x1bb615554a4f8340, 0xa96eda0615555492, 0x93e2026ed8555529, 0x340aa7c9bb615293, 0xc4d0831f26ed293e, 0xd0261bb6b585555, 0x293e0d07c9bb6152, 0x93e0d0246026ed92])
  | 50 => (fromWords [0x1553e0d07c9bb615, 0x293d0d07c9bb6152, 0x93e0e0341bb6155b, 0x555293e0d06ed855, 0x55293e0d01c5bb61, 0x5554a4f8340127c9, 0xbb659854a4f8341c, 0xc6ed85555293e0d0])
  | 51 => (fromWords [0x1a0615554a4f87c9, 0xbb67d854a4f8341e, 0x16ed855552943cd0, 0x6edb1615553e0d02, 0x85bb615554a4f834, 0x537c9bb615293e0, 0xeb341f26ed854a4f, 0x8364d07a9bb65985])
  | 52 => (fromWords [0xb5765bb615554a4, 0xf83a1f26eda06154, 0x24a4f87c9bb6154f, 0x3e0d00f9bb5f9554, 0xa4f8341bb6a5854a, 0x4f8340606ed85555, 0x293e0d0131ff7c9b, 0xb615293e0cc7c9d9])
  | 53 => (fromWords [0xf83408a6ed85555, 0x384a4f8341bb6998, 0x5555293e0d07c9bb, 0x615293e0d01d1f26, 0xed854a4f8340706e, 0xd85555474a4f8341, 0xea6eda061555508f, 0x86eda0615554a4f8])
  | 54 => (fromWords [0x1bb615554a4f80ed, 0xbb68185555243e0d, 0x809ea6c585554f8, 0x341bb615554a5173, 0xe0437c9e1689854a, 0x4d06ed85555293e0, 0xd019df26ed854a4f, 0x83403f6ed855d955])
  | 55 => (fromWords [0xd0225f26edb1681, 0x293e0d06ed855553, 0x63e0d0065bb62185, 0x5554f3e0d0831bb6, 0x81554a4f8341f276, 0x5854a4f8340a36ed, 0x8b615554a4f8341b, 0xb615554dd293e0d0])
  | 56 => (fromWords [0x1853e0d0259f26ed, 0x854a4f8340617a9b, 0xb6c5a0554f8341bb, 0x615554a5173409e7, 0xfdf2785854a4f834, 0x1d96ed85555293e0, 0x8179dbb615293e0d, 0x195bb615554a4f8])
  | 57 => (fromWords [0x1f26ed95615293e0, 0xd06ed88615554a4f, 0x8341f26ed854a506, 0x3e0d07f9bb615293, 0xe0d06ed85555293e, 0xd01b9bb615554a5, 0xc3e0d07c1bb6c58, 0x5554f8341f26edb1])
  | 58 => (fromWords [0x1293e0d00e9d06ed, 0xb1615553e0d07e9b, 0xb615293e0d06ed85, 0x555293e0d009a026, 0xc5554a4f8340276e, 0xda1615554a4d0809, 0xbb681554a5173e1f, 0x16ed85555293e0d0])
  | 59 => (fromWords [0x1bb6155553cf8341, 0xf26ed85549293e0d, 0x785bb5f9554a4f8, 0x342066ed85555243, 0xe0d0809bb555293e, 0xe8341bb68985555, 0x2943cd06edb25552, 0x93e0d0085f26ed85])
  | 60 => (fromWords [0x5b809bb555293e0, 0xd0279ea6ed855555, 0x23e0d0785d061555, 0x4a4f8341bb615554, 0xf9293e0d06edb161, 0x55553cd0279d96ed, 0xa9615554a4f87c9b, 0xb639854a4f8341ff])
  | 61 => (fromWords [0x1293e0d07a9bb615, 0x553e0d0101d96edb, 0x2615554a4f87c9bb, 0x615293e0d0101bb6, 0x89855554f3401980, 0x9ea555293e0d02d1, 0xf2765854a4f83405, 0xe7c9e1615293e0d0])
  | 62 => (fromWords [0x185555293e0d06ed, 0x855a1554a4f8341f, 0x26ed854a4f8340b5, 0x6ed85555293e0d00, 0x8209615554a4f834, 0x276ed554a4f8340, 0xb409dbb615554a4f, 0x83401383df26ed85])
  | 63 => (fromWords [0x827a9bb615553e0, 0xd02d5e36ed855552, 0x9418d06eda055529, 0x3e0d01a5f26ed854, 0xa4fb3e0d06ed855b, 0xd293e0d0809bb555, 0x293e0d0205bb6155, 0xc555293e0d078dbb])
  | 64 => (fromWords [0x12c3e0d07f1f26ed, 0x854a517341f26ed8, 0x5531293e0d06ed85, 0x5554f4a4d028df26, 0xed854a5053e0d06e, 0xd85555394a4f8341, 0xf26edb0615293e0d, 0x6ed85555293e0d0])
  | 65 => (fromWords [0x1bb6dd854a4f8341, 0xfc7c9d9615293e0d, 0x7c9bb6152943cf8, 0x341bb6c985555293, 0xe0b56ed9b615554a, 0x4f8341f26ed854a5, 0x6341fb6ed854a4f, 0x8340877a9bb61555])
  | 66 => (fromWords [0xd06ed85555293e0, 0xd00cdbb615554a4f, 0x8340867c9bb6153b, 0x4a4f8341ea6ed855, 0x550f3e0d06ed8555, 0x5293e0d0231bb6dd, 0x854a4f8340637a98, 0x5555293e0d009dff])
  | 67 => (fromWords [0x1293e0d06ed85554, 0xf8340831fdbb6155, 0x553d29340447c9bb, 0x615364a4f8341bb6, 0x15554c9293e0d07a, 0x9bb615554ecf8341, 0xbb615554a4f83405, 0x6ed855552d4a4f8])
  | 68 => (fromWords [0x1554a4f8340756ed, 0x8555529448f8341b, 0xe6ed85555293e0d0, 0x7f1bb615293e0d01, 0x2dea6ed85555363e, 0xd0809bb6a5554a4, 0xf8341bb615554a4f, 0x8350d0809bf61555])
  | 69 => (fromWords [0x98809bb6c9554a4, 0xf8341d96ed8554d2, 0x93e0d06ed8555529, 0x3e0d00c5f2715854, 0xa4f8341ea6ed7e55, 0x5293e0d07c9bb615, 0x293e0d0035f26ed8, 0x54a4f83408e6ed85])
  | 70 => (fromWords [0xf8340b96ed855f5, 0x554a4f8342027a98, 0x5554f8340ad6ed85, 0x555293e0d0121f27, 0x85854a4f8340116e, 0xda0615554a4f820d, 0xbb615554a4fa3e0d, 0x765bb615554a517])
  | 71 => (fromWords [0x1b1615553e0d06ed, 0xba615293e0d01860, 0x27a9554a4f83407f, 0x6ed96555293e0d00, 0x85ff7c9bb614f834, 0xad765bb681554a4, 0xf8179f2765b16152, 0x93e0d06ed8555529])
  | 72 => (fromWords [0xd0215bb615554a4, 0xf81d9db6ed855552, 0x93e0dd6ed8555529, 0x3e0d02c1bb615554, 0xa4f8340ca7c9bb61, 0x5293e0d00d5bb615, 0x554a4d02aa016ed8, 0x5555293e0d07a9d9])
  | 73 => (fromWords [0x18553cf834007831, 0xbb615764a4f83420, 0x26ed85555243e0d0, 0x6ed5553d293e0d01, 0x25ea6ed854a4f834, 0x5a6ed85555293e0, 0xd01a9f26ed854a4f, 0xb341bb6898555529])
  | 74 => (fromWords [0x20b6ed85555293e0, 0xd07a985555293e0d, 0x2fdf26ed854a4f8, 0x340a67c9bb689855, 0x3d29341fd7c9bb61, 0x5293e0d06ed85555, 0x29428f8341bb6815, 0x5509293e0217c9bb])
  | 75 => (fromWords [0x1293e0d06ed8554d, 0x293e0d0765bb6155, 0x54a4f8381bb61555, 0x4a5073e0d07c9bb6, 0x15293e0d2341ea6e, 0xda26155553cd075d, 0xbb615554a4f8341b, 0xb615554a51a3e0d0])
  | 76 => (fromWords [0x1855554f4a4d0759, 0xbb6c5554a4f8341b, 0xb615554a5143e0d0, 0x6eda0555293e0d01, 0x1bb615554a4f834, 0x6c7fdf26ed85508, 0xf8342027a9855554, 0x23e0d06ed8555535])
  | 77 => (fromWords [0x1293e0d081dbb615, 0x5553d29342026ed5, 0x54a517340986ed85, 0x551293e0d0811bb6, 0x15554a4f8341f278, 0x5854a4d028dbb615, 0x554a4f82f5bb6155, 0x54f1293e0d0809e1])
  | 78 => (fromWords [0x1f26ed854a4d02a9, 0xbb615554a4f8360d, 0x6ed85555293e0d0, 0x21f26edb9615293, 0xe0d0791bb615293e, 0xd07b5bb615554a4, 0xf8341bb681554b12, 0x93e0d0749bb61555])
  | 79 => (fromWords [0xd06ed855553a4a4, 0xf8341bb615554a4f, 0x8340937c9bb61529, 0x3e0d0325bb6154f4, 0xa4f83405d765bb6c, 0x5a0555293e1f26ed, 0xad615293e0d06ed8, 0x5555424a4f810e0c])
  | 80 => (fromWords [0x18558d293e0d081d, 0xf2785854a4f8341d, 0xe6ed85555293e0d0, 0x7c9854a4f8340277, 0x15bb6155553cf834, 0x2067a985555293e0, 0xd06ed854a4f83406, 0x6ed855bd554a4f8])
  | 81 => (fromWords [0xf8341f26ed854a5, 0x133e0d0809bb5552, 0x93e0e0341f26ed85, 0x4a5213e0d06eda26, 0x15554a4d0076026e, 0xd96555293e0d0799, 0xbb615293e0d0785b, 0xb6155553cd016dbb])
  | 82 => (fromWords [0x12942cf8341bb6c5, 0xa0555293e0b57c9b, 0xb615293e0dd34202, 0x6eda0555424a4f87, 0xc9bb615293e0d013, 0x1bb615554a4f8340, 0x4e7edf2785854a4f, 0x8341f27bdd961529])
  | 83 => (fromWords [0x1bb555293e0d02d4, 0x217c9bb615293e0d, 0x1c9bb615554a501, 0x3e0d07c9e16c5854, 0xa4f8341d96ed8555, 0x5524a4f87c9e7765, 0x854a4f8341f26ed8, 0x54a4f8340006ed85])
  | 84 => (fromWords [0xf8340886ed85555, 0x4d4a4f8341bb6156, 0x7555293e0d0809ea, 0x689554a4f8341bb6, 0x15554a4f83401c78, 0x5bb615544a4f8342, 0x2785a255529341b, 0xb61555529293e0d0])
  | 85 => (fromWords [0x1e16152945cd0819, 0xbb555293e0d01fdb, 0xb615554a4f83402c, 0x6ed855552e4a4f83, 0x420c7c9bb681293e, 0xd07d1f26ed854a4, 0xf8341bb681554a4f, 0x83400f7c9bb61529])
  | 86 => (fromWords [0xd0809bb6c5553e0, 0xd0259f26ed854a4f, 0x834089725bb61555, 0x4a4f8341bb681855, 0x54f83408b809bb61, 0x56c4a4f8341f2765, 0x85601293e0d06ed9, 0x1615554a4f8341f2])
  | 87 => (fromWords [0x1855552934202615, 0x554a4f834085765b, 0xb61555490f8341f2, 0x79d854a4f8341bb6, 0xc5554a4f8340157c, 0x9bb61529430f8341, 0xbb615554a4f83403, 0x4721bb681554a4f8])
  | 88 => (fromWords [0x1f27c1e1615293e0, 0xd06ed99615554a4f, 0x8342067c9d961529, 0x3e0d07c9bb6c5293, 0xe0d02d1bb6618555, 0x5293e0d06ed85555, 0x293e0d002dbb5552, 0x93e0d0125e16edb3])
  | 89 => (fromWords [0xf8341d96ed854a4, 0xf8340657a9bb6155, 0x54ccf8342027a985, 0x5554f3e0d06ed855, 0x55293e0d00e1f26e, 0xd854cd293e0d07a9, 0xbb6c5553e0d02d1e, 0x16ed85555293fcd0])
  | 90 => (fromWords [0x1554a4f8341e16ed, 0x85555293f0d06ed8, 0x5549293e0d0175bb, 0x6bd85555293e0d07, 0x51bb615554a5173e, 0x1f26ed854bd293e0, 0xd06ed855552945cf, 0x8095ff7c9bb6154f])
  | 91 => (fromWords [0x2096ed85554f8340, 0x96819bb615553e0d, 0x22dbb6cd85554f8, 0x340196eda4615554, 0xa506341f2785854a, 0x4f8340ba7ddbb615, 0x293e0d06ed855554, 0xf3e0d009e096eda0])
  | 92 => (fromWords [0xd00adbb62585555, 0x293e0d06ed855552, 0x93e0d02d9e76ed85, 0x5554f4a4d06ed855, 0x554e4a4f8341ff7c, 0x9bb615293e0d06ed, 0x85555293e0d0149e, 0xa6ed85555293e0bd])
  | 93 => (fromWords [0x1554a4f8340737c1, 0xbb615554a4f83420, 0x26ed554a4f8340b5, 0x6ed85555243e0d06, 0xed85555293e0d003, 0x9bb615554d92945c, 0xd07c9bb615293e0d, 0x2a9bb615554a4f8])
  | 94 => (fromWords [0x1bb6155550d293e0, 0xd07c9e161529480f, 0x8341f26ed854a51b, 0x3e0d07c9bb615394, 0xa4f8341f26ed8553, 0xcf83405b6ed855d9, 0x293e0d012dbb6818, 0x55554f4a5176ed85])
  | 95 => (fromWords [0x1293e0d01260c6ed, 0x854a4f8340877c9e, 0x7785854a4f8341bb, 0x615293e0d0196027, 0xa985554f83403e7c, 0x985555293e0d009d, 0xbb615293e0d0175f, 0x26ed8553d29340a3])
  | 96 => (fromWords [0x185585554a4f8341, 0xe16ed8555529340b, 0x26ed85555293e0e9, 0x342026ed554ed293, 0xe0d07c9e1681854a, 0x4f8341bb615554a4, 0xf83402e6edb75552, 0x93e0d011de16ed55])
  | 97 => (fromWords [0xd02b9f06ed85554, 0xf83403e6ed855554, 0xf4a4d0279f26ed85, 0x4a4f83b8d07c9bb6, 0x15324a4f8342026e, 0xd554d9293e0d06ed, 0xab615554a4f8341b, 0xb67585555293e1bb])
  | 98 => (fromWords [0x14f3e0d011dbb615, 0x554a51c3e0d07c9e, 0x1615293e0d02b602, 0x7a9554a4f8340987, 0xfdfb6ed854a4f834, 0x1bb64d85555293e0, 0xd07c9bb6153d4a4f, 0x8341bb615554a4f8])
  | 99 => (fromWords [0x185555293e0d0309, 0xbb63185555293e0d, 0x7c9bb615834a4f8, 0x3420c7c9d9615293, 0xe0d06ed85555293e, 0xd0061bb68985555, 0x293f0d07c9bb6152, 0x93e0d00c5bb61555])
  | 100 => (fromWords [0x1293e0d06ed85555, 0x293e0ec341f26eda, 0x4a4f83400a7c9bb, 0x61529340aa805f26, 0xed854a4f8341bb67, 0x985555293e0d06ed, 0x85555293e0d006db, 0xb6155553929341bb])
  | 101 => (fromWords [0x185555293e0bd785, 0xbb6c5855554f341b, 0xb6155552d293e0d0, 0x765d6615554a4f83, 0x41f26ed854a4f834, 0x4d829bb615554a4, 0xf8341bb615554a50, 0x93e0d076dbb61555])
  | 102 => (fromWords [0x1bb615554a5253e0, 0xd0809bb6895553d2, 0x9341f26ed854a4f8, 0x340bc7c9bb615814, 0xa4f8341f26edb361, 0x5293e0d06edb5615, 0x554a4f8341f27858, 0x5509293e0d07fdbb])
  | 103 => (fromWords [0x117340857c9bb615, 0x293e0cb6ed946155, 0x54a4f8341f26ed85, 0x4a4ff3e0d07f9f26, 0xed854a4f8341e16e, 0xd854a4f8340657a9, 0xbb6cd85554f8341b, 0xb615554a4f834016])
  | 104 => (fromWords [0x1bb615293e0d0019, 0xfa7c9bb615293e0d, 0x6eda96155553d29, 0x341ea6ed85554ff3, 0xe0d06ed85555293e, 0xde342026ed85554, 0xf83408b6edb66152, 0x93e0d06ed8555529])
  | 105 => (fromWords [0xf8341bb6156d4a4, 0xf8341d96ed855552, 0x93e0dd6ed8559555, 0x4a4f8341bb635855, 0x55293e0d07c9bb61, 0x54f4a517341ea6ed, 0x554a4f8340496ed8, 0x5555293e0d0105f2])
  | 106 => (fromWords [0x1855554f3e0d07c9, 0xbb615293e0bd77db, 0xb615554a4f8341f2, 0x7658553d293e0d07, 0xc9bb6152949cf834, 0x1bb66985555293e0, 0xd07a9bb6155553d1, 0x7341f2785855d929])
  | 107 => (fromWords [0xd0819bb615554a4, 0xf8341bb615293e0d, 0x1f5bb615554a4f8, 0x340016edac615554, 0xa4f8341bb6418555, 0x5293e0d06ed85555, 0x293e0e1341ce6eda, 0x555293e0d07a9d9])
  | 108 => (fromWords [0x1855552945cf86ed, 0x854a4f8340917fdb, 0xb615293e0d02e9f2, 0x6ed854a4f8340087, 0x19bb615554a4f834, 0x1bb615293e0d0319, 0xbb6155553cf83408, 0x1795bb615554a4f8])
  | 109 => (fromWords [0xe3341bb6c5854a4, 0xf83405a7a9d96155, 0x54a5173e1e861555, 0x4a4f8341c06ed855, 0x55293e0d0835bb61, 0x5554a4f8341f26ed, 0x854a4d01f1bb6155, 0x54a4f8340af819bb])
  | 110 => (fromWords [0x1bb615554a4f8341, 0xf26eda04a4f83407, 0xf7b9bb615554a4f8, 0x341bb615293e0d93, 0x41bb615554a4f834, 0x8b7c9bb619854a4, 0xf8341bb615554a4d, 0xf1f26ed854a4f8])
  | 111 => (fromWords [0xd0125f26ed854a4, 0xf83404e6ed855554, 0x14a4f86ed8555529, 0x3e0d0255bb681554, 0xa4f83408a7a9bb61, 0x5553e0d02c9f06ed, 0x7e555293e0d07c9b, 0xb615293e0d02c9dc])
  | 112 => (fromWords [0x1554a4f8342026ed, 0x554a4f834072809e, 0x16c5554a4f8341d9, 0x6ed85565293e0d07, 0xd9f26ed854a4f834, 0x1bb615554a517340, 0x1d831f2785854a4f, 0x8341bb615554a4f8])
  | 113 => (fromWords [0x185555424a4f8095, 0xf2765854a4f83400, 0xa6ed85554f83408a, 0x16dbb615554a50e3, 0xe0d07c9bb615293e, 0xd0251bb67185555, 0x293e0d06ed855552, 0x93e0d0289bb6155a])
  | 114 => (fromWords [0xf8341f26edb1615, 0x4f3e0d07c9854a4f, 0x8340a07c9bb61555, 0x4a4d02a9bb615554, 0xa4f8398d06eda061, 0x5554a4f82e9f2765, 0x854a4f8340877c9b, 0xb645854a4f8341bb])
  | 115 => (fromWords [0x1293e0d000e026ed, 0x88555293e0d06ed8, 0x5555293e0d005e0c, 0x7c9bb4a4f8340b46, 0xed85555293e0d007, 0x9bb615554c5293e0, 0xd06ed8f615554a4f, 0x8341bb615554c129])
  | 116 => (fromWords [0x1e16eda0615554a5, 0x176ed85555293e0d, 0x69f06eda261555, 0x4a4d07c9bb615294, 0x88f8341bb615594a, 0x4f8341fb7c9bb615, 0x2945cf87c9bb6152, 0x93e0df341bb61555])
  | 117 => (fromWords [0xf8340047a9bb6c5, 0x85554f8341bb6c55, 0x54a4f8340257bdbb, 0x68185555293e1bb6, 0x15293e0f0341f26e, 0xd854a4f83400b7c9, 0xbb6c5854a4f8341b, 0xb681554a4f834044])
  | 118 => (fromWords [0x185599554a4f8341, 0xbb6155d4a4f8341f, 0x26ed8a615293e0d0, 0x765bb615553e0d02, 0x2dd16ed855552945, 0xcd07c9bb615784a4, 0xf8342026ed855552, 0x9418d07c9bb61529])
  | 119 => (fromWords [0xf81e1bb615554a4, 0xf8370d06ed855b55, 0x54a4f8341bb61575, 0x4a4f8341e76eda06, 0x15554a4f86ed8555, 0x5293e0d00e5e16ed, 0x855552945cad6ed8, 0x5555293e0d027dbb])
  | 120 => (fromWords [0x1554a4f8394d06ed, 0x85555293e0d0249b, 0xb555293e0d017847, 0x7c9bb615293e0d02, 0x76027a9b1555293e, 0xd07c9d9615293e0, 0xd012df26ed855552, 0x93e0bd7c9bb61529])
  | 121 => (fromWords [0xb47c9d96152945c, 0xf86ed85555464a4f, 0x8341bb615554a4fd, 0x3e0d0809c5615554, 0xa4f8341ea7218555, 0x5293e0d06eda3615, 0x554a4f8341bb6155, 0x54a5113e0d06ed85])
  | 122 => (fromWords [0x1293e0d06ed85555, 0x293e0ea341dd6ed8, 0x5555293e0d06ed85, 0x555293e0d0119f26, 0xed92615293e0d07a, 0x9d6615554a4f8341, 0xbb615554a5043e0d, 0x825bb555293e0d0])
  | 123 => (fromWords [0x185554f83408b7c9, 0xbb6e9854a4f8341e, 0x16ed855d95553cd0, 0x7c9d9615293e0d01, 0xfdbb6c585554f834, 0x1d7a9bb64985554, 0xf8341f2785854a4f, 0x83403e6edaa61555])
  | 124 => (fromWords [0x1173e1f27858553d, 0x2934202785a05552, 0x93e0d06ed8555542, 0x4a4f8355bb615554, 0xa4f8340307c9bb61, 0x5293e0d017dbb615, 0x554a4f8340236ed8, 0x5554f83409e065bb])
  | 125 => (fromWords [0x1554a4f83406f765, 0xbb6155553d2945de, 0xa765a0615554a4f8, 0x7c9bb6dda04a4f83, 0x41f87c9bb615293e, 0xd07c9bb615484a4, 0xd07a9bb615554a4f, 0x8375bb6598555529])
  | 126 => (fromWords [0xa1831ff6ed854a4, 0xf8341bb615554a4d, 0x1e9f26ed854a50b, 0x3e0d0785bb6a5855, 0x5529341bb615554a, 0x4f8340706ed85555, 0x293e0d0145bb6155, 0x54a4f836cd06ed85])
  | 127 => (fromWords [0x14f3e0d07c9bb615, 0x293e0d0201bb6c55, 0x54a4f8340bf6edb1, 0x6815553cf8341bb6, 0xc5554a4f8354d06e, 0xd855552945cf82e1, 0xf2785854a4f83408, 0x780985555293e0d0])
  | 128 => (fromWords [0x185555293e0d010d, 0xf26ed854a4f8340c, 0x26ed85555424a4f8, 0x3a1ea6ed85554f83, 0x40327c9bb615293e, 0xcc809d4615554a4, 0xf8341f26ed854a4f, 0x8340326fdbb61555])
  | 129 => (fromWords [0x1293e0d06ed85555, 0x2945cd029df26ed8, 0x54a4f8349bb61555, 0x4a4f8340c47f9e86, 0x15293e0d0801f26e, 0xd854a4f8341bb615, 0x554a4f8340147c9b, 0xb679854a4f8341ea])
  | 130 => (fromWords [0x1bb681854a5173e1, 0xff7c9bb615293e0b, 0xd809bb6cd554a4f8, 0x342066ed85555424, 0xa4f87c9bb6154b4a, 0x4f8341bb6c5a0555, 0x2945cf86ed855612, 0x93e0d080dbb61555])
  | 131 => (fromWords [0xa87c9bb615824a4, 0xf834202615554a4f, 0x834027831f26ed85, 0x4a4f4341d96eda05, 0x55293e07f7c9b161, 0x5293e0d009dbb615, 0x554a50d3e0d07c9b, 0xb615293e0d0171f2])
  | 132 => (fromWords [0x1173e0ad809f0615, 0x554a4f8342027a9a, 0x555293e0d07c9e1, 0x615293e0d012dbb6, 0x15554a4f83403a6e, 0xd85555454a4f8375, 0xea6c585554f83402, 0x76ed85555293e0d0])
  | 133 => (fromWords [0x1554a4f83409a6ed, 0x855552940cf83420, 0x27a985554f834096, 0x6ed85555293e0da3, 0x41bb615554a4f838, 0x8d07c9bb615293e0, 0xe8341f26edae6152, 0x93e0d07c9bb61529])
  | 134 => (fromWords [0x1f26ed854a4f8340, 0x9e6ed85555344a4f, 0x8341bb681554a4f8, 0x340277fdf26ed853, 0xe0d0259f26ed9a61, 0x5293e0d07a9bb615, 0x5545cf82b5bb6156, 0x2555293e0d06ed85])
  | 135 => (fromWords [0x185555293e0d0819, 0xbb6c5554a4f8341f, 0x2765854a4f82e9bb, 0x615553e0d0258277, 0xc9c8615293e0d080, 0x9ea6c5553e0d07c9, 0xbb615293e0d0295f, 0x26ed854a4f83bcd0])
  | 136 => (fromWords [0x20f6ed85555293e0, 0xd06ed85555293e0d, 0x265bb6155553cf8, 0x340666ed87615554, 0xa4f8341f77c9bb61, 0x5293e0d07a9bb615, 0x553e0ef341ea6ed8, 0x5554f83409e809d0])
  | 137 => (fromWords [0xd06ed85555293e0, 0xd0199ea6ed855554, 0x23e0d06edb155529, 0x3e0d0085bb615554, 0xa4f8340b56ed8555, 0x5424a4f8340986ed, 0xb7615293e0d021db, 0xb61560555293e0d0])
  | 138 => (fromWords [0x1764a4f8341bb615, 0x554a50f3e0d06ed8, 0x555529418d06ed85, 0x555293e0d07a9bb6, 0x155553d293e0d06e, 0xd85555293e0d012d, 0xbb615554b1293e0d, 0x785bb6155553d29])
  | 139 => (fromWords [0x185555293e0d009d, 0x85555293e0d02420, 0x26ed855c1554a4f8, 0x341bb6155553cf83, 0x40196ed85555364a, 0x4f8341bb615554ed, 0x293e0d06ed855552, 0x93e0d0009f26ed85])
  | 140 => (fromWords [0x1554a4f8341bb6e9, 0xb1615554a4f8341b, 0xb689855554f4a4d0, 0x809bb615554a4f83, 0x4096831f26ed854a, 0x4f8341bb615554a4, 0xf83400f7c9bb6818, 0x5555293e0d06edb1])
  | 141 => (fromWords [0xf834021765bb689, 0x85555293e0d07c9e, 0x1615554a4f8341d6, 0x6ed85555293e0d08, 0x9bb615554a4f834, 0x5b7a9bb615554a4, 0xf8340b4721bb6155, 0x54a4f8342026edb1])
  | 142 => (fromWords [0x1854a4f83407e7c9, 0xbb6154f4a4f83420, 0x96ed85555293e0d0, 0x6ed85555293e0d02, 0x15bb6e585555293e, 0xd06ed85555293e0, 0xd02dde86ed855552, 0x93e0d06eda055529])
  | 143 => (fromWords [0x185555293e0d0055, 0xbb615554a4f8374d, 0x6edb16818555529, 0x3e0d06ed85555293, 0xe0d020dd96eda061, 0x5554a4f87a9bb615, 0x5553cf8341d96edb, 0x7615554a4f8341bb])
  | 144 => (fromWords [0x185555424a4f87a9, 0xbb615553e0d00f9b, 0xb6c585555293e0d0, 0x279f26ed854a4f83, 0x403e7a9bb615554a, 0x4f83407f6ed85555, 0x293e0d01c9bb6155, 0x54a4f834043765bb])
  | 145 => (fromWords [0x1855e9554a4f8341, 0xbb615554a5233e0d, 0x809bb681554a4f8, 0x341bb615554a4f83, 0x401d6edb36155553, 0xd293e0d06ed854a4, 0xf83405a6eda26155, 0x54a4f834019765bb])
  | 146 => (fromWords [0x1bb615293e0d02d1, 0xea6ed85555293e0d, 0x3dbb6c5554a4f8, 0x340b47c9bb615293, 0xe0d0029bb615554a, 0x4f834015831f26ed, 0x85555293e0d06ed8, 0x8615554a4f8341bb])
  | 147 => (fromWords [0x1b1615554a4f8341, 0xbb615554a4f83406, 0x37fdbb615554a4f8, 0x342026ed85555294, 0x5cf8341d96ed8555, 0x5293e0d0261bb615, 0x554cd293e0d07c9b, 0xb615293e0d021df2])
  | 148 => (fromWords [0x1293e0d012dbb615, 0x5553cf83405b7c9b, 0xb6155553d293e0d0, 0x825ea6ed85555293, 0xe0d081e026ed8555, 0x5293e0d0739bb615, 0x554a4f8341d16ed8, 0x5555293e0d06edb2])
  | 149 => (fromWords [0xf83408a819bb681, 0x85555293e0d07c9b, 0xb615293e0d01fdea, 0x6eda2615554a4f83, 0x42026edb1615554a, 0x4f8341e16eda2615, 0x554a4d06edb16152, 0x93e0d007df26ed85])
  | 150 => (fromWords [0x1bb615785554f4a4, 0xf8341bb6cd855552, 0x93e0d06ed8555529, 0x3e0d02b4216edb16, 0x155553d293e0d07a, 0x9bb6dd85555293e0, 0xd06ed85555293e0d, 0x260196ed8555529])
  | 151 => (fromWords [0x1855554f4a517341, 0xd96ed85555293e0d, 0x179bb6a5a061555, 0x4a4f8341e16ed855, 0x55293e0d016df26e, 0xd854a4f8340076ed, 0x85555293fcf8341b, 0xb615554a4f8340a3])
  | 152 => (fromWords [0x1855c5554a4f8341, 0xbb61555509293e0d, 0x85bb615554a4f8, 0x340a76edb2681855, 0x55293e0d06ed8555, 0x5293e0d0111bb615, 0x554a4f8340116ed8, 0x5555293f0f8341bb])
  | 153 => (fromWords [0x1293e0d01fe026ed, 0xa0615554a4f8341b, 0xb6c585555293e0d0, 0x185bb681854a4f83, 0x401f6ed855552934, 0x7c7fdea6ed85555, 0x293e0d07c1bb6155, 0x553d293e0d07a9bb])
  | 154 => (fromWords [0x1554a4f8341fb765, 0xbb615554a4f8341e, 0xa6ed85555293e0d0, 0x261c56ed85555293, 0xe0d07c9bb689854a, 0x4f8341bb615554a4, 0xf8340646ed855552, 0x93e0d02c9bb68155])
  | 155 => (fromWords [0x1554a4f834202785, 0x85555293e0d0765b, 0xb6c585555293e0d0, 0x6ed8555529474f83, 0x41e16ed85555293e, 0xd0045bb61529420, 0xf8342026ed855552, 0x93e0d02b5bb61579])
  | 156 => (fromWords [0xf8340b56edb1615, 0x5553cf8342026ed8, 0x5555424a4f834206, 0x809bb615554a4f83, 0x41bb681855554f4a, 0x4f8342076ed85555, 0x293e0d07c9bb6dd8, 0x54a4f8341fc6ed85])
  | 157 => (fromWords [0x1554a4f8341bb615, 0x78555293e0d0809b, 0xb555293e0d02d1bb, 0x6c585555293e0d06, 0xed85555293e0d028, 0x5bb615554a4f837c, 0xd07edbb615554a4f, 0x8341bb6c58555529])
  | 158 => (fromWords [0x1bb615554a4f8340, 0x9d6ed855c9293e0d, 0x7c9bb615714a4f8, 0x341bb615554a4f81, 0xe1bb62985555293e, 0xd0751bb615554a4, 0xf8341bb615554a4f, 0x834025809bb61576])
  | 159 => (fromWords [0x1bb64985555293e0, 0xd081de16ed855552, 0x93e0d06ed8555529, 0x3e0d009dff7c9bb6, 0x15293e0d0809ea61, 0x5554a4f8341fc785, 0xbb615554a4f8341f, 0x26ed855c1293e0d0])
  | 160 => (fromWords [0x5e7c9bb615293e0, 0xd0261bb615554a4f, 0x83405f6edba61555, 0x4a4f8341ea6ed855, 0x54f8340967bdd96e, 0xd85555293e0d07c1, 0xbb615554a4f8341f, 0x26ed854a4f834096])
  | 161 => (fromWords [0x185555293e0d02e9, 0xf26ed854a4f83405, 0xb832026ed8555529, 0x3e0d0785bb6c5855, 0x55293e0d079dd96e, 0xd85555293e0d0741, 0xbb615554a4f8341e, 0xa6ed85555293e0d0])
  | 162 => (fromWords [0xd5341ef6ed85555, 0x293e0d07a9bb6155, 0x54a5173e0d0785bb, 0x615554a517341bb6, 0x1529454f8342026e, 0xd554a4f83407f6ed, 0xb7681554a4f8341b, 0xb6155552129341bb])
  | 163 => (fromWords [0x1293e0d0825bb6c5, 0x85555293e0d06ed8, 0x553d293e0d007de7, 0x6ed85555293e0d06, 0xed85555293e0d011, 0xdbb615554a4f8340, 0xbf6ed85555293e0d, 0xc9bb615554a4f8])
  | 164 => (fromWords [0xad7a9bb6c585555, 0x293e0d07c9bb6152, 0x93e0d028dbb61555, 0x4a4f83405c6eda06, 0x15554a5173e2026e, 0xd855554f4a4f8341, 0xf0785bb615554a4f, 0x834206765bb61555])
  | 165 => (fromWords [0x1554a4f8341bb6c5, 0x85554f8340196ed8, 0x55b1293e0d0819bb, 0x615554a4f8341bb6, 0x15554a4f83bcd06e, 0xd85555293e0d0279, 0xbb615554a4f83a0d, 0x6ed855552945cf8])
  | 166 => (fromWords [0x1554a4f8341e7785, 0xbb615554a4f8341b, 0xb615554a4f834081, 0x7a185555293e0d06, 0xed855d95553cf834, 0x2026ed85555293e0, 0xd00f9ea765855552, 0x93e0d07fdf26ed85])
  | 167 => (fromWords [0x1554a4f8341e16ed, 0x85555293e0d02b60, 0x26eda2555293e0d0, 0x6ed85555293e0dd7, 0xc1ea6ed85555293e, 0xd06ed855f1554a4, 0xf8341f26ed854a4f, 0x83405e785bb68185])
  | 168 => (fromWords [0x1424a4f8341ef7a9, 0xbb615554a4f8341b, 0xb6dd855d9293e0d0, 0x6edb2615554a4f83, 0x41fc7c9bb615293e, 0xd06edb968185555, 0x293e0d07c9bb6152, 0x945cf8341bb6a585])
  | 169 => (fromWords [0x15553d293e0d0785, 0xbb61576555293e0d, 0x7a9bb6818555529, 0x3e0d0831bb615554, 0xa4f8341bb615554f, 0xd293e1fb7c9bb615, 0x293e0d06ed854a4f, 0x8340c8785bb61555])
  | 170 => (fromWords [0x1293e0d06ed85555, 0x2945cd0261bb6898, 0x5555293e0d02b602, 0x6ed85555293e0d00, 0x9ea6edb1615553e, 0xd06ed855555253d, 0x293e0d07c9bb6c58, 0x54a4f8341d96ed85])
  | 171 => (fromWords [0x1bb65985555293e0, 0xd07c9bb61529460f, 0x8341bb615554a4f1, 0x341bb615554a51f3, 0xe0d06eda26155550, 0x9293e0d06ed85555, 0x293e0c76eda05552, 0x93e0d0179f276585])
  | 172 => (fromWords [0xb86eda061555509, 0x293e1bb6155553cf, 0x83403e7c9bb61529, 0x3e0d02e9bb615554, 0xa4f8340696edb36c, 0x585555293e0d06ed, 0x85555293e0e03420, 0x26ed554a4f834098])
  | 173 => (fromWords [0xd0185f26eda0615, 0x293e0d06fdbb6155, 0x54a4f8341bb6c5a0, 0x555293e0d07c9bb6, 0x1529480f8341fc7c, 0x9bb615554a4f8341, 0xbb615554a4f8340a, 0x6ed85555293e0d0])
  | 174 => (fromWords [0x876ed85555293e0, 0xd02b4987c9bb6152, 0x93e0d02b5fb7c9bb, 0x615554a4f8341bb6, 0x15554a5063e0d082, 0x6026ed85555293e0, 0xd06edb1615553e0d, 0x259bb615554a4f8])
  | 175 => (fromWords [0x1554a5173e1bb615, 0x55549293e0d06ed8, 0x55b9293e0d07c9e1, 0x615293e0d07a9bb6, 0x15553e0d02b5f26e, 0xd85601293e0d07c9, 0xbb6c585555293e0d, 0x6ed85555293e0d0])
  | 176 => (fromWords [0x1293e0d07c9bb615, 0x424a4f8341d96ed8, 0x5555293e0d01fdf2, 0x76585555293e0d07, 0x85bb615554a4f834, 0x3e6ed85555293e0, 0xd0101bb6c5855552, 0x945cf8341d96ed85])
  | 177 => (fromWords [0x1855c5554a4f8341, 0xbb6dd85555293e0d, 0x6eda2615554a4f8, 0x341ea6ed85555293, 0xe0d0785bb615554a, 0x4f8341bb615554a4, 0xf8340196ed855552, 0x93e0d01fdbb61555])
  | 178 => (fromWords [0xf8341f26ed85555, 0x293e0d06ed855552, 0x93e0d0179bb61555, 0x4a4f83405b6ed855, 0x55293e0d0261f26e, 0xd854a4f8341bb615, 0x554a4f8340966ed8, 0x55c1554a4f8341bb])
  | 179 => (fromWords [0x1554a4f8341bb615, 0x554a4f8340216ed8, 0x5555424a4f8341bb, 0x615554a4f8340ad6, 0xeda0615554a4f834, 0x1bb615554a5183e0, 0xd06edb1615554a4f, 0x8341bb615554a517])
  | 180 => (fromWords [0x6ed85555293e0, 0xd0765bb615554a4f, 0x8341bb615554a4f8, 0x340b46ed85555293, 0xe0d00f9bb6155553, 0xd293e0d0809bb615, 0x554a4f8341bb6152, 0x93e0d007dbb61576])
  | _ => 0
def stateWire (i : Nat) : Nat := fld (stateWireBlock (i / 51)) 10 (i % 51)
def stateDescriptorBlock : Nat → Nat
  | 0 => (fromWords [0x2598090602298, 0x84601f98078601c, 0x9806c60199806060, 0x1698054601398048, 0x60109803c600d980, 0x31500b1402750089, 0x401d500614013500, 0x3940095001140004])
  | 1 => (fromWords [0x4f98138604c98, 0x12c6049981206046, 0x9811460439810860, 0x40980fc603d980f0, 0x603a980e46037980, 0xd86034980cc60319, 0x80c0602e980b4602, 0xb980a860289809c6])
  | 2 => (fromWords [0x79981e0607698, 0x1d46073981c86070, 0x981bc606d981b060, 0x6a981a4606798198, 0x60649818c6061981, 0x80605e98174605b9, 0x816860589815c605, 0x5981506052981446])
  | 3 => (fromWords [0xa39828860a098, 0x27c609d98270609a, 0x9826460979825860, 0x949824c609198240, 0x608e98234608b982, 0x2860889821c60859, 0x8210608298204607, 0xf981f8607c981ec6])
  | 4 => (fromWords [0xcd9833060ca98, 0x32460c79831860c4, 0x9830c60c19830060, 0xbe982f460bb982e8, 0x60b8982dc60b5982, 0xd060b2982c460af9, 0x82b860ac982ac60a, 0x9982a060a6982946])
  | 5 => (fromWords [0xf7983d860f498, 0x3cc60f1983c060ee, 0x983b460eb983a860, 0xe89839c60e598390, 0x60e29838460df983, 0x7860dc9836c60d99, 0x836060d69835460d, 0x39834860d09833c6])
  | 6 => (fromWords [0x12198480611e98, 0x474611b984686118, 0x9845c61159845061, 0x1298444610f98438, 0x610c9842c6109984, 0x2061069841461039, 0x84086100983fc60f, 0xd983f060fa983e46])
  | 7 => (fromWords [0x14b98528614898, 0x51c6145985106142, 0x98504613f984f861, 0x3c984ec6139984e0, 0x6136984d46133984, 0xc86130984bc612d9, 0x84b0612a984a4612, 0x79849861249848c6])
  | 8 => (fromWords [0x175985d0617298, 0x5c4616f985b8616c, 0x985ac6169985a061, 0x6698594616398588, 0x61609857c615d985, 0x70615a9856461579, 0x855861549854c615, 0x198540614e985346])
  | 9 => (fromWords [0x19f98678619c98, 0x66c6199986606196, 0x9865461939864861, 0x909863c618d98630, 0x618a986246187986, 0x1861849860c61819, 0x8600617e985f4617, 0xb985e86178985dc6])
  | 10 => (fromWords [0x1ce1c73171ca9c, 0x72461c75c71671c3, 0xdc70961c09c6fb71, 0xbd1c6ed71b99c6df, 0x71b61c6d171b2d86, 0xc561af9c6b861ac5, 0xc6aa71a8dc69c71a, 0x59869061a2986846])
  | 11 => (fromWords [0x1fddc7f161fa9c, 0x7e461f75c7d671f3, 0xdc7c871f05c7ba71, 0xecdc7ac71e95c79e, 0x71e65479271e2dc7, 0x8471df5c77671dc1, 0x876971d89c75b71d, 0x51c74d71d19c73f7])
  | 12 => (fromWords [0x22e188b1722a9c, 0x8a372271c8966224, 0x1888a6220dc87c72, 0x1d5c86e7219dc860, 0x72165c8527212dc8, 0x44720f5c836720bd, 0xc82872085c81a720, 0x4dc80c72015c7fe7])
  | 13 => (fromWords [0x25e9c973725b1c, 0x96572579c9577254, 0x1c94972509c93b72, 0x4d1c92d72499c91f, 0x72461c91172429c9, 0x3723f1c8f5723b9, 0xc8e772381c8da623, 0x4dc8cc72315c8be7])
  | 14 => (fromWords [0x28edca34728b5c, 0xa26728818a197284, 0x9ca0b72811c9fd72, 0x7d9c9ef727a1c9e1, 0x7276d89d472735c9, 0xc6726fdc9b8726c5, 0xc9aa72691899d726, 0x59c98f72621c9817])
  | 15 => (fromWords [0x2bf1caf572bbd8, 0xae872b85cada72b5, 0x18acd72b19cabf72, 0xae1cab172aa9caa3, 0x72a71ca9572a39ca, 0x8772a01ca79729cd, 0x8a6c72995ca5e729, 0x5dca5072925ca427])
  | 16 => (fromWords [0x2ef5cbb672ec18, 0xba972e89cb9c62e5, 0x5cb8e72e1dcb8072, 0xde5cb7362db1cb65, 0x72d79cb5772d41cb, 0x4972d09cb3b72cd1, 0xcb2d72c99cb1f72c, 0x61cb1172c29cb037])
  | 17 => (fromWords [0x3205cc7a731cdc, 0xc6c73195cc5e7315, 0xdcc5073125cc4273, 0xedcc34730b5cc26, 0x7307dcc1873045cc, 0xa7300dcbfc72fd5, 0xcbee72f9dcbe072f, 0x65cbd272f2dcbc47])
  | 18 => (fromWords [0x350dcd3c734d5c, 0xd2e7349dcd207346, 0x5cd127342dcd0473, 0x3f98cf7733c1cce9, 0x73389ccdb73351cc, 0xcd73319ccbf732e1, 0xccb1732a9cca3732, 0x758c967323dcc887])
  | 19 => (fromWords [0x3819cdff737e1c, 0xdf1737a9cde37377, 0x1cdd66373dcdc873, 0x705cdba736cdcdac, 0x73695cd9e7365dcd, 0x9073625cd82735ed, 0xcd74735b5cd66735, 0x7dcd5873545cd4a7])
  | 20 => (fromWords [0x3b1dcec073ae5c, 0xeb273aadcea473a7, 0x5ce9673a418e8973, 0xa0d8e7c739d5ce6e, 0x7399dce6163969ce, 0x5373931ce45738f9, 0xce37738c1ce29738, 0x89ce1b73851ce0d7])
  | 21 => (fromWords [0x3e1dcf8073de5c, 0xf7363db1cf6663d8, 0x18f5973d49cf4b73, 0xd11cf3d73cd9cf2f, 0x73ca1cf2173c6d8f, 0x1473c35cf0673bfd, 0xcef873bc5ceea73b, 0x8dcedc73b55cece7])
  | 22 => (fromWords [0x4119d03f740e1d, 0x31740ad90247407, 0x9901774041d00a64, 0xdcffc73fd98fef, 0x73fa1cfe173f69cf, 0xd373f31cfc573ef9, 0xcfb773ec1cfa973e, 0x89cf9c63e55cf8e7])
  | 23 => (fromWords [0x4421d101743e9d, 0xf3743b1d0e57437, 0x9d0d774341d0c974, 0x30d90bc742d5d0ae, 0x7429dd0a074265d0, 0x927422dd085641f9, 0xd077741c1d069741, 0x89d05b74151d04d7])
  | 24 => (fromWords [0x4725d1c2746edd, 0x1b4746b5d1a67467, 0xdd19874645d18b64, 0x611d17d745d9d170, 0x645a5d1627456dd1, 0x5474535d146744fd, 0xd138744c5d12a744, 0x8dd11d64459d10f7])
  | 25 => (fromWords [0x4a31d285749f9d, 0x277749c1d2697498, 0x9d25b74951d24d74, 0x919d23f748e1d231, 0x748ad922474875d2, 0x167483dd20874805, 0xd1fa747cdd1ec747, 0x95d1de7475dd1d07])
  | 26 => (fromWords [0x4d35d34674cfdd, 0x33874cc5d32a74c8, 0xdd31c74c55d30e74, 0xc21930174be9d2f4, 0x64bb5d2e674b7dd2, 0xd874b45d2ca74b0d, 0xd2bc74ad5d2ae74a, 0x9dd2a164a69d2937])
  | 27 => (fromWords [0x5039d40865005d, 0x3fa74fcdd3ed64f9, 0x9d3df74f61d3d174, 0xf29d3c374ef1d3b5, 0x74eb9d3a774e81d3, 0x9974e49d38b74e11, 0xd37d74dd9d36f74d, 0xa1d36174d69d3546])
  | 28 => (fromWords [0x5341d4c975309d, 0x4bc652d5d4af652a, 0x1d4a175269d49375, 0x231d485751f9d477, 0x751c1d46975189d4, 0x5b75151d44d75119, 0xd43f750e1d431750, 0xa9d42375071d4157])
  | 29 => (fromWords [0x5645958a7560dd, 0x57c755d9956f755a, 0x1d56175569d55375, 0x531d546654fdd538, 0x754c5d52a7548dd5, 0x1c75459950f75421, 0xd501753e9d4f3753, 0xb1d4e575379d4d77])
  | 30 => (fromWords [0x5939d647759059, 0x63a758cdd62c7589, 0x5d61e7585dd61075, 0x825d603657f1d5f5, 0x757bd95e875785d5, 0xda7575195cd75719, 0xd5c0656e5d5b2756, 0xb195a575679d5977])
  | 31 => (fromWords [0x5c45d70a75c0dd, 0x6fc75bd5d6ee75b9, 0xdd6e075b6996d375, 0xb31d6c575af9d6b7, 0x75ac1d6a975a89d6, 0x9b75a51d68d75a19, 0xd67f759e1d671759, 0xa9d66375971d6557])
  | 32 => (fromWords [0x5f4997cb75f11d, 0x7bd75ed9d7af75ea, 0x597a275e6dd79475, 0xe35d78675dfdd778, 0x75dc5d76a75d9197, 0x5d75d59d74f75d21, 0xd74175ce9d73375c, 0xb5972675c7dd7187])
  | 33 => (fromWords [0x624dd88c76215d, 0x87e761ddd870761a, 0x5d8627616dd85476, 0x135d84766101d839, 0x760c9d82b76091d8, 0x1d76059d80f76021, 0xd80175fe9d7f375f, 0xb1d7e665f7dd7d87])
  | 34 => (fromWords [0x654dd94c76515d, 0x93f664e1d931764a, 0x9d92376471d91576, 0x439d90776401d8f9, 0x763cd98ec76395d8, 0xdf66361d8d176329, 0xd8c3762f1d8b5762, 0xbd98a876285d89a7])
  | 35 => (fromWords [0x684dda0c76815d, 0x9fe767ddd9f0767a, 0x999e376771d9d666, 0x73dd9c966709d9bb, 0x766d1d9ad76699d9, 0x9f76661d9926662d, 0xd984765f5d976765, 0xbdd96876585d95a7])
  | 36 => (fromWords [0x6b5ddad076b25d, 0xac276aeddab476ab, 0x5daa676a7dda9876, 0xa45da8a76a0dda7c, 0x769d5da6e7699dda, 0x6076965da527692d, 0xda44768f5da36768, 0xbdda2876885da1a7])
  | 37 => (fromWords [0x6e699b9286e2dd, 0xb8476df5db7676db, 0xddb6876d85db5986, 0xd49db4b76d11db3d, 0x76cd9db2f76ca1db, 0x2176c69db1376c31, 0xdb0666bfddaf966b, 0xcd9aec76b95dade7])
  | 38 => (fromWords [0x718ddc5c77155d, 0xc4e7711ddc3f870e, 0x1dc31770a61c2187, 0x69dc137702e1c04, 0x76ff21bf576fb9db, 0xe686f7a1bd866f42, 0x1bc976f09dbbb76e, 0xd1dbad76e99dba06])
  | 39 => (fromWords [0x74b5dd267747a1, 0xd1777441dd097740, 0x9dcfb773ce1ced67, 0x3961cde7735ddccf, 0x87321dcc0872e5dc, 0xb2772aa1ca37726e, 0x1c9477235dc86771, 0xfa1c78671c5dc6a7])
  | 40 => (fromWords [0x77fa1df6877ba1, 0xde68777dddd78774, 0x1ddc8877021db977, 0x6c9ddab77691dd9c, 0x876521d8c87615dd, 0x7e775da1d6f775a1, 0xdd60875621d51775, 0x29dd43774ee1d347])
  | 41 => (fromWords [0x7b361ec677afdd, 0xeb877ac5deaa77a8, 0xa1e9a87a4dde8d67, 0xa161e7d879d61e6d, 0x87999de5e8795dde, 0x5077925de42778ea, 0x1e32878aa1e23778, 0x71de15778361e067])
  | 42 => (fromWords [0x7e65df9367e31d, 0xf8577df9df7687db, 0xddf6877d85df5a77, 0xd4ddf4c77d121f3d, 0x77cd61f2d87c961f, 0x1e77c5ddf1077c25, 0xdf0187be9def287b, 0xb19ee487b75ded58])
  | 43 => (fromWords [0x8185e05b68151e, 0x4d7811da040780e, 0x5e031880a6202188, 0x69e0128802de004, 0x77ff5dff677fba1f, 0xe777f81dfd977f46, 0x1fca77f0ddfbc77e, 0xd21fad77e99dfa06])
  | 44 => (fromWords [0x84b1a125784762, 0x1167843a21077840, 0x5a0fa783cde0ec78, 0x395e0de7835a20cf, 0x78321e0c1782e620, 0xb1882a620a188269, 0xe09378231e085781, 0xf9e077781c1e0688])
  | 45 => (fromWords [0x87de21f0787a22, 0x1e17876621d18872, 0x621c2786f1a1b578, 0x6bda1a78867e2198, 0x78645e18a7860a21, 0x7b785d1e16c88595, 0xe15f6855e2150785, 0x25e141884e621327])
  | 46 => (fromWords [0x8af9e2b688abde, 0x2a878a85e29a78a4, 0xde28c78a12227d78, 0x9d9e26f789a1e261, 0x78969e2528892de2, 0x44788f5e236788c1, 0xa22978886221b688, 0x51e20e6881de1ff8])
  | 47 => (fromWords [0x8e15a37e78ddde, 0x37078da5e36278d6, 0xde35478d35e34678, 0xd01a33978cc6232a, 0x78c8a231b78c4e23, 0xc78c15e2ff68be5, 0xa2f278bade2e388b, 0x71e2d488b35e2c58])
  | 48 => (fromWords [0x240869, 0x5e3fa78fcde3ec, 0x78f95e3df68f61e3, 0xd178f29e3c378ef1, 0xe3b578eb9e3a778e, 0x81e39978e49e38b7])
  | _ => 0
def stateDescriptor (i : Nat) : Nat := fld (stateDescriptorBlock (i / 28)) 18 (i % 28)
def readState : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => wireAt (stateWire k) :: readState n (k + 1)
def SS (s i : Nat) : List Nat :=
  let v := stateDescriptor (offset s + i)
  readState (v &&& 15) (v >>> 4)
def SD (s i : Nat) : List (Nat × Nat × Nat) := (SS s i).map (fun w =>
  (w, projBit (pairsG.map Prod.fst) w, projBit (pairsG.map Prod.snd) w))
def hashAtBlock : Nat → Nat
  | 0 => (fromWords [0x736d06ceb06b, 0x430690c05de504ec, 0x9042d30417c03fc4, 0x1f9e01c0f013bd0, 0x112500cfee33f0dc, 0x444d7959b341dac2, 0xe7a5d325aede51b3, 0xd1e40a14eb10895d])
  | 1 => (fromWords [0x230da22b2822a, 0x691ee321ec2f1e4f, 0x21d1fa1a5e21a23b, 0x1a21c19d17199e91, 0x94561687011a0511, 0x805106790efc50e0, 0x200d2d50d00c0b8a, 0xc0b3b008d2608036])
  | 2 => (fromWords [0x3bbf43b67a3b6, 0x293a2a139fe838ba, 0x637b203433f300cd, 0x2f5cd2c1e52b2f22, 0xadac2a8f42975229, 0x4a22905f28e5c28a, 0x1a2891c287b82731, 0xa2607925c1924fff])
  | 3 => (fromWords [0x527c75212c519, 0x7450a2c503db4fba, 0xf4ea3a4b7e24b6fc, 0x4b24d4a3f549ff14, 0x97e2494e1492c648, 0x4d74770e4615f455, 0x8d43a4d43a1b4162, 0x53ea843e0b03bef4])
  | 4 => (fromWords [0x65fd565efa641, 0x4e63c48635be62b2, 0xc607e55f2725eec2, 0x5dcdf5db915d8415, 0xd45a5d34a5b8d25b, 0x15c5a4bd5a1d2573, 0x3f55ab25562d53da, 0x253d5d5391753156])
  | 5 => (fromWords [0x7e2db7d1867ce, 0x627cb2f7c9637c2e, 0x27b3bd7afd67a578, 0x78a04771567514f7, 0x3c4e7275d723a371, 0xce16e02b6daf16d1, 0x6e6bbb46a1e36909, 0xc685106742566ade])
  | 6 => (fromWords [0x947e99306592e, 0x73925d190e78905b, 0x8902668dcbc8caa5, 0x8ca758c5168c28f8, 0xb9198b2368a1b689, 0x8d487e978701d86e, 0xe8621185f9f8594, 0x4836df829188226a])
  | 7 => (fromWords [0xafc18ae3c4ad4, 0x2eab11baa691a7bc, 0xba6f38a5d4ba4d09, 0xa3f6da00159d51f9, 0xbf829867a9831297, 0xbb5975af97568974, 0xf796b97968fd966d, 0x595f3895a5094a33])
  | 8 => (fromWords [0xc1c66c0466bf8, 0x78be536be4b7be01, 0xbde4cbb49eb8652, 0xb7d4fb6785b6512b, 0x6291b5a8cb4445b3, 0xcbcb38dab3851b37, 0xeeb12f8b0d93b093, 0x9b08abb06abb02d7])
  | 9 => (fromWords [0xe107bdfdd8de7, 0xbcde12adde2cdd09, 0xfdc309dbcc8db49a, 0xda9fcd50abd4b33d, 0x4936d2786d0eebce, 0x9d5ce225cdea8c89, 0x53c8432c8210c6b1, 0xc23d8c2231c2023])
  | 10 => (fromWords [0xf97ebf93ddf93, 0x17f8ef5f6042f403, 0x7f0c54f0473ef677, 0xeebb2ee9b0edc1ee, 0xcdbfecd58ec6ffeb, 0x259e98dfe9404e89, 0xbbe73ade7153e6c8, 0x2e67d3e4ca8e4643])
  | 11 => (fromWords [0x4eba04e0f041, 0x70040fd03a16039b, 0xe03996037a9031cd, 0x2eb70271e026720, 0x2501019900062b00, 0x3a9ffa4bfe472fde, 0x7efd3b3fc800fc39, 0xcfc095fb35afa871])
  | 12 => (fromWords [0xc22c0b5e80b5, 0xdc0a63d0a5b709f3, 0x5094ae0933a08861, 0x86d508664080a90, 0x7edc07c77079fb07, 0x9d20789d0760206e, 0xda06300062360532, 0x2052d50506104ec9])
  | 13 => (fromWords [0x117301158e113, 0x921127f10f1c107e, 0xc104980f81c0f6a5, 0xf6610f1a40ef560, 0xe8060e4dd0e05f0d, 0xf150dba20d22d0cf, 0x660cf360c8ec0c89, 0x70c8850c4b50c3cd])
  | 14 => (fromWords [0x1bbc21b87e1a6, 0x4919b9b197871932, 0xb18ea318e44183c4, 0x1816517b6a177a31, 0x76fb175001741116, 0xd4a1659c15cd7159, 0x461540f142ad141d, 0x8138ce130c81309b])
  | 15 => (fromWords [0x2534925014243, 0x4523e0023b7c23b2, 0xb23af122ca82173c, 0x210a820c9c20a9e2, 0xa7920a2b203bf1f, 0xce21f8761f5781f0, 0xa61df6d1d9ab1d37, 0x81d0e31cd4c1c52e])
  | 16 => (fromWords [0x2ea3a2ea032da, 0x8f2cb392c72d2c6b, 0xe2c5682c3742c2a8, 0x2c1902bf4f2bdd62, 0xb5b72b4bc2aba829, 0xdf229a6b28d7028b, 0xbb2855a277b926a1, 0xb262d02579a254a5])
  | 17 => (fromWords [0x3637335fb735d, 0x6035b46359323567, 0xc353183392b3339e, 0x332963312c331003, 0x2bea3212d319e331, 0x83b318103113830d, 0x66301a62fa382f9e, 0x12f5cd2ecb22eab9])
  | 18 => (fromWords [0x3f18b3e0b03df, 0xdf3d56a3cd373c47, 0x43c1753c0663c02b, 0x3bfa03bef43b48f3, 0xaf573a8c33a83b3a, 0x70b3a62e3a21f3a1, 0x2b39d49399b1394f, 0x938f2e384bb37cb3])
  | 19 => (fromWords [0x48b8c48989483, 0xe64834d46e4746c4, 0xd4646f4630745854, 0x4477c4404643dd44, 0x3322431cc42f4d42, 0xc07429be42858426, 0xd4426554209e41a2, 0xd41518401fa3f841])
  | 20 => (fromWords [0x4fc954f9ab4f6, 0x7f4f4b34ef774e78, 0xd4e3fc4e0394dd21, 0x4d46c4d3344d0984, 0xcb1d4bdca4bd124b, 0xcf94b9af4b6fc4b5, 0xd04af734ae1f4a8d, 0xb4a6ca4a42148df7])
  | 21 => (fromWords [0x5662d56521562, 0x4c556845522954f5, 0x65448e542b553d34, 0x53a0d538d6538565, 0x368c535de5358453, 0x3d852622520cf51e, 0xde513955136b5077, 0xe500eb500094fffc])
  | 22 => (fromWords [0x5d6f05c9a05c6, 0x545c4f85c3575c2a, 0x15c0215b5865b3e9, 0x5b1565ac575ab5a5, 0xa9355a76d5a00b59, 0xd435945459270586, 0xd3586ce576985754, 0xe56b3f56a0c5665d])
  | 23 => (fromWords [0x640f26357a635, 0x64634d862f0a6229, 0x66220c621b162199, 0x61abb6180a6169b6, 0x5d1604165fe835f, 0xca55f5cc5f2ed5ef, 0xd55ef9f5eec25eb1, 0x25e69f5e5b15dc2a])
  | 24 => (fromWords [0x701126fda16eb, 0x9c6d4ba6ce6e6cc0, 0xb6ca0c6c3d46bfef, 0x6be7e6aefc69f5a6, 0x955e691cf68fac67, 0xc0166d5a66a77669, 0x465db765baf65b7, 0xe65364646e8646b8])
  | 25 => (fromWords [0x788ea781b0776, 0x4b76ba77528274f7, 0x774e01747b273ff3, 0x73a5a73861734447, 0x335072c74724a172, 0x3a3722f47211d71c, 0x9671a2a7142f711d, 0x37099a707bb70559])
  | 26 => (fromWords [0x80ba6808d8803, 0x127fd8d7fa6a7f9b, 0xd7f8fe7d9557d69f, 0x7d5fe7d0f47ce777, 0xc5e67c2507b8877b, 0xa87acdd7a8847a7, 0x3979cff79aa479a5, 0xa790fd790bd78aba])
  | 27 => (fromWords [0x8a4de88c9188b, 0xc98815187e158797, 0xb87591873ea872a9, 0x8701d86f5286edb8, 0x660b864fe85b5d84, 0x64e8432083c7b836, 0xed82bf082659823e, 0xf81639812ac80d94])
  | 28 => (fromWords [0x91ea59180e917, 0xf6902c78fb348f04, 0x8ef7a8ee118ed13, 0x8e8338e2a98dcbc8, 0xdb588d66d8cc9b8c, 0x5ff8c4868c29e8c1, 0x438c12d8bf4f8bdf, 0x58bbde8b2d38ae5d])
  | 29 => (fromWords [0x9a5169a0a5996, 0x45995869884f9879, 0xc986d1984eb97418, 0x9729b971fb970fc9, 0x6a2b965a095e2895, 0x6ae951c694bf6935, 0x7c930659294c928e, 0x1928389228a92117])
  | 30 => (fromWords [0xa1793a1687a16, 0x7aa0c45a09f5a002, 0x79fb8e9f9f39f025, 0x9eed19ec879ec869, 0xdd479d2809d1b89c, 0xd839c7089c65c9bf, 0x829b69b9aeea9ae6, 0xc9ad909aa3b9a6b7])
  | 31 => (fromWords [0xaaa54aa6bcaa1, 0x68aa145aa0aea9fe, 0xca9b09a9908a9401, 0xa91aaa892fa7e1da, 0x7bcda7471a693ba6, 0x74da634ea5d4ba5b, 0xefa5af6a5471a4d0, 0x9a4bf0a35c3a1d81])
  | 32 => (fromWords [0xb0810b0712b06, 0xddb06abb00e5af31, 0xcaf246af012ae45c, 0xae29aadd56adad5a, 0xd6c8ad425ad096ac, 0x33fac335ac31aac0, 0xeaabffcabd25ab91, 0x9ab8d7ab7aeab446])
  | 33 => (fromWords [0xb8f7bb89f9b82, 0x99b7da4b7599b68e, 0xdb68abb6727b6565, 0xb642ab60c6b4cafb, 0x40b1b3f02b3a27b3, 0x4c7b319db307eb2e, 0x64b2c9fb2312b12f, 0x8b1205b0c12b0983])
  | 34 => (fromWords [0xc3ffec3b8fc35, 0xebc2fa0c22b7c17f, 0xbc1275c0fdbc0d42, 0xc0ad0c0892bfae8b, 0xf746bf2fabe046bd, 0xdd5bd5adbd150bc9, 0x4fbc420bb53cbabd, 0x9ba90cb9eabb9075])
  | 35 => (fromWords [0xcf9facf72ece8, 0x49ce6fece5d4ce2c, 0x6ce0cdce029cd66e, 0xccf0dcc9bdcc55dc, 0xc302cc079cb172ca, 0xae1ca59bca48bc85, 0xa3c8077c719fc5ae, 0x3c55a1c4899c4288])
  | 36 => (fromWords [0xd69d9d5f18d5d, 0xbed578bd55b9d44f, 0x6d43fed3ff6d367c, 0xd337ed2bcbd2922d, 0x2323d2292d1fd5d1, 0xa99d159cd10b6d09, 0xa0d08d5d074cd046, 0x6d0441cfb70cfb0e])
  | 37 => (fromWords [0xddbbdddb3ddd7, 0x76dd6a1dce9fdc8e, 0x8dc7c8dc61edbcd0, 0xdb32ddae69da720d, 0x99afd983dd91bdd8, 0x9cbd875ed84bdd7c, 0xc1d7b79d79a2d791, 0x6d7626d6dead6cc8])
  | 38 => (fromWords [0xe8480e8144e7a, 0x55e711fe699ce663, 0xde641de6380e58b3, 0xe512ee3f7ee3e9ce, 0x3c07e38ede1f3fe1, 0x436e0ef8dff93dfd, 0xf9dfdd8dfb7bdf3a, 0x5df2d6ded46ddfe8])
  | 39 => (fromWords [0xf1090f0c54f0c, 0x45effa6efb63ef45, 0x8ef1edef15bee2e7, 0xee2e5ee2c4ecd33e, 0xcbf6ecbc4ec679ec, 0x55dec2d5eb4bfeb4, 0x35eae52ea07de9da, 0x3e96f3e8b87e8b22])
  | 40 => (fromWords [0xf8b7bf8a24f87, 0x15f7f39f7ca4f73f, 0x8f614af601ff5db8, 0xf5a53f5221f5213f, 0x4fe1f4bd8f46b8f3, 0x7e4f35c6f35c2f2f, 0xfff2f60f2d63f28a, 0x1f2222f1d87f1cb1])
  | 41 => (fromWords [0xfda82fda66fd6, 0xe1fc90dfc894fc80, 0x1fc259fbf43fbe36, 0xfbaf5fb35afb2dbf, 0xb20dfb194fa67bfa, 0x529fa22df9f07f9e, 0x15f9bc0f9917f976, 0x9f95b1f92caf8c8a])
  | 42 => (fromWords [0x16f05141e513a, 0x1f118c70b4f50a15, 0xf087e707b2106879, 0x659e05dbc04ec90, 0x45d803e9d0399603, 0x73401dfa013a5012, 0xb300fd300914fff5, 0xbff9f7feceffe33d])
  | 43 => (fromWords [0x297f5296c1282, 0x227f9027bd627a4, 0xd268902501423b98, 0x2351422cfa2219f2, 0x15b51fed61e7521e, 0x5ad1d7881cf821b6, 0x2219787187991811, 0x3179de17411172a5])
  | 44 => (fromWords [0x40de7402193f2, 0x3a3e6e43de9a3dcf, 0x53d8063d73f3c02b, 0x3bc0f3a15e39a893, 0x907938c8737b9637, 0x2d4372d03545933d, 0xb233d5932c9c315e, 0x630f4030dac2f3c3])
  | 45 => (fromWords [0x614fb609b7606, 0xc65f4ae5ba6f59bd, 0x35748f5651954f54, 0x53d6f5374552ecb5, 0x3d44d5944cea94c, 0xbbe4c4534bc804a6, 0x464a4494843a4734, 0x546bd04669f427d5])
  | 46 => (fromWords [0x7666c7602775a, 0x477494f73eb673a4, 0x773329706d66e6ad, 0x6e00f6cec66b4736, 0xa6416890e6873c68, 0xf3667e866700659, 0x1b65381644fc642a, 0x9641fb6262e6253e])
  | 47 => (fromWords [0x89742896e9892, 0x2b880ec871de86a6, 0x851528364c832e8, 0x82e6682b15804697, 0xf7b07f7197dd277c, 0x5837b2947a7847a5, 0xc479870797d378b9, 0xa770ad76bf27666e])
  | 48 => (fromWords [0x9a2819a266995, 0xd1994be9921a9892, 0x697801964849626e, 0x94daf94bf694b6e9, 0x31f1927a191ed090, 0x2c78f64b8f60b8ea, 0x578e4828e4048d72, 0xb8d6f389f85898b3])
  | 49 => (fromWords [0xaf484af01eae6, 0x1dabc35a9ecfa9ec, 0xba9700a7c7ea74a8, 0xa7329a638fa602ba, 0x4d6da3f7ea34cda3, 0xdea1809a1577a06, 0xd39fdd79de069cc8, 0x99ba379ad4e9a918])
  | 50 => (fromWords [0xc65bbc6125c5c, 0x7ac5b2bc382fc1ee, 0x5bf6bbbeed9bcb3f, 0xbc035bb8d4bb4d2b, 0xa568b90b3b9027b8, 0xf7bb8e0ab6bc9b66, 0x8ab65f5b553ab50d, 0x2b3f02b1b16b1a9d])
  | 51 => (fromWords [0xe2858e17d8e14, 0xb1e01eddee63de15, 0x1de015dac4eda434, 0xd8942d79b1d409ad, 0x4088d1fd5d12add0, 0x8d5d073fd020ace9, 0x1fcdd1accea5ccd4, 0x3cc47ac9636c8c48])
  | 52 => (fromWords [0xf88a3f8424f74, 0x2af6f2af6c03f6b2, 0x2f6999f5d2af3071, 0xf28a9f157bf1144f, 0x1014f0bd7f09f1ef, 0x837ed397ebfa8ebe, 0x2fe8467e6341e62e, 0xae4445e36a0e2ccc])
  | 53 => (fromWords [0x871de7a138748, 0xee71ddb512214f22, 0xf4e5c04b47745360, 0x44034346302c9302, 0xc30817f510f86d0b, 0x85d04ec9ffca5fee, 0x3fec70fd6eafd55, 0x6fc44dfae5af8fdd])
  | 54 => (fromWords [0x4ec9f846ff5b43ea, 0x662dd199d1430ce0, 0xbfbd182b8f5cb65a, 0xeac633a74e096af6])
  | _ => 0
def hashAt (i : Nat) : Nat := fld (hashAtBlock (i / 25)) 20 (i % 25)
def htAt (s i : Nat) := hashAt (offset s + i)
def idxH (s h : Nat) := bsr (htAt s) h 11 0 (NN s)
def opAtBlock : Nat → Nat
  | 0 => (fromWords [0x1293e16ed855854, 0x5d6ecf84f83417c9, 0xa01bb5556ecd0585, 0x341615295293e161, 0x4d04f8341830f81f, 0x26156ed555bb3416, 0x14d05ff3407c9295, 0xbb5556ecf85293e1])
  | 1 => (fromWords [0x1bb4a54a5175bb3, 0x413e0d05f24a56ed, 0x555bb3e14a4f85bb, 0x615615425bb4a54a, 0x4d05bb555614f8db, 0xb3413e0d05bb5556, 0x15425bb3414a4d05, 0xf24a66ed555bb3e1])
  | 2 => (fromWords [0x1bb6156ecf85853, 0x416ed555bb45d4a4, 0xf84f83416ed55585, 0x53d6ecf85293e17c, 0x8f85bb5556ecd04f, 0x83418094f1bb6156, 0xed295293e17654f1, 0xbb4a54a4f85bb341])
  | 3 => (fromWords [0x1bb5556ecf860c3, 0xe07c9855bb555614, 0xd05f23416ed555bb, 0x3e13e0d05f24a56e, 0xd555bb3414a4d05e, 0x16c46ed555854a56, 0xecf85bb5556ecf85, 0x4f3434a4f85e1680])
  | 4 => (fromWords [0x185341830f81f26, 0x156ed555bb3416ed, 0x555bb45d614d04f8, 0x3416ed555bb3e14a, 0x4d0cf83417c94f1b, 0xb5556ecf85293e17, 0xc9855bb5556ecd05, 0x853417fcd01f24a5])
  | 5 => (fromWords [0x1bb4a54a4f85bb3, 0x413e0d05f26157c8, 0xf8dbb5556ecf85f2, 0x6156ed555bb3e161, 0x4f85bb555555295b, 0xb3e14a4f85d96c46, 0xed555854a56ecd05, 0xf26166ed555bb341])
  | 6 => (fromWords [0x1bb3e1614d04f83, 0x416ed555a03e36ec, 0xd05853417a9a01bb, 0x6156ed295853417f, 0xcd01f24a56ed5552, 0x93e16ed8558553d6, 0xed295293e17c9295, 0xf23436ed555bb341])
  | 7 => (fromWords [0x1b1343615294f83, 0x416ed555e13436ec, 0xf85bb1f955518d85, 0x4a46ed555bb46161, 0x5291bb5555552952, 0x93e16ed555853e16, 0xecd05bb555615555, 0xbb341614d05bb615])
  | 8 => (fromWords [0x1bb555614f85e15, 0x57555295bb3e16ed, 0x554d017961555df2, 0x2b56ed5552934361, 0x4b254f3434a4f85f, 0x26157c8f8dbb5557, 0xc9855bb555614f85, 0xbb6156ecf84f8341])
  | 9 => (fromWords [0xf83416ecc85552, 0xd3614d0d854a54a4, 0xf84f83416ed15555, 0x45c3e0d05bb5556e, 0xcf85293e16ed555b, 0xb341614d05bb4a56, 0xec985853e36ed555, 0x855556ecd05f2689])
  | 10 => (fromWords [0x1855096ed295293, 0x416ed555855094a4, 0xd05bb6a5615174f8, 0x341680f8dbb34161, 0x4d052912f7c985db, 0xb555784d0dbb3e14, 0xa4f85f24a66ed555, 0xbb3e16ec5a55545e])
  | 11 => (fromWords [0x1855576ecd05f21, 0x796ed555855577c1, 0x85dbb53d4a4f85bb, 0x555460d05854a45f, 0x1559ea6146ed294f, 0x801f7c9299bb5557, 0xc8d0dbb555614d04, 0xd01016154f9293e1])
  | 12 => (fromWords [0x1853417c9295bb5, 0x556ecd05850f96ed, 0x855854a66ed295bb, 0x3414a4d04f816d55, 0x5299bb3e17c898db, 0xb555614f8dea1796, 0x1555dbb4a56ed555, 0xbb3414a4d05d917b])
  | 13 => (fromWords [0x1bb615680f8d853, 0x413404b5f26176ed, 0x5552945d6ecf84f8, 0x3417c9855f23e16e, 0xd555855556ecd058, 0x53416ed4f5293e13, 0xe0d05bb6156145b5, 0x554a6764f8dbb341])
  | 14 => (fromWords [0x1f24a56ed555bb5, 0x5561555d85341615, 0x4f9bb3e14a4f85bb, 0x555614f8dbb3416e, 0xc615b1557615295b, 0xb555614f8cf83416, 0xedb15854a54a4f85, 0xa053e4a4f8585341])
  | 15 => (fromWords [0x1554a67c9855bb5, 0x55614f8df26c46ed, 0x555854a57c918dbb, 0x555615291bb61561, 0x4965293e3830f8db, 0xb6dd615555d94a74, 0xa4f85bb3416ed554, 0xd017b61555dff343])
  | 16 => (fromWords [0xd028d7c8f8dbb5, 0x557c8b4dbb555614, 0xd0e0c3e07c9855bb, 0x555785a09bb3e161, 0x4d05bb555614ad52, 0x93436ec7258550b4, 0xa4d052945d614d04, 0xf83416ed554f816f])
  | 17 => (fromWords [0x1293e1614d04d02, 0x61614f8dbb3416ed, 0x555853414a4d05f0, 0x6146ed4f5293e16a, 0x555d8545d3e0d05f, 0xf3407c9295bb5556, 0xed555bb341614d05, 0xbb3e13e0ad529343])
  | 18 => (fromWords [0x1bb3414a49d5a03, 0xe3614d057c3427a9, 0x851bb4a56ed855bb, 0x4a5615295d96176e, 0xcd04f83416ed555b, 0xb3e1614f86024a76, 0xed855554a54a4a05, 0xd93e36ecd05a053c])
  | 19 => (fromWords [0x1bb5556c555d854, 0xa56c4f8d854a53e0, 0xd05f24a56ed555bb, 0x3e168129dbb34161, 0x4d05e75576ed174f, 0x83416ed555854a56, 0x14d05bb6dd615555, 0x853417c8f8dbb555])
  | 20 => (fromWords [0x1853413e0d05bb5, 0x494a5174f8341614, 0xa35f23e36ed555bb, 0x5553e05b5554a66e, 0xd72555461615291a, 0x53f4a4f85853413, 0xe0875f24a76ed555, 0xbb53d615295293e1])
  | 21 => (fromWords [0xf83416ed765554, 0xa54a4f85bb615340, 0x985853e3614f84f8, 0x2b54a4d0dbb5b955, 0x4b45853436eda998, 0x545d3e0d05bb6c66, 0xed855854a55f0f85, 0xea6146ed295bb615])
  | 22 => (fromWords [0x1bb5e25554f5293, 0xe16154f9bb4a54a4, 0xf85855096ecd0529, 0x3416ed555855576e, 0xcd05bb555555299b, 0xb3e16ed2952945d3, 0xe0d05bb045785299, 0xbb3e1615175bb341])
  | 23 => (fromWords [0x1f23e36ed555854, 0x817c9291bb555809, 0x55dbb615614d04f8, 0x1d7c9299bb55555, 0x4bf6023436ed855b, 0xb61568129d853415, 0x548a6024a76ed855, 0xbb5556c4d0d854a5])
  | 24 => (fromWords [0x12934376555d855, 0x556ecd05bb5d9615, 0x555554a57c8f85bb, 0x5556ecd05e16806e, 0xcf85853416ed554f, 0x816d555299f23e16, 0xed554f83417c8f8d, 0xbb5554a4f852928d])
  | 25 => (fromWords [0x1bb0c9689299853, 0xe16ed29529261614, 0xf8dbb615615174f8, 0x3413401d5bb53e4a, 0x4f85bb5554a49858, 0x53e36ed295292d16, 0x14d0dbb5554a4b45, 0x853436ed294f82b5])
  | 26 => (fromWords [0x1bb4a561529df24, 0xa56ed555293436ed, 0x555854a56ecd0585, 0x3e36ecd04f83416e, 0xd855855094a4d05f, 0x26c76ed555854a56, 0xed555bb16d55529a, 0x250b6ed85529341])
  | 27 => (fromWords [0xf83413e0835d94, 0xa76ecd05f24a66ed, 0x555293e16edb7585, 0x555555294f801d7c, 0x9299bb55548cd0a0, 0x24a46ed8560c3e36, 0xedb75855556ed785, 0x5553d4a4f85bb615])
  | 28 => (fromWords [0x1f24a56ed555293, 0x4155415dd96166ec, 0xd04d01fd61529dbb, 0x3413400a5f26166e, 0xd5552911378585db, 0xb3e17fcf8df24a56, 0xed555bb555614f85, 0x293e17c9175bb555])
  | 29 => (fromWords [0x1bb5554a4f85855, 0xc16ed555553416ed, 0x855525b4a4f8d55, 0x47785299bb3e17c, 0x8f8dbb5556ecf85f, 0xf3436ed765554a53, 0xe0bf6023436ed855, 0x8553e4a4f8585341])
  | 30 => (fromWords [0x1854a56ec5b5554, 0xa64a4f85bb6816ed, 0x295853417a917dbb, 0x4a53e0d05852eb7c, 0x8d0dbb5557c9b11b, 0xb5556152960c3e37, 0xc9855bb5557a8b4d, 0xbb4a5614d0df253e])
  | 31 => (fromWords [0x1bb555765295bb3, 0x413e0ba5f23436ed, 0x555bb6153407f585, 0x4a76ed855852b54a, 0x4d0dbb455555170f, 0x83415547258550b4, 0xa4d05e16156ed555, 0xbb3e16edb19bb555])
  | 32 => (fromWords [0x1bb3e1614f85d95, 0x3c4a4f85bb3416ed, 0x555854a56ecf8529, 0x45d6ecd04f83416e, 0xd555d93e16ecd05f, 0x225b6ed555293e36, 0xed554d017961555d, 0xf23416ed555bb3e1])
  | 33 => (fromWords [0x1bb3416ed555bb3, 0xe13e0d05bb681615, 0x29d853416edba985, 0x5d9555295d91ff61, 0x529dbb3417c9855b, 0xb555614d05f20f96, 0xed555854a68094f1, 0xbb6154a4f85bb615])
  | 34 => (fromWords [0x1f06176ed4f5293, 0xe16154f5bb3e14a4, 0xf85bb5556ed174f8, 0x3413e0875f24a76e, 0xd555ea68b6ed2958, 0x53e16ec5e5855576, 0x14d05bb17d68155d, 0x853417c9851bb555])
  | 35 => (fromWords [0x1bb5554a4f85e75, 0x57764f85bb3414a4, 0x5e5855576ed294f8, 0xf9615299bb3e16e, 0xd555e14a56ecf85d, 0x96156ed555bb3416, 0x14b75e13436ecf85, 0xf26826ed55585341])
  | 36 => (fromWords [0x1553416ed175293, 0xe13e0d05f216d6ed, 0x555554a681929dbb, 0x681614d05f23436e, 0xd555bb3e16ed6c55, 0x52594a4f8dbb6c56, 0x1529585341555529, 0x2945d3e0d05f24a5])
  | 37 => (fromWords [0x12928d7c8f8dbb5, 0x556ed555554a64a4, 0xf85293e1614d04f8, 0x341819291bb68161, 0x4d05ef6166ed4252, 0x93414a4985853e33, 0xe0d060c3e37c9855, 0xbb5556edb99855c1])
  | 38 => (fromWords [0x1855556ed295bb5, 0x55784d05bb3e179d, 0x55dbb45d3e0d05bb, 0x6156ed295854a66e, 0xdb19bb555615295f, 0x23e36ed555293e17, 0xc9291bb5556ecf85, 0x8521f7c929dbb555])
  | 39 => (fromWords [0x1293e14a4a3df23, 0xe36ed555e16c4615, 0x295bb3e15f0d05ea, 0x6146ed2955510d76, 0x585dbb3416ecf854, 0xf3434a4f84d02796, 0xc4f8d854a56ed555, 0xbb3e1614d05ea617])
  | 40 => (fromWords [0xf80656ed299853, 0xe17c9b1dbb555615, 0x295ea6176ed29529, 0x3e161483dd94a76e, 0xcd05bb5556ecf852, 0x93437c9295f23416, 0xed555292e97c8d0d, 0xbb5556ed4f5854a6])
  | 41 => (fromWords [0x1bb5554a4f85bb0, 0x55765859bb3413e0, 0x815a04a7614d05f2, 0x6166ed5558534183, 0xf8df26156ed555f, 0x26806ed555853414, 0x8cf86024a46ed855, 0xf26156ed555bb341])
  | 42 => (fromWords [0x1854a479d55de13, 0x416ecf858553d6ed, 0x295293e17f0d0df2, 0x3e16ed555bb55561, 0x54f5293e16155252, 0x945d3e0d05bb5556, 0xecf85293417fcd0d, 0xbb5d9555295f253c])
  | 43 => (fromWords [0x1bb5554a4f84f83, 0x417c8b45bb555614, 0xd0d8545d4a4f84f8, 0x3416ed294f80f961, 0x52997c5557a9851b, 0xb4a578529dbb3e13, 0xe0d04d002b7c9859, 0xbb5557c9185bb555])
  | 44 => (fromWords [0x1293e16ecd05852, 0xe97c8d0dbb5556ed, 0x295293e13e0d05bb, 0x555555295bb3e155, 0x4a15ea3e36ed294d, 0x17961555dbb3417, 0x845bd554a66ecf85, 0xe10fb615299bb3e1])
  | 45 => (fromWords [0x1bb5556ec5c5555, 0x3e4a4f85552ff808, 0xd0dbb61568129d29, 0x3e1614d055548f80, 0x9291bb61581d299b, 0xb689614f85bb4a54, 0xa4f85bb3417fcd0d, 0xf24a56ed555bb555])
  | 46 => (fromWords [0x1f22b76ed555293, 0x436ed295bb3413e0, 0xd06027a86ed855bb, 0x4a56edb95855c155, 0x4d05bb555460f898, 0x54a46eda05853413, 0xe0d05f24636ed555, 0x854a47c9295f2343])
  | 47 => (fromWords [0x1bb5556ecf85233, 0x41809291bb615809, 0x17dbb6153e0d0602, 0x4a76ed855853416e, 0xd2954f3434a4f85b, 0xb55553cd0d293e17, 0xc8b4dbb555614d0d, 0x7c3e27a9851bb4a5])
  | 48 => (fromWords [0x1bb341830f8df26, 0x156ed555f23436ed, 0x555853417c929dbb, 0x5556ecd05f26166e, 0xd555bb3417c917db, 0xb5553e0d05ea6806, 0xed295853417c87f5, 0xbb55561529df2615])
  | 49 => (fromWords [0x1bb3e1614d04f83, 0x416ed4f5853e14a4, 0xf8555055765859bb, 0x3417c8d05bb5553e, 0xd05f26156ed5558, 0x53436ed5292945d3, 0xe0d05bb555615295, 0x293e16ed555d93e3])
  | 50 => (fromWords [0x1293433e0d05552, 0x1578529dbb3e1554, 0x325a24a6614f85bb, 0x5555554f5293e161, 0x43e5bb4a56152995, 0x52877a8f8dbb4a56, 0x143e5bb555615299, 0xe16176ecf8585341])
  | 51 => (fromWords [0x1853416ed855bb4, 0xa5615295f26176ed, 0x555bb3417fcd0df2, 0x4a56ed555bb55546, 0xd09854a43404b5f, 0x26176ed5555548d8, 0x9291bb6156ed175, 0x853413e0d05bb3e1])
  | 52 => (fromWords [0x1bb4a56ecb45853, 0x436ed555bb3413e0, 0xd04f80956eda0985, 0x3416ed855bb16d55, 0x5299bb17961555db, 0xb4a53e0b55b13436, 0x15295b145f615294, 0xf83416ed555a03e3])
  | 53 => (fromWords [0x1bb681614d05855, 0xd96ed555554a5555, 0x295bb3e14a4f85bb, 0x55561529dbb3416e, 0xd555854a66ecf85d, 0x96c4615295bb3413, 0x40a15ea3e36ed295, 0xbb555614965293e3])
  | 54 => (fromWords [0x1853417c8985bb5, 0x55614f8dbb555460, 0xf85854a4614ad529, 0x3433e0d05bb5556e, 0xcf85293e16ed855b, 0xb3e1614d04d00856, 0xed859293416ed555, 0xa0557614d06064a7])
  | 55 => (fromWords [0x1ea3436ed294f83, 0x417c929dbb5556ec, 0xf85233e2809291bb, 0x6157c896dbb5554a, 0x4f8d8545d6ecf84f, 0x83417c94fdbb5554, 0xa4f85293e16ecd04, 0xf83416ed55585555])
  | 56 => (fromWords [0x1bb5554a4d05d95, 0x3e4a4f85bb3417c9, 0xa01bb555614d060c, 0x3437c9855bb55534, 0x985853e34a4d05f, 0xf3407c9295bb5556, 0xed855bb2b54a4d0d, 0x854a54a4f8585341])
  | 57 => (fromWords [0x1293417c94f1bb5, 0x554a4f85854a5614, 0xd04f8341554115e1, 0x4a66ecf85bb62961, 0x45b5554a6808f8db, 0xb6153e0d04d00297, 0xc9859bb5557a1555, 0xbb461615291f2509])
  | 58 => (fromWords [0x20c3e07c9855bb5, 0x556edb19bb555615, 0x2960225b6ed85529, 0x3e36ed5555553e4a, 0x4f85bb555614d04f, 0x83417fcd0df24a56, 0xed555bb6156154f5, 0x293e16eda0585341])
  | 59 => (fromWords [0x1ea6176ed294d01, 0x1178585dbb3e1601, 0x295f26146ed555bb, 0x5554a4d0cf83416e, 0xd855bb53d4a4f85f, 0x26176ed555bb3e17, 0xc9a0dbb555614d05, 0xbb6c66ed295854a5])
  | 60 => (fromWords [0x1853417c8d0dbb5, 0x556ecd05bb5556ec, 0x5e5855576ed855bb, 0x4a5615295fb3e37c, 0x8d05bb5556ed555b, 0x13e3615295f24a56, 0xed555293e3614ba5, 0xf23436ed5555511d])
  | 61 => (fromWords [0x1bb4a56ed295293, 0x416ed859854a56c4, 0xd0d854a5614f8d29, 0x3416edba5855d955, 0x5295ea5576ed2952, 0x93e17c8965bb5554, 0xa4f8dbb6156ec965, 0x293e36eda05854a5])
  | 62 => (fromWords [0x1bb4a64a4f85292, 0x61614f8d292d1614, 0xd0e024a66ed855bb, 0x555555294f82b54a, 0x4d0cf816d555299b, 0xb4a54a4f85f26176, 0xed555290856ed859, 0xbb3e14a4f85ea557])
  | 63 => (fromWords [0x1853436ec5e5855, 0x576ed855854a56c5, 0x555854a5614f8529, 0x3e16ed855293e37c, 0x9855bb5557a9859b, 0xb4a56ed555853416, 0xedb19854a56ed18d, 0x854a46ed85555341])
  | 64 => (fromWords [0x1bb5554a4f85bb6, 0xc5615295e14a76ec, 0xf85855c1554d05e1, 0x3436ecf85bb46161, 0x5291bb616614d058, 0x53e16ecd05bb5556, 0xecf85bb2d1614d0d, 0xbb615555299bb4a5])
  | 65 => (fromWords [0x1854a66ed295854, 0xa761542d29341765, 0x85dbb341765859bb, 0x3413405e58555761, 0x52958534176529db, 0xb3416ecd05853416, 0xed295293e1615555, 0xbb34155518d854a4])
  | 66 => (fromWords [0x1850656ed299d96, 0x146ecd06024a46ed, 0x855bb615614d05bb, 0x53e4a4f858553d4a, 0x4f855545e3e0d05b, 0xb4a6614f85bb3414, 0xa4d05bb4a5615299, 0xb13e3615295bb555])
  | 67 => (fromWords [0x1bb3416ed765554, 0xa56ed854f8341614, 0xf8dbb3414a45e585, 0x5577c929dbb5556e, 0xd555853437a9859b, 0xb4a5615295853437, 0xc9859bb555765859, 0xbb3417c9855bb555])
  | 68 => (fromWords [0x1bb615615295bb3, 0xe1614f85bb556615, 0x295f26176ed55555, 0x4a64a4f85bb5554a, 0x4f85ea6156ed2960, 0x23e16ed855bb1fd6, 0x1529dbb261614f8d, 0xb1341615295d9557])
  | 69 => (fromWords [0x1854a67c8f8dbb5, 0x555554f5293e1615, 0x4f5293e16ed85929, 0x343615295293e161, 0x5555bb4a56ed2998, 0x53e380929dbb6156, 0xeda05853416ed555, 0x854a76ed295853e1])
  | 70 => (fromWords [0x1bb6164a4d06023, 0xe36ed855a04a5614, 0xd05e16176ecf85e1, 0x4a66ecf84f80656e, 0xd299293e13e0d058, 0x55576ecd05a03e16, 0x14d05554a66ecf85, 0xf24a66ed554f80f9])
  | 71 => (fromWords [0x1554a66ed555853, 0xe178555dbb3e153c, 0xd0d293e161529d85, 0x3416ed855853416c, 0x555d854a56ed5598, 0x5341460f89854a47, 0xa9555bb4a56ed4f5, 0x293e16ed295553e1])
  | 72 => (fromWords [0x1bb555615555bb5, 0xc5554f85bb6156ec, 0xf85854a56ecd0529, 0x876ed859e14a66e, 0xcf855525b4a4f8db, 0xb6154a4d0d850676, 0xed299d95556ecd05, 0xbb4a5614f8dbb16d])
  | 73 => (fromWords [0x15553d4a4f85bb6, 0x15614d0d854a57a8, 0xf8dbb4a5614add29, 0x3436ed705553416c, 0x4d0d854a56152952, 0x93e16ed855293418, 0x8d05bb6154a4f85, 0x853416eda25853e1])
  | 74 => (fromWords [0x1bb5556ed855bb4, 0xa5785555bb3e16ed, 0x55555341680f8d85, 0x341555185854a46e, 0xd555553e1460d098, 0x54a46145b5554a66, 0xecad5293436eda09, 0x853416ed855554a5])
  | 75 => (fromWords [0x1855576ed295bb5, 0x55614f8da0557614, 0xd05855d9555295bb, 0x4a54a4f8dd94a56e, 0xcd05bb53d4a4f85b, 0xb5554a4f8d852594, 0xa4f8de16156ecf85, 0xbb6c6615295f24a5])
  | 76 => (fromWords [0xf83416ecf84f83, 0x41555170f83416ed, 0x855854a761555585, 0x341460f85854a47c, 0x8d0dbb5556ed5555, 0x54a6809555bb6156, 0x15295bb3e1764f85, 0xbb3416ec965293e3])
  | 77 => (fromWords [0x1bb6154a4f85e14, 0xa56ecf85d96156ec, 0xd05bb6c5615295bb, 0x5564a4f85bb45d3e, 0xd05ea6176ed2960, 0x23436ed855a24a66, 0x14f84d00856ed859, 0xbb5094a4d05bb4a5])
  | 78 => (fromWords [0x1bb5556ed299854, 0xa5554965293e36ed, 0xa05853414a498d85, 0x3e36c4f8d854a534, 0x985853e34a4d0cf, 0x83416ed295854a57, 0xc8f8dbb5555554f9, 0x293e1614d04f8341])
  | 79 => (fromWords [0xd017961555dea3, 0xe16ed295ea6146ed, 0x295bb55561555dbb, 0x3e1614d05e13416e, 0xcf85a04a7614d05b, 0xb461615291554a54, 0xa4f85bb615615299, 0xbb4a56ecd05f24a5])
  | 80 => (fromWords [0x1bb555554b4d853, 0x436ecf85293417a8, 0xd05bb4a561555555, 0x4a5615425293417c, 0x8f85bb5556815558, 0x53416ed554f83416, 0x15174f83416ecf85, 0x293436ed855853e1])
  | 81 => (fromWords [0x1853e33e0d05853, 0xe14a4d0e024a66ed, 0x855bb4a56152954f, 0x3414a4f85bb55561, 0x5295293e16ecd055, 0x54a56ecf85bb4a56, 0x14d05bb6dd615555, 0x18341615291f2341])
  | 82 => (fromWords [0x1bb6156c4f85854, 0xa53407f5854a76ed, 0x855853e3614ad529, 0x3436ed555854a43e, 0x5bd554a6785291b, 0xb3e1614f85293413, 0x405ed8555761555d, 0x853416ed555bb341])
  | 83 => (fromWords [0x1b1557615295bb5, 0x55614d05bb0f9615, 0x299854a5614d05f2, 0x4a46ed555f23e16e, 0xd555d93e36ecd05e, 0xa3436ed295853414, 0xa4d05854a64a4f85, 0xf23436ed55602557])
  | 84 => (fromWords [0x1853436ed555bb3, 0xe16ed295293437c9, 0x851bb5556ed55585, 0x4a57c929dbb55561, 0x4f8d293436ed5552, 0x93437c8d05bb5553, 0xe05b5554a6809295, 0xbb615615295293e3])
  | 85 => (fromWords [0x185555614f85bb4, 0xa56ecf85bb4a6615, 0x29dbb5554a4d0585, 0x4a76ecd05bb5556e, 0xcd05854a66ecf858, 0x553e4a4f85854a53, 0xe0d05bb3413e0d05, 0x2945d3e0d05552d1])
  | 86 => (fromWords [0x6ecd05853, 0x43615299293e16ed, 0x855bb556555295bb, 0x6164a4d052934361, 0x4d05854a4615294f, 0x83416ed555855575, 0x55299853e36ed555, 0x293e3554d05553e1])
  | _ => 0
def opAt (i : Nat) : Nat := fld (opAtBlock (i / 23)) 22 (i % 23)
def opDescriptorBlock : Nat → Nat
  | 0 => (fromWords [0x1c8000000, 0x0, 0x520, 0x0, 0x154002800, 0x0])
  | 1 => (fromWords [0x3480000000, 0x0, 0xb200, 0x0, 0x124])
  | 2 => (fromWords [0x132, 0x0, 0x0, 0x0, 0x44800000f20000])
  | 3 => (fromWords [0x3e400000000, 0x0, 0x3a4000000001b, 0x2000000000000000, 0x64800000000, 0xb9000002, 0xa400000000000000, 0x0])
  | 4 => (fromWords [0x1490, 0x0, 0x0, 0x0, 0x0, 0x9c8129000000, 0x8c80000000042, 0x4000000000000000])
  | 5 => (fromWords [0x3120000000000000, 0x0, 0x0, 0x0, 0x5e40000169000000, 0x56, 0x4000000000000000])
  | 6 => (fromWords [0x4520000000000004, 0x32000010481f9000, 0x1e90000, 0xec81c900000, 0x37206, 0xa40cc80000000000, 0x0])
  | 7 => (fromWords [0x9a4000000004, 0xb200000000000000, 0x2490000, 0x0, 0x0, 0x0, 0x8e4])
  | 8 => (fromWords [0xc731886304c, 0x5f18be0176600000, 0x17062d4c00, 0x16462bcc000, 0xac3152600000000, 0xa630000000051200, 0x0, 0x27900000000])
  | 9 => (fromWords [0x7898ee300003acc, 0x7418e530000388c0, 0x0, 0x6f9, 0x80001b8600006c98, 0x6b18d, 0x331a0600000000cd, 0x3194600000000000])
  | 10 => (fromWords [0x12730000490c, 0x121323c600008, 0xd9918322a6000089, 0x190f32186424c831, 0x9033000000008018, 0x3f4c00000, 0x7d1800, 0x3dcc7a18000])
  | 11 => (fromWords [0xb9180002de65b0c, 0xb4996632c66580ca, 0xe980002b460000ab, 0x995432a26538ca59, 0x948328a60000a119, 0x3f32786000000013, 0x9326c60000999930, 0x30000000096992a3])
  | 12 => (fromWords [0xd2980000000688c, 0xcf9800000000000c, 0xe180000000664ccb, 0x180003266640c000, 0x18d331460000c398, 0x610cc0980, 0x2fc60000000000, 0x2f665e0cba98000])
  | 13 => (fromWords [0x3da67a8c, 0xf399e433c26778ce, 0xd980003b06754ce9, 0x19cf339860000e49, 0x800038c670cce019, 0xbd300006e8c00000, 0x36e66d0c0001b1, 0x335c60000d599a83])
  | 14 => (fromWords [0x1101a1d3434685cc, 0x4286844d0, 0x7180000000000000, 0x20b341060000000, 0x40a6808c0001, 0xff33f8600000001f, 0x9300007d8c000000, 0x7cccf818000])
  | 15 => (fromWords [0x1269a4a300000000, 0x24730000910c0, 0x120, 0x9a3e300008ecc000, 0x238346a600000002, 0x32345e6000000022, 0xc300008a4c000226, 0x3446600000000000])
  | 16 => (fromWords [0x13a1800000000000, 0x27134dc600000, 0x26b300009a0c00, 0x265300000000000, 0x2, 0x6234be600012e1a5, 0x9300000000000256, 0x3000094cc0002503])
  | 17 => (fromWords [0x2a4354260000, 0x53c6a6cc0, 0x2983000000014a, 0x9a9230000a3cc000, 0x518600000002, 0x89350c6a0cd40180, 0x4fa69e8c000000, 0x13b98000])
  | 18 => (fromWords [0x16e9ada35ae60000, 0x2d435a2600016, 0x71acb30000b20d62, 0x9ac2300000000000, 0x2bf3578600000002, 0xb930000ad8d599ab, 0x355a6aa8c000000, 0x2a73])
  | 19 => (fromWords [0x188180000000c34c, 0x30a360e6c10d8, 0x9afe35f66000000, 0x2f8300000000000, 0x5ea6bc8c0000, 0xbbcd761ae, 0x930000b98c0002e3, 0x3000000000002e03])
  | 20 => (fromWords [0x1a19800068060001, 0x9e98000000000000, 0x33a366e6cd0c00, 0x1989, 0xb2e30000cacc0003, 0x28364a6c88d8f980, 0xc70c000319, 0x362c6c4cc0000000])
  | 21 => (fromWords [0x37c36f26dd8d, 0xb9980006e060001b, 0x69b6a36ce6d90c00, 0x361300000000000, 0x35e36b66d60daa9b, 0x52300000001a7980, 0x69860000000000, 0x692600000003463])
  | 22 => (fromWords [0x3b530000ec8c, 0xebcc0, 0x3ac37526e98dd1, 0x9ba030000e74c000, 0x39a30000e5cc0003, 0x94300000001c89b8, 0xe37166e20dc29800, 0x70460001bf98000])
  | 23 => (fromWords [0x7dc6facd, 0xf4180000000f94df, 0x11bdf300000001ee, 0x1bd937ac60000000, 0x7a660001e81b, 0xcd37946f1cc0003c, 0x43782600000003be, 0x300000001dd9bb83])
  | 24 => (fromWords [0x2181800085a70a8c, 0x42738487084c0, 0x41e38367060c00, 0x82a7048c000, 0x2079c, 0xc30001024c00040, 0x638067000dfe9bfa, 0x37ee6fd0df898000])
  | 25 => (fromWords [0x22e980000001168c, 0x8ae7150c0, 0x0, 0x45130001138c000, 0x8967120e229c, 0x42300010fcc00000, 0x10f0c000000, 0x87270d8c0004333])
  | 26 => (fromWords [0x2469800000000002, 0x4518000000121cc0, 0x9086000240, 0x9c7e38f6600023c1, 0x80008ea71c8c0000, 0x2379c6, 0xc300000000000469, 0x38cc718cc0004603])
  | 27 => (fromWords [0x9987324e, 0x6318000000130ce6, 0x1800000012f4c00, 0x4ba396e72d0c000, 0x4b1300012b8c0004, 0xab39507294e511c9, 0xf3938600024c9c96, 0x3000124cc0004903])
  | 28 => (fromWords [0x1420c, 0x5053a04600000, 0x4ff39f873e4e7b, 0x1800000000002799, 0x80009e073b4e7518, 0x9ce7390e709cd, 0xe3000136cc000000, 0x9b07354e691ccf3])
  | 29 => (fromWords [0x2a99d5030001534c, 0x1528c0, 0x5473a887504e9f, 0x1d3b3a7074d4e991, 0xd2f3a5874a4e931d, 0x2330001480e8e9d1, 0xa3a2e600028a1d11, 0x30001438e8598000])
  | 30 => (fromWords [0xb0c60002, 0xc198000b00600000, 0x57d3af475dcc00, 0x5743ae275b8c000, 0x56b300000002b41d, 0x6530001588c00000, 0x157cc000000, 0xab87564eab18000])
  | 31 => (fromWords [0x2e495c72b8a570ca, 0xe095bf2b7a56ecad, 0xc95b72b6a56ccad8, 0x95af2b5a56acad49, 0x5a72b4a568cad095, 0x9f2b3a566cacd859, 0x92b2e5654ac99591, 0x2b1e5634ac595892])
  | 32 => (fromWords [0x306960b2c12581cb, 0x296032c0257fcaf, 0xe95fb2bf257dcafa, 0x95f32be257bcaf69, 0x5eb2bd2579caf295, 0xe32bc2577caee95d, 0xb2bb2575caea95d3, 0x2ba2573cae695cb2])
  | 33 => (fromWords [0x328964f2c9a592cb, 0x2496472c8a590cb2, 0x963f2c7a58ecb1c, 0x96372c6a58ccb189, 0x62f2c5a58acb1496, 0x272c4a588cb10961, 0xf2c3a586cb0c9617, 0x2c2a584cb08960f2])
  | 34 => (fromWords [0x34a96932d225a3cb, 0x46968b2d125a1cb4, 0x296832d0259fcb3e, 0x967b2cf259dcb3a9, 0x6732ce259bcb3696, 0x6b2cd2599cb32966, 0x32cc2597cb2e965b, 0x2cb2595cb2a96532])
  | 35 => (fromWords [0x36c16d62da85b48b, 0x6816ce2d985b28b6, 0x416c62d885b08b60, 0x16be2d785ae8b5c1, 0x6b62d685ac8b5816, 0xae2d585aa8b5416a, 0x62d485a88b508e9f, 0x2d3a5a6cb4c96972])
  | 36 => (fromWords [0x38e171a2e305c58b, 0x8a17122e205c38b8, 0x6170a2e105c18b82, 0x17022e005bf8b7e1, 0x6fa2df05bd8b7a16, 0xf22de05bb8b7616e, 0xa2dd05b98b7216e2, 0x2dc05b78b6e16da2])
  | 37 => (fromWords [0x3b0175e2eb85d68b, 0xac17562ea85d48ba, 0x8174e2e985d28ba4, 0x17462e885d08ba01, 0x73e2e785ce8b9c17, 0x362e685cc8b98172, 0xe2e585ca8b941726, 0x2e485c88b90171e2])
  | 38 => (fromWords [0x3d217a22f405e78b, 0xce179a2f305e58bc, 0xa17922f205e38bc6, 0x178a2f105e18bc21, 0x7822f005df8bbe17, 0x7a2ef05dd8bba177, 0x22ee05db8bb6176a, 0x2ed05d98bb217622])
  | 39 => (fromWords [0x3e68fcc1f963f287, 0xe48fc81f8e3f187e, 0x28fc41f863f087e0, 0x8fc01f7e3ef87de8, 0xfbc1f763ee87dc8f, 0xb81f6e3ed87da8fb, 0x41f681ec8bd817ae, 0x2f585ea8bd417a62])
  | 40 => 0x1f403e78fce1
  | _ => 0
def opDescriptor (i : Nat) : Nat := fld (opDescriptorBlock (i / 34)) 15 (i % 34)
def useMaskBlock : Nat → Nat
  | 0 => (fromWords [0xc001000000000, 0x0, 0x2000004, 0x0, 0x0])
  | 1 => (fromWords [0x1000, 0x0, 0x0, 0x0, 0x80000000000000, 0x0, 0x0, 0x200000])
  | 2 => (fromWords [0x80000000, 0x0, 0x0])
  | 3 => (fromWords [0x10000000000000, 0x0, 0x0, 0x0, 0x0, 0x2000000200000])
  | 4 => (fromWords [0x2000000000020000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0])
  | 5 => (fromWords [0x200000000000, 0x0, 0x0, 0x80000000000020, 0x0, 0x0, 0x2000000000000])
  | 6 => (fromWords [0x8000000, 0x20000000000004, 0x0, 0x2000000000000])
  | 7 => (fromWords [0x800000000, 0x40000000000000, 0x0, 0x8000000000000, 0x0, 0x4, 0x0, 0x0])
  | 8 => (fromWords [0x40000000, 0x0, 0x0, 0x0, 0x0, 0x0])
  | 9 => (fromWords [0x200000000001000, 0x40000000000000, 0x4000000, 0x2080, 0x0, 0x2000000, 0x10100000000000, 0x0])
  | 10 => (fromWords [0x20000000000000, 0x800000, 0x0])
  | 11 => (fromWords [0x400000000, 0x0, 0x0, 0x4000000000000, 0x200000000, 0x0, 0x400000, 0x0])
  | 12 => (fromWords [0x40000100000000, 0xc200a050, 0x120000000d050044, 0x4000000000000020, 0x0, 0x4000000000000000, 0x0])
  | 13 => (fromWords [0x3118c0000000100, 0x0, 0x31003000100010, 0x800000000000000, 0x100010000000000, 0x0, 0x4048001000400001, 0x8100080])
  | 14 => (fromWords [0x2000010000000400, 0x2200000040, 0x4000000202000, 0x2115200000000, 0x0, 0x0, 0xc0010000000])
  | 15 => (fromWords [0x20000001000, 0x4000240030000, 0x2000060000, 0x1003414801002074, 0x80000000000001, 0x0, 0x10000000000000, 0x20])
  | 16 => (fromWords [0x202000400000000, 0x40000000020800, 0x0, 0x204000000000004, 0x2000000000000, 0x80001000, 0x201000000000, 0x20000002c0820])
  | 17 => (fromWords [0x2000, 0x8000080000, 0x140000001d0, 0x204002000002004, 0x80000204000010, 0x2105200, 0x1020800000, 0x2080000000020])
  | 18 => (fromWords [0x10040000000000, 0x2010000000, 0x4004801000000, 0x10000400000, 0x80000000, 0x8020800000, 0xc4048000000])
  | 19 => (fromWords [0x20000002000, 0x40400000020048, 0x80000000, 0x21004084, 0x8000004000000, 0x20000000004204, 0x100128000000, 0x4000100000])
  | 20 => (fromWords [0x110800000000000, 0x20200, 0x0, 0x8006800004000, 0x1001004a04001000, 0x800000280000000, 0x80401a0800000, 0x1000000040000000])
  | 21 => (fromWords [0x4000008000020000, 0x0, 0x800002000, 0x20, 0x400000000000, 0x8080000000000, 0x8000000])
  | 22 => (fromWords [0x80000000008, 0x8081000000000000, 0x12014008000, 0x20400000, 0x10000000000, 0x800000280000000, 0x800000, 0x2000008000020])
  | 23 => (fromWords [0x200000000004, 0x8000, 0x200020000000000, 0x800, 0x80000000, 0x0, 0x2000008000000])
  | 24 => (fromWords [0x2000210000000000, 0x40000000201, 0x20000000, 0x0, 0x0, 0x200000000080, 0x40080c0026])
  | 25 => (fromWords [0x80000, 0x100060000, 0x408000, 0x1000080000080000, 0x1000000041000, 0x0, 0x50020000000, 0x2000000000000])
  | 26 => (fromWords [0x1000000081d00, 0xa000000000000000, 0x180, 0x200000010002200, 0x80000000000000, 0x800002000000, 0x201000000000, 0x80108000020])
  | 27 => (fromWords [0x20000000000, 0x83118e0000, 0x8000040400, 0x400010000010, 0x0, 0x2000000200, 0x40080, 0x40020200000])
  | 28 => (fromWords [0x100160000000000, 0x401, 0x5804002000000000, 0x10000000, 0x8002018000001c, 0x20000000000200, 0x1, 0x800010001004020])
  | 29 => (fromWords [0x20000000000, 0xc4806000000400, 0x4080000000, 0x2000, 0x8000000, 0xc080a0400000, 0x8000400800200, 0x4100000000000000])
  | 30 => (fromWords [0x800000000, 0x4000000000000, 0x101, 0x80000002000, 0x0, 0x800000c0, 0x11000001, 0x20000020])
  | 31 => (fromWords [0x100500000, 0x900, 0x800080080000000, 0xa00000800000000, 0x408000000004, 0x1000000000000000, 0x40000000000, 0x44000941020])
  | 32 => (fromWords [0x481004, 0xa480000100000400, 0x40000000, 0x400000000000, 0x20180000800, 0x400040000000000, 0x4000000000400000, 0x2200408100000])
  | 33 => (fromWords [0x800080000, 0xa0408400000000, 0x80020000, 0x2000000002040, 0x2008204000000, 0x800000000000, 0x408000000000400, 0x8000000])
  | 34 => (fromWords [0x40200020, 0x8000000000, 0x1008000, 0x800004040, 0x2000000000010, 0x20001000000000, 0x40000000, 0x800000100a0])
  | 35 => (fromWords [0x800000000, 0x10200800044, 0x2000008000, 0x202000020200000, 0x0, 0x80100100000200, 0x82, 0x84148000000])
  | 36 => (fromWords [0x200000201204000, 0x210150020000, 0x10000014048200, 0x2084, 0x281000000000000, 0x40080000400, 0x0, 0x80000011020])
  | 37 => (fromWords [0x60000000400, 0x2000000000000281, 0x200001020000000, 0x80000004000000, 0x8, 0x148000000000000, 0x2080000000000])
  | 38 => (fromWords [0x60000800000, 0x100, 0xc100c01000000, 0x808000080, 0x2000000, 0x48082, 0x4082000000000000])
  | 39 => (fromWords [0x400000010, 0x0, 0x2000000000, 0x800000000, 0x1110200000000, 0x20800000001000, 0x100000000, 0x2042000000000])
  | 40 => (fromWords [0x3020, 0x3000000000040200, 0x40000000200, 0x4000, 0x1000002000820, 0x40002101200, 0x4000000000000080, 0x14000000100000])
  | 41 => (fromWords [0x50520000001000, 0xc400a100000001, 0x4008000, 0x2000, 0x80100008000000, 0x1000001, 0x8100000000000, 0x8000400])
  | 42 => (fromWords [0x350020200000000, 0x0, 0x30000000000100, 0x8004000000000000, 0x204000000, 0x20000080000000, 0x100000, 0x84020000080])
  | 43 => (fromWords [0x81000, 0x4008102000804, 0x2010000100, 0xc001000002004, 0x2000400404800, 0x341400008004, 0x200000000000, 0xa000100000000])
  | 44 => (fromWords [0x104000000, 0xa000000000800000, 0x0, 0x400000000000000, 0x4081020000004000, 0x400008000200, 0x80000000000, 0x80])
  | 45 => (fromWords [0x2c0824201493d0c, 0x2090100000000000, 0x84000000100, 0x100000, 0x2000004, 0x800088000000, 0x148c80425020080, 0x8000000])
  | 46 => (fromWords [0x80421044203b05, 0x40200583104a2c41, 0x6821008020108390, 0x5a0020003f1028c4, 0x1283505a0f440839, 0x18a2ec4483f00a00, 0x81a0024c4538b, 0x105a0ec00a3118a4])
  | 47 => (fromWords [0x350da0d400c0004, 0x10c47c82c0600d42, 0xc310630ec009010, 0x80f4148390120c4, 0x9710128c66b835, 0x2128f41687107b08, 0x4031216ad41684, 0x800e010308311521])
  | 48 => (fromWords [0x30214080100311d, 0x20e4008b50520001, 0x13c0580c4148b50, 0x5a004130fd1420d4, 0x1683d1421c418873, 0x120081403521206, 0x402c0830301095, 0x400f4108000424])
  | 49 => (fromWords [0x35000cc0580804, 0x68140010080201, 0x3104210008c790, 0x5204004008042140, 0x15a391ce0c4108bd, 0x4040444000004054, 0x427105a1c41286, 0x40200c4e2c3918a6])
  | 50 => (fromWords [0x3130e8dc2483d07, 0x8080188410000c47, 0x383d04a004601820, 0x2c01000240400c4, 0x584c0200c405a3d, 0x1120fc4483f29008, 0x100102340600003, 0xd0022fc5483130e2])
  | 51 => (fromWords [0x390420c40493905, 0xa0c6e2ca80000ec1, 0x5024000080084740, 0x100c405a7114e2c5, 0xc3a900569800003d, 0x5a0200023d00e02, 0x83d05a0860048, 0x420f4029310520])
  | 52 => (fromWords [0x311ae0c46383c10, 0x243000533012cf40, 0x483d152000142790, 0x420e440888042545, 0x2b1b8a2d40d83d, 0x5a0c5c38b905a0f, 0x4138391024d40880, 0x11000cd6383005a1])
  | 53 => (fromWords [0x611000097918, 0xe0d484e310424d40, 0x87d1160d41e8350, 0x834d0a00302128c4, 0x638080521c43b03d, 0x5a0c4e28bd00a20, 0x4030d00000408063, 0xd112400708310420])
  | 54 => (fromWords [0x3905a4c4548b001, 0x80806350e20f41, 0x683b1840200086c0, 0x834246018c0421f4, 0x448350231f412839, 0x560d41a83830002, 0x109310122cc6383, 0x52740400480a000c])
  | 55 => (fromWords [0x80001201092628, 0xe4108340000044, 0x240020c4538fd0, 0x5a0d6008b11d2050, 0x240014e473035, 0xa20c5048818280d, 0x4848352760600001, 0x561c45c812000c])
  | 56 => (fromWords [0x3d1424f43803d00, 0x2245002b52130d42, 0x93d0e00fc540350, 0x22c4438520100d4, 0x1e81004a1e45083d, 0x520f40383d11201, 0x40311d20c63403, 0x50030c0920180100])
  | 57 => (fromWords [0x390420f40082404, 0xd4a0c980100cc1, 0x58302040d080c3f2, 0x920d4168310128a0, 0x4093105220400839, 0x18a2201003900208, 0x6004bf00e0200017, 0xc1500e4738350420])
  | 58 => (fromWords [0x3138e0e46383105, 0xa0f4608391020d43, 0xf83d05a0f4778352, 0x960c4e38b11d20f4, 0x383104a0c40083d, 0x1120c6e383178e0c, 0x47383105e0f46093, 0x12168f44083d05a0])
  | 59 => (fromWords [0xc, 0x4008352830d41683, 0xd15a0fc6583105e1])
  | _ => 0
def useMask (i : Nat) : Nat := fld (useMaskBlock (i / 23)) 22 (i % 23)
def readOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, k =>
    let v := opAt k
    (v &&& 3, wireAt ((v >>> 2) &&& 1023), wireAt (v >>> 12)) :: readOps n (k+1)
def PO (s i : Nat) :=
  let v := opDescriptor (offset s + i)
  readOps (v &&& 15) (v >>> 4)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := useMask (offset s + i)
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom15, 4, runOps true dom15 (0, roots15) ops)] else []) ++
    (if pm.testBit 1 then [(dom23, 4, runOps true dom23 (0, roots23) ops)] else []) ++
    (if pm.testBit 2 then [(dom27, 4, runOps true dom27 (0, roots27) ops)] else []) ++
    (if pm.testBit 3 then [(dom29, 4, runOps true dom29 (0, roots29) ops)] else []) ++
    (if pm.testBit 4 then [(dom30, 4, runOps true dom30 (0, roots30) ops)] else []) ++
    (if pm.testBit 5 then [(dom31, 7, runOps true dom31 (0, roots31) ops)] else []) ++
    (if pm.testBit 6 then [(dom37, 4, runOps true dom37 (0, roots37) ops)] else []) ++
    (if pm.testBit 7 then [(dom39, 5, runOps true dom39 (0, roots39) ops)] else []) ++
    (if pm.testBit 8 then [(dom45, 5, runOps true dom45 (0, roots45) ops)] else []) ++
    (if pm.testBit 9 then [(dom46, 4, runOps true dom46 (0, roots46) ops)] else []) ++
    (if pm.testBit 10 then [(dom47, 6, runOps true dom47 (0, roots47) ops)] else []) ++
    (if pm.testBit 11 then [(dom50, 4, runOps true dom50 (0, roots50) ops)] else []) ++
    (if pm.testBit 12 then [(dom51, 5, runOps true dom51 (0, roots51) ops)] else []) ++
    (if pm.testBit 13 then [(dom52, 4, runOps true dom52 (0, roots52) ops)] else []) ++
    (if pm.testBit 14 then [(dom53, 5, runOps true dom53 (0, roots53) ops)] else []) ++
    (if pm.testBit 15 then [(dom54, 5, runOps true dom54 (0, roots54) ops)] else []) ++
    (if pm.testBit 16 then [(dom55, 7, runOps true dom55 (0, roots55) ops)] else []) ++
    (if pm.testBit 17 then [(dom57, 4, runOps true dom57 (0, roots57) ops)] else []) ++
    (if pm.testBit 18 then [(dom58, 5, runOps true dom58 (0, roots58) ops)] else []) ++
    (if pm.testBit 19 then [(dom59, 6, runOps true dom59 (0, roots59) ops)] else []) ++
    (if pm.testBit 20 then [(dom61, 7, runOps true dom61 (0, roots61) ops)] else []) ++
    (if pm.testBit 21 then [(dom62, 7, runOps true dom62 (0, roots62) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (ws : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) ws
theorem mkCut_sound {s i g ws} (h : mkCut (s + 1) i g ws = true) : ¬ RunD true dom63 goalM s ws := by
  unfold mkCut mkPools at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨e, he, hchk⟩ := List.any_eq_true.mp h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) low15 _ g hchk
    · exact cpcs (by decide +kernel) low23 _ g hchk
    · exact cpcs (by decide +kernel) low27 _ g hchk
    · exact cpcs (by decide +kernel) low29 _ g hchk
    · exact cpcs (by decide +kernel) low30 _ g hchk
    · exact cpcs (by decide +kernel) low31 _ g hchk
    · exact cpcs (by decide +kernel) low37 _ g hchk
    · exact cpcs (by decide +kernel) low39 _ g hchk
    · exact cpcs (by decide +kernel) low45 _ g hchk
    · exact cpcs (by decide +kernel) low46 _ g hchk
    · exact cpcs (by decide +kernel) low47 _ g hchk
    · exact cpcs (by decide +kernel) low50 _ g hchk
    · exact cpcs (by decide +kernel) low51 _ g hchk
    · exact cpcs (by decide +kernel) low52 _ g hchk
    · exact cpcs (by decide +kernel) low53 _ g hchk
    · exact cpcs (by decide +kernel) low54 _ g hchk
    · exact cpcs (by decide +kernel) low55 _ g hchk
    · exact cpcs (by decide +kernel) low57 _ g hchk
    · exact cpcs (by decide +kernel) low58 _ g hchk
    · exact cpcs (by decide +kernel) low59 _ g hchk
    · exact cpcs (by decide +kernel) low61 _ g hchk
    · exact cpcs (by decide +kernel) low62 _ g hchk
def Z (s : Nat) := barP true dom63 goalM mpG SD SS NN htAt idxH id 0 [] mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 10 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 64 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_64 : ∀ i, 64 ≤ i → i < 80 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_80 : ∀ i, 80 ≤ i → i < 96 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 112 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_112 : ∀ i, 112 ≤ i → i < 128 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_128 : ∀ i, 128 ≤ i → i < 144 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_144 : ∀ i, 144 ≤ i → i < 160 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_160 : ∀ i, 160 ≤ i → i < 176 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_176 : ∀ i, 176 ≤ i → i < 192 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_192 : ∀ i, 192 ≤ i → i < 208 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_208 : ∀ i, 208 ≤ i → i < 224 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_224 : ∀ i, 224 ≤ i → i < 240 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_240 : ∀ i, 240 ≤ i → i < 256 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_256 : ∀ i, 256 ≤ i → i < 272 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_272 : ∀ i, 272 ≤ i → i < 273 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 1 272 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 273 → Z 5 i = true := (range_split (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48)) (range_split (range_split z5_64 z5_80) (range_split z5_96 (range_split z5_112 z5_128)))) (range_split (range_split (range_split z5_144 z5_160) (range_split z5_176 z5_192)) (range_split (range_split z5_208 z5_224) (range_split z5_240 (range_split z5_256 z5_272)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 160 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_160 : ∀ i, 160 ≤ i → i < 176 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_176 : ∀ i, 176 ≤ i → i < 192 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 208 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_208 : ∀ i, 208 ≤ i → i < 224 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_224 : ∀ i, 224 ≤ i → i < 240 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 256 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 272 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_272 : ∀ i, 272 ≤ i → i < 288 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : ∀ i, 288 ≤ i → i < 304 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_304 : ∀ i, 304 ≤ i → i < 320 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 336 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : ∀ i, 336 ≤ i → i < 352 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_352 : ∀ i, 352 ≤ i → i < 368 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_368 : ∀ i, 368 ≤ i → i < 384 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : ∀ i, 384 ≤ i → i < 400 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_400 : ∀ i, 400 ≤ i → i < 416 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_416 : ∀ i, 416 ≤ i → i < 432 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : ∀ i, 432 ≤ i → i < 448 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_448 : ∀ i, 448 ≤ i → i < 464 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_464 : ∀ i, 464 ≤ i → i < 480 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_480 : ∀ i, 480 ≤ i → i < 496 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_496 : ∀ i, 496 ≤ i → i < 512 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_512 : ∀ i, 512 ≤ i → i < 528 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_528 : ∀ i, 528 ≤ i → i < 544 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_544 : ∀ i, 544 ≤ i → i < 560 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_560 : ∀ i, 560 ≤ i → i < 576 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_576 : ∀ i, 576 ≤ i → i < 592 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_592 : ∀ i, 592 ≤ i → i < 608 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_608 : ∀ i, 608 ≤ i → i < 624 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_624 : ∀ i, 624 ≤ i → i < 640 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_640 : ∀ i, 640 ≤ i → i < 656 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_656 : ∀ i, 656 ≤ i → i < 672 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_672 : ∀ i, 672 ≤ i → i < 688 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_688 : ∀ i, 688 ≤ i → i < 704 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_704 : ∀ i, 704 ≤ i → i < 720 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_720 : ∀ i, 720 ≤ i → i < 736 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_736 : ∀ i, 736 ≤ i → i < 752 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_752 : ∀ i, 752 ≤ i → i < 768 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 16 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_768 : ∀ i, 768 ≤ i → i < 770 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 2 768 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 770 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 (range_split z6_16 z6_32)) (range_split z6_48 (range_split z6_64 z6_80))) (range_split (range_split z6_96 (range_split z6_112 z6_128)) (range_split z6_144 (range_split z6_160 z6_176)))) (range_split (range_split (range_split z6_192 (range_split z6_208 z6_224)) (range_split z6_240 (range_split z6_256 z6_272))) (range_split (range_split z6_288 (range_split z6_304 z6_320)) (range_split z6_336 (range_split z6_352 z6_368))))) (range_split (range_split (range_split (range_split z6_384 (range_split z6_400 z6_416)) (range_split z6_432 (range_split z6_448 z6_464))) (range_split (range_split z6_480 (range_split z6_496 z6_512)) (range_split z6_528 (range_split z6_544 z6_560)))) (range_split (range_split (range_split z6_576 (range_split z6_592 z6_608)) (range_split z6_624 (range_split z6_640 z6_656))) (range_split (range_split z6_672 (range_split z6_688 z6_704)) (range_split (range_split z6_720 z6_736) (range_split z6_752 z6_768))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 279 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 7 272 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 279 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 (range_split z7_112 z7_128)))) (range_split (range_split (range_split z7_144 z7_160) (range_split z7_176 z7_192)) (range_split (range_split z7_208 z7_224) (range_split z7_240 (range_split z7_256 z7_272)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 29 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 13 16 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 29 → Z 8 i = true := (range_split z8_0 z8_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true :=
  span_ok (by decide +kernel : span (Z 9) 1 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s,
    bar true dom63 goalM mpG SD SS NN htAt idxH id 0 [] mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g ws =>
    (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) ws) s i = true
  rw [← barP_eq]
  interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def rootOK (s : Nat) := found SS NN (fun s ws => idxH s (hk 0 ws)) s xsM
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span rootOK 5 5 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noCircuit : Lower true dom63 roots63 goal63 10 := by
  apply lower_of_search (pairs := pairsG) (by decide +kernel) properFail
  intro s hs h
  have hmin : 5 ≤ s := by
    have hl := run_len h
    change 6 ≤ s + 1 at hl
    omega
  have hf := span_ok rootChecked s hmin (by omega)
  simp only [rootOK, found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
  exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel)
    (fun _ _ => rfl) (by decide +kernel) (fun h => h) mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 h)
end G63

theorem low63 : Lower true dom63 roots63 goal63 10 := G63.noCircuit

def fullGoal : Nat := (fromWords [0xfffffffffffffffe, 0xfffffffffffffafa, 0xffffffffffeeffee, 0xfefefafaeeee0000])
def sliceDomain : Nat := (fromWords [0xf000f000f000f, 0xf000f000f000f, 0xf000f000f000f, 0xf000f000f000f])
def sliceGoal : Nat := (fromWords [0xf000f000f000e, 0xf000f000f000a, 0xf000f000e000e, 0xe000a000e0000])
def sliceRoots := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 0 0]
def sliceMoves : List (Nat × Nat) := [((fromWords [0xaaaa0000aaaa, 0xaaaa0000aaaa, 0xaaaa0000aaaa, 0xaaaa0000aaaa]), 15), ((fromWords [0xcccccccccccccccc, 0x0, 0xcccccccccccccccc]), 62), ((fromWords [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0]), 124), ((fromWords [0xff00ff00ff00ff00, 0x0, 0xff00ff00ff00ff00]), 56), ((fromWords [0xffff0000, 0xffff0000, 0xffff0000, 0xffff0000]), 16), ((fromWords [0xffffffffffffffff, 0x0]), 64)]
theorem lowerSix : Lower true sliceDomain sliceRoots sliceGoal 10 :=
  lower_iso sliceMoves (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) low63

theorem lowerFull : Lower true mask256 xs256 fullGoal 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(xs256.getD 2 0, 32, 36), (xs256.getD 3 0, 64, 72)] (by decide +kernel) (by decide +kernel) lowerSix

def edgeList : List ℕ := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7]
def hasEdge (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)

theorem goal_eq_f : ∀ r : Fin 256, fullGoal.testBit r.val = hasEdge (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = hasEdge x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 13 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = fullGoal &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates xs256 r hlt (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates xs256).map (·.testBit r)).getD o false =
          ((execN gates xs256).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates xs256)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := lowerFull p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List Gate :=
  [{ op := GateOp.or, inputs := [0, 1] },
   { op := GateOp.or, inputs := [0, 2] },
   { op := GateOp.or, inputs := [3, 5] },
   { op := GateOp.or, inputs := [4, 5] },
   { op := GateOp.or, inputs := [4, 6] },
   { op := GateOp.or, inputs := [5, 7] },
   { op := GateOp.and, inputs := [8, 12] },
   { op := GateOp.and, inputs := [9, 13] },
   { op := GateOp.and, inputs := [6, 10] },
   { op := GateOp.and, inputs := [7, 11] },
   { op := GateOp.or, inputs := [14, 15] },
   { op := GateOp.or, inputs := [16, 18] },
   { op := GateOp.or, inputs := [17, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = hasEdge x := by
  decide +kernel

end PEqualNP.Outside.L_meta_30006_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_30006_aux in
theorem PEqualNP.Outside.L_meta_30006 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 13 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 20, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 13 := rfl
    omega
  · push_neg at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this
