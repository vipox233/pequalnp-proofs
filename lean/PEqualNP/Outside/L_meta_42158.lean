import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_42158_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
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
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2,hp.2] at heq; contradiction
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
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&4294967295
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
             !(isConstB d T)&&(roots.map (·&&&d)).Nodup &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs⟩,hpairs⟩:=hinit
  have hnd_xs' : (roots.map (·&&&d)).Nodup:=by simpa using hnd_xs
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
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
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
theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb:Nat)
    (hT : ∀ r : Fin 256,T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ,HasCircuitSize 8 f t → lb ≤ t:=by
  rintro t ⟨C,hfan,hsz,hev⟩
  have hout : (execN C.gates xs256).getD C.output 0&&&mask256 = T&&&mask256:=by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and,Nat.testBit_and,mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt,decide_true,Bool.and_true]
      have h1:=execN_bit C.gates xs256 r hlt (fun g hg=>(hfan g hg).1)
      have h2:=congrArg (fun l=>l.getD C.output false) h1
      rw [xs256_bits ⟨r,hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r:=by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none=>simp | some v=>rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r):=hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r,hlt⟩).symm)
    · simp [hlt]
  by_cases hhas : ∃ g ∈ C.gates,isNotGate g = true
  · obtain ⟨g,hg,hgn⟩:=hhas
    have hsup0 : ∀ v ∈ xs256,Avail true mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach true C.gates xs256 hfan (fun h=>Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hS p bank hr (avail_of_eq hout hav_out)
    have hlt:=countP_not_lt hg hgn
    have : C.gates.length ≤ t:=hsz
    omega
  · push_neg at hhas
    have hmono : ∀ g ∈ C.gates,isNotGate g = false:=fun g hg=>Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256,Avail false mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach false C.gates xs256 hfan (fun _=>hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hM p bank hr (avail_of_eq hout hav_out)
    have hle:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=C.gates)
    have : C.gates.length ≤ t:=hsz
    omega
def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_19:=0xf000f
def roots_19:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 4 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_38:=0x5500000055
def roots_38:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_39:=0xff000000ff
def roots_39:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_41:=0x30300000303
def roots_41:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_42:=0x50500000505
def roots_42:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_43:=0xf0f00000f0f
def roots_43:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_45:=0x333300003333
def roots_45:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_46:=0x555500005555
def roots_46:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_47:=0xffff0000ffff
def roots_47:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_49:=0x3000300030003
def roots_49:List Nat:=[xs256.getD 0 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_51:=0xf000f000f000f
def roots_51:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_53:=0x33003300330033
def roots_53:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_54:=0x55005500550055
def roots_54:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_55:=0xff00ff00ff00ff
def roots_55:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_56:=0x101010101010101
def roots_56:List Nat:=[xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_57:=0x303030303030303
def roots_57:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_58:=0x505050505050505
def roots_58:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_59:=0xf0f0f0f0f0f0f0f
def roots_59:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_60:=0x1111111111111111
def roots_60:List Nat:=[xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_61:=0x3333333333333333
def roots_61:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_62:=0x5555555555555555
def roots_62:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_32:=0xe8
def goal_14_48:=0x5440
def goal_15_16:=0xeec0
def goal_15_32:=0xeae8
def goal_15_48:=0xfeea
def goal_19_8:=0xe0008
def goal_22_40:=0x540040
def goal_23_8:=0xee00c8
def goal_23_32:=0xea00e8
def goal_23_40:=0xfe00ea
def goal_27_0:=0xe000800
def goal_27_32:=0xe0a0a08
def goal_29_32:=0x32222220
def goal_30_1:=0x55404440
def goal_30_32:=0x54404040
def goal_31_0:=0xeec0c8c0
def goal_31_32:=0xfeeaeae8
def goal_38_1:=0x5400000040
def goal_39_0:=0xe8000000c0
def goal_39_8:=0xea000000c8
def goal_41_20:=0x30200000200
def goal_42_1:=0x50400000400
def goal_43_0:=0xa0800000800
def goal_43_16:=0xe0a00000e00
def goal_43_20:=0xf0e00000e0c
def goal_45_16:=0x322200002200
def goal_46_1:=0x555400004440
def goal_46_16:=0x544000004440
def goal_47_0:=0xeae80000c8c0
def goal_47_16:=0xfeea0000eec0
def goal_49_12:=0x3000200020000
def goal_51_8:=0xe000a000e0008
def goal_51_12:=0xf000e000e000c
def goal_53_8:=0x32002200220000
def goal_54_1:=0x55005400400040
def goal_54_8:=0x54004000440040
def goal_55_0:=0xea00e800c000c0
def goal_55_8:=0xfe00ea00ee00c8
def goal_56_1:=0x101010001000000
def goal_57_0:=0x202020002000000
def goal_57_2:=0x302020203000200
def goal_57_4:=0x302020202000000
def goal_58_1:=0x505050405000400
def goal_59_0:=0xe0a0a080e000800
def goal_60_1:=0x1111111011000000
def goal_61_0:=0x3222222022000000
def goal_62_0:=0x5440404044404040
def goal_62_1:=0x5555555455404440
def goal_63_0:=0xfeeaeae8eec0c8c0
namespace S_27_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(1,17),(2,3),(8,9),(10,11),(10,26),(16,17),(18,19),(18,26),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_32 &&& dom_27
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x8e339dbc21bad7fd
|3,0=>0x9d277db192b669203734731c262c6e4921b3afde205d852e1c41677216a5493a1288e76e019df92000be1cca
|4,0=>0x9d277db1629e221b4dec4760464d889c3ba977c9256ff9441a9db4f605d02eb9
|5,0=>0x9d277db1
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc000c0000a000a8080808f080f08f0a0f0aa000a0040404042020202f0f0f00f000000f0a00003030202f000f0c7070000f000300f0f0000300030000c000ca0a0a0a00f0f00f000f00c0c0c0c5050a0a
|_,_=>0
def stPool:Nat → Nat
|0=>0x71048710487104863883621c41254e2092079082471c4121c41250e2090f3090f20c4e283dcd09182090e222cea09041224e8090e43142418820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xaa94165ac6582af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 28 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_27 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_27==dom_27) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 goalM v ys):RunD true dom_27 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_27 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27_32 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_32
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 6:=S_27_32.noCircuit
namespace S_7_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_7.map (· &&& dom_7)
def goalM:Nat:=goal_7_32 &&& dom_7
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xd4bda944
|3,0=>0xd4bda944
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_7 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_7 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_7==dom_7) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_7 goalM v ys):RunD true dom_7 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_7 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_7 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_7 roots_7 goal_7_32 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_7_32
theorem lowS_7_32:Lower true dom_7 roots_7 goal_7_32 4:=S_7_32.noCircuit
def isoMv_42_1:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_42_1:Lower true dom_42 roots_42 goal_42_1 4:=lower_iso isoMv_42_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
theorem lowS_46_1:Lower true dom_46 roots_46 goal_46_1 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050,2,6)] (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_58_1:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_58_1:Lower true dom_58 roots_58 goal_58_1 5:=lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_1
def isoMv_56_1:List (Nat × Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_56_1:Lower true dom_56 roots_56 goal_56_1 4:=lower_iso isoMv_56_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def isoMv_19_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_19_8:Lower true dom_19 roots_19 goal_19_8 4:=lower_iso isoMv_19_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def dzo_19_8:=0xf000f00
def gzo_19_8_8:=0xe000800
theorem lowSh_19_8_8:Lower true dzo_19_8 roots_19 gzo_19_8_8 4:=lower_iso (d1:=dom_19) (roots1:=roots_19) (T1:=goal_19_8) [(dom_19,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_19_8
namespace S_27_0
def pairsG:List (Nat × Nat):=[(3,11),(9,11),(9,25),(10,11),(10,26),(17,25),(18,26),(19,27),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_0 &&& dom_27
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_19_8,4,runOps true dzo_19_8 (0,roots_19) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_27 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_19_8_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_19_8 4 s (0,roots_19) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_19_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_27==dom_27) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 goalM v ys):RunD true dom_27 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_27 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_0
theorem lowS_27_0:Lower true dom_27 roots_27 goal_27_0 5:=S_27_0.noCircuit
def isoMv_57_0:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_57_0:Lower true dom_57 roots_57 goal_57_0 5:=lower_iso isoMv_57_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_0
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00,1,9)] (by decide +kernel) (by decide +kernel) lowS_7_32
def isoMv_51_8:List (Nat × Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_51_8:Lower true dom_51 roots_51 goal_51_8 5:=lower_iso isoMv_51_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_43_0:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_43_0:Lower true dom_43 roots_43 goal_43_0 5:=lower_iso isoMv_43_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_0
namespace S_15_16
def pairsG:List (Nat × Nat):=[(1,9),(2,6),(2,10),(3,7),(3,11),(4,6),(5,7),(5,13),(8,9),(8,10),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_16 &&& dom_15
def NN:Nat → Nat
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xff00f0f0ccccaaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0xe4
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_16 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_16
theorem lowS_15_16:Lower true dom_15 roots_15 goal_15_16 4:=S_15_16.noCircuit
def isoMv_57_2:List (Nat × Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57_2:Lower true dom_57 roots_57 goal_57_2 4:=lower_iso isoMv_57_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def isoMv_43_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_43_16:Lower true dom_43 roots_43 goal_43_16 4:=lower_iso isoMv_43_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_27_32:=0xf0f0f0f00000000
def gzo_27_32_32:=0xe0a0a0800000000
theorem lowSh_27_32_32:Lower true dzo_27_32 roots_27 gzo_27_32_32 6:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_32) [(dom_27,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def dzo_58_1:=0xa0a0a0a0a0a0a0a
def gzo_58_1_1:=0xa0a0a080a000800
theorem lowSh_58_1_1:Lower true dzo_58_1 roots_58 gzo_58_1_1 5:=lower_iso (d1:=dom_58) (roots1:=roots_58) (T1:=goal_58_1) [(dom_58,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_58_1
def dzo_56_1:=0x202020202020202
def gzo_56_1_1:=0x202020002000000
theorem lowSh_56_1_1:Lower true dzo_56_1 roots_56 gzo_56_1_1 4:=lower_iso (d1:=dom_56) (roots1:=roots_56) (T1:=goal_56_1) [(dom_56,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_56_1
def dzo_42_1:=0xa0a00000a0a
def gzo_42_1_1:=0xa0800000800
theorem lowSh_42_1_1:Lower true dzo_42_1 roots_42 gzo_42_1_1 4:=lower_iso (d1:=dom_42) (roots1:=roots_42) (T1:=goal_42_1) [(dom_42,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_51_8:=0xf000f000f000f00
def gzo_51_8_8:=0xe000a000e000800
theorem lowSh_51_8_8:Lower true dzo_51_8 roots_51 gzo_51_8_8 5:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_8) [(dom_51,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_8
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2_2:=0xc0808080c000800
theorem lowSh_57_2_2:Lower true dzo_57_2 roots_57 gzo_57_2_2 4:=lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_2) [(dom_57,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_57_2
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16_16:=0xe0a00000e000000
theorem lowSh_43_16_16:Lower true dzo_43_16 roots_43 gzo_43_16_16 4:=lower_iso (d1:=dom_43) (roots1:=roots_43) (T1:=goal_43_16) [(dom_43,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43_16
namespace S_59_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,25),(9,41),(10,11),(10,26),(17,25),(17,49),(18,26),(19,27),(19,51),(24,25),(24,26),(33,35),(33,41),(33,49),(34,35),(40,41),(42,43),(42,58),(48,49),(50,51),(50,58),(56,57),(56,58)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_59.map (· &&& dom_59)
def goalM:Nat:=goal_59_0 &&& dom_59
def NN:Nat → Nat
|2=>4
|3=>49
|4=>195
|5=>448
|6=>205
|7=>24
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xe1ea640b53f92cd746e432bf1f4cab78
|3,0=>0xff8a9b9bfd118ba0f2f40a3ef25d4dead8dfc9bece284496c02643c2b589e933a6c4815aa66d96079764d0af8f8672e08cf027fd8c8e3080813408c07da1b7266ecbbc27680f07966761bddc620b2a1f617a8697531cdd3e4f2106b34cd553174c68e114482af64d45fe0c4c422155483d49955f3a182ace368856e1309171df2dae87cb2d3705942d2890d5278537aa21c2690d205075291ef0845b1d274e221b7d59b9170d9c800e980b5d0d4481860d16a6130c7c036d0b9eadcb0a89edb104738541
|4,0=>0x77dadb7177bb9a7b76d555ff769314627541ee97735a2a6d7236775b70e029bf6e5521fa6e46ef886d93b5eb6c58b20369570c3766f8ee0e669bd775658858b0650b175462b3b762624ab4dd6243254b623e14e25f42ce8e5e59acd25d7c46c05d68696a5b77606b59a2cab158a18b9358574ecc58052bf65708758b559c94735575b42a53e1d8c052323e2051f86fdb51bc46b64ff0e01d4fdb98924fcc44634fb4a0204efcbfb24eee9b5d4e3901f44de842a94c3df308489e9a8147ffdb53479fadff471e492346ce18c7465f7ab0459d734344fed4ee444c51c943970dc5438ffb0842ed3de44221803441fdc04441c5d91f40ce5f0d3eea1be63e5222f93e32f80a3d54d57b3cca1c5e3bb040443b616ef43b46f2cf3b091ca2389f827236a3f9ef367ef83c36103efe3601842035a53dc2320ed28030a50786300e5b5f2ef3f2642dd3e6f72dae3f702c93d471295ff8a12938fcef28e253ef289531dc287ff190285c097226d6ac612567ec8823caece722bdd27920ddccee1faed6641f7abbb71c24c2791bc4d8b01946f7721857086d1759d37d16aef3be159645e01552a66613f9639b13ef705c0f72e7ca0cccf5080cc8579d0ca51dc40b09aa240ac870e809825ace08064e6b07c7c4c207951f9f06f1a07006e26d3006c389ea03fabd6803238085031b917602d1d58b0135ffcb00f9a695007e492a002c79fe
|4,1=>0xff3f2121fd118ba0f8a098bbf7b7c808f318ee60ed9ec47dea1b181ae9f27bd0e621a457e5004665e4d80767dd4f7bc3d9c4ac0cd95e998bd692a014d3ec0cf6d3e9f164cfed8a14ce2316d2ccf26d5dcc885c92cb184704c38bd316c28aa73bc190d622bc485204b8874873b394073eb26f785eb259eb5eafed2685afced15bafaf409eaea38849adb211e3ab814fa8a6ec5b63a3f20a1ba080f7c49fc978499e7fa1239ba1456c97edd0af9776dfef9690d1b79642e9f295d4c81e938d86d0926ad07c91ed694c911ab79a9101979f8eedfc208d9d06848cb1c0ec8a8faeca8959672b8548981b843165a58411a51680d05e877e6ada6a7d946b627d673a647b6b90d37a219fbb79c09950
|5,0=>0x314b853f313d8092312dc1c12f9899a32f02d1432e80c43a2dbb84cd2da36dcf2d924bff2d5f7d3c2d5e4d742cffc67a2cea28042c254d652b32e2f129e674da29a857db2952724928f54dca2843abd1282552ec280c490a27dce7a727429a2027103f63270d7f0f26f8a70a26a74c30262a03dc25ef1bb0254e958b253ed31a24fde71d24f431ef23826cce22f7f57822cda0f0228aa69022613ad92177a4e0208d3463206c2ea52040f09e1fb5a9131faed6641f0100b21dba880a1c9e22ee1c80a0a01c2fd0061acf018c1aaacc6b197d0377191a210518742b3017b1335c1793bf5417514c7416fb0df316d7f0e01636c66a161116f715d68d4615cd981215427bc514db695514dae23414a1166614870bee1479c635146e5886144cd3f613f4828a13b4062e136022b012edf1a31287235f122c30d5121ed95411df9c9f11d074cb11b51add118bce31118a0e321143dbbe10df5e3e107de1611078ca860ed1dd7c0ea5861d0e6a1a140e6846680e4ee0140e14f0cb0dfd82790dd5bce30dd0031d0d6fd6e10d4498740d40918f0d28ef470cfa00930b88f9c70b731f980b70506b0b0ae2730a0c1d310a08427308f1f31607f50ada07f46177079c9f39077eb578071b40dc06ef2890069412200620e99a0553020d0479a98504300da803c5259f023eaacd01d9a842015c8b87015327bf011e42510089e520005172bd
|5,1=>0x6e5160eb6e00e7ef6d8cd90e6c887db66b9770366b4c9c5a6b1e3eb56affdd026ad2e0a26aba78926a6bce526a53f2da69f40bf268534e0e679b6e826714801a66f9ab7766c9fbfc65fd59f765cbb54365ca52d7644448326303636d62a88150623e14e26161e45b60da61c95f31b60c5ef27cb15e97d6765e16f0a25d93722e5c3fdcc05b92d1955afe59c75af652b657b2263557354be456b521245600c3a855daeeb755c7786655c521c8550a7062545a20e454286ad453cf39ef5377074252c4a48e51ef181e51c7bdea50b30dda50557eb84f251eab4f1f05124f068cc14e71f0a94db8e2574da6d3124d817d204d5220a44cf131fb4bd563e24bc42fa44b692ea74b1ef2794a41488449f97ee149d7b93749d3084c4979483d49242c174920331949091e3848eb3d004888a03f4723452246be48d14632a44345e4920c45bb86d44570d1144488a06244531595432c1d6242847914423a2e9f4235023c41a0a50b416f0c2140d0c81f40cba1244084fba03fccda6c3f6ffa783ee651783eace9483e7090753e1936623dffed743d4c6db33d39476c3c9ca2473b653b383afa0ee13a4053283a35ffc73a0c97273a04a19939ea332f39d6cdfe39bb05bc38d55ceb3871f12a37d7380e379b12f737759b883745476736fbc1713635ef4c355cd6463526964d34ee2e5a34d3f06934ad79c53394a5e133932cd33326286a
|5,2=>0xb00b12d8adc576ffadc3b123ad43e582ac2cf43ba9cd044aa8ad6be9a7754e8aa6d23b34a5bb8f45a546fd7ba4ef51a3a4dcbf74a41893c7a3c9c339a3b1afb0a38ca210a38be003a33b93f3a2a985a3a257235ea1fab677a19ff939a186b22fa05229f39d5a2d559d3b44149d0d3f7d9d02fb229c32d2799bd8c10a9b0dc2a69adf0d2d9ac62d949a71150c99e05b399925859297bcd79e97b92785979bdad9973331dc972688529711d216968098769661186a95f13619953bf41d94bcae20948ace58933760fb92f1a67f928b6d67926c2c299256df8791f8b04a91b2b3c291472b959131e20090c4cc0d90c343e990a2f10e9092dc0a90840a8e9035f8578f8ae3f68f64acbf8d3cacff8bc8031e8baf22d18a596a0c8959672b892ed24988fa5aa688037cb387c9f614875649c88726de0a86ee0892869dff99867be14385c9d431857ff2a7851482ad84ce63f184876612840053df8200a8c581e39525814ca18e809d66d580257b267ef350f07e8e925e7e378ab57d9d8e547c96c6097c569d1b7be500c37b7ebeea7b46794679eb3b21795b5c28792294ca78b7157677b4d0127726f5cb7701f5c676cadada76c942d876934515767f7bba7664d814765adcbd761d4bd875cfbf6c75c351d474f1070b7456a19171e460cf71818deb710e71e570711bd66fc0f7db6ef93fc96ee73d616eb37eec6ea52f596e90c898
|5,3=>0xfc29846ff4826a58f433d59cf3c89c15f2acaab4f2133462f18240daed074f98eacd3070e5b2365fe26f0d71dd93e307dd4f7bc3dd3409badca55a29d7cfcac4d7b8e8aed7030e84d57ca830d29a6c2cd1f3bd64d1cf3872d0c102d0d0b8ea66ce18349ccc2cc5fdcba2d4e1cb3ffaffca76e171c9deb5a5c7d7ce4ec6bcda14c64e3bfdc5e9f326c5db3dedc51213bdc4bfa05fc3da12d4c1815e5bc1535c11c0ccab5abf9e8d50be2daa49bd499829bd15e9acbcd671e9bb0efb34baeabb05bac4db59ba6f00bbba125e26b94aa614b9084a98b8b243c4b888739cb7560641b6cfa84bb65c01ecb4a53e08b402dba7b1ca0f47b1b67218b0bd970fb0b27e59
|6,0=>0x6b1f38d566df723964444832641c84cb640fd9c6640845136336426f61906180618b3c13611bfa6360784b95603aa4325e63dae35d06a59a5afe59c75aa545535a3b622b58770fb9584c09075777458f576298f2560ef54055af57c2559ec35b552add5f5516de6b53476869531963d252848f97504ba5304eba076e4d507cb84ca2224f4a782c3d4a421725494e4b354920331948451596480b13b747c0c296478a811e45de45e043cbfcf34361387b430a3aee42ccf22b423806913fec9ef93dffed743d6f1eff3d3bcf603afd678b3afa0ee139760cc4385056b83809ef6334daf1d934167658308138b13049e5e22e12fad62e06c5a02d5e4d742cc19fda2b9d499a2b49df182b2dfc672a6444302a579f09280ac697272678dc2664c1e6264bdd13255d775124bd8a782476f5f62474b238245bffc0241708a5240f300f23a0339423826cce2313ceb7230c80ae21af24e52169762d203987721f8d2e931e6ce0cf1e4484171d6bafb61cc804401b8ad74e1a5020921a4d736b1a3c0c271a14885b197dccbb18e499a017172a3b16d7f0e016b489bf146cc5bf143b329a13f5da6e139792b912edf1a311b51add11785a740ec8cb000e6d1e690b731f98098c191d0874fc7307cc46dc073c8c300718309706aa02ab06a72c5f0657e8780620e99a0564f2f40527f9bd0398c42d0351df2901636d28012146a6005172bd
|6,1=>0xfd8f2cebfb54e77afa257a09f83d8d08f76bf9e9f33f8349f18240dae7066a39e67123ffe5ece2a2e4c27b57e233b50fde315142de2e8696d88f1b14d8672c4ad57ca830d39540bfd2e2c3b6cffc0d20cd430eaccc632374caa4d6c1c726f429c1cc6f53bfddce8dbe3f898abc2f8917ba446ebeb72a66a6b4897373b45d1aefb23cce00b17d7fd4b17b7225b133e7d2ae6d86ddabdca25ea967b509a963a80ea70e0299a5d873e7a33b07f7a0863de99cd5f5e29a71150c97f7e98897e24ec496ca34539680987694d24545942a33109275cc05913cefcf8e347da18e23c4498748945486cd272585c9d43182038752803cdc2d7ec7cfe27eb92c227b5c8d81795292f67713062576c942d876b57b8573706894730a829271de22cc71cebf6d6fe1fc7f6ea52f596e5160eb6daaec266d764879
|7,0=>0xff13f26abc640ccdbb341e12b23cce00a967b50993621e3d8da5724889a9dbc07cb1d5ec771306257407ca1a6cb2dc48638b81de5d6d0d234db527d74c0bcfb043cbfcf33ce6063334c550772cc19fda128d66fb0f0260ba0d6ebd470657c985
|8,0=>0xf0260ba
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc030c000c030c4040c0c04040c0c00f0f00000f0f000000000000a0a0ac0f030f00000000e000c000e000c00a0a0a080a0a0a08e0c0e0c0e0c0e0ce0a0e0a0c000c00f0f0f0f03000000f0f00000f0f000030c030c030c030ce0e00000e0e0000a080a0808080808c0c0f0c0c0c0f0c00f0c00000f0c0050f0a00050f0a00a0a00000a0a0000a000a000a000a00f0f0a000f0f0a00e0e0c0c0e0e0c0ca0a0a0a00000000a0a0a0a02000800f0f0f0f00000000c03030c0c03030ca0a0a0a0a0a0a0ac0c0c0c0c0c0c0c5050a0a05050a0a00f000f0f000f00f000f000f000f00a0a0a0a0a0008003030c0c03030c0c
|0,1=>0xf0e0f0c00000000a0a0a0a0a00000000f000f0000000000000000f000f00c0300000c030000000030c0000030cc0f03000c0f030000c000c000c000cf0f0f0f0f000f00f030f0c0f030f0c3000c0003000c00f0f0c0c0f0f0c0cf0f0a0a0f0f0a0af0f0f0f03000c00c0f0f0c0c0f0f0c00c0c00000c0c00c0c00000c0c0000a0a0a080a0a080800000000f0f030cf0a0a0a0f000000a0a08080a0a08085050a0a05050a0040404040404040420202020202020200f0708000f0708a0a0a0a08000800f000f0000000000e0e0e0e0e000e00808080808080808f0f08080f0f080800f000a0f000a00c0f00000c0f0000
|0,2=>0x505000005050000e0c0c0c0e0c0c0c3030000030300000000c0c00000c0c3030c0c00000000f0c0f0c0f0c0f0c0000c0e00000e0ef000a000f000a0000f00000f0f000030f000c030f000c300030003000300f0f0f000f0f0000c0c08080c0c0808c000c000c000c00a0a0a0a0a000a00707000007070000f0f0f0f0f000c0000f030f00000000c0003000f000f003030f0c03030c0c003000c0003000cc0003000c00030000f000c000f000c6060606060606060000f0f00000f00606060606000600f0a0e0a0f000c00f000f000e000c00e0e0c0c00000000f030f0c0f000f00f0f08000f0f080010103030e0e0c0c
|0,3=>0xc000c0c0c0c0c00f0300000f0300e0e0e0e0c0c0c0cf0f0f0f0f050c04f0a0f0800000000000030000000300f0f0f0f0a000800802080208020802f0f0c0c00000000c0c0f0f0c0c0c0c00f070f000000003030303030003000000a0a00000a0a00a020a0000000000a0a00000a0a003000f0003000f0030000000300000060c060c060c060c30f0000030f0000c0f0c0c0c0f0c0c0000f0000000f00c0c030300000000404040c04040c0ce0e000e0e0e000e00000000a0a0a0ab080b080b080b08c00000c0c00000cf0f0f0f0f000000f0c0f0c0f0c0c0cc0e00000e0e000000000020a0a0a0aa000a0a00000a0a
|0,4=>0xf0a0f080f000f00f0f0f0f0e0e0c0cf0f0f0f0c000c00c020c020c020c02f0003000f000300a0a000a0a0a000af000a000f0f0a0a00000000f0e0f0cf0f0f0f0f000d00a0a0f0f0a000f0050007000f000f000000000000a020af0f0f0f0e000c00f000c000f000c0000f000a0f0f0a0a20c020c020c020ca0a080a0a0a080a200020002000200f0f0c000f0f0c000000f0c00000f0cf0000000f0a0a0a10003000100030000e000c000e000c500070005000700e0e0e0e0e0e0e0ef000e000f000c005050f0f05000f00a0a0a000a0a0000f000f020f000f02c0c0f0c0c0c0d0cf0f000f0f0f0000c0c000c0c0c000c
|0,5=>0xf0f0f0c0f0f0c0c00f0008000f000830f030f00000000e0c0e0c0c0c0c0cf0f0f080000000030c000c030c000cb0b08080b0b080850a050a050a050a0000f0c00000c0c800080008000800f0e0f0c0f0e0f0cf0f0f000f0f0f00f0f0f0f08000800f00000a0f00000af0f0f0f0f00080000f0000000f00000000c0000000c00f0f0f0c05050504f0000000f00000000f0a00000f0a00f000c000f0a0e0a50f040c050f040cf0a0f080f0a0f0800000000a0a0a0800000000f0a0f08a0a050a0a0a050af0c0f0c0c0c0c0ce000e000e000e00a080a080a080a08e0e0e0c0e0e0c0c8080f0f08000f00f0f03000f0f0300
|0,6=>0xf0c0c0c0f0c0c0cc000f000c000f00c000c000e0a0e0af0f00000f0f0c0c30303030202020250504040f0f0c0ca080f0c0a080f0c8080f0f08080808000080a0000080a00a000a000a000af0f03030f0f000080a080a080a080aa0a0f000a0a0f0000000000c0c0c0cf080f0808080808f000f0c00000c0cc0f0c0f0c0c0c0c000080800000808c0f000c0c0f000ca0008000a0a0a0aa0008000a00080050f070f0000000000f000c0f0f0c0c00f020f00000000f0f0a080f0f0a08c0f000f0c0c0000c0c000c0c0c000000000000f0f0f0810f010f0000000000000000e000e00202020202000200a0a0a0a0a0a0808
|0,7=>0x30f000003030000a0000000a000000f0f00000f0f0a0a8080c0c08080c0cf0f0f0f050500000000f000c0c0f0ca0a00000a0a0a0af0f0a0a00000000000070000000700a0f000f0a0a00000000f00000005000000f0000000a0020002000202020200f0c0c000f0c0c00a080a000a080a8000a0008000a00a0a080800000000704070407040704b0b0b0b0b000b000000b0000000b00202020200000000c0c0c0c04040404f0f0a0a0f0f0000000050000000500002000200020002f000f000f0000003000f0c03000f0c0000a0000000a00f0c0f000c0c000000a0008000a0008300020003000200b0a0b0a0b0a0b0a
|0,8=>0xf0c0f00000c0cf0808080f08080800a020a000a020a300030000000300300000003030000f000f000c000c00303000203030002000080800000a0a0000a0800000a08c000c000f0f0c000000e0e00000e0e50005000500050080c080c080c080cf0f07000f0f0700303030003030300f0000000f0f0000f0f0c0e0f0f0c0ef000f0c0f000f0cb0b0b0b00000000000020200000202300030001000100c0e0c0e0c0e0c0e00a0a0a00000000c0c0c0c0e0e0e0e302030203020302e000e0000000000c0c0c0c0f0f0c0c20a020a020a020aa0a02020a0a0000f0f000a0f0f000aa0a0a000a0a0a00c000c000c0c0c0c
|0,9=>0x303030003030000700070007000700f0c0c0c0f0f0c0c00000000e0e0e0ec0c0c0c0808080870f070f00000000808080a0808080af0f080800000000f0f0e0c0f0f0e0cf0f0f0c0f0f0f0c101030300000000f0f0000030300000000c0f00000c0ca020a020202020200c0c0c000c0c0c505050405050504f000f0a0f000f0a303020203030000f0c03000f0c030050f0000050f0000f0f0f080f0f0f08a0a02000a0a0200000000a00000a0af0f000c0f0f000c00300000303000000f0f0f00000000f0f05000f0f050080a080a0808080850507070000000000f0f0f000c0c0cf0f07070f0f00000000f000a0a0f0a
|0,10=>0xc0e0c0e0e0e0e0ef030f000f030f00f0f00000c0c000050f000f050500000000f0800000f08f0f0f0f0c0c0c0c303030300000000a000a000a0a0a0ae0c0e0c0e0e0e0e00007070000000080808080a0a0a0a00f000a000f000a00000000f0f000000002020a0a0a0a000030300000000a0a08080a0a0a0a00f00000a0f0a0af0f0e0e0f0f0c0c0000e0c00000e0ca000a020a000a02f050c040f050c04f0f02020f0f0202f0f02000f0f0200f0f04040f0f0404f0f000f0a0a000af0f0d0d00000000b0a0b0a00000000f00000003000000f0f000c0f0f0c0c00000000b0a0b0af0000000c000000b0a03000b0a0300
|0,11=>0xa0a0a000a0a0ac080c080c080c08c0c0c0c0000000030300000f0f0000f0f0f0f0f0f0000c000c0c0c000c0ce0e0e0e00000000f080f080f080f08000000003000300a020a020a020a02c0c00000f0f0000a0a0f0a0a0a0f0a00e000e000e000ea0a0f0f00000000f0f030300000000f0f0f0f03000300f0f0c0f0f0f0c0cf000c000f0f0c0c0000200000002004040f0404040f04f0f0f0f05000500a0a0a0a08080808f000d000f000d00f0f0f0c00000000008000808080808f0a0f0a0f0a0f0af040f040404040430303030303000070707000707070000f050f0000000000000000f0f0f0c00a000a0a0a0a0a
|0,12=>0x505050500000000f0a0f0a00000000f0a0f0a0a0a0a0a0000f0a00000f0a3030f0f0000000000000000f0a0f0aa0f0a0f00000000f050f000f050f00f0f0f0f0a0a0a0aa0f0a0f0a0a0a0a0000a0a00000000a000f000a000f00f0c0f000f0c0f00100010001000100f0f0c0c0f0f0000000000a0000000a707070700000000
|_,_=>0
def stPool:Nat → Nat
|0=>0x40e40c381b8940a04040d80c351a0b00a0d198141c03190080c00040c40c30040085e2e0a818282d160080a2b040080a2a0a8a45003040140c270a80816260a8944823110080a01110140c030a8140c21040800c1f0a8183c03028183a1c0106c0c000405434190a8602e0d0b0540c14040082612040440c1001014140f06008160a010240008038180a04018080200
|1=>0x188140c1d04054b402240200405031642a1702834105802818ae080a818ac5504150045303054305205034101503038280801014a250278080c000a8080a0101018004e041340c00040080c4c041280c4b041280c490400890470405404460a9140a0d0a9108606041080c00028187c1d20808300a0a8080c400a8fc3406060080a3e028107a3c1a0085e01040ec0c3a
|2=>0x3a1cc2a0202818e408028183a71040d00406380200a060e970101503050de080a8080c6e040540c6d0a020440236018100b0d018d608011a80c00040540406348202a021208c1034011a00c081b0080c00110080c55338202a02330a01005328183a64110080a0604054c652030540405130341002310140c15010140c61040080a602f82018022f018100203000b608
|3=>0x40080c00258210202058186e08010140834010bc0c4e0401500060e8200413031fc0405050acd60802818fc6b0a8140c5f01854047d050acf815010140c08011280c000a9ec04050302040061c1e80a06249acce080101800490102c0c0a358dc2a2503078f215010140c080a818f014040540c141d0547e0205818107701018000811008ec060a8080a063a820045f
|4=>0x3000d608062480a060b0540c551c0200a06140741033010acaa370a8140c91040540c554813c6802178182a02028291e080a818288e042342a060a020040b0323010150315512340122c0a06040880418030202a06452244405030f47815010141488040090e23238202a86028181033010150a08198080a840a8183c3d1e0202a83031541015012080c370a8945228
|5=>0x510181002028194264500080a0604054b41a030202205030741015010143208060080a9a040553e05032782a02218193a15010600c080aa700c080126c16061b8cc4a05070202a5802a68100c01014560805819126b0aa640a061e054040b032612e15010140c1549014140d040080a963985452281e8f01015028192a22010140c750a8080a064a24c2a02028181002
|6=>0x35ac44402028181011032c15eae0a8080a06012b40a0a158201805032b0101501120d60802819341d060080a0a0705404ab028182a9b028281a150101414aa040d12406380202aa9028353a15030501034010186a34160080a06040540405170200405020f02a0202819500801018003d198141c3d1e05404050329c1015010154c080aa95480604054040b518202a02
|7=>0x40540c555f054040b032f410155e2900c081a018e0495d8540405030202a065d15410ad028ac1a08012e40c6b040302a055c02004062eadc1002028107a150106014b61a0540405008202ab50d01810b401018000503074ce3456814140d04054047d158204402088193a152d018dab30a8083006040084a06000216405031ac1022010143208010183c47040081606
|8=>0x28299615010140cca0a8080a0600820042f033242a86028181415010140cc8278540405030218e02028381002030006a081a0098c06040d004c5030540405033102a0202864ce150281986c20a9140405030206802250181005030746015012480a01040d00a060e85404050caa010021281408080a80852c1028183a6b3385404056002810bf010bc0c08028183a7a
|9=>0x1402004052f8f4e615010140c0a4d0202a0208819a4080ab440405030202ad0010140c083b8540405030202a062a9242a0202818f467010140c6b3999c10150133c0c2304054b005030f0a815010140c67040440a06581ac101501018aace040080c5d2a970101503174aa38040080a06071ac1034013340c150101402080a9481ca3040092406000540405033302a02
|10=>0x50351c081a0080c552e020681529018aa080a8080a066c8202a0202819b0080a96924050302068150315470080a8090e05518216834568140c080a8080a066b8202a9b02819ac080a968040b03021aa0202818e6080a809a855140202a020281892080a808340503020665a010141c0801015a606358202a024388cd6080a8080a062b020a833010140c640a8080a06
|11=>0x3582004052f954e608010800a063d0200a06581adc8080ab8c0405030202a05030501015010140ce20a8080a0a158202a023e8140c080a8080a06708202a056f01878080a8080ae047054040605154b8640ab7c040503020681501018aa1501015bc06050dc1015010183c080a8080add03021b802568140c080a8080cdb2a8202a020c018b815010140c0a6d0540405
|12=>0x3385404ea03154ce08500080a062e8200a064d2c0d6085a0080c5d2e02068e9010140c080a8080a9a7402004050315cb808010140c6d358202a02630140c080a9480ce704055cc05031ac10152901946640a8080a06068206802568140c080a8080a06648202a0203394aa080a860a406040540405628193a152d1480c080a808220611820042503174b808060080a06
|13=>0x1a05404de0302068ad02819ac081a0080a06790540405030397a08010181c1e358202a0202819e208062b40a06068202a0202819e0081a0082206358dc1015010a450080a8080a06470202a020590c0c080a8080a06778202a0202819dc080a8080aed032742a02028181c080a8080a067602168ad0281846081a168042f030202a022f018103401018e015010140ceb
|14=>0x10140cfe042d004052f9cdfa02568140c670405404067e155f6152d0080a06040540418032381015010140cfa500540405030281015010140cf904054b005030f4040503174d66732054040503155f015010140c55040540405033dc2a020b8140c080a8090e231e8202a0202bd80c08010940a5f398200a060e8202a0202819ea080a8080a067a0202a0202819e608
|15=>0x10140c0a3d0202a5802818aa1501015ba06010140c0a359cc2a020281a1215014200c55338202a0236018aa080a8080d072a8202aa4830140c080a8080a06658202a0282818aa080a8080a0d820202a5a29018e6080a8080aa3140140cb03599c103401018aa6b040540ade030341015010140d03040d20402028181015010160229040540405033fc100203000100c
|16=>0x2818be08010181c552e0202a060715470080aad4040b030206802880140c37040cc0405070202a0503074d6081a009242f030540405032f4da080a808300614054b4520319c110f0a8080a06040561c52030202a020281a0215010161a0635854046c02818ce08010140c6b8605404050342cce080a80a1405032742a0202818da34010140c6b338202a026f0184615
|17=>0x8c0202a020281912080a8080c293a0202a0212a1c46080a815bc062a8202a020281a2e0802819606b578202a0202c580c080a8082205030200405031ae2a080a8080d132a821020202818e6080a8080c1e1e0200405030a48e08468080a06358200a060e9ac1054010145e06040d00420030222415010140c080aa0c040503054049202818ce080a8080c23888dc2a25
|18=>0x281a4808110080a067b8202a020281a46080a8080a06910224215010140c08010140c8c398202a020281a40080a8080a068f8202b1e010140c080a8080a068e82044020308caa080a8080a060c8200a06581acf4080a8080a068e0202a0267818b8080a894b005030202a020281a36640a8080a52030540405031fcce080ac695a05030202a020281a32080a8080a06
|19=>0x10140c9a044ac2a020281810150102c34060405404050c8202a020281a5408010140c5f2b8302a0202818ce08060095a05030200405020202a5a29018ba080a8084655140202a020281a5215011b00c67044a00405030202a020281a4e340a8080a0693020440202818d615010140c8c33820680229018d6080a808d0050302068020317caa08928080a06358202a02
|20=>0x34c8101501015bc06010140c0e3599c10b4568140d31468540405032f41015010140cda1b8202a9b028186815010140c4e040081605031ac6e080aa900a060a80936050319c1015010166015010140ce73385404050328cce08010140c3d8a8225e05031ac2a0202818152e040565a020281810024d8140c73040080a06961ac1015010160873040082605031ac1015
|21=>0x10140c6b043540405030381015010140d11040540405034e41022010140c3d040cc0405070f011380a8080a06044dc2a0202818100202818a06b040d0042f031241015528080c5d9b05404050319c1015010183c3d0416804052f9cc1015010140d35040d0ee0217818680202818146b044d00405031ac6815011f40c0a040540405034cc101501018aa5c040540405
|22=>0x338202a026f018b8080acf4040503054047d0302846080a808cc0611854047d02818ce08010140c2b3585404056e818ce081a2040405030540405031ae78080a80a76062a9906815010140c340a808a4065e8202a0243815a808010140c5d460540405034e810150c2900a06042800405031bc2a020281892670a8092405030289e340a8080a064e8d02a022901810fd
|23=>0x568140c1d040540544028181034010800c55040540411030a01015010140c880405404e02a8a011430a8080a06040081606358202a024c8140c08010940a068aba4040503028e6080a80900062a85404050315684080a80a82050302004ad0281a18080a8080b40030202a020281a7e080a8080a069f020683301018aa080104c0a061e8202a9202818d634012b40a06
|24=>0x3020680217818d608010140c6b398202b4b010140c08a505404062a8229215010140c0c0a8080a06050d02a02028281a080a968048711822900202818d6080a8084a060f0202a0229018ac08a38540405030202a0202b511c08a3054040503020680c010140c15010140c8e338202a02028191e8d0a8080a06338540405a2818aa08198080a062b8211a02568140c08
|25=>0x581912080a8080a06090202a0243816aa08110095a05030206802569480c080aaa40405032742a0202818aa080a8140c55aa02018020281aa6080a8080a06a90202a92028181a15010140cf9338202a020281aa015010140d4f338540405031acce085a05404060f0202a0202944534e0a8080a06050202a020281a9a080a8080a06a60540492028189c08110084a05
|26=>0xa8080a06ae0202a0275018aa340a8080a0a158202a0202819ca08500080a06358202a0202a681a080a8085e063f8202a020281ab75a040540418030202a5a02b780c08010942605030202a0202a6a28080a8080a2b068202a0202be4e6080aa480a061e93c2a02490140c080a80aae050302044020281aac0202818140e358202a0202b5050085a37d5a05030202a02
|27=>0x281a40670405404050359c101502ae010b4010140c500a8080a065e9cc100c0ad980a0d04056ca0202818101502818926b040540452035906802568140c0a044d004ad028181015010140d6304054b005035882a020281ac2080a80abe0503054041102818ce081a0085e061e8202a020581ab2080ad780a062a8202a02028192208ae8095a05033a4040503028ba08
|28=>0x89480c15010140c9a338202a050303492fb0a8080a062a8540405031381015010140d6cb58540405031ac10340101800085a054040b0302004ad0281856080aa940406148540405035a81415010140c0a472342a020281814080a80ad205030540a06118f47808060080a06070202a25490140c080a8080a06970202a020281954087e8095a05035a02a02028182a02
|29=>0x2a8216815010140c5d040080a06071ac116f0a8080a06045382a02028181002031747a5c0aab40a0a068202a02b70140c080a8141ab8040302a02028181015010140d6d040540405050ac1015490140cd6042fc2a02028181015010141ca32785404050302068ad028181a0c0a8080a0a068202a062a8e0e60802a000cb0358206802128bc0c080a8092405030202a02
|30=>0x3e8140c081a05404062a8206815012b40a06040540405030a4d6085a0d02a02028181015010140c49040095a0503176b4080a8080a52030202a0202dc80c080a8080a520317410340a8084a05030202a0202818ba38044d82a02028181015010140c232a820ee15010140d5a0405404ad028181015010145e062a822e215010140c080a8080a06148f2e0080a8080a06
|31=>0x10145e060a8080b0d030202a0202818ab77748540405030281015010140d760405404050315c101501016000604054b40202818e615012b40a06050202a02028181c3d0405404250281846080a8080a06860202a02128145e061a05404050319c1034012b40a060405404ad02819a4080a8080b75030202a0202dd00c6b040d02a020281870080a8080a06b98202a02
|32=>0x31ac6e080a8080a062f8202a02bd01810340a8080a066b0202a02028181c55040555a05031ac100c0a8080a060685404ad0281a4c080a80af205030202b78010140c080a8095a050308c10330a9680405030202a0202818d65c040d02a020281814152d0080a06338202a02028191c08468540405030202b0e010140c640405404ad0281810b40a8080a06118216815
|33=>0x42d02a02028181c080a8140c0d1c0202a020281a02080aab40a06068202a0202a000c6b040540405030a4aa080a80a1405030204402028181015010140c28580202a02678140c080a8080c1e040882a02028181015015f80c080a8080a06be0202a0202818523dbd8202a0202818d6080a8080a067c8202a0202818d6080a8080a060756410020281a2a080a8090e05
|34=>0xa8140c551c2742a020281810150281aa8080a8080a06141ac1015010140c552e0202a02128140c290a80af205030d02a020281814080a8090e05030f4c815012b40a06040540405033f81015010440a06040540429140200413028181015010140c0e1c0202a020281afe080a808a406118202a02028181a080a8080a061e97010152d0080a062e8202a0202818aa6f
|35=>0x28181015010940a062e0202a0202818ab83040540405031c01015010140c0d358202a02029480c6d0a8080a069e0202a058a3581015011600a06040540405030ac1128010140c080a8080a068a1aef6080a8080a062a8540405032f41015010140c0d470230415010140c080a8090e050315410b40a8080a06148202a020281b0208940540405030202a020281b0008
|36=>0x40540405036181015010140c55140202a020281b0a081a0085e060405404ad028181015010140d1104054040503154d6080a818aa38042d15a05030202a0202818d667040540405030a07a081a054049202818101501018aa5c0405404056f01810b40aab40a06040540405031551c080a8084a87028181015010440a06358202a02028193408198080a0e040570802
|37=>0xac0206815010140c49043542a020281810343b8540405030202a02568140c280a8080a063599c10152d0080a06148202a02029480c6b040540405031e8100202818d6730405404ad02818d6082a0540405030202a02128140c28040540405032bc108d0a8080a52030202aa4028181015568140cd67d8540405030202a020281a7c080a8080a064d1ac2a02028196067
|38=>0x358200405036341015010140c6b690202a020281b18081a0540405031ac1015010140d593985404050362c1015011480c280405404ad02818ce15010171406040080c5d2e0202a0202818d67a04054b402438140c15010140c0a040571202028182a02028181a67c40202a0202818d76b0a8080a060405404ad028181a081a0540405030202a0202e1c0c080a8080a06
|39=>0x40540405031701015010140d510a8080a066b19c2a02028281a080a8080a2f030f410340a8080a0615854040505450100c0a8080a060a8080a060503410340a8080a061e8571e02028182a02568140c670405404ad029480c081a0540405030341015c70080a0604056cc05068216815010140c73040540492028181015010140d60040540405031aea615010140c0a
|40=>0xa8080a06118202a02028bc0c15010140c0a040d02a02028181015010140d90040540405033581015010140c0a0a8080a06338202a02568140c085a0540405030202a02128140c080a8080b7d030202a020281ab2080a8080a062f8202a02028187a080a8080a06068202a020281a28080a8080a06140202a0202818d6080a8080a06580202a020281810150121c0a06
|41=>0x40540405030202b66010140c08
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x498018c00660003
|3,0=>0xcc406420311018080bc405c202d1016080ac4054202910140809c404c202510120808c4044202110100807c403c201d100e0806c40342019100c0805c402c2015100a0804c4024201110080803c401c200d10060802c4014200910040801c400c200510020800c4
|4,0=>0x105288154400a1fb50fb287c543d8a1e750f12877543b0a1d350e7287254388a1bf50dd286d54360a1ab50d3286854338a19750c9286354310a18350bf285e542e8a16f50b52859542c0a15b50ab285454298a14750a1284f54270a1335097284a54248a11f508d284554220a10b50832840541f8a0f75079283b901d2a0e4506fa836941aaa0d05
|4,1=>0x1a428d0d467ca33a419aa8cc14656a3265190a8c71462ea3125186a8c214606a2fe517ca8bd145dea2ea5172a8b8145b6a2d65168a8b350590a2c3515f28ae54568a2af515528a954540a29b514b28a454518a2875141289f544f0a2735137289a544c8a25f512d2895544a0a24b5123289054478a2375119288b54450a223510f288654428a20f5
|4,2=>0x243a920948faa4785239a91b948d2a464522fa916948aaa4505225a91194882a43c521ba90c9485aa4285211a90794832a4145207a9029480aa40051fda8fd947e2a3ec51f3a8f8947baa3d851e9a8f394792a3c451dfa8ee9476aa3b141d628e9d4744a39d51cc28e4d471ca38951c228dfd46f4a37551b828dad46cca36151ae28d5d46a4a34d5
|4,3=>0x12554922848c5
|5,0=>0x308a982d8c0ac5ff62fcb17cd8bdac5e762f1297718baea5d162e5b17158b7ec5b962d9b16b58b4ec5a162cdb16558b1ec58962c1b15f58aeec57162b5b15958abec55962a9b15358a8ec541629db14d58a5ec5296291b14758a2ec5116285b141589fec4f96279b13b589cec4e1626db135949a0c4ca6262312f98970c4b26256312998940c49a6
|5,1=>0x3c331e090ef8c77663b831da98ec8c75e63ac31d498e98c74663a031ce98e68c72e6394a9c8d8e3ac7176389a1c358e0ec701637db1bd58ddec6e96371b1b758daec6d16365b1b158d7ec6b96359b1ab58d4ec6a1634db1a558d1ec68a5342a99fd8cf2c6736336b199d8cc2c65b632ab193d8c92c644531f318e54c66c62d6313b18858c38a6166
|5,2=>0x47fb23e591e6c8ed6473b238591b6c8d56467b23259186c8bd645bb22c59156c8a654503226d512ac88f6444b220d90fac8776438b21ad90cac85f642cb214d909ac84764212a0f1906ea8316415b2095903ec8196409b2035900ec80163fdb1fd58fe0a7ea63f2a9f7d8fb2c7d363e6b1f1d8f82c7bb63dab1ebd8f54a7a463cf31e618f24c78c6
|5,3=>0x53c329c994d8ca6665303296994a8ca4e652432909947aaa376518b28ad944caa20650d32851941cca086501327f193ecc9f064f5aa79593bec9d964e9b273d1392c9c364deb26e15366a9ad64d3b26859336c99564c7b26259306c97d64bbb25c592d6c96564afb256592a6c94d64a3b25059276c9356497b24a59246c91d648bb24459216c9056
|5,4=>0x5fb32fc197d4cbe465ef32f6197a6abcd65e3b2f059776cbb565d7b2ea59746cb9d65cbb2e459716cb8565bfb2de596e6cb6d65b3b2d8596b6cb5565a7b2d259686cb3d659bb2cc59656cb26559032c699628cb0e658432c0995f8caf6657832ba995c8cade656c32b499598cac6656032ae99568caae655432a899538ca96654832a299508ca7e6
|5,5=>0x6bab35bd9ad2cd6366aeb355d9aa2cd4b66a2b34fd9a72cd336696b349d9a42cd1b668ab343d9a12cd03667eb33dd99e2cceb6672b337d99b2ccd36666b331d9982ccbb665ab32bd9952cca3664eb325d9922cc8b6642b31fd98f2cc736636b319d98c2cc5b662ab313d9892cc43661eb30dd9862cc2b6612b307d9832cc136606b301d9802cbfc5
|5,6=>0x77633b999dc0cedb576ab3b415d94cec4675f33ae19d64ceac6753aba859d36ce956747b3a259d06ce7d673bb39c59cd6ce665730339699caaae4f6724b390d9c7ace376718b38ad9c4ace1f670cb384d9c1ace0767012b7f19beccdf246f6337999bc0cdda66ea337399b90cdc266de336d99b62adab66d2b367d9b32cd9366c6b361d9b02cd7b6
|6,0=>0x8453c21560fcf07778392c1ade0c8f05e682bbc145a096d045681f3c0dde060f0297811b4075a02ed01168053c00ddff8eff757f83bfa99fc8cfde67ec33f45df96cfc477debbedd9f60efaa67d233e75df2ecf9077c4bbe0d9efacf7767b83bda5dec4ef5c67ab33d3dde92cf42779dbbcd1de5ccf277790b3c69de26ef0d67833bbfdddf0eef26
|6,1=>0x90b3c83de412d20458ff347dde3e0f1ea68f1bc771e3aeb1d258e634719a382b1ba78d9bc6b9634ef1a168cd3c64de31ad18768c0b45eda2ecb17158b53c58de2b8f15758a8b4529e288d13e689c344cd625cb1277890b446da22ad10e7883bc401e1f2f0f36876b439da1c0f0d97869b4339618ef0c1685e2c2d9a162b0ab68523c275e12ed0916
|6,2=>0x9d234e7d6730f39269c634e15e6fed37a59b9bcdb5a6ccf35f79ad2cd51a69af34859a1accf1e66af330599534c91a63af3185988bcc2da60ad2ff697c3cbc9a5d6f2e4796f34b5de5a0f2ca696234af5e56ed2b0795534a8de53cb2986949aca35a50cf280693d349cde4dad268593134971a4aaf2505925ac911e47af2367918348a9a448d21d7
|6,3=>0x13f469f734fa567c4f3db79eb2cf41a794d3c379df2cee1a762f3aa7
|7,0=>0xa40b51eda8ead4705a3535191a8bcd4586a29ad135a88ed4416a1db50d5a85ed4296a11b5075a82ed4116a05b50196800d3fa6
|8,0=>0x14875
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 401 then fld (dictB (i / 512) (i / 32 % 16)) 60 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0xa8160a815010170400a028190121c02819010030a954010181a0180101601018040182e9710a8170a816040181a01801017028352e9710a8170a81601017011cd02819040090281b0281a01015031540a80a0283902835028180281904009040181a01801016028291a00b02839010170a808010150a9540a8342e9710a8170a81602818028192e9710a8170a816028750401801018010140a80a0283902835
|1=>0x10150401a01017011730101a0101404009040ac0281b0101501014010160a81504018010170a94b0a8080281a04055010170a808042b5010141a00b0a808028350ab3c0a8090a8170a81602835010160a808010ae040181a0180a8150281a0a8160101704009010140101401017010181a02b0a815040171a0080a819010150a81a04017010171a00b1100801015010170101702819010141288d0281812971
|2=>0x400b04009010161a008028350401a0a8080ac29011750a81702835010170a80a01017010a20401a1a00a0121c0401a01014010175681a0101401017029af031ad042900121c02819010ac0101701018010140a8080a81a010150401a010160a81501173040170a8150101a0281b010150ac030400b2e9710a8170a816028350101402835010180281a0121c02819042b5010140a80a04018010140281802819
|3=>0x121c028191a0090aa1e02819010170281a0a837010140101711009110080a8150a81b02835028350401a010161a00b0a815010140a80a028180a815010170a815010170ac51010171100a010140a80901017010140a815010170121c04008028190ab3f01014010141100b0281b0281802819010170a95401014010170ac530400b0281a0281b0a80a010140101601017014311a0080a815010150a80a11009
|4=>0x1014029ad0295d040080283901017438f70400b028190aa1e028190a81a028290a95701017010140a8a2028182a0170aa1c028191a0080a8150401a011730a81802829028291a0180a8150400b01017010140a81901014010181a00b1a0080a8150a99d010170400b0a88d0281802835010181a00b0a8161a0090a8150408b0a8140a8150a81504018028290a8150315f04008010150a815011730a81602818
|5=>0xa815040180101701017010180a8140400802835010180aa1c0400802819010170a81a03567040171a0080a8150a81502d61030f70400b0408b0a88d02818010170a81a01017010151100b2a0180a81904017010140a81501014010ad0121e3b81a0a8151a008035470a8150401a010150281b1a0290a8150a8151a0080a8150a88d0281801017028180a815028350a8150101701017010180a8190101401015
|6=>0x10151a0180a8152a0151281504008028181a0080a81501018028350a80a0a8150a8140a8150a8150a815044511a0bf0a8150a814010151a018010140a81b028290101402818028351a0080a815010140a815040088a3590101b0101a02835128a50281b0a81501014040180ab4b010141a0090a81502d811281a040080a8150400b0a814028390a8180401712a1e0400802819ad05401014148f50281b1a018
|7=>0x400b0281a0401801014028180400b02818040080a8a20281a040080a8140a8150401a0a81501014010140ad6704017010170121e0281902829040180a8150101701014010170a8151a00b0a8150a81701014010140281b010140a815010161a0090a8150a818040d00a81501014041730a8160281b010170101501017028180ab3d028f51a0290a8150a8170a8160401801018010140a815b30370101801019
|8=>0x1018010140a81b02b590101a0a88d028180281a01016028f50400b028180a88d02818b3014010190adf7040140281b0400b010170356704017010150a818040170aa1e0281901017040090281b010160a815028180101402835042b701014028190108d028180101402819010150a815010150401a010a00281a5681501014011710a8160101402818010150281b010170282904018010161281604008028f7
|9=>0x1017010bf0a81401017010140421e028190101b0101a0121c028191a0180a815010170101701014010180adf504014010170281b01015010a20281a010160408f028180a80a01014028190a80a0281b040080421c028190a815040180400b02819042b50101401014029ad010170281b0281a0aa1c02819010165681a010140a818010140335b0101a0a8160400b0a816010150101701015010180101601015
|10=>0x400b030f70400b0a8150ad65040170a81501014010170401a0a81b01017010170281a010141281504008040080281a01014010140121c028190101a010140281b0108f02818031af010170401a01016040a00281a0a81a010170281b0a8150a8140101601015010170a80a01015010170400b0281a1a0080a815010170a816011730a81601015010170400802819029ad031af01017010bd0a8140a81604008
|11=>0x281a0101701016028190a816040d30a8150101a0401a01018040180400b0a8141a0180a8150101b04018028350101801018040180a815010190401a0101401014128190400801018010190a81a010151a0080a8151281a04008010170101704018010170a8140a8150a81a04017010190a81a0101401014044530101b0a8170a8160a819010150281b010180401a01017044510101b010140a9710a816030f5
|12=>0x1019028180a8140a8150101a01014010150281b010180101b
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>2
|4,0=>0x1a10000000000018205c40000584000000000000000000544132000000004840000000000000000000000000444000000010103c40000000000030c000028800000000000000000000000000000000000000000007301840000000033000000000000000084000
|4,1=>0x283000000009c4000000000000000000000000000000000000000000261000000000000000000251000000000002410888000000000000000000000000084400000001f200000000000000000000000001d2000000000001b200000000000000
|4,2=>0x3920000381000000000000000000000000000000000000000000000000000003710d4800000000000000000000000000003410c88000000000000002f300000000000000000000000002d200002c100002b10000000
|4,3=>0
|5,0=>0x190400018886110000000180400017c45e116cc5a100005910000000000058100005711584551150453114480000000000000050113c40001384000000000013444b2128449112044711184451000044110c4000000000010483f200003e100003d100003b2000000000000000000000
|5,1=>0x24488e32344000230400000008a20000000224487200008520000841208880200000001fc47d200000001f047b11e8400000000000000000000079100000001e040001dc400000007610000751000000000000001d040001c88711000070100006e21b086b11a4868100000001988651
|5,2=>0xd513504d2234440003404cf10000ce13344cb20000ca13208c710000c610000c5130c8c2100000003044c012fc4be12f44bc10000bb12e48b812d88b512d040002cc4b212c440002c040002bc4ae12b08ab12a48a8129c4a6128cca2128449f227849c2268899126049712548932
|5,3=>0x410400040c501200010013f880003f440000000fb23e4800000000003e04f713d840003d44f413cc40003c84f113c0400000000000000ee23b080003ac4e920000e8139c4e5238c8000388400038440003804df10000de1000000037440003704000364cd8135c40003584000
|5,4=>0x4fc40004f8400000013c24e893734d493324c853114c052f14b852d100000004ac92924a052710001252000124148c4000484920100011f100011e100011d1470400046c5192000000045c8000000000045840004509122000111144050e2000000043450b2424800041c80000001052
|5,5=>0x17e300017d15ec9792000177200017435cc40005c0d6e25b456a359cd6615909631588561157c95e157095b100015a1000158255c400055480005505531548550200014f153494b2000149252040000001471518400051440000000000510400050c4000000000000014215045401
|5,6=>0x72c9c9271c9c4370c5c036fc40006f480006e8db916dc9b616d45b410001b226c440000001b010001af10001ae16acdaa16a09a71698400069440006905a3168480000001a0167c400067859b30000000668598265c59616545932000000064498e300018b3620c000614d8320001812
|6,0=>0x898a24288c621288061f187861d187061a2864617285861420002131844a0f2834a0b282860918206071818604280c60127fc9fe17f09fa27e09f627d09f227c09ef17b49ec10001ea27a09e627945e4178c5e1277c9de17745dc176c5da17609d717549d410001d227445d0173c5cd2
|6,1=>0xa1ca861a108000a08a8029fc67d29f067b19e4a7729d4a73200027219c467019bc66d29b066a29a0a671994a64198c6621984400097ca5d296ca59295ca561950a522940a4f1934a4b2924a472914a44190c641290063e200023d18eca3928dca3528d063228c0a2e28b0a2b18a4a281
|6,2=>0xb90ae22b80ade2b70adb1b648000b606d71b586d42b4c6d12b406ce2b308000b288000b246c72b186c42b0c6c12afcabd2af06ba2ae46b81ad8ab510002b41ac8ab11abcaad2ab06ab1aa4aa72a986a42a88aa02a78a9c2a6c6992a606971a586951a506931a44a8f2a34a8b2a286891
|6,3=>0x2f92bdcaf52bccaf12bbcaed2bacaea1ba46e72b984000
|7,0=>0xc247081c1c4000c184000c1440000003041c0c40000000000c084000c047001bfc6fe1bf44000bf06fb1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x600b41602905009c128240420800f81d0380680c81802e0580a012022040050090100180280400600800800
|1=>0xfe1f83d87a0ee1d83686c0ca1903005f0bc1602b8560a814c2905009812c2504808c110210410800fc1b834
|2=>0x21241882904206408809001fa3f07c8f81ee3a46c8d81903005c8b71662c8588b01422804c09712022040880
|3=>0x37e6f4dc9a1312614c097a2da594b015f2bc55ca49432824f49d93925a4949212124047c8c91822a4448810f
|4=>0x65ac0d7e2e056eacd48a90502a013fa7b4f29d1342664c09212223d46e8d51a23344081101a02402800f79e7
|5=>0x719df3b835ceb7d6bacb58ea0cb39027ecf996affdfdbf77e6fadf3bb9762e65bdb736d6d8d9db38
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>2
|4,0=>0x100000a000000000000000000000000040000000400070000000a01000000000000000a0400260000000000000006000000010000000000000000000d0000001640000a00000000004002000004000000000000000a000007040000000100010000000000000004000000000107000069000000000400
|4,1=>0x1004000000000000000000000000000000023180000000000000000101600000000010000000000000016000a00020000
|5,0=>0x670b0a000100040500005901004e04166a010000101700004016401800000016160e00000d000118000a160a430000160a00670a00230026242b2c16001626581d00012c04820a00380d4c58820782000096001f010101160b04160004401600360000000a6106b40a060a0a16580a0000000101008e000c0009000016160000
|5,1=>0x40005801002601000a0404012c000000231f0a00160d2816580c230d001600323600403500350c062500160058000201001f0016070001000b5801000100001f010146000701000c265c000147450098008601020000040a160e4e9616062b2336100a000401161616000a18690c64012323050d011a043732230a0a3510
|5,2=>0x4a1697036700011605020d5b010705170219400a585e1f4e0a161600590a585907234001100007010100250700001213041f0016008300180000000458405059000a0000670e03015a3501591640580018018f1640005e16011800750a00401618166716820d100016080000161600012a0096580b00040a011b0061000067
|5,3=>0x15f013e58150c000b005d8d01180d040001071600280407002399402058010006000102010000012800161400040a0123011608160008050041411603080001
|6,0=>0x608fa40e5568854d3346883195b83829016b187e063c93816c381e330d1668a17f7050a7a28a9a20ab3a34689c83403aa53e87183f219276484b3b7d685fa1aa7a880c15562f40510d51653f1f9087633b8ca9b17b36406d016d8077762c7862689b7c4c5608a80c16946e9d401f8fbb5401ae465f46b3186508166e01014033
|6,1=>0xbc317479b6733f746f723d520d74152db9664278301c658f632e3a117449872766ac34113133b57272b2a659893d18919e334f775d6846883c44222d3fa027ac99ada39c3850085dba9db05084
|7,0=>0x34214966b76634660f5739716b9f4c6f34348b3957538baf
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_27_32,6,runOps true dzo_27_32 (0,roots_27) ops)] else [])++(if pm.testBit 1 then [(dzo_58_1,5,runOps true dzo_58_1 (0,roots_58) ops)] else [])++(if pm.testBit 2 then [(dzo_56_1,4,runOps true dzo_56_1 (0,roots_56) ops)] else [])++(if pm.testBit 3 then [(dzo_19_8,4,runOps true dzo_19_8 (0,roots_19) ops)] else [])++(if pm.testBit 4 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])++(if pm.testBit 5 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 6 then [(dzo_51_8,5,runOps true dzo_51_8 (0,roots_51) ops)] else [])++(if pm.testBit 7 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 8 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 9 then [(dzo_57_2,4,runOps true dzo_57_2 (0,roots_57) ops)] else [])++(if pm.testBit 10 then [(dzo_43_16,4,runOps true dzo_43_16 (0,roots_43) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_59 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_27_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_58_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_56_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_19_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_42_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_51_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_43_16_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_27_32 6 s (0,roots_27) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_59 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_27_32_32 h
def symsG:List (List (Nat × Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_59==dom_59) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 goalM v ys):RunD true dom_59 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 4 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 49 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 49 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 195 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 3 192=true)
private theorem z4:∀ i,0 ≤ i → i < 195 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 z4_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 320 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_320:∀ i,320 ≤ i → i < 384 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 320=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_384:∀ i,384 ≤ i → i < 448 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 384=true)
private theorem z5:∀ i,0 ≤ i → i < 448 → Z 5 i=true:=(range_split (range_split z5_0 (range_split z5_64 z5_128)) (range_split (range_split z5_192 z5_256) (range_split z5_320 z5_384)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 128 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128:∀ i,128 ≤ i → i < 192 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_192:∀ i,192 ≤ i → i < 205 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 13 192=true)
private theorem z6:∀ i,0 ≤ i → i < 205 → Z 6 i=true:=(range_split (range_split z6_0 z6_64) (range_split z6_128 z6_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 24 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 24 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_59 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_59 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59_0 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_59_0
theorem lowS_59_0:Lower true dom_59 roots_59 goal_59_0 9:=S_59_0.noCircuit
def isoMv_29_32:List (Nat × Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 6:=lower_iso isoMv_29_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def isoMv_49_12:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_49_12:Lower true dom_49 roots_49 goal_49_12 4:=lower_iso isoMv_49_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def isoMv_60_1:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_60_1:Lower true dom_60 roots_60 goal_60_1 5:=lower_iso isoMv_60_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_41_20:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_41_20:Lower true dom_41 roots_41 goal_41_20 4:=lower_iso isoMv_41_20 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def dzo_41_4:=0x303000003030
def gzo_41_20_4:=0x302000002000
theorem lowSh_41_20_4:Lower true dzo_41_4 roots_41 gzo_41_20_4 4:=lower_iso (d1:=dom_41) (roots1:=roots_41) (T1:=goal_41_20) [(dom_41,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41_20
namespace S_45_16
def pairsG:List (Nat × Nat):=[(1,9),(1,33),(5,13),(5,37),(8,9),(12,13),(12,44),(32,33),(36,37),(36,44),(40,41),(40,44)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_45.map (· &&& dom_45)
def goalM:Nat:=goal_45_16 &&& dom_45
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_41_4,4,runOps true dzo_41_4 (0,roots_41) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_45 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_41_20_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_41_4 4 s (0,roots_41) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_45 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_41_20_4 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_45==dom_45) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_45 goalM v ys):RunD true dom_45 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_45 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_45 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_45 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_45 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_45 roots_45 goal_45_16 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_45_16
theorem lowS_45_16:Lower true dom_45 roots_45 goal_45_16 5:=S_45_16.noCircuit
def isoMv_53_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_53_8:Lower true dom_53 roots_53 goal_53_8 5:=lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
def isoMv_38_1:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_38_1:Lower true dom_38 roots_38 goal_38_1 4:=lower_iso isoMv_38_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def dzo_38_1:=0xaa000000aa
def gzo_38_1_1:=0xa800000080
theorem lowSh_38_1_1:Lower true dzo_38_1 roots_38 gzo_38_1_1 4:=lower_iso (d1:=dom_38) (roots1:=roots_38) (T1:=goal_38_1) [(dom_38,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_38_1
namespace S_39_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,35),(4,6),(5,7),(5,37),(33,35),(33,37),(34,35),(34,38),(36,37),(36,38)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_39.map (· &&& dom_39)
def goalM:Nat:=goal_39_0 &&& dom_39
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_38_1,4,runOps true dzo_38_1 (0,roots_38) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_39 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_38_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_38_1 4 s (0,roots_38) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_39 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_38_1_1 h
def symsG:List (List (Nat × Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_39==dom_39) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_39 goalM v ys):RunD true dom_39 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_39 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_39 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_39 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_39 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_39 roots_39 goal_39_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_39_0
theorem lowS_39_0:Lower true dom_39 roots_39 goal_39_0 5:=S_39_0.noCircuit
def isoMv_57_4:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57_4:Lower true dom_57 roots_57 goal_57_4 5:=lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_0
def dzo_29_32:=0x3333333300000000
def gzo_29_32_32:=0x3222222000000000
theorem lowSh_29_32_32:Lower true dzo_29_32 roots_29 gzo_29_32_32 6:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_32) [(dom_29,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def dzo_49_12:=0x3000300030003000
def gzo_49_12_12:=0x3000200020000000
theorem lowSh_49_12_12:Lower true dzo_49_12 roots_49 gzo_49_12_12 4:=lower_iso (d1:=dom_49) (roots1:=roots_49) (T1:=goal_49_12) [(dom_49,12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_49_12
def dzo_60_1:=0x2222222222222222
def gzo_60_1_1:=0x2222222022000000
theorem lowSh_60_1_1:Lower true dzo_60_1 roots_60 gzo_60_1_1 5:=lower_iso (d1:=dom_60) (roots1:=roots_60) (T1:=goal_60_1) [(dom_60,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_60_1
def dzo_53_8:=0x3300330033003300
def gzo_53_8_8:=0x3200220022000000
theorem lowSh_53_8_8:Lower true dzo_53_8 roots_53 gzo_53_8_8 5:=lower_iso (d1:=dom_53) (roots1:=roots_53) (T1:=goal_53_8) [(dom_53,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53_8
def dzo_57_4:=0x3030303030303030
def gzo_57_4_4:=0x3020202020000000
theorem lowSh_57_4_4:Lower true dzo_57_4 roots_57 gzo_57_4_4 5:=lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_4) [(dom_57,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_57_4
def dzo_45_16:=0x3333000033330000
def gzo_45_16_16:=0x3222000022000000
theorem lowSh_45_16_16:Lower true dzo_45_16 roots_45 gzo_45_16_16 5:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=goal_45_16) [(dom_45,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
namespace S_61_0
def pairsG:List (Nat × Nat):=[(5,37),(9,25),(9,41),(13,29),(13,45),(17,25),(17,49),(21,29),(21,53),(24,25),(28,29),(28,60),(33,37),(33,41),(33,49),(36,37),(40,41),(44,45),(44,60),(48,49),(52,53),(52,60),(56,57),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_61.map (· &&& dom_61)
def goalM:Nat:=goal_61_0 &&& dom_61
def NN:Nat → Nat
|4=>1
|5=>4
|6=>2
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|4,0=>0x41a5b2e0
|5,0=>0x5fb7b7fe4e47719d1d459bec14d52ea8
|6,0=>0xd3b212568cff9f0a
|7,0=>0x653667d8
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x8888880088888a2002200220022008800000088000001100330011003300cccccccc000000033000000330000008888000088880003333000033330000cc00cc00cc00cc030303030303030308888888888888889133333300000000
|_,_=>0
def stPool:Nat → Nat
|0=>0x7432174321a74362174321b74321974321873621543210
|_=>0
def stOffB:Nat → Nat → Nat
|4,0=>5
|5,0=>0x5d9162d856
|6,0=>0x8d9d6
|7,0=>0x295
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 12 then fld (dictB (i / 512) (i / 32 % 16)) 62 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 10 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0xc4431283110c
|_=>0
def opOffB:Nat → Nat → Nat
|5,0=>0x48001
|6,0=>0x20b1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 7 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xfff91a0700
|_=>0
def pmB:Nat → Nat → Nat
|5,0=>0x42
|6,0=>0x23
|7,0=>3
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_29_32,6,runOps true dzo_29_32 (0,roots_29) ops)] else [])++(if pm.testBit 1 then [(dzo_49_12,4,runOps true dzo_49_12 (0,roots_49) ops)] else [])++(if pm.testBit 2 then [(dzo_56_1,4,runOps true dzo_56_1 (0,roots_56) ops)] else [])++(if pm.testBit 3 then [(dzo_60_1,5,runOps true dzo_60_1 (0,roots_60) ops)] else [])++(if pm.testBit 4 then [(dzo_53_8,5,runOps true dzo_53_8 (0,roots_53) ops)] else [])++(if pm.testBit 5 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 6 then [(dzo_57_4,5,runOps true dzo_57_4 (0,roots_57) ops)] else [])++(if pm.testBit 7 then [(dzo_45_16,5,runOps true dzo_45_16 (0,roots_45) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_61 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_29_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_49_12_12 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_56_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_60_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_53_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_45_16_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_29_32 6 s (0,roots_29) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_61 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_29_32_32 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_61==dom_61) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 goalM v ys):RunD true dom_61 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 1 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 4 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 2 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 1 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 7):∀ i < NN s,bar true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_61 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 7) (h:RunD true dom_61 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61_0 8:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_61_0
theorem lowS_61_0:Lower true dom_61 roots_61 goal_61_0 8:=S_61_0.noCircuit
def isoMv_54_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_54_8:Lower true dom_54 roots_54 goal_54_8 5:=lower_iso isoMv_54_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
def dzo_54_8:=0x5500550055005500
def gzo_54_8_8:=0x5400400044004000
theorem lowSh_54_8_8:Lower true dzo_54_8 roots_54 gzo_54_8_8 5:=lower_iso (d1:=dom_54) (roots1:=roots_54) (T1:=goal_54_8) [(dom_54,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54_8
namespace S_62_0
def pairsG:List (Nat × Nat):=[(2,6),(4,6),(10,14),(10,26),(12,14),(18,22),(18,26),(20,22),(24,26),(28,30),(28,60),(34,38),(36,38),(42,46),(42,58),(44,46),(44,60),(50,54),(50,58),(52,54),(52,60),(56,58),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7fffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_62.map (· &&& dom_62)
def goalM:Nat:=goal_62_0 &&& dom_62
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_54_8,5,runOps true dzo_54_8 (0,roots_54) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_62 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_54_8_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_54_8 5 s (0,roots_54) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_62 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_54_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_62==dom_62) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_62 goalM v ys):RunD true dom_62 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_62 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_62 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_62 roots_62 goal_62_0 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_62_0
theorem lowS_62_0:Lower true dom_62 roots_62 goal_62_0 6:=S_62_0.noCircuit
def isoMv_23_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 5:=lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_22_40:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def isoMv_14_48:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaaaa,0,1)] (by decide +kernel) (by decide +kernel) lowS_14_48
def isoMv_51_12:List (Nat × Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51_12:Lower true dom_51 roots_51 goal_51_12 5:=lower_iso isoMv_51_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def isoMv_23_40:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_iso isoMv_23_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def isoMv_39_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_39_8:Lower true dom_39 roots_39 goal_39_8 4:=lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_49_4:=0x30003000300030
def gzo_49_12_4:=0x30002000200000
theorem lowSh_49_12_4:Lower true dzo_49_4 roots_49 gzo_49_12_4 4:=lower_iso (d1:=dom_49) (roots1:=roots_49) (T1:=goal_49_12) [(dom_49,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_49_12
def dzo_22_32:=0x55005500000000
def gzo_22_40_32:=0x54004000000000
theorem lowSh_22_40_32:Lower true dzo_22_32 roots_22 gzo_22_40_32 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_51_4:=0xf000f000f000f0
def gzo_51_12_4:=0xf000e000e000c0
theorem lowSh_51_12_4:Lower true dzo_51_4 roots_51 gzo_51_12_4 5:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_12) [(dom_51,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_12
def dzo_23_32:=0xff00ff00000000
def gzo_23_40_32:=0xfe00ea00000000
theorem lowSh_23_40_32:Lower true dzo_23_32 roots_23 gzo_23_40_32 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
namespace S_55_8
def pairsG:List (Nat × Nat):=[(1,3),(1,17),(1,33),(2,3),(2,6),(2,18),(4,6),(5,7),(5,21),(5,37),(16,17),(16,18),(20,21),(20,22),(20,52),(32,33),(34,35),(34,38),(34,50),(36,37),(36,38),(36,52),(48,49),(48,50),(48,52)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_55.map (· &&& dom_55)
def goalM:Nat:=goal_55_8 &&& dom_55
def NN:Nat → Nat
|3=>3
|4=>12
|5=>13
|6=>6
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x80fb7a4d58dfe78152948fd1
|4,0=>0xbb6316817722f36348af5d5335cdabfd30570d32303d70d325197355131d16ed125c01bc10773ac5100a6bf50bc98e2a
|5,0=>0xc8be71d0be2624c9a9bc9208a60ddcc099d399f36af9db5a56b10e1844f99c162b43d1ba2afc17e62afb0b6d1c46cc270763b48b
|6,0=>0xa5e2e6eba3f876e66f149ea93cfb43bc23419d79003c1023
|7,0=>0xa5e2e6eb
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x5500440055004411000000110000550000005500000000ee000000eeff00ee00ff00eedd00cc00dd00cc500050005000503300000033000050004000500040d000c000d000c0ff00ee00000000ee000000ee0000ff00ff00cc00cc1100ff00000000fa00fa00fa00facc008800ff00aa00000000ff00aafa00ea00fa00eaff00aa00ff00aaff00aa00000000cc00cc00cc00ccaa000000aa0000ff00aa00cc0088ff000000ff0000f000f000f000f0ee00ee00ee00eeff00cc00ff00ccee00aa00ee00aaff00ff00000000f000c000f000c0aa00aa00aa00aa3300cc003300cc
|_,_=>0
def stPool:Nat → Nat
|0=>0x3982329d61e8d07587832a161c8ca812c23409611ed075846569d611a0fa58468587381a161b8d16586a83ac2369e8b9a04b0a0eb0c865444c32b4e641d700a0eb0bc6872c2d61d6a4a0e61944418820
|1=>0xd07584683ac2341ccb08d07587a342c391a22b08da83ac2341e8b08d07587e341d61f0ca8
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x84044004
|4,0=>0x4353e53953452f52a52552051b51651150c5
|5,0=>0x8f68968367d67767166b66566055a65464e6486
|6,0=>0xb15ab6a56a059b5956
|7,0=>0xb65
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 32 then fld (dictB (i / 512) (i / 32 % 16)) 56 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 12 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x58540738738540541840540542d3874056ad40542d405407387418405
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x11000000001000000000
|5,0=>0xd16080000b1002480081311086221
|6,0=>0x12188c05e2e1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 9 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x3af6fd9f63d6f100360c01003c0c0180400800
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x100030000
|5,0=>0x8601204097362
|6,0=>0x5deace
|7,0=>0xb
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 4 (j % 128);fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 1 then [(dom_54,5,runOps true dom_54 (0,roots_54) ops)] else [])++(if pm.testBit 2 then [(dom_53,5,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 3 then [(dom_51,5,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 4 then [(dzo_49_4,4,runOps true dzo_49_4 (0,roots_49) ops)] else [])++(if pm.testBit 5 then [(dzo_22_32,4,runOps true dzo_22_32 (0,roots_22) ops)] else [])++(if pm.testBit 6 then [(dom_19,4,runOps true dom_19 (0,roots_19) ops)] else [])++(if pm.testBit 7 then [(dzo_51_4,5,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 8 then [(dzo_23_32,5,runOps true dzo_23_32 (0,roots_23) ops)] else [])++(if pm.testBit 9 then [(dom_39,4,runOps true dom_39 (0,roots_39) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_55 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_23_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_49_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_19_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_51_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_39_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_23 5 s (0,roots_23) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_55 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_23_8 h
def symsG:List (List (Nat × Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_55==dom_55) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_55 goalM v ys):RunD true dom_55 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 3 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 3 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 12 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 12 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 13 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 13 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 6 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 6 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 1 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 7):∀ i < NN s,bar true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_55 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 7) (h:RunD true dom_55 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_55 roots_55 goal_55_8 8:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_55_8
theorem lowS_55_8:Lower true dom_55 roots_55 goal_55_8 8:=S_55_8.noCircuit
def isoMv_46_16:List (Nat × Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46_16:Lower true dom_46 roots_46 goal_46_16 5:=lower_iso isoMv_46_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
def isoMv_43_20:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_43_20:Lower true dom_43 roots_43 goal_43_20 5:=lower_iso isoMv_43_20 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def dzo_14_32:=0x555500000000
def gzo_14_48_32:=0x544000000000
theorem lowSh_14_48_32:Lower true dzo_14_32 roots_14 gzo_14_48_32 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_20_4:=0xf0e00000e0c0
theorem lowSh_43_20_4:Lower true dzo_43_4 roots_43 gzo_43_20_4 5:=lower_iso (d1:=dom_43) (roots1:=roots_43) (T1:=goal_43_20) [(dom_43,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43_20
def dzo_15_32:=0xffff00000000
def gzo_15_48_32:=0xfeea00000000
theorem lowSh_15_48_32:Lower true dzo_15_32 roots_15 gzo_15_48_32 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
namespace S_47_16
def pairsG:List (Nat × Nat):=[(1,9),(1,33),(2,6),(2,10),(3,7),(3,11),(3,35),(4,6),(5,7),(5,13),(5,37),(8,9),(8,10),(12,13),(12,14),(12,44),(32,33),(34,35),(34,38),(34,42),(36,37),(36,38),(36,44),(40,41),(40,42),(40,44)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_47.map (· &&& dom_47)
def goalM:Nat:=goal_47_16 &&& dom_47
def NN:Nat → Nat
|3=>4
|4=>20
|5=>38
|6=>8
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0xdce8f7f6d2a105ba757108572f6bc743
|4,0=>0xd4ae6952c1049790abc7700e994b3fa58fb25c53736f580b6b9134b15b3f2d40589ca3f9577e351c348ec43533be1a052e03a65427895bf31ec42dc516b4c83a0987f25108c4963e05acef89023cffdf
|5,0=>0xdbed0874d08351f3c7f1dd2ebe9f478ebdc60a32ac9aae158eb098a67cd23d057c0db15b78fd1a2071a897b66fc5d6636df3a8266c84a0df65c3bc58594f185b58e1c91e53e31fd3504383644dccdb5442be05b73ee302ef3c08d0233aad941438c18f4436c63be9280bc35d1beb6c4a1b6caeea176629e417436b3e16b4c83a166de8e61108d4d80a5ae06806922bef02827adb006e62e8
|6,0=>0x8151f4be3c08d0233b576e793aad94142c66de412ac37c4c1720d1bf058847cc
|7,0=>0x3b576e79
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x550000000000ddcc0000ddcc00550000000000aa000000aa00ee000000eebbaa00000000eeee0000eeee10f0000010f0ffee00000000ffaa0000ff00444400004444faaa0000000030f0000000f0cc000000ff0000ff00000000ffaa0000ffaaeecc0000eeccaa000000aa00ffaa00000000550000005500ffcc0000ffccee000000ee00aaaa0000aaaa33cc000033ccffff00000000ff000000ff00f0c00000f0c0eeaa0000eeaaf0f00000f0f0cccc0000cccc55aa000055aa55aa00000000
|0,1=>0xf0000000f0f0000000f000ffcc00000000ffee0000ffee0fff00000000fff00000ff00f0f0000000000f000000ff00aaff00000000ff500000ff50110000001100500000005000aafa0000aafaa0f00000a0f000000000ffaafaaa0000faaa005000000050c0c00000c0c0333300000000af000000af00f0000000f0f0330000003300303000003030332200003322
|_,_=>0
def stPool:Nat → Nat
|0=>0x74718308c7071830896c60c26891c60c92070c204c1c615924718225858d0c225034308e5c60c224758308c1c61495474030811940c22471822530c24894474060cf1c614224d18308e1c30813460c23072c32891c52891c52481c61440c2040
|1=>0x1c60c226c1c60c2ac91c60c226a1c60c5089183089a471a80c22474060c23874060c23072c60c22471830898870c231c1c60c22671c60e62621c60c29091c60e30891cb1850891c60c98a11c61422471830898071830897c7183782247183089
|2=>0xd90891cb1830891c60c2247183089887183c42247183089947183089dc7183d82247d460c2247d060c2247183089cc72c60d9247c860c2247183089c071832822472c60c9550183089a4740308e1830899511c60c2bc91ee1830891c60c226d
|3=>0x71830891c6
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x620210088004
|4,0=>0x3729a54c8a5f52d29554a0a4b5232905478a3751928b5450a2350f286902aa105
|5,0=>0x29ad476a0b4eda6ad2f694b48da3ad185893431a0cd0067d33d19dcce8671ab759aecd1665b315980aba65a32b9950ca264e325d522c8b642b1fd8f2c736
|6,0=>0xbe35d9ae2b6b6b2b57dab2d536
|7,0=>0x1825
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 56 then fld (dictB (i / 512) (i / 32 % 16)) 48 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 6 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 13 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x894625189c70c0c9c60e18306251b1c664182071b189c625183060b189c62518286271a5c625189c625189c6271820608
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x2200000000000000040000
|5,0=>0x14100000013190800011180bc400000000000e10034400c158a852200409c40061289040031108000000
|6,0=>0xd8e840191c0dc6c351
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 14 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 63),wireSAt ((code >>> 8) &&& 63))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 9 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xffe47f7d7b79716041403028201b1008070403020100
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x400000000800
|5,0=>0xe004144004333400000060080159c24514095180c48800
|6,0=>0x8c1f0ace52
|7,0=>0x11
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 5 (j % 128);fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_46,5,runOps true dom_46 (0,roots_46) ops)] else [])++(if pm.testBit 1 then [(dzo_14_32,4,runOps true dzo_14_32 (0,roots_14) ops)] else [])++(if pm.testBit 2 then [(dom_43,4,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 3 then [(dzo_41_4,4,runOps true dzo_41_4 (0,roots_41) ops)] else [])++(if pm.testBit 4 then [(dom_45,5,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 5 then [(dzo_43_4,5,runOps true dzo_43_4 (0,roots_43) ops)] else [])++(if pm.testBit 6 then [(dzo_15_32,5,runOps true dzo_15_32 (0,roots_15) ops)] else [])++(if pm.testBit 7 then [(dom_15,4,runOps true dom_15 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_47 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_46_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_41_20_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_43_20_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_48_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_46 5 s (0,roots_46) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_47 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46_16 h
def symsG:List (List (Nat × Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_47==dom_47) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 goalM v ys):RunD true dom_47 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 4 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 20 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 20 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 38 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 38 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 8 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 1 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 7):∀ i < NN s,bar true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_47 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 7) (h:RunD true dom_47 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47_16 8:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_47_16
theorem lowS_47_16:Lower true dom_47 roots_47 goal_47_16 8:=S_47_16.noCircuit
def isoMv_54_1:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_54_1:Lower true dom_54 roots_54 goal_54_1 5:=lower_iso isoMv_54_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
namespace S_62_1
def pairsG:List (Nat × Nat):=[(2,6),(2,10),(2,34),(4,6),(4,36),(8,10),(8,24),(8,40),(12,14),(12,28),(12,44),(16,24),(16,48),(18,22),(18,26),(18,50),(20,22),(20,28),(20,52),(32,34),(32,36),(32,40),(32,48)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7fffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_62.map (· &&& dom_62)
def goalM:Nat:=goal_62_1 &&& dom_62
def NN:Nat → Nat
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|6,0=>0xc99170a
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x5555555500000000aaaa0000aaaa000154015401540154028282828282828284444444444444444
|_,_=>0
def stPool:Nat → Nat
|0=>0x4688
|_=>0
def stOffB:Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 63 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 3 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 8 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 7),wireSAt ((code >>> 5) &&& 7))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf0
|_=>0
def pmB:Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_60,5,runOps true dom_60 (0,roots_60) ops)] else [])++(if pm.testBit 1 then [(dom_54,5,runOps true dom_54 (0,roots_54) ops)] else [])++(if pm.testBit 2 then [(dom_46,5,runOps true dom_46 (0,roots_46) ops)] else [])++(if pm.testBit 3 then [(dom_58,5,runOps true dom_58 (0,roots_58) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_62 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_60_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_46_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_58_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_60 5 s (0,roots_60) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_62 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_60_1 h
def symsG:List (List (Nat × Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_62==dom_62) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_62 goalM v ys):RunD true dom_62 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_62 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_62 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_62 roots_62 goal_62_1 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_62_1
theorem lowS_62_1:Lower true dom_62 roots_62 goal_62_1 7:=S_62_1.noCircuit
def isoMv_23_32:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_30_32:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_0
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfeea0000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(1,17),(2,3),(2,6),(4,5),(4,6),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(16,17),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>6
|3=>60
|4=>115
|5=>221
|6=>75
|7=>13
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xe77c113d96e715fd84cb36aa663b432334479cc605723852
|3,0=>0xe32cdce9e0cd7b16b2e2f8c8b0c90f16a45f3aa0a2441b20a19e3d119d52e25d9638e8f58f0bf3318a2547fd885e21497f95fd787c9d94346efd24806bc1fc306a0eddb669291a4f65209d8c62a447cb6007a545580ade975624d83454ef1fcd5479c62b504648be502b1f844fa8a7b04fa21a7a4c20948e459b0020453a62ed43f161e641e660d13d0885cf3c9e43bf38699e2937b3523934fa787c2be1abbd29d51d5827c9cf0c1fe146271b8d6a36162e3dfa1497a16f1404f3c6113ae4570fdec44e0c5d915f0bcfa8760ae8822e0aa47b1c0aa2e4e709f54dd609aa8c6b096f711c05d9543b05a09c64027fb23f
|4,0=>0xf88b121bdd410db8d1133626cbaf6331c42589c3a802f718a50e0bf3a48506e994aaf7508dcf8e0488b927918735da29852c4328812ed8c17eb809c77d3494bd7d0379b27ca8998d7974442571dee69470e1439270b6af5d6edf4c7f6dccdf3c6836d176680bd06166c71628632c3f6862d35b045edf5ed35dee6f825d9be30f5b55ee485b3d5e5a59d04230596b636c58ab1b425540f7d4545d46ed520a3541505f26cf4fc7e1b54bb0aa5545f6563a45a1e545453a7c9d452eadf544cbf1e541eadb9741e662fb4111b6ca407e69993f9b53ee3de68bad3d888e263d653f3b3a2f451f37d5d05836d7ea173610e05d349b1be1345eac4a3443d1e433c16527337d731c3315cc0a31e2e26c3174431d3021862a2dd40b4e2d42133f2c42e0902a085bc32908c2e8280b5b072793b32626ce8ca326baa6e324b1d5e4216bd3922111e3011f87dcae1f6224961e12d5871de0f1b11ddd9ddd19a473f818eb802118e1f7071888265b177d0234161207c6150b652514d2b56f1078bbb51001684c0f1a9c9d0d09ca810c94a4800a852818088523ac08812045074d774c06f32a2006cd007a066dc74906666ee2061ff50f05ac74cf050e3e9c0467e2ff033e8ad102dd8e9a013a84690117afc3
|5,0=>0x49a1fa394944f59948773af647ce092a4788f640468606aa439f9758438d03024258341840d49df040b2d5c140b2036a400caa233ebdd55e3e0ba5b23dd1a5683d867f143d1825783cde142f3bb685e83b7e67fa3acc6e253a6d6f523a5d89983967034738f920f13814d90836eb5069354cd925353d53f734ff6990342144112fc8dae02f43fc842d92e0092d57fd142be20dff2b373e1f2a48467c29b4f93528ae69ed28a153a5274dc3c3254f218d24fe9f8024e3533024c46c4d241dcca4241cb7b22326eae921d08c112175128f1febdd111fbc84251fb84f691f55dfec1f4f26e11e489d4d1e0f4f6c1dee9d271de8f2ad1d3ce97e1cd6d2541c77b5a01b1d04c31a7f49c819927a8f198ce1f3192a467a190b5d3b18d1621618c50e0818b5b64f1855f9d317f89e0017684dce1662ba7b1542f2b8148e0880145851971400b75b13a7d2f71372f57212ef47ae12e256e81267305511f92a861175bbd510d02a8710410323103ee1de1026e1e30f3e81490e9b53410d9ce5310cf234830c287cef0bc415b80b0e103c0ad15a450a8ca5f60a5a15d80a4954ce0a09a33009b7f91f09a0ff5b09966c850964c27808aa2e5a086f8f480790264206d064e8068126b9063fd31205a7cb26055aab69053466f8049b9c2d042604df03d503020304148201f1297d01e69cb301d693990145c58201041bab00afdc2100a7504a
|5,1=>0xf3646964e99d8a4ce9148542dc924058dc17eff7da867c97d9331fc3d18c4d1fcfe24645c6a4dd9cc4a6440fc427da71c2afcbabc15dd4f2bfe3b222bfd86441bceebcd0b44642d4b437c42faf1e9219ac3c1109a951d62ca7ad298ba54be7eea4ce50bca2643d339df08a979ce1902a992da287977c37b994e5febc91d217e68f8f1b778f21023d8c8113df8c2d4720874309d9867bd42683cea023801484ee7f0f2a6c7ea82caf7e66eb0d7a19de6378786220786518b678180520751696de749ffdb872885be1712a8d6570e1439270d611ff70bc8ac86f92c96d6f7717e56ae466b068548ee6682e065f65fb51eb645efea86414b3a56364827b63400eac62eca9e46256342b618f5f4a610b5fed5f25078f5d8f47805cf8c63e5cf6f3ef5c0c808d5b7132d656b9bb40566ad2115631218c528f7f7951ab89e250c951844fc7e1b54f0981774e7506584e1d02df4dc7e76c4c919c034b82a8794b5e1c384b1446704aebb2864a82231849df6f9249c04ff5
|6,0=>0xee573519e7c60b1dce52c4fac6a4dd9cc41b66cbb58372c9b44642d4af753242ae051815abea8af4a2ce316898e3564c989ce8d793b7475f91863ebb8cc90b2686981ddb7f5bec7e79238a6e77f7b44a75d43412745f33c174064f5d71732e19712a8d656f92c96d6b1cb35a668a76c9642830f25dd68d6a5cf6f3ef5cc01e274e0ae47e4c535ece472e25f7466611f241ecc3373f1826db3ed81f4c3ebdd55e3abf154635cd937131c1c2362f79e7db2f61f1a42ee8d5252e160c322d9fc0262ae9b58328ec7d1328c7924328ae69ed289999ce241cb7b222fed1a022c5a1b520f514d61fc249c41fa24f531c25b9451b0173181a79258e17f89e0017f3b30d16032cd50d7a72cd0d59fc0a0a8ea06009a0ff5b089d02fa08088c370728aace05f43a9b03d43e99017e3b29
|7,0=>0xd5d7a2ceaacb8ff0974979bd894af9796ec079dc6432baff34b0cb8f2c56ab271f16380d1495c9760d59fc0a09e2bbbd090d6eb4
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3fc03fcffaaffaaaa00aa00ccccccccaffaaffaaaa0aaa0ff00fffcffffaa88ffccffccf0f0f0f0eeaaeeaa0000ffaac3c0c3c000fc00fcffffaaaaeaeac0c0ffc3c0c0fcfcfcfcf000f000333c333cc3c33c3caaaaaaaa1616161696969696ff00ff00eaeaeaea0303fcfc55aa55aa3c3c3c3cffff0000666666660ff00ff0
|0,1=>0xff00aacccc00005a5a5a5a44444444222222220f0ff0f0ffff00fc5555aaaacc30cc300f0c0f0ceeeceeeccffccffc0cc00cc0f600f600fafafafaa0a0a0a0ff000300ffffccccfafaf8f8eeeeaaaaffc0ff303333cccc0000aaaa33cc33ccff030000c0c0eaea55550000ffff0330dededede48484848cc32cc32c0c0c0c0
|0,2=>0xc0c0c0c03030202fefcfefcecececec1212121204040404b700b7001515aaaac3c2c3c254fc54fceeeaeaea50705070fcfcfffc0300030007700770ff000000333033300f0f0c0cfcfca8a8c0c0303003030c0c3e3c3e3cffffaa00989898980e0e0e0e14143c3ceca0eca0fffffcfcfcfc00003c3c3f3cfefe00001e1e3c3c
|0,3=>0xfe00fefff8fff8ccccfafa33323232060606063033303033323332fffcfffcff00fff000003030aaaa0000fafaf0f00e0c0e0cffffaaa0f0c0c0c0ffc0ffc00f0a0f0ac8c8c8c833223322ff0eff0e0f000f0011114444fffff0f0f0f00000fff0fff0faaafaaaeeeeeeee888888881e1e1e1efc00fc003f3c3f3c30303030
|0,4=>0xcfcfcecefcfcaaaa54545454ffff888803020302fafaaaaa55555050c8c8c0c0ffeeffeecc00cc00aa88aa8800fe00aa0a0a0a0afe00ff0000000e0e77777070fefefcfcffffff0000fcfcfcffabff00ff03ff00f8f88888ffaaaaaafefefefefcfffcfc0303000032323232fca8fca8333330300000fcfc00aa00aaffaa0000
|0,5=>0xf0f0fafa51505150a8a8a8a80c0f0c0ccdcd0000fe00fe00c0eac0ea00ffff0000fffcfc54ff0000f3f0f3f01030103003033030f6f6f6f60202020256565656ccffcccc55005500ffaaff00aaaaa0a0464646463030c0c015150000aaaa8888ffffc0c0ccccffccff0cff0c0000fefefafaa0a0ffff0c0cf0f0fff0fc00fe00
|0,6=>0xb0a0b0afafafffaff88ff885700570000ff000000ff00fcfffffafaffcccccce4e4e4e4fff0f0f000cc00ccffcc0f0c33332222ff50ff5033003300faf0faf0eecceecce0c0e0c050505050feccfecc0f0f000011001100bbbbaaaaafafaaaa000a000a0000ff002f2f22220f0f0a0aabaaabaababababaffff0a0a33330000
|0,7=>0xfcff000050555050cfcccfccafafaeae0c0e0c0e30ba30ba3232000055554444010100008f8f8888dcdcfcfc5050f0f0fcfc5454ccffccfccdcdccccccaaccaaf8f8f8f88c0c8c0c50f050f0f3f3f0f000f0fff055505550f3f2f3f211111010ffff030004040c0cf2f2f2f2ccc0ccc0c8fac8faffffa8a83f003f00fbfafbfa
|0,8=>0xfa00fa000000cccc050005000000ffccff00aa0055505050fffcfcfc5400540055ff0000cecececefffafafa0f0a0a0acceecceefcfefcfe57570000323032300f0c0c0cf0c0f0c0ab00ab0000300030fcfc00fc73507350feaafeaa00eeeeeeffa8ffa8fff0ccc0ccccf0f0
|_,_=>0
def stPool:Nat → Nat
|0=>0x1d8e872070500c0e0e100e00437050d80435050000434050cc04320b0040e31180a8042f070185c07168b05616050a80e25018a43016050a04e070500c0e0e13094481c0500004071188804161082804200507c041e0e80c041c0d86804190701830170b0540e0e030500413050482207070401e0707028040d050300e0b050080e090101c1007030140404018080200
|1=>0x500c04073218c04620518404043017c04070317804072e8180e411897004072d968041c2c8f40e160e16004072b8280407031585c070b154040a2a0a0040729818040629048041c05144a00a279380407268180e4c0512c0407051280e410b00492070500c04072411c0407051180417189148807218180407051080e4107018040705100040a018fc5c071f0f40e3c
|2=>0x359240e0e1002804070b028f80203858ca7b0101c147a2f8080e16051e4f0270b07014023b8701436038f8144e3b0440e0e101d404073a018380203828c0733919c1a1c05008ce710e028040e100287e0238070146f17858380a1481c82163702804070b018da0236070146b1701c2c0a351a40e681e0ec7207070801402038380c121701c5a3e05008ce66328700e41
|3=>0x340701491039a0380a480080e8f100291c160e0291a0246058380a01070144f0004516160e028d20745070142e28058144f0119d12310e0082c65321fc0407438801407100290c820101c383d429a45e160e02804074208014070b02906823481cd06532008380a320000e1c050f0740203828068140058380a279042c1c051fc047e0687014070b1f4380a0101c2c01
|4=>0x515004a50e028de020b070141f03858380a521a40ea30e0294407508701402038289e4e012802c1c050080e9f0517c0e9e0b07014070b070706045858380a410080e164ea1404070500d049c33834380a0101c60852d0080e200526c04070e0f444020705838043481d341c4c8080e8f4c02804970b2592a020b07014940105c2c154980924160e02892070b0183807
|5=>0x3858380a5b0085e0e1002804075a8290a0203829687303870143a598080e430500c040759058020720858380a0101c2c1c580080e1c0518c04070b0195e02038290a470101c1c06148082c1c1001004ae3017d020256828c05f0387014ac1d0080e0e3101804070b19556070b02854aa03858980a1501c2c1c548a40407189710a2e0385858a85381c2ca6050082e96
|6=>0x385838c21db040e160e0298002038397e1c050080e160e0297c020b85814280101c2c655e8080e0e1002904024481c2c650e008a0160e0289e0203858380a5e0080e165d87014160e028fea40101c400a2b01c82163299082ba0b070140203839720a0103840ae409100e43100280e4107080140e0b07014b8039042c0a428080e1c1e96c0e160e0296e070b0704c25
|7=>0x13482c1c0534404070b1955e0a0101c2ccf6702822070b070144e0101c382005310d2070e0299ac00101d98160e02804070b0f076cb0125c2e164b02804070b19438c90101c2c1c6402804070b02878360385838380119c1a1c0531c040729858380a0101c2c1c053140407070c4ca2e0101c2c0a278080e16008080e1c05310be020385838c3050082c1c051482402
|8=>0xe028fe0203858380a698080e1632b5c3869038c4380a60009ac0707070140233834380a1d8080e160520daa020b0715c5f408095a160e028be026a01c2c1c050080e0e0b33c14020387014601b0080e16328713a0203a3ce81c052700e160e028d6020f0382c1c0e80832070b070142e03858580a0119c2caf0e0280e160e029a6cb0101cd01c0511c5c1728058380a
|9=>0xe09452020f0594c1c050080e410b070140207058380a6e1a40e680e029582e0385838c805008380a000b80e500b028780203b403820050080e310e02906020b07014366d8b80e430b07014160e0297002038c438306889c0e0e0b070140203858ca0a698080e160e029b4020b07040ae40b640e160e0298002568583820050080ed00e028be696c01c2c1c050091016
|10=>0x630080e1667828e602039d0380a730080e0e72870142e0101c2ce4050080e160e38c14e203858380a010642c1c052000e160e028c00203858ca0a42808ce160e028240203858380a428082c1c05384520231058380a40808f0170b258140203b802c1c050080e160e029be0203b782c1c050382c1c0536d8c0203858380a09009ba160e028d60203858380a2b01c1c16
|11=>0xe0295c360101c380a773b40407073b0380a013600e1632828040e0b070147f0101c62160e0ec0e163287014a40101c2c1c05178041e03838400a0101c2caf050f004670b07014eb0101cba160e028040707058ca930101c1c431002804670687014ea0101c2ccf0517c040774858380a0101c2c1c0523404070b07014e87381c2c1c050080e160e2e414020b0701412
|12=>0xe2f40e160e029480203bd4380a7a0080ef30b070140203859e41c05008ce0d3287014020387014cd238081c160e0287e0203859e21c050085e160e02804160e029c2810101c2c0a1e34c041e0b071e00a1701c2c3e050c0040777870146b0101c2c0a602145c070b0f814cd1c81c1c160e0285c070b0f8144e471401c160e0283c160e028d614011e0a0160e0280416
|13=>0x385a001c050080e840b07014077f858380a0101c2c1c053f8041e5a858380a0101c2c657e82804070b194be930101c2c1c7e02804075a87014cd0101c2c1c053ec0e410b194380a0101c2c1c053e804070b07014f90101d6a160e028920707058380a03858380a7c32c22070b07014860101c2caf0518004070b07014f70101c1c1c050d804070b07014f60101d1016
|14=>0x543004070b070150b0101c380a3011c04070b070150a0105c2d094b02804070b072100a0105c2c960541c040707058cabd0101e0c160e0285c070b07014c40101c14602f8a404070b07015050101d10160e274040782058380a011e00e160e0280e410b070140203858380a8180a040e0b070140203a202c1c0500a02070b0701480038382c1c050080e0e100283a69
|15=>0x3858380a898080e0e10028520203b942c1c050080e0e0b0290ae7038382c1c050080e160e32126020383862650501c1c160e02a24020385a220a2f808f00707080140203838400a570080e0e0b1953a028801c2c1c050080e310e0c10a80038583820050080e310b1950a023c058380a090080e160e02a1e694481c2c1c050080e880b0290a0203c342c1c0501c2c1c
|16=>0xb07014250101c1c160e028ea020390c2c1c051a40e160e029800203858380a2fa4c040707058380a148080e160e27562440390c2c1c0501c820e0b07014077f8382c1c050080e160e02a2a020385814852d0080e160307052690b9402c1c0500a28070b070140203858380a4e8080e0e188290a0203afc380a300080e16578801407441042c1c051a40e50188701402
|17=>0x3858380a2f8a404070b07015170101c2c1c052148802038382c1c050080e160e028248e0101c1c160e02804070b438380a014582c1c051a4040707058380a0101c2c650e028d62e0101c2c1c05180040707058380a5e8080e310b194380a0101c2c1c0534c22070b07014c00101c380a768080e160e029060203858ca1c050080e165787014020385838c8050080e0e
|18=>0xb194380a0101d6a160e028040707058380a290080e5007058380a0101c1c160e028762e038587c0a0101c1c160e02904023381c2c1c0546404d803858380a0101c1c160e0293a02038c42c1c1d8080e163287014ca0101c62160e0290a110101c1c160e0280e160e02a240203858380a8c0080e160e02860c00101c2c1c10028520203858380a66b000e160e0282802
|19=>0xb81c2c1c05058380a6db1804070b07014bd0101c1c1632828041e0b0703a02038c634160e028d2023381c2c1c050080e0e0b07014c60101e34160e02804070710c2c1c050080ed00e028040718858ca1c0101da0160e02804160e2b9020256858380a0101c2c1c0530126023c01c2c1c050080e880b070140203858380a430080e0e0b07014b10101c2c3c1d8080e88
|20=>0x101ca0160e0291c0203858380a0101c1c160e02804070b07014290101c2c1c052b804070b07014930101c2c1c0507404070b07014c00101c2c1c050080e160e0298c0203858ca1c050083c070b07014023381c2c1c050080e160e029620203a201c160e0291c500b070140203858380a4e8080e500b194380a012240e160e028040772858380a3481ca0160e028d202
|21=>0x203858380a
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xf300c30093006300330003
|3,0=>0xfe40fa40f640f240ee40ea40e640e240de40da40d640d240ce40ca40c640c240be40ba40b640b240ae40aa40a640a2409e409a40964092408e408a40864082407e407a40764072406e406a40664062405e405a40564052404e404a40464042403e403a40364032402e402a40264022401e401a401640124
|4,0=>0x23d52385233522e52295224521f521a52155210520b5206520151fc51f751f251ed51e851e351de51d951d451cf51ca51c551c051bb51b651b151ac51a751a2519d51985193518e51895184517f517a51755170516b51665161515c51575152514d51485143513e51395134512f512a51255120511b51165111510c510751025
|4,1=>0x33c53375332532d53285323531e53195314530f530a5305530052fb52f652f152ec52e752e252dd52d852d352ce52c952c452bf52ba52b552b052ab52a652a1529c52975292528d52885283527e52795274526f526a52655260525b52565251524c524752425
|5,0=>0x4b364ad64a764a1649b6495648f64896483647d64776471646b6465645f64596453644d64476441643b6435642f64296423641d64185412640c6406640063fa63f463ee63e863e263dc63d663d063ca63c463be63b863b443ae63a863a2639d53976393438d63876381637b6375636f63696364535f53596353634d634763416
|5,1=>0x62c66266620661a6614660e6608660265fc65f665f065ea65e465de65d865d265cc65c665c065ba65b465ae65a865a2659c65966590658b5585657f65796573656d65676561655c55575551654b6545653f65396533652d65276521651b6515650f6509650364fd64f764f164eb64e564df64db44d564cf64c964c364bd64b94
|5,2=>0x7a767a1679b6795678f67896783677e57786772676c67666760675a6754674e67486742673c67366730672a6725571f67196713670d6707670166fb66f566f056ea66e466de66d866d266cc66c666c066ba66b466ae66a866a2669c66966690668a6684667e66795673666d66676661665b6655664f664a5644663e663866326
|5,3=>0x855684f68496843683d68376831682b6825681f68196813680d6807680167fb67f567ef67e967e367dd67d767d167cb67c567bf67b967b367ad6
|6,0=>0x9ea69e559de79d779d079ca69c379be59b869b269ad59a859a1799b6995698f69887983597c7976696f79687961795c5955794e79486941793b6934792d79267921591b6914790d7906790158fa78f468ee68e778e168da78d468cf58c878c178ba78b378ac78a668a0689b5895688f68896883687c7875786f68696862785b7
|6,1=>0xa2d6a267a215a1b6a147a0e6a086a0269fb79f659f06
|7,0=>0xa7a6a746a6e6a686a626a5c6a566a506a4b5a456a3f6a396a336
|8,0=>0xa805
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 283 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x5329039970e029073190b0710101e0b0710b0290e029038710b02b0383a0383b0b0710b02a0b0710382a03858070280b0710e0290e029280290101c038710b2be0382a471430101c0101d0e02a0b0700e0020b0054eac50702a0702b0f07703829038281702803871038380e0030b0710b00401075038280b0710b071280290b02903a220b1950b0280382a0b0280107503828038290b1960383a0e00003871
|1=>0x702a0b0710b858329af0385b0b0710b07101078038290b1950103a038710b0700101f0101e0b07103873038280e31903af7070281702803871038710b0700e075038280387103838471430101c0101d0b0290b028038730b0710f073038290b0710b07008859010290b0700b0720b02a0101c03871038710b071038284402b0b19568071038580101c01059038710e0290e3196807003828039940e02903873
|2=>0x52750702b0b07103af5070280b0710b071010780382903828038730b071038730b02a038710b1960b07101075038280b0710b0730b195038390b071183010b0280387307029070280e077038280b0290e02b0e0290b0710382a03829010290b028038580b0280101c0b0710101d0e077038280b3010e0292807103a22070290e029038290b0710b02a0e02903871038280f073038290b0710b0710382a0b071
|3=>0x38730e0770382833873038710e3190101e05301038730b0710b07103828038380b07101059038730e02a0382a0b0710702a0702b0114b0383b0b1960e0290b0700b0290382a0b196011490383b0b071038730b0710b0290e0290107703828038390382b0702b0b07144871280290101c0e0290107803829188730b029010390383a280290b1950b4390382a680730b19603a770702b070280731b0b0710101e
|4=>0xb0710702a0b0710b02b0b1950e0290b301038730383b0b0710101c0b071038580b07101072280710101c0702b0b0710b02a0e029039970e0290b1960e0290b0710107703828039970e0290b028038730b0700382a0b02b038730107a038290b0720382a0119e038710b1960e0290b0710383a0b0710b0710101d0e0a50382a01078038290b071038710385b0e029070280b0710b0290e0290f0730382901029
|5=>0x101c0101d0382a0382b0e02a03828038730101e0e02903829038710702a0b071070290b0710101c0101d0702b0b0710101c0e029280290101c0e24d0e02a038710101c01071038710101f0101e070280b0710b0710e02903829038280e02901059038710b0710101e039940e0290b0710b0290e0290e075038280382a0382b01075038280b02a03873038390b0710b1950e029
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>0x800000000000000000000000000000000000000000000000000000000000000000000000
|4,0=>0x9080000000000000000000000081000000000007880000000e100000001840a20000000000000000000000009100002040000000388000000052000000000000000000000000000000000000000000000000000002080c40000000000084000000
|4,1=>0x944000000000088c000211000080400000000000003e20000f08000366000000000000018300000002c415100000002820000000000000000000000000000000000000000000000000262000
|5,0=>0x2e99704b445912c09588aa254100000000005310001484a220000000000a024e20001308962000000000094200000000008e600022910c800000000010488020001e980000000000000e8c0003731b08d4400000019180006222f20000b8456600014189c44c2000
|5,1=>0x4b88000000000000250c00000000024892228f2469230400000045880000008a144100010e286142120c4000821408a0040000003f11f44f647a13c89dc8ec27420001cc400000000000000007123809bc4dc20003688000d646920001a040006533208000c62603
|5,2=>0x6813389984000658b285904000638b1840000006210001862c030000000000be25e880000000005d92e84000b735b0ad456820000000001662b2158880000000000002c04000ad30002b05562aa1541294d4640005090000000a014f100000009d14e0a6c5342982
|5,3=>0xeb20000001d24000000000000000000039c8000e610003944000e4100038c5c06df16e1b688000d916c0b589a66d21
|6,0=>0xac1558aaa3532a8953ca9c2000a61528a905462a21508a8053f19e94f067453829b14d08001331990cc465e52d29594a4a4e5261921488a4051e28e1468a3051628a144c62250f286942ca125072000414a0650127f93f49f640007c93dc9ec2f427913c09de2ed2
|6,1=>0x5b8ad856a2b41598ac85622b01578ab855a2
|7,0=>0x17a1bc88002f03771bb0dd46e82000b98dc86e23701
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x10841100370d0310c024088210801c060170581404c120441003c0d03009020060140400c0200400
|1=>0x400ff3dcde364d734cd2340b32709b2448f2348b22083204801dc741c46519061180551404711845
|2=>0xfafe3ec77fddf72d4f3ebfeefb62bb9463188201801fb7cdd373db05dd4f53547511435054048101
|3=>0xfdfef
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>0x800000000000000000000000000000000000000
|4,0=>0x40000004002001c000000060012000800000001000070100006000000004000000000000000000600001000012000002a000000200000180000c00013810000000000001000040002a00201000000000000000000200000000002100000004004
|5,0=>0xa0000000a461500080c50208000020129d0600b81050802302300005a040ac080c08300300152a027812a081807e0008e004423c5e0009206644156a35aac000002d000430000027a102049840000680000200020ec000007c3951a000142a7803282280001a0460800597008f3c600
|5,1=>0x100000800000a80000c00c006c0010004f025c0408102b618202b40803606880580401506540d000000014600000022401a02fca8000316010e0000000b002000306042c200800400018040000c020518d
|6,0=>0xc96ab171e5e0b14a33264d93daa6e863764e5cca66705aa5ac41cd4d1008d186a32e64a170798907b11f596e11630e52a9547a202b973ebae2f8193389b457641b0
|7,0=>0x48b60ebbd64e64deb8c9f2b
|8,0=>3
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_29,6,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 1 then [(dom_27,6,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 2 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 3 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 4 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 5 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 6 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 7 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 8 then [(dom_15,5,runOps true dom_15 (0,roots_15) ops)] else [])++(if pm.testBit 9 then [(dzo_15_16,5,runOps true dzo_15_16 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_7_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_29 6 s (0,roots_29) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_29_32 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 6 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 6 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 60 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 60 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 115 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 51 64=true)
private theorem z4:∀ i,0 ≤ i → i < 115 → Z 4 i=true:=(range_split z4_0 z4_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 221 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 29 192=true)
private theorem z5:∀ i,0 ≤ i → i < 221 → Z 5 i=true:=(range_split (range_split z5_0 z5_64) (range_split z5_128 z5_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 75 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 11 64=true)
private theorem z6:∀ i,0 ≤ i → i < 75 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 13 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 13 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_31 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_31 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31_32 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_31_32
theorem lowS_31_32:Lower true dom_31 roots_31 goal_31_32 9:=S_31_32.noCircuit
def dzo_46_1:=0xaaaa0000aaaa
def gzo_46_1_1:=0xaaa800008880
theorem lowSh_46_1_1:Lower true dzo_46_1 roots_46 gzo_46_1_1 5:=lower_iso (d1:=dom_46) (roots1:=roots_46) (T1:=goal_46_1) [(dom_46,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_1
def gzo_15_32_32:=0xeae800000000
theorem lowSh_15_32_32:Lower true dzo_15_32 roots_15 gzo_15_32_32 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_32) [(dom_15,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
namespace S_47_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,11),(3,35),(4,6),(5,7),(5,37),(9,11),(9,41),(10,11),(10,14),(12,14),(13,15),(13,45),(33,35),(33,37),(33,41),(34,35),(34,38),(36,37),(36,38),(40,41),(42,43),(42,46),(44,45),(44,46)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_47.map (· &&& dom_47)
def goalM:Nat:=goal_47_0 &&& dom_47
def NN:Nat → Nat
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|6,0=>0x3b576e79
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xffff00000000ff000000ff00f0f00000f0f0cccc0000ccccaaaa0000aaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x4688
|_=>0
def stOffB:Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 48 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 3 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 8 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 7),wireSAt ((code >>> 5) &&& 7))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf0
|_=>0
def pmB:Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_39,5,runOps true dom_39 (0,roots_39) ops)] else [])++(if pm.testBit 1 then [(dzo_46_1,5,runOps true dzo_46_1 (0,roots_46) ops)] else [])++(if pm.testBit 2 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 3 then [(dzo_15_32,5,runOps true dzo_15_32 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_47 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_39_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_32_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_39 5 s (0,roots_39) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_47 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_39_0 h
def ori (zs:List Nat):List Nat:=zs
theorem ori_ok {v ys} (h:RunD true dom_47 goalM v ys):RunD true dom_47 goalM v (ori ys):=h
def Z (s:Nat):=barP true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_47 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_47 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47_0 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_47_0
theorem lowS_47_0:Lower true dom_47 roots_47 goal_47_0 7:=S_47_0.noCircuit
def isoMv_30_1:List (Nat × Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_30_1:Lower true dom_30 roots_30 goal_30_1 4:=lower_iso isoMv_30_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_30_1:=0xaaaaaaaa
def gzo_30_1_1:=0xaa808880
theorem lowSh_30_1_1:Lower true dzo_30_1 roots_30 gzo_30_1_1 4:=lower_iso (d1:=dom_30) (roots1:=roots_30) (T1:=goal_30_1) [(dom_30,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
def gzo_23_8_8:=0xee00c800
theorem lowSh_23_8_8:Lower true dzo_23_8 roots_23 gzo_23_8_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_8) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def gzo_15_16_16:=0xeec00000
theorem lowSh_15_16_16:Lower true dzo_15_16 roots_15 gzo_15_16_16 4:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_16) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
namespace S_31_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,11),(4,6),(5,7),(9,11),(9,25),(10,11),(10,14),(10,26),(12,14),(13,15),(13,29),(17,25),(18,22),(18,26),(19,23),(19,27),(20,22),(21,23),(21,29),(24,25),(24,26),(28,29),(28,30)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_0 &&& dom_31
def NN:Nat → Nat
|3=>1
|4=>4
|5=>4
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x63fd312
|4,0=>0xb79599307b3a363b642830f2472e25f7
|5,0=>0xc20712038fd54a872c56ab271e29e5df
|6,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc0c0c0caaaa000033330000f2f2f2f2cccccccc777700004444444422222222ffffcccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f066666666
|_,_=>0
def stPool:Nat → Nat
|0=>0x321a432a4e321a4d321a4c321a5432ba421a4932187621543210
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>4
|4,0=>0x4d4e525445
|5,0=>0xa964679986
|6,0=>0x2f5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 15 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 10 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x1aa92
|_=>0
def opOffB:Nat → Nat → Nat
|5,0=>0x440040
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 6 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf5210
|_=>0
def pmB:Nat → Nat → Nat
|5,0=>0x68a
|6,0=>4
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 1 then [(dzo_30_1,4,runOps true dzo_30_1 (0,roots_30) ops)] else [])++(if pm.testBit 2 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 3 then [(dzo_15_16,4,runOps true dzo_15_16 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_27_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_30_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_16_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_27 5 s (0,roots_27) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_27_0 h
def symsG:List (List (Nat × Nat)):=[[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 4 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 4 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_31 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_31 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31_0 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_31_0
theorem lowS_31_0:Lower true dom_31 roots_31 goal_31_0 7:=S_31_0.noCircuit
theorem lowS_55_0:Lower true dom_55 roots_55 goal_55_0 6:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff000000ff0000,33,49)] (by decide +kernel) (by decide +kernel) lowS_39_0
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8_8:=0xfe00ea00ee00c800
theorem lowSh_55_8_8:Lower true dzo_55_8 roots_55 gzo_55_8_8 8:=lower_iso (d1:=dom_55) (roots1:=roots_55) (T1:=goal_55_8) [(dom_55,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55_8
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16_16:=0xfeea0000eec00000
theorem lowSh_47_16_16:Lower true dzo_47_16 roots_47 gzo_47_16_16 8:=lower_iso (d1:=dom_47) (roots1:=roots_47) (T1:=goal_47_16) [(dom_47,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_47_16
def dzo_62_1:=0xaaaaaaaaaaaaaaaa
def gzo_62_1_1:=0xaaaaaaa8aa808880
theorem lowSh_62_1_1:Lower true dzo_62_1 roots_62 gzo_62_1_1 7:=lower_iso (d1:=dom_62) (roots1:=roots_62) (T1:=goal_62_1) [(dom_62,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_62_1
def dzo_31_32:=0xffffffff00000000
def gzo_31_32_32:=0xfeeaeae800000000
theorem lowSh_31_32_32:Lower true dzo_31_32 roots_31 gzo_31_32_32 9:=lower_iso (d1:=dom_31) (roots1:=roots_31) (T1:=goal_31_32) [(dom_31,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_31_32
def dzo_54_1:=0xaa00aa00aa00aa
def gzo_54_1_1:=0xaa00a800800080
theorem lowSh_54_1_1:Lower true dzo_54_1 roots_54 gzo_54_1_1 5:=lower_iso (d1:=dom_54) (roots1:=roots_54) (T1:=goal_54_1) [(dom_54,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54_1
def dzo_30_32:=0x5555555500000000
def gzo_30_32_32:=0x5440404000000000
theorem lowSh_30_32_32:Lower true dzo_30_32 roots_30 gzo_30_32_32 5:=lower_iso (d1:=dom_30) (roots1:=roots_30) (T1:=goal_30_32) [(dom_30,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_32
def dzo_51_12:=0xf000f000f000f000
def gzo_51_12_12:=0xf000e000e000c000
theorem lowSh_51_12_12:Lower true dzo_51_12 roots_51 gzo_51_12_12 5:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_12) [(dom_51,12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_12
def dzo_46_16:=0x5555000055550000
def gzo_46_16_16:=0x5440000044400000
theorem lowSh_46_16_16:Lower true dzo_46_16 roots_46 gzo_46_16_16 5:=lower_iso (d1:=dom_46) (roots1:=roots_46) (T1:=goal_46_16) [(dom_46,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_16
namespace S_63_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,11),(3,35),(4,6),(5,7),(5,37),(9,11),(9,25),(9,41),(10,11),(10,14),(10,26),(12,14),(13,15),(13,29),(13,45),(17,25),(17,49),(18,22),(18,26),(19,23),(19,27),(19,51),(20,22),(21,23),(21,29),(21,53),(24,25),(24,26),(28,29),(28,30),(28,60),(33,35),(33,37),(33,41),(33,49),(34,35),(34,38),(36,37),(36,38),(40,41),(42,43),(42,46),(42,58),(44,45),(44,46),(44,60),(48,49),(50,51),(50,54),(50,58),(52,53),(52,54),(52,60),(56,57),(56,58),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffffffffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_63.map (· &&& dom_63)
def goalM:Nat:=goal_63_0 &&& dom_63
def NN:Nat → Nat
|5=>1
|6=>1
|7=>22
|8=>31
|9=>9
|10=>1
|_=>0
def HT:Nat → Nat → Nat
|5,0=>0x115fccb2
|6,0=>0x771ee677
|7,0=>0xd7ed68f4d6985041d55dfa25ce530f95cccc1527c77a3b44b04302eaac9ce1c1a6b9e07fa09ee23da04bfe0d935c64b3838a58b964119eef5ebfc50c5a69526637ca4906327f00522ce907c704e437fd0330b35302123af1
|8,0=>0xe8a202a5e1fa81cddfec8c63db7c6105d80bf947d7068044d24ac501c73f73a1c3827a75adcd0e94a3dc3944a30f43b09575de8b94eb139f9418d2ec915985fb87303edc81d2870375d4877f686021f65e7afffb595af484537f76e651cea8ce4897f058485e2aaa37410a9535a4da960ec4bc360a0f27a80630021d
|9,0=>0xc43bc065ba47a138b0bd880585cf5b438302b3d65a24f22f28f2496d212bd53217a485a0
|10,0=>0x69904ec9
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3300330033003300bbaabbaa000000002200220022002200f2f0f2f0f2f0f2f02222000022220000f2f2f0f0f2f2f0f00022222200222222ffccccccffccccccaa888888aa888888ff222222ff2222222222222222222222aa00ff00aa00ff005555000055550000eeccffcceeccffcc44cccccc44ccccccaa000000aa000000aa00aa00aa00aa00eecccccceeccccccbbbbaaaabbbbaaaa3333000033330000bbbbaaaa00000000ffffffff00000000ffaaaaaaffaaaaaaff000000ff000000ffeeeeeeccccccccf0f0f0f0f0f0f0f0ffff0000ffff0000ffaaaaaa00000000ff00ff00ff00ff00ccccccccccccccccaaaaaaaaaaaaaaaa0f0e0e0e0c0c0c0c
|0,1=>0xeeeecccceeeeccccdddd0000dddd0000ee00ee00ee00ee00eeeeeeeeeeeeeeeeeeee0000eeee0000ccff0000ccff0000cc00ff00cc00ff0055ff000055ff0000aaaa0000aaaa00005500ff005500ff00330000003300000088aa88aa88aa88aa110011001100110000aaaaaa00aaaaaa8888aaaa8888aaaaddddccccddddccccddccddccddccddccdd00dd00dd00dd00aaff0000aaff00005500550055005500eeffcccceeffcccc55ffffff000000003322222233222222eecceecceecceeccfaf0f0f0faf0f0f0faf0faf0faf0faf0bbaabbaabbaabbaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x1820592856031820572850c638204a1438630812850e20812852210811431827812850dc0812850da0812850c608164a14318205728558318204a1490c60952850c648204a14318144a14318e0451031820450c608b0451c40c60811440c2040
|1=>0x1431a30813ca14818204f2850c68c204a143182a012850c608d04a1490c60812850c6081b8a1431828012850c6081b4a14318206c2850c6ac204a1431aa0812850c608150a1431a90812850c698204a1491823c50c608194a143182064285603
|2=>0x7ca1432060812850c6e8204a14318205b2850c6e4204a1431b80812850c608174a14320608154a1580c60812850e10813ca1431b60812850e10812850c608140a1431b50812850c60b404a1431820732850c6081c4a1431820702850c6081bca
|3=>0xa14318204a1431820722850c6dc204a1431820672850c60814ca14318204f2850c608130a1431820552850c6081
|_=>0
def stOffB:Nat → Nat → Nat
|5,0=>6
|6,0=>0x67
|7,0=>0x12ee91645b211cf9074836b999cc0c5a62a3139890c4171d38cdc58e2570fb065826c0d6
|8,0=>0x5c5ed4f637ae3d55e9b14679fbce1e64d2b7923c75e2cf0f7843c05df30f2775bb91dbaed6767bb21d82eba759bab1d4ae9e7
|9,0=>0x1b07d4be89f36f947c6be19efef787
|10,0=>0x1b76
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 59 then fld (dictB (i / 512) (i / 32 % 16)) 64 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 6 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 13 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x1430a4314f0304242c80514308091431804202450c090453c0c1063d08f4304190453c0c1063d0c1050c2a0017d0c2c67508f830419b45540819806202450c60108091430855081850c201420614302510d3c507090c53c0c1024114f030428908051430a3404c450b1024a24201450c
|1=>0x81855708183dc081423e0c102061430809143063d0c105dc081463d0c1053c0c1057f0c2c333142c53f0c103cb141057c0c2c17f0c2c23d0c10304143023d0c1059f0c1c131142c805143017e0c2c17d0c2c8061430133142c24d141c29d0c1c34f141c35708182a1167c3072014304
|2=>0x14102050c1c5070c1050b081830b14302c91410554
|_=>0
def opOffB:Nat → Nat → Nat
|6,0=>4
|7,0=>0x4233f33c33933723433132e32b32832532231f31c31931631331030d30a3073043
|8,0=>0x8127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b2492472452
|9,0=>0x8b18a1891881871861851841831
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 14 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 63),wireSAt ((code >>> 8) &&& 63))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 12 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x403f8183fc08bfe042db020fd8105fc081fe0407b00c3f8027ec012f6008fb003bf801dec00e440067b003100015fc006f60035b0013d8007fc003f6001db000bf8005ec001fe000fb0003f80016c0000600000
|1=>0x61076e006b6842fb200bf8c01fc2c1fe1217f0907f8313fc10afe0817b
|_=>0
def pmB:Nat → Nat → Nat
|6,0=>1
|7,0=>0x19a5c63d11de9a4505290487818083556
|8,0=>0xa3a7a0584c94d8c7a6a9dd31965a1462461044ca2446e2
|9,0=>0xa2c424521f70c
|10,0=>2
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 6 (j % 128);fld (pmPalB (k / 32)) 21 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_59,9,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 1 then [(dom_61,8,runOps true dom_61 (0,roots_61) ops)] else [])++(if pm.testBit 2 then [(dom_62,6,runOps true dom_62 (0,roots_62) ops)] else [])++(if pm.testBit 3 then [(dzo_55_8,8,runOps true dzo_55_8 (0,roots_55) ops)] else [])++(if pm.testBit 4 then [(dzo_47_16,8,runOps true dzo_47_16 (0,roots_47) ops)] else [])++(if pm.testBit 5 then [(dzo_62_1,7,runOps true dzo_62_1 (0,roots_62) ops)] else [])++(if pm.testBit 6 then [(dzo_31_32,9,runOps true dzo_31_32 (0,roots_31) ops)] else [])++(if pm.testBit 7 then [(dom_39,5,runOps true dom_39 (0,roots_39) ops)] else [])++(if pm.testBit 8 then [(dom_47,7,runOps true dom_47 (0,roots_47) ops)] else [])++(if pm.testBit 9 then [(dzo_54_1,5,runOps true dzo_54_1 (0,roots_54) ops)] else [])++(if pm.testBit 10 then [(dzo_54_8,5,runOps true dzo_54_8 (0,roots_54) ops)] else [])++(if pm.testBit 11 then [(dom_31,7,runOps true dom_31 (0,roots_31) ops)] else [])++(if pm.testBit 12 then [(dzo_30_32,5,runOps true dzo_30_32 (0,roots_30) ops)] else [])++(if pm.testBit 13 then [(dzo_49_12,4,runOps true dzo_49_12 (0,roots_49) ops)] else [])++(if pm.testBit 14 then [(dom_55,6,runOps true dom_55 (0,roots_55) ops)] else [])++(if pm.testBit 15 then [(dzo_60_1,5,runOps true dzo_60_1 (0,roots_60) ops)] else [])++(if pm.testBit 16 then [(dzo_51_12,5,runOps true dzo_51_12 (0,roots_51) ops)] else [])++(if pm.testBit 17 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 18 then [(dzo_46_16,5,runOps true dzo_46_16 (0,roots_46) ops)] else [])++(if pm.testBit 19 then [(dzo_46_1,5,runOps true dzo_46_1 (0,roots_46) ops)] else [])++(if pm.testBit 20 then [(dzo_38_1,4,runOps true dzo_38_1 (0,roots_38) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_63 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_59_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_61_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_62_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_55_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_47_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_62_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_31_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_39_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_47_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_54_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_54_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_31_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_30_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_49_12_12 _ g hchk
    · exact cpcs (by decide +kernel) lowS_55_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_60_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_51_12_12 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_38_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_59 9 s (0,roots_59) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_63 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_59_0 h
def ori (zs:List Nat):List Nat:=zs
theorem ori_ok {v ys} (h:RunD true dom_63 goalM v ys):RunD true dom_63 goalM v (ori ys):=h
def Z (s:Nat):=barP true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 22 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 22 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 31 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 31 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9:∀ i,0 ≤ i → i < 9 → Z 9 i=true:=span_ok (by decide +kernel:span (Z 9) 9 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10:∀ i,0 ≤ i → i < 1 → Z 10 i=true:=span_ok (by decide +kernel:span (Z 10) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 10):∀ i < NN s,bar true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
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
  · exact z10 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_63 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 5=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 10) (h:RunD true dom_63 goalM s xsM):False:=by
  have hmin:5 ≤ s:=by have hl:=run_len h;change 6 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63_0 11:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_63_0
theorem lowS_63_0:Lower true dom_63 roots_63 goal_63_0 11:=S_63_0.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel

theorem signed_to_mono6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (wit : Circuit) (hwm : Monotone2 wit) (hws : wit.size ≤ lb + 1)
    (hwe : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = f x)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hT0 : T.testBit 0 = false)
    (hncT : ¬ IsConst dom_63 T)
    (hS : Lower true dom_63 roots_63 T lb) :
    ∀ s : ℕ, HasCircuitSize 6 f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  rintro s ⟨C, hfan, hsz, hev⟩
  by_cases hhas : ∃ g ∈ C.gates, isNotGate g = true
  · obtain ⟨g, hg, hgn⟩ := hhas
    have hsup0 : ∀ v ∈ roots_63, Avail true mask256 roots_63 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true C.gates roots_63 hfan (fun h => Bool.noConfusion h) 0 roots_63 roots_63 rfl hsup0
    set out := (execN C.gates roots_63).getD C.output 0
    have hout : out &&& dom_63 = T &&& dom_63 := by
      apply Nat.eq_of_testBit_eq; intro r
      rw [Nat.testBit_and, Nat.testBit_and]
      by_cases hlt : r < 64
      · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
        have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
        have h2 := congrArg (fun l => l.getD C.output false) h1
        rw [roots_63_bits ⟨r, hlt⟩] at h2
        have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false = out.testBit r := by
          simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
        rw [hgd] at h2
        exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
      · have hd : dom_63.testBit r = false := by
          apply Nat.testBit_lt_two_pow
          have h64 : dom_63 < 2 ^ 64 := by decide
          exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
        rw [hd, Bool.and_false, Bool.and_false]
    have hav_out : Avail true mask256 bank out := by
      by_cases hi : C.output < (execN C.gates roots_63).length
      · exact hsup _ (getD_mem hi)
      · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hd63 : dom_63 &&& mask256 = dom_63 := by decide
    have hm256 : mask256 &&& mask256 = mask256 := by decide
    have hm0 : mask256.testBit 0 = true := by decide
    have hR0 : roots_63.all (fun r => !r.testBit 0) = true := by decide
    have hout0 : out.testBit 0 = false := by
      have h0 := congrArg (fun v => v.testBit 0) hout
      have hd0 : dom_63.testBit 0 = true := dom_63_lt ⟨0, by omega⟩
      simp only [Nat.testBit_and, hd0, Bool.and_true, hT0] at h0
      exact h0
    have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
      rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
    have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by
      rcases hc with h0 | h1
      · exact Or.inl (houtm.symm.trans h0)
      · exact Or.inr (houtm.symm.trans h1))
    have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
      rcases hc with h0 | h1
      · exact Or.inl (by rw [h0]; simp)
      · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
    obtain ⟨s0, ws, hs0, _, hws_sub, hrun⟩ := reach_to_run hm256 hm0 hout0 hR0 hnc_256 hr hav_out
    have hws63 : ∀ w ∈ ws, Avail true dom_63 roots_63 w := fun w hw => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws_sub w hw)
      exact Or.inr (Or.inl ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩)
    obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach true dom_63 roots_63 0 roots_63 from rfl) hws63
    have hL := hS q next hq (avail_of_eq houtm hav_q)
    have hlt := countP_not_lt hg hgn
    have hsz' : C.gates.length ≤ s := hsz
    exact ⟨wit, hwm, le_trans hws (by omega), hwe⟩
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, by simp [isNotGate, h]⟩ hhas

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 16]⟩], 17⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_sz : wit.size ≤ 11 + 1 := by decide
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_63_0.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  signed_to_mono6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63_0 11 wit wit_mono wit_sz wit_ev hT6 (by decide) (by unfold IsConst; decide) lowS_63_0
end PEqualNP.Outside.L_meta_42158_aux
theorem PEqualNP.Outside.L_meta_42158 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4005611712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_42158_aux.main
