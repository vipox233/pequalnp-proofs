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
namespace PEqualNP.Outside.L_meta_41790_aux
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
def dom_11:=0xf0f
def roots_11:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0]
def dom_13:=0x3333
def roots_13:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_25:=0x3030303
def roots_25:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0]
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
def dom_57:=0x303030303030303
def roots_57:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_58:=0x505050505050505
def roots_58:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_59:=0xf0f0f0f0f0f0f0f
def roots_59:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_61:=0x3333333333333333
def roots_61:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_62:=0x5555555555555555
def roots_62:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_48:=0xe8
def goal_11_48:=0xe08
def goal_13_48:=0x3220
def goal_14_48:=0x5440
def goal_15_16:=0xeae0
def goal_15_32:=0xeac8
def goal_15_48:=0xfee8
def goal_22_40:=0x540040
def goal_23_8:=0xea00c8
def goal_23_32:=0xe800c8
def goal_23_40:=0xfe00ea
def goal_25_36:=0x3020200
def goal_27_32:=0xe080a08
def goal_27_36:=0xf0e0e0c
def goal_29_32:=0x32202200
def goal_30_32:=0x54404040
def goal_31_32:=0xfee8eac8
def goal_38_24:=0x5400000040
def goal_39_8:=0xea000000c8
def goal_39_24:=0xfe000000ea
def goal_41_18:=0x30200000200
def goal_42_1:=0x50400000400
def goal_43_0:=0xa0800000800
def goal_43_16:=0xe0800000a00
def goal_45_16:=0x322000002220
def goal_46_1:=0x554400004440
def goal_47_0:=0xeac80000c8c0
def goal_47_16:=0xfee80000eae0
def goal_49_12:=0x3000200020000
def goal_51_8:=0xe000a000a0008
def goal_51_12:=0xf000e000e000c
def goal_53_8:=0x32002200220000
def goal_54_8:=0x54004000400040
def goal_55_8:=0xfe00ea00ea00c8
def goal_57_2:=0x302020202000200
def goal_57_4:=0x302020002020000
def goal_58_1:=0x504050405000400
def goal_59_0:=0xe080a080a000800
def goal_61_0:=0x3220220022200000
def goal_61_2:=0x3332323232303230
def goal_62_0:=0x5440404040404040
def goal_62_1:=0x5554554455504440
def goal_63_0:=0xfee8eac8eae0c8c0
namespace S_51_8
def pairsG:List (Nat × Nat):=[(1,3),(1,17),(1,33),(2,3),(16,17),(18,19),(18,50),(32,33),(34,35),(34,50),(48,49),(48,50)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_51.map (· &&& dom_51)
def goalM:Nat:=goal_51_8 &&& dom_51
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x4bea8e87009cbb69
|3,0=>0xa35f290e9908a63a7316d6a0587818bd564b80b04536224829c5ac2a29a4607124088376216373de0100fcd0
|4,0=>0x54fde8fc4b5405dd2e5ade2929c5ac2a26366b081f979d7b18e398641767c918
|5,0=>0x29c5ac2a
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0000c0000000c0000f000c000f000ca000a00000000f000f000a0000300030000000000000000c000ce000e000e000e8000800080008f000f000f0000f000000000000e0000000e0000c000f000c000cc0000000f000040004000400042000200020002c000c000c000c00000000e000e40004000c000cf000f000000006000600060006f0000000f0000a000a000a000a30003000c000c
|_,_=>0
def stPool:Nat → Nat
|0=>0x411c2411c37208f609050384823849511c2411c29208e1a10470a262384419448283dcd3848c384825848238487504824a047098820948218820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xa8b3d652c6482af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 24 then fld (dictB (i / 512) (i / 32 % 16)) 52 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_51 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_51 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_51==dom_51) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_51 goalM v ys):RunD true dom_51 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_51 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_51 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_51 roots_51 goal_51_8 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_51_8
theorem lowS_51_8:Lower true dom_51 roots_51 goal_51_8 6:=S_51_8.noCircuit
namespace S_42_1
def pairsG:List (Nat × Nat):=[(2,10),(2,34),(8,10),(8,40),(32,34),(32,40)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_42.map (· &&& dom_42)
def goalM:Nat:=goal_42_1 &&& dom_42
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x47202343
|3,0=>0x47202343
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x141400000002800000028040400000404
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 43 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_42 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_42 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_42==dom_42) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_42 goalM v ys):RunD true dom_42 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_42 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_42 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_42 roots_42 goal_42_1 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_42_1
theorem lowS_42_1:Lower true dom_42 roots_42 goal_42_1 4:=S_42_1.noCircuit
def isoMv_25_36:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_25_36:Lower true dom_25 roots_25 goal_25_36 4:=lower_iso isoMv_25_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_25_4:=0x30303030
def gzo_25_36_4:=0x30202000
theorem lowSh_25_36_4:Lower true dzo_25_4 roots_25 gzo_25_36_4 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_36) [(dom_25,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_36
namespace S_29_32
def pairsG:List (Nat × Nat):=[(1,9),(5,13),(5,21),(8,9),(12,13),(12,28),(17,21),(17,25),(20,21),(20,28),(24,25),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_32 &&& dom_29
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
    (if pm.testBit 0 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_25_4 4 s (0,roots_25) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_25_36_4 h
def symsG:List (List (Nat × Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_32
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 5:=S_29_32.noCircuit
def isoMv_54_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_54_8:Lower true dom_54 roots_54 goal_54_8 5:=lower_iso isoMv_54_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_22_40:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_40
def isoMv_39_24:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_39_24:Lower true dom_39 roots_39 goal_39_24 5:=lower_iso isoMv_39_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def isoMv_38_24:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_38_24:Lower true dom_38 roots_38 goal_38_24 4:=lower_iso isoMv_38_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_49_12:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_49_12:Lower true dom_49 roots_49 goal_49_12 4:=lower_iso isoMv_49_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_7_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_7_48:Lower true dom_7 roots_7 goal_7_48 4:=lower_iso isoMv_7_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_7_16:=0xff0000
def gzo_7_48_16:=0xe80000
theorem lowSh_7_48_16:Lower true dzo_7_16 roots_7 gzo_7_48_16 4:=lower_iso (d1:=dom_7) (roots1:=roots_7) (T1:=goal_7_48) [(dom_7,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_48
namespace S_23_32
def pairsG:List (Nat × Nat):=[(1,3),(2,3),(2,6),(4,6),(5,7),(5,21),(17,19),(17,21),(18,19),(18,22),(20,21),(20,22)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_23.map (· &&& dom_23)
def goalM:Nat:=goal_23_32 &&& dom_23
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
    (if pm.testBit 0 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_23 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_7_16 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_23 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_7_48_16 h
def symsG:List (List (Nat × Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_23==dom_23) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_23 goalM v ys):RunD true dom_23 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_23 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_23 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_23 roots_23 goal_23_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_23_32
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=S_23_32.noCircuit
def isoMv_53_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_53_8:Lower true dom_53 roots_53 goal_53_8 5:=lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
namespace S_15_16
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(2,6),(3,7),(3,11),(4,5),(4,6),(8,9),(10,11),(10,14),(12,13),(12,14)]
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
def isoMv_39_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_39_8:Lower true dom_39 roots_39 goal_39_8 4:=lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def isoMv_51_12:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51_12:Lower true dom_51 roots_51 goal_51_12 5:=lower_iso isoMv_51_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def isoMv_23_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 4:=lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_39_16:=0xff000000ff0000
def gzo_39_24_16:=0xfe000000ea0000
theorem lowSh_39_24_16:Lower true dzo_39_16 roots_39 gzo_39_24_16 5:=lower_iso (d1:=dom_39) (roots1:=roots_39) (T1:=goal_39_24) [(dom_39,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_24
def dzo_38_16:=0x55000000550000
def gzo_38_24_16:=0x54000000400000
theorem lowSh_38_24_16:Lower true dzo_38_16 roots_38 gzo_38_24_16 4:=lower_iso (d1:=dom_38) (roots1:=roots_38) (T1:=goal_38_24) [(dom_38,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_38_24
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
def pairsG:List (Nat × Nat):=[(1,3),(1,17),(1,33),(2,3),(2,6),(4,6),(5,7),(5,21),(5,37),(16,17),(18,19),(18,22),(18,50),(20,21),(20,22),(20,52),(32,33),(34,35),(34,38),(34,50),(36,37),(36,38),(36,52),(48,49),(48,50),(48,52)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_55.map (· &&& dom_55)
def goalM:Nat:=goal_55_8 &&& dom_55
def NN:Nat → Nat
|2=>5
|3=>50
|4=>212
|5=>371
|6=>156
|7=>24
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xf88bcab5f1d796ba739645eb65370def1f724d16
|3,0=>0xecd3ba2ceca0bfa4dddd59cccb927da3c1d6afedbaa8a906b404f765b317cb6caacaf859a6122054a3ca27209a7a6a8999819ab0936eb8fb92afa6188a6f7d027cb926ba7a89da3b73b05f9c6bedb2336b0a02b16931166367363b7765a3f7e259d2fcbf459c07cf4546c3fa44c5b18d40a8ee94401257173efd9b1e3783b8192de2010e2d81f8cc2d4f7a062cfd287d1f7d988f1ef18b501c1fc6611661f45f135a1e9013085cd7124b987d1167c1ff114d3acc112b77180959af8503419f62025f20b90227a138
|4,0=>0x716ee0677155158a7096b87d6e7988866dc5501869b3c8f167e347646768fa6d671b41186668d9ed661c077f6544124964665047644c01d363afa33f623c5ba461db797a5f288d8d5d24b87a5d0bdb865c842bde5c6343d75b9dea1f5a17e93857946fe2553071455453de0e536d2afe5326aae25242b2d052370bb751df884f4f7ff5cc4d376ce94d25e0dd4ccbff884c86e70e4c03fcd64b0b7bf14af6fe644a308ab4497c32c347a4ad8a4476831643ff525643ce018542c29cc3424f6b884202c728416528e6412eb1603fc97be93cd804cc3c26c8d63bd43d603a62651138e7f2e238bcfe3d3872e0b636cf7fd034d2a9ed33d1828232c96c623243572e3210f99c2f2577ae2eb472a22cb8b8522c0092932bc9d21d2b23eeec2a72230027b3fb732795edac25c46cb125c09a4e256f93ee2526439324f3212e24c201da238a57762340a6b320f4685420a70f1e207bef03207bde1c1ea7c97e1dfdbcdc1dc0e0b01cd2e1131b1331711af21fc61aa682401a4f1e3219b1e3ce1951fa5a192848ce1788b8f9162cda8b15494a2b153acf1714863b6a13f31e3d13d06be413af4cab13a40f8313720c0212ce17cb1139f5361133a3cc1100129910262ea00ee49f660d6a83cc0cdf2f2e0c7d54560b17f9e80a930f4409fde6980853c553071e52fb05f363440548f31e01766cb401745acf01528bc9011ed795000fbc49
|4,1=>0xfcb34b42f94e4bbff8844fc8f8057f4cf7d0412bf1af9878f13280daf103f879f0cdc2a0ee7b703cecd3ba2cebec9947eb26da25e95cf97ce74f14dae698529de196ca21df65625adbabc5a1d896650fd631a64ad21be976d0602502cf6d76b3cedb659bce230cf2cae86773c991470dc97898b5c833077bc7d8277ec48fc107c3e4598fc1eb1ff9bf5732d5bb7fea6eb993e758b9531318b7fc6408b733f83db6960700b68e03c2b5b1a835b09b6ee3af078363abc3ee75aba68d29aa0c28c8a8734b95a43e7c5aa26b8d199f7f1e1e9ebd2eeb9d2df7a29b81245298061833952e5fac944f7586930071ea92c77812924cdeb79245d4b7916a2e698febd8648f2b93488d30b93e8c4efa538a3473a188d46013889f7fd685be7876851083958478e042830cc44581e5c3ea8061855d7f10ad477efce6d77e4c69b17e0e1c907cae83ef79d9ff34788c2e7476bdb548
|5,0=>0x346456b83420cbf633d56105334c5dcd32e3cd78329158173253456c32507548318fd84e3048cfa22da7c1af2d6dc12e2d19d73a2cdc473c2c3f0cd82afb782e2af926a1298579be2952666e28b8eb48273e51d0271b489626ddb89826c0978c26a89d02266d6b0f25919a8025911e77257b6f2a2503886124d09179248c042c2475d9f723fa891723aed07e22e9210c22afdb28229c95fc2271dc8622691b6322172930219cf3ae219bf63e21713cf220d976f920b10be22095f7cd209568981fc81ea61f1b3c561ea2845f1e7cf6c31e7b2b601e463aae1c937f9e1c289a1c1c240a571b5ed5371b34b1c01a31696119ddf34919a5e647192327d018ba295f18460d05175df24d16a3a4ae15d7d72f1589cdba1512a95614daaf6d1498f53b14302c0013ee1b6c13cabe6513c661121358686112fe5c9f12f972ef12e6df4a125836041251c2ff11ee96fc11d48a66119c1cdc1139f5361127d1d2104735d31022b21e0fb1fe780fa3ff2a0efa52cf0ee30fa10ebbc8470d261f890cd96ed20c8545670c21dbf30be1c94d0b70bf660b43b9f30aad28f50a9e75d50a53ab1a0a02db080964b6d70963a25b09530b86094859a6090ac9a808f01f90085cf66e07ee3e9307b681be079ae9f0076d45670763b48b0721632f068f0e0c061848770533099e0518e00904e3c95f014cd4d7012492b400f50720008e16b0004bd32f
|5,1=>0x743ab308742b5d227295703a7239191371fcb6ee704b57ba70187c1c6dfc4d306deec9496d9b601c6d5d4a9d6d25dd9b6ce102b26c86863f6c388c356b4e2e596ac225ec6a4dea6d699c178468b32052677d624e6698ef2865d2954065758648655f307664356fdf64030bcb63d1d804637d858d6350121c62f9aef761b2a37f60e5306960b0bfb9608f4c406076a95b601bc7b65fab894d5f15af545ee0d3b95e7367355e5add385e4140d95d91986e5c43e99d5acb33345a6a7453587a071b56ea332556e1a3af56599c9d55e3307255cbe2b4553b0f005529af8e54a5b2c654439a93542e23a1531052e152e72ce352abf21d517390325132b3be512e441a512da257511544f250f3509f50d43d7750c18218503af7694fffc6dd4fa8a1d74f7ff5cc4f17765d4e7fd8434dd315c54d80a9bb4d6c9e204ca19c624c8f461e4c17d9284c0c16b44b4ef5cf4b0862a74a1494c54a097fe54a0275e549f111df48078cf347f6ceff47cc50c346d37d7d46b727ec464205ba4605c573451aa2c143989aa143879ebe4325707a42c03b424201c361405fd1c240359fa23f9a17213f3dc53c3f35156d3f220d953ed37e613e9cac873cdc88653cb982853c9ff65a3c789c573c618acb3b7b395d3ab0557a3a06439239fff9a138be8a43378a706b3773fc14374f2ae436a611a0366f7fb9360b018935ffb1fc35eedc71348d3ddf
|5,2=>0xffbd6cdafe9154bbfbb2c816f20c7b2bf0cdc2a0ea003b16e82da1c3e816cfbae469504ae015b690df43e71ade83b2f0dc649f3ddc444255d7952373d75d6e16d5d31b7bd35ddeeed153b31bce808172ce73fb80cd865458cc095396cb7cb389c9af7278c8ec4700c84e57c9c55be272c36aa6c4c2436907bfd350d4bf862093bf413fccbde8d04fbb55384cb993e758b92f8601b67046f2b4ce5c24b456c7dcb34d92ffb2ea1914b1c30d46b0f6501aafbb20acae5009a5ae336223adffad69ad4b7bd1ac4647dbab88336baa8edb56aa75bd38a9a3edb4a865a70ba5b66b45a488ea04a47e61c9a420e469a40305d5a3e77a52a3176e09a170586ea060b677a05678dea022b60aa004e9df9e001ea99d2df7a29c0020a79b8768c79b43879d9ab2e18999e844ba9976a97a98d4a79b973ca9d796e0f4a1968f64de964cc94d96026e0f9586e7439296e0c99137b8fd90a8ace18fdcac138ca4a9c98b0b9d198b07f87c89f74d3089921da8885d643b87855b3b86c5d34b86a71034861a382a851e58bd83ad3f838123449180dbe8e57f8b47dd7dd2e1557d0490577cb261947c166f0c7b05602a7a4e56d27a42b52a7a1e3eb779ea78f9793d88c3777722507633e8d275c1120174bfe284
|6,0=>0xaae96690aa817e3aa4ff8acfa3f876e6a3626338a33974dfa01f03909cf02c9d9afeeeaf9aea8d45968f64de93bb1ec891e00a568f7554fa8df5cbbe8a42b5d38868d1ff863cd907844f9f5d8202ddc981af6859802b286e7f8b47dd7d7e93c77d4fb6c17cb261947c5c4f4c79630cd475c11201742b5d22727860797240ed1d713455817082d366704b57ba6eef87176e60e7b56dfc4d306c86863f6a707d4d6a6279476933765e68bfa94c68791c1667e3cb706560625b63f25c0d61e530cc5fd736de5f214d135e4c573e5a4275b259e2356d59ddc5c958676d6256438df551466125511544f2508ece464ba99e664339b9da42c499aa41e921ab40c7ba3f3de6f6463dad40b43d457f193cbf984d3c6dcde03b10d3b73b0003853abf377539fc54ee3968c4c038be8a43378cbae236284ab635c85379346456b833ca35c53135faf83091e62c2f5ee2712e91394b2c7c9cd62c05a2a62b43d1ba28bf54f0285f93d2267dc72e260cdc3224bc29b923419d7923415b6d23040d7b22afdb28225567f62217293021572d742125cf481ea2845f1db7ccad1d83bc4a1cdd36261bdf6c631bda94ab1af3d06e19ddf349176dd385174ef202162e383715c3810b1311a6fa13019fb010773ac51065ccb20ebbc8470e8112ae0d9247a00cd87b2c094859a60763b48b0728131f064e77b905c2aad8059b9297046f0bf60469dff1
|6,1=>0xfe24254af40b9d29f2afbcc5e9d907e1e9809f6be618545ade650322dc1578eed9a2c40ed70844bdd25ef427d0dfb02fc7011277c2436907c1bf7c36bf413fccbe7595d4be74fb79be576b4cbbced012ba2e0454ba154586b93c8a41b843944fb43689f7b2ea1914afbb20acadd0b0a7
|7,0=>0xe96d8581d1cd36f1bf98b147ba2e0454a96ded2ca5e2e6eba3f876e6963660d1928aab73869f6fdc704b57ba6f149ea96e21827567d0cec264ee17b544608fe23cfb43bc326207382485f87923419d7910710c500ed4e76f0322b61c003c1023
|8,0=>0xa5e2e6eb
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xee00ee00ee00ee300030003000300c000c000c000ccc00ff00ff00cc0000cc00cc00cc0300ff00ff000033003300cc00cc3000f000c000f00f000c000c000cff00ff00aa00aaea00ea00c000c0700050007000503300cc003300ccff00ea00c000c0ff00aa00000000ff00cc00ee00ccfc00f000f800f0fc00fc00fc00fcc000c000c000c05500aa005500aaff00ff00000000140014003c003cf000f000f000f0cc0033003300ccaa00aa00aa00aaff000000ff000055005500aa00aa3c003c003c003cfa00ea00ea00eafa00ea00ea00facc00cc00cc00cc0000ff00ff0000
|0,1=>0xee00ee00000000cc00cf00cf00ccff00ff00ff0000fe00aa00aa00aafa00fa00fa00fa11001100ee00ee3f003f00000000f000c000c000f00000ff0000000000000000ff0000f000f300f300f0ff003300ff00cc33000000cc0000f000c000c000c0cc000000ff000000003300cc00ccc000ff00ff00c0fa00ea00fa00eafa00c800c800c8550000005500000000aa000000aa3300cc006600cc0000ff000000aaaa00aa00000000ff00aa00ff0000fe00fe00aa00aaee000000ee00000000cc00cc0000ee00aa00aa00aa15002a0015002aff000000000000fa00c800fa00c8
|0,2=>0x330000002200000000cc004400ccff00ab00ff00003300000033000000003300000000aa000000aa0000100030001000300e000c000e000cfe00cc00cc00ccf000f000c000c0cc00cc000000000000ff000000cc11001100000000fe000000aa0000330033000000000000ff00cc00cc3300cc0000000000000000aa00aa0f000e000c000cf000c000f000f0ea00ea00ea00ea00003f003f0000ff000000ee0000cc003300ff000000000000cc00cccc0000000000cc00003300330000cc00c000c000ccff00aa00aa00aacc000000330000000033000000ccff000000aa0000
|0,3=>0xff00aaee00aa0000000050005000500050cc000000cc0000fc00f800f800f8fa000000fa0000f000e000e000e0ff00ee00cc00ccff00aa00ff00aaf000ff00000000fc00f800f000f0ff00cc00ff00ccee00aa00ee00aaff00cc00000000cc00ff00cc00cc66006600660066bb00aa00aa00aafa00fa00ea00fafc000000fc0000ee00cc00ee00ccee00ee00cc00cc1f001f00000000ff00ff00cc00cc0d000c000c000c0f003f000c000cff00030000000000004400cc00ccff00cc00cc00cc03000000ff000055005500000000cc00ff0000000088008800aa00aa
|0,4=>0xff00f000f000f08800cc00cc00ccf000c000f000c0bb00aa00bb00aa30007000f000f0ea00c000ea00c0d000c000c000c05000400040004033003300330000fc00fc00a800a8fc000000fc00fcf000ff00ff00f00000fc00fc00fc11001100440044330022003300223f002a003f002a0f000e000e000ecc008800000000ff000000aa00aa9900990088008800000000fc00fc33000000000000ff00c000ff00c0f000f000e000e0fc0000000000000000cc000000cc00000000330000fa00fa00000000cc003300000000c000ff00c000c010005000500050cc00aa00cc00aa
|0,5=>0xf000f0000fe00fc00fe00fce000c000e000c0cc008800880088ff00fa00f000f0f000a0000000001100cc001100cc0200aa00aa00aacc00c800c800c833002200220022bb00bb00ee00eeaf00ae00ae00ae05000400040004ff003300000000aa00fe00aa00feff00aa00330000f300f3000000003300ff000000003300ff00cc00cc22000000220000ff003300ff0000f000c000e000c0fe00f000f000f0ff00ff00ee00ee54005400fc00fcff00ff00aa00000000fc000000fc54000000ff0000bb00bb00cc00ccff00f300ff0000fe000000fe0000af008c00af008c
|0,6=>0xf000ff00f0ff000c00ff000c0c000000ff000000000000ff00ccbb00bb00aa00aafe00fe00fc00fc0f0000000f0000fa00aa00ff00aa55000000440000ee00aa00ff00aa0f000f000c000c44000000440000ff00ff000c000cf0004000400040ff00ee00ee00ee33003200320032dc005000500050ff003300330000cc00cc00ff00cc3f0000003f00000000ee00ee00eef300f300f300005000500051005054005000500050ae00ae000c000cff00ee00aa00aa3000700070007000000000ee00ee1f003f000000001000f000f000f0fa00aa00aa00aaaf008c008c008c
|0,7=>0x3300ff00330000fc00f000f000f00c000c00ff000c5500ff000000000000f0000000f051000000510000880088008800884400ff00000000fb00fb00aa00aacc000000ee00aafc00fc00000000cc00000088000033000000ff000054005400000000af00aa00af00aa88008800cc00ccff000000330000f0000000ff00000000fa00fa00faf3000000f3000044004400440044440055000000000300ff00000000bb00bb00000000ff0000000c00000f000a0000000033003300220022f0000000f50000ff00ff00330000f000f000000000f300f300a200a2ee00ee00aa00aa
|0,8=>0xee00ff000000001100ff00000000af000000aa000005000500000000aa00ff00000000ff00ff00fc000054005400540054ab000000ab0000220022002200220f000f000000000000550000000077000000770000ae00ae00ae00aeae000000ae0000f000a000ff00aa3300000077000033002200ff00aacc008800ff00aabb00ff00aa00aaf000f0005000500c00ae000c00aef0000000f000003000f000f000f0bb000000bb00000000fc00000000ff000000cc00000500ff00000000f30000000000001000100030003000000000f30000cc00cc00ff000011000000110000
|0,9=>0x55005000500050ff004400440044dd00cc00cc00cccc000000000000f500f000f000f0cc00cc00aa00aaee00000000000050005500000000ff000f00ff0000ff00ae00ff00ae00004400440044aa00ee00ee00ee00000000f000f033002200000000e000e000c000c011000000000000550000000000002200aa00aa00aaff00f000fa00f0fc005400fc005455004400440044ff000000f00000ff00fa00aa00aa0e000e000c000cfa000000000000aa00aa00fe00fef000f300f000f0000054000000540f000000000000af00aa00aa00aa55000400550004ff00ee00ff00ee
|0,10=>0xa800a800a800a80f000f000f0000f200f200f200f2cc008800cc0088cc00cc00cc0000fa00fa00f000f0700070007000705000f0005000f0cc00cc00ee00ee55000000ff0000ff008800ff00880f000a000f000aa200a200a200a2f000ff00f000f0cc000000cc00cc440044000000000f000c000f000cff000000ff00cc5500500055005044004400cc00cccc00cc00440044ff00ff00f000f0f000f000fa00faff00f000ff00f0fa00f000fa00f0fc00fc00fc0000bb000000000000ff000c000c000c0f000a000a000acc000000dd0000f0005000f00050ff00fa00fa00fa
|0,11=>0xa000a000a000af800f800f800f8d000d000d000d0
|_,_=>0
def stPool:Nat → Nat
|0=>0x24620718024022f0381c3c1d0002c5c250082c0c2d0f82c58041582c1207150381a070002c0e04148580c280209c4c090082c401f1282438071202c20091182c12011102c42200f82c181e0e82438070d82402070d0180e190c0040e17000580c0e0a82c0e14098480c0e038440c070202c200f0382c1c0d0602c0c07050241007038100006028100601000080200
|1=>0xc82c12070993c1606038109c0b030040e4d059300231038240207001141627070340e0b0308406010487002070002c0c0300824960100024020725124763f008249007238248c072282488070002c4e070202c8620008f4420300824840720900763f008247c07000f478090081876011d024020c1c8440c03008e002070001c08371b0d40207000d01207198c80207
|2=>0x21818121f0581802073402c0c010399c7a66048040e110481cb86532018123f038240207318dc0c620f0749c0b04804900720024c201038181207300640c090081c740b0481cbe5e0597412010384412010397012310396c8e0b0301cb25805818ae3b03818ac55039500c0903864a60b290240207058381201060181207289400c09008143a43030247e01030240e2c
|3=>0x9f018060481c323705818f6010382c867a0480416063c8040e78088240e5c058181e01039dc12012d0e48076048040e11031d402070b02ce809399a40c211d87c16720481c260b03024967105818127029818ac070c82c0c3b009bc0c09008340a16058240e130498402310382c0c6e0081c166d049b00e0b1381c3c1d03024d60735018ac0103940d2061d87c7e69
|4=>0x4902c0c3b0fa44160900969200b030040e8f3c018128e03a3412010397016060487d1806049ac0e8b058240e134502d12093881c0c881f8040e0b04804181e1ea1c12010382c120709a142c0642004fa0b03024d64b0582506070982c42200081c12014101c6c0b0308c0281058240280160181c0d039fc227a048040e1603024fc010581cfa132e1e00c092a81c1609
|5=>0x4e8940207058185a010382c0c09362701606048fce011030040e9b03158c2010382c8009398042206070340e0b3b8253401218187684008184209038647a210081c2e060481ca25e0b018763f0082c0c990081c16060488c020b030040e983208412074b82c0c960681c92091f8040e06038783a7f058192a0d03a501201038001c090081c003d048040e93030240e19
|6=>0x48040e4505824025506084121c0081c0c095181c16094e01c26a8030ec7e01048040e1e0010076010394416060681d4ea6048040ea5088180e1e0e82c120103a90124b008dc6c060481c325404804f8070001812a3039454421048040e43030ec0251030240e513282c0c07020dc420903a5c360b50824d8070581cfa130588402a003a7c1201038000c0903a78a20b
|7=>0x2886c160900ac45616030a03c1d048041a07001a40c091f81d6011048040e0b320180601088180207269015e090081c160e068b0560b0315c12072002402075710002073e9440c0903ab4a20b0481c26ac531b41201038184c09008a0160912805380b030040e81048040e1d002ac0c09038642c06070345034030240e19048048c070002c80aa0081c1606548040e21
|8=>0x5818020762818760129b102c0b0301c0806049b00ec33202402070002c0c0103b0816061db04020b030058007048040e005f8381a071b8d816065f2f40e0b030243ebc1082402074baec0cba0081c16091281d720b0302402b8059900c3b0f82c0c095b81c16061d8056c69218187601030256a070c82c0c015a01c16060081d663d108c80207591001201038180e7d
|9=>0x38a0b80b030040e7d0d82c0cd20081c16d1030ec02090081c00240581812076804412014001c1606678040ece108240207058259a076602c0c320081c16061e024020b0300c020b030ec02cb0581806010388594090081c16060081d920b0308c027d048040e000d8440c09118040e1e0e8dc6c0b030040ec8058198e070f02d8c061d8040c0903864820b049840e13
|10=>0x30240207459380c3b0081ca23632018420903944160604805b60705818121f00b6c16066d024d60705819b0090081c1643048040e5c05818120103b5c166d048040e2b0581812d60081c16060081cfa5c34818420103b540c09038b0a24705818126c038781606048058e070581842320081c0c0e04804c44e349c80c090081c16740481da8d30302402071b0841201
|11=>0xb02c0c09398041606048040e5f0882402072e02c0c096681c3c0b033841201039a40c097001c160900954582b05818120103b7c16776f0240207030855e090081d6406048040e060481ca21b0308402073e9441606048040edd03024020728b7016090081d98360589c1c090081c16060081cfa53048040e1d1b8d80c0900980c4511e99042090081c1640048040e5c
|12=>0x1881ca216058181c0d0382ce821049f00e0b0302402077502c0c090081dd20b03005d0073e8181201038a1160b0339c12010382c0c093601c3a0b0327402072882c0c090081dcc0b0480462072e02c0c3b0081dca0b0321002073e82c0c0970004566903158aa07058847601039701609008c40e2c048040e622e0dc160604b9002077182c12072e218220604b880207
|13=>0x7b01c1606048040ef303210120103988160604805382c0308412072886c7a067a82402070590012017a01c12010681c6e36058184c090081c16090081de63705818120103bc8160604805e2070590c0c3b04804d206049540e37048040e00030240ef02882dde090081cb80b04bb802071602c0c3b0081dda0b7602402071b82cc8060481dd60b030240207450841201
|14=>0x58181273009680c0903864a20b0302402820382c0c3b0081e000b030ec3e018002c120103bfcb80b033f8020705818120103bf40c0e048040efc05824023103bec16061d9840207058240207528d81606048040efa05818121f7c94c0c0900ba00e6205818120103be0161020024020705818120748878160604b80020705819ee090081c7a21048040e1b058181201
|15=>0x668340e0b5d81812010382c0c090081e0a0604804c41e27018120103988a20b3b8244a010382c423b3d0040e0b034101201038581606038783a21048040e00058240280039701606049ac0f033490c0c090081c2c061d8040e510581802073eb941606048040f0205818763f0081c16061d87c7e010590c0c090f8041606049b01a0705824c2072e218160604c040207
|16=>0x8681c1609770040e37058441201039701606308040e7d030240e191e818120103a2c12012a81c6e360581a18012a81c1606048040f0b34818423b0081c1609850940207030381201039fc16060081e120b6f01802073e82cee0900c200e0b0302402078382c0c09008c40e0b32018121f0382c0d061d8040e0b03084761f0082c0c090081d6c0b0480462071b82c0c09
|17=>0x57824020705818120103bfdc606048040e510589c1201038742c06048040eae0b01802073e944160604806240705900120103978160604c44020705818120d03a4416061f8040e7d05818120103c40ee090081cb87f3481a0c092a81c1664030040e1705818120103c3c0c09009883a4e05900120103b64166d048040e360581802073ea2c1606048061c07058181201
|18=>0x81cfb1c05818127005824031b0397042090081ca25c718841201039701606830040e7d059900c090081e340b03024020705818ec01039f416060487ce00b03024031803818123f0081ca60b030243e070d82c0c09118040c090081ca6c40581812016dc5c16060488c02070302402078b1fc0c21048040e500b10012010394416090081cb9150582402078a1702c06
|19=>0x7282c0c090081e420b900244a010382c0c098f8040e69058193a010382c0c090081e3c0b0313002070581812014e4001609008b0a22b0581812014701c1606048063a07058192c090081c1606048050007348184201039f42c0b3a024f80705818e601039f40c090081df81e058192a090081c0c091f8040e621082402072e0dc1606070340e4e05b180c090081c1606
|20=>0x960240207059d0429d0081c1606048040f2b05ca40c090081c2c060480450d905818126b03ca00c2104805d0070581877270081c16640303812070302402077e0741606048064c070581a4a010382ce809008c40e0b0480462072d8184284048040e110303812010382c0c09258046e0b0302402079202c0c0900c880e6903024aa072a02c0c090f8fdf20b030240eeb
|21=>0x3cbca2064202402071b01812012a9889c21048040e511581842090081ca216058040ed97d82c0c09358fc0e0b0302402072982ccc06048040e69030240e190581812019702c0c090081cb80b5101812010382c1201039706e0b0301c3c1d2734c1606710040e0b9690012010382c0c09038641606048040ecb0581812710081cd206048040e50030247e01039441606
|22=>0x590012013e01c1610030240207058181273008b0d206108240eeb0b018120131145c621048040e0b030ec02db0382c0c0935cc40e0b030040e7d6a02c0c090081e600b3682402072d02c0c090081d4e0b0302402e80382dbc090081c580b030243e077282c0c84048040e0604805d0071b018120103874fe06048040e391b02da206048040e06048041a077e0181201
|23=>0x381812010282c0c090081dda69030247e07059900c320081c16743e01cfa69030243e3f039a442090081cb80b030040e170302402db311441606048040f3505818760103a28160643824020705818120103b94160607024d60703084123f0081c1706048040e5c0581812019a01cd206108240e51030247e0103ccc2c0607024022808818120103cc87a21070240207
|24=>0x48fc0207058181201039781606108040e170581813390081c167704bb80207030247e01038d81643030ec023d10824027c0382c0c090081e700b9b88412010382e6c06048040e6903084121f0382c0c090081d26110302402077302cee09008c40e0b3201812070e82c0c0900b6c503d4f88412010382c0c09009bc0e0b03005b6073e8440c090081c3a16032101201
|25=>0x1b0180207311f4a23d1082402070e82dbc21048040e0b0300678073e82c0d3b048040e690302402079782c0c090081d2e0b21818423b008580c09008a03c690308412010382c0c090081d3c0b4482402071b084120103a5c16060081cfaf30b01812019d01cd206048fc0207058181c0d038dc16061d8040f050b0181201039440c3b0081cc4510581802073ea281606
|26=>0x48068a07048040e1e1b8d81606650240207058186401039a4e821048040e0b3201802073e82c0d27048040e1603024020d1402e8806048040e0b030240207a182c0c0900d080e0b0350402550382e8006048040e0b0302402079f82ce8093e01cc40b9f01812010382c0c0900af00e0b030267a01038580c09008a03a0b320187601038195e090081cc40e048040e37
|27=>0x81c160604804aa073102c0d49048040e0b03024020d038ac1606048040e850581812010681c6e06048040e7f0b02e9006048040eb203024020705818767a0081c160604804aa071602c0c3b0081ca20b0302402db0382c0c01039f4b80b031b41201038f4160604804aa070581a8e090081c160610824027c0382ce8093e01da60b0302402070581a8c090081c1606
|28=>0x2e218174e03024020705818120103d3416060481e980b0308412010387416061d8040e16058181c090081c16061d87c020b03025c0010382c0c09008c40e5105818120103bcc16061d87c02070581812014e01cb80b0302402f10382c0c01039f5d60b033b0120103a980c090081c160604804f8071b02c0d2a048040e0b03024034b0382c0c090081d154a058184209
|29=>0x302402078b02d6406048040e0b030240207a982c0c1f0081cfa0b0302402070e8d816060702402072d02c0d52048040e0ba702402070581812011881c1606108ec0207058181201a881c2206048040e06048040e622882c0c09009540e2b0581812019e01c1606048040f50058180207a782c0c40048040e0b2181812010382c0c090081c3c36058193a010382c1207
|30=>0x38580c09008a02c0b0302402070e9a41606049540e3d108240207058181c090081c9c0b03024027c039681606048040e512e38c1606048040e5c05818120103d5016060487df20b0308402073e82cc806048040e0b0302402076e02cee0604804f80705818120103988b8160581812013e01c160604bb802070590c0c21048040e0b03504020705818120103d301677
|31=>0x356802070581908090081c1606048040e626c82c0c090081cb41d030841201039441606048040e53058180207ac82c0c090f8040e5305824022c1582c0c0103d601606048040e5c0581812012a81c6c0b030243e010397016090081cb8370581812710081c160604d5c020705818126b0382c0c090081c360b048040f560581876018b82eaa090081c1664030841201
|32=>0x39a41606048040e5c0581a92010382402071b8d81606048040e1d2702c0c0e048040e2c0581842090081dd60b030240207728f4160607024020705d200c090081cc4e30581812010382c0c090081c3c4e0581812013e01c500b03004f8073e82c0c0900d700e0b9b81812010382c0c09358040e0b048040f14058181201ad81c160604805d0070581842090081c360b
|33=>0x30240255039381606048040f5e05818120103a5c2c0b0302402072e1a40c21048040e0b0302402078c82c0c0e048040e3705818120103cbc1606048040f1c0581842090081c16068302402070581812018981c1606108243e010382c0c0975c5c2c06048040e5105818123f0081c16060487c7e010382c0c090081d160b0308476090081c1606ae8040e0b030243e01
|34=>0x302402074302c0c09009540e0b030040e7d058181201039381606048040f620581876010382c0c090081c3a0b0302402072d5281606048040e0b3b81812010382d3e0610824020705818120103c8cd20b3a01812010382d3e06048040e0ba40181201038d816061083812010382c0d610081c1606b00040e0b030240207160741606048040f5f1e82c0c090081c3a0b
|35=>0xb03024020705818120103c5c1606070240207059d00c090081c160610824020705818120103b641606048040e0b030243e010382c0c3b048040e0b0302402071b82c0c090081dd60b0302402072e02c0c090081c580b0302402077c8f41606048040e0b
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xc300498018c00660003
|3,0=>0x1a680cf4065a031d018680bf405da02dd016680af4055a029d0146809f404da025d0126808f4045a021d0106807f403da01dd00e6806f4035a019d00c6805f402da015d00a6804f4025a011d0086803f401da00dd0066802f4015a009d0046801f400da005d0026800f4
|4,0=>0x108a8831440ea20250fea87e143e6a1ee50f4a879143bea1da50eaa87414396a1c650e0a86f1436ea1b340d7286a54348a19f50cd286554320a18b50c32860542f8a17750b9285b542d0a16350af2856542a8a14f50a5285154280a13b509b284c54258a1275091284754230a1135087284254208a0ff507d283d541e0a0eb50732838541b8a0d75
|4,1=>0x1a828d2d468ca341519e28cdd4664a32d519428c8d463ca319518a28c410616a3065180a8bf145eea2f25176a8ba145c6a2de516ca8b51459ea2ca5162a8b014576a2b65158a8ab1454ea2a2514ea8a614526a28e5144a8a1144fea27a513aa89c144d6a2665130a897144aea2525126a89214486a23e511ca88d1445ea22a5112a88814436a2165
|4,2=>0x247a9229490aa480523da91d948e2a46c5233a918948baa4585229a91394892a444521fa90e9486aa4305215a90994842a41c520ba9049481aa4085201a8ff947f2a3f451f7a8fa947caa3e051eda8f5947a2a3cc51e3a8f09477aa3b851d9a8eb94752a3a451cfa8e69472aa39051c5a8e194702a37c51bba8dc946dc836951b228d7d46b4a3555
|4,3=>0x279293b549d0a4e3526f2936549a8a4cf526529315498284bc525ba92c9495aa4a85251a92794932a4945
|5,0=>0x335b19958cbec6596329b19358c8ec641631db18d58c5ec6296312298798c30c6126306318198c00c5fa62fa317bd4bd2c5e362ef297618ba4c5cc62e3317054b78a5b662d8316a98b48c59e62cc316498b18c58662c0315e98ae8c56e62b4315898ab8c55662a8315298a88c53e629c314c98a58c5266290314698a28c50e6284a940d89fac4f76
|5,1=>0x3f2b1f7d8fb2c7d363e6b1f214f84c7bc63db31ec18f54c7a463cf31e618f24c78c63c331e018ef4c77553b7b1da58ec6c75d63ac29d498e98c74663a031ce98e68c72e639431c898e38c716638831c298e08c6fe637c31bc98dd8c6e6637031b698da8c6ce636431b098d78c6b6635831ab10d4ea6a1634db1a558d1ec6896341b19f58ceec6716
|5,2=>0x4b03256992a8c94e64a4aa50d927ac93764992a4b1924cc920648d32451921cc9086481323f191ecc8f064753239191bcc8d8646932331918cc8c0645d322d1915cc8a8645132271912cc89064453221190fcc8786439321b190d08862642e3215990a0c84a6422320f99072a8336416b209d9042c81b640ab203d9012c80363feb1fdd8fe2c7eb6
|5,3=>0x56cb2b4d959acac85561aaaf5956ecab16555b2a95953eca9a554a32a399510ca82653e329d994e0ca6a65323297994b0ca526526329199480ca3b551ab28bd9452ca23650eb285d9422ca0b6502b27fd93f2c9f364f6b279d93c2c9dc54eb327419394c9c464df326e19364c9ac64d3326819334c99464c7326219304c97c64bc225c992d8c9666
|5,4=>0x629b3135988ecc41661db30d5985ecc296611b3075982ecc116605b301597fecbfb45fab2fc157d4cbe555efb2f6597a8abce65e432f099778cbb665d832ea99748cb9e65cc32e499718cb8665c032de996e8cb6e65b432d8996baab5765a8b2d2d968acb3f659cb2ccd965acb276590b2c6d962acb0f6584b2c0d95facaf76578b2bad95cacadf6
|5,5=>0x36099af8cd7666b8335ad5acacd5f66acb354d9a9acd4766a0b34ed9a6acd2f6694b348d9a3acd176688b342d9a0accff667cb33cd99dacce76670b336d99aacccf6664b330d997accb766592b2b1994ccca0664d33251991ccc886641331f198eccc7066353319198bccc595
|6,0=>0x7842bc099df6eef56777b3ba59dc4eedb776ab3b415d94cec4675f33ae55d66ceac775333a819d36ae956747b3a21dd06ae7e573c339c99cdaae667730ab969dcaaae4f67243b9099c78ce357717b38a59c46ce1e570bbb8459c16ce0566ff3b7dddbe2cdea76f233775dbb0add176e62b7199b7eedb966d9b36b59b4ecda076cd3364ddb1cad886
|6,1=>0x848b4229e10ab07f683c3c1cd60dcb06778303c165e0a6d04c7822bc0fda070f0317815b4095a03ed019680a2c039a010d00177fe2bfd99fdeefe877f133f719faeafd077e5abf195f80cfb977d93beb19f4ccfa067cdabe559f20af8b57c32bdfddef4af7377b6b3da15ec2ef5a77a9bbd31de8ccf41579db3cd59e5ecf287790bbc69de28cf0d7
|6,2=>0x8a03c4e9a266f12d68933c47de234b11558873c421a202f0fa787a343b9a1cef0e1686db4351e19cd0c86861342f1a16cd0af78552c291a13cd0977
|7,0=>0x8e734721a384d1bc68db346c56356d1a568cfb4665a326d18d68c3b4605a2f6d17568b82c5a9a2c8d15f58acb454da29ad1476
|8,0=>0x11d45
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 355 then fld (dictB (i / 512) (i / 32 % 16)) 56 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x301c1e8870581805819009690301c059dc0301d1081d0481d03004048042e21903006030071e88705818058190300400801008b00301f0b018030070481d1081d0301d0301c1081d0481d0307c1e88705818058191e8870581805819030040301d0301c0307f2e2190300603007030670301d0301c0081d0481d0300404804058050081d1081d039470307f009690301c160ad0301e0301f030060b0180307c
|1=>0x5818059730301d059b70481f0581c009690301c05807059733b807030ec0301e0300403004030070581805807059dc0301d0301d030070b018030070581a03004030040581d04806058180480605971058180481f3481b0581a048050581b0581a10805030070581e0581803971049ad05b67030070301e05973030070300503006009690301c2d075048060301c059d0058050301f0581a048061080610806
|2=>0x481d0307c0081d108040581803075033af1080505818059730581a059dc0301d0301d030070307c030ec0581810877058181e88705818058191081d03005030076981a0307c0307c009690301c0581c030040581a058180596b0301c0307f0581f033af088053b8070301d0307c108060581f030ec0300708804048043681d048050301f1081d058181e8870581805819030070301f0581805b670581f108ee
|3=>0x307c0301d6981f0587d3a024058050300505972030070307f0081d059dc0301d05bc403b650581e0481f058050596b0301c0307c75c5d0081e0081f05818059700fbe70081c0081d034670701f0307f0081d05818058180307f0397105818030050301f05971030040344c0387504806088060581d3b8070301d0307c0300410805058180581d030270581a0300705b670301d030070300405819030040301e
|4=>0x58190300420005059dc0301d0581f030040081f0597103007049ac0301c0716b048050301c039710581f3b8070301d048b20301f059de0301d0581a1087d0596b0301c058070301f0581803007058180581d0307c0322f048050300410804058180301d05bb103004030050307c0301e9501d058180081f108ec0581810805058180596b0301c03a2d0597205973058180481d0581a0480503c8d0581803004
|5=>0x4806030070480605818058190480610804058181081f1081d058180481d1080500cbf0581a0307c0581a0581f030070307f200061087c1081d058180481d0581805b656981d048060081d08827059dc0301d1080505818030070581905818048060581d030ec058180307c058180481f05805058180580705818030072180605970059b40303804805009690301c0081d348180580703005058180880705818
|6=>0x481f0307704806059690301c0581b03004a5018030250301e059700300705818030250581f030040301e0301e0597203007048040581a059de0301d0301d05a1b03006030ec0481d0301f030070481d0397103007030070481f0303804805030040301c05818058050307504806033a01080505818058181080505818108ec05818048040581803004218254f81f0581805805058182180410805058180301f
|7=>0x58180301e0096b0301c0581d05a1b0300603877048060081d0481f0581a04806048050301c0581a030060597303007058180481d008df0581a059dc0301d030070301f0301e030041080405818008b00301f3a02703005059dc0301d1081d058180581a3a02403005030060300705a1903006a501f030250301c058180301d048050481d0081d0300405973030040481d0081d039710300703b65030270081f
|8=>0x33af0081f058180301c030ec0481d0581f03027048060301c058180307f0081d0081c0307f0301e0301f0496b0301c0300703004030070081d030070581a008dd0581a0301e10806058180081e0481d033e50081c10805058180301d048060300405818058190301e048050581c030040580703007030073b8270301d0081c0081d058180481f1080505818059d2030050581d0301d0300405b67030271081d
|9=>0x3004058191e807058190300705818030050701f04805048050581a058b00301f048b20301f05818059d00300503875048060081e0081f0301d030070307c0081d0307c0303a048050581804c5d0081e0081d05807030050301e0301e04806048050301f058183b8070301d04805058190301f0597103007048070301e0301c03004030040481f3b8040301d05b6503027009690301c033e70081c1e80405819
|10=>0x81e03005058180081d0581a0081f030070301f0081c0581903006030040301e0301c030250301d05818108270581805805030051082505818058180081c04c5f0081e0301f048060701c0480504806058190581e
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
|4,0=>0x112000000000000f2000000000000e100000d1030400000000000000000000000002880000000000000000000000000000000024408100000000000000018800000000000000033000000000000210000000000000000000000000000
|4,1=>0x9880000000000000000000000000000000000000000000000000000000024208880000000000084400000000000000000000000000001e306cc00006840000608000000000005c4000000000000000000000143000000004c400000000000000000
|4,2=>0xfc4000000000000000000000000000000000000000f0c0000e8800000003820000000000000000003620d440000000000000000000000000d0400000000000000000000000000000000000313000000000000000b8c0000000000000000000000000b442c10a8800000000000a08000
|4,3=>0x10040000000000
|5,0=>0x7c11ec47a100007821dc40001d847511d047221c446f21b8400000000001b086b11a8468219c400019846510000632184860117c45e100005d117045b10000592000058115c45610000551000054114c4521144400014044f113844d113044a211cc000000046111084220000411
|5,1=>0x2c48b012b88ac20000a93000000029c8a610000a512904a310000a12000000027c800027840000000000274400026c8000000000000009a1260800025c4952250400024c40000000912240400000008f123848c2000000022c48920000863210883120487f2000000000007e11f44000
|5,2=>0xe61000000038cce1237c8de13744dc136c4da10000d91000000036040000000d710000d610000d333484d1133c8ce100000003344cb200000003248c810000c710000c61310800030c4c210000c113004bf12f480002ec8ba12e440000000b810000b710000b612d44b320000000
|5,3=>0x478400047091b1464918145c4000000000000011610000000454514144c40000001121000000044090e243090a2424508141c40004148000410503140490013fc4fe13f44fc10000f930000f723d480003cc8f120000f013bc4ee10000ec20000eb1000000000000003a0c00039c4000
|5,4=>0x5949632588400057cc00057495c15688000000159155c800055855515505522000150253c54e153454c1528800051cd46150cd421000000000014114fc93e14ecd3924e040004d880004d4400000013414c4d3014bc52d24ac80004a4928149c525248c8000000121248051f1
|5,5=>0x64c4000000191264058e263098b1628400000018916205862614584160c400000018125fc80005f857b35e857820001771000174300017315c85711000000000017015bc400000016d200016c15ac40005a840000001673
|6,0=>0x7f85fc27ec5f927dc9f527cc9f127c05ef17b49eb27a49e727949e327849df27749db27649d817589d427489d0273c5ce10001cc27289c917205c717149c327049bf26f49bb26e49b726d85b426c89b026bc5ae16b09aa26a09a716949a326885a0267899c2668999166059716585942
|6,1=>0x98ca621980a5f1974a5c100025a2960a571954a5329486502938a4c2928a482918a442908a4028f8a3d18f063a28e0a3628d463328c863118bca2d28b062b18a4a272894a24100022220002202878a1c200021a28646172854a132844a101838a0c2828a082818a05100020328049ff2
|6,2=>0xa4468f2a34a8b200028a1a246872a14a832a04a7f29f867c29ec67929dca7529cca7129c066e29b080009a8a682998a651
|7,0=>0xa844000a8069f10000000a784000a7469c1a6c69a1a646981a5c6961000295100000000002941a4c6921
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x7c0f41e03b0740e01883005a0ac1402504808810820030050098120220400600a0120200280400600800800
|1=>0x1042044007f0f61e83c8770e41c0358680c016c2c8580aa1482804f09c1302584a09011c220430841042003f
|2=>0x2464848d9192224308490820840c811012003fc7a8ec19e32c650c818e2f85e8b915c2b0540a413223444084
|3=>0x408805001ff3a874cdb99d3105ecbc9762d65a4b095f2b655ca99492865009e93b2744e49892d2524a092924
|4=>0x6bad6d9fb2163ac157ead959eb315fabd578a914027f4fa9f13826f4a093d1ea3c46889110a1041c83506208
|5=>0x39ff2fd9fb375eeafd49a3b06d99a7f2e6503ff7eefbdceb5f
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>0x20000000000000000000000000000000000000000000000000000000000000000000000000000
|4,0=>0x4000000000a00000000000000000000000104000000020000000000000000010100210001000000330000000000003e00000a0600000000000000000000000000000001000000040000002100270600000000000000090000000000000000000a2100000000010000000001000006210000000000000000
|4,1=>0x40000000a0000000000000000000000010001000001000000000004210000000000000006000000000000000000003e00000000010000000000000021042d0000000200
|5,0=>0x12086a01004204002a0200532e0f270100001b18010006041800010000000021120027012d0040060056080000218158040054070007361058070000000453000053105300010e041002242d8b2d0200003d01457d2b530036210062131a180400100121000100407d530010001021044c005304017d2101030000101a600927
|5,1=>0x2100578d0f1010000053008d00007d10010400770600130f0101530a100057001904547d211053060011000107210507000904060f0100230400090031001300000a0000390b22181821100a007f000010000410003f00072104012300047d0104007e53007d040433002d53007d010401000b01080000060630000453010000
|5,2=>0x1000000113015b28530000212754060a0600000f1500230504070004008300044101090000105300000c002325000600068a0400015709000500012301000004552753330a1a00130a23270654002209850a0000000401272216040096002806005303105333550001012701150000021301
|6,0=>0x696c6890879e815f59343c9a58990d4a3c3c9b521c8938a56f6e6c5f1d2f16214e4b957d1f93b0a228ad4d6720ab28718d426b1b86916e398aad89092150a1aa2652571e733b9c5da78894a0b12c3a37a651698aaf011748149d3a5e5d6a767c447976477a35639792a3a2437e34a401981e8a5a1e704674523c667d6d441d64
|6,1=>0x54a8875c045b6835637661845c89808e7557977bac8f72271c3a3c27
|7,0=>0x3b651eae788c3b6fa93b494f3b821e1e298a326f5e4f9f2c
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_51,6,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 1 then [(dom_54,5,runOps true dom_54 (0,roots_54) ops)] else [])++(if pm.testBit 2 then [(dzo_39_16,5,runOps true dzo_39_16 (0,roots_39) ops)] else [])++(if pm.testBit 3 then [(dzo_38_16,4,runOps true dzo_38_16 (0,roots_38) ops)] else [])++(if pm.testBit 4 then [(dzo_49_4,4,runOps true dzo_49_4 (0,roots_49) ops)] else [])++(if pm.testBit 5 then [(dom_53,5,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 6 then [(dzo_22_32,4,runOps true dzo_22_32 (0,roots_22) ops)] else [])++(if pm.testBit 7 then [(dom_39,4,runOps true dom_39 (0,roots_39) ops)] else [])++(if pm.testBit 8 then [(dzo_51_4,5,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 9 then [(dzo_23_32,5,runOps true dzo_23_32 (0,roots_23) ops)] else [])++(if pm.testBit 10 then [(dom_23,4,runOps true dom_23 (0,roots_23) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_55 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_51_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_39_24_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_38_24_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_49_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_39_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_51_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_51 6 s (0,roots_51) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_55 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_51_8 h
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_55==dom_55) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_55 goalM v ys):RunD true dom_55 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 5 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 5 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 50 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 50 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 212 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 20 192=true)
private theorem z4:∀ i,0 ≤ i → i < 212 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 z4_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 320 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_320:∀ i,320 ≤ i → i < 371 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 51 320=true)
private theorem z5:∀ i,0 ≤ i → i < 371 → Z 5 i=true:=(range_split (range_split z5_0 (range_split z5_64 z5_128)) (range_split z5_192 (range_split z5_256 z5_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 128 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128:∀ i,128 ≤ i → i < 156 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 28 128=true)
private theorem z6:∀ i,0 ≤ i → i < 156 → Z 6 i=true:=(range_split z6_0 (range_split z6_64 z6_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 24 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 24 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=scr true dom_55 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_55 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_55 roots_55 goal_55_8 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_55_8
theorem lowS_55_8:Lower true dom_55 roots_55 goal_55_8 9:=S_55_8.noCircuit
def dzo_54_8:=0x5500550055005500
def gzo_54_8_8:=0x5400400040004000
theorem lowSh_54_8_8:Lower true dzo_54_8 roots_54 gzo_54_8_8 5:=lower_iso (d1:=dom_54) (roots1:=roots_54) (T1:=goal_54_8) [(dom_54,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54_8
namespace S_62_0
def pairsG:List (Nat × Nat):=[(2,6),(4,6),(10,14),(12,14),(18,22),(20,22),(26,30),(26,58),(28,30),(28,60),(34,38),(36,38),(42,46),(42,58),(44,46),(44,60),(50,54),(50,58),(52,54),(52,60),(56,58),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3fffff
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
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
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
def isoMv_57_4:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_57_4:Lower true dom_57 roots_57 goal_57_4 5:=lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_45_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_45_16:Lower true dom_45 roots_45 goal_45_16 5:=lower_iso isoMv_45_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
def dzo_57_4:=0x3030303030303030
def gzo_57_4_4:=0x3020200020200000
theorem lowSh_57_4_4:Lower true dzo_57_4 roots_57 gzo_57_4_4 5:=lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_4) [(dom_57,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_57_4
def dzo_53_8:=0x3300330033003300
def gzo_53_8_8:=0x3200220022000000
theorem lowSh_53_8_8:Lower true dzo_53_8 roots_53 gzo_53_8_8 5:=lower_iso (d1:=dom_53) (roots1:=roots_53) (T1:=goal_53_8) [(dom_53,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53_8
def dzo_45_16:=0x3333000033330000
def gzo_45_16_16:=0x3220000022200000
theorem lowSh_45_16_16:Lower true dzo_45_16 roots_45 gzo_45_16_16 5:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=goal_45_16) [(dom_45,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
def dzo_29_32:=0x3333333300000000
def gzo_29_32_32:=0x3220220000000000
theorem lowSh_29_32_32:Lower true dzo_29_32 roots_29 gzo_29_32_32 5:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_32) [(dom_29,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
namespace S_61_0
def pairsG:List (Nat × Nat):=[(5,21),(9,25),(9,41),(13,29),(13,45),(17,21),(17,25),(20,21),(24,25),(28,29),(28,60),(33,41),(37,45),(37,53),(40,41),(44,45),(44,60),(49,53),(49,57),(52,53),(52,60),(56,57),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7fffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_61.map (· &&& dom_61)
def goalM:Nat:=goal_61_0 &&& dom_61
def NN:Nat → Nat
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|6,0=>0x653667d8
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3333333300000000cccc0000cccc0003300330033003300c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def stPool:Nat → Nat
|0=>0x4688
|_=>0
def stOffB:Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 62 (i % 32) else 0
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
    (if pm.testBit 0 then [(dzo_57_4,5,runOps true dzo_57_4 (0,roots_57) ops)] else [])++(if pm.testBit 1 then [(dzo_53_8,5,runOps true dzo_53_8 (0,roots_53) ops)] else [])++(if pm.testBit 2 then [(dzo_45_16,5,runOps true dzo_45_16 (0,roots_45) ops)] else [])++(if pm.testBit 3 then [(dzo_29_32,5,runOps true dzo_29_32 (0,roots_29) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_61 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_57_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_53_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_45_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_29_32_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_57_4 5 s (0,roots_57) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_61 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_57_4_4 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_61==dom_61) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 goalM v ys):RunD true dom_61 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_61 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_61 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61_0 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_61_0
theorem lowS_61_0:Lower true dom_61 roots_61 goal_61_0 7:=S_61_0.noCircuit
def dzo_42_1:=0xa0a00000a0a
def gzo_42_1_1:=0xa0800000800
theorem lowSh_42_1_1:Lower true dzo_42_1 roots_42 gzo_42_1_1 4:=lower_iso (d1:=dom_42) (roots1:=roots_42) (T1:=goal_42_1) [(dom_42,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
namespace S_43_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,41),(10,11),(33,35),(33,41),(34,35),(40,41),(42,43)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_43.map (· &&& dom_43)
def goalM:Nat:=goal_43_0 &&& dom_43
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
    (if pm.testBit 0 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_43 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_42_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_42_1 4 s (0,roots_42) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_43 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_42_1_1 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_43==dom_43) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_43 goalM v ys):RunD true dom_43 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_43 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_43 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_43 roots_43 goal_43_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_43_0
theorem lowS_43_0:Lower true dom_43 roots_43 goal_43_0 5:=S_43_0.noCircuit
def isoMv_43_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_43_16:Lower true dom_43 roots_43 goal_43_16 5:=lower_iso isoMv_43_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
theorem lowS_46_1:Lower true dom_46 roots_46 goal_46_1 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050,2,6)] (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_58_1:List (Nat × Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_58_1:Lower true dom_58 roots_58 goal_58_1 5:=lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_1
def isoMv_57_2:List (Nat × Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57_2:Lower true dom_57 roots_57 goal_57_2 5:=lower_iso isoMv_57_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
def isoMv_41_18:List (Nat × Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_41_18:Lower true dom_41 roots_41 goal_41_18 4:=lower_iso isoMv_41_18 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_27_32:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 5:=lower_iso isoMv_27_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
def dzo_51_8:=0xf000f000f000f00
def gzo_51_8_8:=0xe000a000a000800
theorem lowSh_51_8_8:Lower true dzo_51_8 roots_51 gzo_51_8_8 6:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_8) [(dom_51,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_8
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16_16:=0xe0800000a000000
theorem lowSh_43_16_16:Lower true dzo_43_16 roots_43 gzo_43_16_16 5:=lower_iso (d1:=dom_43) (roots1:=roots_43) (T1:=goal_43_16) [(dom_43,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43_16
def dzo_58_1:=0xa0a0a0a0a0a0a0a
def gzo_58_1_1:=0xa080a080a000800
theorem lowSh_58_1_1:Lower true dzo_58_1 roots_58 gzo_58_1_1 5:=lower_iso (d1:=dom_58) (roots1:=roots_58) (T1:=goal_58_1) [(dom_58,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_58_1
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2_2:=0xc08080808000800
theorem lowSh_57_2_2:Lower true dzo_57_2 roots_57 gzo_57_2_2 5:=lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_2) [(dom_57,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_57_2
def dzo_41_18:=0xc0c00000c0c0000
def gzo_41_18_18:=0xc08000008000000
theorem lowSh_41_18_18:Lower true dzo_41_18 roots_41 gzo_41_18_18 4:=lower_iso (d1:=dom_41) (roots1:=roots_41) (T1:=goal_41_18) [(dom_41,18)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41_18
def dzo_27_32:=0xf0f0f0f00000000
def gzo_27_32_32:=0xe080a0800000000
theorem lowSh_27_32_32:Lower true dzo_27_32 roots_27 gzo_27_32_32 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_32) [(dom_27,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
namespace S_59_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,25),(9,41),(10,11),(17,25),(19,27),(19,51),(24,25),(26,27),(26,58),(33,35),(33,41),(34,35),(40,41),(42,43),(42,58),(49,51),(49,57),(50,51),(50,58),(56,57),(56,58)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_59.map (· &&& dom_59)
def goalM:Nat:=goal_59_0 &&& dom_59
def NN:Nat → Nat
|4=>4
|5=>12
|6=>2
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|4,0=>0x4ebae2c83f4b944537b2141b1f596e8a
|5,0=>0xe6d7b8d7d66b03b9acc8b14c85c9d4317eb9f287552add5f30d9886e2928435f24b172a10fed498e06c5ef24044cb8d6
|6,0=>0x89a9dbc0638b81de
|7,0=>0xf0260ba
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0f08080f0f080820202020a0a0a0a0000f0000000f00700070007000700808080800000000707070700000000a000a0000000000303030300000000300030003000300f000f0000000000c0c0c0c00000000a0a0a0a0000000070007000f000f0040c040c0c0c0c0cf000f000f000f00a0a0f0a00000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0af0f0f0f00000000f0f00000f0f0000c000c000c000c00a000a000a000a00808080808080808
|_,_=>0
def stPool:Nat → Nat
|0=>0x41a0c520d062ac83419852590628083418b5220c55d083418b320d062c883418b120d062c0834140f20d0503868698ab1a0cc2ac834182020cc5510682a48831ca418820
|_=>0
def stOffB:Nat → Nat → Nat
|4,0=>0x1ea2942a805
|5,0=>0xacd41a534467cce19932c64cc818d3146
|6,0=>0x3135c6
|7,0=>0x685
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 60 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x3142183141a2314314614218314314220314218314314
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>1
|5,0=>0xc100a2917200610051322111
|6,0=>0xe1d1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xffbb70452a201811060100
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>1
|5,0=>0x204170651381
|6,0=>0xa9
|7,0=>9
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 4 (j % 128);fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_51_8,6,runOps true dzo_51_8 (0,roots_51) ops)] else [])++(if pm.testBit 1 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 2 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])++(if pm.testBit 3 then [(dzo_43_16,5,runOps true dzo_43_16 (0,roots_43) ops)] else [])++(if pm.testBit 4 then [(dzo_58_1,5,runOps true dzo_58_1 (0,roots_58) ops)] else [])++(if pm.testBit 5 then [(dzo_57_2,5,runOps true dzo_57_2 (0,roots_57) ops)] else [])++(if pm.testBit 6 then [(dzo_41_18,4,runOps true dzo_41_18 (0,roots_41) ops)] else [])++(if pm.testBit 7 then [(dzo_27_32,5,runOps true dzo_27_32 (0,roots_27) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_59 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_51_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_42_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_43_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_58_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_41_18_18 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_32_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_51_8 6 s (0,roots_51) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_59 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_51_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_59==dom_59) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 goalM v ys):RunD true dom_59 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 4 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 12 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 12 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 2 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 1 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 7):∀ i < NN s,bar true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_59 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 7) (h:RunD true dom_59 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59_0 8:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_59_0
theorem lowS_59_0:Lower true dom_59 roots_59 goal_59_0 8:=S_59_0.noCircuit
def isoMv_13_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_13_48:Lower true dom_13 roots_13 goal_13_48 4:=lower_iso isoMv_13_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_14_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_11_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_11_48:Lower true dom_11 roots_11 goal_11_48 4:=lower_iso isoMv_11_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
namespace S_15_48
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_48 &&& dom_15
def NN:Nat → Nat
|3=>2
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x804d157017d4d0b
|4,0=>0x443fc56f3770bdeb2f2504b62e12f4272b8d2b7e262ad8c118ab9c7114e1c470
|5,0=>0x57e3d3b0129291b907006be5
|6,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xffaafefe00fc00f000fa4444ff00fafaf0f000feccccfff0ffccfcfcaaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x86408640e864081640387408d6408640c8140b8640a38140286098174064053210
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x22004
|4,0=>0x56a9950a9c52ea4946a885
|5,0=>0xe91aab05
|6,0=>0x3e4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 15 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x80501605018690160d01
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>1
|4,0=>0x5141003100211100
|5,0=>0x7161
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf7653210
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>3
|4,0=>0x8420d5
|5,0=>0x1bf
|6,0=>7
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 1 then [(dom_13,4,runOps true dom_13 (0,roots_13) ops)] else [])++(if pm.testBit 2 then [(dom_14,4,runOps true dom_14 (0,roots_14) ops)] else [])++(if pm.testBit 3 then [(dom_11,4,runOps true dom_11 (0,roots_11) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_7_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_13_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_14_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_11_48 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_7 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_7_48 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 2 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 3 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 3 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_48 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_48
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 7:=S_15_48.noCircuit
def isoMv_30_32:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_27_36:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_27_36:Lower true dom_27 roots_27 goal_27_36 5:=lower_iso isoMv_27_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfee80000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 7:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_13_16:=0x33330000
def gzo_13_48_16:=0x32200000
theorem lowSh_13_48_16:Lower true dzo_13_16 roots_13 gzo_13_48_16 4:=lower_iso (d1:=dom_13) (roots1:=roots_13) (T1:=goal_13_48) [(dom_13,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_48
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_11_16:=0xf0f0000
def gzo_11_48_16:=0xe080000
theorem lowSh_11_48_16:Lower true dzo_11_16 roots_11 gzo_11_48_16 4:=lower_iso (d1:=dom_11) (roots1:=roots_11) (T1:=goal_11_48) [(dom_11,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_11_48
def dzo_27_4:=0xf0f0f0f0
def gzo_27_36_4:=0xf0e0e0c0
theorem lowSh_27_36_4:Lower true dzo_27_4 roots_27 gzo_27_36_4 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_36) [(dom_27,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_36
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(2,3),(2,6),(4,6),(5,7),(5,13),(5,21),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(17,19),(17,21),(17,25),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>7
|3=>131
|4=>302
|5=>258
|6=>84
|7=>14
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xf56a1f9cd4b6d4718ec34ef78c5fec1e84cb36aa5e483e8534479cc6
|3,0=>0xca410ae5c5510f74c4f1028dbb05676fb68b2110b34bde55b0c90f16b02600acacb08d0bacaf0b77aa4a833ba98bd46aa1c581329d354eda9c1996d09a4922e099fdf6f89596f062939e38a391a329069161d1649126ee9e9122537e8fa5ae848cd93f208bd5b2f289f7fdcd89c3c46386bf0a3f82b5db707f62a33b7d6166916dec5a0a6d98ab276bc4904469ef5dbe68a7fc9d681b91a064fcbe5763b3cc1d62d9b6dd61c330f560120a2f6007a5455d1238125cf465f25ad289835a375d155924bc4d58b575a7587e57c756e89399552ab1c4509a7f6c501b78f74fa8a7b04e05812e4b3c7a804a97c9ac49754ed647c6fa82470a5cc645a36502459b00204535264144c701f640c0e7c6409e5e513f9fcc513f5dcc413da1d1603d9645c73d4d68483b36d6993a2501ca3888b023364ac10934b24baa3426ec7c341cd23d327a6fe6318acd9130f9833230b82b90307d48ca2e2240232d6317072c6d059e2c37be842c2731042a69ac7e28ff4e1c27dcd34626b7fa1024812a8522624656202b40fc1e109a031c430be91c0955d01b8d6a361a275a1319dcd7c61861eee916e05e5515ed589f136de1a21346ad641184cb1e113cbe53106281700ea95a0e0ea2f8410deba9d50d0a76280bcfa8760ae8822e0aa7b6b009cc5dd4098a08c608bf775506a9f90f04e9f8c704d89e9d0427963002cbca3d0264d830014ddb2e
|3,1=>0xe4680b7ee19c44e3dacf3814
|4,0=>0x3f5dcc413e9a767d3e92c9913e54fa973da1d1603d893b2c3d86ab1e3c1a10233c109fc33a2f451f38f076f337c31de5379f53e63786d9bf366e3bbf3662cb6a36374edd362ce41d35f20157359a4ad234d2bbf333e8e3c733954b5a331f1062327a6fe63201a3d131c07e7731a3e9523170e96430b82b902fe3cb7c2f9385a62e5608a12e4499be2bda19dd2bcb972c2b2553822a4bb8ce2a2a4ff12a1dc82e286e5510273b64d4272f99e92654e857252e722e24f9772124a6669623863d5722b1f1752298ee68216bd392216a342f2016343e1f7e35a31ef9d35d1ef6f8651eba38e61e46f3821de0f1b11ddb8fcc1d953a641d51fb051d4595111d1e44c11d1cf1cd1d1729471ce965801c0955d01bd0fa9f1b92ecfe1a6f6b6f1a3f88121a33fbe319b6c12a18b9ff74189b0920185caaf5181cb76217d88cd6177d02341742191d16d9650a16621c6c163ecc2815feb1a915d5aaba1519cabf151720b414f9da3314c83fdd149ee5ce13936ff7132d6ea811a6453e11982b5b1192a17f0e616dc10deba9d50de343b40c71fe630c39d32b0af493e30a91a3ed0a673ee109d66ab60995131409701b2d095a304e093d1a6708c6b48c082bb2f907d288fa0795c01807711ece07044c8606d5d98006bff29b0653e7fd061ff50f04526d98044d1ef6030fac4c030deb0602ff50a202b55aa10220e3de01f6885100ac2075
|4,1=>0x999430e898b8184397db5c1497d7e165967af1b49596f06294aa391a91a329069126ee9e903a00d88fb4e2818faad6bf8f89dd9f8f5c78898ea7cf768dc32e798c1bd8ee8be654fe8bbcacfc89f7fdcd8769f47e86bf0a3f859221d8856ca5c9835bd69682ac1a80826199ba81d2980c814c2fc7812ed8c180f8a0fd7fff301f7fa595617fa4738b7f620e257d0379b27bf112d87bec798b7baa0aa17ae562da796e0e3778e8a7a878c00d1e780b9354766690ac757539bf753bb4ad751fdd9774944693739e532a7358b0df73496e1870ea08487090d91e6f64164b6edf4c7f6e5009296e2162966e1db5af6df55a3c6dd24e0f6d0ca7d56c37d5ca6b6a41286b220e5a6a0ce04069eea2bf681d274b66c7162865d2413a6539b3396446456663ce8b446378063a6373dbe2632c3f68631dab3262420584610a451360a6b92c5f02e12e5ecc106a5ea28f925e9974da5e4ac6625dc393f95d5fefa75ce5d5965b9591b15a61957858b575a75867a6165797230855d202a455058d5a54f85fc3543bd6f1533c64e252e3179452b9fb6452824ed4527f189e50adef194f3a5f034e0658254aff15cf4abb9ddd4a447f0248233c2547d6c2924779ad824751c4f5466bb67545d6b026455f5d1544c701f6447230f54337887342cc454242994b4a42269b13417856d040bacd3b407e69994056b4ba40022f313fc3a61e3f66498d
|4,2=>0xfadb57f2f94c1570eaa42c48e37626bce1de62c4e10c1333da93bc79d4e5d36cce838bb9cc40ac2ec89f9dddc8360337c7b89038c6df32aec6526190c645282bc3e010efc17965a9be44c5e7bd4c59b8bc2b9dc9bb63907fb76d4208b4bb271bb3a5ec8baf1a4984ae03d8e4ad9665efad881b03abf5347aabc7dc7aaa48da52a8537a75a70c652da6d5b928a4c5ce06a3b57be7a1a6335da0b7a2c2a09ebea09fed8d6d9eca1beb9c89c2f89b5d5b159a9d9a389a6aca22
|5,0=>0x43dfabe24358f550431deb014319edeb427b26d8425b66cf4244a0e240f8329b40dd29da40d49df040c8b4c140bd4fd5408f88274073ea4b3f8718b73ebe0cb33de06abd3d67fb903a5d89983a3cbe7d39bdffda39398c8438e89bda383e6c7137cda7f237b1fffe3775142c366b3531362ce41d35b5e6c535a080f03567479334ff69903475e8c93349baee32512a9431bea6153123a890310354fe30e877f630c2fcda306e337b2f12aa542eece4332c0031742bfa7ecb2b373e1f2a37788328cfa3f6274dc3c326439a1a25bfc91825516548240843682301ae1321faf87021f54f5721d08c112194ce9b2115b8de20e5646a1ebffd381e6b8a021e489d4d1de044ca1d853eac1d2275031c6866fd1c0850591ba036781b67e75e1b13165d1a80579d1a466b8b197366b7192a467a186ed88f179d969315e918d415cb7182153b5be514c83fdd145cce64145953b51442b6c81400b75b134c3aee12ef47ae12b1852b11a6453e10d02a870e290ae80e00f47e0d574f4c0d1f19440c3b303a0bf274900bc415b80bc1162909e08ade09a7d8f709951314097b662508d28bee086b9afb0867c74e084bb8820811cecc072cd911070adda606c005bf063fd312060752a90500130004f9784904f6ee0903fd00cd0362d51d03486bd803026ea402174f7101df929b01d6939901c638ea01a2813b015a593100ec9e360067d350
|5,1=>0xec927571e47a6982e3d4fe57d704caf4d28b70f2d0fe898ed080abebc76d0723bea8a026bceebcd0baf049d3b744f36caf930799aed8f1e2ae6025cdab5a7594a7fc7918a684b1daa5dd5bf1a4ce50bca3368cc4a2643d33a236c81aa1c44cfda129948a9fbe3e359ec076b19d69ed2d9c55d9d49c233cba9c051afd9ad150299a19852c99cfb3d0999e641d99989b97997cc6bd97b096a9964edcee949e29b294580ad79392a0479337e7069252a89a9161d1648f89dd9f8e366e858e127b088d2d5fe58d0267a78ca00cef8c4e38768c3a8743897949ca8946e502891e5fbc8860caa984aaed5884a647a883ff3e6e829619e27f36ccf17f30454d7ea82caf7defba927db5bc9878180520780e9d697780d6c176a33ec775a848c075746e58751696de74656a0273dc95fb73cdae277372e193712a1940710c45666de7fdbd6dd977086c37d5ca69896e1d680000fa66159e9f65fb51eb656c93bf647d74b3636fcea262a2f7be5ee7f2835ec37a3c5e342b405d8d85835d716bf35d5fefa75d4222545d2650f05d0e99285ce5e66c5ce5d5965c5c98925c3db75c5adf94395ac3cbe45a64fcf859c8630959967f3a5966f1845762308c5761180d56994abe5653f03252fb5306527f189e5270c80551c7b8e5506d53ad4ff701f34ec2c2d84ead54614d553f164c7b51494aebb28649df6f9248398ccd47c0752346912e38
|5,2=>0xf483970feeee01a8
|6,0=>0xf2d7842ae2f6cc52dc943f54d97bde48c6adaa0ac649b516b70b8c48ace40d3fabe6e128a8c42078a7848147a74692fba2e1b633a0acd41c9ffc183a9be1e518906efd648f9570a78215fd6d7f482aa17c00ecf67b3a363b79238a6e723bc33370098edb6f02c2726efe5e576dd427ae680ad10c6501036f64dcc446642830f25f9423af5f84236f5f4048c95e12612d5c56672d5aa3dacd5a4a0be5584d6a3b572d3d6a565fc1da52b9fb6450606b134c7b51494b36dbf445e0152944e04f8d431deb014268d4dc3e67f4813abf154634b0cb8f32ccbb283161aefe2eb642ba2b039043241cb7b223c89a0a22c5a1b521b4f2fa205f4d0c1edb55471be11d8c18907b5416e0a50516032cd515e918d414e19db8138b8c9513195c2512b3d679118433b6117fcf9b10de97a00ea311090e61fd760e5dbbed0de343b40d59fc0a0ca6363d0a93ed5809e2bbbd090f6918
|7,0=>0xab95585a579c512c569c8b903e49a49334b0cb8f2e079448258c480e21a8620b205f4d0c202fbf56129dfe450d59fc0a09e2bbbd090d6eb4
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x1414141444cc44ccffff2200ffaaffaafaf0faf0ffaa000044444444cc88cc8855ee55ee50f050f0000055aac4c8c4c8ff000000fcfccccceaeaeaeaffffaa00eecceecc15ea15eafca8fca8eac0eac0aa5555aaaaaaaaaa00ffff00cccccccca55aa55aff00ff0096969696f0f0f0f03333ccccffff000055aa55aa3c3c3c3c
|0,1=>0x152a152a565656563cfc3cfc0000ffaafcfc0000faf0f0f0c0c0fcfc3c3cfcfcffff8800f3f3000030303c3c555500000000aaaafcfcc0c03cff0000ffffc0c0ffc0ffc0aa00aa8855ffaa00fcfcfcfc55aa0000ffeeccccfcf8f0f0ff3cff3c3c003c00f0e0f0e0c0c0c0c003fc03fcf0a0f0a0ccc8ccc8aa00aa0082828282
|0,2=>0xffaa55aa0000ffeeffffa00077bb000070f070f03c3c3f3cffffaaaaaaaa0000c300c300003c003cf0f0c0c0eecccccc00ff00aaf8f0f8f0ffff3c3c3c3c0000ffffff00ff3c0000ddeeddee448844885656aaaafcfc3c3c00fe00feffeac0c033cc33ccddaaddaa0000fcfc3f3f00003f003f00d5aad5aa0000f5fa55ff0000
|0,3=>0x30303030babababa2c2c2c2c55145514ecccecccff00ff0cffee0000cfcf00000c0c3c3c9a9a9a9a0c0c0c0caaff550000aa00aaaa44aa4433223322aaaaeaeac3c3000000003c3c0f5af0f00000fffa2a2aaaaa151500001c3c1c3cffc0c0c0fffcff00feaaaaaaffaaaa0055fa55fa7f7f00005af05af0555455543e3c3e3c
|0,4=>0xa2a2a2a255aa5500cc00cc00fefefefea8a8a8a8f8f8f8f8aeaeaeaeffeaffeaea00ea00ffff55005500000000440044000000aaf0c0f0c000aa00003300330000cc00ccee00ee00bbaabbaaaa00000080808080550055000000f5f0fffa0000f0f0f050d5ead5eac2c2c2c2ffccffccffff8844ff300000aaa8aaa8ffffc300
|0,5=>0xf0f00a000a00fefe0a0afcfc8888aa88aa880000c0c0fffffcfcf5f0f5f0c000c000333300000000cccce0c0e0c0fff0ff0050a050a0ff003300c0c00000ff0cff0c3070f0f0ffff55aa2a002a00bb00bb003f2a000000003030ffaaaaaa00ee00eeeeeeeeee3e3e3e3e2020202000550000fffff0f0f0f000000f0c0f0c
|0,6=>0xff44ff44ff50ff50332200000044cccc888888880f0a00000050f0f00000fffc0f0a0f0a3f2a3f2aaa55aa00707070700c000c00ffff0c0cc080ffaafc000000005000500302ffaaa000a000545454542222222244004400fceccccc50005000f4f40000fcfc00fcfff0fff0f000f00002aaaaaa040404040000aa000f0f0000
|0,7=>0xffc0ff00153f0000323232321f3f00000a00aa00fefeaaaaa8a800001e1e1e1e28282828f300f30000fe00aaffbb0000f2f2fafa000a000a4444cccc22002200fffcfffcff00f300ffff00aaa0f0a0f005000500feaa000000aa55aa11221122eeaaaaaa40404040fe00aa00ffea000050505050ffff0044f050f050ae0cae0c
|0,8=>0xfefcdcfc0000fca80000fcfcfffc0088008850f0f0f00f0e0f0e00fc00fcfe00fe00fc00fc00fffc000074740000dcdcdcdcf0faf0fa00a000a0f8f8f0f0bfaa0000aa00ffaa55f00000fefcaa00af00af00cf00cf00faaafaaa5050f0f0ff55000054ff00001133000077007700e0e0e0e0103010300e0c0e0cffaaff00
|0,9=>0xa0a0a0a00220022fcccfcccfeeefeeefffaf0f05444544400000c0cccfc000088cc88ccbfaabfaa0202020254fc54fc0ff00ff0fafafafaa0a0a0a05a5a5a5a3030000011001100ffff3030acacacaceeaaeeaaeeaa000066666666545400000f000f00ddcccccc0000ff00003f000010101010eaea000000f000f0feee0000
|0,10=>0xff30ff30aaff0000fc54fc5403030000f0a000000eee0eee3020302030103010b0a0b0a0ddccddccab00ab00ffffffaacceeccee44cc000073507350cc44cc440202aaaaff303030405040500300ff00cccc00003f000000131300001f001f000c0c0000ccaaccaafcecfceca8fca8fc8c0c8c0cffcc000088008800ffffcccc
|0,11=>0xfafa0000fff0000077770000c0f0c0f0afaaafaaff3300002a2a2a2aff88ff880cae0caec0e0c0e050550000fcdcfcdc
|_,_=>0
def stPool:Nat → Nat
|0=>0x160c8140213020021a020043c06050c4003017828001a020205c1c020205a020e0b0181a0203c0204040ac2a2a030a41402140284e04040042a021306042021282848020e0840002118884202030803e10020043c1d0e06c101a0203c3202020602e08008582a020205002060984822100203c0202020201c02068300808058280009010200e02030140801018080200
|1=>0x400456020203c0202021349806020209602179281402050009248030b01408008ac2c3b020288e020d9181006090ec2230178b0140202088020a218008a020510c000a2210c000202108100404004821b041000202020207e02030947c02178287a1c0d8202a1b04004782f1d82800021d02002061c82800300302870370202002061b0286a020d82002061a000662f
|2=>0x2020021a03028001a02020c8060518c00020e020c40203184000203028c05f02020800404004bc5d0e06c102f160448a300510c00020e06c1e040417002020416c0204200043c0400878782c12828120203028b40407900025903160001c0203c2a040780478022b828ac022a82002100e010a80205000a602290200202020043c5103028a04f09828004e030280004
|3=>0x30280002009fcea02068944202031f8fa02031f000100e0e810020e06cf6060510000060500078023d02800790202002063c028ee1a020200202031d8ea06050008a02030280006051100004041d0e602021c8e202178b0e00637828dc1a0203c140604028da1002020020404004d80203000d60211820c80609044d40203028d24f340b0143b0510c0067330101065
|4=>0x101010014a00838041108404040400526020315c1400030ed240805040380404100041c0d82002020202002911d8101490478080c04089c40404470211a0242018581101010108c0087036081090004060522c00020302868000101814580013c262c128280808451cd12880202002024382002020221810061da141484030ec22830202002820302800061d8950280
|5=>0x30b014a50e0101021158080c7e521d404060526c00020302886000202042a31e21034040402944a104228e6061d82014a001018149f00008080800a28040605000ac1a030a4100a01010109e3981010010a8080c0a3f9d5083b022741402032704a9b0d01934080501876084c82804980225c100616028004501018580a0025808084a9cc0c2c051100002030b10a0a
|6=>0x201fcea0203028007301070080f0c808080800ac8040404005461a58810100a1801858b0050095e06050009e020302800020302800900106c10010d018100a572b4040404004041c02021581a02021560a42018762505018147f3a8f0041b0202002023d028fe7503010100a550080c0a002a5501a020204210030b04a0a0d010100a538c05e0616029081a022981402
|7=>0xf008080800b04108a601cd7e590101814000e01042400f008080800af8040407820021c02020022b032f408080500838040780438041087878065e010100a0d0185825050680c04042ec042f16029741c0203c42400202042010aae404060500004b8020200202030344a0a01018582530870080f108f0042f162dc1404452d8e6b50101858b4052cc0808052540c0a
|8=>0x4081826a1088203404040847802020219a01010b00808008080c0a6600034060206596020202002ca41018147f3a8184a0a0011434066481014025c0219073010184a0a000184a0a22000200202020020663810100a010198c25050700808109798a1a620201430178b01430030b01400030ec0808618083608108040404040043c020510c00020302800c2010700801
|9=>0xb5c04060982800020202042d60107008086aa10340405064040605001961a0302014d401070360f0400808010f008340404004380410ad96a06160ec14000d0180811040080c0a0034da402030280002030b04a6b010181400228080c9905000040605110000602021a20a33b40080805010100115808080800b3c0c04040299c02178185811010101e0101018080f
|10=>0x40085e2c0539860061282800e51d810100a720180811040403804040840c3b04029c6e20e01010210101042010f008381b0781876e104028040670028fe1a6f810100a0d3780808050101021008ac0c0405375b8020203c42010d01808a66d8080c2c12828380810b017e0616094144408008381b040187608050580c3b08820140604029b4d9030b04a0a6c0080808
|11=>0xe06c1e210101814007b818f00a3aaa404067b028003b0202014f57a0700808108703404040840c3b7982014020202002f2030ec080a78808080800bc00404040058002020204a0177818762505009dc0a3f9d40406050d4eaed02021149101021d8eb39819d40404028048a3f9d4e60616094144001010108a7480950130203c04280302800020202002e80d01808e7
|12=>0x541434040402a0802032981400030ee06080501808110410004060540a0202031bc14008004c08080501814503f9d4041c02020c806051fcea6e0306c100a22009fe2c1282804980202042060202014fe0107036210f0187604053f40c2c05000dc060203c14fc0107008087d819f404043e40468030b014790e0101021030ed340805018762505000040604029f002
|13=>0x1070085410868080800810110f0510c0c0a001140c0a22000380404438429601010100103010100a868083808108580d0c02020140254018080f010bc580a21868080885828040685028000202084e2940d0101e0a01070427f3a8400808008080d090203c0c3b0402a100202134100101070080c040080c0a811d60e040422926020202002bf03010100a8304c080f
|14=>0xd0101490178b04a0a228080c0a00140760404228e6028b8b04a0a010104608008080c0a001b804a80203c04ef8b0941515030b04a0a42068089d05018080805450041c040042c020301023130d0101490478680808108643808109002c0605000a075010184a0a1c07010210b0f005120422a220404004e6150101814200001877100402804061b0280002420181400
|15=>0x40840c3b0409414020202002b5034800808050080c040784404ef03028000203270140001018148a00018080f0547d500602020b00204084021601070582510818580a222e8340404085280602478100a010184c110401a3a0404028381a0d8204202034704a0a0101010018d8185825051b8041c0408634020e0204319010101e0a8c040381b040840406051fcfa84
|16=>0x50080d0a051fcea1a03010100a108083804040843c02030125408050090804040292a0203248100a3f8080c0494808080f052280c3b0202015280d01808080549c041c0202042c1010180926040280406051fceb2503010100a22490040602044112301071ec0404028040602488100a01018582505114041c0202042be0d018080805484040616094144401070080f
|17=>0x12100c0a3f9d4041c0203c4202020211475398080c045336e4602030b0080f050083804040859a0202020028a01070580404084040447020152e968080c0a3f9d40c3b0202014cb030114c080511020020e010102101018112c0538c04060203d680a0101876080538c040604264147f0e01808080511004061602800020304c5825053140c040402888020301010e0
|18=>0x202042d701018080c040280406044c1c6020402a660203028fea43a8080808451cde4020302260020e0101021388680c0404029b4061d811420805008380410878041c0d010102101010108a601cc380602020144001018080f4e8280404040951473010182208600187604040297e0202020148a4801876040402a5e020e010102167a1034040402804061b028fe75
|19=>0x101808a6042340c040402880e3010111c08052280406024e0100a010101137451ce001a03010100a034c8080805110340602020147f0d01808c4040280404044d81443014580808051cc04060203c14900101826040882108060202014440101808110432c0c0404028808f010185825054d40404042299073010180808054d004040402920a351008380404084041c
|20=>0xe0101025108080c0407828ea02020211495398080c040408598024c018081104500040404228e6020e01010213a8680c040402a7e0202284108a398680c040402922020202114739f0080c250500004069e010100a010194211044ec3406020201402030101e0a80818080805084880203010100a9d0080c0450844100203028fe759c8180808051124e02030280075
|21=>0x398083804045181402030b04a0a928080c040782a04061d8114c08050080d450202014060202014955b0080c0481820141c030ec0808050080c040402a881a03010100a453140c3b02020140203010100a350080c040782980020302015430b0080c0407a38140602020144435008380404085e14203010100a5b0080c040789414020e0101021600083804040868202
|22=>0x34f408a60501876040402a62061d810100aa63b4040404228e602098101e0805018760404029c6061d810100a6d80966040402914061d810114b05018080805112948409810100a5b0185825051140c2c12828880203010100aa48080c0408c88100203010100aa40080c040426d140203028fe75a3818080805100320203044100a3f8080c040402a5c02020201443
|23=>0x2022a08a39870340404084040605000fe7503010100a201fc0c3b02020154f010181a04040280c3b99010100a01010100a008180808051fc780202298108a398a83406020201484030ec080805008380404229200203029147f3a8080c040782a0a100e01010210101808a60882280020e0101021015380c04040283406020201433030ec100a718080c040402a9a02
|24=>0x48008095604228e6020e0104608108080c0a1a1fcea1a03010100a398080c0404554140203010220890d50041c02020420203028fe7519808095304228e6061d810100a0c818080805102a4020202114e339809080602044100203010100aa8818760404029f2020202114738d8080c0404229980202022968a3980808e104228e60202020152e538187604040284202
|25=>0x500838040452c420202021560a450080c0a3f9d5520203048080805008080845064e602178185825050680c0404028ea020302800020e0204216010185808050580406020280002034f4080a0c8080c2c0882014020e0101018108080c040402ab2020e01010210b0080c04044d8140203010100aac2a03406020201402030101157050080808453ace61c0d010100a
|26=>0x20201444398080c04078296c02030118811040083804040856c02778185825050080c9c160941402030b04a0a450080808451ce220202021152e398083804078280406ae810100a010185825055700c3b02020153f0d018095b040280c2c04029c64501018080f0538c340404028e60203010100aad0080c0407d2c140257818147f3a93c0406051fcea02030b04ab0
|27=>0x4028040602020147f658080c04051fcea020e0180808050080c04118201402030114d290101808080558c042c0202114730304c0808054bc0c3b020201490030ec08084e828040602022c40a010180808055840c2c1d810100a0101ac00404028040602044108a010185825050cc04060882014c00157c0c0a3f9d40404045791473010bc5825050080c2c128280006
|28=>0x51cc04060254c100a0101a64040402a4a0203010100a71818080805110040602384100a010180808a8028040404029147301018100a0b008080805229200203010100a453000406020204a0a450080c0404060140203010100a0b0080c040402aca020301022080500ac80404028040602298100a718080c0404029147501018260404028fe0203028fe750101808a6
|29=>0x457814061d810100a010180808b3828056603010100a010185825050080c04040941473010180808054b80406020201475398080c0453020147f0101808c453020140203012060805008380602020147f01018091304028040602298100a970080c04040284202420180808052d804060229a0608050080c04ab02014020301010ab050080c040402a3002030b00808
|30=>0x20201402034c81131010700c2c020201402030114cdb010180808052296c06020201569010183608050080c0805350040602020148a718080c0404594040602044100203010114b05228040699020147f010180808b402804060202014b63f8080c040cb2c042f03010100a01315880805008100a93c84048403010100a3f8080c04958201402034f40808050080c04
|31=>0x536c040602020148f0101808a604028041c03010100a013140c0404028040699284100a01018273202020140203010100a978080c040409414212c8080d3202020140203021c73f010700c0404228040616010100a108080c0404029c6900101ad6040402acc0602020140203010100a451fc04060202014710101a240404028040404028428a0101858080538ed406
|32=>0x80c04040280406020201473010180808051fc040602310100a01018080805064040602020142101018080805484048403010100a010180808054c404060202014e3010180808
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x48c01e600c300498018c00660003
|3,0=>0x88a0435021281054080a03f501f280f54078a03b501d280e54070a037501b280d54068a0335019280c54060a02f5017280b54058a02b5015280a54050a0275013280954048a0235011280854040a01f500f280754038a01b500d280654030a017500b280554028a0135009280454020a00f5007280354018a00b5005280254010a0075003280154
|3,1=>0x108a0835041282054100a07f503f281f540f8a07b503d281e540f0a077503b281d540e8a0735039281c540e0a06f5037281b540d8a06b5035281a540d0a06750332819540c8a06350312818540c0a05f502f2817540b8a05b502d2816540b0a057502b2815540a8a05350292814540a0a04f5027281354098a04b5025281254090a0475023281154
|3,2=>0x875043282154
|4,0=>0x1ad28d5546a0a34c41a3a8d09467aa3385199a8cb94652a324518fa8c69462aa3105185a8c194602a2fc517ba8bc945daa2e85171a8b7945b2a2d45167a8b29458aa2c0515da8add0564a2ad515428a8d453ca299514a28a3d4514a2855140289ed44eca27151362899d44c4a25d512c2894d449ca2495122288fd4474a2355118288ad444ca2215
|4,1=>0x24ba1249491aa4885242211fd48f4a4755238291ad48cca461522e2915d48a4a44d52242910d487ca439521a290bd4854a4255210a1071482ea4125206a90250808a3ff51fd28fd547e0a3eb51f328f8547b8a3d751e928f354790a3c351df28ee54768a3af51d528e954740a39b51cb28e454718a38751c128df546f0a37351b728da546c8a35f5
|4,2=>0x2ea2973d4b94a5c552e0296ed4b6ca5b152d62969d4b44a59d52cc2964d4b1ca58952c2295fd4af4a57552b8295ad4acca56152ae2955d4aa6854e52a4a95114a7ea53a529aa94c14a56a5265290a94714a2ea5125286a94214a06a4fe527ca93d149dea4ea5272a938149b6a4d74269293354990a4c3525f292e54968a4af5255292954940a49b5
|4,3=>0x387a9c294e0aa700537da9bdd0de4a6ee437521b954dc0a6db536b29b454d98a6c7536129af54d70a6b44357a9aad0d4ca6a1534e29a5d4d24a68d534429a0d4cfca679533a299bd4cd4a66553302996d4caca65153262991d4c84a63d531c298cd4c5ca62953122987d4c34a61553082982d4c0ca60152fe297dd4be4a5ed52f42978d4bbca5d95
|4,4=>0xfe8a7ef53f529f954fc0a7db53eb29f454f98a7c753e129ef54f70a7b353d729ea54f48a79f53cd29e554f20a78b53c329e054ef8a77753b929db54ed0a76353af29d690eaaa75053a5a9d194e82a73c539ba9cc94e5aa7285391a9c794e32a7145
|5,0=>0x4b3b258592ba895764a8b252d928ca940649d324d1925cc9286491aa475922ec9116485b24195200c8fa647aaa3bd91d2c8e3646eb236151a4c8cc6463323019174c8b46457322a19144c89c644b322455116c885643fb21e590e6c86d6433b218590b6c85744292a131908cc840641d320d1905cc828641132071902cc8106405320118ffcc7f95
|5,1=>0x570b2b6d95aacacf6564b2b0d957acab76558b2aad954aca9f654cb2a4d951aca876540b29ed94eaca6f6534b298d94baca576528b292d948aca3f651d2a8d1945eaa296511b2875942eca116505b28159400a9fa64fa327b993d0c9e264ee3275993a0c9ca64e2326f99370c9b264d6326999340c99a64ca326399310c98264be325d992e2a96d4
|5,2=>0x62db3155989ecc496621b30f5986ecc316615b3095983ecc196609b3035980ecc0165fdb2fd957e0cbea65f232f7997b0cbd355e6b2f1d9782cbbb65dab2ebd9752cba455cf32e619724cb8c65c3aae0596f6cb7565b7b2da596c6cb5d65abb2d459696cb45659fb2ce9566aab2f6594b2c8d963acb176588b2c2d960acaff657cb2bcd95dacae76
|5,3=>0x6ea337399b90cdc266de336d99b60cdaa66d2336799b30cd9266c63361d5b02cd7b66bab35bd9ad2cd6366aeb355d9aa2cd4b66a32b5019a74cd346697334a19a44cd1d568bb34459a16cd05667fb33e599e6cced6673b338599b6ccd56668a3331598cccc1565db32d5995ecca96651b3275992ecc916645b321598fecc796639b31b598cecc616
|5,4=>0x1bc0adda6
|6,0=>0x7b2bbd815eb6af5657a7bbd295e8aaf3e779c33cc99e56ef26579033c6d5e2caf0f7784b3c0d9dfacef8577933bb19dceaee0776d33b4ddd98eec5775fb3ae1dd64ceab7752b3a79dd2eee916745b3a159cfcee786738bb9ad9cccae60672d339519c9eae4967213b8eddc6ace2f6714b388d9c3cae1777083b825dc08adfe66fbbb7c59bd6cde56
|6,1=>0x7f033f65dfa6cfcc77e2bbf015f74cfb377d63be999f42af9a77ca33e399f10cf8267beabde15ee2ef6c5
|7,0=>0x2068d02e681434089a038d016680834029a008cffe67fc33fc99fd8cfe66
|8,0=>0x103a5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 364 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x302801070030295082103029030285082101070020210302b0302a0408503028030290329a451cd030280302b0302a0302b0302a0302b0302a508210302903028030290302801070030290302803029010700302903028451cd030290302b0302a010700302903028010700302b0302a030290302b0302a0202002021030280107003029030280302903028010700302b0302a010700302b0302a0302b0302a
|1=>0x3013030120302b0302a994c7020290202803029030280302b0302a020210302802028030280302b0302a03028030290302903028020290107003029040850302803029030280302b0302a030290202103028032980229b040290302803029030280302904085030280302b03028020200302a020200107003029014ac0202842010030210302b5336f040280402902023010700302903028030280302803029
|2=>0x3028030290302801023020290408503028030290302803029030280302b0302a02020030290302b0302a0302201070030290302b0302a010709e829620290301001010030280302803028030280438d0202b040290302302298040290302b0302b0302a03029030280107004059030280202b040850302803028030280202a03028160870202103028030230302903029030281288502020030280302393c85
|3=>0x208703028030290202201070021c70e0230302903028030290302803029030280302b0302a020230302b0302a0229b0302803029030280e0b00202103029020220408503028030290302803028030290302803029010b0030290344f0438d0202b04029030100302b0302a040850302803029098110302b0302801018020290302802022118210e010030290302b03028020230107003028040850302803028
|4=>0x202202087030280202b0302b0302b030280302b0e0200302902087030280408703028040850302804029020230302a0302b0402a0302b0302b0302b0e010030295336f0402804029030290302b0302a0302a0202103029040850302b0302a04085030280302803029030280202101070030230202201070040850302803029030280232f0402a0302b0302b02022010700202102087030280302b0302804059
|5=>0x302904028040290302b0402802085030280236f0402803028030280302b020290302b0338f0202b0302b0208503028030110301003013030120302b044c50202862029030100302b04485030120202a020200302a0302b020220302a0302b0402902298040290438d0202b0229b0302b0102302029040290302b030670402a0e01303029020210302a041cd0302a020290202903028021cf0302a041cf0302a
|6=>0x302a0302b030100402a030280301202029020280202b040280202a04029030290301102029020290302b020200302802029030230302b0202103028030230202b020290202a0302b0e02303029021cd0302a0302b03023030290131403011020290202802021
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0xd30000000182000051000000000004101c40a4000000000000000000000000000000000104000000000000004400000000000000000000000000000000000000000000000000000000000000000002
|4,1=>0x6500001810000000000000000000000000000000002c41510000000000000000000000000000004c80000000000000000000000000024200000000000000000000000000000000000020400000000000000000000000000000
|4,2=>0x16a000000000015900000000000000a48502000000000000000000000004c40001210000000000000000000000000000004620001090000000000100800000000000000000001f10000000000000000074800000000000000000000000000000000
|4,3=>0xe8800000000000007220000000000000372000000000000000000000003520000000664000000000000000000000000000000000000000000000000000000000000000000000000c8400031100000000000000000000000000
|4,4=>0xf04000000000000000000000000000000000000000000000
|5,0=>0x1f08f2600000000000007723a91cc8e426f337080000006d13591a4800000000000000006633211888be65c30000000b625922c09588000551000000000054129100009e6000269000094647323080008a2432000000084200000010440003f21f080000003d1
|5,1=>0x641b1c58c20000003108000c316093004000bf15e92ec9724b725a90000000b3258900015e4000561aa89522000000298d48400000028c4000a2100028440009e34e8a68c0009824b8a58400095149900012068f14708001184000000224d0e4852000208d0227e3
|5,2=>0x7b8bd480000007a08000000f310000001e24f017710001da2ec10003a8800000000039cc000e6100000000000000000001c84e22708b7c8000de16e1364dae40000003549a64000690b408000cf1669000000000066080000000000000000000cb10000000000000
|5,3=>0x90180000000008f880023a40008e080000000008d100000000008c145c62a400000000000000008a0800000000089880022431020004388000000000430a126000840c1c4001061000000206702100040440000000003f8c000fd100000000000000000001f64f83
|5,4=>0x2466000
|6,0=>0xbe0dec6f257720005d86ea3741b915c0ade2000b695acad25681b31590ac62000b0958040015e2ae8d6cab43591ab90002aa5541a98d44aa034f1a6952ca925472a30d146883422a014fc67a53b29d0ce0a6c53429914c080012f19694b040012b1950ca46503262
|6,1=>0xcd0e647303962ca8e507263912c7963871a38c1c51620b0e3852c19604afe57d2
|7,0=>0x3503a71d30e947483a31d10e8474039f1cf0e7473839b1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x4582241100830408200080021010007c03a01b00d006002c014008804001e00e0068030016009004001c00a0040018008002000
|1=>0x245922890040820310004bc24e0cf867431a18b0c3861830a1840c0846421a10c0840414202100071828013e09d04a024412008e
|2=>0x8cbc62e3111818c0447620108f846c2020330114de267531490d450a08100a8044001aa8b1e58b2c4940097a4ab250127c93a492
|3=>0x56feb5f5abacdd65eb0151d8cfc676337198
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
|3,1=>0
|4,0=>0x4380000800000080400700000000800000000008400000040000004080400408001000808b8000002020010000040008000000000438000000000400080000000000000000100003800200000021c08000000001408000001c000000008000387070000004000000000102000000001
|4,1=>0x83800000040000800c800000707001020004000013200080000000000000100000000001000000100001c5c01a080000000380000e00219060000002100000004c800400000000008002102000000002001038002000002e0000000008070000004000400000000000000000
|4,2=>0xc8000000000000200003800000080070010700080000000000000064000040020004002000008380
|5,0=>0x5204d000048c9702a02170a0d2010a000014200080120438700aa180013801a012c0080e24005032c00498002972e0030008140811caa89c0020e0e0000201021820d4c002171e4c0000800d150a147830000b813454046000004b5600a044c0111c18002010000b80005c0052000217
|5,1=>0x2380003400c001c000000200000026808000003847000000140038700040000004f005e1c01000114e500e870008a800100107041c0091c34040072e6403a000040e021c1560e3c00000040390000000080008174047017aa560000040802e0401736000002e000000e000042000000
|5,2=>0xe00
|6,0=>0x2069c903442d864060304b882bebf72a1f02febc7232a181c0a67bec7718a3d140080cd9c02e54f0eb2903af02549edb7d36aaa402a673682e56a0025a1351715f5d773406a3b67237
|7,0=>0xad267105dfc2d2f3fcefcb5f
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 13 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_15_16,7,runOps true dzo_15_16 (0,roots_15) ops)] else [])++(if pm.testBit 1 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 2 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 3 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 4 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 5 then [(dzo_13_16,4,runOps true dzo_13_16 (0,roots_13) ops)] else [])++(if pm.testBit 6 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])++(if pm.testBit 7 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])++(if pm.testBit 8 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 9 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 10 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 11 then [(dzo_11_16,4,runOps true dzo_11_16 (0,roots_11) ops)] else [])++(if pm.testBit 12 then [(dzo_27_4,5,runOps true dzo_27_4 (0,roots_27) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_13_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_11_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_15_16 7 s (0,roots_15) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_15_48_16 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 7 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 7 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 64 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_64:∀ i,64 ≤ i → i < 128 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_128:∀ i,128 ≤ i → i < 131 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 3 128=true)
private theorem z3:∀ i,0 ≤ i → i < 131 → Z 3 i=true:=(range_split z3_0 (range_split z3_64 z3_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 256 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_256:∀ i,256 ≤ i → i < 302 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 46 256=true)
private theorem z4:∀ i,0 ≤ i → i < 302 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 (range_split z4_192 z4_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 258 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 2 256=true)
private theorem z5:∀ i,0 ≤ i → i < 258 → Z 5 i=true:=(range_split (range_split z5_0 z5_64) (range_split z5_128 (range_split z5_192 z5_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 84 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 20 64=true)
private theorem z6:∀ i,0 ≤ i → i < 84 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 14 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 14 0=true)
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
def isoMv_47_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_47_16:Lower true dom_47 roots_47 goal_47_16 9:=lower_iso isoMv_47_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_31_32
theorem lowS_62_1:Lower true dom_62 roots_62 goal_62_1 6:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5050505050505050,2,6)] (by decide +kernel) (by decide +kernel) lowS_58_1
theorem lowS_61_2:Lower true dom_61 roots_61 goal_61_2 6:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3030303030303030,0,4)] (by decide +kernel) (by decide +kernel) lowS_57_2
def isoMv_15_32:List (Nat × Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 4:=lower_iso isoMv_15_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_46_1:=0xaaaa0000aaaa
def gzo_46_1_1:=0xaa8800008880
theorem lowSh_46_1_1:Lower true dzo_46_1 roots_46 gzo_46_1_1 5:=lower_iso (d1:=dom_46) (roots1:=roots_46) (T1:=goal_46_1) [(dom_46,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_1
def dzo_39_8:=0xff000000ff00
def gzo_39_8_8:=0xea000000c800
theorem lowSh_39_8_8:Lower true dzo_39_8 roots_39 gzo_39_8_8 4:=lower_iso (d1:=dom_39) (roots1:=roots_39) (T1:=goal_39_8) [(dom_39,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_8
def dzo_15_32:=0xffff00000000
def gzo_15_32_32:=0xeac800000000
theorem lowSh_15_32_32:Lower true dzo_15_32 roots_15 gzo_15_32_32 4:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_32) [(dom_15,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
namespace S_47_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,11),(3,35),(4,6),(5,7),(9,11),(9,41),(10,11),(10,14),(12,14),(13,15),(13,45),(33,35),(33,41),(34,35),(34,38),(36,38),(37,39),(37,45),(40,41),(42,43),(42,46),(44,45),(44,46)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_47.map (· &&& dom_47)
def goalM:Nat:=goal_47_0 &&& dom_47
def NN:Nat → Nat
|3=>2
|4=>4
|5=>4
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0xcbf2de123c55207c
|4,0=>0x6c93ca6d6acb8a7f68c9c2e817e430ae
|5,0=>0xf57e7faba2db35a4578aea252ac37c4c
|6,0=>0x3b576e79
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc0c00000c0cff0000000000cc000000cc0033330000000033000000330000cc000000ccffcc0000ff0033ff00000000f3f00000f3f0ff000000ff00aaaa0000aaaa33330000ccccffff00000000f0f00000f0f0cccc0000ccccaa880000aa00
|_,_=>0
def stPool:Nat → Nat
|0=>0x362153615f36e2153621d536215c325ba39215621583671562543210
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x11004
|4,0=>0x5d52535485
|5,0=>0xb9686899c6
|6,0=>0x335
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 16 then fld (dictB (i / 512) (i / 32 % 16)) 48 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 10 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x21987
|_=>0
def opOffB:Nat → Nat → Nat
|5,0=>0x440001
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 6 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf4310
|_=>0
def pmB:Nat → Nat → Nat
|5,0=>0x4d9
|6,0=>4
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 1 then [(dzo_46_1,5,runOps true dzo_46_1 (0,roots_46) ops)] else [])++(if pm.testBit 2 then [(dzo_39_8,4,runOps true dzo_39_8 (0,roots_39) ops)] else [])++(if pm.testBit 3 then [(dzo_15_32,4,runOps true dzo_15_32 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_47 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_39_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_32_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_43 5 s (0,roots_43) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_47 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43_0 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_47==dom_47) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 goalM v ys):RunD true dom_47 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 2 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 4 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 4 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 4 0=true)
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
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8_8:=0xfe00ea00ea00c800
theorem lowSh_55_8_8:Lower true dzo_55_8 roots_55 gzo_55_8_8 9:=lower_iso (d1:=dom_55) (roots1:=roots_55) (T1:=goal_55_8) [(dom_55,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55_8
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16_16:=0xfee80000eae00000
theorem lowSh_47_16_16:Lower true dzo_47_16 roots_47 gzo_47_16_16 9:=lower_iso (d1:=dom_47) (roots1:=roots_47) (T1:=goal_47_16) [(dom_47,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_47_16
def dzo_31_32:=0xffffffff00000000
def gzo_31_32_32:=0xfee8eac800000000
theorem lowSh_31_32_32:Lower true dzo_31_32 roots_31 gzo_31_32_32 9:=lower_iso (d1:=dom_31) (roots1:=roots_31) (T1:=goal_31_32) [(dom_31,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_31_32
def dzo_62_1:=0xaaaaaaaaaaaaaaaa
def gzo_62_1_1:=0xaaa8aa88aaa08880
theorem lowSh_62_1_1:Lower true dzo_62_1 roots_62 gzo_62_1_1 6:=lower_iso (d1:=dom_62) (roots1:=roots_62) (T1:=goal_62_1) [(dom_62,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_62_1
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2_2:=0xccc8c8c8c8c0c8c0
theorem lowSh_61_2_2:Lower true dzo_61_2 roots_61 gzo_61_2_2 6:=lower_iso (d1:=dom_61) (roots1:=roots_61) (T1:=goal_61_2) [(dom_61,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_61_2
namespace S_63_0
def pairsG:List (Nat × Nat):=[(2,6),(3,7),(3,11),(3,35),(4,6),(5,7),(5,21),(9,11),(9,25),(9,41),(10,11),(10,14),(12,14),(13,15),(13,29),(13,45),(17,21),(17,25),(18,22),(19,23),(19,27),(19,51),(20,21),(20,22),(24,25),(26,27),(26,30),(26,58),(28,29),(28,30),(28,60),(33,35),(33,41),(34,35),(34,38),(36,38),(37,39),(37,45),(37,53),(40,41),(42,43),(42,46),(42,58),(44,45),(44,46),(44,60),(49,51),(49,53),(49,57),(50,51),(50,54),(50,58),(52,53),(52,54),(52,60),(56,57),(56,58),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffffffffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_63.map (· &&& dom_63)
def goalM:Nat:=goal_63_0 &&& dom_63
def NN:Nat → Nat
|7=>13
|8=>32
|9=>8
|10=>1
|_=>0
def HT:Nat → Nat → Nat
|7,0=>0xfacb1233e5f93c5de2fd77acdd1a5b1cdcc9e4eeceafb2ffb83183a0b574c2ce9c7c55c094db7b8630109ec32dd1ad8b2c05dd8b
|8,0=>0xe9e3dfc4e5f93c5de4ae95b3e4a7316bce4ad0efcc1168e4ba47a1389bd7494f8f533e867751c4e17596bf2d73d637ce67fcab565bef74535385f47e4eed60524e875dd94b9779ef477294e63abc111938019ffe2b74cc1f299e865d28f2496d18bc18ae178e4e9e16f1fadc141f8fdd139e8f960eccb740052b8f99034547c7
|9,0=>0xf92dd199ba47a1388f8b65ae56713ef94b36c4a0448b584228f2496d159b56a6
|10,0=>0x69904ec9
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x404040404040404f8f8f8f8f8f8f8f80c0c0c0c0c0c0c0caeaeaeaeaeaeaeaef4f4f4f4f4f4f4f4f2f2f2f2f2f2f2f237370000373700005454545454545454fcfcfcfcfcfcfcfca8a8a8a8a8a8a8a8c8c8c8c8c8c8c8c8fefefefe00000000fafafafafafafafad8d8d8d8d8d8d8d8fefe0000fefe00004444444444444444c4c4c4c4c4c4c4c4222222222222222208080808080808080a0a0a0a0a0a0a0af7f70000f7f7000088888888888888886666666666666666ff00ff00ff00ff00fefefefefefefefeeeeeeeeeeeeeeeeeffffffff00000000ffff0000ffff0000fe00fe00fe00fe00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa
|0,1=>0x3232323232323232a2a2a2a2a2a2a2a2020202020202020277770000777700000e0e0e0e0e0e0e0ecececececececece
|_,_=>0
def stPool:Nat → Nat
|0=>0x51086c20401442020403451081c20401442130403051080862851084c218114421a08100520204064510808101614420219514420224421408100510809204014420200914844204014420224e1442023ce1482c20401442021891440c2040
|1=>0x4014420204060510808102314808102214421708101614421308138510808102114420204f0051080a004014421308100e14420240e1442020407c510878204014420204e30510808170014421708101814420201038510808100e144202055
|2=>0x51080810051085c20401442021810051084c204014420204030510808101d14420204028510808100e14420204040510808600a14420204058510808102514420204090510808600e144202181305108086
|_=>0
def stOffB:Nat → Nat → Nat
|7,0=>0x4962138f186ea31615389183cc18609303180cc006
|8,0=>0x943c85e34f137863c15dfcef77783ba99c50db76a3b35d8cebe85c32c5d54ea374e3a5211ae8673fb9e1ce2e6a731b9758ace4f7
|9,0=>0xb03d65ea4f4b7a23cf5e6cf2f7
|10,0=>0x1676
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 38 then fld (dictB (i / 512) (i / 32 % 16)) 64 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 6 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 13 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x40807508197030814103040802b04013040804241040c1300808219040423108081010400201040423904084574c102015d8d7030815304080410118ac101040051c08641014cec201040862b040410010702190405039040c10204cc202040843704c020218ac101040081c0864101
|1=>0x205040420108082060400102040c1010401700081530708040770818139040820204041390409703081423a040842b04017000814201040821a0404133080813108082010408103040930608042290400202
|_=>0
def opOffB:Nat → Nat → Nat
|7,0=>0x24342678cd99832a648c798c312618c19803
|8,0=>0xca58cb095f2ba56cac9572aa54ca894f29a52ca494728a50ca093f27a4ec9c93726a4cc9892f25a4ac949272
|9,0=>0xdc3b4760eb1d43a4740e71
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 14 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 63),wireSAt ((code >>> 8) &&& 63))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 11 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x257b27f49fa3fd17a83f41d96f4a7e4bf25e92e487e43b15e88f437a13f09e84ec1f20bf05e82ec0fe07901f80f4072000
|_=>0
def pmB:Nat → Nat → Nat
|7,0=>0x1d51c8d451f71ba4d
|8,0=>0x430e24528d672ba6c468c1c7115918c9c6d34f2c
|9,0=>0x5d93011773
|10,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 5 (j % 128);fld (pmPalB (k / 32)) 13 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_55_8,9,runOps true dzo_55_8 (0,roots_55) ops)] else [])++(if pm.testBit 1 then [(dom_62,6,runOps true dom_62 (0,roots_62) ops)] else [])++(if pm.testBit 2 then [(dom_61,7,runOps true dom_61 (0,roots_61) ops)] else [])++(if pm.testBit 3 then [(dom_59,8,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 4 then [(dzo_47_16,9,runOps true dzo_47_16 (0,roots_47) ops)] else [])++(if pm.testBit 5 then [(dzo_31_32,9,runOps true dzo_31_32 (0,roots_31) ops)] else [])++(if pm.testBit 6 then [(dzo_57_4,5,runOps true dzo_57_4 (0,roots_57) ops)] else [])++(if pm.testBit 7 then [(dzo_62_1,6,runOps true dzo_62_1 (0,roots_62) ops)] else [])++(if pm.testBit 8 then [(dzo_61_2,6,runOps true dzo_61_2 (0,roots_61) ops)] else [])++(if pm.testBit 9 then [(dom_47,7,runOps true dom_47 (0,roots_47) ops)] else [])++(if pm.testBit 10 then [(dzo_58_1,5,runOps true dzo_58_1 (0,roots_58) ops)] else [])++(if pm.testBit 11 then [(dzo_57_2,5,runOps true dzo_57_2 (0,roots_57) ops)] else [])++(if pm.testBit 12 then [(dzo_46_1,5,runOps true dzo_46_1 (0,roots_46) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_63 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_55_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_62_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_61_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_59_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_47_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_31_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_62_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_61_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowS_47_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_58_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_55_8 9 s (0,roots_55) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_63 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_55_8_8 h
def ori (zs:List Nat):List Nat:=zs
theorem ori_ok {v ys} (h:RunD true dom_63 goalM v ys):RunD true dom_63 goalM v (ori ys):=h
def Z (s:Nat):=barP true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
private theorem z6:∀ i,0 ≤ i → i < 0 → Z 6 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 13 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 13 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 32 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 32 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9:∀ i,0 ≤ i → i < 8 → Z 9 i=true:=span_ok (by decide +kernel:span (Z 9) 8 0=true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩], 17⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_sz : wit.size ≤ 11 + 1 := by decide
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_63_0.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  signed_to_mono6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63_0 11 wit wit_mono wit_sz wit_ev hT6 (by decide) (by unfold IsConst; decide) lowS_63_0
end PEqualNP.Outside.L_meta_41790_aux
theorem PEqualNP.Outside.L_meta_41790 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3940600000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_41790_aux.main
