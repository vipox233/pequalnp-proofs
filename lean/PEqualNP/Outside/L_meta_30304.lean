import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30304

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
section RunSection
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
end RunSection
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

theorem lower_mask_target {u : Bool} {d T L : Nat} {roots : List Nat}
    (h : Lower u d roots T L) : Lower u d roots (T &&& d) L := by
  intro p bank hp ha
  exact h p bank hp (avail_of_eq (by rw [Nat.and_assoc, Nat.and_self]) ha)

theorem lower_masked_iso {d1 d2 T1 T2 L1 L2 : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1 &&& mask256 = d1) (hd : applyMoves ms d2 = d1)
    (hT : applyMoves ms (T2 &&& d2) = T1 &&& d1)
    (hroots : roots2.all (fun r => availB true d1 roots1 (applyMoves ms r)) = true)
    (h : Lower true d1 roots1 T1 L1) (hle : L2 ≤ L1) :
    Lower true d2 roots2 T2 L2 := by
  have h' := lower_iso ms hok hd1 hd hT hroots (lower_mask_target h)
  intro p bank hp ha
  exact hle.trans (h' p bank hp (avail_of_eq (by rw [Nat.and_assoc, Nat.and_self]) ha))

namespace Prior28586
open PEqualNP.Outside.L_meta_30304

def dom_102 : Nat := 0x55000000550000005500000055

def dom_103 : Nat := 0xff000000ff000000ff000000ff

def dom_113 : Nat := 0x30003000300030003000300030003

def dom_114 : Nat := 0x50005000500050005000500050005

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f

def dom_117 : Nat := 0x330033003300330033003300330033

def dom_118 : Nat := 0x550055005500550055005500550055

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff

def dom_162 : Nat := 0x50000000500000000000000000000000500000005

def dom_166 : Nat := 0x550000005500000000000000000000005500000055

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

def dom_51 : Nat := 0xf000f000f000f

def dom_81 : Nat := 0x300030000000000030003

def dom_83 : Nat := 0xf000f00000000000f000f

def dom_85 : Nat := 0x3300330000000000330033

def dom_87 : Nat := 0xff00ff0000000000ff00ff

def dzo_115_4:=0xf000f000f000f000f000f000f000f0

def dzo_166_16:=0x5500000055000000000000000000000055000000550000

def dzo_167_16:=0xff000000ff0000000000000000000000ff000000ff0000

def dzo_226_16:=0x5000000050000000500000005000000050000000500000005000000050000

def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000

def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000

def dzo_51_4:=0xf000f000f000f0

def goal_102 : Nat := 0xfcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000

def goal_103 : Nat := 0xfefefefefefefefeeeeeeeee00000000fefefefefefefefeeeeeeeee00000000

def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000

def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000

def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000

def goal_117 : Nat := 0xfffffafafffffafaaaaaaaaaaaaa0000fffffafafffffafaaaaaaaaaaaaa0000

def goal_118 : Nat := 0xfffffcfcfffffcfccccccccc00000000fffffcfcfffffcfccccccccc00000000

def goal_119 : Nat := 0xfffffefefffffefeeeeeeeeeaaaa0000fffffefefffffefeeeeeeeeeaaaa0000

def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000

def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000

def goal_167 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfceeeeeeee00000000eeeeeeee00000000

def goal_183 : Nat := 0xfffffffffefefcfcfffffffffefefcfceeeeeeeeaaaa0000eeeeeeeeaaaa0000

def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000

def goal_195 : Nat := 0xffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeee0000000000000000

def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000

def goal_199 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfefefefefefefefe0000000000000000

def goal_209 : Nat := 0xffffffffffffffffaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_210 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccc0000000000000000

def goal_211 : Nat := 0xffffffffffffffffeeeecccceeeeccccffffeeeeffffeeeeaaaa0000aaaa0000

def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f00000000000000000

def goal_213 : Nat := 0xfffffffffffffffffafaf0f0fafaf0f0fffffafafffffafaaaaa0000aaaa0000

def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffcfcfffffcfc0000000000000000

def goal_215 : Nat := 0xfffffffffffffffffefefcfcfefefcfcfffffefefffffefeaaaa0000aaaa0000

def goal_226 : Nat := 0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccc00000000

def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f00000000000000000

def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfccccccccc00000000

def goal_231 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfefefefefefefefeeeeeeeee00000000

def goal_240 : Nat := 0xffffffffffffffffffffffff00000000ffff0000ffff00000000000000000000

def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffccccffffcccccccccccc00000000

def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeccccffffeeeeffffeeeeeeeeeeeeaaaa0000

def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffff0f0fffff0f00000000000000000

def goal_245 : Nat := 0xfffffffffffffffffffffffffafaf0f0fffffafafffffafaaaaaaaaaaaaa0000

def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffcfcfffffcfccccccccc00000000

def goal_247 : Nat := 0xfffffffffffffffffffffffffefefcfcfffffefefffffefeeeeeeeeeaaaa0000

def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000

def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000

def goal_85 : Nat := 0xfffffafafffffafaaaaa0000aaaa0000fffffafafffffafaaaaa0000aaaa0000

def goal_87 : Nat := 0xfffffefefffffefeaaaa0000aaaa0000fffffefefffffefeaaaa0000aaaa0000

def gsh_115_4:=0xf000f000f000f000e000e000a0000

def gsh_166_16:=0x550000005400000000000000000000004400000000

def gsh_167_16:=0xff000000fe0000000000000000000000ee000000aa

def gsh_226_16:=0x500000005000000050000000400000005000000050000000400000000

def gsh_230_16:=0x5500000055000000550000005400000055000000550000004400000000

def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000ee000000aa

def gsh_51_4:=0xe000e000a0000

def gzo_115_4:=0xf000f000f000f000e000e000a00000

def gzo_166_16:=0x5500000054000000000000000000000044000000000000

def gzo_167_16:=0xff000000fe0000000000000000000000ee000000aa0000

def gzo_226_16:=0x5000000050000000500000004000000050000000500000004000000000000

def gzo_230_16:=0x55000000550000005500000054000000550000005500000044000000000000

def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000ee000000aa0000

def gzo_51_4:=0xe000e000a00000

def isoMvS_226 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]

def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_51
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (2,34), (3,19), (3,35), (16,17), (18,19), (18,50), (32,33), (32,34), (48,49), (48,50)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x5ac2a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000f0000000f0000c000c000c000ca000a000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 52 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 6 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 3), wireSAt ((code >>> 4) &&& 3)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0
|_=>0
def pmB : Nat → Nat → Nat
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_51 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_51 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_51 goalM v ys) : RunD true dom_51 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_51 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_51 roots_51 goal_51 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_51

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := S_51.noCircuit

theorem lowS_zo_115_4_51:Lower true dzo_115_4 roots_115 gzo_115_4 5:=lower_iso (d1:=dom_115) (roots1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_115_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_51)

theorem lowS_zo_51_4_51:Lower true dzo_51_4 roots_51 gzo_51_4 4:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=gsh_51_4) [(dom_51,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_51_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_51)

def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

end Prior28586

namespace Prior28450
open PEqualNP.Outside.L_meta_30304

def dom_101 : Nat := 0x33000000330000003300000033

def dom_113 : Nat := 0x30003000300030003000300030003

def dom_114 : Nat := 0x50005000500050005000500050005

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f

def dom_117 : Nat := 0x330033003300330033003300330033

def dom_118 : Nat := 0x550055005500550055005500550055

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333

def dom_53 : Nat := 0x33003300330033

def dom_81 : Nat := 0x300030000000000030003

def dzo_113_4:=0x300030003000300030003000300030

def dzo_117_8:=0x33003300330033003300330033003300

def dzo_172_64:=0x111100001111000000000000000000001111000011110000000000000000

def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000

def dzo_188_64:=0x1111111111111111000000000000000011111111111111110000000000000000

def dzo_189_64:=0x3333333333333333000000000000000033333333333333330000000000000000

def dzo_209_4:=0x300030000000000030003000000000003000300000000000300030

def dzo_209_8:=0x3000300000000000300030000000000030003000000000003000300

def dzo_229_8:=0x330000003300000033000000330000003300000033000000330000003300

def dzo_241_12:=0x3000300030003000300030003000300030003000300030003000300030003000

def dzo_241_4:=0x30003000300030003000300030003000300030003000300030003000300030

def dzo_241_8:=0x300030003000300030003000300030003000300030003000300030003000300

def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300

def dzo_81_4:=0x3000300000000000300030

def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000

def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000

def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000

def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000

def goal_117 : Nat := 0xfffffafaffffaaaafafafafaaaaa0000fffffafaffffaaaafafafafaaaaa0000

def goal_118 : Nat := 0xfffffcfcffffccccfcfcfcfc00000000fffffcfcffffccccfcfcfcfc00000000

def goal_119 : Nat := 0xfffffefeffffeeeefefefefeaaaa0000fffffefeffffeeeefefefefeaaaa0000

def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f000000000f0f0f0f000000000

def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fafafafa00000000fafafafa00000000

def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafafafaaaaa0000fafafafaaaaa0000

def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0f0f0f0f000000000f0f0f0f000000000

def goal_189 : Nat := 0xfffffffffffffff0fffffffffffffff0fafafafaaaaa0000fafafafaaaaa0000

def goal_213 : Nat := 0xfffffafafffffafafffff0f0fffff0f0ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_215 : Nat := 0xfffffefefffffefefffff0f0fffff0f0ffffeeeeffffeeeeaaaa0000aaaa0000

def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ffff0000ffff00000000000000000000

def goal_221 : Nat := 0xfffffffafffffffafffffff0fffffff0ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_229 : Nat := 0xfffffffffafafafafffffffff0f0f0f0fafafafaaaaaaaaafafafafa00000000

def goal_233 : Nat := 0xffffffffffaaffaaffffffffff00ff00aaaaaaaaaaaaaaaaaaaaaaaa00000000

def goal_237 : Nat := 0xfffffffffffafffafffffffffff0fff0fafafafaaaaaaaaafafafafa00000000

def goal_241 : Nat := 0xffffffffffffaaaaffffffffffff0000ffffaaaaffffaaaaaaaaaaaaaaaa0000

def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffff0f0ffff0000f0f0f0f000000000

def goal_245 : Nat := 0xfffffffffffffafafffffffffffff0f0fffffafaffffaaaafafafafaaaaa0000

def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffff0000ffff00000000000000000000

def goal_249 : Nat := 0xffffffffffffffaaffffffffffffff00ffffaaaaffffaaaaaaaaaaaaaaaa0000

def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffff0f0ffff0000f0f0f0f000000000

def goal_253 : Nat := 0xfffffffffffffffafffffffffffffff0fffffafaffffaaaafafafafaaaaa0000

def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000

def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000

def gsh_113_4:=0x30003000300020003000300020000

def gsh_117_8:=0x330032003300220032003200220000

def gsh_172_64:=0x11110000111000000000000000000000101000000000

def gsh_173_64:=0x33330000333200000000000000000000323200002222

def gsh_188_64:=0x111111111111111000000000000000001111101011110000

def gsh_189_64:=0x333333333333333200000000000000003333323233332222

def gsh_209_4:=0x30003000000000003000300000000000300020000000000020000

def gsh_209_8:=0x30003000000000003000300000000000300020000000000020000

def gsh_229_8:=0x3300000033000000330000003300000032000000220000003200000000

def gsh_241_12:=0x3000300030003000300030003000300030003000300020003000300020000

def gsh_241_4:=0x3000300030003000300030003000300030003000300020003000300020000

def gsh_241_8:=0x3000300030003000300030003000300030002000300020002000200020000

def gsh_245_8:=0x33003300330033003300330033003300330032003300220032003200220000

def gsh_81_4:=0x300020000000000020000

def gzo_113_4:=0x300030003000200030003000200000

def gzo_117_8:=0x33003200330022003200320022000000

def gzo_172_64:=0x111100001110000000000000000000001010000000000000000000000000

def gzo_173_64:=0x333300003332000000000000000000003232000022220000000000000000

def gzo_188_64:=0x1111111111111110000000000000000011111010111100000000000000000000

def gzo_189_64:=0x3333333333333332000000000000000033333232333322220000000000000000

def gzo_209_4:=0x300030000000000030003000000000003000200000000000200000

def gzo_209_8:=0x3000300000000000300030000000000030002000000000002000000

def gzo_229_8:=0x330000003300000033000000330000003200000022000000320000000000

def gzo_241_12:=0x3000300030003000300030003000300030003000300020003000300020000000

def gzo_241_4:=0x30003000300030003000300030003000300030003000200030003000200000

def gzo_241_8:=0x300030003000300030003000300030003000200030002000200020002000000

def gzo_245_8:=0x3300330033003300330033003300330033003200330022003200320022000000

def gzo_81_4:=0x3000200000000000200000

def isoMvS_233 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]

def isoMvS_237 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]

def isoMvS_241 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]

def isoMvS_249 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]

def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_51 (by decide +kernel)

theorem lowS_101 : Lower true dom_101 roots_101 goal_101 4 :=
  lower_masked_iso [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_53 (by decide +kernel)

theorem lowS_zo_229_8_101:Lower true dzo_229_8 roots_229 gzo_229_8 5:=lower_iso (d1:=dom_229) (roots1:=roots_229) (T1:=gsh_229_8) [(dom_229,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_229_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300000033000000330000003300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_101)

def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

namespace S_81
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (16,17), (16,80), (64,65), (64,80)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_81.map (· &&& dom_81)
def goalM : Nat := goal_81 &&& dom_81
def NN : Nat → Nat
|2=>1
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x9e3d8
|3,0=>0x9e3d8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30000000000000003000080008000000000008000b00030000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 82 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 6 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 3), wireSAt ((code >>> 4) &&& 3)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0
|_=>0
def pmB : Nat → Nat → Nat
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_81 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_81 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_81 == dom_81) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_81 goalM v ys) : RunD true dom_81 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_81 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_81 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_81 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_81 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_81 roots_81 goal_81 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_81

theorem lowS_81 : Lower true dom_81 roots_81 goal_81 4 := S_81.noCircuit

theorem lowS_zo_113_4_81:Lower true dzo_113_4 roots_113 gzo_113_4 5:=lower_iso (d1:=dom_113) (roots1:=roots_113) (T1:=gsh_113_4) [(dom_113,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_113_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_209_4_81:Lower true dzo_209_4 roots_209 gzo_209_4 5:=lower_iso (d1:=dom_209) (roots1:=roots_209) (T1:=gsh_209_4) [(dom_209,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_209_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_209_8_81:Lower true dzo_209_8 roots_209 gzo_209_8 5:=lower_iso (d1:=dom_209) (roots1:=roots_209) (T1:=gsh_209_8) [(dom_209,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_209_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_241_12_81:Lower true dzo_241_12 roots_241 gzo_241_12 6:=lower_iso (d1:=dom_241) (roots1:=roots_241) (T1:=gsh_241_12) [(dom_241,12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_241_12) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3000300000000000300030000000000030003000000000003000300000000,0,32),(0x3000300030003000300030003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_241_4_81:Lower true dzo_241_4 roots_241 gzo_241_4 6:=lower_iso (d1:=dom_241) (roots1:=roots_241) (T1:=gsh_241_4) [(dom_241,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_241_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3000300000000000300030000000000030003000000000003000300000000,0,32),(0x3000300030003000300030003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_81_4_81:Lower true dzo_81_4 roots_81 gzo_81_4 4:=lower_iso (d1:=dom_81) (roots1:=roots_81) (T1:=gsh_81_4) [(dom_81,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_81_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_81)

end Prior28450

namespace Prior27923
open PEqualNP.Outside.L_meta_30304

def dom_114 : Nat := 0x50005000500050005000500050005

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f

def dom_162 : Nat := 0x50000000500000000000000000000000500000005

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f

def dom_81 : Nat := 0x300030000000000030003

def dom_83 : Nat := 0xf000f00000000000f000f

def dzo_162_16:=0x500000005000000000000000000000005000000050000

def dzo_163_16:=0xf0000000f00000000000000000000000f0000000f0000

def dzo_209_32:=0x3000300000000000300030000000000030003000000000003000300000000

def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000

def dzo_226_16:=0x5000000050000000500000005000000050000000500000005000000050000

def dzo_227_16:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000

def dzo_81_32:=0x30003000000000003000300000000

def dzo_83_32:=0xf000f00000000000f000f00000000

def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000

def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeccccaaaa0000ffffeeeeffffeeeeeeeeccccaaaa0000

def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000

def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeecccccccc00000000cccccccc00000000

def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa0000

def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeccccaaaa0000eeeeccccaaaa0000

def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000

def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000

def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000

def goal_209 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaaaaaa0000aaaa0000

def goal_210 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccc0000000000000000

def goal_211 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffeeeeffffeeeeaaaa0000aaaa0000

def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeecccccccc00000000

def goal_240 : Nat := 0xffffffffffffffffffffffff00000000ffff0000ffff00000000000000000000

def goal_241 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffaaaaffffaaaaaaaa0000aaaa0000

def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffccccffffcccccccccccc00000000

def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffeeeeffffeeeeeeeeccccaaaa0000

def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000

def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000

def gsh_162_16:=0x50000000400000000000000000000000400000000

def gsh_163_16:=0xf0000000e00000000000000000000000e0000000a

def gsh_209_32:=0x30003000000000003000300000000000300020000000000020000

def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000c

def gsh_226_16:=0x500000005000000050000000400000005000000050000000400000000

def gsh_227_16:=0xf0000000f0000000f0000000e0000000f0000000f0000000e0000000a

def gsh_81_32:=0x300020000000000020000

def gsh_83_32:=0xf000e00000000000e000c

def gzo_162_16:=0x500000004000000000000000000000004000000000000

def gzo_163_16:=0xf0000000e00000000000000000000000e0000000a0000

def gzo_209_32:=0x3000300000000000300030000000000030002000000000002000000000000

def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000c00000000

def gzo_226_16:=0x5000000050000000500000004000000050000000500000004000000000000

def gzo_227_16:=0xf0000000f0000000f0000000e0000000f0000000f0000000e0000000a0000

def gzo_81_32:=0x30002000000000002000000000000

def gzo_83_32:=0xf000e00000000000e000c00000000

def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

theorem lowS_81 : Lower true dom_81 roots_81 goal_81 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_81 (by decide +kernel)

theorem lowS_zo_209_32_81:Lower true dzo_209_32 roots_209 gzo_209_32 5:=lower_iso (d1:=dom_209) (roots1:=roots_209) (T1:=gsh_209_32) [(dom_209,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_209_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_211_32_81:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

theorem lowS_zo_81_32_81:Lower true dzo_81_32 roots_81 gzo_81_32 4:=lower_iso (d1:=dom_81) (roots1:=roots_81) (T1:=gsh_81_32) [(dom_81,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_81_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_81)

def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

theorem lowS_zo_83_32_81:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso (d1:=dom_83) (roots1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_83_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc000c00000000000c000c,0,2)] (by decide +kernel) (by decide +kernel) lowS_81)

end Prior27923

namespace Prior29242
open PEqualNP.Outside.L_meta_30304

def dom_108 : Nat := 0x1111000011110000111100001111

def dom_109 : Nat := 0x3333000033330000333300003333

def dom_124 : Nat := 0x11111111111111111111111111111111

def dom_125 : Nat := 0x33333333333333333333333333333333

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333

def dzo_109_16:=0x33330000333300003333000033330000

def dzo_124_1:=0x22222222222222222222222222222222

def dzo_236_1:=0x222200002222000022220000222200002222000022220000222200002222

def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000

def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000

def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300

def dzo_252_1:=0x2222222222222222222222222222222222222222222222222222222222222222

def goal_108 : Nat := 0xffffffffff00ff00f0f0f0f000000000ffffffffff00ff00f0f0f0f000000000

def goal_125 : Nat := 0xffffffffffaaff00fafaf0f0aaaa0000ffffffffffaaff00fafaf0f0aaaa0000

def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeccccaaaa0000eeeeccccaaaa0000

def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaf0f0aaaa0000fafaf0f0aaaa0000

def goal_205 : Nat := 0xfffffffffffffffffafafafafafafafaff00ff00ff00ff000000000000000000

def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeeeeecccceeeeccccaaaa0000aaaa0000

def goal_217 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffaaff00ffaaff00aaaa0000aaaa0000

def goal_219 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffeeffccffeeffccaaaa0000aaaa0000

def goal_220 : Nat := 0xfffffffffffffffffffff0f0fffff0f0ff00ff00ff00ff000000000000000000

def goal_221 : Nat := 0xfffffffffffffffffffffafafffffafaffaaff00ffaaff00aaaa0000aaaa0000

def goal_236 : Nat := 0xfffffffffffffffffffffffff0f0f0f0ffffffffff00ff00f0f0f0f000000000

def goal_237 : Nat := 0xfffffffffffffffffffffffffafafafaffffffffff00ff00f0f0f0f000000000

def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafaffffffffaaaa0000fafaf0f0aaaa0000

def goal_248 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffff00ff000000000000000000

def goal_249 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffaaff00aaaa0000aaaa0000

def goal_252 : Nat := 0xfffffffffffffffffffffffffffff0f0ffffffffff00ff00f0f0f0f000000000

def goal_253 : Nat := 0xfffffffffffffffffffffffffffffafaffffffffffaaff00fafaf0f0aaaa0000

def gsh_109_16:=0x3333000033220000323200002222

def gsh_124_1:=0x11111111111111001111101011110000

def gsh_236_1:=0x111100001111000011110000111100001111000011000000101000000000

def gsh_236_16:=0x111100001111000011110000111100001111000011000000101000000000

def gsh_237_16:=0x333300003333000033330000333300003333000033220000323200002222

def gsh_245_8:=0x33003300330033003300330033003200330033003300330032003000220000

def gsh_252_1:=0x1111111111111111111111111111111111111111111111001111101011110000

def gzo_109_16:=0x33330000332200003232000022220000

def gzo_124_1:=0x22222222222222002222202022220000

def gzo_236_1:=0x222200002222000022220000222200002222000022000000202000000000

def gzo_236_16:=0x1111000011110000111100001111000011110000110000001010000000000000

def gzo_237_16:=0x3333000033330000333300003333000033330000332200003232000022220000

def gzo_245_8:=0x3300330033003300330033003300320033003300330033003200300022000000

def gzo_252_1:=0x2222222222222222222222222222222222222222222222002222202022220000

def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

end Prior29242

namespace Prior27921
open PEqualNP.Outside.L_meta_30304

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f

def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00

def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeccccaaaa0000eeeeccccaaaa0000

def gsh_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000f000e000c000a0000

def gzo_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000f000e000c000a000000

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

end Prior27921

namespace Prior27979
open PEqualNP.Outside.L_meta_30304

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f

def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeccffffeecceeeeaa00eeeeaa00

def goal_251 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeccffffeecceeeeeecceeeeaa00

def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

end Prior27979

namespace Prior28586
open PEqualNP.Outside.L_meta_30304

theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_101 (by decide +kernel)

theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_102

theorem lowS_81 : Lower true dom_81 roots_81 goal_81 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_81 (by decide +kernel)

theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_81 (by decide +kernel)

theorem lowS_194 : Lower true dom_194 roots_194 goal_194 4 :=
  lower_masked_iso [(0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_162 (by decide +kernel)

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c00000000000c000c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_81

theorem lowS_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffff0000ffff0000ffff0000ffff0000, 112)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_83 (by decide +kernel)

theorem lowS_85 : Lower true dom_85 roots_85 goal_85 5 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_83 (by decide +kernel)

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000cc00cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_85

theorem lowS_zo_226_16_162:Lower true dzo_226_16 roots_226 gzo_226_16 5:=lower_iso (d1:=dom_226) (roots1:=roots_226) (T1:=gsh_226_16) [(dom_226,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_226_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500000005000000000000000000000005000000050000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_162)

end Prior28586

namespace Prior27923
open PEqualNP.Outside.L_meta_30304

theorem lowS_114 : Lower true dom_114 roots_114 goal_114 4 :=
  lower_masked_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_102 (by decide +kernel)

theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_162 (by decide +kernel)

theorem lowS_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_masked_iso [(0xffffffff00000000ffffffff00000000, 96), (0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_195 (by decide +kernel)

theorem lowS_177 : Lower true dom_177 roots_177 goal_177 4 :=
  lower_masked_iso [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccccccccccccccccccccccccccc, 126)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_114 (by decide +kernel)

theorem lowS_194 : Lower true dom_194 roots_194 goal_194 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_194 (by decide +kernel)

theorem lowS_193 : Lower true dom_193 roots_193 goal_193 4 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_194 (by decide +kernel)

theorem lowS_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000000000000000a000000000000000a000000000000000a, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_194

theorem lowS_240 : Lower true dom_240 roots_240 goal_240 4 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccccccccccccccccccccccccccccccc, 126)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_114 (by decide +kernel)

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_83 (by decide +kernel)

theorem lowS_zo_162_16_162:Lower true dzo_162_16 roots_162 gzo_162_16 4:=lower_iso (d1:=dom_162) (roots1:=roots_162) (T1:=gsh_162_16) [(dom_162,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_162_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_162)

theorem lowS_zo_163_16_162:Lower true dzo_163_16 roots_163 gzo_163_16 5:=lower_iso (d1:=dom_163) (roots1:=roots_163) (T1:=gsh_163_16) [(dom_163,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_163_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa0000000a00000000000000000000000a0000000a,0,1)] (by decide +kernel) (by decide +kernel) lowS_162)

theorem lowS_zo_226_16_162:Lower true dzo_226_16 roots_226 gzo_226_16 5:=lower_iso (d1:=dom_226) (roots1:=roots_226) (T1:=gsh_226_16) [(dom_226,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_226_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500000005000000000000000000000005000000050000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_162)

theorem lowS_zo_227_16_162:Lower true dzo_227_16 roots_227 gzo_227_16 6:=lower_iso (d1:=dom_227) (roots1:=roots_227) (T1:=gsh_227_16) [(dom_227,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_227_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,0,1),(0xf0000000f00000000000000000000000f0000000f0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_162)

end Prior27923

namespace Prior28586
open PEqualNP.Outside.L_meta_30304

theorem lowS_114 : Lower true dom_114 roots_114 goal_114 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_114 (by decide +kernel)

theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_114

theorem lowS_166 : Lower true dom_166 roots_166 goal_166 5 :=
  lower_masked_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_163 (by decide +kernel)

theorem lowS_198 : Lower true dom_198 roots_198 goal_198 5 :=
  lower_masked_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_195 (by decide +kernel)

theorem lowS_199 : Lower true dom_199 roots_199 goal_199 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00000000000000aa00000000000000aa00000000000000aa, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_198

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 :=
  lower_masked_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_199 (by decide +kernel)

theorem lowS_226 : Lower true dom_226 roots_226 goal_226 5 :=
  lower_iso isoMvS_226 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_198

theorem lowS_240 : Lower true dom_240 roots_240 goal_240 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_240 (by decide +kernel)

theorem lowS_zo_166_16_166:Lower true dzo_166_16 roots_166 gzo_166_16 5:=lower_iso (d1:=dom_166) (roots1:=roots_166) (T1:=gsh_166_16) [(dom_166,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_166_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_166)

theorem lowS_zo_167_16_166:Lower true dzo_167_16 roots_167 gzo_167_16 6:=lower_iso (d1:=dom_167) (roots1:=roots_167) (T1:=gsh_167_16) [(dom_167,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_167_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa0000000000000000000000aa000000aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_166)

theorem lowS_zo_230_16_166:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso (d1:=dom_230) (roots1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_230_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500000055000000000000000000000055000000550000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_166)

theorem lowS_zo_231_16_166:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso (d1:=dom_231) (roots1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_231_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_166)

end Prior28586

namespace Prior28450
open PEqualNP.Outside.L_meta_30304

theorem lowS_114 : Lower true dom_114 roots_114 goal_114 4 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_114 (by decide +kernel)

theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_114

theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 :=
  lower_masked_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_166 (by decide +kernel)

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x22220000222200000000000000000000222200002222, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_172

theorem lowS_188 : Lower true dom_188 roots_188 goal_188 6 :=
  lower_masked_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_87 (by decide +kernel)

theorem lowS_233 : Lower true dom_233 roots_233 goal_233 5 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118

theorem lowS_248 : Lower true dom_248 roots_248 goal_248 5 :=
  lower_masked_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_118 (by decide +kernel)

theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 :=
  lower_masked_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_248 (by decide +kernel)

theorem lowS_zo_172_64_172:Lower true dzo_172_64 roots_172 gzo_172_64 5:=lower_iso (d1:=dom_172) (roots1:=roots_172) (T1:=gsh_172_64) [(dom_172,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_172_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_172)

theorem lowS_zo_173_64_172:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso (d1:=dom_173) (roots1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_173_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x22220000222200000000000000000000222200002222,0,1)] (by decide +kernel) (by decide +kernel) lowS_172)

theorem lowS_zo_188_64_172:Lower true dzo_188_64 roots_188 gzo_188_64 6:=lower_iso (d1:=dom_188) (roots1:=roots_188) (T1:=gsh_188_64) [(dom_188,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_188_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x111100001111000000000000000000001111000011110000,0,16)] (by decide +kernel) (by decide +kernel) lowS_172)

theorem lowS_zo_189_64_172:Lower true dzo_189_64 roots_189 gzo_189_64 7:=lower_iso (d1:=dom_189) (roots1:=roots_189) (T1:=gsh_189_64) [(dom_189,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_189_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x222222222222222200000000000000002222222222222222,0,1),(0x333300003333000000000000000000003333000033330000,0,16)] (by decide +kernel) (by decide +kernel) lowS_172)

end Prior28450

namespace Prior28586
open PEqualNP.Outside.L_meta_30304

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_173 (by decide +kernel)

theorem lowS_228 : Lower true dom_228 roots_228 goal_228 5 :=
  lower_masked_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_172 (by decide +kernel)

theorem lowS_212 : Lower true dom_212 roots_212 goal_212 5 :=
  lower_masked_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_228 (by decide +kernel)

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_212 (by decide +kernel)

namespace S_242
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (2,130), (16,80), (18,50), (18,82), (18,146), (32,34), (32,160), (48,50), (48,112), (48,176), (64,66), (64,80), (64,192), (96,98), (96,112), (96,224), (128,130), (128,160), (128,192), (144,146), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_242.map (· &&& dom_242)
def goalM : Nat := goal_242 &&& dom_242
def NN : Nat → Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xe337c
|5,0=>0xcd6b2
|6,0=>0xd0973
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140014000000000014001400000000001400140000000000140014000000028002800280028002800280028002800200020002000200020002000200025000000050000000500000005000000050000000500000005000000050000800080008000800080008000800080008000800080008000800080008000800000001400140000000000140014000000000010001000000000001000128002800280028000000000000000000280028002800280000000000000005000500050005000500050005000500000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xd191a5644688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 243 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 9 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x61
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3f3c0
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>1
|6,0=>2
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 1 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 2 then [(dzo_226_16,5,runOps true dzo_226_16 (0,roots_226) ops)] else [])++(if pm.testBit 3 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 4 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 5 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_242 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_226_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_226 5 s (0, roots_226) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_242 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_226 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_242 == dom_242) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_242 goalM v ys) : RunD true dom_242 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_242 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_242 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_242 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_242 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_242 roots_242 goal_242 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_242

theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff0000ffff0000ffff0000ffff0000, 112)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_210 (by decide +kernel)

namespace S_211
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (2,66), (2,130), (3,19), (3,67), (3,131), (16,17), (16,80), (18,19), (18,82), (18,146), (64,65), (64,66), (64,80), (64,192), (128,130), (128,192), (129,131), (129,145), (129,193), (144,145), (144,146), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x4b50
|4,0=>0x4caa515ba807f5006bba
|5,0=>0x8ed3b6469c57baf45b6a3cc473a2e8206e91a81318c5902eaf
|6,0=>0xc246738d3027bde15e94
|7,0=>0xc2467
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f0000000000000000f000f00000000000f000f00000000000a000a00000000000a000af000f00000000000c000c00000000000f000f00000000000c000ce000e000000000000000000000000000e000e000000000000000010001000000000000000000000000000100010000000000000000d000d00000000000c000c00000000000d000d00000000000c000c5000500000000000000000000000000050005000000000000000050005000000000005000000000000000500050000000000050000e000e00000000000e000e00000000000e000e00000000000e000ef000f00000000000a000a00000000000f000f00000000000a000a0000f000000000000000a000000000000000f000000000000000af000f00000000000f000f00000000000f000f00000000000a000a0000f000000000000000f000000000000000f00000000000000000000000000000000e000e000000000000000000000000000e000ef000f000000000000000000000000000f00000000000000000000300030000000000030003000000000001000100000000000000000000f000000000000000e000000000000000f000000000000000ec000c00000000000c000c00000000000c000c00000000000c000cf000e00000000000a000a00000000000f000e00000000000a000af000f000000000000000000000000000f000f0000000000000000f000f00000000000f000f00000000000000000000000000000000f000000000000000f000000000000000f000000000000000f0000f000f00000000000c000c00000000000f000c00000000000c000ca000a00000000000a000a00000000000a000a00000000000a000af000f00000000000f000f00000000000f000f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xce12906709483384b820cf709483b1c2520ce12d483384b420e67094833bcb220cf1290703bca43bc2e29067684a419c256106b384a419c2050c25490e141483398a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 25 then fld (dictB (i / 512) (i / 32 % 16)) 212 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 11 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x29309129d81428728578f285005291
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x61005100004122020000
|6,0=>0x918171
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xffbe57509185080
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x6012054300
|6,0=>0x7898
|7,0=>9
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 1 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])++(if pm.testBit 2 then [(dom_194,4,runOps true dom_194 (0,roots_194) ops)] else [])++(if pm.testBit 3 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 4 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 5 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_211 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_210 5 s (0, roots_210) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_210 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_211 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_211

theorem lowS_113 : Lower true dom_113 roots_113 goal_113 5 :=
  lower_masked_iso [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffffffff00000000ffffffff00000000, 96)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_209 (by decide +kernel)

theorem lowS_117 : Lower true dom_117 roots_117 goal_117 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300030003000300030003000300030, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_113

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 8 := S_211.noCircuit

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 8 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_211 (by decide +kernel)

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_213

theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 := S_242.noCircuit

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_211

theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_117 (by decide +kernel)

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33003300000000003300330000000000330033000000000033003300000000, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_213

end Prior28586

namespace Prior29242
open PEqualNP.Outside.L_meta_30304

theorem lowS_108 : Lower true dom_108 roots_108 goal_108 4 :=
  lower_masked_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_102 (by decide +kernel)

theorem lowS_125 : Lower true dom_125 roots_125 goal_125 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x22222222222222222222222222222222, 16, 17), (0x33330000333300003333000033330000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_108

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 8 :=
  lower_masked_iso [(0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_211 (by decide +kernel)

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 8 :=
  lower_masked_iso [(0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_211 (by decide +kernel)

theorem lowS_181 : Lower true dom_181 roots_181 goal_181 8 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_179 (by decide +kernel)

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00, 64, 72)] (by decide +kernel) (by decide +kernel) lowS_211

theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 :=
  lower_masked_iso [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_220 (by decide +kernel)

theorem lowS_205 : Lower true dom_205 roots_205 goal_205 5 :=
  lower_masked_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_220 (by decide +kernel)

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_masked_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_215 (by decide +kernel)

theorem lowS_248 : Lower true dom_248 roots_248 goal_248 6 :=
  lower_masked_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_244 (by decide +kernel)

theorem lowS_249 : Lower true dom_249 roots_249 goal_249 9 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_219 (by decide +kernel)

theorem lowS_zo_109_16_108:Lower true dzo_109_16 roots_109 gzo_109_16 5:=lower_iso (d1:=dom_109) (roots1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_109_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x2222000022220000222200002222,0,1)] (by decide +kernel) (by decide +kernel) lowS_108)

theorem lowS_zo_124_1_108:Lower true dzo_124_1 roots_124 gzo_124_1 5:=lower_iso (d1:=dom_124) (roots1:=roots_124) (T1:=gsh_124_1) [(dom_124,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_124_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x11110000111100001111000011110000,0,16)] (by decide +kernel) (by decide +kernel) lowS_108)

theorem lowS_zo_236_16_108:Lower true dzo_236_16 roots_236 gzo_236_16 5:=lower_iso (d1:=dom_236) (roots1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_236_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x111100001111000011110000111100000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_108)

theorem lowS_zo_236_1_108:Lower true dzo_236_1 roots_236 gzo_236_1 5:=lower_iso (d1:=dom_236) (roots1:=roots_236) (T1:=gsh_236_1) [(dom_236,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_236_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x111100001111000011110000111100000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_108)

theorem lowS_zo_237_16_108:Lower true dzo_237_16 roots_237 gzo_237_16 6:=lower_iso (d1:=dom_237) (roots1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_237_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_108)

theorem lowS_zo_245_8_181:Lower true dzo_245_8 roots_245 gzo_245_8 9:=lower_iso (d1:=dom_245) (roots1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_245_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33003300330033000000000000000000330033003300330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_181)

theorem lowS_zo_252_1_108:Lower true dzo_252_1 roots_252 gzo_252_1 6:=lower_iso (d1:=dom_252) (roots1:=roots_252) (T1:=gsh_252_1) [(dom_252,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_252_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111111111111111111111111111100000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_108)

end Prior29242

namespace Prior27923
open PEqualNP.Outside.L_meta_30304

theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_226 (by decide +kernel)

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_210 (by decide +kernel)

namespace S_211
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (2,66), (2,130), (3,19), (3,67), (3,131), (16,17), (16,80), (18,19), (18,82), (18,146), (64,65), (64,66), (64,80), (64,192), (128,129), (128,130), (128,192), (144,145), (144,146), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xc2467
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000000000000000f000000000000000f000000000000000f0000c000c00000000000c000c00000000000c000c00000000000c000ca000a00000000000a000a00000000000a000a00000000000a000af000f000000000000000000000000000f000f0000000000000000f000f00000000000f000f00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 212 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xf0
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 1 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 2 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 3 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_211 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_210 5 s (0, roots_210) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_210 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_211 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_211

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 := S_211.noCircuit

theorem lowS_227 : Lower true dom_227 roots_227 goal_227 7 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_211 (by decide +kernel)

theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_242 (by decide +kernel)

theorem lowS_241 : Lower true dom_241 roots_241 goal_241 7 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_242 (by decide +kernel)

end Prior27923

namespace Prior27921
open PEqualNP.Outside.L_meta_30304

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 8 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior29242.lowS_179 (by decide +kernel)

theorem lowS_zo_243_8_179:Lower true dzo_243_8 roots_243 gzo_243_8 9:=lower_iso (d1:=dom_243) (roots1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_243_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f000f000f0000000000000000000f000f000f000f0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_179)

end Prior27921

namespace Prior28450
open PEqualNP.Outside.L_meta_30304

theorem lowS_113 : Lower true dom_113 roots_113 goal_113 5 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_113 (by decide +kernel)

namespace S_117
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (4,36), (5,21), (5,37), (5,69), (16,17), (16,80), (20,21), (20,52), (20,84), (32,33), (32,36), (48,49), (48,52), (48,112), (64,65), (64,80), (68,69), (68,84), (68,100), (96,97), (96,100), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_117.map (· &&& dom_117)
def goalM : Nat := goal_117 &&& dom_117
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x8a56840839
|5,0=>0x7af916dc843bf89
|6,0=>0xc3dee
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcc00cc00cc00cc00cc000000cc000000000000000000022002200220022cc000000cc000000cc000000cc0003300330033003300220022002200220000cc000000cc000000880000008b30033000000000033003300000000c000c000c000c000c000c000c000c220022002200220022002200220022cc000000cc0000008800000088000330033003300330000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x473204973204732804736204325043210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 118 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 10 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x83
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x20
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x1f41c40
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0xd1
|6,0=>4
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 1 then [(dom_53,4,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 2 then [(dzo_113_4,5,runOps true dzo_113_4 (0,roots_113) ops)] else [])++(if pm.testBit 3 then [(dom_101,4,runOps true dom_101 (0,roots_101) ops)] else [])++(if pm.testBit 4 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_117 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_113_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_113 5 s (0, roots_113) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_117 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_117 == dom_117) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_117 goalM v ys) : RunD true dom_117 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_117 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_117 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_117 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_117 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_117 roots_117 goal_117 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_117

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c000c000c000c000c, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_113

theorem lowS_117 : Lower true dom_117 roots_117 goal_117 7 := S_117.noCircuit

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00cc00cc00cc00cc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_117

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 7 :=
  lower_masked_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffffffff00000000ffffffff00000000, 96)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_117 (by decide +kernel)

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_213

theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_masked_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_213 (by decide +kernel)

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030000000003030303000000000303030300000000030303030, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_217

theorem lowS_237 : Lower true dom_237 roots_237 goal_237 8 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

theorem lowS_241 : Lower true dom_241 roots_241 goal_241 6 :=
  lower_iso isoMvS_241 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

theorem lowS_181 : Lower true dom_181 roots_181 goal_181 6 :=
  lower_masked_iso [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff0000ffff0000ffff0000ffff0000, 112)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_241 (by decide +kernel)

theorem lowS_249 : Lower true dom_249 roots_249 goal_249 8 :=
  lower_iso isoMvS_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119

theorem lowS_zo_117_8_117:Lower true dzo_117_8 roots_117 gzo_117_8 7:=lower_iso (d1:=dom_117) (roots1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_117_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_117)

theorem lowS_zo_241_8_113:Lower true dzo_241_8 roots_241 gzo_241_8 6:=lower_iso (d1:=dom_241) (roots1:=roots_241) (T1:=gsh_241_8) [(dom_241,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_241_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3000300030003000300030003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_113)

theorem lowS_zo_245_8_117:Lower true dzo_245_8 roots_245 gzo_245_8 8:=lower_iso (d1:=dom_245) (roots1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_245_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_117)

end Prior28450

namespace Prior28586
open PEqualNP.Outside.L_meta_30304

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_masked_iso [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_115 (by decide +kernel)

namespace S_119
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (2,34), (2,66), (3,19), (3,35), (3,67), (4,68), (5,21), (5,37), (5,69), (6,38), (6,70), (7,23), (7,39), (7,71), (16,17), (16,80), (18,19), (18,50), (18,82), (20,21), (20,84), (22,23), (22,54), (22,86), (32,33), (32,34), (36,37), (36,38), (36,100), (48,49), (48,50), (48,112), (52,53), (52,54), (52,116), (64,65), (64,66), (64,68), (64,80), (96,97), (96,98), (96,100), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_119.map (· &&& dom_119)
def goalM : Nat := goal_119 &&& dom_119
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x481ca
|4,0=>0xe0fe3c8757b1bb134cf7
|5,0=>0xe39b4d664abb7d7b52849f6f28272c4b9de4075d3e23e07050
|6,0=>0xf8931f7bfee8e24a8c394c84f2024719cf7
|7,0=>0x2c4d1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00f000ff00f000ff00f000ff00f0fa00fa00fa00fa00fa00fa00fa00faff00ff00ff00ff00ff000000ff0000ff000f00ff000f00ff000000ff00000f000f000f000f0000000000000000fe00fe00fe00fe00fe00fe00fe00fe33003300330033003300330000000000000000ee00ee0000000000ee00ee0000ff000000ff000000aa000000aaaf00af00af00af00aa00aa00aa00aaff00ff0000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa0000af000000af000000aa000000aaff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00000000ee00ee00ee00ee00ee00ee00ee00eeff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0ee00ee00ee00ee00ee00ee00000000ff00ff00ff00ff00aa00aa00aa00aa
|_,_=>0
def stPool : Nat → Nat
|0=>0x28c49419541a50650c444194312408328734a0ca90c49419434a0d05446941943220d050de4418a31110628c49020a3121c650d2b41862221a650c44019424a18650c8b30c414194941cc51888018820
|1=>0x14312506
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7a67466e66776165a7546
|7,0=>0x806
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 21 then fld (dictB (i / 512) (i / 32 % 16)) 120 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 12 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x5191894a141912119911a1114a1
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x200000000000000
|6,0=>0x81716151413121
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xce6fdda89f52a63d46106603001001000
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x30100020
|6,0=>0x7a64b59
|7,0=>8
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_117,6,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 1 then [(dzo_51_4,4,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 2 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 3 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 4 then [(dom_87,6,runOps true dom_87 (0,roots_87) ops)] else [])++(if pm.testBit 5 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])++(if pm.testBit 6 then [(dom_115,6,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 7 then [(dom_103,5,runOps true dom_103 (0,roots_103) ops)] else [])++(if pm.testBit 8 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 9 then [(dzo_115_4,5,runOps true dzo_115_4 (0,roots_115) ops)] else [])++(if pm.testBit 10 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_119 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_51_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_115_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_117 6 s (0, roots_117) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_119 goalM v ys) : RunD true dom_119 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_119 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_119 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_119 roots_119 goal_119 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_119

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 := S_119.noCircuit

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 8 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_237 (by decide +kernel)

theorem lowS_230 : Lower true dom_230 roots_230 goal_230 7 :=
  lower_masked_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_227 (by decide +kernel)

namespace S_246
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (2,130), (4,68), (4,132), (6,38), (6,70), (6,134), (16,80), (18,50), (18,82), (18,146), (20,84), (20,148), (22,54), (22,86), (22,150), (32,34), (32,160), (36,38), (36,100), (36,164), (48,50), (48,112), (48,176), (52,54), (52,116), (52,180), (64,66), (64,68), (64,80), (64,192), (96,98), (96,100), (96,112), (96,224), (128,130), (128,132), (128,160), (128,192), (144,146), (144,148), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_246.map (· &&& dom_246)
def goalM : Nat := goal_246 &&& dom_246
def NN : Nat → Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xc5c9
|4,0=>0xfada5eb905db95ad80f2d0dd6d0135b3cd0afc02ad6839a8c391a9f914bf8ecd985cd8834b580d4c7f9307cc9d76f36745a342e7242ad53d6f83ca5739ee42cb7c1f2be1a08d198ba0d7ce
|5,0=>0xfddeafbf0dfaf3bf3d30f233ae9d3ae65e4e5bb6e4196e3c53e2749db9e5d9724d6b58d34fbc6285c56efbdd38bd097bb3edba476b51ffb3546aa233a7483a657da29959e7f29d9659cf0b9ccc49c8ff9c38a9bc5e985128cf96882d884df1834f4831c3824e4805907ef9378fa278cda72abe7261360e305fa215a08059713527e94f0ff4be544877547ab1462c743f3543c8f420103e02e3d4323a72533f5b2f46d27c1d2558b23a131c63619c6418fc317f76127c212203113330f1ac0e99b0d7e80cd990ae55092750922108580073210549d
|6,0=>0xf6faeef100ee45feb3b5e7c72e658ae578de4aece1b53e06c4ddd2cddcb5dc9b5d88c2d73b1cd17bc7ca0c16cbb64c0b3527aad76a9ea6a3437a31509561694a8088bec86c4d84f537f967795c4722976c06e6afbc6a5b06a31b678a36353861d3d6109c5be8453f604c0b948a8841a9f40954402e13f0f03bb193462d2f20327dc021b7a1fc3f1c0671b2df1ac2817b0616e4211b150f63c03079
|7,0=>0xff1f8ec056de9cdd7288ce003c8941c09338a1b57d6d4792373e2283c7ba25a4d1b8c9
|8,0=>0x8ae56
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xaa00aa00aa00aa008800880088008954015401540154015401540110011001540154000000000154015400000002a802a802a802a8000000000000000002a802a002a802a0000000000000000000000000000000000000000000000004400550044005500440044004400440000aa00aa00aa0000000000aa00aa000000aa008800aa000000000088008950015001500150015001500150015001500150015001500000000000000002280228022802280228022802280228022002280220022802200220022002255005500550055005500550055005500550055005500550055005500000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa0000000044004400440044004400440044004400440040004400400044004000440042a802a802a802a802a802a802a802a8000002a8000002a8000000000000000550055005500550055005500550055004400440044004400440044004400440a000a000a000a000a000a000a000a0008000a0008000a000800080008000954015401540154015401540154015401100154011001540110011001100112a802a802a802a8022002200220022002a802a802a802a802200220022002255005500550055005500550000000000550055005500550055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800880088008804000400040004000400040004000400000004000000040000000000000002a802a802a802a802a802a802a802a8000000000000000000000000000000055005500550055005400540054005400500050005000500050005000500050aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000000000000000000000000000000001540150015401500154015001540152200220022002200220022002200220022002200220022002200220022002201000100010001000100010001000100000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa0000000140014001400140014001400140014001400140014001400140014001400142a802a802a802a802a802a802200220022002200220022002200220022002255005500550055000000000000000000550055005500550000000000000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa000150015001500150015001500150015001500150015001500150015001500152a802a802a802a802a802a800000000022002200220022002200220000000055005500550055005500550055005500550055005500550000000000000000
|0,1=>0xa000a000a000a00000000000a000a000a000a000a000a00000000000000001400140014001400140014001400140014001400140014000000000000000000000002a802a80000000002a802a80000000002a002a00000000002a002a11001100110011001100110011001100110011001100110000000000000000aa000200aa000200aa000200aa000200aa000000aa000000aa000000aa000110011001100110011001100110011001100110011001100110011000000000000000000000000000000002a802a8000000000000000000000000000000055005500550055005500550055005500550044005500440055004400550044000000000000000000000000880088008800880088008800880088008800895401540154015401540154015401540154000001540000015400000154000088008800880088008800880088008800000000000000000000000000000000000000000000000000000000000000055005500550055005500550000000000000000aa00aa0000000000aa00aa00000000000000000000000000000000040004000400040004000400040004000400040004000400000000000000000002a8000002a80000000000000000000002a8000002a8000000000000000440055004400550044004400440044004400550044005500440044004400442200aa002200aa0022002200220022000000aa000000aa00000000000000004400440044004400440044004400440000004400000044000000000000000000000002a802a80000000002a802a8000000000220022000000000022002255005500550055005500550000000000550055005500550000000000000000a800aa00a800aa00a800a800a800a800a800aa00a800aa00a800a800a800a954015401540154015401540000000000000000000000000000000000000002280228022802280228022802280228022802280228022802200220022002244004400440044005500550055005500440044004400440044004400440044aa00aa00aa00aa00aa00aa00aa00aa00aa00a800aa00a800aa00a800aa00a954015401540154011001100110011000000000000000000000000000000002a802a002a802a002a802a002a802a002a802a002a802a002a802a002a802a000000000000000000000000550055000000000000000000000000004400440000aa00aa00aa0000000000aa00aa000000aa000000aa000000000000000000001400140014000000000014001400000014000000140000000000000002a802a802a802a802a802a802800280028002800280028002800280028002801000500010005000100010001000100000005000000050000000000000000
|0,2=>0xaa00aa00000000000000000000000000aa00aa0000000154011001540110015401100154011001540110015401100154011001540112a802a80000000002a802a802a802a802a802a80000000002a802a8000000000000000000000001100110011001100000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00a800a800a800a800a800a800a800a800000001540154000000000154015400000000015401540000000000000002a8008802a8008802a8008802a8008802a8000002a8000002a8000002a8000550055005500550055005500440044005500550055005500550055004400442200220022002200220022002200220022000000220000002200000022000154000001540154015400000154015401540000015400000154000001540002a802a802a802a802a002a002a002a002a802a802a802a802a002a002a002a5500550055005500000000005500550055005500550055000000000044004402000200020002000200020002000200020000000200000002000000020000000000000000000154015401540154000000000000000000000000000000000000000000000002a802a802a802a8000000000000000002200220022002245004500450045004500450045004500440044004400440044004400440044aa000000aa00aa00aa000000aa00aa00aa000000aa008800aa000000aa008954015401540154004400440044004401540154015401540000000000000000880088008800880088008800880088008800880088008800880088000000000000000000000005500550055005500000000000000000055005500000000000000008800880000000000aa00aa00000000008800880000000000880089540154015401540000000001540154015401540154015400000000000000008800880088008800880088000000000088008800880088008800880000000050005000500050005000500050005000000050000000500000000000000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000000001400140014001400040004000400040014001400140014000000000000000000000002a802a80000000002a802a80000000002a802a800000000022002205000500050005000500050005000500050005000500050004000400040004
|_,_=>0
def stPool : Nat → Nat
|0=>0x68448016242201a401823e34f030c5020b0424e8d1608e041a1849b08345832810d0b322420d300c305085c18612105822c106830c4408d1608a042a2c5022810803045000b124c20d160c30500401860a005822410690060878d162420e1a2c18c120058a121040706182840608080
|1=>0x1a2d582121068b06184805440186120150b06a44841a2c18250106900618a09004018222345a7042420d200c11408345821210a8d160c309009858a042420d161890908345830c1420d200c3050834186129020d16184844634583226868b121110d0618481000c10108345834224010
|2=>0x1211c8b0c704841a6018612115380c256841a401866e1068b6c08a041a401861201ab40618484662c1823e1068b06088801a2c3141210a9e06184841a2c18908c868b0618a044c184ad08c468b4a08a041a2c330281068b0c2422f1a2c30908b868304516841a2c189086869006184ac
|3=>0x1a40186131869006188c51a41a030c2400b06261841a2c4848834803130c20d160d0890834583121210d200d089083458260106830c260841a2c189801068b062423f1a4018900f868b0c242156a0c1097a1068b061889400401863e2469006184bc1a2dd8212106900619d041ad0186
|4=>0x9e1068b0608a049c1c18612115360c256841a2c18c121068b060a6841a2c182981068b4a2420d102c182280021006084801b2c3095a1069006184ca1a2dc02281068b06087841a2c1869210690061a4841a424030c246830c263841a2c4842b1069006188941a2c11408c46830c24084
|5=>0x16184d308345830c263041a40182121068b06084841a2038b6c184841a40186120068b6c18a0908345d20c2420d160c48008f8690160c30900348030c2420d6a2c1863e2420d160c311120068b06184847834583045020d160e8821210690060a2841a401861e246830c268041a2c109
|6=>0x9c1c586121188d160c309095868b6c084841a2c314121188d160c109001068b06184ca0835a0b06184841a2d2821210690680c3090834586602420d16184846235998160c3090834c1006184841a2c309085468b900c30908345830c44a041a2ea86121068b70184841b508030c2420d
|7=>0x160c328121069006188891a40186282420db22c186121068b06184841b605830c2420d4c2c10908c469006184c508348030c2420d662c186282424e16184846235a8b06184cd08345830c50480082c18222106830c256841a2c1d7042420d16e0314121068b06187890834583042420d
|8=>0x1a2c18612106ce16d830908345830c2420d662c186120020d200c309083480b06184841a2c186222420d17683090834583042420d161848462345830c2420d6a0c31412b420d160c3090835c9006184841ae480706184841a2c1861200235160c4847c345830c2420d544018612106aa
|9=>0xb06184841b6c1861210687160c30908345830c50484
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x422c82d902b1ff63f2c7cd8f6b1e763c4a7718eb31d06394c7154dfb1b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c35946830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c94d926b2476482c8ed91ab22f6452c88d90eb2176
|6,0=>0x2183c297844f06de0a3c0e680ef001dfcbbf367d8ef95def3bd777a2cf29de1bbbc776aeeb9dd3bba16736ce51dc6bb8676feede1db8bb6b66c8ed75dab3b4f7692cd09d9e3335765cec9dd90b31a7626ec35983b30075f4cbcdd76b2e675beeb659693acc658aeaf9d5bbab07552ea89d4e32957
|7,0=>0x246b48678fef1e1e39346b78c8f179a2bbc507894d111a1f34377
|8,0=>0x4936
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 92 then fld (dictB (i / 512) (i / 32 % 16)) 247 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x83516111235063506cd16360c0208350835161112362237121108351202083512350c2504110c2520270c2522352813043604360c250c25065112010835123506122050202720370c560c2506120c02123508351235063512360c252234123506090c2512350400083520340836123512110c25161122344a370c2520502235
|1=>0x16111235083606121236281312351235083512110c251652123504350c2506511235120108350c25083606120c250635123506120c25083508d512362037161106090c252037161112c50612061216362035161120351611623506120e131635123506d5123606511235202516116c27063508cd16360c25161104360c250635
|2=>0x161316351235083606351636083516111611121106250c2506121236165212352036161120361611163512360c020835203416112034161113390836121116111235161122361211223412110c250612202716111636
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x11000000000000000000000000000000000000000000000000000000000000000001000000000000
|5,0=>0x2011f11e10001d11c10001b10000000000001920000000001810000001620000000000000000000001510001411310000001210000000001110000f20000000000d20b20000000000a1000091081053000000000041022000000000000000
|5,1=>0x2a2291000000000000000000281271252000241000000231212000000000000
|6,0=>0x9b29929729619519329128f28d28b28920008728528328127f27d27b27927727527327126f26d26b26a10006826626426226025e25c25a25825625425225024f14d24b24924724524324124013e23c23a23823713523323213022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 16 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x57802b40158009f004e00250011a008c00420020801000040001e000e0005a002c001200080003c0019000a00040001e000e0006800300010000400018000800020000
|1=>0x442fe213f00bd805da08288118309f140d08068317e18970b5f842fc217610af084d84224204010120808020080c060408015f80aec047602080080002fc017a00bb
|_=>0
def pmB : Nat → Nat → Nat
|4,0=>0x2000000000000000000000000000000002000000
|5,0=>0xe080500000002085004000a830000000040820041005400000160000040006800000000008c0084000100000280a40000381014004002113000015a00000000
|6,0=>0x4861955d87d92216c019cc5360bac86a733adc96ce032b1b1d8cddbed247b905fdd0de1186439edb064f6c62c7979
|7,0=>0x8bbefcfbbf218a2d66c7b
|8,0=>0x20
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 17 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 1 then [(dom_212,5,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 2 then [(dzo_166_16,5,runOps true dzo_166_16 (0,roots_166) ops)] else [])++(if pm.testBit 3 then [(dom_230,7,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 4 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 5 then [(dom_214,6,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 6 then [(dzo_226_16,5,runOps true dzo_226_16 (0,roots_226) ops)] else [])++(if pm.testBit 7 then [(dom_166,5,runOps true dom_166 (0,roots_166) ops)] else [])++(if pm.testBit 8 then [(dom_198,5,runOps true dom_198 (0,roots_198) ops)] else [])++(if pm.testBit 9 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 10 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 11 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 12 then [(dzo_230_16,6,runOps true dzo_230_16 (0,roots_230) ops)] else [])++(if pm.testBit 13 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 14 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 15 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 16 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_246 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_166_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_226_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_230_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_242 7 s (0, roots_242) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_246 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_246 goalM v ys) : RunD true dom_246 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_246 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_246 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_246 roots_246 goal_246 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_246

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_230

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 9 := S_246.noCircuit

namespace S_247
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (2,34), (2,66), (2,130), (3,19), (3,35), (3,67), (3,131), (4,68), (4,132), (5,21), (5,37), (5,69), (5,133), (6,38), (6,70), (6,134), (7,23), (7,39), (7,71), (7,135), (16,17), (16,80), (18,19), (18,50), (18,82), (18,146), (20,21), (20,84), (20,148), (22,23), (22,54), (22,86), (22,150), (32,33), (32,34), (32,160), (36,37), (36,38), (36,100), (36,164), (48,49), (48,50), (48,112), (48,176), (52,53), (52,54), (52,116), (52,180), (64,65), (64,66), (64,68), (64,80), (64,192), (96,97), (96,98), (96,100), (96,112), (96,224), (128,130), (128,132), (128,160), (128,192), (129,131), (129,133), (129,145), (129,161), (129,193), (144,145), (144,146), (144,148), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7ffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
|6=>3
|7=>7
|8=>5
|9=>4
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x68651161100d08b
|7,0=>0xe1c5ddefe0c36dfc2f37c0a62ab60a0013a
|8,0=>0xc5f83bf10cb4299acf6195634
|9,0=>0xce95e929b772daa1ad5e
|10,0=>0x6bf33
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000300030003000300030003000300030003000300030003000300030000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa330033003300330033003300330033003300330033003300330033000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x38ad49101039e56a481038a922027038a9204e0328ad49020315a92200c315a92040c315a4184062b483081862a482080ca2b524418a920820619456a4813152441c062906b080ca2a488398a418820
|1=>0xe2b524081d02b524080c56a481
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0xe7077007
|7,0=>0x4183a73282b72471c8157
|8,0=>0x678607588517498
|9,0=>0x8687f77786f8
|10,0=>0x8e7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 17 then fld (dictB (i / 512) (i / 32 % 16)) 248 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 12 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x2817050812856a20816a20813037057050813017056273017056273017056373017053037050816373017053033017057056a208168e627
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x200000
|7,0=>0x14344ce32cc8314c23
|8,0=>0x1f2749b264972
|9,0=>0x9063188611
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 10 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x7bd7fa7fcfe9bd1fa2ec5887d03c01c01000
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>0x100
|7,0=>0x3634527
|8,0=>0x9999a
|9,0=>0xb99c
|10,0=>8
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_246,9,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 1 then [(dom_87,6,runOps true dom_87 (0,roots_87) ops)] else [])++(if pm.testBit 2 then [(dom_119,8,runOps true dom_119 (0,roots_119) ops)] else [])++(if pm.testBit 3 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 4 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 5 then [(dom_215,9,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 6 then [(dzo_167_16,6,runOps true dzo_167_16 (0,roots_167) ops)] else [])++(if pm.testBit 7 then [(dom_183,8,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 8 then [(dom_231,8,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 9 then [(dzo_231_16,7,runOps true dzo_231_16 (0,roots_231) ops)] else [])++(if pm.testBit 10 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_247 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_167_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_231_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_246 9 s (0, roots_246) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
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
def RootG (s : Nat) : Bool :=
  scr true dom_247 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_247 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit

end Prior28586

namespace Prior29242
open PEqualNP.Outside.L_meta_30304

theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_masked_iso [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xffff0000ffff0000ffff0000ffff0000, 112)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_217 (by decide +kernel)

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030000000003030303000000000303030300000000030303030, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_217

theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_242 (by decide +kernel)

theorem lowS_237 : Lower true dom_237 roots_237 goal_237 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x222200002222000022220000222200002222000022220000222200002222, 128, 129)] (by decide +kernel) (by decide +kernel) lowS_236

theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_237 (by decide +kernel)

namespace S_253
def pairsG : List (Nat × Nat) := [(1,17), (1,129), (4,36), (4,132), (5,21), (5,37), (5,133), (8,72), (9,25), (9,73), (9,137), (12,44), (12,76), (12,140), (13,29), (13,45), (13,77), (13,141), (16,17), (16,144), (20,21), (20,52), (20,148), (24,25), (24,88), (24,152), (28,29), (28,60), (28,92), (28,156), (32,36), (32,96), (32,160), (33,37), (33,49), (33,97), (33,161), (40,44), (40,104), (40,168), (41,45), (41,57), (41,105), (41,169), (48,49), (48,52), (48,112), (48,176), (56,57), (56,60), (56,120), (56,184), (64,72), (64,96), (64,192), (65,73), (65,81), (65,97), (65,193), (68,76), (68,100), (68,196), (69,77), (69,85), (69,101), (69,197), (80,81), (80,88), (80,112), (80,208), (84,85), (84,92), (84,116), (84,212), (128,129), (128,132), (128,144), (128,160), (128,192), (136,137), (136,140), (136,152), (136,168), (136,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_253.map (· &&& dom_253)
def goalM : Nat := goal_253 &&& dom_253
def NN : Nat → Nat
|5=>3
|6=>10
|7=>24
|8=>21
|9=>5
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0x95839655415a928
|6,0=>0xdcd82935f8802987887c4cc1e40cd0391fe3436625e4810d74
|7,0=>0xf5d49b840fb80ec9416784b6348a6544bc04144b40b9f3b6d138f3c357b02d0a32b9632aad329375238750b0c40abb6094ec06e2c055a101ad200087
|8,0=>0xff958d5dc5c9ec6c28849cfd48c161804856adbe5e70f520ff499324679f3dbe235f0c34a5f2e70c2d76922ad221b831cbe205b46
|9,0=>0xd63b54181b28ae1155a01140f
|10,0=>0x6412b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccccccc0000cccccccccccc0000cccccccccccc00000000cccccccc00000003333333333333333333333333333333333330000333300003333000033330000cccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0000cccc0c0ccccc00033333333333333333333333333333333333333332222222233333333222222220000cccc0000cccc0000cccc0000cccc00000000000000000000000000000003333333333330000333333333333000033333333333300003333333333330000cccccccc44444444cccccccc44444444cccccccc00000000cccccccc000000011111111111111111111111111111111000000000000000000000000000000000c0c0c0c040404040c0c0c0c040404040c0c0c0c000000000c0c0c0c000000000000000000033330000000000003333333333330000000033333333000000004444444444444444444444444444444444444444444400004444444444440003333333333332222333333333333222233330000333300003333000033330000cccccccccccccccccccccccccccccccc8888888888888888888888888888888b33333333333000033333333333300000000000000000000000000000000000044440404444404044444040444440404444404044444000044440404444400033333333323232323333333332323232303030303030303030303030303030300000cccc0000cccc0000cccc0000cccc00008888000088880000888800008888303030303030303030303030303030303030303000000000303030300000000cccccccccccccccccccccccccccc0000cccccccccccccccc0000000000000003030303030303030303030303030303030303030303030303030303030303030cccccccc88888888cccccccc8888888800000000000000000000000000000003333333322222222333333332222222233333333222222223333333322222222cccccccccccccccccccccccccccccccc00000000000000000000000000000003333333300000000333333330000000033333333000000003333333300000000ccccccccccccccccccccccccc8c8c8c8ccccccccccccccccc0c0c0c0c0c0c0c3333333333333333333333332222222233333333333333330000000000000000cccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc02222222222222222222222222222222222222222222222222222222222222222000000000404040400000000040404040c0c0c0c000000000c0c0c0c00000003333333333333333000000000000000033333333333333330000000000000000
|0,1=>0x33333333000000003333333300000000222222220000000022222222000000004444444400000000444444440000000000000000000000000000000000000000000000000000000000000003333333333330000333333333333000044444444444444444444444444444444444400004444000044440000444400000000000030303030000000003030303000000000000000000000000000000000c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c000000000c0c0c0c000000003030303030303030303030303030303030303030303000003030303030300000404040404040404040404040404040404040404000000000404040400000003333333333333333333333333333333333333333333300003333333333330000444444444444444444444444444444444444444400000000444444440000000333300003333333333330000333333333333000033330000333300003333000000000000cccccccc00000000cccccccc00000000000000000000000000000001111000011111111111100001111111111110000111100001111000011110000
|_,_=>0
def stPool : Nat → Nat
|0=>0xc23802481033021891440cc0802c52033023c024810308e0096c81030970096051033023481034d70092040c70862455840cc0802040d538024850331300510308e0122040d13802451034020080c238f0091440c238d1440c70861440c2040
|1=>0x3802611440c23802682040cc54025f2040c29c02481030a60092040c23a50091481033150092040d00802481030970092040c28ce0092040cc4c02c85033020092040cc80025f21e0cc0802487440c238025a1440c23802481034c238025c204
|2=>0x8c025a1440cc080248103302009adc2040cc08026a2040cc0802480cc4c23c025f2040cc0802487833020096e41481033020096887833020091481033028c025f2040cc08025b2040cc08024b2040c23802481033290091481030a60091440c2
|3=>0x2040cc08024810330200985a2040cc0802481033020096087840cc0802452040cc0802451033020098452040cc08025814810308e0091487840cc080248103302b002488840cc080248103302
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x3180cc006
|6,0=>0x9ec48720b8e9c66e2d613387dc32c127
|7,0=>0x8243f21e90ed772c379dad0ce863bb01d710b17553a8dd37093845c20e0f7074736b9960bb0558
|8,0=>0x1af8d34e7a32b38d8c2c5f62eb16d8b2c5762ab14d8a2c4f266912b9914c6a226f0c7
|9,0=>0x1d78e7c71e37f1b78
|10,0=>0x1df7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 45 then fld (dictB (i / 512) (i / 32 % 16)) 254 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 13 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x289080964cc861089850b14cc8252890809089442d2890809882c485209886d14cc82514cc82514cc82514cc82500b4a242024a2420248254c4c225209442614cc82564cc8610898049689081120959332184c1900b4a24202442d2890809089482530b4a242024825306402d2890809
|1=>0x20945332094425209484e0894485209850b2094811209428620985092095a272045313089486d109842610945112094811109450b209486d1098a2420245332095e0b109643314448252098533209483a14cc825902c5112095f3321b442690cc511209423a14cc825902c5112094c2d
|2=>0x2098811089842520948262094226
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x5000
|6,0=>0x1341120d4000000094000000054000
|7,0=>0x5635335034d34a34734434133e33b33833533232f32e12c22a22822622332031d31a3173
|8,0=>0x8127f27d27b27927727527327126f26d26b26926726526326125f25d25b2592
|9,0=>0x871861851841831
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x16ff016df012df012ce012cb0124f0124b0120f00810006df0067f00301002df002cf0020b00201000cf000ce000900008a00080000500004b0004a0003f000100000f0000e0000b0000a0000200000
|1=>0xc02df8629b822df480df462df422df402df312cf0b2df0b20f0a2df0864b082df0828b0629b042ff042ef
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x40
|6,0=>0x2460400070003c0
|7,0=>0x4505050c421170e09569818d2ca5db591308
|8,0=>0x279528a199dba47aa824b6fad98df4e9
|9,0=>0x28c24b13
|10,0=>0x13
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 20 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_249,9,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 1 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 2 then [(dom_181,8,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 3 then [(dzo_245_8,9,runOps true dzo_245_8 (0,roots_245) ops)] else [])++(if pm.testBit 4 then [(dom_236,7,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 5 then [(dzo_252_1,6,runOps true dzo_252_1 (0,roots_252) ops)] else [])++(if pm.testBit 6 then [(dom_252,8,runOps true dom_252 (0,roots_252) ops)] else [])++(if pm.testBit 7 then [(dom_237,8,runOps true dom_237 (0,roots_237) ops)] else [])++(if pm.testBit 8 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 9 then [(dom_221,8,runOps true dom_221 (0,roots_221) ops)] else [])++(if pm.testBit 10 then [(dom_220,5,runOps true dom_220 (0,roots_220) ops)] else [])++(if pm.testBit 11 then [(dom_248,6,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 12 then [(dzo_124_1,5,runOps true dzo_124_1 (0,roots_124) ops)] else [])++(if pm.testBit 13 then [(dzo_109_16,5,runOps true dzo_109_16 (0,roots_109) ops)] else [])++(if pm.testBit 14 then [(dom_108,4,runOps true dom_108 (0,roots_108) ops)] else [])++(if pm.testBit 15 then [(dom_125,6,runOps true dom_125 (0,roots_125) ops)] else [])++(if pm.testBit 16 then [(dzo_236_16,5,runOps true dzo_236_16 (0,roots_236) ops)] else [])++(if pm.testBit 17 then [(dzo_236_1,5,runOps true dzo_236_1 (0,roots_236) ops)] else [])++(if pm.testBit 18 then [(dzo_237_16,6,runOps true dzo_237_16 (0,roots_237) ops)] else [])++(if pm.testBit 19 then [(dom_205,5,runOps true dom_205 (0,roots_205) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_253 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_245_8_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_252_1_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_124_1_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_109_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_236_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_236_1_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_237_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_249 9 s (0, roots_249) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_253 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_253 == dom_253) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_253 goalM v ys) : RunD true dom_253 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 21 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 21 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
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
def RootG (s : Nat) : Bool :=
  scr true dom_253 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_253 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_253 roots_253 goal_253 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_253

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 := S_253.noCircuit

end Prior29242

namespace Prior27923
open PEqualNP.Outside.L_meta_30304

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 7 :=
  lower_masked_iso [(0xcccccccccccccccccccccccccccccccc, 126), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28450.lowS_213 (by decide +kernel)

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 7 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_115 (by decide +kernel)

namespace S_243
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (2,34), (2,66), (2,130), (3,19), (3,35), (3,67), (3,131), (16,17), (16,80), (18,19), (18,50), (18,82), (18,146), (32,34), (32,160), (33,35), (33,49), (33,97), (33,161), (48,49), (48,50), (48,112), (48,176), (64,65), (64,66), (64,80), (64,192), (96,97), (96,98), (96,112), (96,224), (128,129), (128,130), (128,160), (128,192), (144,145), (144,146), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_243.map (· &&& dom_243)
def goalM : Nat := goal_243 &&& dom_243
def NN : Nat → Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xcc39fb28e967f5946b3c3cb4223aa80098a
|5,0=>0xe9e55af1339e4609087d8abcd83d0979c6f76dc76c37a61a444c72c4a29b27207232151eb88181a5040e900f53
|6,0=>0xfd937e6bb4d68d3d092bc9913be67eb2892a4a979fc239526d9422d93fdc93bcc90a4f8fb5e7a5266fc176d1b56cf56672a663e48589c1534a032727318e7308582fb7a2e2732aba82ab5c2697425f22243e520a8d1a530193b5175bd173ee172ac170210f19e0d0840826e06ecd05ce404771
|7,0=>0xf6c05cfcdace1eccdbe6cb53ec328dbd857a5feca4425a26f6989db924158e1838a5128919c884c487305811707bc7879b737818577c597136a706b562308602555ae4056bff4c5fa37b1831a8d2122c1e07d1c05c19f5b078c2
|8,0=>0xbe802aa738a20478d91f701185b03d3ac122f6f5275f513a1e1088d05184
|9,0=>0xaa738
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cb000b000b000b000b000b000b000b000b000b000b000b000a000a000a000af000f000f000f000f000f000f000f0000000f0000000f0000000a0000000a0000000000000000300030003000300000000000000000002000200020002f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a50005000500050005000500000000000500050005000500040004000000003000300030003000300030003000300020002000200020002000200020002f0000000f0000000a0000000a0000000f0000000f0000000a0000000a0000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000500050005000500050005000500050005000500050005000000000000000000000000f000f00000000000f000f00000000000c000c00000000000c000cf000f00000000000f000f00000000000c000c00000000000c000c00000000f000f000f000f000e000e000e000e000f000f000f000f000e000e000e000ef000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cf000f000f000f000f000f000f000f000a000a000a000a000a000a000a000ae000e000e000e000e000e000e000e000e000e000e000e00000000000000000000f0000000f0000000a0000000a0000000f0000000f0000000a0000000af000f000f000f000c000c000c000c000a000a000a000a0008000800080008f000f000f000f000f000f000f000f000f000f000f000f0000000000000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a00000000f000f00000000000f000f00000000000f000c00000000000e000cf000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f000f0000000f0000000a0000000a0000f000f000f000f0000000000000000000f000f000f000f0000000000000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef000f000f000f000f000f000a000a000f000f000f000f000e000e000a000af000f000f000f000f000f00000000000f000f000f000f000c000c00000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|0,1=>0xf000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000a0000000000000000f000f000000000000000000000000000f000f00000000f000f000f000f000f000f000f000f000f000c000f000c000f000c000f000c00000000000000000000000000000000f0000000f0000000f0000000f0000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000500050005000500040004000400040005000500050005000400040004000400000000000000000000000000000000e000e000e000e000e000e000e000e5000500050005000500050000000000050005000500050005000500000000000000000000000000000000000000000000000000000000e000e000e000ea000a000a000a000a000a000a000a000f000f000f000f000e000e000e000ef000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f000f000f000f000f000f000f000f000f000f000f000f000e000e000e000ef000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000300030003000300030003000300030003000300030003000000000000000000000000000000000000000000000000f000f000f000f000c000c000c000cf000f000f000f0003000300030003000f000f000f000f00020002000200021000100010001000100010001000100010001000100010000000000000000f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000e0000000000000000f000f000f000f0000000000000000000e000e000e000ef000f000f000f000f000f000f000f000f000f000f000f000c000c000c000c3000300030003000300030003000300030003000300030002000200020002f000f000f000f0000000000000000000f000f000f000f000e000e000e000e0000000000000000e000e000e000e0000000000000000000e000e000e000e
|_,_=>0
def stPool : Nat → Nat
|0=>0x4b6802440c848c24415264c14b6151802431471891034503091082c63c91112cf01710540c5891052cd3092052c71891033460052ce54600911315030408504b00911320b30910848f2444503c504b3802440cd3052c72862432071840c2040
|1=>0x12414b18024414b34600910344b3002440e32c60091052e21802452c71802448452c60041412c02441523160041522d51802448082c601f2452ce18024415e2c600910540c1962452dd18024414b7060171056cb300243147180103512180105
|2=>0x30624420548b32c1052d518026a94540b18912b14b18024444540b309a852cc1a924415b196009103212180244152646009103a0b18024414b9c600910345018024414b18f0091052c69802440c82cc1890c560600912015018024414b64c189
|3=>0xc89b0414b18024415b40b18024414bc4600912514b180244c052c60171052ef18026a1502c67c910548b180244b852c6017a852cc5c40d12c024494548600911120b30912d14b1801055122c6009a9114b30912544b18024415019600912514b
|4=>0x14b1802440d12c600912314b18024494314b1802741052c60091052ef1802441522cc009a9114b18024494540b1802730c52c600910540b30624414b1a900912314b3060091081522c6009cd114b1802452d818024414b306a4024444540b180
|5=>0x2cc18026c1052c6009a8414b180d891052c6009a852c600910814b1802440c52c6009cc52c600910540b1802440c52cc180c8910548b1801052d5180244a052c6035cc52c6017a852c600910320b1802444482c6017cc52c6009a852cc189a83
|6=>0x91052c601f24414b18024414b180dc91052c6009105
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619545f61658536135847610583b60d582f60a58236
|6,0=>0x6fddba56d19ad769d9a07665d936631d8575f9d7775c1d697589d5b7551d4d7519d3f74e1d3174a9d237471d15743d9087405cfa73cdcec7395cde73618d173314c572f9cb772c1ca97289c9c6255c8e7
|7,0=>0xafa2b68ac1aa97a8da9d6a59e8f7a25a8369f1e7579b9e66897de587945e4a790a23b78d1e2d789621d8859e10682220087e21f087a5de2776ddd477399c68
|8,0=>0xc41f0a6c0defc7bd5eee7b9dee16b69ed37b35ac67
|9,0=>0x3176
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 56 then fld (dictB (i / 512) (i / 32 % 16)) 244 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 14 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x2c64b150c6cb151508b01946d1401464b0114c401960044482c6430350649201404b320064922140431b14b444a2c645322cc8601380444a2c6491918058011120b191405419248050114058011120b192c5433014b43302c551401464b0114043192c5541924805014854b191404501
|1=>0x1404519100c4482c6453200645192c0490110650192c04b46146430114b430314b572f2464b011004b19245491918044012c5451924643012c545191404601440c920140460114644010c0452d4064b21140450124885012c044010cc440114c80191804501440c5190cc052d1804448
|2=>0x24549111804419100492d100450114b44032c0452d1804b1924049221405103146491b100c919100450114b450114644032464601100452d10045192c54531006430114b4421140572f2464b19006451910045412c0452d100cb01180453200645310064b19
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x11001
|5,0=>0x1a31911631510000001140000f20d20000a3091000000072043022
|6,0=>0x6436135f25c35b15925635425315125014e24c24b10004834714610004420000004130000003e33c23a23913630003420003133012d32b22922722522412221f30001d2
|7,0=>0xad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d26b2692672
|8,0=>0xb91000b81b71b61b51b41b31b21b11b01af1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x204400081000018ac0002eb0000ba40002e1000080000017900005040001310000440000108000041400010400004000000e100001e0000050000012000004000000e0000020000006000001100000400000090000020000004000000c0000020000004000000
|1=>0x318ba40c414d030cfa40c12e903041240a82fd0222be40842e90200bb40783f50160fb404e6f9012afa40282e90072be401c8780070be40108700038fe400e16800321a000c2f90020bf40082ef0008120001145000441400110100025f400091400020c0000825
|2=>0x206e2e943a0ba48426e92088a004a06eb108008c2200830560f94149af90522be4148ab90520ba410183104060640ee3f903a0ba40c63e9
|_=>0
def pmB : Nat → Nat → Nat
|4,0=>0x102
|5,0=>0x5020210000200048c00341000014185
|6,0=>0x426c3159206b07241c10ca144005a508004002a8c007345071e1a44f803848e9702145120c9c013
|7,0=>0x312992f390a33075019c9630da417cb622876a972052707969a99ac88f05ecb
|8,0=>0x986e8389cfe7c07315bbc
|9,0=>0x1b
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 7 (j % 128); fld (pmPalB (k / 32)) 26 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 1 then [(dom_194,4,runOps true dom_194 (0,roots_194) ops)] else [])++(if pm.testBit 2 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 3 then [(dom_115,7,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 4 then [(dzo_81_32,4,runOps true dzo_81_32 (0,roots_81) ops)] else [])++(if pm.testBit 5 then [(dom_241,7,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 6 then [(dom_179,7,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 7 then [(dom_211,7,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 8 then [(dzo_162_16,4,runOps true dzo_162_16 (0,roots_162) ops)] else [])++(if pm.testBit 9 then [(dom_227,7,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 10 then [(dom_193,4,runOps true dom_193 (0,roots_193) ops)] else [])++(if pm.testBit 11 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])++(if pm.testBit 12 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 13 then [(dzo_227_16,6,runOps true dzo_227_16 (0,roots_227) ops)] else [])++(if pm.testBit 14 then [(dzo_163_16,5,runOps true dzo_163_16 (0,roots_163) ops)] else [])++(if pm.testBit 15 then [(dzo_209_32,5,runOps true dzo_209_32 (0,roots_209) ops)] else [])++(if pm.testBit 16 then [(dom_177,4,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 17 then [(dzo_211_32,6,runOps true dzo_211_32 (0,roots_211) ops)] else [])++(if pm.testBit 18 then [(dzo_226_16,5,runOps true dzo_226_16 (0,roots_226) ops)] else [])++(if pm.testBit 19 then [(dzo_83_32,5,runOps true dzo_83_32 (0,roots_83) ops)] else [])++(if pm.testBit 20 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 21 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 22 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 23 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 24 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 25 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_243 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_81_32_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_162_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_227_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_163_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_209_32_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_32_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_226_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_32_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_242 7 s (0, roots_242) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_243 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_243 == dom_243) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_243 goalM v ys) : RunD true dom_243 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
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
def RootG (s : Nat) : Bool :=
  scr true dom_243 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_243 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_243 roots_243 goal_243 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_243

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 10 := S_243.noCircuit

end Prior27923

namespace Prior28450
open PEqualNP.Outside.L_meta_30304

theorem lowS_189 : Lower true dom_189 roots_189 goal_189 8 :=
  lower_masked_iso [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffffffffffffffff0000000000000000, 64)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior28586.lowS_119 (by decide +kernel)

theorem lowS_229 : Lower true dom_229 roots_229 goal_229 7 :=
  lower_masked_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xffffffff00000000ffffffff00000000, 96)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_179 (by decide +kernel)

theorem lowS_244 : Lower true dom_244 roots_244 goal_244 7 :=
  lower_masked_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffffffff00000000ffffffff00000000, 96)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    lowS_229 (by decide +kernel)

namespace S_245
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (4,36), (4,132), (5,21), (5,37), (5,69), (5,133), (16,17), (16,80), (16,144), (20,21), (20,52), (20,84), (20,148), (32,33), (32,36), (32,160), (48,49), (48,52), (48,112), (48,176), (64,65), (64,80), (68,69), (68,84), (68,100), (68,196), (96,97), (96,100), (96,112), (96,224), (128,132), (128,144), (128,160), (129,133), (129,145), (129,161), (129,193), (192,193), (192,196), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_245.map (· &&& dom_245)
def goalM : Nat := goal_245 &&& dom_245
def NN : Nat → Nat
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|8,0=>0xc2522
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000033000000330000003300000033000000330000003300000033000000330000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c22002200220022002200220022002200220022002200220022002200220022cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000033003300330033003300330033003300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|8,0=>6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 6 then fld (dictB (i / 512) (i / 32 % 16)) 246 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3f80
|_=>0
def pmB : Nat → Nat → Nat
|8,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 7 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_244,7,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 1 then [(dom_117,7,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 2 then [(dom_229,7,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 3 then [(dom_213,7,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 4 then [(dom_241,6,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 5 then [(dzo_241_4,6,runOps true dzo_241_4 (0,roots_241) ops)] else [])++(if pm.testBit 6 then [(dom_181,6,runOps true dom_181 (0,roots_181) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_245 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_244 7 s (0, roots_244) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_245 == dom_245) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_245 goalM v ys) : RunD true dom_245 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_245 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_245 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_245 roots_245 goal_245 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_245

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 := S_245.noCircuit

theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x1100110011001100110011001100110011001100110011001100110011001100, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_244

namespace S_253
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (4,36), (4,132), (5,21), (5,37), (5,69), (5,133), (8,136), (9,25), (9,41), (9,73), (9,137), (12,44), (12,140), (13,29), (13,45), (13,77), (13,141), (16,17), (16,80), (16,144), (20,21), (20,52), (20,84), (20,148), (24,25), (24,88), (24,152), (28,29), (28,60), (28,92), (28,156), (32,33), (32,36), (32,160), (40,41), (40,44), (40,168), (48,49), (48,52), (48,112), (48,176), (56,57), (56,60), (56,120), (56,184), (64,65), (64,80), (68,69), (68,84), (68,100), (68,196), (72,73), (72,88), (72,200), (76,77), (76,92), (76,108), (76,204), (96,97), (96,100), (96,112), (96,224), (104,105), (104,108), (104,120), (104,232), (128,132), (128,136), (128,144), (128,160), (129,133), (129,137), (129,145), (129,161), (129,193), (192,193), (192,196), (192,200), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_253.map (· &&& dom_253)
def goalM : Nat := goal_253 &&& dom_253
def NN : Nat → Nat
|3=>1
|4=>2
|5=>8
|6=>28
|7=>94
|8=>70
|9=>18
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xf7944
|4,0=>0xe186c1269b
|5,0=>0xfc5c3990e08b5f88a2c0716ea4da793cc4e25091
|6,0=>0xf61cdf4e95edd73ed4d9d1224cee1dca102c9868c1547b3e37a7823a634f9e8239b0069a3da813757c49a779cb7785a6b21a42e6c41b342eb68299a82902128f5e27ada117c7
|7,0=>0xfe9a6eb5e1e7a6fe71cee51fde25a0e121ce0babe0059d9797d88f4d0bf0d00bdcfc19cf5c8c7970c680dc2a53be92fbb1f0b97b7b6aadb53d1b526db391aada41ad7adac709abaaea987fa83a8a55e7a4d4da1fe9a05599d6be9aff69ad2494f7293bf6926af8de508d5b68d1e38a72585f71819df8126e7f92c7d6b37adae78dbb77bf874abc720d17075f5dbc35d5fd5ca0059ba95346051c4e50e4b50a8b4e42848d854141e3e0bc399f2391c038be931963318162f23f2e4862d24b2c4592a72229ab828c8826226237631e7b11ad771a2b11768f16df514fa60c2cb0ae3f0973207267053ac0297b
|8,0=>0xf3caaf0b3cee434ed58ceb769e7fede21c9e1299cebe8ce2ffcc877c26b3c13c8c0902bf788bb5f7b35f8aaf1caab8aa2e559e3d89cfd49c10199e1497954939978d7cd8b6be8b4b68777b8267d81e8a7a9ee6d8056adbe64e6b62924520ff4aef54993244a57405e13f6ab3a2f438bf038ae2352bc3475b2fcfd2e70c2c330287d62702225dc523d042134b1eb711cd9b1cbe21c8411c348152fe14efd14b991164b0f06d0bebc0ad2305c9c04ad9
|9,0=>0xecb30d5399d2bbfc434ab5c5db00dda392b86cac83172749505ebd85260d4181b39cae1a450155a01140f0a935
|10,0=>0x6412b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccccccccccccccccccccccccccccccc0000cccc000088880000cccc00008888303030303030303030303030303030303030303000000000303030300000000c0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1111111111110000111111111111000011111111111100001111111111110000000088cc000088cc000088cc000088cc0000888800008888000088880000888b3333333333333333333000033330000333333333333333333330000333300000000cccc0000cccc0000cccc0000cccc00008888000088880000888800008889133113311330033113311331133003311111111111100001111111111110000cccccccccccccc00cccccccccccccc00cccccccccccccc00cccccccccccccc0333300333333003333330033333300333333000033330000333300003333000000cc00cc00cc00cc00cc00cc00cc00cc00000000000000000000000000000003333333333333333222222222222222233333333333333332222222222222222cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc8888cccc888b3333333003300333333333300330033333333330000000033333333000000000000000000000000cccc8888cccc88880000000000000000cccc8888cccc888b3330000333300003333000033330000333300003333000033330000333300008888888888888888888888888888888888888888888888888888888888888888303030300030003030303030003000303030303000000000303030300000000cccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0003333333322222222333333332222222233330000222200003333000022220000cccccccccccccccccccccccccccccccc8888888888888888888888888888888b333333322222222333333332222222233333333222222223333333322222222cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0003333333333333333000000000000000033333333333333330000000000000000cccccccccccc0000cccccccccccc000088888888888800008888888888880003333222233332222000000000000000033332222333322220000000000000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333333333333333333333333333333300000000000000000000000000000000cccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000003300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333332222333333333333000033332222333322222222222222220000
|0,1=>0xcccc00cc00000000cccc00cc00000000cccc000000000000cccc0003333223333332233333322333333223333332222333322223333222233332222ccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000003333333300000000333333330000000033332222000000003333222288888888888888888888888888888888cccccccccccc8888cccccccccccc88880003333000033330000333300003333000033330000222200003333000022224444444444444444444444444444444444440000444400004444000044440003311331133113300331133113311330033113311331133003311331133113300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c800033300000333000003330000033300000333000003330000033300000333000000000cccccccc00000000cccccccc00000000cccc000000000000cccc00033333333333333333333333333333333333333333333222233333333333322220000000044444444000000004444444400000000444400000000000044440003333333333330033333333333333003333333333333300003333333333330000cccc0000cccccccccccc0000cccccccccccc0000cccc8888cccc0000cccc888b333000033330000333300003333000033333333333322223333333333332222cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc03333333333332222333333333333222233333333333322223333333333332222000000000000000000000000000000000000cccc000088880000cccc00008888000000000003333000000000000333300000000000022220000000000002222cccccccc44444444cccccccc44444444cccccccc44440000cccccccc44440001111111111111111111111111111111111111111111100001111111111110000cccccccccccccccccccccccccccccccccccccccccccc0000cccccccccccc000000000000000000000000000000000001111111111110000111111111111000000000000000000000000000000000000cccccccc88888888cccccccc88888888000000000000000000000000000000033333333333300003333333333330000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc3333333333333333333333333333333333332222333322223333222233332222cccccccccccccccccccccccccccccccccccccccc88888888cccccccc88888888000000033333333000000003333333300000000222222220000000022222222cccccccccccccccccccccccccccccccc44444444444400004444444444440000000333300002222000033330000222200003333000022220000333300002222
|0,2=>0x33333333333333333030303030303030333333333333333330303030303030304444404044444040444440404444404044444040444440404444404044444040000000000000000000000000000000033333333333333333333333300000000cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000033333333000000003333333300000000333333330000000000000000ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8cb333303033333030333330303333303033333030333330303333303033333030ccccccc0ccccccc0ccccccc0ccccccc0ccccccc0ccccccc0ccccccc0ccccccc3333330033333300333333003333330033333300333333003333330033333300cccccccccccccccccccccccccccccccccccccccccccccccccccccccc000000033333333333333333333333300000000333333333333333333333333000000000000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8ca222222233333333222222223333333322222222333322222222222233332222cccccccc0000cccccccccccc0000cccccccccccc00008888cccccccc00008888000000000000000000000000000000033333333333322223333333333332222
|_,_=>0
def stPool : Nat → Nat
|0=>0x3020203200808f0e20683260808b1034913023c4040a241011e1c4171a1408f0c1068c040478808149901e384041a28b011e20205205078e1010282021c304064c1010e2068304045861a4808f0c102901e383040a4480f1c1068c040458814241010e20182021c30504040040608080
|1=>0x200808b0c48290023c3040a4010f3c18205207408f0c10905224008f083450904045880a448021e782052240e811e106850404e060814982021c4040a40602022c40d0a0808b0c10296023cd880814d101e384041a1408f0c10a8504045990c1051004043880834182023c3040a4008f
|2=>0x200808f44202294c14802023c40d14401011620205200808f50202120a688011e2020d4e401011e2020d144008f1010a85344010f3c202053440e811e2020d0640101163c40d4c0c802023c405209408f0c102890404799101119004047a2101029004047a11010290040479f1010185
|3=>0x2abc29120047845c148011e202151a141011e182170a4008f382020d14401013820205200808f5a2020a0a24802022c405200808b4020205260808b32202290a40101163c405200808f582020d064c1011e20205480808f322020520047a01010aab0a401011e20205200808f542020a
|4=>0x23c3880828802022d10808148011e182150a401011ecc4041a488011e202321a148011e2020d0a4c101382022e0a40101382022f0a4008f0c102b1200808f1010190040458f4420685260808b101029120047842ab8290040458808c0290040478808342a404047880834293023c404
|5=>0x1e202171a288011e202320a588011e20205264010f3c202052640e811e2020520dc7b610102901e3840464148011e2020d0a5808f1010290040458f6a209052004a0f1010290180808f10105052c4008f1010290045079e10102903a04a0f1010290040458608d029004047880814802
|6=>0x1e2020d4c14482023c4057c588011e20205224013d023c205200808f782023b0a401011e202030a44802023c20d14241011e20205200479c1010aa60a24802023c405200808f742020d0a0808f7220205120808b1e644030a4c802022c40d0a41c011e202120a4c8011e2020d4640101
|7=>0x4047880814802022c7991010685260808f1011705200808f1010290040610f101029004f408f0c10505200809c1010291209408f09042900404788080c2900404786085c685260478809002900404788085d70520047880814838023ce080834289040458f10148011efc4040a41c01
|8=>0x1e202054840101163c4041a9829004047880828289200808f101090520047880814801283c4042b10290023c4042a5c685200478808148021e784040a401011e644040a40e811e2022e1414802023c4040a688027a0478808bc2900250788081489004047840a401011f0c4040614d10
|9=>0x1a14802023c40446282900404788088c29004047880834290040479c1011305200808f1010293200808b1011185200808b1e202170a4008f10102a4200808f101148512401011e20205264008f1010a85200808f0c1029a209408f1010685200808b1e2020d0a241011e2022f0a4c801
|10=>0x7a0478808bc29a20047880814802023d1080814802023dc88080c293200808f10102c7200478808282c620047880834290023c4042a148027a04a0f1010290040458f44202290a401011e202030a40101283c4040a588011e202450a401011e20205200808f382020d06401011e20229
|11=>0x1e202054824802023c4040a4008f6c2022e1a14802023c4040a401011e804040a401011e225041a28802023c4041414802022c4040a4c825023c4044e14802023c40414148011e202150a24802022c7880614802022c7880b24802023c4040a41281283c4040a688011e202150a4c802
|12=>0xa4008f1010aaf0a4008f10102c8200808f10102c62004788082829004047880814d1004047880814802022c788083429004047880814825023c4040a4013d023c4040a24802023c4040614802023c4040a40137023c4040a412b71e20205200808f6a20205200808f9a2024c0a40101
|13=>0x14802023c4040a4c802023c4040a40101283c4048814802023c4040a401011f2c4040a4014e023c404
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x4a8045
|5,0=>0x70c0c981630266040c06980a300e6
|6,0=>0x1f6e3d1c76b8e671bee361c68b8ca7186e2f1c5ab8ae714ee281c4cb8927116e211c3eb87670dee1a1c30b85a70a6e131c22b83e7
|7,0=>0x5db0b9616ec2d675a0cb25d613aba85650aaa151429a85250a2dd41c27b84e709b1d32425d74ab0936122c23e746d08ba113421f742f083e103c1ff83f0e7c20f4b9e183b307460e4c1c1837306c60d4c1a1833306460c4c18182f305c60b4c16182b305460a4c141827304c6094c1227235044a08541028
|7,1=>0x1ed43d287950f0ddddc3b387570e8e1cdc39387170e11dbebb7586db0d961aec355869b0d1619ec335865b0c9618ec315861b0c1617ec2f58
|8,0=>0xbc937722ea45cc8b8916f22da45ac8b4916722ca458c8b0915ee6b9c56b8ac7156a6a9bd4b8a8714ea698cd298a413465e88c5098a0313e2677cce789bd335a26744c5997cf2da256cca5893cf25a246cc8588fb11d2635cc6298b6f14e225c4438878f0d2216bc249837304e2063c0487f72fca5f543e28
|8,1=>0x30abe0d8c0b17f62fa4ded7
|9,0=>0x35046988d211a2234046797ce4f9aa331be5b8ca7192e321c63c7c6918b2312461c8
|10,0=>0x6a87
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 79 then fld (dictB (i / 512) (i / 32 % 16)) 254 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x1e110a410a11203d48432611203d461714110a3d1a111a130a414c3f1a130a410a55041214130a3d0a410a3d041206070a11025504120a410a4104052620203d4843123d2011461714110a3d38111a3f0a41401114430a3d2620203d1a2c24070a5504122620203d1a3f1a2c0a1126201a090a4124070a55041224070a550412
|1=>0x4121e112620203d0a912611203d1a2c1e110a411e1104122620203d0a550a4104121a550a4104120a411e711a3f0a410a092620203d20890a2e1e110a2e1e112623203d04120a4d203d4e4114130a3d2611203d203d0a41041226230a09203d04120a412620203d0a410a41142720110a3d0a3d14430a3d1e1106410a111a2e
|2=>0xa412055041226230211203d0a922611203d1a1326230a11203d1a3f0a4152130a252011464314110a3d123f2011202e1e11203d0a1104711a3f0a410a55041214110a3d0a3d1a090a412055041206070a110255041220960405023d24070a5504121a550a41041220550a4104120a2620110a5504122055041206070a110255
|3=>0x1e2104120a2104121a090a4106070a11202e1e110255041214410a3d202102110a091e212623203d20de023d0a112021202e1e110a41203d0a4d203d1ed50a26201102112620203d5c3f14410a3d26230405203d0a65202e1e110a112620203d203d1a090a415c130a4d203d1a091a3f0a410a410a5a2055041204711a3f0a41
|4=>0xa11203d9009200520090a3d0a41041202111e210a2e1e1106410a110a111e212055041206210a111a3f0a410a410a111a110a4114110a3d14110a3d1a3f0a411a130a411e11203d0a2d1e111a090a412611203d0a252011203d04122620203d040520211e110a4120110a410a09203d202d1e111a130a4120110a3d0a550412
|5=>0x203d1e210a211011022104120a09200520090a3d20211e110a410405021120110a11023d0405023d0a262011903f200588130a21123d2011209604051a3d0a4114430a3d0b2e10110a410a3d1e110a3d0405203d14130a3d0a3d041220111e111e110a112605203d04051e21202104120211203d20210a090a2e1e11123f2011
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x91000000000000000000000000000444000000000038c00000000003081620a1048800000006300000cc000003
|7,0=>0x4c925c92a4923479a30d12687242900010648123f91f0cf267633a89c8c0006f33619ac4d0665331198080005d32d9160cac453328193c49864b125091cc8c244221890487c63c21c980000000001b18ccc0003031710b0852627212909044622030e9868c2e6143
|7,1=>0x1be6dc36c9b58da66d03669b28d922c72630b0cd806bf15e92e8d6e6b615998001624ae3559aa494e4a52511a8093c49b3
|8,0=>0xb01578ab855a2ac1558aa85522a81538a9854a2a41518a885422a014f8a7853a29c14d8a6853229814b8a5852a2941498a485222901478a3851a28c1458a285122881438a1850a2841418a0850228013f89f84fa27c13d89e84f227813b89d84ea27413989c84e22
|8,1=>0x2d856a2b41598ac85622
|9,0=>0x2fe37e1be8df06f637a1bc8de06ee3761ba8dd06e63721b88dc06de36e1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 16 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 13 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x20080000040000000048980000090000000100800000200000000241800000412000000406000000800000000b680000016100000022600000043400000082000000102000000202000000400000000480000000400000000480000000880000001000000001c0000000240000000400000000600000000800000000800000000800000000800000000
|1=>0x83666000106cc80002008080002173300004142600008244c0000a8b880001497100002804200004007c0000800f00001001100002000a00003458c000064b180000c00100001023e00002040c000040028000051350000078440000068c800000cbf80000191300000322200000640c00000b9180000112100000220000000424000000809800001010
|2=>0x40c34660081864cc01030c1980203193100404b2620045868cc00400000000561b330009c7466001386ecc00236cb98004699330008d324600119648c00230fd9800461b330008c34660011864cc00230c19800443a220004c34660008868880010183180020306000040448400078604c00070d198000659330000c3e66000186ccc00030c19800061033
|3=>0x308c30660601004440c00089880e5e183301c8c32660291868cc05230cb980a4619330148c30660281060cc030f0c1f8061e183300c0d323e0181a644c03030c9980606191300c05122601808245c022f0c198044699330049c342e009187cdc01230d9b8024618370048c206e008586ccc0103acb98020719330040e307e0081c60cc01038819802061bb3
|4=>0x100058644d000b0c99a0014011520c3c3066201186ccc230f0c1982a061f330540c36660a818684c15030c19828040103050002246061187ccc0c230d99818461a13
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>0xe00000000000000000400000002000000090c0c0300000d00060006
|7,0=>0xf3d343f1424220f05010e2b2a1c083d0f052400162e0f1e101119060a184806063e46494c0606000606063a15291e3b004a4706333c122300171b0f1f2025054059060f0e1a02060f0b2d0000003430000f02020702020e1c422e37140f
|8,0=>0x66548b782f8a366278615c69645f6f5b7581868c885e722c58604f7e27557d57795d52313865214e6e395073326b418728536a2f26134b807a518e705a3584827689831d6763
|9,0=>0x687f777b7c45436d566285714d428d6c4474
|10,0=>0x41
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 35 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 1 then [(dom_237,8,runOps true dom_237 (0,roots_237) ops)] else [])++(if pm.testBit 2 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 3 then [(dzo_172_64,5,runOps true dzo_172_64 (0,roots_172) ops)] else [])++(if pm.testBit 4 then [(dom_252,8,runOps true dom_252 (0,roots_252) ops)] else [])++(if pm.testBit 5 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 6 then [(dzo_81_4,4,runOps true dzo_81_4 (0,roots_81) ops)] else [])++(if pm.testBit 7 then [(dom_229,7,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 8 then [(dzo_117_8,7,runOps true dzo_117_8 (0,roots_117) ops)] else [])++(if pm.testBit 9 then [(dzo_245_8,8,runOps true dzo_245_8 (0,roots_245) ops)] else [])++(if pm.testBit 10 then [(dom_213,7,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 11 then [(dom_117,7,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 12 then [(dom_221,8,runOps true dom_221 (0,roots_221) ops)] else [])++(if pm.testBit 13 then [(dzo_229_8,5,runOps true dzo_229_8 (0,roots_229) ops)] else [])++(if pm.testBit 14 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])++(if pm.testBit 15 then [(dom_101,4,runOps true dom_101 (0,roots_101) ops)] else [])++(if pm.testBit 16 then [(dom_220,5,runOps true dom_220 (0,roots_220) ops)] else [])++(if pm.testBit 17 then [(dom_189,8,runOps true dom_189 (0,roots_189) ops)] else [])++(if pm.testBit 18 then [(dom_249,8,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 19 then [(dzo_241_12,6,runOps true dzo_241_12 (0,roots_241) ops)] else [])++(if pm.testBit 20 then [(dzo_241_4,6,runOps true dzo_241_4 (0,roots_241) ops)] else [])++(if pm.testBit 21 then [(dzo_209_8,5,runOps true dzo_209_8 (0,roots_209) ops)] else [])++(if pm.testBit 22 then [(dzo_173_64,6,runOps true dzo_173_64 (0,roots_173) ops)] else [])++(if pm.testBit 23 then [(dom_244,7,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 24 then [(dzo_241_8,6,runOps true dzo_241_8 (0,roots_241) ops)] else [])++(if pm.testBit 25 then [(dzo_188_64,6,runOps true dzo_188_64 (0,roots_188) ops)] else [])++(if pm.testBit 26 then [(dzo_113_4,5,runOps true dzo_113_4 (0,roots_113) ops)] else [])++(if pm.testBit 27 then [(dzo_189_64,7,runOps true dzo_189_64 (0,roots_189) ops)] else [])++(if pm.testBit 28 then [(dom_188,6,runOps true dom_188 (0,roots_188) ops)] else [])++(if pm.testBit 29 then [(dom_173,6,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 30 then [(dom_248,5,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 31 then [(dom_241,6,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 32 then [(dom_233,5,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 33 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 34 then [(dzo_209_4,5,runOps true dzo_209_4 (0,roots_209) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_253 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_172_64_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_81_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_117_8_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_245_8_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_229_8_101 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_12_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_209_8_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_64_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_8_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_188_64_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_113_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_189_64_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_209_4_81 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_245 9 s (0, roots_245) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_253 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_253 goalM v ys) : RunD true dom_253 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 28 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 28 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 94 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 94 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 70 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 70 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 18 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
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
def RootG (s : Nat) : Bool :=
  scr true dom_253 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_253 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_253 roots_253 goal_253 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_253

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 := S_253.noCircuit

end Prior28450

namespace Prior27979
open PEqualNP.Outside.L_meta_30304

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 10 :=
  lower_masked_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffffffff000000000000000000000000ffffffff00000000, 32)] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    Prior27923.lowS_243 (by decide +kernel)

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 2, 34)] (by decide +kernel) (by decide +kernel) lowS_219

end Prior27979

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 8} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 8} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 8) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 8) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 8) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

private def Sample (point : ℕ → X) (d : ℕ) (f : F) (v : ℕ) : Prop :=
  ∀ r < 256, d.testBit r = true → v.testBit r = f (point r)

private theorem sample_cut {point : ℕ → X} {d v w : ℕ} {f : F}
    (hd : d &&& mask256 = d) (hv : Sample point d f v) (hw : Sample point d f w) :
    v &&& d = w &&& d := by
  apply Nat.eq_of_testBit_eq
  intro r
  simp only [Nat.testBit_and]
  cases hr : d.testBit r
  · simp
  · have h := congrArg (fun a : ℕ => a.testBit r) hd
    rw [Nat.testBit_and, hr, Bool.true_and, mask256_bit] at h
    have hlt := of_decide_eq_true h
    rw [hv r hlt hr, hw r hlt hr]

private theorem sample_operands {point : ℕ → X} {d : ℕ} {bank : List ℕ} {s : Set F}
    (hd : d &&& mask256 = d)
    (hs : ∀ u ∈ s, ∃ v, Sample point d u v ∧ Avail true d bank v)
    {u : F} (h : Av s u) :
    ∃ v, Sample point d u v ∧ Avail true d bank v := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,he | he⟩
  · cases b
    · exact ⟨0,by intro r _ _; simp,Or.inl (Or.inl (by simp))⟩
    · exact ⟨d,by intro r _ hr; exact hr,Or.inl (Or.inr (Nat.and_self d))⟩
  · rw [he]
    exact hs a ha
  · rw [he]
    obtain ⟨v,hv,hav⟩ := hs a ha
    refine ⟨negD d v,?_,avail_neg hd hav⟩
    intro r hlt hr
    simp [negD, Nat.testBit_and, Nat.testBit_xor, hv r hlt hr, mask256_bit, hlt, hr]

private theorem prog_sample {point : ℕ → X} {d : ℕ} {roots : List ℕ}
    (hd : d &&& mask256 = d) {s : Set F} {f : F} {k : ℕ} (p : Prog s f k) :
    ∀ (m : ℕ) (bank : List ℕ), NatReach true d roots m bank →
      (∀ u ∈ s, ∃ v, Sample point d u v ∧ Avail true d bank v) →
      ∃ bank' v, NatReach true d roots (m+k) bank' ∧
        Sample point d f v ∧ Avail true d bank' v := by
  induction p with
  | done ha =>
    intro m bank hm hs
    obtain ⟨v,hv,hav⟩ := sample_operands hd hs ha
    exact ⟨bank,v,hm,hv,hav⟩
  | @gate s f a b k t ha hb _ ih =>
    intro m bank hm hs
    obtain ⟨v,hv,hav⟩ := sample_operands hd hs ha
    obtain ⟨w,hw,haw⟩ := sample_operands hd hs hb
    let op : ℕ := if t then 0 else 1
    let z := opD d op v w
    have hop : allowedB true op = true := by cases t <;> decide
    have hreach : NatReach true d roots (m+1) (z::bank) :=
      ⟨bank,v,w,op,hop,rfl,hm,hav,haw⟩
    have hnew : Sample point d (comb t a b) z := by
      intro r hr hh
      cases t <;>
        simp [z, op, opD, andD, orD, comb, Nat.testBit_and, Nat.testBit_or, hh,
          hv r hr hh, hw r hr hh]
    have hbank : ∀ u ∈ insert (comb t a b) s,
        ∃ v, Sample point d u v ∧ Avail true d (z::bank) v := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact ⟨z,hnew,Or.inr (Or.inl ⟨z,List.mem_cons_self,rfl⟩)⟩
      · obtain ⟨v,hv,hav⟩ := hs u hu
        exact ⟨v,hv,avail_cons z v hav⟩
    obtain ⟨bank',v',hr',hv',ha'⟩ := ih (m+1) (z::bank) hreach hbank
    rw [show m+1+k = m+(k+1) by omega] at hr'
    exact ⟨bank',v',hr',hv',ha'⟩

private theorem column_bits : ∀ (i : Fin 8) (r : Fin 256),
    (xs256.getD i.val 0).testBit r.val = pt8 r.val i := by
  decide +kernel

private theorem from_mask {f : F} {d T L : ℕ} {roots : List ℕ} (perm : Fin 8 → Fin 8)
    (hd : d &&& mask256 = d)
    (hc : ∀ i : Fin 8, availB true d roots (xs256.getD (perm i).val 0) = true)
    (ht : ∀ r : Fin 256, T.testBit r.val = f (fun i => pt8 r.val (perm i)))
    (h : Lower true d roots T L) : Low L f := by
  intro k prog
  let point := fun (r : ℕ) (i : Fin 8) => pt8 r (perm i)
  have hstock : ∀ u ∈ stock, ∃ v, Sample point d u v ∧ Avail true d roots v := by
    rintro u ⟨i,rfl⟩
    exact ⟨xs256.getD (perm i).val 0,fun r hr _ => column_bits (perm i) ⟨r,hr⟩,
      (availB_iff true d roots _).mp (hc i)⟩
  obtain ⟨bank,v,hr,hv,ha⟩ := prog_sample hd prog 0 roots rfl hstock
  have hm : v &&& d = T &&& d := sample_cut hd hv (fun r hr _ => ht ⟨r,hr⟩)
  exact h k bank (by simpa only [Nat.zero_add] using hr) (avail_of_eq hm ha)

abbrev GateTrace := List (Bool × F × F)

def TraceValid (s : Set F) (f : F) : GateTrace → Prop
  | [] => Av s f
  | g :: gs =>
    Av s g.2.1 ∧ Av s g.2.2 ∧ TraceValid (insert (comb g.1 g.2.1 g.2.2) s) f gs

theorem prog_trace {s : Set F} {f : F} {k : ℕ} (p : Prog s f k) :
    ∃ gs : GateTrace, gs.length = k ∧ TraceValid s f gs := by
  induction p with
  | done ha => exact ⟨[],rfl,ha⟩
  | @gate s f a b k tag ha hb _ ih =>
    obtain ⟨gs,hlen,hr⟩ := ih
    exact ⟨(tag,a,b)::gs,by simp [hlen],ha,hb,hr⟩

theorem trace_prog {s : Set F} {f : F} {gs : GateTrace} (hr : TraceValid s f gs) :
    Prog s f gs.length := by
  induction gs generalizing s with
  | nil => exact .done hr
  | cons g gs ih => exact .gate g.1 hr.1 hr.2.1 (ih hr.2.2)

def cutGate (i : Fin 8) (c : Bool) (g : Bool × F × F) : Prop :=
  Cst (rs i c g.2.1) ∨ Cst (rs i c g.2.2) ∨ Cst (rs i c (comb g.1 g.2.1 g.2.2))

noncomputable def cutCount (i : Fin 8) (c : Bool) (gs : GateTrace) : ℕ :=
  gs.countP fun g => @decide (cutGate i c g) (Classical.propDecidable _)

private theorem cut_count_cons (i : Fin 8) (c : Bool) (g : Bool × F × F) (gs : GateTrace) :
    cutCount i c (g::gs) = cutCount i c gs +
      (@ite ℕ (cutGate i c g) (Classical.propDecidable _) 1 0) := by
  classical
  simp [cutCount, List.countP_cons]

theorem cutCount_append (i : Fin 8) (c : Bool) (pre post : GateTrace) :
    cutCount i c (pre ++ post) = cutCount i c pre + cutCount i c post := by
  simp [cutCount, List.countP_append]

theorem cutCount_cons_cut (i : Fin 8) (c : Bool) (g : Bool × F × F)
    (gs : GateTrace) (hc : cutGate i c g) :
    cutCount i c (g::gs) = cutCount i c gs + 1 := by
  rw [cut_count_cons, ite_eq_left hc]

theorem cutCount_positive (i : Fin 8) (c : Bool) {g : Bool × F × F}
    {gs : GateTrace} (hg : g ∈ gs) (hc : cutGate i c g) : 0 < cutCount i c gs := by
  induction gs with
  | nil => simp at hg
  | cons a gs ih =>
    rw [cut_count_cons]
    rcases List.mem_cons.mp hg with rfl | hm
    · rw [ite_eq_left hc]
      omega
    · have h := ih hm
      omega

theorem restriction_budget {s : Set F} {f : F} {gs : GateTrace}
    (i : Fin 8) (c : Bool) (run : TraceValid s f gs) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) :
    ∃ k, k + cutCount i c gs ≤ gs.length ∧ Prog t (rs i c f) k := by
  classical
  induction gs generalizing s t with
  | nil => exact ⟨0,by simp [cutCount],.done (av_rs hs run)⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,htail⟩ := run
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : cutGate i c g
    · have hresult : Av t (rs i c (comb g.1 g.2.1 g.2.2)) := by
        rcases hc with h | h | h
        · exact av_cheap g.1 pa pb (Or.inl h)
        · exact av_cheap g.1 pa pb (Or.inr h)
        · exact Or.inl h
      obtain ⟨k,hk,hr⟩ := ih htail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact hresult
        · exact hs _ hu)
      refine ⟨k,?_ ,hr⟩
      rw [cut_count_cons, ite_eq_left hc, List.length_cons]
      omega
    · obtain ⟨k,hk,hr⟩ := ih htail (insert (comb g.1 (rs i c g.2.1) (rs i c g.2.2)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨k+1,?_ ,.gate g.1 pa pb hr⟩
      rw [cut_count_cons, ite_eq_right hc, List.length_cons]
      omega

theorem restrict_lower_count {f : F} {gs : GateTrace} {i : Fin 8} {c : Bool} {n r : ℕ}
    (run : TraceValid stock f gs) (cnt : r ≤ cutCount i c gs) (low : Low n (rs i c f)) :
    n+r ≤ gs.length := by
  obtain ⟨k,hk,hprog⟩ := restriction_budget i c run stock (stock_rs i c)
  have h := low k hprog
  omega

def traceBank (s : Set F) : GateTrace → Set F
  | [] => s
  | g :: gs => traceBank (insert (comb g.1 g.2.1 g.2.2) s) gs

private theorem av_rebase {s t : Set F} {f : F}
    (hs : ∀ u ∈ s, Av t u) (h : Av s f) : Av t f := by
  rcases h with h | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl h
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem trace_rebase {s t : Set F} {f : F} {gs : GateTrace}
    (run : TraceValid s f gs) (hs : ∀ u ∈ s, Av t u) : TraceValid t f gs := by
  induction gs generalizing s t with
  | nil => exact av_rebase hs run
  | cons g gs ih =>
    obtain ⟨ha,hb,ht⟩ := run
    refine ⟨av_rebase hs ha,av_rebase hs hb,?_⟩
    apply ih ht
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact av_mem (Set.mem_insert _ _)
    · exact av_ins _ (hs _ hu)

theorem trace_remove_redundant {s : Set F} {f : F} (pre : GateTrace)
    (g : Bool × F × F) (post : GateTrace) (run : TraceValid s f (pre ++ g::post))
    (redundant : Av (traceBank s pre) (comb g.1 g.2.1 g.2.2)) :
    TraceValid s f (pre ++ post) := by
  induction pre generalizing s with
  | nil =>
    apply trace_rebase run.2.2
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact redundant
    · exact av_mem hu
  | cons h pre ih =>
    exact ⟨run.1,run.2.1,ih run.2.2 redundant⟩

theorem mem_traceBank {s : Set F} {u : F} {gs : GateTrace} :
    u ∈ traceBank s gs ↔ u ∈ s ∨ ∃ g ∈ gs, u = comb g.1 g.2.1 g.2.2 := by
  induction gs generalizing s with
  | nil => simp [traceBank]
  | cons g gs ih =>
    rw [traceBank, ih]
    constructor
    · rintro (hu | ⟨h,hh,he⟩)
      rcases Set.mem_insert_iff.mp hu with he | hu
      · exact Or.inr ⟨g,List.mem_cons_self,he⟩
      · exact Or.inl hu
      · exact Or.inr ⟨h,List.mem_cons_of_mem _ hh,he⟩
    · rintro (hu | ⟨h,hh,he⟩)
      · exact Or.inl (Set.mem_insert_of_mem _ hu)
      · rcases List.mem_cons.mp hh with rfl | hh
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl he))
        · exact Or.inr ⟨h,hh,he⟩

def target : F := fun x =>
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) ||
  (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 5 && x 6) ||
  (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) ||
  (x 5 && x 7)

def Good30304 (i : Fin 8) : Prop := i ≠ 3 ∧ i ≠ 7

instance (i : Fin 8) : Decidable (Good30304 i) :=
  inferInstanceAs (Decidable (i ≠ 3 ∧ i ≠ 7))

private def goodRow30304 (i : Fin 8) (a b : Bool) : ℕ :=
  if a then (![8, 24, 40, 0, 10, 12, 10, 0] : Fin 8 → ℕ) i
  else if b then (![128, 128, 192, 0, 128, 128, 132, 0] : Fin 8 → ℕ) i
  else (![32, 16, 32, 0, 2, 1, 1, 0] : Fin 8 → ℕ) i

private theorem goodRow_correct30304 : ∀ (i : Fin 8) (a b : Bool),
    Good30304 i → (a && b) = false →
    let x := pt (goodRow30304 i a b)
    x 3 = a ∧ x 7 = b ∧ x i = false ∧ target x = false ∧
      target (Function.update x i true) = true := by decide +kernel

theorem good_influence30304 (i : Fin 8) (a b : Bool) (hi : Good30304 i)
    (hab : (a && b) = false) : ∃ x : X,
    x 3 = a ∧ x 7 = b ∧ x i = false ∧ target x = false ∧
      target (Function.update x i true) = true :=
  ⟨pt (goodRow30304 i a b), goodRow_correct30304 i a b hi hab⟩

private def pairRow30304 (i j : Fin 8) : ℕ :=
  (![
    ![0, 8, 8, 0, 2, 4, 2, 0],
    ![8, 0, 16, 0, 64, 1, 1, 0],
    ![8, 16, 0, 0, 2, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 64, 2, 0, 0, 1, 1, 0],
    ![4, 1, 1, 0, 1, 0, 2, 0],
    ![2, 1, 1, 0, 1, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]] : Fin 8 → Fin 8 → ℕ) i j

theorem bad3_influence30304 : ∃ x : X, x 7 = false ∧ x 3 = false ∧
    target x = false ∧ target (Function.update x 3 true) = true :=
  ⟨pt 1, by decide +kernel⟩

theorem good_notSmp30304 (i : Fin 8) (hi : Good30304 i) : ¬ Smp i false target := by
  have notInd : ¬ Ind i target := by
    obtain ⟨x, _, _, _, hfalse, htrue⟩ := good_influence30304 i false false hi rfl
    intro h
    exact Bool.noConfusion (htrue.symm.trans ((h x true).trans hfalse))
  refine fun h => h.elim notInd ?_
  rintro ⟨b, hb⟩
  have h0 : rs i false target (pt 0) = false := by
    have hc : ∀ j : Fin 8, rs j false target (pt 0) = false := by decide +kernel
    exact hc i
  have h1 : rs i false target (pt 136) = true := by
    have hc : ∀ j : Fin 8, Good30304 j → rs j false target (pt 136) = true := by decide +kernel
    exact hc i hi
  exact Bool.noConfusion (h1.symm.trans ((congrFun hb _).trans ((congrFun hb _).symm.trans h0)))

private def pairInput30304 (x : X) (i j : Fin 8) (v : Fin 4) : X :=
  Function.update (Function.update x i (v.val.testBit 0)) j (v.val.testBit 1)

private theorem pairGateRow_correct30304 : ∀ i j : Fin 8,
    Good30304 i → Good30304 j → i ≠ j → ∀ tag sa sb : Bool,
    let x := pt (pairRow30304 i j)
    let a : F := fun x => xor (x i) sa
    let b : F := fun x => xor (x j) sb
    ∃ v w : Fin 4,
      comb tag a b (pairInput30304 x i j v) = comb tag a b (pairInput30304 x i j w) ∧
      target (pairInput30304 x i j v) ≠ target (pairInput30304 x i j w) := by
  decide +kernel

theorem good_pair_gate_distinguish30304 (i j : Fin 8) (hi : Good30304 i)
    (hj : Good30304 j) (hij : i ≠ j) (tag sa sb : Bool) : ∃ x y : X,
    (∀ k, k ≠ i → k ≠ j → x k = y k) ∧
    comb tag (fun z => xor (z i) sa) (fun z => xor (z j) sb) x =
      comb tag (fun z => xor (z i) sa) (fun z => xor (z j) sb) y ∧ target x ≠ target y := by
  obtain ⟨v, w, hEq, hNe⟩ := pairGateRow_correct30304 i j hi hj hij tag sa sb
  refine ⟨pairInput30304 (pt (pairRow30304 i j)) i j v,
    pairInput30304 (pt (pairRow30304 i j)) i j w, ?_, hEq, hNe⟩
  intro k hki hkj
  simp [pairInput30304, Function.update_of_ne hki, Function.update_of_ne hkj]

theorem target_not_initial30304 : ¬ Av stock target := by
  rintro (⟨c, hc⟩ | ⟨u, ⟨i, rfl⟩, hu⟩)
  · have hn : target (pt 0) ≠ target (pt 9) := by decide +kernel
    exact hn ((congrFun hc (pt 0)).trans (congrFun hc (pt 9)).symm)
  · rcases hu with hu | hu
    · have hn : ∀ i : Fin 8, target (pt (2 ^ i.val)) ≠ pt (2 ^ i.val) i := by decide +kernel
      exact hn i (congrFun hu _)
    · have hn : ∀ i : Fin 8, target (pt 0) ≠ !(pt 0 i) := by decide +kernel
      exact hn i (congrFun hu _)

theorem good_operand_rigidity30304 (i : Fin 8) (hi : Good30304 i) (u : F)
    (hdep : ∀ x y : X, x 3 = y 3 → x 7 = y 7 → u x = u y)
    (hmask : ∀ x : X, x i = false → u x = true →
      target x = target (Function.update x i true)) :
    u = (fun _ => false) ∨ u = (fun x => x 3 && x 7) := by
  have hzero (x : X) (hx : (x 3 && x 7) = false) : u x = false := by
    obtain ⟨y, h3, h7, hyi, hfalse, htrue⟩ := good_influence30304 i (x 3) (x 7) hi hx
    cases hu : u x
    · rfl
    · have hc : u y = true := (hdep y x h3 h7).trans hu
      exact Bool.noConfusion (hfalse.symm.trans ((hmask y hyi hc).trans htrue))
  have hmatch (x : X) (hx : (x 3 && x 7) = true) : u x = u (pt 136) := by
    simp only [Bool.and_eq_true] at hx
    obtain ⟨h3, h7⟩ := hx
    apply hdep x (pt 136)
    · exact h3
    · exact h7
  cases hu : u (pt 136)
  · left
    funext x
    cases hx : x 3 && x 7
    · exact hzero x hx
    · exact (hmatch x hx).trans hu
  · right
    funext x
    cases hx : x 3 && x 7
    · exact hzero x hx
    · exact (hmatch x hx).trans hu

private theorem from_mask_on30304 {f : F} {d T L : ℕ} {roots : List ℕ} (perm : Fin 8 → Fin 8)
    (hd : d &&& mask256 = d)
    (hc : ∀ i : Fin 8, availB true d roots (xs256.getD (perm i).val 0) = true)
    (ht : ∀ r : Fin 256, d.testBit r.val = true → T.testBit r.val = f (fun i => pt8 r.val (perm i)))
    (h : Lower true d roots T L) : Low L f := by
  intro k prog
  let point := fun (r : ℕ) (i : Fin 8) => pt8 r (perm i)
  have hstock : ∀ u ∈ stock, ∃ v, Sample point d u v ∧ Avail true d roots v := by
    rintro u ⟨i,rfl⟩
    exact ⟨xs256.getD (perm i).val 0,fun r hr _ => column_bits (perm i) ⟨r,hr⟩,
      (availB_iff true d roots _).mp (hc i)⟩
  obtain ⟨bank,v,hr,hv,ha⟩ := prog_sample hd prog 0 roots rfl hstock
  have hm : v &&& d = T &&& d := sample_cut hd hv (fun r hr hrD => ht ⟨r,hr⟩ hrD)
  exact h k bank (by simpa only [Nat.zero_add] using hr) (avail_of_eq hm ha)

private theorem pin1_lower30304 : Low 11 (rs 1 false (target)) := by
  exact from_mask ![4, 2, 3, 6, 5, 7, 0, 1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior27979.lowS_251

private theorem pin0_lower30304 : Low 11 (rs 0 false (target)) := by
  exact from_mask ![1, 5, 6, 3, 2, 4, 0, 7] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior28450.lowS_253

private theorem pin2_lower30304 : Low 11 (rs 2 false (target)) := by
  exact from_mask ![7, 0, 3, 2, 4, 1, 5, 6] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior28586.lowS_247

private theorem pin52_false_lower30304 : Low 9 (rs 2 false (rs 5 false target)) := by
  exact from_mask ![0, 7, 1, 4, 2, 3, 5, 6] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior28586.lowS_245

private theorem pin52_true_lower30304 : Low 9 (rs 2 true (rs 5 false target)) := by
  exact from_mask_on30304 ![0, 1, 2, 4, 5, 3, 6, 7] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior27921.lowS_zo_243_8_179

private theorem pin5_lower30304 : Low 11 (rs 5 false target) :=
  two 2 (good_at 64 9 0 (by decide +kernel)) (good_at 64 9 0 (by decide +kernel))
    pin52_false_lower30304 pin52_true_lower30304


private theorem pin6_lower30304 : Low 11 (rs 6 false (target)) := by
  exact from_mask ![5, 0, 3, 2, 4, 6, 1, 7] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior29242.lowS_253

private theorem pin41_lower30304 : Low 10 (rs 1 false (rs 4 false (target))) := by
  exact from_mask ![6, 2, 5, 4, 3, 7, 1, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior27923.lowS_243

private theorem pin30_lower30304 : Low 9 (rs 0 false (rs 3 false (target))) := by
  exact from_mask ![1, 0, 2, 3, 6, 7, 5, 4] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Prior28450.lowS_245

private theorem pin4_lower30304 : Low 11 (rs 4 false target) :=
  one 1 false (good_at 64 9 0 (by decide +kernel)) pin41_lower30304

theorem bad3_lower30304 : Low 10 (rs 3 false target) :=
  one 0 false (good_at 32 18 0 (by decide +kernel)) pin30_lower30304

theorem good_pin_lower30304 (i : Fin 8) (hi : Good30304 i) : Low 11 (rs i false target) := by
  have casesGood : ∀ j : Fin 8, Good30304 j →
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by decide +kernel
  rcases casesGood i hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pin0_lower30304
  · exact pin1_lower30304
  · exact pin2_lower30304
  · exact pin4_lower30304
  · exact pin5_lower30304
  · exact pin6_lower30304

abbrev StepGate := Bool × F × F

def resultOf (g : StepGate) : F := comb g.1 g.2.1 g.2.2

def raw (i : Fin 8) : F := fun x => x i

def signed (i : Fin 8) (b : Bool) : F := fun x => if b then !x i else x i

def Literal (i : Fin 8) (u : F) : Prop := ∃ b, u = signed i b

def Read (i : Fin 8) (g : StepGate) : Prop := Literal i g.2.1 ∨ Literal i g.2.2

def Agreement (vary : Fin 8 → Prop) (x y : X) (s : Set F) : Prop :=
  ∀ u ∈ s, u x = u y ∨ ∃ i, vary i ∧ u = raw i

theorem stock_agreement {vary : Fin 8 → Prop} {x y : X}
    (h : ∀ i, ¬ vary i → x i = y i) : Agreement vary x y stock := by
  rintro u ⟨i, rfl⟩
  by_cases hi : vary i
  · exact .inr ⟨i, hi, rfl⟩
  · exact .inl (h i hi)

theorem agreement_av {vary : Fin 8 → Prop} {x y : X} {s : Set F} {u : F}
    (hs : Agreement vary x y s) (hu : Av s u)
    (hn : ∀ i, vary i → ¬ Literal i u) : u x = u y := by
  rcases hu with ⟨c, rfl⟩ | ⟨v, hv, eq | eq⟩
  · rfl
  · rcases hs v hv with h | ⟨i, hi, vi⟩
    · exact eq.symm ▸ h
    · exact False.elim (hn i hi ⟨false, eq.trans vi⟩)
  · rcases hs v hv with h | ⟨i, hi, vi⟩
    · rw [eq]
      exact congrArg Bool.not h
    · exact False.elim (hn i hi ⟨true, eq.trans (by rw [vi]; rfl)⟩)

theorem agreement_insert {vary : Fin 8 → Prop} {x y : X} {s : Set F} {u : F}
    (hs : Agreement vary x y s) (hu : u x = u y) : Agreement vary x y (insert u s) := by
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact .inl hu
  · exact hs v hv

theorem agreement_step {vary : Fin 8 → Prop} {x y : X} {s : Set F} {g : StepGate}
    (hs : Agreement vary x y s) (ha : Av s g.2.1) (hb : Av s g.2.2)
    (h : resultOf g x = resultOf g y ∨ ∀ i, vary i → ¬ Read i g) :
    Agreement vary x y (insert (resultOf g) s) := by
  apply agreement_insert hs
  rcases h with h | h
  · exact h
  have ea := agreement_av hs ha (fun i hi h' => h i hi (.inl h'))
  have eb := agreement_av hs hb (fun i hi h' => h i hi (.inr h'))
  simp only [resultOf, comb, ea, eb]

theorem literal_pin {i : Fin 8} {a : F} (h : Literal i a) (b : Bool) : Cst (rs i b a) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨if c then !b else b, by funext x; simp [rs, signed]⟩

theorem read_cuts {i : Fin 8} {g : StepGate} (hr : Read i g) (b : Bool) : cutGate i b g := by
  exact hr.elim (fun h => .inl (literal_pin h b)) (fun h => .inr (.inl (literal_pin h b)))

theorem agreement_trace {vary : Fin 8 → Prop} {x y : X} {s : Set F}
    {f : F} {cs : GateTrace} (hv : TraceValid s f cs)
    (hs : Agreement vary x y s)
    (hb : ∀ g ∈ cs, resultOf g x = resultOf g y ∨ ∀ i, vary i → ¬ Read i g) :
    Agreement vary x y (traceBank s cs) := by
  induction cs generalizing s with
  | nil => exact hs
  | cons g cs ih =>
    obtain ⟨ha, hz, hv⟩ := hv
    apply ih hv (agreement_step hs ha hz (hb _ (List.mem_cons_self ..)))
    exact fun g hg => hb g (List.mem_cons_of_mem _ hg)

theorem trace_final_agreement {vary : Fin 8 → Prop} {x y : X} {s : Set F}
    {f : F} {cs : GateTrace} (hv : TraceValid s f cs)
    (hs : Agreement vary x y s)
    (hb : ∀ g ∈ cs, resultOf g x = resultOf g y ∨ ∀ i, vary i → ¬ Read i g)
    (hf : ∀ i, vary i → ¬ Literal i f) : f x = f y := by
  induction cs generalizing s with
  | nil => exact agreement_av hs hv hf
  | cons g cs ih =>
    obtain ⟨ha, hz, hv⟩ := hv
    apply ih hv (agreement_step hs ha hz (hb _ (List.mem_cons_self ..)))
    exact fun g hg => hb g (List.mem_cons_of_mem _ hg)

theorem trace_valid_split {s : Set F} {pre post : GateTrace} {f : F}
    (h : TraceValid s f (pre ++ post)) :
    TraceValid s (fun _ => false) pre ∧ TraceValid (traceBank s pre) f post := by
  induction pre generalizing s with
  | nil => exact ⟨.inl ⟨false, rfl⟩, h⟩
  | cons g pre ih =>
    obtain ⟨ha, hb, h⟩ := h
    obtain ⟨hpre, hpost⟩ := ih h
    exact ⟨⟨ha, hb, hpre⟩, hpost⟩

theorem trace_pair_no_read {s : Set F} {cs : GateTrace} {x y : X} {i : Fin 8} {f : F}
    (hv : TraceValid s f cs) (hs : Agreement (fun j => j = i) x y s)
    (hb : ∀ g ∈ cs, resultOf g x = resultOf g y ∨ ¬ Read i g)
    (hf : ¬ Literal i f) : f x = f y :=
  trace_final_agreement hv hs
    (fun g hg => (hb g hg).imp_right (fun h _ e => e.symm ▸ h))
    (fun _ e => e.symm ▸ hf)

theorem split_first {α : Type} (p : α → Prop) (l : List α) (h : ∃ x ∈ l, p x) :
    ∃ pre a post, l = pre ++ a :: post ∧ p a ∧ ∀ x ∈ pre, ¬ p x := by
  classical
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : p a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · obtain ⟨pre, u, post, eq, hu, hn⟩ := ih (by
        obtain ⟨x, hm, hp⟩ := h
        exact ⟨x, (List.mem_cons.mp hm).resolve_left (fun e => ha (e ▸ hp)), hp⟩)
      exact ⟨a :: pre, u, post, by simp [eq], hu, by simpa using And.intro ha hn⟩

theorem av_subset {s t : Set F} {u : F} (hst : s ⊆ t) (h : Av s u) : Av t u := by
  rcases h with h | ⟨a, ha, h⟩
  · exact .inl h
  · exact .inr ⟨a, hst ha, h⟩

theorem stock_signed (i : Fin 8) (b : Bool) : Av stock (signed i b) := by
  cases b
  · exact av_mem ⟨i, rfl⟩
  · exact av_not (av_mem ⟨i, rfl⟩)

theorem signed_pair {i : Fin 8} (op a b : Bool) : Av stock (comb op (signed i a) (signed i b)) := by
  cases op <;> cases a <;> cases b
  · convert stock_signed i false using 1
    funext x
    unfold comb signed
    cases x i <;> rfl
  · exact .inl ⟨true, by funext x; unfold comb signed; cases x i <;> rfl⟩
  · exact .inl ⟨true, by funext x; unfold comb signed; cases x i <;> rfl⟩
  · convert stock_signed i true using 1
    funext x
    unfold comb signed
    cases x i <;> rfl
  · convert stock_signed i false using 1
    funext x
    unfold comb signed
    cases x i <;> rfl
  · exact .inl ⟨false, by funext x; unfold comb signed; cases x i <;> rfl⟩
  · exact .inl ⟨false, by funext x; unfold comb signed; cases x i <;> rfl⟩
  · convert stock_signed i true using 1
    funext x
    unfold comb signed
    cases x i <;> rfl

def FirstInput (i : Fin 8) (g : StepGate) (u : F) (b : Bool) : Prop :=
  (g.2.1 = signed i b ∧ g.2.2 = u) ∨ (g.2.2 = signed i b ∧ g.2.1 = u)

theorem expose_input {i : Fin 8} {g : StepGate} (h : Read i g) :
    ∃ u b, FirstInput i g u b := by
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨g.2.2, b, .inl ⟨hb, rfl⟩⟩
  · exact ⟨g.2.1, b, .inr ⟨hb, rfl⟩⟩

theorem first_result {i : Fin 8} {g : StepGate} {u : F} {b : Bool} (h : FirstInput i g u b) :
    resultOf g = comb g.1 (signed i b) u := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [resultOf, ha, hb]
  · funext x
    rw [resultOf, ha, hb]
    simp only [comb, Bool.and_comm, Bool.or_comm]

theorem first_other {i : Fin 8} {g : StepGate} {u : F} {b : Bool}
    (h : FirstInput i g u b) {s : Set F} (ha : Av s g.2.1) (hb : Av s g.2.2) : Av s u := by
  rcases h with ⟨_, e⟩ | ⟨_, e⟩
  · exact e ▸ hb
  · exact e ▸ ha

theorem cut_other {i j : Fin 8} {g : StepGate} {u : F} {b c : Bool}
    (h : FirstInput i g u b) (hu : Cst (rs j c u)) : cutGate j c g := by
  rcases h with ⟨_, e⟩ | ⟨_, e⟩
  · exact .inr (.inl (e.symm ▸ hu))
  · exact .inl (e.symm ▸ hu)

theorem first_case {i : Fin 8} {g : StepGate} {u : F} {b : Bool}
    (h : FirstInput i g u b) :
    Cst (rs i false (resultOf g)) ∨ ∃ (v : F) (s : Bool), (v = u ∨ v = fun x => !u x) ∧
      resultOf g = fun x => if s then !(x i || v x) else x i || v x := by
  rw [first_result h]
  cases e : g.1 <;> cases b
  · exact .inr ⟨u, false, .inl rfl, rfl⟩
  · exact .inl ⟨true, by funext x; simp [rs, comb, signed]⟩
  · exact .inl ⟨false, by funext x; simp [rs, comb, signed]⟩
  · refine .inr ⟨fun x => !u x, true, .inr rfl, ?_⟩
    funext x
    simp [comb, signed]

theorem constant_first_other {i : Fin 8} {g : StepGate} {u v : F} {b c : Bool}
    (h : FirstInput i g u b) (hv : v = u ∨ v = fun x => !u x)
    (hc : Cst (rs 3 c v)) : cutGate 3 c g := by
  apply cut_other h
  rcases hv with rfl | hv
  · exact hc
  · obtain ⟨a, ha⟩ := hc
    refine ⟨!a, ?_⟩
    funext x
    have hh := congrFun ha x
    rw [hv] at hh
    change Bool.not (u (Function.update x 3 c)) = a at hh
    simpa [rs] using congrArg Bool.not hh

theorem bad_product_nonliteral (i : Fin 8) : ¬ Literal i (fun x : X => x 3 && x 7) := by
  have h : ∀ i : Fin 8, ∀ b : Bool, ∃ x : X, (x 3 && x 7) ≠ signed i b x := by
    decide +kernel
  rintro ⟨b, e⟩
  obtain ⟨x, hx⟩ := h i b
  exact hx (congrFun e x)

theorem bad_product_nonconstant : ¬ Cst (fun x : X => x 3 && x 7) := by
  rintro ⟨b, hb⟩
  have h0 := congrFun hb (fun _ => false)
  have h1 := congrFun hb (fun _ => true)
  simp at h0 h1
  cases b <;> simp_all

theorem signed_eq_xor (i : Fin 8) (b : Bool) :
    (fun x : X => xor (x i) b) = signed i b := by
  funext x
  unfold signed
  cases b <;> cases x i <;> rfl

theorem target_not_literal (i : Fin 8) : ¬ Literal i target := by
  rintro ⟨b, h⟩
  exact target_not_initial30304 (h.symm ▸ stock_signed i b)

theorem stable_after_pin {i : Fin 8} {s : Set F} {f : F} {cs : GateTrace}
    (hv : TraceValid s f cs) (hs : ∀ u ∈ s, Smp i false u)
    (hn : ∀ g ∈ cs, ¬ cutGate i false g) : Smp i false f := by
  induction cs generalizing s with
  | nil => exact smp_av hs hv
  | cons g cs ih =>
    obtain ⟨ha, hb, ht⟩ := hv
    have ng := hn g List.mem_cons_self
    have ia := (smp_av hs ha).resolve_right (fun h => ng (.inl h))
    have ib := (smp_av hs hb).resolve_right (fun h => ng (.inr (.inl h)))
    apply ih ht _ (fun d hd => hn d (List.mem_cons_of_mem _ hd))
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact .inl (fun x b => by simp only [comb, ia x b, ib x b])
    · exact hs u hu

theorem cutCount_two_distinct (i : Fin 8) (c : Bool) {a b : StepGate}
    {cs : GateTrace} (ha : a ∈ cs) (hb : b ∈ cs) (hne : a ≠ b)
    (hca : cutGate i c a) (hcb : cutGate i c b) : 2 ≤ cutCount i c cs := by
  induction cs with
  | nil => simp at ha
  | cons d cs ih =>
    rcases List.mem_cons.mp ha with rfl | haTail
    · have hp := cutCount_positive i c ((List.mem_cons.mp hb).resolve_left (Ne.symm hne)) hcb
      rw [cutCount_cons_cut i c _ cs hca]
      omega
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · have hp := cutCount_positive i c haTail hca
        rw [cutCount_cons_cut i c _ cs hcb]
        omega
      · have hi := ih haTail hbTail
        change 2 ≤ cutCount i c ([d] ++ cs)
        rw [cutCount_append]
        omega

theorem noninitial_producer {s : GateTrace} {v : F} (h : Av (traceBank stock s) v)
    (hc : ¬ Cst v) (hl : ∀ i, ¬ Literal i v) :
    ∃ d ∈ s, v = resultOf d ∨ v = fun x => !(resultOf d x) := by
  rcases h with h | ⟨u, hu, e⟩
  · exact False.elim (hc h)
  · rcases mem_traceBank.mp hu with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
    · exact False.elim (e.elim (fun h => hl i ⟨false, h⟩) (fun h => hl i ⟨true, h⟩))
    · exact ⟨d, hd, e⟩

set_option maxHeartbeats 1200000 in
theorem lower30304_structure
    (good_pin_lower30304 : ∀ i, Good30304 i → Low 11 (rs i false target))
    (bad3_lower30304 : Low 10 (rs 3 false target))
    (base : Low 12 target) : Low 13 target := by
  classical
  intro k p
  by_contra! hk
  obtain ⟨cs, hl, hr⟩ := prog_trace p
  have someGood : ∃ d ∈ cs, ∃ i, Good30304 i ∧ Read i d := by
    by_contra hn
    have h0 : Good30304 (0 : Fin 8) := by decide
    obtain ⟨x, _, _, _, hfalse, htrue⟩ := good_influence30304 0 false false h0 rfl
    have hxy := trace_pair_no_read hr (stock_agreement (x := x) (y := Function.update x 0 true)
      (fun _ hj => by rw [Function.update_of_ne hj]))
      (fun d hd => .inr (fun h => hn ⟨d, hd, 0, h0, h⟩)) (target_not_literal 0)
    rw [hfalse, htrue] at hxy
    contradiction
  obtain ⟨pre, g, post, rfl, ⟨i, hi, hread⟩, hnpre⟩ :=
    split_first (fun d => ∃ i, Good30304 i ∧ Read i d) cs someGood
  obtain ⟨hvpre, hv⟩ := trace_valid_split (pre := pre) hr
  obtain ⟨ha, hb, ht⟩ := hv
  have noPre (d) (hd : d ∈ pre) (j) (hj : Good30304 j) : ¬ Read j d :=
    fun hdj => hnpre d hd ⟨j, hj, hdj⟩
  have cap (j) (hj : Good30304 j) : cutCount j false (pre ++ g :: post) ≤ 1 := by
    obtain ⟨m, hm, hq⟩ := restriction_budget j false hr stock (stock_rs j false)
    have hh := good_pin_lower30304 j hj m hq
    omega
  have noPostCuts (j) (hj : Good30304 j) (hgj : Read j g) :
      ∀ d ∈ post, ¬ cutGate j false d := by
    intro d hd hdc
    have hcap := cap j hj
    rw [cutCount_append, cutCount_cons_cut j false _ _ (read_cuts hgj false)] at hcap
    have hp := cutCount_positive j false hd hdc
    omega
  have noPost (j) (hj : Good30304 j) (hgj : Read j g) (d) (hd : d ∈ post) : ¬ Read j d :=
    fun h => noPostCuts j hj hgj d hd (read_cuts h false)
  have removeImpossible (h : Av (traceBank stock pre) (resultOf g)) : False := by
    have hshort := base _ (trace_prog (trace_remove_redundant pre g post hr h))
    simp only [List.length_append, List.length_cons] at hl hshort
    omega
  have initialImpossible (h : Av stock (resultOf g)) : False :=
    removeImpossible (av_subset (fun _ hu => mem_traceBank.mpr (.inl hu)) h)
  obtain ⟨u, b, hAs⟩ := expose_input hread
  have hOut := first_result hAs
  have uAv := first_other hAs ha hb
  have uNotGood (j) (hj : Good30304 j) : ¬ Literal j u := by
    rintro ⟨b', e⟩
    by_cases hij : i = j
    · subst j
      exact initialImpossible (by rw [hOut, e]; exact signed_pair g.1 b b')
    have rj : Read j g := by
      rcases hAs with ⟨_, t⟩ | ⟨_, t⟩
      · exact .inr ⟨b', t.trans e⟩
      · exact .inl ⟨b', t.trans e⟩
    obtain ⟨x, y, hxy, heg, hne⟩ := good_pair_gate_distinguish30304 i j hi hj hij g.1 b b'
    let vary := fun q => q = i ∨ q = j
    have initial : Agreement vary x y stock := stock_agreement fun q hq =>
      hxy q (fun e => hq (.inl e)) (fun e => hq (.inr e))
    have gateSame : resultOf g x = resultOf g y := by
      rw [hOut, e]
      simpa only [signed_eq_xor] using heg
    apply hne (trace_final_agreement hr initial _ (fun j _ => target_not_literal j))
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact .inr (fun q hq => hq.elim (fun e => e.symm ▸ noPre d hd i hi)
        (fun e => e.symm ▸ noPre d hd j hj))
    rcases List.mem_cons.mp hd with rfl | hd
    · exact .inl gateSame
    · exact .inr (fun q hq => hq.elim (fun e => e.symm ▸ noPost i hi hread d hd)
        (fun e => e.symm ▸ noPost j hj rj d hd))
  have agreeingPre {vary : Fin 8 → Prop} {x y : X}
      (hgood : ∀ j, vary j → Good30304 j) (hxy : ∀ j, ¬ vary j → x j = y j) :
      Agreement vary x y (traceBank stock pre) :=
    agreement_trace hvpre (stock_agreement hxy)
      (fun d hd => .inr (fun j hj => noPre d hd j (hgood j hj)))
  have uStable {x y : X} (h3 : x 3 = y 3) (h7 : x 7 = y 7) : u x = u y := by
    apply agreement_av (vary := Good30304) _ uAv uNotGood
    apply agreeingPre (fun _ h => h)
    intro j hj
    by_cases ej : j = 3
    · simpa only [ej] using h3
    have e7 : j = 7 := by by_contra hn; exact hj ⟨ej, hn⟩
    simpa only [e7] using h7
  obtain hAnnihilates | ⟨v, sign, hvu, hor⟩ := first_case hAs
  · have prefixSmp (a) (hma : a ∈ traceBank stock pre) : Smp i false a := by
      by_cases hraw : a = raw i
      · exact .inr (literal_pin ⟨false, hraw⟩ false)
      apply Or.inl
      intro x b
      have hagree := agreeingPre (vary := fun j => j = i)
        (x := Function.update x i b) (y := x)
        (fun _ e => e.symm ▸ hi) (fun _ hn => Function.update_of_ne hn _ _)
      exact (hagree a hma).resolve_right (by rintro ⟨j, rfl, h⟩; exact hraw h)
    have hafter : ∀ a ∈ insert (resultOf g) (traceBank stock pre), Smp i false a := by
      intro a h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · exact .inr hAnnihilates
      · exact prefixSmp a h
    exact good_notSmp30304 i hi (stable_after_pin ht hafter (noPostCuts i hi hread))
  have vStable {x y : X} (h3 : x 3 = y 3) (h7 : x 7 = y 7) : v x = v y := by
    have h := uStable h3 h7
    rcases hvu with rfl | e
    · exact h
    · rw [e]
      exact congrArg Bool.not h
  have vAv : Av (traceBank stock pre) v := by
    rcases hvu with rfl | e
    · exact uAv
    · exact e.symm ▸ av_not uAv
  have vBlocks (x : X) (hx : v x = true) : target x = target (Function.update x i true) := by
    let y := Function.update x i true
    have hxy (j) (h : j ≠ i) : x j = y j := (Function.update_of_ne h _ _).symm
    have hy : v y = true := (vStable (hxy 3 (Ne.symm hi.1)) (hxy 7 (Ne.symm hi.2))).symm.trans hx
    have hgate : resultOf g x = resultOf g y := by
      rw [hor]
      change (if sign then !(x i || v x) else x i || v x) =
        (if sign then !(y i || v y) else y i || v y)
      rw [hx, hy]
      simp
    apply trace_pair_no_read hr
      (stock_agreement (x := x) (y := y) hxy) _ (target_not_literal i)
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact .inr (noPre d hd i hi)
    rcases List.mem_cons.mp hd with rfl | hd
    · exact .inl hgate
    · exact .inr (noPost i hi hread d hd)
  obtain hzero | hproduct := good_operand_rigidity30304 i hi v
    (fun _ _ => vStable) (fun x _ => vBlocks x)
  · exact initialImpossible (by
      rw [hor, hzero]
      convert stock_signed i sign using 1
      funext x
      cases sign <;> simp [signed])
  have hVPin : Cst (rs 3 false v) := by
    rw [hproduct]
    exact ⟨false, by funext x; simp [rs]⟩
  obtain ⟨producer, hp, he⟩ := noninitial_producer vAv
    (hproduct.symm ▸ bad_product_nonconstant) (fun j => hproduct.symm ▸ bad_product_nonliteral j)
  have cp : cutGate 3 false producer := by
    apply Or.inr
    apply Or.inr
    change Cst (rs 3 false (resultOf producer))
    rcases he with e | e
    · rwa [← e]
    · obtain ⟨a, ha⟩ := hVPin
      refine ⟨!a, ?_⟩
      funext x
      have hh := congrFun ha x
      rw [e] at hh
      change Bool.not (resultOf producer (Function.update x 3 false)) = a at hh
      simpa [rs] using congrArg Bool.not hh
  have cg : cutGate 3 false g := constant_first_other hAs hvu hVPin
  have another : ∃ d ∈ pre ++ post, d ≠ producer ∧ Read 3 d := by
    by_contra hn
    obtain ⟨x, h7, _, hfalse, htrue⟩ := bad3_influence30304
    let y := Function.update x 3 true
    have hxy (j) (hj : j ≠ 3) : x j = y j := (Function.update_of_ne hj _ _).symm
    have h7y : y 7 = false := (hxy 7 (by decide)).symm.trans h7
    have vfalse : v x = false := by simp [hproduct, h7]
    have vfalsey : v y = false := by simp [hproduct, h7y]
    have sameP : resultOf producer x = resultOf producer y := by
      have ve : v x = v y := vfalse.trans vfalsey.symm
      rcases he with e | e
      · exact (congrFun e x).symm.trans (ve.trans (congrFun e y))
      · have sameNot := (congrFun e x).symm.trans (ve.trans (congrFun e y))
        simpa using congrArg Bool.not sameNot
    have sameG : resultOf g x = resultOf g y := by
      rw [hor]
      change (if sign then !(x i || v x) else x i || v x) =
        (if sign then !(y i || v y) else y i || v y)
      rw [hxy i hi.1, vfalse, vfalsey]
    have allOther (d) (hd : d ∈ pre ++ post) :
        resultOf d x = resultOf d y ∨ ¬ Read 3 d := by
      by_cases hdp : d = producer
      · exact .inl (hdp.symm ▸ sameP)
      · exact .inr (fun h => hn ⟨d, hd, hdp, h⟩)
    have e := trace_pair_no_read hr (stock_agreement (x := x) (y := y) hxy) (by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact allOther d (List.mem_append_left _ hd)
      rcases List.mem_cons.mp hd with rfl | hd
      · exact .inl sameG
      · exact allOther d (List.mem_append_right _ hd)) (target_not_literal 3)
    exact Bool.noConfusion (hfalse.symm.trans (e.trans htrue))
  obtain ⟨d, hd, hdne, hdr⟩ := another
  have cd := read_cuts hdr false
  have count3 : 3 ≤ cutCount 3 false (pre ++ g :: post) := by
    rw [cutCount_append, cutCount_cons_cut _ _ _ _ cg]
    rcases List.mem_append.mp hd with hd | hd
    · have h2 := cutCount_two_distinct 3 false hd hp hdne cd cp
      omega
    · have h1 := cutCount_positive 3 false hp cp
      have h2 := cutCount_positive 3 false hd cd
      omega
  have hh := restrict_lower_count hr count3 bad3_lower30304
  omega

open PEqualNP.CircuitLowerBounds

private def upperCircuit : Circuit := ⟨[
  ⟨.or, [0, 7]⟩,
  ⟨.and, [3, 8]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.and, [4, 10]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [12, 13]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [0, 15]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [16, 17]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.or, [19, 14]⟩,
  ⟨.or, [20, 18]⟩], 21⟩

private theorem upperSize : upperCircuit.size = 14 := rfl

private theorem upperAllowed : ∀ g ∈ upperCircuit.gates,
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp [upperCircuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
private theorem upperTable : ∀ x : Fin 8 → Bool,
    upperCircuit.eval (List.ofFn x) = decide (∃ i <
      ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] :
        List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] :
        List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

set_option maxRecDepth 12000 in
private theorem target_eq : ∀ x : Fin 8 → Bool, target x = decide (∃ i <
      ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] :
        List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] :
        List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

private theorem graph_lower : Low 13 target := by
  have h1 : Good30304 (1 : Fin 8) := by decide
  have h12 := one 1 false (good_notSmp30304 1 h1) (good_pin_lower30304 1 h1)
  exact lower30304_structure good_pin_lower30304 bad3_lower30304 h12

end PEqualNP.Outside.L_meta_30304

open PEqualNP.Outside.L_meta_30304 in
theorem PEqualNP.Outside.L_meta_30304 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 14 ≤ gates.length
  · refine ⟨upperCircuit.gates, upperCircuit.output, upperAllowed, ?_, upperTable⟩
    change upperCircuit.size ≤ gates.length
    simpa only [upperSize] using hs
  · have hsem := fun x => (he x).trans (target_eq x).symm
    exact ⟨gates, o, all_not_not graph_lower gates o hg (by omega) hsem, le_rfl, he⟩
