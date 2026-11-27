import Mathlib

namespace PEqualNP.Outside.L_lib_582_aux

abbrev K := ZMod 2
abbrev W (V : Type) := V → Bool
noncomputable def ev {V : Type} (s : Finset V) (x : W V) : K := by
  classical
  exact if ∀ v ∈ s, x v = true then 1 else 0

def D {V : Type} (d : ℕ) (f : W V → K) := ∃ t : Finset (Finset V),
  (∀ a ∈ t, a.card ≤ d) ∧ ∀ x, f x = ∑ a ∈ t, ev a x

theorem twoZero (z : K) : z+z=0 := by revert z; decide

theorem normalize {V I : Type} (s : Finset I) (m : I → Finset V) (d : ℕ)
    (bound : ∀ i ∈ s, (m i).card ≤ d) : D d (fun x => ∑ i ∈ s, ev (m i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨t,ht,eq⟩ := ih (fun j hj => bound j (Finset.mem_insert_of_mem hj))
    by_cases h : m i ∈ t
    · refine ⟨t.erase (m i),fun a ha => ht a (Finset.mem_of_mem_erase ha),?_⟩
      intro x
      dsimp only at eq ⊢
      rw [Finset.sum_insert hi,eq x,← Finset.add_sum_erase t (fun a => ev a x) h,
        ← add_assoc,twoZero,zero_add]
    · refine ⟨insert (m i) t,?_,?_⟩
      · intro a ha; rcases Finset.mem_insert.mp ha with h'|h'
        · subst a; exact bound i (Finset.mem_insert_self ..)
        · exact ht a h'
      · intro x; dsimp only at eq ⊢; rw [Finset.sum_insert hi,Finset.sum_insert h,eq x]

theorem dMono {V : Type} {d e : ℕ} {f : W V → K} (h : D d f) (le : d ≤ e) : D e f := by
  obtain ⟨t,ht,eq⟩ := h
  exact ⟨t,fun a ha => (ht a ha).trans le,eq⟩

theorem dZero {V : Type} (d : ℕ) : D d (fun _ : W V => 0) :=
  ⟨∅, by simp,by simp⟩

theorem dOne {V : Type} : D 0 (fun _ : W V => 1) := by
  classical
  exact ⟨{∅},by simp,by intro x; rw [Finset.sum_singleton]; simp [ev]⟩

theorem dVar {V : Type} (v : V) : D 1 (fun x : W V => if x v = true then 1 else 0) := by
  classical
  exact ⟨{{v}},by simp,by intro x; rw [Finset.sum_singleton]; simp [ev]⟩

theorem dAdd {V : Type} {d : ℕ} {f g : W V → K} (hf : D d f) (hg : D d g) :
    D d (fun x => f x + g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  let mon : Finset V ⊕ Finset V → Finset V := Sum.elim id id
  have h := normalize (a.disjSum b) mon d (by
    intro i hi; cases i with
    | inl i => exact ba i (by simpa using hi)
    | inr i => exact bb i (by simpa using hi))
  simpa only [Finset.sum_disjSum,mon,Sum.elim_inl,Sum.elim_inr,id_eq,← ea,← eb] using h

theorem evUnion {V : Type} [DecidableEq V] (a b : Finset V) (x : W V) :
    ev (a ∪ b) x = ev a x * ev b x := by
  classical
  simp only [ev,Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem dMul {V : Type} {d e : ℕ} {f g : W V → K} (hf : D d f) (hg : D e g) :
    D (d+e) (fun x => f x * g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  have h := normalize (a ×ˢ b) (fun p => p.1 ∪ p.2) (d+e) (by
    intro i hi
    exact (Finset.card_union_le ..).trans (Nat.add_le_add
      (ba i.1 (Finset.mem_product.mp hi).1) (bb i.2 (Finset.mem_product.mp hi).2)))
  simpa only [Finset.sum_product,evUnion,← Finset.mul_sum,← Finset.sum_mul,← ea,← eb] using h

theorem dSum {V I : Type} (s : Finset I) (f : I → W V → K) (d : ℕ)
    (h : ∀ i ∈ s, D d (f i)) : D d (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dZero (V:=V) d)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert,hi] using dAdd (h i (Finset.mem_insert_self ..))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem dProd {V I : Type} (s : Finset I) (f : I → W V → K) (d : ℕ)
    (h : ∀ i ∈ s, D d (f i)) : D (s.card*d) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dOne (V:=V))
  | @insert i s hi ih =>
    simpa [Finset.prod_insert,hi,Nat.succ_mul,Nat.add_comm] using
      dMul (h i (Finset.mem_insert_self ..)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem lucasBit (n e : ℕ) : n.choose (2^e) % 2 = (n / 2^e) % 2 := by
  induction e generalizing n with
  | zero => simp
  | succ e ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2) (n:=n) (k:=2*2^e)
    change _ % 2 = _ % 2 at h
    rw [pow_succ,Nat.mul_comm (2^e) 2]
    simp only [Nat.mul_mod_right,Nat.choose_zero_right,one_mul,Nat.mul_div_right _ (by decide : 0<2)] at h
    rw [h,ih,Nat.div_div_eq_div_mul]

def bit (u : Bool) : K := if u then 1 else 0
theorem binj : Function.Injective bit := by decide
theorem parity (k : ℕ) : bit (k % 2 == 1) = (k : K) := by
  rw [← ZMod.natCast_mod k 2]
  have h := k.mod_lt (by decide : 0<2)
  rcases (by omega : k%2=0 ∨ k%2=1) with e|e <;> rw [e] <;> rfl

theorem dLiteral {V : Type} (v : V) (b : Bool) :
    D 1 (fun x : W V => if x v = b then 1 else 0) := by
  cases b with
  | true => exact dVar v
  | false =>
    have h := dAdd (dMono (dOne (V:=V)) (by decide : 0 ≤ 1)) (dVar v)
    convert h using 1
    funext x; cases x v <;> decide

theorem prodInd {I : Type} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (1:K) else 0) = if ∀ i ∈ s, P i then 1 else 0 := by
  classical
  by_cases ok : ∀ i ∈ s, P i
  · rw [ite_eq_left ok]; apply Finset.prod_eq_one; intro i hi; simp [ok i hi]
  · rw [ite_eq_right ok]; push Not at ok; obtain ⟨i,hi,no⟩ := ok
    exact Finset.prod_eq_zero hi (ite_eq_right no)

theorem dChoose {V I : Type} (s : Finset I) (P : I → W V → Prop) [∀ i, DecidablePred (P i)]
    (d k : ℕ) (h : ∀ i ∈ s, D d (fun x => if P i x then 1 else 0)) :
    D (k*d) (fun x => (((s.filter (fun i => P i x)).card.choose k : ℕ) : K)) := by
  classical
  have H := dSum (s.powersetCard k)
    (fun t x => ∏ i ∈ t, if P i x then (1:K) else 0) (k*d) (by
      intro t ht
      obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp ht
      simpa [sz] using dProd t (fun i x => if P i x then (1:K) else 0) d
        (fun i hi => h i (sub hi)))
  convert H using 1
  funext x
  simp_rw [prodInd,Finset.sum_boole]
  have sets : ((s.powersetCard k).filter (fun t => ∀ i ∈ t, P i x)) =
      (s.filter (fun i => P i x)).powersetCard k := by
    ext t; simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_iff]
    constructor
    · rintro ⟨⟨sub,sz⟩,ok⟩; exact ⟨fun i hi => ⟨sub hi,ok i hi⟩,sz⟩
    · rintro ⟨sub,sz⟩; exact ⟨⟨fun i hi => (sub hi).1,sz⟩,fun i hi => (sub hi).2⟩
  rw [sets,Finset.card_powersetCard]

abbrev Words (m r : ℕ) := W (Fin m × Fin r)
def matchesPrefix {m r} (x : Words m r) (l path : ℕ) (i : Fin m) :=
  ∀ j : Fin r, j.val<l → x (i,j) = path.testBit j.val
noncomputable def active {m r} (x : Words m r) (l path : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (matchesPrefix x l path)
def zeroRow {m r} (l path : ℕ) (hl : l<r) (i : Fin m) (x : Words m r) :=
  matchesPrefix x l path i ∧ x (i,⟨l,hl⟩)=false

theorem dRow {m r} (l path : ℕ) (hl : l<r) (i : Fin m) :
    D (l+1) (fun x : Words m r => @ite K (zeroRow l path hl i x) (Classical.propDecidable _) 1 0) := by
  classical
  let s := Finset.univ.filter (fun j : Fin r => j.val ≤ l)
  let b := fun j : Fin r => if j.val<l then path.testBit j.val else false
  have eq (x : Words m r) : (∀ j ∈ s, x (i,j)=b j) ↔ zeroRow l path hl i x := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,zeroRow,matchesPrefix]
    constructor
    · intro h; exact ⟨fun j hj => by simpa [b,hj] using h j hj.le,
        by simpa [b] using h ⟨l,hl⟩ (le_refl l)⟩
    · rintro ⟨h,atL⟩ j hj
      rcases lt_or_eq_of_le hj with less|e
      · simpa [b,less] using h j less
      · have ej : j=⟨l,hl⟩ := Fin.ext e
        subst j; simpa [b] using atL
  have sz : s.card ≤ l+1 := by
    calc
      s.card ≤ (Finset.range (l+1)).card := Finset.card_le_card_of_injOn Fin.val
        (fun j hj => Finset.mem_range.mpr (by have h := (Finset.mem_filter.mp hj).2;omega))
        (fun _ _ _ _ h => Fin.ext h)
      _ = _ := Finset.card_range _
  have h := dProd s (fun (j : Fin r) (x : Words m r) => if x (i,j)=b j then (1:K) else 0)
      1 (fun j _ => dLiteral (i,j) (b j))
  simpa only [mul_one,prodInd,eq] using dMono h (by simpa using sz : s.card*1 ≤ l+1)

noncomputable def zeros {m r} (x : Words m r) (l path : ℕ) (hl : l<r) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => zeroRow l path hl i x)
noncomputable def question {m r} (l path : ℕ) (x : Words m r) : Bool :=
  if hl : l<r then (zeros x l path hl).card.choose (2^(r-1-l)) % 2 == 1 else false

theorem dQuestion {m r} (u : Fin r) (path : ℕ) :
    D ((u.val+1)*2^(r-1-u.val)) (fun x : Words m r => bit (question u.val path x)) := by
  classical
  have h := dChoose Finset.univ (zeroRow (m:=m) u.val path u.isLt) (u.val+1) (2^(r-1-u.val))
    (fun i _ => dRow _ _ _ i)
  simpa only [question,dite_eq_left u.isLt,parity,zeros,Nat.mul_comm] using h

def extend (path l : ℕ) (b : Bool) := path + (b.toNat <<< l)
theorem extendEq (path l : ℕ) (b : Bool) : extend path l b = 2^l*b.toNat+path := by
  simp [extend,Nat.shiftLeft_eq,Nat.add_comm,Nat.mul_comm]

theorem bitNext (path l : ℕ) (b : Bool) (hp : path<2^l) :
    (extend path l b).testBit l = b := by
  rw [extendEq,Nat.testBit_two_pow_mul_add _ hp]
  cases b <;> simp

theorem prefixNext {m r} (x : Words m r) (l path : ℕ) (b : Bool) (hl : l<r)
    (hp : path<2^l) (i : Fin m) :
    matchesPrefix x (l+1) (extend path l b) i ↔ matchesPrefix x l path i ∧ x (i,⟨l,hl⟩)=b := by
  have low (j : Fin r) (hj : j.val<l) : (extend path l b).testBit j.val = path.testBit j.val := by
    rw [extendEq,Nat.testBit_two_pow_mul_add _ hp,ite_eq_left hj]
  constructor
  · intro h; exact ⟨fun j hj => (h j (by omega)).trans (low j hj),
      (h ⟨l,hl⟩ (by simp)).trans (bitNext _ _ _ hp)⟩
  · rintro ⟨h,atL⟩ j hj
    by_cases hlt : j.val<l
    · exact (h j hlt).trans (low j hlt).symm
    · have ej : j=⟨l,hl⟩ := Fin.ext (by change j.val=l; omega)
      subst j; exact atL.trans (bitNext _ _ _ hp).symm

theorem advanceCount {m r} (x : Words m r) (l path : ℕ) (hl : l<r)
    (hp : path<2^l) (ha : (active x l path).card<2^(r-l)) :
    (active x (l+1) (extend path l (question l path x))).card < 2^(r-(l+1)) := by
  classical
  let A := active x l path
  let Z := zeros x l path hl
  let B := A.filter (fun i => x (i,⟨l,hl⟩)=true)
  let e := r-1-l
  have old : r-l=e+1 := by dsimp [e]; omega
  have newE : r-(l+1)=e := by dsimp [e];omega
  rw [newE]
  have shape (b : Bool) : active x (l+1) (extend path l b) =
      A.filter (fun i => x (i,⟨l,hl⟩)=b) := by
    ext i
    simp only [A,active,Finset.mem_filter,Finset.mem_univ,true_and,prefixNext x l path b hl hp]
  have hZ : Z = A.filter (fun i => x (i,⟨l,hl⟩)=false) := by
    ext i
    have zmem : i ∈ Z ↔ i ∈ (Finset.univ : Finset (Fin m)) ∧ zeroRow l path hl i x :=
      @Finset.mem_filter _ (fun a => zeroRow l path hl a x) (fun _ => Classical.propDecidable _) Finset.univ i
    rw [zmem]
    simp only [A,active,Finset.mem_filter,Finset.mem_univ,true_and,zeroRow]
  have sum : Z.card+B.card=A.card := by
    rw [hZ]
    simpa [B,Bool.not_eq_false] using Finset.card_filter_add_card_filter_not
      (s:=A) (fun i => x (i,⟨l,hl⟩)=false)
  change A.card < _ at ha
  rw [old,pow_succ] at ha
  have q : question l path x = (Z.card / 2^e % 2 == 1) := by
    simp only [question,dite_eq_left hl,lucasBit,Z,e]
  have pos : 0<2^e := Nat.two_pow_pos _
  by_cases small : Z.card<2^e
  · rw [q,Nat.div_eq_of_lt small]
    change (active x (l+1) (extend path l false)).card < _
    rwa [shape,← hZ]
  · have hd : Z.card/2^e=1 := by
      have hup : Z.card/2^e < 2 := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
      have hlo : 1 ≤ Z.card/2^e := (Nat.le_div_iff_mul_le pos).mpr (by omega)
      omega
    rw [q,hd]
    change (active x (l+1) (extend path l true)).card < _
    rw [shape]; change B.card < _; omega

noncomputable def trace {m r} (x : Words m r) (l : ℕ) :=
  (List.range l).foldl (fun path k => extend path k (question k path x)) 0

theorem traceBounds {m r} (hm : m < 2^r) (x : Words m r) (l : ℕ) (hl : l ≤ r) :
    trace x l < 2^l ∧ (active x l (trace x l)).card < 2^(r-l) := by
  induction l with
  | zero =>
    have emptyMatch : active x 0 (trace x 0) = Finset.univ := by
      ext i
      simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,iff_true,matchesPrefix]
      intro j h; omega
    rw [emptyMatch]; simpa [trace] using hm
  | succ l ih =>
    have hlt : l<r := by omega
    obtain ⟨hp,ha⟩ := ih hlt.le
    have step : trace x (l+1) = extend (trace x l) l (question l (trace x l) x) := by
      simp [trace,List.range_succ,List.foldl_append]
    rw [step]
    refine ⟨?_,advanceCount x l (trace x l) hlt hp ha⟩
    rw [extendEq,pow_succ]
    cases question l (trace x l) x <;> simp <;> omega

end PEqualNP.Outside.L_lib_582_aux

open PEqualNP.Outside.L_lib_582_aux in
theorem PEqualNP.Outside.L_lib_582 : ∀ (m r : Nat), m < 2^r →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range steps).foldl (fun past pos => past + ((ask pos past x).toNat <<< pos)) 0
  ∃ ask : Nat → Nat → W → Bool,
    (∀ (u : Fin r) (path : Nat), deg ((u.val+1)*2^(r-1-u.val)) (ask u.val path)) ∧
    ∀ (input : W) (l : Nat), l ≤ r →
      let trace := run l ask input
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∀ j : Fin r, j.val < l → input (i,j) = trace.testBit j.val)).card < 2^(r-l) := by
  classical
  intro m r hm V W par deg run
  refine ⟨question,?_,?_⟩
  · intro u path
    obtain ⟨t,ht,eq⟩ := dQuestion (m:=m) u path
    refine ⟨t,ht,?_⟩
    intro x
    apply binj
    dsimp only at eq
    rw [eq x]
    change (∑ a ∈ t, ev a x) = bit ((_ % 2) == 1)
    rw [parity]
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro a ha; unfold ev; split_ifs <;> rfl
  · intro x l hl
    have ok := (traceBounds hm x l hl).2
    let actual := run l (@question m r) x
    have pathEq : actual = trace x l := rfl
    change (Finset.univ.filter (fun i => ∀ j : Fin r, j.val<l → x (i,j)=actual.testBit j.val)).card < _
    rw [pathEq]
    convert ok using 2
    ext i; simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,matchesPrefix]
