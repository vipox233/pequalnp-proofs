import PEqualNP.Defs
namespace PEqualNP.Outside.L_clb_053_aux
open BranchingProgram
abbrev Bits (m : Nat) := Fin m → Bool
abbrev Fn (m : Nat) := Bits m → Bool
abbrev Pool (m : Nat) := Finset (Fn m)
def input {m : Nat} (S : Finset (Fin m)) (a x : Bits m) :=
  List.ofFn (fun j => if j ∈ S then x j else a j)
def mix {m : Nat} (v : Fin m) (p : Fn m × Fn m) : Fn m :=
  fun x => if x v then p.2 x else p.1 x
def tCount {m : Nat} (S : Finset (Fin m)) (L : Program) :=
  (L.filter (fun st => st.var ∈ S.image Fin.val)).length

def Valid {m : Nat} (P : Program) (S : Finset (Fin m)) (a : Bits m) (offset : Nat) (G : Pool m) : Prop :=
  (∀ b : Bool, (fun _ => b) ∈ G) ∧
  ∀ i : Nat, offset ≤ i → i < P.length → ∃ g ∈ G,
    ∀ x fuel, P.length-i≤fuel → P.run (input S a x) fuel i=g x

lemma stepValid {m : Nat} {P : Program} {S : Finset (Fin m)} {a : Bits m}
    {q : Nat} {s : State} {G : Pool m} (fr : P.Forward) (reads : P.ReadsBelow m)
    (hs : P[q]?=some s) (hG : Valid P S a (q+1) G) :
    let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
    ∃ p ∈ G ×ˢ G,
      if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G := by
  classical
  dsimp only
  let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
  have readBit (x : Bits m) : (input S a x).getD s.var false = if v∈S then x v else a v := by
    simp [input,List.getD_eq_getElem?_getD,v,reads s (List.mem_of_getElem? hs)]
  let go (n : Next) (x : Bits m) (fuel : Nat) :=
    match n with
    | .out b => b
    | .state i => P.run (input S a x) fuel i
  have get (n : Next) (chosen : s.lo=n ∨ s.hi=n) :
      ∃ g ∈ G, ∀ x fuel, P.length-q≤fuel+1 → go n x fuel=g x := by
    cases n with
    | out b => exact ⟨_,hG.1 b,by intros;rfl⟩
    | state i =>
      have h := fr q s hs i chosen
      obtain ⟨g,mg,eq⟩:=hG.2 i (by omega) h.2
      exact ⟨g,mg,fun x fuel hf=>eq x fuel (by omega)⟩
  obtain ⟨lo,ml,el⟩:=get s.lo (Or.inl rfl)
  obtain ⟨hi,mh,eh⟩:=get s.hi (Or.inr rfl)
  refine ⟨(lo,hi),Finset.mem_product.mpr ⟨ml,mh⟩,?_⟩
  have current (x : Bits m) (f : Nat) (hf:P.length-q≤f) :
      P.run (input S a x) f q=(if (if v∈S then x v else a v) then hi x else lo x) := by
    have qlt : q<P.length := (List.getElem?_eq_some_iff.mp hs).1
    cases f with
    | zero => omega
    | succ f =>
      simp only [Program.run,hs,readBit x]
      by_cases e : (if v∈S then x v else a v)=true
      · cases ee : s.hi <;> simpa [go,e,ee] using eh x f hf
      · cases ee : s.lo <;> simpa [go,e,ee] using el x f hf
  by_cases inside : v∈S
  · rw [ite_eq_left inside]
    refine ⟨fun b=>Finset.mem_insert_of_mem (hG.1 b),?_⟩
    intro i qi ip
    by_cases e:i=q
    · subst i
      exact ⟨_,Finset.mem_insert_self ..,fun x f hf=>by simpa [inside,mix] using current x f hf⟩
    · obtain ⟨g,mg,h⟩:=hG.2 i (by omega) ip
      exact ⟨g,Finset.mem_insert_of_mem mg,h⟩
  · rw [ite_eq_right inside]
    refine ⟨hG.1,?_⟩
    intro i qi ip
    by_cases e:i=q
    · subst i
      by_cases av:a v=true
      · exact ⟨hi,mh,fun x f hf=>by simpa [inside,av] using current x f hf⟩
      · exact ⟨lo,ml,fun x f hf=>by simpa [inside,av] using current x f hf⟩
    · exact hG.2 i (by omega) ip

lemma bounds {m : Nat} (P : Program) (S : Finset (Fin m)) (fr : P.Forward) (reads : P.ReadsBelow m)
    (T : Program) (q : Nat) (suffix : P.drop q=T) (leq : q≤P.length) :
    ∃ F : Finset (Pool m), F.card≤(Nat.factorial (tCount S T+1))^2 ∧
      (∀ G∈F,G.card≤tCount S T+2) ∧ ∀ a, ∃ G∈F, Valid P S a q G := by
  classical
  induction T generalizing q with
  | nil =>
    let G : Pool m := {fun _=>false,fun _=>true}
    refine ⟨{G},by simp [tCount],?_,?_⟩
    · intro z hz
      obtain rfl:=Finset.mem_singleton.mp hz
      exact (Finset.card_insert_le ..).trans (by simp [tCount])
    · intro a
      have eq:=congrArg List.length suffix
      simp at eq
      exact ⟨G,by simp,fun b=>by cases b <;> simp [G],fun i qi ip=>by omega⟩
  | cons s T ih =>
    have drop : P.drop (q+1)=T := by rw [←List.drop_drop (i:=1) (j:=q),suffix];rfl
    have qlt : q<P.length := by have e:=congrArg List.length suffix;simp at e;omega
    have hs : P[q]?=some s := by
      have e : (P.drop q)[0]?=some s := by rw [suffix];rfl
      simpa only [List.getElem?_drop,Nat.add_zero] using e
    obtain ⟨F,hF,hsize,keep⟩:=ih (q+1) drop (by omega)
    let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
    have mem : s.var∈S.image Fin.val ↔ v∈S := by
      constructor
      · rintro h
        obtain ⟨i,mi,e⟩:=Finset.mem_image.mp h
        exact (show i=v from Fin.ext e) ▸ mi
      · intro h
        exact Finset.mem_image.mpr ⟨v,h,rfl⟩
    by_cases hv:v∈S
    · have ct : tCount S (s::T)=tCount S T+1 := by
        unfold tCount
        rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using mem.mpr hv)];rfl
      let ex (G : Pool m) := (G ×ˢ G).image (fun p => insert (mix v p) G)
      refine ⟨F.biUnion ex,?_,?_,?_⟩
      · calc
          (F.biUnion ex).card ≤ ∑ G ∈ F, (ex G).card := Finset.card_biUnion_le
          _ ≤ ∑ _G ∈ F, (tCount S T+2)^2 := by
            apply Finset.sum_le_sum
            intro G mg
            exact (Finset.card_image_le).trans (by rw [Finset.card_product,pow_two];exact Nat.mul_le_mul (hsize G mg) (hsize G mg))
          _ = F.card * (tCount S T+2)^2 := by simp
          _ ≤ (Nat.factorial (tCount S (s::T)+1))^2 := by
            rw [ct,Nat.factorial_succ,mul_pow,Nat.mul_comm]
            exact Nat.mul_le_mul_left _ hF
      · intro H mh
        obtain ⟨G,mg,aa⟩:=Finset.mem_biUnion.mp mh
        obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp aa
        have h:=hsize G mg
        have e:=Finset.card_insert_le (mix v p) G
        rw [ct];omega
      · intro a
        obtain ⟨G,mg,hG⟩:=keep a
        obtain ⟨p,mp,ok⟩:=stepValid fr reads hs hG
        change (if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G) at ok
        exact ⟨_,Finset.mem_biUnion.mpr ⟨G,mg,Finset.mem_image.mpr ⟨p,mp,rfl⟩⟩,by simpa [hv] using ok⟩
    · have nh : s.var∉S.image Fin.val := fun e=>hv (mem.mp e)
      have ct : tCount S (s::T)=tCount S T := by
        unfold tCount
        rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using nh)]
      rw [ct]
      refine ⟨F,hF,hsize,?_⟩
      intro a
      obtain ⟨G,mg,hG⟩:=keep a
      obtain ⟨p,mp,ok⟩:=stepValid fr reads hs hG
      change (if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G) at ok
      exact ⟨G,mg,by simpa [hv] using ok⟩

end PEqualNP.Outside.L_clb_053_aux

open PEqualNP.Outside.L_clb_053_aux in
theorem PEqualNP.Outside.L_clb_053 :
∀ (m : ℕ) (S : Finset (Fin m)) (P : PEqualNP.BranchingProgram.Program),
  P.Forward → P.ReadsBelow m →
  let t := (P.filter (fun st => st.var ∈ S.image Fin.val)).length
  let res := fun (a x : Fin m → Bool) =>
    P.eval (List.ofFn (fun j => if j ∈ S then x j else a j))
  (Finset.univ.image res).card ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2 := by
  classical
  intro m S P fr reads t res
  obtain ⟨F,cf,cg,keep⟩:=bounds P S fr reads P 0 (by simp) (by omega)
  have cover : Finset.univ.image res ⊆ F.biUnion id := by
    intro g mg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp mg
    obtain ⟨G,mg,hG⟩:=keep a
    refine Finset.mem_biUnion.mpr ⟨G,mg,?_⟩
    by_cases h:0<P.length
    · obtain ⟨g,mem,eq⟩:=hG.2 0 (by omega) h
      have e : res a=g := funext (fun x=>eq x P.length (by omega))
      change res a ∈ G
      rw [e]
      exact mem
    · have emp : P=[] := List.length_eq_zero_iff.mp (by omega)
      subst P
      exact hG.1 false
  calc
    _ ≤ (F.biUnion id).card := Finset.card_le_card cover
    _ ≤ ∑ G ∈ F,G.card := Finset.card_biUnion_le
    _ ≤ ∑ _G ∈ F,(t+2) := Finset.sum_le_sum cg
    _ = (t+2)*F.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ cf

