import PEqualNP.Defs

/-! Original proof. The desk sketch also notes the disjoint-edge highest-degree strategy. -/


namespace PEqualNP.Outside.L_meta_32058_aux
abbrev H := List Bool

def cut (b : Bool) : List H → List H
  | [] => []
  | []::ns => cut b ns
  | (a::p)::ns => if a=b then p::cut b ns else cut b ns

theorem mem_cut (b : Bool) (p : H) (ns : List H) :
    p ∈ cut b ns ↔ (b::p) ∈ ns := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil => simp [cut,ih]
    | cons a h =>
      by_cases eq : a=b
      · subst a; simp [cut,ih]
      · have ne : b ≠ a := Ne.symm eq
        simp [cut,eq,ne,ih]

theorem cut_budget (ns : List H) :
    (cut false ns).length+(cut true ns).length+(if [] ∈ ns then 1 else 0) ≤ ns.length := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil =>
      simp only [cut,List.mem_cons,true_or,ite_true,List.length_cons]
      have h := Nat.le_add_right ((cut false ns).length+(cut true ns).length)
        (if [] ∈ ns then 1 else 0)
      omega
    | cons a h =>
      cases a <;> simp [cut] at ih ⊢ <;> omega

def leaves (ns : List H) : Nat → List H
  | 0 => [[]]
  | d+1 => if [] ∈ ns then
      (leaves (cut false ns) d).map (false::·) ++
      (leaves (cut true ns) d).map (true::·)
    else [[]]

theorem leaf_budget (d : Nat) (ns : List H) : (leaves ns d).length ≤ ns.length+1 := by
  induction d generalizing ns with
  | zero => simp [leaves]
  | succ d ih =>
    by_cases h : [] ∈ ns
    · have l := ih (cut false ns)
      have r := ih (cut true ns)
      have b := cut_budget ns
      simp only [h,ite_true] at b
      simp only [leaves,h,ite_true,List.length_append,List.length_map]
      omega
    · simp [leaves,h]

def advance (ns : List H) (answer : H → Bool) (p : H) : H :=
  if p ∈ ns then p++[answer p] else p

def follow (ns : List H) (answer : H → Bool) : Nat → H → H
  | 0,p => p
  | d+1,p => follow ns answer d (advance ns answer p)

theorem no_node (ns : List H) (Q : H → Bool) (d : Nat) (p : H)
    (h : p ∉ ns) : follow ns Q d p=p := by
  induction d with
  | zero => rfl
  | succ d ih => simp [follow,advance,h,ih]

theorem advance_shift (ns : List H) (Q : H → Bool) (b : Bool) (p : H) :
    advance ns Q (b::p) = b::advance (cut b ns) (fun q=>Q (b::q)) p := by
  unfold advance
  simp only [mem_cut]
  split <;> rfl

theorem follow_shift (ns : List H) (Q : H → Bool) (b : Bool) (d : Nat) (p : H) :
    follow ns Q d (b::p) = b::follow (cut b ns) (fun q=>Q (b::q)) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [follow,advance_shift]
    exact ih _

theorem mem_leaves (d : Nat) (ns : List H) (Q : H → Bool) :
    follow ns Q d [] ∈ leaves ns d := by
  induction d generalizing ns Q with
  | zero => simp [follow,leaves]
  | succ d ih =>
    by_cases h : [] ∈ ns
    · simp only [follow,advance,leaves,h,ite_true,List.nil_append,follow_shift]
      cases a : Q [] with
      | false =>
        apply List.mem_append_left
        apply List.mem_map_of_mem
        exact ih _ _
      | true =>
        apply List.mem_append_right
        apply List.mem_map_of_mem
        exact ih _ _
    · simp [no_node _ _ _ _ h,leaves,h]

theorem fold_follow {α : Type} (ns : List H) (Q : H → Bool) (xs : List α) (p : H) :
    xs.foldl (fun q _ => advance ns Q q) p = follow ns Q xs.length p := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,List.length_cons,follow,ih]

theorem exact_leaf_list (ns : List H) (N : Nat) :
    ∃ ls : List H, ls.length ≤ ns.length+1 ∧ 
      ∀ Q : H → Bool, (List.range N).foldl (fun p _ =>
        if p ∈ ns then p++[Q p] else p) [] ∈ ls := by
  refine ⟨leaves ns N,leaf_budget _ _,?_⟩
  intro Q
  change (List.range N).foldl (fun p _ => advance ns Q p) [] ∈ _
  rw [fold_follow,List.length_range]
  apply mem_leaves

theorem prefix_follow (ns : List H) (Q : H → Bool) (d : Nat) (p : H) :
    ∃ r : H, follow ns Q d p = p++r := by
  induction d generalizing p with
  | zero => exact ⟨[],by simp [follow]⟩
  | succ d ih =>
    obtain ⟨r,hr⟩ := ih (advance ns Q p)
    by_cases h : p ∈ ns
    · refine ⟨Q p::r,?_⟩
      simpa only [follow,advance,h,ite_true,List.append_assoc,List.cons_append,List.nil_append] using hr
    · refine ⟨r,?_⟩
      simpa only [follow,advance,h,ite_false] using hr

theorem reachable_leaf_cell (ns : List H) (Q : H → Bool) (d : Nat) (p : H) :
    ∃ checks : List (H × Bool), ∀ R : H → Bool,
      follow ns R d p = follow ns Q d p ↔ ∀ z ∈ checks, R z.1=z.2 := by
  induction d generalizing p with
  | zero => exact ⟨[],fun _ => by simp [follow]⟩
  | succ d ih =>
    by_cases h : p ∈ ns
    · obtain ⟨checks,hc⟩ := ih (p++[Q p])
      refine ⟨(p,Q p)::checks,fun R => ?_⟩
      simp only [follow,advance,h,ite_true]
      constructor
      · intro same
        obtain ⟨s,hs⟩ := prefix_follow ns R d (p++[R p])
        obtain ⟨t,ht⟩ := prefix_follow ns Q d (p++[Q p])
        have hb : R p=Q p := by
          rw [hs,ht] at same
          have e := List.append_inj_left same (by simp)
          exact List.cons.inj (List.append_cancel_left e) |>.1
        intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact hb
        · apply ((hc R).mp ?_) z hz
          simpa only [hb] using same
      · intro agree
        have same₁ := agree (p,Q p) List.mem_cons_self
        change R p=Q p at same₁
        rw [same₁]
        exact (hc R).mpr (fun z hz => agree z (List.mem_cons_of_mem _ hz))
    · exact ⟨[],fun R => by simp [no_node _ R _ _ h,no_node _ Q _ _ h]⟩

end PEqualNP.Outside.L_meta_32058_aux


namespace PEqualNP.Outside.L_meta_32058_aux.Path

/-- Greedy alternating witnesses for any subset of edges of a path.
    Edge i joins vertex i to vertex i+1. Choose the right endpoint of every
    witness for a minimum cover. -/
def choose (mark : Nat → Bool) : Nat → Nat → List Nat
  | 0, _ => []
  | 1, a => if mark a then [a] else []
  | n+2, a => if mark a then a::choose mark n (a+2)
              else choose mark (n+1) (a+1)

def Covers (xs : List Nat) (i : Nat) : Prop :=
  i ∈ xs ∨ ∃ j ∈ xs, i=j+1

theorem good (f : Nat → Bool) (n a : Nat) :
    (∀ i ∈ choose f n a, a ≤ i ∧ i < a+n ∧ f i=true) ∧ 
    (choose f n a).Pairwise (fun i j => i+2 ≤ j) ∧ 
    (∀ i, a ≤ i → i < a+n → f i=true → Covers (choose f n a) i) := by
  induction n using Nat.strongRecOn generalizing a with
  | ind m strong =>
   rcases m with _ | _ | n
   · simp [choose]
     omega
   · cases h : f a
     · simp [choose,h]
       intro i hi hj hf
       have e : i=a := by omega
       simp [e,h] at hf
     · simp [choose,h]
       intro i hi hj hf
       have e : i=a := by omega
       subst i
       exact .inl (by simp)
   · cases h : f a
     · rw [choose,ite_eq_right (by simp [h])]
       obtain ⟨range,pair,cover⟩ := strong (n+1) (by omega) (a+1)
       refine ⟨?_,pair,?_⟩
       · intro i hi
         obtain ⟨l,r,m⟩ := range i hi
         exact ⟨by omega,by omega,m⟩
       · intro i hi hj hf
         have ne : i ≠ a := by intro e;subst i; simp [h] at hf
         exact cover i (by omega) (by omega) hf
     · rw [choose,ite_eq_left (by simp [h])]
       obtain ⟨range,pair,cover⟩ := strong n (by omega) (a+2)
       refine ⟨?_,List.pairwise_cons.mpr ⟨fun i hi => (range i hi).1,pair⟩,?_⟩
       · intro i hi
         rcases List.mem_cons.mp hi with rfl|hi
         · exact ⟨by omega,by omega,h⟩
         · obtain ⟨l,r,m⟩ := range i hi
           exact ⟨by omega,by omega,m⟩
       · intro i hi hj hf
         by_cases eq : i=a
         · exact .inl (eq ▸ List.mem_cons_self)
         by_cases nx : i=a+1
         · exact .inr ⟨a,List.mem_cons_self,nx⟩
         rcases cover i (by omega) (by omega) hf with m|⟨j,m,jx⟩
         · exact .inl (List.mem_cons_of_mem _ m)
         · exact .inr ⟨j,List.mem_cons_of_mem _ m,jx⟩

def bad (keep : Nat → Bool) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,a => (if keep a then 0 else 1) + bad keep n (a+1)

def pair (keep : Nat → Bool) (i : Nat) : Bool := keep i && keep (i+1)

/-- If a path is cut at a removed terminal vertex, every uncovered free
    vertex can be charged to one removed vertex immediately after it. -/
theorem terminal_bound (keep : Nat → Bool) (n a : Nat)
    (endDel : keep (a+n)=false) :
    n+1 ≤ 2*(choose (pair keep) n a).length + 2*bad keep (n+1) a := by
  induction n using Nat.strongRecOn generalizing a with
  | ind m strong =>
   rcases m with _ | _ | n
   · have h : keep a=false := by simpa using endDel
     simp [choose,bad,h]
   · have h : pair keep a=false := by simp [pair,endDel]
     simp only [choose,h,Bool.false_eq_true,ite_false,List.length_nil,Nat.mul_zero,Nat.zero_add]
     cases ha : keep a <;> simp [bad,ha,endDel]
   · cases h0 : keep a
     · have hp : pair keep a=false := by simp [pair,h0]
       have ih := strong (n+1) (by omega) (a+1) (by rw [show a+1+(n+1)=a+(n+1+1) by omega];exact endDel)
       simp only [choose,hp,Bool.false_eq_true,ite_false]
       have b : bad keep (n+1+1+1) a = 1+bad keep (n+1+1) (a+1) := by
         rw [bad]; simp only [h0,Bool.false_eq_true,ite_false]
       rw [b]
       omega
     · cases h1 : keep (a+1)
       · have hp : pair keep a=false := by simp [pair,h0,h1]
         have hp' : pair keep (a+1)=false := by simp [pair,h1]
         have ih := strong n (by omega) (a+2) (by rw [show a+2+n=a+(n+1+1) by omega];exact endDel)
         rw [choose,ite_eq_right (by simp [hp])]
         have e : choose (pair keep) (n+1) (a+1) = choose (pair keep) n (a+2) := by
           cases n with
           | zero => simp [choose,hp']
           | succ n =>
             rw [choose,ite_eq_right (by simp [hp'])]
         rw [e]
         change n+3 ≤ 2*(choose (pair keep) n (a+2)).length + 2*bad keep ((n+1)+1+1) a
         have b : bad keep (n+1+1+1) a = 1+bad keep (n+1) (a+2) := by
           rw [bad,bad]; simp only [h0,h1,ite_true,Bool.false_eq_true,ite_false,Nat.zero_add]
         rw [b]
         omega
       · have hp : pair keep a=true := by simp [pair,h0,h1]
         have ih := strong n (by omega) (a+2) (by rw [show a+2+n=a+(n+1+1) by omega];exact endDel)
         rw [choose,ite_eq_left (by simp [hp]),List.length_cons]
         change n+3 ≤ 2*((choose (pair keep) n (a+2)).length+1) + 2*bad keep ((n+1)+1+1) a
         have b : bad keep (n+1+1+1) a = bad keep (n+1) (a+2) := by
           rw [bad,bad]; simp only [h0,h1,ite_true,Nat.zero_add]
         rw [b]
         omega

theorem odd_terminal_match (keep : Nat → Bool) (n a : Nat)
    (odd : (n+1) % 2=1) (endDel : keep (a+n)=false) :
    (n+1)/2 + 1 ≤ (choose (pair keep) n a).length + bad keep (n+1) a := by
  have b := terminal_bound keep n a endDel
  omega

theorem all_length (n a : Nat) :
    (choose (fun _=>true) n a).length=(n+1)/2 := by
  induction n using Nat.strongRecOn generalizing a with
  | ind m ih =>
    rcases m with _|_|n
    · rfl
    · rfl
    · simp only [choose,ite_true,List.length_cons,ih n (by omega) (a+2)]
      omega

theorem all_mem (n a i : Nat) :
    i ∈ choose (fun _=>true) n a ↔ a ≤ i ∧ i < a+n ∧ (i-a) % 2=0 := by
  induction n using Nat.strongRecOn generalizing a with
  | ind m ih =>
    rcases m with _|_|n
    · simp [choose];omega
    · simp [choose];omega
    · simp only [choose,ite_true,List.mem_cons,ih n (by omega) (a+2)]
      omega

theorem bad_succ_right (f : Nat → Bool) (n a : Nat) :
    bad f (n+1) a=bad f n a+(if f (a+n) then 0 else 1) := by
  induction n generalizing a with
  | zero => simp [bad]
  | succ n ih =>
    have e : a+1+n=a+(n+1) := by omega
    let c (i : Nat) : Nat := if f i then 0 else 1
    change c a+bad f (n+1) (a+1)=(c a+bad f n (a+1))+c (a+(n+1))
    rw [ih,e,Nat.add_assoc]

end PEqualNP.Outside.L_meta_32058_aux.Path


namespace PEqualNP.Outside.L_meta_32058_aux.Degree

abbrev Point := Nat → Bool
abbrev Mon := List Nat
abbrev Poly := List Mon

def varSet (x : Point) (i : Nat) (b : Bool) : Point :=
  fun j => if j=i then b else x j

def mon (xs : Mon) (x : Point) : Bool :=
  xs.foldr (fun i z => x i && z) true

def eval (p : Poly) (x : Point) : Bool :=
  p.foldr (fun m z => xor (mon m x) z) false

def parity (vs : List Nat) (f : Point → Bool) : Bool :=
  match vs with
  | [] => f (fun _=>false)
  | i::is => xor (parity is (fun x=>f (varSet x i false))) (parity is (fun x=>f (varSet x i true)))

private theorem xor4 (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem and_xor (a b c : Bool) :
    (a && xor b c)=xor (a&&b) (a&&c) := by cases a <;> cases b <;> cases c <;> rfl

private theorem xor_and (a b c : Bool) :
    (xor a b && c)=xor (a&&c) (b&&c) := by cases a <;> cases b <;> cases c <;> rfl

private theorem xor_assoc (a b c : Bool) :
    xor (xor a b) c = xor a (xor b c) := by cases a <;> cases b <;> cases c <;> rfl

theorem parity_zero (vs : List Nat) : parity vs (fun _=>false)=false := by
  induction vs with
  | nil => rfl
  | cons i is ih => simp only [parity,ih];rfl

theorem parity_add (vs : List Nat) (f g : Point → Bool) :
    parity vs (fun p=>xor (f p) (g p)) = xor (parity vs f) (parity vs g) := by
  induction vs generalizing f g with
  | nil => rfl
  | cons i is ih =>
    simp only [parity,ih]
    apply xor4

theorem mon_absent (xs : Mon) (i : Nat) (h : i ∉ xs) (x : Point) (b : Bool) :
    mon xs (varSet x i b) = mon xs x := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
    have h₀ : j ≠ i := by
      intro e; subst j; exact h List.mem_cons_self
    have h₁ : i ∉ js := fun e=>h (List.mem_cons_of_mem _ e)
    simp only [mon,List.foldr_cons,varSet,ite_eq_right h₀]
    exact congrArg (fun z=>x j && z) (ih h₁)

theorem mon_set_false (xs : Mon) (i : Nat) (h : i ∈ xs) (x : Point) :
    mon xs (varSet x i false)=false := by
  induction xs with
  | nil => simp at h
  | cons j js ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp [mon,varSet]
    · change (varSet x i false j && mon js (varSet x i false)) = false
      simp [ih h]

theorem mon_set_true (xs : Mon) (i : Nat) (x : Point) :
    mon xs (varSet x i true)=mon (xs.filter (fun j=>decide (j ≠ i))) x := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
    by_cases h : j=i
    · subst j
      simpa [List.filter_cons,mon,varSet] using ih
    · simp [List.filter_cons,mon,varSet,h] at ih ⊢
      exact congrArg (fun v => x j && v) ih

theorem absent_parity (vs xs : List Nat) (i : Nat) (hi : i ∈ vs) (hm : i ∉ xs) :
    parity vs (mon xs)=false := by
  induction vs generalizing xs with
  | nil => simp at hi
  | cons j js ih =>
    by_cases jx : j ∈ xs
    · have ij : i ≠ j := by rintro rfl;exact hm jx
      have ijm : i ∈ js := by
        rcases List.mem_cons.mp hi with e|e
        · exact False.elim (ij e)
        · exact e
      have h₁ : i ∉ xs.filter (fun k => decide (k ≠ j)) := fun e=>hm (List.mem_filter.mp e).1
      have one : (fun x=>mon xs (varSet x j true)) = mon (xs.filter (fun k=>decide (k ≠ j))) := funext (mon_set_true xs j)
      have zero : (fun x=>mon xs (varSet x j false)) = (fun _=>false) := funext (mon_set_false xs j jx)
      rw [parity,one,zero,parity_zero,ih _ ijm h₁]
      rfl
    · have e (b : Bool) : (fun x=>mon xs (varSet x j b)) = mon xs :=
        funext (fun x=>mon_absent xs j jx x b)
      rw [parity,e false,e true]
      cases parity js (mon xs) <;> rfl

theorem top_parity (vs : List Nat) (nd : vs.Nodup) :
    parity vs (mon vs)=true := by
  induction vs with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi,nd⟩ := List.nodup_cons.mp nd
    have zero : (fun x=>mon (i::is) (varSet x i false)) = (fun _=>false) :=
      funext (mon_set_false (i::is) i List.mem_cons_self)
    have one : (fun x=>mon (i::is) (varSet x i true)) = mon is := by
      funext x
      change ((varSet x i true i) && mon is (varSet x i true)) = _
      simp [varSet,mon_absent _ _ hi x true]
    rw [parity,zero,one,parity_zero,ih nd]
    rfl

theorem nodup_subset_length (vs xs : List Nat) (nd : vs.Nodup)
    (sub : ∀ a ∈ vs,a ∈ xs) : vs.length ≤ xs.length := by
  induction vs generalizing xs with
  | nil => simp
  | cons i is ih =>
    obtain ⟨hi,nd⟩ := List.nodup_cons.mp nd
    have hx := sub i List.mem_cons_self
    have hsub (a : Nat) (ha : a ∈ is) : a ∈ xs.erase i := by
      have ne : a ≠ i := by rintro rfl;exact hi ha
      exact List.mem_erase_of_ne ne |>.mpr (sub a (List.mem_cons_of_mem _ ha))
    have r := ih (xs.erase i) nd hsub
    have l := List.length_erase_of_mem hx
    have pos : 0 < xs.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

theorem short_parity (vs xs : List Nat) (nd : vs.Nodup) (small : xs.length < vs.length) :
    parity vs (mon xs)=false := by
  classical
  by_cases suff : ∀ a ∈ vs,a ∈ xs
  · have contra := nodup_subset_length vs xs nd suff
    omega
  · have w : ∃ i, i ∈ vs ∧ i ∉ xs := by
      apply Classical.byContradiction
      intro h
      apply suff
      intro a ha
      apply Classical.byContradiction
      intro hn
      exact h ⟨a,ha,hn⟩
    obtain ⟨i,hi,hm⟩ := w
    exact absent_parity vs xs i hi hm

theorem polynomial_parity_zero (vs : List Nat) (p : Poly) (nd : vs.Nodup)
    (small : ∀ xs ∈ p,xs.length < vs.length) :
    parity vs (eval p)=false := by
  induction p with
  | nil => exact parity_zero vs
  | cons m p ih =>
    have h₀ := short_parity vs m nd (small m List.mem_cons_self)
    have h₁ := ih (fun s hs=>small s (List.mem_cons_of_mem _ hs))
    change parity vs (fun x=>xor (mon m x) (eval p x))=false
    rw [parity_add,h₀,h₁];rfl

def mul (p q : Poly) : Poly :=
  p.flatMap (fun a=>q.map (fun b=>a++b))

theorem eval_append (p q : Poly) (x : Point) : eval (p++q) x = xor (eval p x) (eval q x) := by
  induction p with
  | nil =>
    change eval q x=xor false (eval q x)
    cases eval q x <;> rfl
  | cons a p ih =>
    change xor (mon a x) (eval (p++q) x)=xor (xor (mon a x) (eval p x)) (eval q x)
    rw [ih,xor_assoc]

theorem mon_append (a b : Mon) (x : Point) : mon (a++b) x = (mon a x && mon b x) := by
  induction a with
  | nil =>
    change mon b x=(true && mon b x)
    rfl
  | cons i a ih =>
    change (x i && mon (a++b) x)=(x i && mon a x && mon b x)
    rw [ih]
    cases x i <;> cases mon a x <;> cases mon b x <;> rfl

theorem eval_map_app (a : Mon) (q : Poly) (x : Point) :
    eval (q.map (fun b=>a++b)) x = (mon a x && eval q x) := by
  induction q with
  | nil =>
    change false=(mon a x && false)
    cases mon a x <;> rfl
  | cons b q ih =>
    change xor (mon (a++b) x) (eval (q.map (fun b=>a++b)) x) =
      (mon a x && xor (mon b x) (eval q x))
    rw [mon_append,ih,and_xor]

theorem eval_mul (p q : Poly) (x : Point) : eval (mul p q) x = (eval p x && eval q x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change eval (q.map (fun b=>a++b)++mul p q) x =
      (xor (mon a x) (eval p x) && eval q x)
    rw [eval_append,eval_map_app,ih,xor_and]

theorem degree_mul (p q : Poly) (n m : Nat)
    (hp : ∀ a ∈ p,a.length ≤ n) (hq : ∀ b ∈ q,b.length ≤ m) :
    ∀ w ∈ mul p q,w.length ≤ n+m := by
  intro w hw
  obtain ⟨a,ha,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  rw [List.length_append]
  exact Nat.add_le_add (hp _ ha) (hq _ hb)

abbrev Residual := (Nat × Nat) × Poly

def top : List Residual → Mon
  | [] => []
  | ((a,b),_)::rs => a::b::top rs

def product : List Residual → Point → Bool
  | [], _ => true
  | ((a,b),aff)::rs,x => (xor (mon [a,b] x) (eval aff x) && product rs x)

/-- The highest-degree monomial appears just once; the others are strictly
    shorter, even if the affine tail mentions variables in other pairs. -/
theorem product_split (rs : List Residual)
    (affine : ∀ r ∈ rs, ∀ w ∈ r.2, w.length ≤ 1) :
    ∃ low : Poly, (∀ w ∈ low, w.length < (top rs).length) ∧ 
      ∀ x, product rs x = xor (mon (top rs) x) (eval low x) := by
  induction rs with
  | nil => exact ⟨[],by simp,by intro x; rfl⟩
  | cons r rs ih =>
    rcases r with ⟨⟨a,b⟩,p⟩
    have hp := affine ((a,b),p) List.mem_cons_self
    obtain ⟨low,hl,eq⟩ := ih (fun r hr => affine r (List.mem_cons_of_mem _ hr))
    let low' := mul [[a,b]] low ++ mul p (top rs::low)
    refine ⟨low',?_,?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with h|h
      · obtain ⟨m,hm,ht⟩ := List.mem_flatMap.mp h
        have e : m=[a,b] := by simpa using hm
        subst m
        obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ht
        have b₀ := hl m hm
        simp only [List.length_append,List.length_cons,List.length_nil,top]
        omega
      · have h₂ := degree_mul p (top rs::low) 1 (top rs).length hp (by
          intro m hm
          rcases List.mem_cons.mp hm with rfl|hm
          · exact Nat.le_refl _
          · exact Nat.le_of_lt (hl m hm)) w h
        simp only [top,List.length_cons]
        omega
    · intro x
      change (xor (mon [a,b] x) (eval p x) && product rs x) =
        xor (mon ([a,b]++top rs) x) (eval low' x)
      have single : eval [[a,b]] x=mon [a,b] x := by
        change xor (mon [a,b] x) false=mon [a,b] x
        cases mon [a,b] x <;> rfl
      change _ = xor (mon ([a,b]++top rs) x) (eval (mul [[a,b]] low++mul p (top rs::low)) x)
      rw [eval_append,eval_mul,eval_mul,mon_append,single,eq]
      change (xor (mon [a,b] x) (eval p x) && xor (mon (top rs) x) (eval low x)) =
        xor (mon [a,b] x && mon (top rs) x)
          (xor (mon [a,b] x && eval low x) (eval p x && xor (mon (top rs) x) (eval low x)))
      rw [xor_and,and_xor (mon [a,b] x),xor_assoc]

theorem simultaneous_errors (rs : List Residual) (nd : (top rs).Nodup)
    (affine : ∀ r ∈ rs, ∀ w ∈ r.2,w.length ≤ 1) :
    ∃ x, ∀ r ∈ rs, xor (mon [r.1.1,r.1.2] x) (eval r.2 x)=true := by
  classical
  obtain ⟨low,hl,eq⟩ := product_split rs affine
  have ep : product rs = (fun x=>xor (mon (top rs) x) (eval low x)) := funext eq
  have parityTrue : parity (top rs) (product rs)=true := by
    rw [ep,parity_add,top_parity _ nd,polynomial_parity_zero _ _ nd hl]
    rfl
  have existsProduct : ∃ x, product rs x=true := by
    apply Classical.byContradiction
    intro h
    have he : product rs = (fun _=>false) := by
      funext x
      cases e : product rs x
      · rfl
      · exact False.elim (h ⟨x,e⟩)
    rw [he,parity_zero] at parityTrue
    cases parityTrue
  obtain ⟨x,hx⟩ := existsProduct
  refine ⟨x,?_⟩
  clear low hl affine eq ep parityTrue nd
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rcases r with ⟨⟨a,b⟩,p⟩
    change (xor (mon [a,b] x) (eval p x) && product rs x)=true at hx
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp hx
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · exact head
    · exact ih tail t ht

end PEqualNP.Outside.L_meta_32058_aux.Degree


namespace PEqualNP.Outside.L_meta_32058_aux.Kernel

def Period {A : Type} (x : Nat → A) (p : Nat) : Prop :=
  ∀ i, x (i+p)=x i

theorem period_mul {A : Type} {x : Nat → A} {p : Nat} (hp : Period x p) (m : Nat) :
    Period x (p*m) := by
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [Nat.mul_succ,←Nat.add_assoc,hp,ih]

theorem period_of_dvd {A : Type} {x : Nat → A} {p q : Nat}
    (hp : Period x p) (d : p∣q) : Period x q := by
  obtain ⟨t,rfl⟩ := d
  exact period_mul hp t

theorem period_sub {A : Type} {x : Nat → A} {p q : Nat}
    (hp : Period x p) (hq : Period x q) (le : q ≤ p) : Period x (p-q) := by
  intro i
  have e := hq (i+(p-q))
  have f : i+(p-q)+q=i+p := by omega
  rw [f,hp] at e
  exact e.symm

theorem period_mod {A : Type} {x : Nat → A} {p q : Nat}
    (hp : Period x p) (hq : Period x q) : Period x (p % q) := by
  have e := Nat.mod_add_div p q
  have f := period_sub hp (period_mul hq (p/q)) (by omega)
  have h : p-q*(p/q)=p % q := by omega
  rwa [h] at f

theorem period_gcd {A : Type} (x : Nat → A) (p q : Nat)
    (hp : Period x p) (hq : Period x q) : Period x (p.gcd q) := by
  induction p,q using Nat.gcd.induction with
  | H0 n => simpa using hq
  | H1 m n _ ih =>
    rw [Nat.gcd_rec]
    exact ih (period_mod hq hp) hp

theorem eval_mod {A : Type} {x : Nat → A} {p : Nat}
    (hp : Period x p) (i : Nat) : x i=x (i % p) := by
  conv => lhs; rw [←Nat.mod_add_div i p]
  exact period_mul hp (i/p) (i % p)

def Rec3 (x : Nat → Bool) (d : Nat) : Prop := ∀ i, xor (x i) (x (i+d))=x (i+d+d)

theorem period3 (x : Nat → Bool) (d : Nat) (rec : Rec3 x d) : Period x (3*d) := by
  intro i
  have a := rec i
  have b := rec (i+d)
  rw [←a] at b
  have e : xor (x (i+d)) (xor (x i) (x (i+d)))=x i := by
    cases x i <;> cases x (i+d) <;> rfl
  rw [e] at b
  rw [show i+3*d=i+d+d+d by omega]
  exact b.symm

theorem gcdThree (k d : Nat) (hk : 0 < k) :
    k.gcd (3*d) = k.gcd d * ((k/(k.gcd d)).gcd 3) := by
  let g := k.gcd d
  let K := k/g
  let D := d/g
  have kfac : g*K=k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
  have dfac : g*D=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have cop : K.gcd D=1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hk
  change k.gcd (3*d)=g*(K.gcd 3)
  rw [←kfac,←dfac,←Nat.mul_assoc,Nat.mul_comm 3 g,Nat.mul_assoc,Nat.gcd_mul_left]
  rw [Nat.gcd_mul_left_right_of_gcd_eq_one cop]

theorem gcd_three (n : Nat) : n.gcd 3 = if 3∣n then 3 else 1 := by
  by_cases h : 3∣n
  · rw [ite_eq_left h,Nat.gcd_eq_right h]
  · rw [ite_eq_right h,Nat.gcd_comm n 3,Nat.gcd_rec 3 n]
    have nz : n % 3 ≠ 0 := fun e=>h (Nat.dvd_of_mod_eq_zero e)
    have lt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    have e : n % 3=1 ∨ n % 3=2 := by omega
    rcases e with e|e <;> rw [e] <;> decide +kernel

def allowance (k d : Nat) : Nat :=
  if 3 ∣ k/(k.gcd d) then 2*(k.gcd d) else 0

theorem zero_of_samples (k d : Nat) (hk : 0 < k) (x : Nat→Bool)
    (pk : Period x k) (rec : Rec3 x d)
    (zero : ∀ i, i < allowance k d → x i=false) : ∀ i,x i=false := by
  let g := k.gcd d
  let K := k/g
  let D := d/g
  have dfac : g*D=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have cop : K.gcd D=1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hk
  have p := period_gcd x k (3*d) pk (period3 x d rec)
  change Period x (k.gcd (3*d)) at p
  rw [gcdThree k d hk,gcd_three] at p
  change Period x (g*(if 3∣K then 3 else 1)) at p
  by_cases dv : 3∣K
  · rw [ite_eq_left dv] at p
    have z : ∀ i, i < 2*g → x i=false := by
      intro i hi
      apply zero i
      change i < (if 3∣K then 2*g else 0)
      rwa [ite_eq_left dv]
    have notD : ¬ 3∣D := by
      intro dD
      have e := Nat.dvd_gcd dv dD
      rw [cop] at e
      exact (by decide : ¬ 3∣1) e
    have rem : D % 3=1 ∨ D % 3=2 := by
      have h : D % 3 < 3 := Nat.mod_lt _ (by decide)
      have nz : D % 3 ≠ 0 := fun z=>notD (Nat.dvd_of_mod_eq_zero z)
      omega
    have last (i : Nat) (hi : i < g) : x (i+g*2)=false := by
      let line (t : Nat) := x (i+g*t)
      have pl : Period line 3 := by
        intro t
        unfold line
        rw [Nat.mul_add,←Nat.add_assoc]
        exact p _
      have rec0 : xor (line 0) (line D)=line (D+D) := by
        unfold line
        simpa only [Nat.mul_zero,Nat.add_zero,Nat.mul_add,dfac,←Nat.add_assoc] using rec i
      rw [eval_mod pl D,eval_mod pl (D+D)] at rec0
      have z0 : line 0=false := by simpa [line] using z i (by omega)
      have z1 : line 1=false := by simpa [line] using z (i+g) (by omega)
      rcases rem with h|h
      · have hh : (D+D) % 3=2 := by omega
        rw [h,hh,z0,z1] at rec0
        exact rec0.symm
      · have hh : (D+D) % 3=1 := by omega
        rw [h,hh,z0,z1] at rec0
        have h' : xor false (line 2)=line 2 := by cases line 2 <;> rfl
        simpa only [h'] using rec0
    intro i
    rw [eval_mod p i]
    let j := i % (g*3)
    change x j=false
    by_cases hj : j < 2*g
    · exact z j hj
    · have gp : 0 < g := Nat.gcd_pos_of_pos_left d hk
      have ht : j < g*3 := Nat.mod_lt _ (by omega)
      have eq : j=(j-2*g)+g*2 := by omega
      rw [eq]
      exact last _ (by omega)
  · rw [ite_eq_right dv,Nat.mul_one] at p
    have pd : Period x d := by rw [←dfac]; exact period_mul p D
    intro i
    have a := rec i
    rw [pd (i+d),pd i] at a
    cases e : x i <;> simp [e] at a ⊢

end PEqualNP.Outside.L_meta_32058_aux.Kernel


namespace PEqualNP.Outside.L_meta_32058_aux.Cyclic
def idx (k : Nat) (hk : 0 < k) (i : Nat) : Fin k :=
  ⟨i % k,Nat.mod_lt _ hk⟩

def next {k : Nat} (hk : 0 < k) (i : Fin k) : Fin k := idx k hk (i.val+1)

theorem mod_left (a b k : Nat) : (a % k+b) % k=(a+b) % k := by
  rw [Nat.add_mod (a % k) b k,Nat.mod_mod]
  exact (Nat.add_mod a b k).symm

theorem mod_right (a b k : Nat) : (a+b % k) % k=(a+b) % k := by
  rw [Nat.add_mod a (b % k) k,Nat.mod_mod]
  exact (Nat.add_mod a b k).symm

theorem at_add (k : Nat) (hk : 0 < k) (a b : Nat) :
    idx k hk ((idx k hk a).val+b)=idx k hk (a+b) :=
  Fin.ext (mod_left a b k)

theorem next_at (k : Nat) (hk : 0 < k) (a : Nat) :
    next hk (idx k hk a)=idx k hk (a+1) := at_add k hk a 1

theorem next_shift (k : Nat) (hk : 0 < k) (a i : Nat) :
    next hk (idx k hk (a+i))=idx k hk (a+(i+1)) := by
  rw [next_at,Nat.add_assoc]

theorem at_val {k : Nat} (hk : 0 < k) (i : Fin k) : idx k hk i.val=i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem shift_inj {k : Nat} (hk : 0 < k) (a i j : Nat) (hi : i < k) (hj : j < k)
    (e : idx k hk (a+i)=idx k hk (a+j)) : i=j := by
  have h := congrArg Fin.val e
  change (a+i) % k = (a+j) % k at h
  rw [Nat.add_mod_eq_sub (a:=a) (b:=i),Nat.add_mod_eq_sub (a:=a) (b:=j),
      Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at h
  have ha := Nat.mod_lt a hk
  split at h <;> split at h <;> omega

theorem translation_onto {k : Nat} (hk : 0 < k) (a : Nat) (i : Fin k) :
    ∃ j : Fin k, idx k hk (a+j.val)=i := by
  let b := i.val+k-a % k
  have hm := Nat.mod_lt a hk
  let j := idx k hk b
  refine ⟨j,Fin.ext ?_⟩
  change (a+b % k) % k=i.val
  rw [mod_right,←mod_left]
  have h : a % k+b=i.val+k := by dsimp [b]; omega
  rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

theorem next_inj {k : Nat} (hk : 0 < k) {i j : Fin k} (h : next hk i=next hk j) : i=j := by
  apply Fin.ext
  apply shift_inj hk 1 _ _ i.isLt j.isLt
  simpa [next,Nat.add_comm] using h

theorem next_ne {k : Nat} (hk : 0 < k) (large : 1 < k) (i : Fin k) : next hk i ≠ i := by
  intro e
  have h := next_shift k hk i.val 0
  rw [Nat.add_zero,at_val,e] at h
  have r : idx k hk (i.val+0)=idx k hk (i.val+1) := by simpa [at_val] using h
  have impossible := shift_inj hk i.val 0 1 hk large r
  omega

theorem cut_last {k : Nat} (hk : 0 < k) (r : Fin k) :
    idx k hk (r.val+1+(k-1)) = r := by
  apply Fin.ext
  change (r.val+1+(k-1)) % k = r.val
  rw [show r.val+1+(k-1)=r.val+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt r.isLt]

/-- The shift used in the literal output, with no hidden predecessor
    when n % k is zero. -/
theorem reverse_shift_inj {k : Nat} (hk : 0 < k) (n : Nat) {i j : Fin k}
    (e : idx k hk (i.val+k-n % k)=idx k hk (j.val+k-n % k)) : i=j := by
  have h := Nat.mod_lt n hk
  have e₁ : i.val+k-n % k=(k-n % k)+i.val := by omega
  have e₂ : j.val+k-n % k=(k-n % k)+j.val := by omega
  rw [e₁,e₂] at e
  exact Fin.ext (shift_inj hk _ _ _ i.isLt j.isLt e)

theorem reverse_shift_onto {k : Nat} (hk : 0 < k) (n : Nat) (i : Fin k) :
    ∃ j : Fin k, idx k hk (j.val+k-n % k)=i := by
  obtain ⟨j,hj⟩ := translation_onto hk (k-n % k) i
  have rm := Nat.mod_lt n hk
  refine ⟨j,?_⟩
  rw [show j.val+k-n % k=k-n % k+j.val by omega]
  exact hj

theorem back_after {k : Nat} (hk : 0 < k) (i d : Nat) :
    idx k hk ((idx k hk (i+d)).val+k-d % k)=idx k hk i := by
  apply Fin.ext
  change (((i+d) % k+k-d % k) % k) = i % k
  rw [Nat.add_mod_eq_sub (a:=i) (b:=d)]
  have hi := Nat.mod_lt i hk
  have hd := Nat.mod_lt d hk
  split
  · rw [show i % k+d % k-0+k-d % k=i % k+k by omega,Nat.add_mod_right,Nat.mod_mod]
  · rw [show i % k+d % k-k+k-d % k=i % k by omega,Nat.mod_mod]

end PEqualNP.Outside.L_meta_32058_aux.Cyclic


namespace PEqualNP.Outside.L_meta_32058_aux.Endpoints
open PEqualNP.Outside.L_meta_32058_aux.Cyclic

noncomputable def flatten {k : Nat} (hk : 0 < k) (es : List (Fin k)) : List Nat :=
  es.flatMap (fun i=>[i.val,(next hk i).val])

theorem flatten_mem {k : Nat} (hk : 0 < k) (es : List (Fin k)) (n : Nat) :
    n ∈ flatten hk es ↔ ∃ i ∈ es,n=i.val ∨ n=(next hk i).val := by
  simp only [flatten,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]

theorem flatten_nodup {k : Nat} (hk : 0 < k) (es : List (Fin k)) (nd : es.Nodup)
    (ind : ∀ i ∈ es,next hk i ∉ es) : (flatten hk es).Nodup := by
  induction es with
  | nil => simp [flatten]
  | cons i es ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp nd
    have its : next hk i ∉ i::es := ind i List.mem_cons_self
    have rest : ∀ j ∈ es,next hk j ∉ es :=
      fun j hj h=>ind j (List.mem_cons_of_mem _ hj) (List.mem_cons_of_mem _ h)
    change (i.val::(next hk i).val::flatten hk es).Nodup
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,ih nd rest⟩⟩
    · intro bad
      rcases List.mem_cons.mp bad with eq|e
      · exact its (List.mem_cons.mpr (.inl (Fin.ext eq.symm)))
      · obtain ⟨j,jm,eq|eq⟩ := (flatten_mem hk es _).mp e
        · exact fresh (Fin.ext eq ▸ jm)
        · exact ind j (List.mem_cons_of_mem _ jm) (List.mem_cons.mpr (.inl (Fin.ext eq.symm)))
    · intro bad
      obtain ⟨j,jm,eq|eq⟩ := (flatten_mem hk es _).mp bad
      · exact its (List.mem_cons_of_mem _ (Fin.ext eq ▸ jm))
      · exact fresh (next_inj hk (Fin.ext eq) ▸ jm)

theorem next_onto {k : Nat} (hk : 0 < k) (i : Fin k) :
    ∃ j, next hk j=i := by
  obtain ⟨j,jh⟩ := translation_onto hk 1 i
  exact ⟨j,by simpa [next,Nat.add_comm] using jh⟩

end PEqualNP.Outside.L_meta_32058_aux.Endpoints


namespace PEqualNP.Outside.L_meta_32058_aux.Fixed
open PEqualNP.Outside.L_meta_32058_aux

def nodes : Nat → List H
  | 0 => []
  | d+1 => [] :: (nodes d).map (false::·) ++ (nodes d).map (true::·)

theorem membership (d : Nat) (p : H) : p ∈ nodes d ↔ p.length < d := by
  induction d generalizing p with
  | zero => simp [nodes]
  | succ d ih =>
    cases p with
    | nil => simp [nodes]
    | cons v p => cases v <;> simp [nodes,ih]

private theorem cons_nd (ps : List H) (nd : ps.Nodup) (b : Bool) :
    (ps.map (b::·)).Nodup :=
  List.pairwise_map.mpr (nd.imp (fun hn e => hn (List.cons.inj e).2))

theorem nodup (d : Nat) : (nodes d).Nodup := by
  induction d with
  | zero => simp [nodes]
  | succ d ih =>
    rw [nodes]
    change ([] :: ((nodes d).map (false::·) ++ (nodes d).map (true::·))).Nodup
    rw [List.nodup_cons]
    refine ⟨by simp, List.nodup_append.mpr ⟨cons_nd _ ih _,cons_nd _ ih _,?_⟩⟩
    intro a ha b hb e
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
    cases e

theorem count (d : Nat) : (nodes d).length+1=2^d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [nodes,List.length_cons,List.length_append,List.length_map,Nat.pow_succ]
    omega

theorem depth_le (d : Nat) : d ≤ (nodes d).length := by
  induction d with
  | zero => simp
  | succ d ih => simp only [nodes,List.length_cons,List.length_append,List.length_map];omega

theorem final_length (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H)
    (hp : p.length ≤ d) :
    (follow (nodes d) (fun a=>A a.length) fuel p).length =
      min d (p.length+fuel) := by
  induction fuel generalizing p with
  | zero => simp [follow,Nat.min_eq_right hp]
  | succ fuel ih =>
    by_cases e : p.length < d
    · have he := (membership d p).mpr e
      simp only [follow,advance,he,ite_true]
      rw [ih (p++[A p.length]) (by simp;omega)]
      simp only [List.length_append,List.length_cons,List.length_nil]
      congr 1
      omega
    · have he : p ∉ nodes d := fun h=>(Nat.not_lt.mpr (Nat.le_of_not_gt e)) ((membership d p).mp h)
      rw [no_node _ _ _ _ he,Nat.min_eq_left (by omega)]
      omega

theorem answer_get (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H)
    (j : Nat) (hj : p.length ≤ j)
    (hr : j < (follow (nodes d) (fun a=>A a.length) fuel p).length) :
    (follow (nodes d) (fun a=>A a.length) fuel p)[j]=A j := by
  induction fuel generalizing p with
  | zero =>
    change j < p.length at hr
    omega
  | succ fuel ih =>
    by_cases e : p ∈ nodes d
    · have eq : follow (nodes d) (fun a=>A a.length) (fuel+1) p =
          follow (nodes d) (fun a=>A a.length) fuel (p++[A p.length]) := by
          simp [follow,advance,e]
      simp only [eq] at hr ⊢
      by_cases h : j=p.length
      · subst j
        obtain ⟨ss,hss⟩ := prefix_follow (nodes d) (fun a=>A a.length) fuel (p++[A p.length])
        simp only [hss]
        rw [List.getElem_append_left (by simp),List.getElem_append_right (by omega)]
        simp
      · exact ih (p++[A p.length]) (by simp;omega) hr
    · have eq := no_node (nodes d) (fun a=>A a.length) (fuel+1) p e
      rw [eq] at hr
      omega

theorem fixed_history (d : Nat) (A : Nat → Bool) (fuel : Nat) (hf : d ≤ fuel) :
    let p := (List.range fuel).foldl (fun p _ =>
      if p ∈ nodes d then p++[A p.length] else p) []
    p.length=d ∧ ∀ j : Nat, j < d → p[j]?=some (A j) := by
  dsimp only
  have e := fold_follow (nodes d) (fun a=>A a.length) (List.range fuel) []
  have len : (follow (nodes d) (fun a=>A a.length) fuel []).length=d := by
    rw [final_length _ _ _ _ (by simp),List.length_nil,Nat.zero_add,Nat.min_eq_left hf]
  simp only [List.length_range] at e
  refine ⟨e ▸ len,?_⟩
  intro j hj
  change ((List.range fuel).foldl (fun q _ => advance (nodes d) (fun a=>A a.length) q) [])[j]? = _
  rw [e,List.getElem?_eq_getElem (by omega),answer_get d A fuel [] j (by simp) (by omega)]

end PEqualNP.Outside.L_meta_32058_aux.Fixed


namespace PEqualNP.Outside.L_meta_32058_aux.Chart
open Function
abbrev F := ZMod 2

theorem zero_or_one (x : F) : x=0 ∨ x=1 := by decide +kernel +revert

theorem eq_one (x : F) (h : x ≠ 0) : x=1 :=
  (zero_or_one x).resolve_left h

theorem two_add (x : F) : x+x=0 := by
  rcases zero_or_one x with rfl|rfl <;> decide +kernel

def project {M : Type} [AddCommGroup M] [Module F M] {I : Type}
    (z : M →ₗ[F] (I→F)) (J : Finset I) : M →ₗ[F] (J→F) where
  toFun x j := z x j
  map_add' x y := by ext j; simp
  map_smul' s x := by ext j; simp

theorem chart {M : Type} [AddCommGroup M] [Module F M] {I : Type}
    [Fintype I] [DecidableEq I] (z : M →ₗ[F] (I→F)) :
    ∃ J : Finset I, Surjective (project z J) ∧ 
      ∀ x : M, (∀ i ∈ J,z x i=0) → z x=0 := by
  classical
  let ps := (Finset.univ : Finset (Finset I)).filter (fun J=>Surjective (project z J))
  have emp : (∅ : Finset I) ∈ ps := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro w
    exact ⟨0,funext (fun j=>False.elim (Finset.notMem_empty (j:I) j.2))⟩
  obtain ⟨J,hJ,eq⟩ := Finset.sup_mem_of_nonempty (f:=Finset.card) (s:=ps) ⟨∅,emp⟩
  have sur := (Finset.mem_filter.mp hJ).2
  refine ⟨J,sur,?_⟩
  intro x hx
  funext i
  change z x i=0
  by_cases hi : z x i=0
  · exact hi
  have nJ : i ∉ J := fun e=>hi (hx i e)
  have one := eq_one _ hi
  have inser : Surjective (project z (insert i J)) := by
    intro w
    let embed (j : J) : (insert i J : Finset I) := ⟨j,Finset.mem_insert_of_mem j.2⟩
    obtain ⟨v,hv⟩ := sur (fun j=>w (embed j))
    let it : (insert i J : Finset I) := ⟨i,Finset.mem_insert_self _ _⟩
    let t : F := w it - z v i
    refine ⟨v+t • x,?_⟩
    funext j
    change z (v+t • x) j = w j
    have add : z (v+t • x) j = z v j + t*z x j := by
      simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [add]
    rcases Finset.mem_insert.mp j.2 with e|m
    · have je : j=it := Subtype.ext e
      subst j
      change z v i+t*z x i=w it
      rw [one,mul_one]
      dsimp [t]
      rw [add_comm (z v i),sub_add_cancel]
    · rw [hx _ m,mul_zero,add_zero]
      have hh := congrFun hv ⟨j,m⟩
      exact hh
  have hmem : insert i J ∈ ps := Finset.mem_filter.mpr ⟨Finset.mem_univ _,inser⟩
  have bound := Finset.le_sup (f:=Finset.card) hmem
  rw [←eq,Finset.card_insert_of_notMem nJ] at bound
  omega

/-- An explicit linear section avoids importing generic projective modules. -/
noncomputable def sectionOf {M : Type} [AddCommGroup M] [Module F M] {J : Type}
    [Fintype J] [DecidableEq J] (q : M →ₗ[F] (J→F)) (hq : Surjective q) :
    (J→F) →ₗ[F] M where
  toFun w := ∑ j, w j • Classical.choose (hq (Pi.single j 1))
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' s x := by simp [Finset.smul_sum,mul_smul]

theorem section_right {M : Type} [AddCommGroup M] [Module F M] {J : Type}
    [Fintype J] [DecidableEq J] (q : M →ₗ[F] (J→F)) (hq : Surjective q) :
    RightInverse (sectionOf q hq) q := by
  classical
  intro w
  change q (∑ j, w j • Classical.choose (hq (Pi.single j 1)))=w
  have h (i : J) : q (Classical.choose (hq (Pi.single i 1)))=Pi.single i 1 := Classical.choose_spec (hq _)
  simp only [map_sum,map_smul,h]
  funext j
  change (∑ i, w i • Pi.single i (1:F)) j=w j
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

end PEqualNP.Outside.L_meta_32058_aux.Chart


namespace PEqualNP.Outside.L_meta_32058_aux.Cycle
open PEqualNP.Outside.L_meta_32058_aux.Cyclic

def independent {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) : Prop :=
  ∀ i ∈ E, next hk i ∉ E

noncomputable def mu {k : Nat} (hk : 0 < k) (sites : Finset (Fin k)) : Nat := by
  classical exact (sites.powerset.filter (independent hk)).sup Finset.card

theorem matching_witness {k : Nat} (hk : 0 < k) (sites : Finset (Fin k)) :
    ∃ E ⊆ sites, independent hk E ∧ E.card=mu hk sites := by
  classical
  let s := sites.powerset.filter (independent hk)
  have hm : (∅ : Finset (Fin k)) ∈ s := by simp [s,independent]
  obtain ⟨E,he,eq⟩ := Finset.sup_mem_of_nonempty (f:=Finset.card) (s:=s) ⟨∅,hm⟩
  have EProp := Finset.mem_filter.mp he
  exact ⟨E,Finset.mem_powerset.mp EProp.1,EProp.2,eq⟩

theorem le_mu {k : Nat} (hk : 0 < k) {E sites : Finset (Fin k)}
    (es : E⊆sites) (ind : independent hk E) : E.card ≤ mu hk sites := by
  classical
  exact Finset.le_sup (f:=Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr es,ind⟩)

theorem twice_mu {k : Nat} (hk : 0 < k) (sites : Finset (Fin k)) :
    2*mu hk sites ≤ k := by
  classical
  obtain ⟨E,_,he,hE⟩ := matching_witness hk sites
  let dest (p : E × Bool) := if p.2 then next hk p.1 else (p.1 : Fin k)
  have inj : Function.Injective dest := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    change (if a then next hk i else (i:Fin k)) = (if b then next hk j else (j:Fin k)) at eq
    cases a <;> cases b <;> simp at eq
    · exact congrArg (fun u : E=>(u,false)) eq
    · have h : next hk j ∈ E := by rw [←eq];exact i.2
      exact False.elim (he _ j.2 h)
    · have h : next hk i ∈ E := by rw [eq];exact j.2
      exact False.elim (he _ i.2 h)
    · exact congrArg (fun u : E=>(u,true)) (Subtype.ext (next_inj hk eq))
  have h := Fintype.card_le_of_injective dest inj
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_bool,Fintype.card_fin] at h
  omega

theorem endpoint_filter {k : Nat} (hk : 0 < k) (E J : Finset (Fin k))
    (ind : independent hk E) :
    E.card ≤ (E.filter (fun i=>i ∈ J ∧ next hk i ∈ J)).card + (k-J.card) := by
  classical
  let ok (i : Fin k) := i ∈ J ∧ next hk i ∈ J
  let dest (i : Fin k) := if i ∈ J then next hk i else i
  have hmaps : Set.MapsTo dest ↑(E.filter (fun i => ¬ ok i)) ↑(Finset.univ \ J) := by
    intro i hi
    have q := (Finset.mem_filter.mp hi).2
    change dest i ∈ Finset.univ \ J
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,dest]
    by_cases h : i ∈ J
    · rw [ite_eq_left h]; exact fun z=>q ⟨h,z⟩
    · rwa [ite_eq_right h]
  have hinj : Set.InjOn dest ↑(E.filter (fun i => ¬ ok i)) := by
    intro i hi j hj eq
    have ei := (Finset.mem_filter.mp hi).1
    have ej := (Finset.mem_filter.mp hj).1
    unfold dest at eq
    split at eq <;> split at eq
    · exact next_inj hk eq
    · exact False.elim (ind _ ei (eq.symm ▸ ej))
    · exact False.elim (ind _ ej (eq ▸ ei))
    · exact eq
  have bw := Finset.card_le_card_of_injOn dest hmaps hinj
  have add := Finset.card_filter_add_card_filter_not (s:=E) (p:=ok)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_fin] at bw
  change E.card ≤ (E.filter ok).card+(k-J.card)
  omega

theorem separation (ls : List Nat) (hp : ls.Pairwise (fun i j=>i+2 ≤ j)) :
    ∀ i ∈ ls, ∀ j ∈ ls, i ≠ j → i+2 ≤ j ∨ j+2 ≤ i := by
  intro i im j jm ne
  obtain ⟨a,al,ha⟩ := List.getElem_of_mem im
  obtain ⟨b,bl,hb⟩ := List.getElem_of_mem jm
  have hne : a ≠ b := by intro e; subst b; exact ne (ha.symm.trans hb)
  rcases Nat.lt_or_gt_of_ne hne with lt|lt
  · exact .inl (ha ▸ hb ▸ (List.pairwise_iff_getElem.mp hp) a b al bl lt)
  · exact .inr (ha ▸ hb ▸ (List.pairwise_iff_getElem.mp hp) b a bl al lt)

theorem translated_path {k : Nat} (hk : 0 < k) (a : Nat) (ls : List Nat)
    (rng : ∀ i ∈ ls, i+1 < k) (sep : ls.Pairwise (fun i j=>i+2 ≤ j)) :
    let T := fun i => idx k hk (a+i)
    let E := ls.toFinset.image T
    independent hk E ∧ E.card=ls.length := by
  classical
  intro T E
  have inj : Set.InjOn T ↑ls.toFinset := by
    intro i hi j hj e
    have il := rng i (List.mem_toFinset.mp hi)
    have jl := rng j (List.mem_toFinset.mp hj)
    exact shift_inj hk a i j (by omega) (by omega) e
  have nodup : ls.Nodup := sep.imp (fun h e=>by omega)
  constructor
  · intro x hx sx
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,neq⟩ := Finset.mem_image.mp sx
    have il := rng i (List.mem_toFinset.mp hi)
    have jl := rng j (List.mem_toFinset.mp hj)
    have wrapped : T (i+1)=T j := by rw [neq,←eq];exact (next_shift k hk a i).symm
    have e := shift_inj hk a (i+1) j il (by omega) wrapped
    have h := separation ls sep i (List.mem_toFinset.mp hi) j (List.mem_toFinset.mp hj)
      (by omega)
    omega
  · exact (Finset.card_image_of_injOn inj).trans (List.toFinset_card_of_nodup nodup)

/-- Non-full marked sets have a cover no larger than their matching
    budget. A selected witness edge provides its right endpoint. -/
theorem proper_cover {k : Nat} (hk : 0 < k) (sites : Finset (Fin k))
    (proper : sites ≠ Finset.univ) :
    ∃ C : Finset (Fin k), C.card ≤ mu hk sites ∧ 
      ∀ i ∈ sites, i ∈ C ∨ next hk i ∈ C := by
  classical
  have miss : ∃ r : Fin k, r ∉ sites := by
    by_contra hn
    apply proper
    ext i
    simp only [Finset.mem_univ,iff_true]
    by_contra hh
    exact hn ⟨i,hh⟩
  obtain ⟨r,hr⟩ := miss
  let a := r.val+1
  let T := fun i=>idx k hk (a+i)
  let marked := fun i=>decide (T i ∈ sites)
  let ls := Path.choose marked (k-1) 0
  obtain ⟨rr,sep,cov⟩ := Path.good marked (k-1) 0
  have rng (i) (hi : i ∈ ls) : i+1 < k := by have := (rr i hi).2.1;omega
  obtain ⟨ind,cE⟩ := translated_path hk a ls rng sep
  let E := ls.toFinset.image T
  have es : E⊆sites := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact of_decide_eq_true (rr j (List.mem_toFinset.mp hj)).2.2
  let C := ls.toFinset.image (fun j=>T (j+1))
  have cC : C.card ≤ ls.length :=
    Finset.card_image_le.trans ((List.toFinset_card_of_nodup (sep.imp (fun h e=>by omega))).le)
  refine ⟨C,cC.trans (cE ▸ le_mu hk es ind),?_⟩
  intro i hi
  obtain ⟨j,eq⟩ := translation_onto hk a i
  have bound : j.val < k-1 := by
    by_contra hn
    have e : j.val=k-1 := by omega
    have hi' : i=r := by rw [←eq,e];exact cut_last hk r
    exact hr (hi' ▸ hi)
  have m : marked j.val=true := by unfold marked T;rw [eq];exact decide_eq_true hi
  rcases cov j.val (Nat.zero_le _) (by omega) m with hit|⟨b,hb,bb⟩
  · right
    apply Finset.mem_image.mpr
    exact ⟨j.val,List.mem_toFinset.mpr hit, (next_shift k hk a j.val).symm.trans (congrArg (next hk) eq)⟩
  · left
    apply Finset.mem_image.mpr
    exact ⟨b,List.mem_toFinset.mpr hb, by rw [←bb];exact eq⟩

/-- A full cycle has the alternating cover, with one additional
    vertex exactly in the nondegenerate odd case. -/
theorem full_cover {k : Nat} (hk : 0 < k) (large : 1 < k) :
    ∃ C : Finset (Fin k),
      C.card ≤ mu hk Finset.univ+(if k % 2=1 then 1 else 0) ∧ 
      ∀ i : Fin k, i ∈ C ∨ next hk i ∈ C := by
  classical
  let T := fun j=>idx k hk (0+j)
  let ls := Path.choose (fun _=>true) (k-1) 0
  obtain ⟨rr,sep,cov⟩ := Path.good (fun _=>true) (k-1) 0
  have rng (i) (hi : i ∈ ls) : i+1 < k := by have := (rr i hi).2.1;omega
  obtain ⟨ind,cE⟩ := translated_path hk 0 ls rng sep
  let E := ls.toFinset.image T
  have l := Path.all_length (k-1) 0
  change ls.length=(k-1+1)/2 at l
  have len : ls.length=k/2 := by omega
  have bound := le_mu hk (Finset.subset_univ E) ind
  change E.card ≤ _ at bound
  change E.card=ls.length at cE
  have half : k/2 ≤ mu hk (Finset.univ : Finset (Fin k)) := by omega
  let B := ls.toFinset.image (fun j=>T (j+1))
  have bcard : B.card ≤ ls.length :=
    Finset.card_image_le.trans ((List.toFinset_card_of_nodup (sep.imp (fun h e=>by omega))).le)
  let C := if k % 2=1 then insert (idx k hk 0) B else B
  have incl : B⊆C := by
    intro i hi
    unfold C
    split
    · exact Finset.mem_insert_of_mem hi
    · exact hi
  refine ⟨C,?_,?_⟩
  · unfold C
    split
    · have ct := Finset.card_insert_le (a:=idx k hk 0) B
      omega
    · omega
  intro i
  have mv : T i.val=i := by simpa [T] using at_val hk i
  by_cases edge : i.val < k-1
  · rcases cov i.val (Nat.zero_le _) (by omega) rfl with hit|⟨j,hj,ji⟩
    · right
      apply incl
      apply Finset.mem_image.mpr
      exact ⟨i.val,List.mem_toFinset.mpr hit,
        (next_shift k hk 0 i.val).symm.trans (congrArg (next hk) mv)⟩
    · left
      apply incl
      exact Finset.mem_image.mpr ⟨j,List.mem_toFinset.mpr hj,by rw [←ji];exact mv⟩
  · have top : i.val=k-1 := by omega
    by_cases odd : k % 2=1
    · right
      have wrap : next hk i=idx k hk 0 := by
        unfold next
        rw [top,show k-1+1=k by omega]
        apply Fin.ext
        simp [idx]
      rw [wrap]
      unfold C
      rw [ite_eq_left odd]
      exact Finset.mem_insert_self _ _
    · left
      have w : k-2 ∈ ls := (Path.all_mem _ _ _).mpr (by omega)
      apply incl
      apply Finset.mem_image.mpr
      exact ⟨k-2,List.mem_toFinset.mpr w,by
        rw [show k-2+1=i.val by omega];exact mv⟩

theorem bad_range (keep : Nat → Bool) (n : Nat) :
    Path.bad keep n 0=((Finset.range n).filter (fun i=>keep i=false)).card := by
  induction n with
  | zero => simp [Path.bad]
  | succ n ih =>
    rw [Path.bad_succ_right,ih,Nat.zero_add,Finset.range_add_one]
    by_cases h : keep n=false
    · have e : (((insert n (Finset.range n)).filter (fun i=>keep i=false))) =
          insert n ((Finset.range n).filter (fun i=>keep i=false)) := by
        ext x
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_range]
        constructor
        · intro h; rcases h with ⟨rfl | l,r⟩
          · exact .inl rfl
          · exact .inr ⟨l,r⟩
        · intro h; rcases h with rfl | ⟨l,r⟩
          · exact ⟨.inl rfl,h⟩
          · exact ⟨.inr l,r⟩
      rw [e,Finset.card_insert_of_notMem (by simp),h]
      rfl
    · have ht : keep n=true := by cases en : keep n <;> simp_all
      have e : (((insert n (Finset.range n)).filter (fun i=>keep i=false))) =
          ((Finset.range n).filter (fun i=>keep i=false)) := by
        ext x
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_range]
        constructor
        · intro h; rcases h with ⟨rfl | l,r⟩
          · exact False.elim (h r)
          · exact ⟨l,r⟩
        · rintro ⟨l,r⟩;exact ⟨.inr l,r⟩
      rw [e,ht]
      simp

theorem odd_match_inside {k : Nat} (hk : 0 < k) (odd : k % 2=1)
    (J : Finset (Fin k)) {r : Fin k} (hr : r ∉ J) :
    ∃ E : Finset (Fin k), independent hk E ∧ 
      (∀ i ∈ E, i ∈ J ∧ next hk i ∈ J) ∧ 
      k/2+1 ≤ E.card+(k-J.card) := by
  classical
  let a := r.val+1
  let T := fun j=>idx k hk (a+j)
  let keep := fun j=>decide (T j ∈ J)
  let ls := Path.choose (Path.pair keep) (k-1) 0
  have last : keep (0+(k-1))=false := by
    unfold keep T a
    rw [Nat.zero_add,cut_last hk r]
    exact decide_eq_false hr
  have b := Path.odd_terminal_match keep (k-1) 0 (by rwa [show k-1+1=k by omega]) last
  obtain ⟨rr,sep,_⟩ := Path.good (Path.pair keep) (k-1) 0
  have rng (i) (hi : i ∈ ls) : i+1 < k := by have := (rr i hi).2.1;omega
  obtain ⟨ind,cE⟩ := translated_path hk a ls rng sep
  let E := ls.toFinset.image T
  have bcount : Path.bad keep k 0 ≤ k-J.card := by
    rw [bad_range]
    let R := (Finset.range k).filter (fun i=>keep i=false)
    have maps : Set.MapsTo T ↑R ↑(Finset.univ \ J) := by
      intro i hi
      have hn := (Finset.mem_filter.mp hi).2
      change T i ∈ Finset.univ \ J
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      exact of_decide_eq_false hn
    have inj : Set.InjOn T ↑R := by
      intro i hi j hj eq
      exact shift_inj hk _ _ _ (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) eq
    have bb := Finset.card_le_card_of_injOn T maps inj
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_fin] at bb
  refine ⟨E,ind,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have z := Bool.and_eq_true_iff.mp (rr j (List.mem_toFinset.mp hj)).2.2
    exact ⟨of_decide_eq_true z.1, (next_shift k hk a j).symm ▸ of_decide_eq_true z.2⟩
  · change E.card=ls.length at cE
    change (k-1+1)/2+1 ≤ ls.length+Path.bad keep (k-1+1) 0 at b
    rw [show k-1+1=k by omega] at b
    omega

end PEqualNP.Outside.L_meta_32058_aux.Cycle


namespace PEqualNP.Outside.L_meta_32058_aux.Model
open PEqualNP.Outside.L_meta_32058_aux.Cyclic PEqualNP.Outside.L_meta_32058_aux.Chart
abbrev W (k : Nat) := Fin k → F

def asBool (x : F) : Bool := decide (x ≠ 0)
def asField (x : Bool) : F := if x then 1 else 0

theorem asBool_asField (x : Bool) : asBool (asField x)=x := by
  cases x <;> decide +kernel
theorem asField_asBool (x : F) : asField (asBool x)=x := by
  rcases zero_or_one x with rfl|rfl <;> decide +kernel
theorem asBool_add (x y : F) : asBool (x+y)=xor (asBool x) (asBool y) := by
  rcases zero_or_one x with rfl|rfl <;> rcases zero_or_one y with rfl|rfl <;> decide +kernel
theorem asBool_mul (x y : F) : asBool (x*y)= (asBool x && asBool y) := by
  rcases zero_or_one x with rfl|rfl <;> rcases zero_or_one y with rfl|rfl <;> decide +kernel
theorem asBool_false (x : F) : asBool x=false ↔ x=0 := by
  rcases zero_or_one x with rfl|rfl <;> decide +kernel

def reindex {k : Nat} (s : Fin k → Fin k) : W k →ₗ[F] W k where
  toFun x i := x (s i)
  map_add' x y := rfl
  map_smul' a x := rfl

def rot {k : Nat} (hk : 0 < k) (d : Nat) : W k →ₗ[F] W k :=
  reindex (fun i => idx k hk (i.val+k-d % k))

def mix {k : Nat} (hk : 0 < k) (d : Nat) : W k →ₗ[F] W k :=
  LinearMap.id + reindex (fun i => idx k hk (i.val+d)) +
    reindex (fun i => idx k hk (i.val+k-d % k))

def ylin {k : Nat} (hk : 0 < k) (d s : Nat) : W k →ₗ[F] W k := (mix hk d).comp (rot hk s)

def yaff {k : Nat} (hk : 0 < k) (d s : Nat) (name x : W k) : W k :=
  ylin hk d s x + mix hk d name

def base {k : Nat} (hk : 0 < k) (d s t : Nat) : W k →ₗ[F] W k :=
  ylin hk d s + rot hk t

def bias {k : Nat} (hk : 0 < k) (d : Nat) (name constant : W k) : W k :=
  mix hk d name + constant

def rise {k : Nat} (hk : 0 < k) (y : W k) (i : Fin k) : F :=
  (1+y (next hk i))*y (next hk (next hk i))

def output {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k) : W k :=
  fun i => base hk d s t x i + bias hk d name constant i + rise hk (yaff hk d s name x) i

theorem y_literal {k : Nat} (hk : 0 < k) (d s : Nat) (name x : W k) (i : Fin k) :
    let old := rot hk s x + name
    yaff hk d s name x i =
      old i + old (idx k hk (i.val+d)) + old (idx k hk (i.val+k-d % k)) := by
  dsimp only
  change ((mix hk d) (rot hk s x) + (mix hk d) name) i=_
  rw [←map_add]
  rfl

theorem out_literal {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k) (i : Fin k) :
    let old := rot hk s x + name
    let y := fun u : Fin k => old u + old (idx k hk (u.val+d)) + old (idx k hk (u.val+k-d % k))
    output hk d s t name constant x i =
      y i + (1+y (idx k hk (i.val+1)))*y (idx k hk (i.val+2)) + rot hk t x i + constant i := by
  dsimp only
  rw [←y_literal,←y_literal,←y_literal]
  have e : next hk (next hk i)=idx k hk (i.val+2) := by
    unfold next
    rw [at_add]
  unfold output rise
  simp only [e]
  change ylin hk d s x i + rot hk t x i + (mix hk d name i + constant i) + _ =
    (ylin hk d s x i + mix hk d name i) + _ + rot hk t x i + constant i
  ac_rfl

theorem rise_not_both {k : Nat} (hk : 0 < k) (y : W k) (i : Fin k) :
    rise hk y i ≠ 0 → rise hk y (next hk i)=0 := by
  unfold rise
  rcases zero_or_one (y (next hk (next hk i))) with hz|hz
  · rw [hz,mul_zero]
    simp
  · rw [hz]
    have e : (1:F)+1=0 := by decide +kernel
    rw [e,zero_mul]
    intro; rfl

theorem loop_vanish {k : Nat} (hk : 0 < k) (one : k=1) (y : W k) (i : Fin k) :
    rise hk y i=0 := by
  have e : next hk i=i := by
    apply Fin.ext
    have h := (next hk i).isLt
    have hi := i.isLt
    omega
  unfold rise
  simp only [e]
  rcases zero_or_one (y i) with he|he <;> rw [he] <;> decide +kernel

def sample {k : Nat} (hk : 0 < k) (d s : Nat) : W k →ₗ[F] (Fin (Kernel.allowance k d) → F) where
  toFun x j := rot hk s x (idx k hk j.val)
  map_add' x y := by ext j; simp
  map_smul' a x := by ext j; simp

/-- The first h cyclic raw samples separate every kernel fiber. -/
theorem samples_kernel {k : Nat} (hk : 0 < k) (d s : Nat) (x : W k)
    (hy : ylin hk d s x=0) (hs : sample hk d s x=0) : x=0 := by
  let z := fun n=>asBool (rot hk s x (idx k hk n))
  have per : Kernel.Period z k := by
    intro i
    unfold z
    rw [show idx k hk (i+k)=idx k hk i from Fin.ext (Nat.add_mod_right i k)]
  have re : Kernel.Rec3 z d := by
    intro n
    have ze := congrFun hy (idx k hk (n+d))
    change (rot hk s x (idx k hk (n+d)) +
      rot hk s x (idx k hk ((idx k hk (n+d)).val+d)) +
      rot hk s x (idx k hk ((idx k hk (n+d)).val+k-d % k)))=0 at ze
    rw [at_add,back_after] at ze
    have be := congrArg asBool ze
    rw [asBool_add,asBool_add] at be
    change xor (xor (z (n+d)) (z (n+d+d))) (z n)=false at be
    cases a : z n <;> cases b : z (n+d) <;> cases c : z (n+d+d) <;> simp_all
  have zs (i : Nat) (hi : i < Kernel.allowance k d) : z i=false := by
    apply (asBool_false _).mpr
    exact congrFun hs ⟨i,hi⟩
  have all := Kernel.zero_of_samples k d hk z per re zs
  funext i
  obtain ⟨j,hj⟩ := reverse_shift_onto hk s i
  have hz := (asBool_false _).mp (all j.val)
  rw [at_val] at hz
  change x (idx k hk (j.val+k-s % k))=0 at hz
  change x i=0
  simpa only [hj] using hz

end PEqualNP.Outside.L_meta_32058_aux.Model


namespace PEqualNP.Outside.L_meta_32058_aux.Upper
open PEqualNP.Outside.L_meta_32058_aux PEqualNP.Outside.L_meta_32058_aux.Cyclic PEqualNP.Outside.L_meta_32058_aux.Cycle PEqualNP.Outside.L_meta_32058_aux.Model PEqualNP.Outside.L_meta_32058_aux.Chart

abbrev Tree (k : Nat) := Finset H × (H → W k →ₗ[F] F) × (H → F) ×
  (H → W k →ₗ[F] W k) × (H → W k)

def hist {k : Nat} (tree : Tree k) (x : W k) : H :=
  (List.range tree.1.card).foldl (fun (p : H) _ =>
    if p ∈ tree.1 then p ++ [asBool (tree.2.1 p x + tree.2.2.1 p)] else p) []

def predict {k : Nat} (tree : Tree k) (x : W k) : W k :=
  let p := hist tree x
  tree.2.2.2.1 p x + tree.2.2.2.2 p

def coord {k : Nat} (i : Fin k) : W k →ₗ[F] F where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coord_apply {k : Nat} (i : Fin k) (x : W k) : coord i x=x i := rfl

def own {k : Nat} (hk : 0 < k) (C : Finset (Fin k)) (i : Fin k) : Fin k :=
  if i ∈ C then i else next hk i

theorem own_mem {k : Nat} (hk : 0 < k) (C : Finset (Fin k))
    (i : Fin k) (cover : i ∈ C ∨ next hk i ∈ C) : own hk C i ∈ C := by
  unfold own
  split <;> rename_i c
  · exact c
  · exact cover.resolve_left c

theorem own_injective_rises {k : Nat} (hk : 0 < k) (C : Finset (Fin k))
    (y : W k) {i j : Fin k} (hi : rise hk y i ≠ 0) (hj : rise hk y j ≠ 0)
    (eq : own hk C i=own hk C j) : i=j := by
  unfold own at eq
  split at eq <;> split at eq
  · exact eq
  · exact False.elim (hi (eq ▸ rise_not_both hk y j hj))
  · exact False.elim (hj (eq.symm ▸ rise_not_both hk y i hi))
  · exact next_inj hk eq

noncomputable def fixedNodes (n : Nat) : Finset H := (Fixed.nodes n).toFinset

def chooseAsk {k : Nat} (hk : 0 < k) (d s : Nat) (qs : List (Fin k)) (p : H) :
    W k →ₗ[F] F :=
  if h : p.length < qs.length then (coord (next hk qs[p.length])).comp (ylin hk d s) else 0

def chooseBias {k : Nat} (hk : 0 < k) (d : Nat) (name : W k) (qs : List (Fin k)) (p : H) : F :=
  if h : p.length < qs.length then mix hk d name (next hk qs[p.length]) else 0

def pin {k : Nat} (qs : List (Fin k)) (p : H) (i : Fin k) : F :=
  asField ((p[qs.idxOf i]?).getD false)

def correctionLin {k : Nat} (hk : 0 < k) (d s : Nat) (C Q : Finset (Fin k))
    (qs : List (Fin k)) (p : H) (i : Fin k) : W k →ₗ[F] F :=
  let o := own hk C i
  let a := pin qs p o
  if o ∈ Q then
    if o=i then (1+a) • (coord (next hk (next hk i))).comp (ylin hk d s)
    else a • (coord (next hk i)).comp (ylin hk d s)
  else 0

def correctionBias {k : Nat} (hk : 0 < k) (d : Nat) (name : W k) (C Q : Finset (Fin k))
    (qs : List (Fin k)) (p : H) (i : Fin k) : F :=
  let o := own hk C i
  let a := pin qs p o
  if o ∈ Q then
    if o=i then (1+a)*mix hk d name (next hk (next hk i))
    else a*(1+mix hk d name (next hk i))
  else 0

noncomputable def fixedTree {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (C Q : Finset (Fin k)) : Tree k :=
  let qs := Q.toList
  (fixedNodes qs.length, chooseAsk hk d s qs, chooseBias hk d name qs,
    fun p => base hk d s t + LinearMap.pi (correctionLin hk d s C Q qs p),
    fun p => bias hk d name constant + correctionBias hk d name C Q qs p)

theorem fixed_card {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (C Q : Finset (Fin k)) :
    (fixedTree hk d s t name constant C Q).1.card+1=2^Q.card := by
  unfold fixedTree fixedNodes
  simp only [List.toFinset_card_of_nodup (Fixed.nodup _),Finset.length_toList,Fixed.count]

theorem fixed_pin {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k)
    (C Q : Finset (Fin k)) (i : Fin k) (hi : i ∈ Q) :
    pin Q.toList (hist (fixedTree hk d s t name constant C Q) x) i =
    yaff hk d s name x (next hk i) := by
  classical
  let qs := Q.toList
  let tree := fixedTree hk d s t name constant C Q
  let A := fun j : Nat=> if h:j < qs.length then asBool (yaff hk d s name x (next hk qs[j])) else false
  have Aeq (p : H) : asBool (tree.2.1 p x + tree.2.2.1 p)=A p.length := by
    change asBool (chooseAsk hk d s qs p x + chooseBias hk d name qs p)=_
    unfold chooseAsk chooseBias A
    split
    · rfl
    · simpa using (asBool_false 0).mpr rfl
  have ds : qs.length ≤ tree.1.card := by
    change qs.length ≤ (Fixed.nodes qs.length).toFinset.card
    rw [List.toFinset_card_of_nodup (Fixed.nodup _)]
    exact Fixed.depth_le _
  have he : hist tree x = (List.range tree.1.card).foldl (fun p _=>
      if p ∈ Fixed.nodes qs.length then p++[A p.length] else p) [] := by
    unfold hist
    simp only [Aeq]
    change (List.range tree.1.card).foldl (fun (p : H) _=>
      if p ∈ (Fixed.nodes qs.length).toFinset then p++[A p.length] else p) [] = _
    simp only [List.mem_toFinset]
  have j : qs.idxOf i < qs.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr hi)
  have hx := (Fixed.fixed_history qs.length A tree.1.card ds).2 _ j
  change asField ((hist tree x)[qs.idxOf i]?.getD false)=_
  rw [he,hx]
  change asField (A (qs.idxOf i))=_
  unfold A
  rw [dite_eq_left j,List.getElem_idxOf]
  exact asField_asBool _

theorem fixed_output {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k)
    (C Q : Finset (Fin k)) (i : Fin k) :
    predict (fixedTree hk d s t name constant C Q) x i =
      base hk d s t x i + bias hk d name constant i +
      (if own hk C i ∈ Q then rise hk (yaff hk d s name x) i else 0) := by
  classical
  let p := hist (fixedTree hk d s t name constant C Q) x
  let o := own hk C i
  let qs := Q.toList
  change (base hk d s t x i + correctionLin hk d s C Q qs p i x) +
    (bias hk d name constant i + correctionBias hk d name C Q qs p i) = _
  unfold correctionLin correctionBias
  dsimp only
  change ((base hk d s t x i +
    ((if o ∈ Q then _ else 0) : W k →ₗ[F] F) x) +
    (bias hk d name constant i + (if o ∈ Q then _ else 0))) =
    base hk d s t x i + bias hk d name constant i +
      (if o ∈ Q then rise hk (yaff hk d s name x) i else 0)
  by_cases h : o ∈ Q
  · rw [ite_eq_left h,ite_eq_left h,ite_eq_left h,fixed_pin hk d s t name constant x C Q o h]
    change _ = _ + rise hk (yaff hk d s name x) i
    by_cases oi : o=i
    · have eq : own hk C i=i := oi
      simp only [eq,ite_true,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul,coord_apply,oi]
      unfold rise
      change _ = _ + (1+yaff hk d s name x (next hk i)) *
          (ylin hk d s x (next hk (next hk i))+mix hk d name (next hk (next hk i)))
      rw [mul_add]
      ac_rfl
    · have oe : o=next hk i := by
        change (if i ∈ C then i else next hk i)=_
        by_cases ic : i ∈ C
        · exact False.elim (oi (ite_eq_left ic))
        · exact ite_eq_right ic
      rw [ite_eq_right oi,ite_eq_right oi,oe]
      simp only [LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul,coord_apply]
      unfold rise
      change _ = _ + (1+(ylin hk d s x (next hk i)+mix hk d name (next hk i))) *
          yaff hk d s name x (next hk (next hk i))
      rw [show 1+(ylin hk d s x (next hk i)+mix hk d name (next hk i)) =
          ylin hk d s x (next hk i)+(1+mix hk d name (next hk i)) by ac_rfl,add_mul]
      simp only [mul_comm (ylin hk d s x (next hk i)),mul_comm (1+mix hk d name (next hk i))]
      ac_rfl
  · simp only [ite_eq_right h,LinearMap.zero_apply,add_zero]

noncomputable def extra {k : Nat} (hk : 0 < k) (sites : Finset (Fin k)) (e : Nat) : Nat :=
  if sites=Finset.univ ∧ 1 < k ∧ k % 2=1 ∧ e < mu hk sites then 1 else 0

theorem upper {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e : Nat) :
    ∃ tree : Tree k, tree.1.card < 2^(mu hk sites-e+extra hk sites e) ∧ 
      ∀ x : W k, (sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)).card ≤ e := by
  classical
  by_cases exc : mu hk sites ≤ e
  · let tree := fixedTree hk d s t name constant ∅ ∅
    refine ⟨tree,?_,?_⟩
    · have b := fixed_card hk d s t name constant ∅ ∅
      have pos : 0 < 2^(mu hk sites-e+extra hk sites e) := Nat.two_pow_pos _
      change tree.1.card+1=2^0 at b
      omega
    intro x
    let bad := sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)
    have bs : bad⊆sites := Finset.filter_subset _ _
    have nz (i) (hi : i ∈ bad) : rise hk (yaff hk d s name x) i ≠ 0 := by
      have h := (Finset.mem_filter.mp hi).2
      intro ce
      rw [fixed_output,output,ce,ite_eq_right (Finset.notMem_empty _),add_zero] at h
      exact h rfl
    have ind : independent hk bad := fun i hi hj=>nz _ hj (rise_not_both hk _ _ (nz _ hi))
    exact (le_mu hk bs ind).trans exc
  · have et : e < mu hk sites := by omega
    have large : 1 < k := by have := twice_mu hk sites; omega
    have cover : ∃ C : Finset (Fin k), C.card ≤ mu hk sites+extra hk sites e ∧ 
        ∀ i ∈ sites,i ∈ C ∨ next hk i ∈ C := by
      by_cases full : sites=Finset.univ
      · subst sites
        obtain ⟨C,cs,cc⟩ := full_cover hk large
        refine ⟨C,?_,fun i _=>cc i⟩
        simpa only [extra,true_and,large,et,and_true] using cs
      · obtain ⟨C,cs,cc⟩ := proper_cover hk sites full
        exact ⟨C,by omega,cc⟩
    obtain ⟨C,cs,cc⟩ := cover
    obtain ⟨D,dc,dl⟩ := Finset.exists_subset_card_eq (Nat.min_le_right e C.card)
    let Q := C \ D
    let tree := fixedTree hk d s t name constant C Q
    refine ⟨tree,?_,?_⟩
    · have qn := Finset.card_sdiff_of_subset dc
      change Q.card=C.card-D.card at qn
      have b := fixed_card hk d s t name constant C Q
      have ex := Nat.le_of_lt et
      have qr : Q.card ≤ mu hk sites-e+extra hk sites e := by omega
      have pow := Nat.pow_le_pow_right (by decide : 0 < 2) qr
      change tree.1.card+1=2^Q.card at b
      omega
    intro x
    let bad := sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)
    have err (i) (hi : i ∈ bad) : own hk C i ∈ D ∧ rise hk (yaff hk d s name x) i ≠ 0 := by
      obtain ⟨hsite,he⟩ := Finset.mem_filter.mp hi
      have hm : own hk C i ∈ C := own_mem hk _ i (cc i hsite)
      change predict (fixedTree hk d s t name constant C Q) x i ≠ _ at he
      rw [fixed_output,output] at he
      by_cases hq : own hk C i ∈ Q
      · exact False.elim (he (by rw [ite_eq_left hq]))
      · refine ⟨?_,?_⟩
        · by_contra hd
          exact hq (Finset.mem_sdiff.mpr ⟨hm,hd⟩)
        · intro hz
          exact he (by rw [ite_eq_right hq,hz])
    have bc := Finset.card_le_card_of_injOn (own hk C)
      (s:=bad) (t:=D) (fun i hi=>(err i hi).1)
      (fun i hi j hj eq=>own_injective_rises hk C _ (err i hi).2 (err j hj).2 eq)
    exact bc.trans (dl ▸ Nat.min_le_left _ _)

end PEqualNP.Outside.L_meta_32058_aux.Upper


namespace PEqualNP.Outside.L_meta_32058_aux.Encoding
open PEqualNP.Outside.L_meta_32058_aux.Cyclic PEqualNP.Outside.L_meta_32058_aux.Chart PEqualNP.Outside.L_meta_32058_aux.Model PEqualNP.Outside.L_meta_32058_aux.Cycle

def terms {I : Type} (addr : I → Nat) (coeff : I → F) : List I → Degree.Poly
  | [] => []
  | i::is => if asBool (coeff i) then [addr i]::terms addr coeff is else terms addr coeff is

theorem terms_short {I : Type} (addr : I → Nat) (coeff : I → F) (ls : List I) :
    ∀ m ∈ terms addr coeff ls, m.length ≤ 1 := by
  induction ls with
  | nil => simp [terms]
  | cons i ls ih =>
    intro m hm
    unfold terms at hm
    split at hm
    · rcases List.mem_cons.mp hm with rfl|h
      · rfl
      · exact ih _ h
    · exact ih _ hm

theorem terms_eval {I : Type} (addr : I → Nat) (coeff : I → F) (ls : List I) (x : Degree.Point) :
    Degree.eval (terms addr coeff ls) x =
      asBool ((ls.map (fun i=>asField (x (addr i))*coeff i)).sum) := by
  induction ls with
  | nil => rfl
  | cons i ls ih =>
    simp only [terms,List.map_cons,List.sum_cons,asBool_add,asBool_mul,asBool_asField]
    rw [←ih]
    have hstep : Degree.eval ([addr i]::terms addr coeff ls) x =
        xor (x (addr i)) (Degree.eval (terms addr coeff ls) x) := by
      change xor (x (addr i) && true) (Degree.eval (terms addr coeff ls) x) = xor (x (addr i)) (Degree.eval (terms addr coeff ls) x)
      rw [Bool.and_true]
    cases h : asBool (coeff i) <;> simp [h,hstep]

noncomputable def polynomial {I : Type} [Fintype I] [DecidableEq I] (addr : I → Nat)
    (l : (I → F) →ₗ[F] F) (b : F) : Degree.Poly :=
  (if asBool b then [[]] else []) ++
    terms addr (fun i=>l (fun j=>if i=j then 1 else 0)) Finset.univ.toList

theorem polynomial_short {I : Type} [Fintype I] [DecidableEq I] (addr : I → Nat)
    (l : (I → F) →ₗ[F] F) (b : F) :
    ∀ m ∈ polynomial addr l b, m.length ≤ 1 := by
  intro m hm
  rcases List.mem_append.mp hm with he|he
  · split at he
    · have h : m=[] := by simpa using he
      subst m
      decide
    · simp at he
  · exact terms_short _ _ _ _ he

theorem polynomial_eval {I : Type} [Fintype I] [DecidableEq I] (addr : I → Nat)
    (l : (I → F) →ₗ[F] F) (b : F) (x : Degree.Point) :
    Degree.eval (polynomial addr l b) x =
      asBool (l (fun j=>asField (x (addr j)))+b) := by
  unfold polynomial
  rw [Degree.eval_append,terms_eval,Finset.sum_map_toList]
  rw [LinearMap.pi_apply_eq_sum_univ,asBool_add]
  simp only [smul_eq_mul]
  cases h : asBool b <;>
    cases e : asBool (∑ i : I, asField (x (addr i)) * l (fun j=>if i=j then 1 else 0)) <;>
    simp [h,e,Degree.eval,Degree.mon]

def evaluate {I : Type} [DecidableEq I] (j : I) : (I→F) →ₗ[F] F where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem top_flatten {k : Nat} (hk : 0 < k) (ls : List (Fin k))
    (forms : Fin k → Degree.Poly) :
    Degree.top (ls.map (fun i=>((i.val,(next hk i).val),forms i)))=Endpoints.flatten hk ls := by
  induction ls with
  | nil => rfl
  | cons i ls ih =>
    change i.val::(next hk i).val::Degree.top _ = i.val::(next hk i).val::Endpoints.flatten hk ls
    rw [ih]

theorem joint {k : Nat} (hk : 0 < k) (J E : Finset (Fin k))
    (ind : independent hk E) (ends : ∀ i ∈ E,i ∈ J ∧ next hk i ∈ J)
    (L : (J → F) →ₗ[F] W k) (b : W k) :
    ∃ x : J → F, ∀ i (hi : i ∈ E),
      L x i + b i + (1+x ⟨i,(ends i hi).1⟩)*x ⟨next hk i,(ends i hi).2⟩ ≠ 0 := by
  classical
  let addr : J → Nat := fun j=>j.1.val
  let lin (i : Fin k) : (J → F) →ₗ[F] F :=
    (evaluate i).comp L + (if h : next hk i ∈ J then evaluate ⟨next hk i,h⟩ else 0)
  let forms (i : Fin k) : Degree.Poly := polynomial addr (lin i) (b i)
  let ats (i : Fin k) : Degree.Residual := ((i.val,(next hk i).val),forms i)
  let ls := E.toList
  let rs := ls.map ats
  have nd : (Degree.top rs).Nodup := by
    change (Degree.top (ls.map (fun i=>((i.val,(next hk i).val),forms i)))).Nodup
    rw [top_flatten]
    exact Endpoints.flatten_nodup hk ls E.nodup_toList
      (fun i hi h=>ind i (Finset.mem_toList.mp hi) (Finset.mem_toList.mp h))
  have a : ∀ r ∈ rs, ∀ m ∈ r.2,m.length ≤ 1 := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact polynomial_short _ _ _
  obtain ⟨p,hp⟩ := Degree.simultaneous_errors rs nd a
  let x : J→F := fun j=>asField (p (addr j))
  refine ⟨x,?_⟩
  intro i hi
  let j₀ : J := ⟨i,(ends i hi).1⟩
  let j₁ : J := ⟨next hk i,(ends i hi).2⟩
  have h := hp (ats i) (List.mem_map_of_mem (Finset.mem_toList.mpr hi))
  change xor (Degree.mon [i.val,(next hk i).val] p) (Degree.eval (forms i) p)=true at h
  change xor (p i.val && (p (next hk i).val && true)) (Degree.eval (forms i) p)=true at h
  have hmono : Degree.mon [i.val,(next hk i).val] p = asBool (x j₀*x j₁) := by
    rw [asBool_mul]
    change (p i.val && (p (next hk i).val && true)) =
      (asBool (asField (p i.val)) && asBool (asField (p (next hk i).val)))
    simp [asBool_asField]
  change xor (Degree.mon [i.val,(next hk i).val] p)
      (Degree.eval (polynomial addr (lin i) (b i)) p)=true at h
  rw [hmono,polynomial_eval,←asBool_add] at h
  have r : lin i x=L x i+x j₁ := by
    unfold lin
    rw [dite_eq_left (ends i hi).2]
    rfl
  change asBool (x j₀*x j₁+(lin i x+b i))=true at h
  rw [r] at h
  change L x i+b i+(1+x j₀)*x j₁ ≠ 0
  intro z
  rw [add_mul,one_mul] at z
  have z' : x j₀*x j₁+(L x i+x j₁+b i)=0 := (by ac_rfl : _ = L x i+b i+(x j₁+x j₀*x j₁)).trans z
  rw [z'] at h
  contradiction

end PEqualNP.Outside.L_meta_32058_aux.Encoding


namespace PEqualNP.Outside.L_meta_32058_aux.Lower
open PEqualNP.Outside.L_meta_32058_aux PEqualNP.Outside.L_meta_32058_aux.Upper PEqualNP.Outside.L_meta_32058_aux.Model PEqualNP.Outside.L_meta_32058_aux.Chart PEqualNP.Outside.L_meta_32058_aux.Cycle PEqualNP.Outside.L_meta_32058_aux.Cyclic

theorem hist_follow {k : Nat} (tree : Tree k) (x : W k) :
    hist tree x = follow tree.1.toList
      (fun p => asBool (tree.2.1 p x + tree.2.2.1 p)) tree.1.card [] := by
  simpa [hist,advance,Finset.mem_toList] using
    fold_follow tree.1.toList (fun p => asBool (tree.2.1 p x + tree.2.2.1 p))
      (List.range tree.1.card) []

theorem hist_count {k : Nat} (tree : Tree k) :
    ∃ fs : Finset H, fs.card ≤ tree.1.card+1 ∧ ∀ x : W k, hist tree x ∈ fs := by
  obtain ⟨ls,size,cov⟩ := exact_leaf_list tree.1.toList tree.1.card
  refine ⟨ls.toFinset,?_,?_⟩
  · exact (List.toFinset_card_le ls).trans (by simpa using size)
  · intro x
    apply List.mem_toFinset.mpr
    simpa [hist,Finset.mem_toList] using
      cov (fun p=>asBool (tree.2.1 p x + tree.2.2.1 p))

theorem leaf_submodule {k : Nat} (tree : Tree k) (x₀ : W k) :
    ∃ S : Submodule F (W k), ∀ x, hist tree x=hist tree x₀ ↔ x-x₀ ∈ S := by
  let Q (x : W k) (p : H) := asBool (tree.2.1 p x + tree.2.2.1 p)
  obtain ⟨checks,eq⟩ := reachable_leaf_cell tree.1.toList (Q x₀) tree.1.card []
  let S : Submodule F (W k) :=
    { carrier := {v | ∀ z ∈ checks, tree.2.1 z.1 v=0}
      zero_mem' := fun z _=>map_zero _, add_mem' := fun {a b} ha hb z hz=>by rw [map_add,ha z hz,hb z hz,add_zero]
      smul_mem' := fun a b hb z hz=>by rw [map_smul,hb z hz,smul_zero] }
  refine ⟨S,?_⟩
  intro x
  rw [hist_follow,hist_follow]
  change follow tree.1.toList (Q x) tree.1.card [] =
    follow tree.1.toList (Q x₀) tree.1.card [] ↔ _
  rw [eq]
  have ref := (eq (Q x₀)).mp rfl
  change (∀ z ∈ checks,Q x z.1=z.2) ↔ ∀ z ∈ checks,tree.2.1 z.1 (x-x₀)=0
  constructor
  · intro h z hz
    have q : Q x z.1=Q x₀ z.1 := (h z hz).trans (ref z hz).symm
    have f := congrArg asField q
    simp only [Q,asField_asBool] at f
    rw [map_sub,sub_eq_zero]
    exact add_right_cancel f
  · intro h z hz
    have f := h z hz
    rw [map_sub,sub_eq_zero] at f
    change asBool (tree.2.1 z.1 x+tree.2.2.1 z.1)=z.2
    rw [f]
    exact ref z hz

def shiftedLin {k : Nat} (hk : 0 < k) (d s : Nat) : W k →ₗ[F] W k :=
  (reindex (next hk)).comp (ylin hk d s)

theorem shifted_zero {k : Nat} (hk : 0 < k) (d s : Nat) (v : W k)
    (z : shiftedLin hk d s v=0) : ylin hk d s v=0 := by
  funext i
  obtain ⟨j,hj⟩ := Endpoints.next_onto hk i
  have hz := congrFun z j
  change ylin hk d s v (next hk j)=0 at hz
  change ylin hk d s v i=0
  simpa only [hj] using hz

theorem matching_of_large_chart {k : Nat} (hk : 0 < k) (sites J : Finset (Fin k)) (e : Nat)
    (huge : k-(mu hk sites-e+extra hk sites e) < J.card) :
    ∃ E ⊆ sites, independent hk E ∧ e < E.card ∧ ∀ i ∈ E,i ∈ J ∧ next hk i ∈ J := by
  classical
  let c := k-J.card
  have size : J.card ≤ k := by simpa using J.card_le_univ
  have csmall : c < mu hk sites-e+extra hk sites e := by omega
  have main (n : Nat) (hn : e+c < n) (hm : n=mu hk sites) :
      ∃ E ⊆ sites, independent hk E ∧ e < E.card ∧ ∀ i ∈ E,i ∈ J ∧ next hk i ∈ J := by
    obtain ⟨E,es,ind,card⟩ := matching_witness hk sites
    let E' := E.filter (fun i=>i ∈ J ∧ next hk i ∈ J)
    have bound := endpoint_filter hk E J ind
    change E.card ≤ E'.card+c at bound
    refine ⟨E', (Finset.filter_subset _ _).trans es,?_,by omega,?_⟩
    · intro i hi hj
      exact ind i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  by_cases reg : e+c < mu hk sites
  · exact main _ reg rfl
  have ex : extra hk sites e=1 := by
    by_cases e₁ : sites=Finset.univ ∧ 1 < k ∧ k % 2=1 ∧ e < mu hk sites
    · unfold extra
      exact ite_eq_left e₁
    · have e₀ : extra hk sites e=0 := by unfold extra;exact ite_eq_right e₁
      rw [e₀] at csmall
      omega
  have ex' : sites=Finset.univ ∧ 1 < k ∧ k % 2=1 ∧ e < mu hk sites := by
    by_contra h
    unfold extra at ex
    rw [ite_eq_right h] at ex
    contradiction
  have cp : 0 < c := by omega
  have notFull : J ≠ Finset.univ := by
    intro h
    change 0 < k-J.card at cp
    simp [h] at cp
  have miss : ∃ r : Fin k, r ∉ J := by
    by_contra nh
    apply notFull
    ext i
    simp only [Finset.mem_univ,iff_true]
    by_contra n
    exact nh ⟨i,n⟩
  obtain ⟨r,hr⟩ := miss
  obtain ⟨E,ind,inside,paid⟩ := odd_match_inside hk ex'.2.2.1 J hr
  have twice := twice_mu hk sites
  refine ⟨E,by rw [ex'.1];exact Finset.subset_univ _,ind,by omega,inside⟩

/-- A sufficiently large chart would fit the endpoints of e+1 disjoint
    quadratic residuals and contradict the everywhere guarantee. -/
theorem chart_limit {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e : Nat) (tree : Tree k)
    (good : ∀ x, (sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)).card ≤ e)
    (x₀ : W k) (S : Submodule F (W k))
    (cell : ∀ x, hist tree x=hist tree x₀ ↔ x-x₀ ∈ S)
    (J : Finset (Fin k))
    (sur : Function.Surjective (project ((shiftedLin hk d s).comp S.subtype) J)) :
    J.card ≤ k-(mu hk sites-e+extra hk sites e) := by
  classical
  by_contra h
  obtain ⟨E,es,ind,large,ends⟩ := matching_of_large_chart hk sites J e (by omega)
  let M := (shiftedLin hk d s).comp S.subtype
  let q := project M J
  let lift := sectionOf q sur
  let liftW := S.subtype.comp lift
  let initial : J→F := fun j=>yaff hk d s name x₀ (next hk j)
  let x' : W k := x₀ - liftW initial
  let input (w : J→F) : W k := liftW w+x'
  have cell_input (w : J→F) : hist tree (input w)=hist tree x₀ := by
    apply (cell (input w)).mpr
    have e₁ : input w-x₀=liftW w-liftW initial := by
      change liftW w+(x₀-liftW initial)-x₀=liftW w-liftW initial
      simp only [sub_eq_add_neg]
      calc
        _ = (liftW w + -liftW initial) + (x₀ + -x₀) := by ac_rfl
        _ = _ := by simp
    rw [e₁]
    exact S.sub_mem (lift w).2 (lift initial).2
  have get (w : J→F) (j : J) : yaff hk d s name (input w) (next hk j)=w j := by
    have r (w : J→F) : ylin hk d s (liftW w) (next hk j)=w j :=
      congrFun (section_right q sur w) j
    have ea : input w=liftW w+(x₀-liftW initial) := rfl
    unfold yaff
    rw [ea,map_add,map_sub]
    simp only [Pi.add_apply,Pi.sub_apply,r]
    change w j + (ylin hk d s x₀ (next hk j) - initial j) + mix hk d name (next hk j)=w j
    change w j + (ylin hk d s x₀ (next hk j) -
        (ylin hk d s x₀ (next hk j)+mix hk d name (next hk j))) + mix hk d name (next hk j)=w j
    simp only [sub_eq_add_neg,neg_add_rev]
    calc
      _ = w j + (ylin hk d s x₀ (next hk j) + -ylin hk d s x₀ (next hk j)) +
        (mix hk d name (next hk j) + -mix hk d name (next hk j)) := by ac_rfl
      _ = _ := by simp [two_add]
  let p := hist tree x₀
  let aff := tree.2.2.2.1 p
  let cst := tree.2.2.2.2 p
  let L := (aff+base hk d s t).comp liftW
  let b := aff x'+cst+(base hk d s t) x'+bias hk d name constant
  obtain ⟨w,all⟩ := Encoding.joint hk J E ind ends L b
  let bad := sites.filter (fun i=>predict tree (input w) i ≠ output hk d s t name constant (input w) i)
  have eb : E⊆bad := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨es hi,?_⟩
    intro eq
    have hz := two_add (predict tree (input w) i)
    rw [eq] at hz
    have sum : predict tree (input w) i+output hk d s t name constant (input w) i=0 := by
      rw [eq]
      exact hz
    apply all i hi
    unfold output rise predict at sum
    rw [cell_input] at sum
    change (aff (input w) i+cst i) +
      (base hk d s t (input w) i+bias hk d name constant i+
        (1+yaff hk d s name (input w) (next hk i))*yaff hk d s name (input w) (next hk (next hk i)))=0 at sum
    have a := get w ⟨i,(ends i hi).1⟩
    have b' := get w ⟨next hk i,(ends i hi).2⟩
    change yaff hk d s name (input w) (next hk i)=_ at a
    change yaff hk d s name (input w) (next hk (next hk i))=_ at b'
    rw [a,b'] at sum
    unfold input at sum
    rw [map_add,map_add] at sum
    simp only [Pi.add_apply] at sum
    change (aff (liftW w) i+base hk d s t (liftW w) i) +
      (aff x' i+cst i+base hk d s t x' i+bias hk d name constant i) +
      (1+w ⟨i,(ends i hi).1⟩)*w ⟨next hk i,(ends i hi).2⟩=0
    exact (by ac_rfl : _ = (aff (liftW w) i+aff x' i+cst i)+
      (base hk d s t (liftW w) i+base hk d s t x' i+bias hk d name constant i+
        (1+w ⟨i,(ends i hi).1⟩)*w ⟨next hk i,(ends i hi).2⟩)).trans sum
  have small := (Finset.card_le_card eb).trans (good (input w))
  omega

theorem leaf_card {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e : Nat) (tree : Tree k)
    (good : ∀ x, (sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)).card ≤ e)
    (p : H) :
    ((Finset.univ : Finset (W k)).filter (fun x=>hist tree x=p)).card ≤ 
      2^(k-(mu hk sites-e+extra hk sites e)+Kernel.allowance k d) := by
  classical
  let fs := (Finset.univ : Finset (W k)).filter (fun x=>hist tree x=p)
  by_cases hh : fs.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hh
    have hp₀ := (Finset.mem_filter.mp hx₀).2
    obtain ⟨S,cell⟩ := leaf_submodule tree x₀
    let M := (shiftedLin hk d s).comp S.subtype
    obtain ⟨J,sur,sep⟩ := chart M
    have jc := chart_limit hk d s t name constant sites e tree good x₀ S cell J sur
    let fn (x : fs) : (J→F) × (Fin (Kernel.allowance k d)→F) :=
      (fun j=>shiftedLin hk d s x j, sample hk d s x)
    have inj : Function.Injective fn := by
      intro x y eq
      apply Subtype.ext
      have xs : (x:W k)-x₀ ∈ S := (cell x).mp ((Finset.mem_filter.mp x.2).2.trans hp₀.symm)
      have ys : (y:W k)-x₀ ∈ S := (cell y).mp ((Finset.mem_filter.mp y.2).2.trans hp₀.symm)
      have vs : (x:W k)-(y:W k) ∈ S := by
        have e : (x:W k)-(y:W k)=((x:W k)-x₀)-((y:W k)-x₀) :=
          (sub_sub_sub_cancel_right _ _ _).symm
        rw [e]
        exact S.sub_mem xs ys
      let v : S := ⟨(x:W k)-(y:W k),vs⟩
      have jzero (i : Fin k) (hi : i ∈ J) : M v i=0 := by
        change shiftedLin hk d s ((x:W k)-(y:W k)) i=0
        rw [map_sub,Pi.sub_apply,sub_eq_zero]
        exact congrFun (congrArg Prod.fst eq) ⟨i,hi⟩
      have yy : ylin hk d s ((x:W k)-(y:W k))=0 :=
        shifted_zero hk d s _ (sep v jzero)
      have ss : sample hk d s ((x:W k)-(y:W k))=0 := by
        rw [map_sub,sub_eq_zero]
        exact congrArg Prod.snd eq
      exact sub_eq_zero.mp (samples_kernel hk d s _ yy ss)
    have bd := Fintype.card_le_of_injective fn inj
    simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fun,ZMod.card,Fintype.card_fin] at bd
    rw [←Nat.pow_add] at bd
    exact bd.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have ef := Finset.not_nonempty_iff_eq_empty.mp hh
    change fs.card ≤ _
    rw [ef,Finset.card_empty]
    exact Nat.zero_le _

theorem lower {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e : Nat) (L : Nat) (tree : Tree k) (nt : tree.1.card < L)
    (good : ∀ x, (sites.filter (fun i=>predict tree x i ≠ output hk d s t name constant x i)).card ≤ e) :
    2^(mu hk sites-e+extra hk sites e) ≤ 2^(Kernel.allowance k d)*L := by
  classical
  let p := mu hk sites-e+extra hk sites e
  let h := Kernel.allowance k d
  have pk : p ≤ k := by
    have t := twice_mu hk sites
    unfold p extra
    split <;> omega
  obtain ⟨fs,fc,reach⟩ := hist_count tree
  have part := Finset.card_eq_sum_card_fiberwise (s:=(Finset.univ : Finset (W k)))
    (t:=fs) (f:=hist tree) (fun x _=>reach x)
  have sums : (∑ a ∈ fs, ((Finset.univ : Finset (W k)).filter (fun x=>hist tree x=a)).card) ≤ 
      fs.card*2^(k-p+h) := by
    calc
      _ ≤ ∑ _a ∈ fs, 2^(k-p+h) := Finset.sum_le_sum (fun a _=>leaf_card hk d s t name constant sites e tree good a)
      _ = _ := by simp
  rw [Finset.card_univ,Fintype.card_fun,ZMod.card,Fintype.card_fin] at part
  have be := part.le.trans (sums.trans (Nat.mul_le_mul_right _ (by omega : fs.card ≤ L)))
  change 2^k ≤ L*2^(k-p+h) at be
  have kt : 2^k=2^(k-p)*2^p := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have ht : L*2^(k-p+h)=2^(k-p)*(2^h*L) := by
    rw [Nat.pow_add]
    ac_rfl
  rw [kt,ht] at be
  exact Nat.le_of_mul_le_mul_left be (Nat.two_pow_pos _)

end PEqualNP.Outside.L_meta_32058_aux.Lower


namespace PEqualNP.Outside.L_meta_32058_aux.Exact
open PEqualNP.Outside.L_meta_32058_aux.Upper PEqualNP.Outside.L_meta_32058_aux.Lower PEqualNP.Outside.L_meta_32058_aux.Cyclic PEqualNP.Outside.L_meta_32058_aux.Chart PEqualNP.Outside.L_meta_32058_aux.Model

def literalOutput {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k) (i : Fin k) : F :=
  let old := rot hk s x + name
  let y := fun u : Fin k =>
    old u + old (idx k hk (u.val+d)) + old (idx k hk (u.val+k-d % k))
  y i + (1+y (idx k hk (i.val+1)))*y (idx k hk (i.val+2)) + rot hk t x i + constant i

theorem literal {k : Nat} (hk : 0 < k) (d s t : Nat) (name constant x : W k) (i : Fin k) :
    literalOutput hk d s t name constant x i=output hk d s t name constant x i :=
  (out_literal hk d s t name constant x i).symm

theorem literal_mu {k : Nat} (hk : 0 < k) (sites : Finset (Fin k))
    [dec : DecidablePred (fun E : Finset (Fin k) =>
      ∀ i ∈ E, (⟨(i.val+1) % k,Nat.mod_lt _ hk⟩ : Fin k) ∉ E)] :
    (sites.powerset.filter (fun E =>
      ∀ i ∈ E, (⟨(i.val+1) % k,Nat.mod_lt _ hk⟩ : Fin k) ∉ E)).sup Finset.card =
      PEqualNP.Outside.L_meta_32058_aux.Cycle.mu hk sites := by
  unfold PEqualNP.Outside.L_meta_32058_aux.Cycle.mu
  congr 1
  ext E
  simp only [Finset.mem_filter]
  rfl

end PEqualNP.Outside.L_meta_32058_aux.Exact

theorem PEqualNP.Outside.L_meta_32058 :
  ∀ (k : Nat) (hk : 0 < k),
    let F := ZMod 2
    let W := Fin k → F
    let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
    ∀ (spacing s t : Nat) (name constant : W),
      let out := fun (raw : W) (site : Fin k) =>
        let old := rot s raw + name
        let y := fun u : Fin k =>
          old u + old (ix (u.val+spacing)) + old (ix (u.val+k-spacing % k))
        y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
      let H := List Bool
      let Tree := Finset H × (H → W →ₗ[F] F) × (H → F) × (H → W →ₗ[F] W) × (H → W)
      let predict : Tree → W → W := fun tree raw =>
        let nodes := tree.1
        let ask := tree.2.1
        let bias := tree.2.2.1
        let aff := tree.2.2.2.1
        let c := tree.2.2.2.2
        let leaf := (List.range nodes.card).foldl (fun (p : H) _ =>
          if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []
        aff leaf raw + c leaf
      let g := Nat.gcd k spacing
      let h := if 3 ∣ k/g then 2*g else 0
      ∀ (sites : Finset (Fin k)) (e : Nat),
        let mu := (sites.powerset.filter (fun E => ∀ i ∈ E, ix (i.val+1) ∉ E)).sup Finset.card
        let extra := if sites = Finset.univ ∧ 1 < k ∧ k % 2 = 1 ∧ e < mu then 1 else 0
        let price := 2^(mu-e+extra)
        let feasible := fun L : Nat =>
          ∃ tree : Tree, tree.1.card < L ∧ ∀ x : W,
            (sites.filter (fun i => predict tree x i ≠ out x i)).card ≤ e
        feasible price ∧ ∀ L : Nat, feasible L → price ≤ 2^h*L
 := by
  classical
  intro k hk
  dsimp only
  intro spacing s t name constant sites e
  simp only [@PEqualNP.Outside.L_meta_32058_aux.Exact.literal_mu k hk sites]
  change
    (∃ tree : PEqualNP.Outside.L_meta_32058_aux.Upper.Tree k,
      tree.1.card < 2^(PEqualNP.Outside.L_meta_32058_aux.Cycle.mu hk sites-e+PEqualNP.Outside.L_meta_32058_aux.Upper.extra hk sites e) ∧
      ∀ x : PEqualNP.Outside.L_meta_32058_aux.Model.W k,
        (sites.filter (fun i =>
          PEqualNP.Outside.L_meta_32058_aux.Upper.predict tree x i ≠ PEqualNP.Outside.L_meta_32058_aux.Exact.literalOutput hk spacing s t name constant x i)).card ≤ e) ∧
    ∀ L : Nat, (∃ tree : PEqualNP.Outside.L_meta_32058_aux.Upper.Tree k, tree.1.card<L ∧
      ∀ x : PEqualNP.Outside.L_meta_32058_aux.Model.W k,
        (sites.filter (fun i =>
          PEqualNP.Outside.L_meta_32058_aux.Upper.predict tree x i ≠ PEqualNP.Outside.L_meta_32058_aux.Exact.literalOutput hk spacing s t name constant x i)).card ≤ e) →
      2^(PEqualNP.Outside.L_meta_32058_aux.Cycle.mu hk sites-e+PEqualNP.Outside.L_meta_32058_aux.Upper.extra hk sites e) ≤
        2^(PEqualNP.Outside.L_meta_32058_aux.Kernel.allowance k spacing)*L
  simp only [PEqualNP.Outside.L_meta_32058_aux.Exact.literal]
  refine ⟨PEqualNP.Outside.L_meta_32058_aux.Upper.upper hk spacing s t name constant sites e,?_⟩
  rintro L ⟨tree,ht,he⟩
  exact PEqualNP.Outside.L_meta_32058_aux.Lower.lower hk spacing s t name constant sites e L tree ht he
