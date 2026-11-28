import PEqualNP.Defs

open scoped BigOperators

/- Independent affine-chart and binary-circuit proof architecture. -/

/- Source segment: AffinePivot. -/


namespace PEqualNP.Outside.L_meta_32580.AffinePivot

                                                                     
                                                                       
structure Form (Y : Type) where
  coeff : Nat  →  Bool
  offset : Y  →  Bool

def parity (f : Nat → Bool) : List Nat → Bool
  | [] => false
  | a::as => f a ^^ parity f as

theorem parity_perm {u v : List Nat} (h : u.Perm v) (f : Nat → Bool) :
    parity f u=parity f v := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [parity,ih]
  | swap a b r => simp [parity,Bool.xor_left_comm]
  | trans _ _ a b => exact a.trans b

theorem parity_congr {u : List Nat} {f g : Nat → Bool}
    (h : ∀ i∈u,f i=g i) : parity f u=parity g u := by
  induction u with
  | nil => rfl
  | cons a as ih =>
    simp only [parity,h a List.mem_cons_self,ih (fun i hi=>h i (List.mem_cons_of_mem _ hi))]

theorem parity_xor (f g : Nat → Bool) (u : List Nat) :
    parity (fun j=>f j ^^ g j) u=(parity f u ^^ parity g u) := by
  induction u with
  | nil => rfl
  | cons a t ih =>
    simp only [parity,ih]
    cases f a <;> cases g a <;> cases parity f t <;> cases parity g t <;> decide

theorem parity_scale (f : Nat → Bool) (b : Bool) (u : List Nat) :
    parity (fun j=>b && f j) u=(b && parity f u) := by
  induction u with
  | nil => cases b <;> rfl
  | cons a t ih => simp [parity,ih,Bool.and_xor_distrib_left]

def linear {Y : Type} (a : Form Y) (d : List Nat) (x : Nat → Bool) : Bool :=
  parity (fun j=>a.coeff j && x j) d

def value {Y : Type} (a : Form Y) (d : List Nat) (x : Nat → Bool) (y : Y) : Bool :=
  linear a d x ^^ a.offset y

def branch {Y : Type} (a : Form Y) (d : List Nat) (k : Nat) (want : Bool) (x : Nat → Bool) (y : Y) :
    Nat → Bool :=
  fun j=>if j=k then want ^^ linear a (d.erase k) x ^^ a.offset y else x j

def pull {Y : Type} (pivot a : Form Y) (k : Nat) (want : Bool) : Form Y :=
  ⟨fun j=>a.coeff j ^^ (a.coeff k && pivot.coeff j),
   fun y=>a.offset y ^^ (a.coeff k && (want ^^ pivot.offset y))⟩

theorem pull_coeff_independent {Y : Type} (a b p q : Form Y) (k : Nat) (e : Bool)
    (sameA : a.coeff=b.coeff) (samePivot : p.coeff=q.coeff) :
    (pull p a k e).coeff=(pull q b k e).coeff := by
  simp [pull,sameA,samePivot]

theorem erase_avoids {d : List Nat} {k : Nat} (nd : d.Nodup) (h : k∈d) :
    k∉d.erase k :=
  (List.nodup_cons.mp ((List.perm_cons_erase h).nodup_iff.mp nd)).1

theorem linear_split {Y : Type} (a : Form Y) {d : List Nat} {k : Nat} (hk : k∈d) (x : Nat → Bool) :
    linear a d x=((a.coeff k && x k) ^^ linear a (d.erase k) x) := by
  exact (parity_perm (List.perm_cons_erase hk) _)

theorem branch_else {Y : Type} (a : Form Y) (d : List Nat) (k : Nat) (want : Bool) (x : Nat → Bool) (y : Y)
    {j : Nat} (h : j≠k) : branch a d k want x y j=x j := by simp [branch,h]

theorem linear_branch_keep {Y : Type} (pivot a : Form Y) {d : List Nat} {k : Nat}
    (nd : d.Nodup) (hp : k∈d) (want : Bool) (x : Nat → Bool) (y : Y) :
    linear a (d.erase k) (branch pivot d k want x y)=linear a (d.erase k) x := by
  apply parity_congr
  intro i hi
  have ne : i≠k := fun e=>erase_avoids nd hp (e ▸ hi)
  rw [branch_else pivot d k want x y ne]

theorem linear_pull {Y : Type} (p a : Form Y) (k : Nat) (e : Bool) (d : List Nat) (x : Nat → Bool) :
    linear (pull p a k e) d x=(linear a d x ^^ (a.coeff k && linear p d x)) := by
  unfold linear
  have pt (j : Nat) : ((pull p a k e).coeff j && x j) =
      ((a.coeff j && x j) ^^ (a.coeff k && (p.coeff j && x j))) := by
    simp [pull,Bool.and_xor_distrib_right,Bool.and_assoc]
  have pointwise := parity_congr (u:=d) (fun j _=>pt j)
  rw [pointwise,parity_xor,parity_scale]

                                                                          
                                                                             
theorem substitution {Y : Type} (p a : Form Y) {d : List Nat} {k : Nat}
    (nd : d.Nodup) (hp : k∈d) (want : Bool) (x : Nat → Bool) (y : Y) :
    value a d (branch p d k want x y) y=value (pull p a k want) (d.erase k) x y := by
  unfold value
  rw [linear_split a hp,linear_branch_keep p a nd hp,linear_pull]
  simp only [branch,ite_true,pull]
  cases a.coeff k <;> cases want <;> cases linear p (d.erase k) x <;>
    cases linear a (d.erase k) x <;> cases p.offset y <;> cases a.offset y <;> decide

theorem pivot_satisfied {Y : Type} (p : Form Y) {d : List Nat} {k : Nat}
    (nd : d.Nodup) (hp : k∈d) (active : p.coeff k=true)
    (want : Bool) (x : Nat → Bool) (y : Y) :
    value p d (branch p d k want x y) y=want := by
  rw [substitution p p nd hp]
  unfold value
  rw [linear_pull]
  simp only [active,Bool.true_and,Bool.xor_self,pull,Bool.false_xor]
  cases want <;> cases p.offset y <;> decide

                                                                          
                                                                          
                                                            
theorem branch_reconstruct {Y : Type} (p : Form Y) {d : List Nat} {k : Nat}
    (hp : k∈d) (active : p.coeff k=true) (x : Nat → Bool) (y : Y) :
    branch p d k (value p d x y) x y=x := by
  funext j
  by_cases eq : j=k
  · subst j
    simp only [branch,if_pos rfl,value,linear_split p hp,active,Bool.true_and]
    cases x k <;> cases linear p (d.erase k) x <;> cases p.offset y <;> decide
  · exact branch_else p d k _ x y eq

def scale {Y : Type} (b : Bool) (a : Form Y) : Form Y :=
  ⟨fun j=>b && a.coeff j,fun y=>b && a.offset y⟩

theorem scale_value {Y : Type} (b : Bool) (a : Form Y) (d : List Nat) (x : Nat → Bool) (y : Y) :
    value (scale b a) d x y=(b && value a d x y) := by
  simp only [value,linear,scale,Bool.and_assoc,parity_scale,Bool.and_xor_distrib_left]

                                                                        
                                                                    
                          
theorem product_after_cut {Y : Type} (p a : Form Y) {d : List Nat} {k : Nat}
    (nd : d.Nodup) (hp : k∈d) (active : p.coeff k=true)
    (want : Bool) (x : Nat → Bool) (y : Y) :
    (value p d (branch p d k want x y) y && value a d (branch p d k want x y) y)=
      value (scale want (pull p a k want)) (d.erase k) x y := by
  rw [pivot_satisfied p nd hp active,substitution p a nd hp,scale_value]

end PEqualNP.Outside.L_meta_32580.AffinePivot

/- Source segment: CubePivot. -/


namespace PEqualNP.Outside.L_meta_32580.CubePivot
open PEqualNP.Outside.L_meta_32580.AffinePivot
abbrev Assign := Nat → Bool

def put (x : Assign) (i : Nat) (b : Bool) : Assign :=
  fun j=>if j=i then b else x j

def two (i : Nat) (x : Assign) : List Assign := [put x i false,put x i true]

def cube : List Nat → List Assign
  | [] => [fun _=>false]
  | k::ds => (cube ds).flatMap (two k)

theorem put_comm (x : Assign) {a b : Nat} (ne : a≠b) (v w : Bool) :
    put (put x a v) b w=put (put x b w) a v := by
  funext j
  by_cases h : j=a
  · subst j
    simp [put,ne]
  · by_cases k : j=b
    · simp [put,h,k,Ne.symm ne]
    · simp [put,h,k,Ne.symm ne]

theorem local_subst {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a∈l,(f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact .nil
  | cons a t ih =>
    exact (h a List.mem_cons_self).append (ih (fun x hx=>h x (List.mem_cons_of_mem _ hx)))

theorem two_swap {a b : Nat} (ne : a≠b) (x : Assign) :
    ((two a x).flatMap (two b)).Perm ((two b x).flatMap (two a)) := by
  change [put (put x a false) b false,put (put x a false) b true,
     put (put x a true) b false,put (put x a true) b true].Perm
    [put (put x b false) a false,put (put x b false) a true,
     put (put x b true) a false,put (put x b true) a true]
  simp only [put_comm x ne]
  exact .cons _ (.swap _ _ _)

theorem pivot_free {d : List Nat} {k : Nat} (h : k∈d) :
    (cube d).Perm ((cube (d.erase k)).flatMap (two k)) := by
  induction d with
  | nil => simp at h
  | cons a t ih =>
    by_cases e : a=k
    · subst a
      rw [List.erase_cons_head]
      rfl
    · rw [List.erase_cons_tail (by simpa [beq_iff_eq,Ne.symm e])]
      have ht : k∈t := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      have step := (ih ht).flatMap_right (two a)
      change (cube (a::t)).Perm (((cube (t.erase k)).flatMap (two a)).flatMap (two k))
      apply step.trans
      simp only [List.flatMap_assoc]
      exact local_subst _ _ _ (fun x _=>two_swap (Ne.symm e) x)

theorem branch_pair {Y : Type} (p : Form Y) (d : List Nat) (k : Nat) (x : Assign) (y : Y) :
    ([branch p d k false x y,branch p d k true x y] : List Assign).Perm (two k x) := by
  change [put x k ((false ^^ linear p (d.erase k) x) ^^ p.offset y),
    put x k ((true ^^ linear p (d.erase k) x) ^^ p.offset y)].Perm [put x k false,put x k true]
  cases v : linear p (d.erase k) x <;> cases o : p.offset y <;>
  first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _

theorem branch_partition {Y : Type} (p : Form Y) {d : List Nat} {k : Nat} (hk : k∈d) (y : Y) :
    (cube d).Perm ((cube (d.erase k)).flatMap
      (fun x=>[branch p d k false x y,branch p d k true x y])) :=
  (pivot_free hk).trans (local_subst _ _ _ (fun x _=>(branch_pair p d k x y).symm))

theorem pair_count {α β : Type} (P : β → Bool) (u v : α → β) (l : List α) :
    (l.flatMap (fun x=>[u x,v x])).countP P =
      l.countP (fun x=>P (u x))+l.countP (fun x=>P (v x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp [List.flatMap_cons,List.countP_append,ih,List.countP_cons]
    omega

theorem count_cut {Y : Type} (p : Form Y) {d : List Nat} {k : Nat} (h : k∈d) (y : Y)
    (f : Assign → Bool) :
    (cube d).countP f=(cube (d.erase k)).countP (fun x=>f (branch p d k false x y))+
      (cube (d.erase k)).countP (fun x=>f (branch p d k true x y)) := by
  rw [(branch_partition p h y).countP_eq f]
  exact pair_count _ _ _ _

theorem cube_size (d : List Nat) : (cube d).length=2^d.length := by
  have two_length (l : List Assign) (k : Nat) : ((l.flatMap (two k))).length=2*l.length := by
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp [List.flatMap_cons,List.length_append,List.length_cons,two,ih]
      omega
  induction d with
  | nil => rfl
  | cons k t ih =>
    simp only [cube,List.length_cons,two_length,ih,Nat.pow_succ]
    omega

end PEqualNP.Outside.L_meta_32580.CubePivot

/- Source segment: Translation. -/


namespace PEqualNP.Outside.L_meta_32580.Translation
open PEqualNP.Outside.L_meta_32580.CubePivot

def shift (a x : Assign) : Assign := fun j=>a j ^^ x j
def supported (d : List Nat) (a : Assign) : Prop := ∀ j,j∉d → a j=false

theorem shift_put (a x : Assign) (k : Nat) (b : Bool) :
    shift a (put x k b)=put (shift (put a k false) x) k (a k ^^ b) := by
  funext j
  by_cases e : j=k
  · subst j
    simp [shift,put]
  · simp [shift,put,e]

theorem shift_two (a x : Assign) (k : Nat) :
    ((two k x).map (shift a)).Perm (two k (shift (put a k false) x)) := by
  simp only [two,List.map_cons,List.map_nil,shift_put]
  cases p : a k
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ _

theorem cube_shift {d : List Nat} {a : Assign} (sp : supported d a) :
    ((cube d).map (shift a)).Perm (cube d) := by
  induction d generalizing a with
  | nil =>
    have a0 : a=(fun _=>false) := funext (fun j=>sp j (by simp))
    subst a
    rfl
  | cons k t ih =>
    have next : supported t (put a k false) := by
      intro j hj
      by_cases kJ : j=k
      · simp [put,kJ]
      · have out : j∉k::t := fun h=> (List.mem_cons.mp h).elim kJ hj
        simp [put,kJ,sp j out]
    have inside :
        ((cube t).flatMap (fun x=>(two k x).map (shift a))).Perm
          ((cube t).flatMap (fun x=>two k (shift (put a k false) x))) :=
      local_subst _ _ _ (fun x _=>shift_two a x k)
    simp only [cube,List.map_flatMap]
    exact inside.trans (by
      rw [←List.flatMap_map]
      exact (ih next).flatMap_right _)

theorem count_shift {d : List Nat} {a : Assign} (sp : supported d a) (f : Assign → Bool) :
    (cube d).countP (fun x=>f (shift a x))=(cube d).countP f := by
  simpa only [List.countP_map,Function.comp_def] using (cube_shift sp).countP_eq f

theorem count_complement {α : Type} (l : List α) (f : α → Bool) :
    l.countP f+l.countP (fun x=>!(f x))=l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x <;> simp [List.countP_cons,h] <;> omega

                                                                         
                                                                           
theorem exactly_half {d : List Nat} {a : Assign} (sp : supported d a) (f : Assign → Bool)
    (opposite : ∀ x,f (shift a x)= !(f x)) :
    2*(cube d).countP f=(cube d).length := by
  have equal := count_shift sp f
  have equalPred : (fun x=>f (shift a x))=(fun x=>!(f x)) := funext opposite
  rw [equalPred] at equal
  have total := count_complement (cube d) f
  omega

theorem count_four {α : Type} (l : List α) (f g h k : α → Bool)
    (odd : ∀ x, (((f x ^^ g x) ^^ h x) ^^ k x)=true) :
    l.length ≤ l.countP f+l.countP g+l.countP h+l.countP k := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons i t ih =>
    have u := odd i
    simp only [List.length_cons,List.countP_cons]
    cases a : f i <;> cases b : g i <;> cases c : h i <;> cases d : k i <;>
      simp [a,b,c,d] at u ⊢ <;> omega

                                                                        
                                                                            
                                                                      
theorem at_least_quarter {d : List Nat} {a b : Assign}
    (sa : supported d a) (sb : supported d b) (f : Assign → Bool)
    (odd : ∀ x, (((f x ^^ f (shift a x)) ^^ f (shift b x)) ^^ f (shift a (shift b x)))=true) :
    (cube d).length ≤ 4*(cube d).countP f := by
  have n := count_four (cube d) f (fun x=>f (shift a x)) (fun x=>f (shift b x))
    (fun x=>f (shift a (shift b x))) odd
  rw [count_shift sa f,count_shift sb f,count_shift sb (fun x=>f (shift a x))] at n
  rw [count_shift sa f] at n
  omega

end PEqualNP.Outside.L_meta_32580.Translation

/- Source segment: CubeGeometry. -/


namespace PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.Translation

theorem mem_cube {d : List Nat} {a : Assign} : a ∈ cube d ↔ supported d a := by
  induction d generalizing a with
  | nil =>
    constructor
    · intro hi
      have ee : a=(fun _=>false) := by simpa [cube] using hi
      rw [ee]
      intro j _
      rfl
    · intro ha
      have eq : a=(fun _=>false) := funext (fun j=>ha j (by simp))
      simp [cube,eq]
  | cons k t ih =>
    constructor
    · intro hi j hj
      obtain ⟨u,hu,hu'⟩ := List.mem_flatMap.mp hi
      have n1 : j≠k := fun z=>hj (z ▸ List.mem_cons_self)
      have n2 : j∉t := fun z=>hj (List.mem_cons_of_mem _ z)
      rcases (show a=put u k false ∨ a=put u k true by simpa [two] using hu') with rfl|rfl <;>
        simpa [put,n1] using ih.mp hu j n2
    · intro ha
      let u := put a k false
      have hu : supported t u := by
        intro j hj
        by_cases h : j=k
        · simp [u,put,h]
        · have hn : j∉k::t := fun pp=>(List.mem_cons.mp pp).elim h hj
          simp [u,put,h,ha j hn]
      have eq : put u k (a k)=a := by
        funext j
        by_cases h : j=k <;> simp [u,put,h]
      apply List.mem_flatMap.mpr
      refine ⟨u,ih.mpr hu,?_⟩
      rw [←eq]
      cases a k <;> simp [two]

theorem put_false_recover {d : List Nat} {k : Nat} {a : Assign} (hx : a∈cube d) (hk : k∉d)
    (v : Bool) : put (put a k v) k false = a := by
  have ha := mem_cube.mp hx k hk
  funext j
  by_cases h : j=k
  · subst j
    simp [put,ha]
  · simp [put,h]

theorem cube_nodup {d : List Nat} (nd : d.Nodup) : (cube d).Nodup := by
  induction d with
  | nil => simp [cube]
  | cons k t ih =>
    obtain ⟨nk,nt⟩ := List.nodup_cons.mp nd
    change ((cube t).flatMap (two k)).Pairwise (· ≠ ·)
    rw [List.pairwise_flatMap]
    constructor
    · intro x _
      have neq : put x k false≠put x k true := by
        intro e
        have ce := congrFun e k
        simp [put] at ce
      simp [two,neq]
    · have h0 := List.nodup_iff_pairwise_ne.mp (ih nt)
      refine h0.imp_of_mem ?_
      intro a b ha hb neq va hva vb hvb e
      have flipA : put va k false = a := by
        rcases (show va=put a k false ∨ va=put a k true by simpa [two] using hva) with rfl|rfl
        all_goals exact put_false_recover ha nk _
      have flipB : put vb k false = b := by
        rcases (show vb=put b k false ∨ vb=put b k true by simpa [two] using hvb) with rfl|rfl
        all_goals exact put_false_recover hb nk _
      exact neq (flipA.symm.trans ((congrArg (fun t=>put t k false) e).trans flipB))

theorem maps_perm {α β γ : Type} [BEq β] [LawfulBEq β]
    (l : List α) (orig : α → β) (ls : List γ) (walk : γ → List β)
    (transport : ∀ f : β → Bool, l.countP (fun x=>f (orig x))=(ls.map (fun c=>(walk c).countP f)).sum) :
    (l.map orig).Perm (ls.flatMap walk) := by
  apply List.perm_iff_count.mpr
  intro y
  simp only [List.count_eq_countP,List.countP_map,List.countP_flatMap,Function.comp_def]
  exact transport (fun x=>x == y)

theorem each_sub {α β : Type} (l : List α) (walk : α → List β) {a : α} (h : a∈l) :
    List.Sublist (walk a) (l.flatMap walk) := by
  induction l with
  | nil => simp at h
  | cons c ls ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl|h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

theorem nodup_map_from {α β : Type} (l : List α) (nd : l.Nodup) (f : α → β)
    (h : ∀ a∈l,∀ b∈l,f a=f b → a=b) : (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp nd).imp_of_mem
    (fun {a b} ha hb neq e=>neq (h a ha b hb e))

theorem map_inj_of_nodup {α β : Type} {l : List α} {f : α → β} (nd : (l.map f).Nodup) :
    ∀ a∈l,∀ b∈l,f a=f b → a=b := by
  induction l with
  | nil => simp
  | cons c t ih =>
    intro a ha b hb same
    have nd' := List.nodup_cons.mp (show (f c::t.map f).Nodup from nd)
    rcases List.mem_cons.mp ha with h1|ha <;> rcases List.mem_cons.mp hb with h2|hb
    · exact h1.trans h2.symm
    · have e : f c=f b := (congrArg f h1).symm.trans same
      exact False.elim (nd'.1 (e.symm ▸ List.mem_map_of_mem hb))
    · have e : f a=f c := same.trans (congrArg f h2)
      exact False.elim (nd'.1 (e ▸ List.mem_map_of_mem ha))
    · exact ih nd'.2 a ha b hb same

                                                                       
                                                                      
                                                                    
theorem chart_injective {α β γ δ : Type} [BEq β] [LawfulBEq β]
    (l : List α) (nd : l.Nodup) (orig : α → β) (ls : List γ) (dom : γ → List δ)
    (localMap : γ → δ → β)
    (separates : ∀ a∈l,∀ b∈l,orig a=orig b → a=b)
    (transport : ∀ f : β → Bool, l.countP (fun x=>f (orig x))=
      (ls.map (fun c=>(dom c).countP (fun x=>f (localMap c x)))).sum)
    {c : γ} (hc : c∈ls) :
    ∀ a∈dom c, ∀ b∈dom c, localMap c a=localMap c b → a=b := by
  have p := maps_perm l orig ls (fun c=>(dom c).map (localMap c)) (by
    simpa only [List.countP_map,Function.comp_def] using transport)
  have allnd := (nodup_map_from l nd orig separates).perm p
  have inside := List.Nodup.sublist (each_sub ls _ hc) allnd
  exact map_inj_of_nodup inside

end PEqualNP.Outside.L_meta_32580.CubeGeometry

/- Source segment: ZMod2Bridge. -/


namespace PEqualNP.Outside.L_meta_32580.ZMod2Bridge
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry PEqualNP.Outside.L_meta_32580.Translation

abbrev F := ZMod 2

def toBit (x : F) : Bool := decide (x=1)
def ofBit (x : Bool) : F := if x then 1 else 0

theorem cases_F (x : F) : x=0∨x=1 := by
  have h := ZMod.val_lt x
  cases ha : x.val with
  | zero => exact .inl (ZMod.val_injective 2 (ha.trans ZMod.val_zero.symm))
  | succ k =>
    have kz : k=0 := by omega
    subst k
    have h1 : (1:F).val=1 := by rw [ZMod.val_one_eq_one_mod] <;> decide
    exact .inr (ZMod.val_injective 2 (ha.trans h1.symm))

theorem of_to (x : F) : ofBit (toBit x)=x := by
  rcases cases_F x with rfl|rfl <;> decide

theorem to_of (x : Bool) : toBit (ofBit x)=x := by
  cases x <;> decide

theorem to_add (x y : F) : toBit (x+y)=(toBit x ^^ toBit y) := by
  rcases cases_F x with rfl|rfl <;> rcases cases_F y with rfl|rfl <;> decide

theorem to_mul (x y : F) : toBit (x*y)=(toBit x && toBit y) := by
  rcases cases_F x with rfl|rfl <;> rcases cases_F y with rfl|rfl <;> decide

theorem to_sub (x y : F) : toBit (x-y)=(toBit x ^^ toBit y) := by
  rcases cases_F x with rfl|rfl <;> rcases cases_F y with rfl|rfl <;> decide

def pack {n : Nat} (x : Fin n → F) : Assign :=
  fun j=>if h:j<n then toBit (x ⟨j,h⟩) else false

def unpack {n : Nat} (x : Assign) : Fin n → F := fun j=>ofBit (x j)

theorem pack_mem {n : Nat} (x : Fin n → F) : pack x∈cube (List.range n) := by
  apply mem_cube.mpr
  intro j hj
  have no : ¬ j<n := by simpa only [List.mem_range] using hj
  simp [pack,no]

theorem unpack_pack {n : Nat} (x : Fin n → F) : unpack (pack x)=x := by
  funext j
  simp [unpack,pack,j.isLt,of_to]

theorem pack_unpack {n : Nat} {x : Assign} (hx : x∈cube (List.range n)) :
    pack (unpack (n:=n) x)=x := by
  funext j
  by_cases p : j<n
  · simp [pack,unpack,p,to_of]
  · have e := mem_cube.mp hx j (by simpa only [List.mem_range] using p)
    simp [pack,p,e]

theorem pack_add {n : Nat} (a b : Fin n → F) : pack (a+b)=shift (pack a) (pack b) := by
  funext j
  by_cases p : j<n <;> simp [pack,shift,p,to_add]

theorem pack_sub {n : Nat} (a b : Fin n → F) : pack (a-b)=shift (pack a) (pack b) := by
  funext j
  by_cases p : j<n <;> simp [pack,shift,p,to_sub]

theorem bits_pack {n : Nat} (a : Fin n → F) :
    List.ofFn (fun j : Fin n=>decide (a j=1))= (List.range n).map (pack a) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have h : j<n := by simpa using h2
  simp [pack,h,toBit]

end PEqualNP.Outside.L_meta_32580.ZMod2Bridge

/- Source segment: TapeKernel. -/


namespace PEqualNP.Outside.L_meta_32580.TapeKernel
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot

abbrev Fun (Y : Type) := Y → Bool

inductive Span {Y : Type} (p : List (Fun Y)) : Fun Y → Prop
  | const (b : Bool) : Span p (fun _=>b)
  | generator {f : Fun Y} : f∈p  →  Span p f
  | plus {f g : Fun Y} : Span p f  →  Span p g  →  Span p (fun y=>f y ^^ g y)

theorem Span.weaken {Y : Type} {p q : List (Fun Y)} {f : Fun Y} (a : Span p f)
    (h : ∀ x∈p,x∈q) : Span q f := by
  induction a with
  | const b => exact .const b
  | generator m => exact .generator (h _ m)
  | plus _ _ l r => exact .plus l r

theorem Span.scale {Y : Type} {p : List (Fun Y)} {f : Fun Y}
    (a : Span p f) (b : Bool) : Span p (fun y=>b && f y) := by
  cases b
  · exact .const false
  · exact a

inductive ParamProgram {Y : Type} (input : List (Fun Y)) : List (Fun Y) → Nat → Prop
  | initial : ParamProgram input input 0
  | mul {p : List (Fun Y)} {n : Nat} {f g : Fun Y} :
      ParamProgram input p n  →  Span p f  →  Span p g  → 
        ParamProgram input (p++[fun y=>f y&&g y]) (n+1)

def const {Y : Type} (b : Bool) : Form Y := ⟨fun _=>false,fun _=>b⟩
def add {Y : Type} (a b : Form Y) : Form Y :=
  ⟨fun j=>a.coeff j ^^ b.coeff j,fun y=>a.offset y ^^ b.offset y⟩
def pullAll {Y : Type} (p : Form Y) (w : List (Form Y)) (j : Nat) (b : Bool) :=
  w.map (fun a=>pull p a j b)

def Lookup {Y : Type} (w : List (Form Y)) (j : Nat) : Form Y := w[j]?.getD (const false)
def wire {Y : Type} (w : List (Form Y)) (d : List Nat) (x : Assign) (y : Y) : List Bool :=
  w.map (fun a=>value a d x y)

def inSpan {Y : Type} (p : List (Fun Y)) (w : List (Form Y)) : Prop :=
  ∀ a∈w,Span p a.offset

theorem zero_linear {Y : Type} (a : Form Y) (d : List Nat) (x : Assign)
    (h : ∀ j∈d,a.coeff j=false) : linear a d x=false := by
  unfold linear
  rw [parity_congr (f:=fun j=>a.coeff j && x j) (g:=fun _=>false) (fun j hj=>by simp [h j hj])]
  induction d with
  | nil => rfl
  | cons a t ih =>
    rw [parity,Bool.false_xor]
    exact ih (fun j hj=>h j (List.mem_cons_of_mem _ hj))

theorem const_value {Y : Type} (b : Bool) (d : List Nat) (x : Assign) (y : Y) :
    value (const b) d x y=b := by
  have z := zero_linear (const (Y:=Y) b) d x (fun _ _=>rfl)
  unfold value
  rw [z]
  simp only [Bool.false_xor,const]

theorem add_value {Y : Type} (a b : Form Y) (d : List Nat) (x : Assign) (y : Y) :
    value (add a b) d x y=(value a d x y ^^ value b d x y) := by
  unfold value linear
  have pt : parity (fun j=>(add a b).coeff j && x j) d=
      parity (fun j=>(a.coeff j && x j) ^^ (b.coeff j && x j)) d :=
    parity_congr (fun j _=>by simp [add,Bool.and_xor_distrib_right])
  rw [pt,parity_xor]
  simp only [add]
  cases a.offset y <;> cases b.offset y <;> cases parity (fun j=>a.coeff j && x j) d <;>
    cases parity (fun j=>b.coeff j && x j) d <;> decide

theorem lookup_inSpan {Y : Type} {w : List (Form Y)} {p : List (Fun Y)}
    (h : inSpan p w) (j : Nat) : Span p (Lookup w j).offset := by
  unfold Lookup
  cases e : w[j]? with
  | none => exact .const false
  | some a => exact h a (List.mem_of_getElem? e)

theorem lookup_value {Y : Type} (w : List (Form Y)) (j : Nat) (d : List Nat) (x : Assign) (y : Y) :
    value (Lookup w j) d x y=(wire w d x y)[j]?.getD false := by
  simp only [Lookup,wire,List.getElem?_map]
  cases z : w[j]? <;> simp [const_value,z]

theorem wire_pull {Y : Type} (p : Form Y) (w : List (Form Y)) {d : List Nat} {k : Nat}
    (nd : d.Nodup) (hk : k∈d) (b : Bool) (x : Assign) (y : Y) :
    wire (pullAll p w k b) (d.erase k) x y=wire w d (branch p d k b x y) y := by
  unfold wire pullAll
  rw [List.map_map]
  exact List.map_congr_left (fun a _=>(substitution p a nd hk b x y).symm)

theorem span_pull {Y : Type} {P : List (Fun Y)} {p a : Form Y}
    (hp : Span P p.offset) (ha : Span P a.offset) (k : Nat) (b : Bool) :
    Span P (pull p a k b).offset :=
  .plus ha ((Span.plus (.const b) hp).scale (a.coeff k))

theorem span_pullAll {Y : Type} {P : List (Fun Y)} {p : Form Y} {w : List (Form Y)}
    (hp : Span P p.offset) (ha : inSpan P w) (k : Nat) (b : Bool) :
    inSpan P (pullAll p w k b) := by
  intro a hm
  obtain ⟨a,h,rfl⟩ := List.mem_map.mp hm
  exact span_pull hp (ha a h) k b

structure Instruction where
                                                                           
  kind : Bool
  bias : Bool
  reads : List Nat

def Instruction.cost (g : Instruction) : Nat := g.kind.toNat

def read (w : List Bool) (j : Nat) := w[j]?.getD false
def evalParity (w : List Bool) (l : List Nat) := parity (read w) l

def evalInst (g : Instruction) (w : List Bool) : Bool :=
  if g.kind then
    let a := read w (g.reads[0]?.getD 0)
    let b := read w (g.reads[1]?.getD 0)
    (a&&b) ^^ (g.bias&&(a^^b))
  else (g.bias ^^ evalParity w g.reads)

def run (t : List Instruction) (w : List Bool) : List Bool :=
  t.foldl (fun acc g=>acc++[evalInst g acc]) w

def paid (t : List Instruction) : Nat := (t.map Instruction.cost).sum

def linearInstr {Y : Type} (w : List (Form Y)) : List Nat → Form Y
  | [] => const false
  | j::l => add (Lookup w j) (linearInstr w l)

theorem linearInstr_ok {Y : Type} (w : List (Form Y)) (l d : List Nat) (x : Assign) (y : Y) :
    value (linearInstr w l) d x y=evalParity (wire w d x y) l := by
  induction l with
  | nil => simp [linearInstr,const_value,evalParity,parity]
  | cons j l ih => simp [linearInstr,add_value,lookup_value,evalParity,parity,ih,read]

theorem linearInstr_span {Y : Type} {p : List (Fun Y)} {w : List (Form Y)}
    (h : inSpan p w) (l : List Nat) : Span p (linearInstr w l).offset := by
  induction l with
  | nil => exact .const false
  | cons j l ih => exact .plus (lookup_inSpan h j) ih

def finalForm {Y : Type} (anyOr : Bool) (a b product : Form Y) : Form Y :=
  add product (scale anyOr (add a b))

theorem final_value {Y : Type} (op : Bool) (a b product : Form Y) (d : List Nat) (x : Assign) (y : Y) :
    value (finalForm op a b product) d x y=(value product d x y ^^ (op&&(value a d x y ^^ value b d x y))) := by
  rw [finalForm,add_value,scale_value,add_value]

theorem final_span {Y : Type} {p : List (Fun Y)} {a b m : Form Y}
    (ha : Span p a.offset) (hb : Span p b.offset) (hm : Span p m.offset) (op : Bool) :
    Span p (finalForm op a b m).offset :=
  .plus hm ((Span.plus ha hb).scale op)

theorem extend_span {Y : Type} {p : List (Fun Y)} {w : List (Form Y)} {f : Form Y}
    (h : inSpan p w) (k : Span p f.offset) : inSpan p (w++[f]) := by
  intro a m
  rcases List.mem_append.mp m with left|right
  · exact h a left
  · exact (List.eq_of_mem_singleton right).symm ▸ k

theorem wire_extend {Y : Type} (w : List (Form Y)) (a : Form Y) (d : List Nat)
    (x : Assign) (y : Y) : wire (w++[a]) d x y=wire w d x y++[value a d x y] := by
  simp [wire,List.map_append]

end PEqualNP.Outside.L_meta_32580.TapeKernel

/- Source segment: Flatten. -/


namespace PEqualNP.Outside.L_meta_32580.Flatten
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.TapeKernel

structure State (Y : Type) where
  domain : List Nat
  forms : List (Form Y)
  pool : List (Fun Y)
  cost : Nat

def count {Y : Type} (L : List (State Y)) (y : Y) (test : List Bool → Bool) : Nat :=
  (L.map (fun s=>(cube s.domain).countP (fun x=>test (wire s.forms s.domain x y)))).sum

def Good {Y : Type} (B : List (Fun Y)) (s t : State Y) (g : List Instruction) : Prop :=
  t.domain.length ≤ s.domain.length ∧ s.cost ≤ t.cost ∧
  s.domain.length-t.domain.length+(t.cost-s.cost) ≤ paid g ∧
  t.forms.length=s.forms.length+g.length ∧ t.domain.Nodup ∧
  ParamProgram B t.pool t.cost ∧ inSpan t.pool t.forms

def yesAt {Y : Type} (a : Form Y) (d : List Nat) : Prop := ∃ j∈d,a.coeff j=true

theorem noSlope {Y : Type} {a : Form Y} {d : List Nat} (h : ¬ yesAt a d) :
    ∀ j∈d,a.coeff j=false := by
  intro j hj
  exact Bool.eq_false_iff.mpr (fun t=>h ⟨j,hj,t⟩)

def readsA (g : Instruction) := g.reads[0]?.getD 0
def readsB (g : Instruction) := g.reads[1]?.getD 0

def freeInst {Y : Type} (g : Instruction) (s : State Y) : Form Y :=
  add (const g.bias) (linearInstr s.forms g.reads)
def subFree {Y : Type} (g : Instruction) (s : State Y) : State Y :=
  {s with forms := s.forms++[freeInst g s]}

theorem free_shape {Y : Type} (g : Instruction) (s : State Y) (lin : g.kind=false)
    (x : Assign) (y : Y) :
    wire (subFree g s).forms s.domain x y =
      wire s.forms s.domain x y ++ [evalInst g (wire s.forms s.domain x y)] := by
  rw [subFree,wire_extend]
  simp [freeInst,add_value,const_value,linearInstr_ok,evalInst,lin]

def paramProduct {Y : Type} (a b : Form Y) : Form Y :=
  ⟨fun _=>false,fun y=>a.offset y && b.offset y⟩

def subParam {Y : Type} (g : Instruction) (s : State Y) : State Y :=
  let a := Lookup s.forms (readsA g)
  let b := Lookup s.forms (readsB g)
  let f := paramProduct a b
  ⟨s.domain,s.forms++[finalForm g.bias a b f],s.pool++[f.offset],s.cost+1⟩

theorem param_shape {Y : Type} (g : Instruction) (s : State Y) (and_ : g.kind=true)
    (pa : ¬ yesAt (Lookup s.forms (readsA g)) s.domain)
    (pb : ¬ yesAt (Lookup s.forms (readsB g)) s.domain) (x : Assign) (y : Y) :
    wire (subParam g s).forms s.domain x y =
      wire s.forms s.domain x y ++ [evalInst g (wire s.forms s.domain x y)] := by
  let a := Lookup s.forms (readsA g)
  let b := Lookup s.forms (readsB g)
  have za := zero_linear a s.domain x (noSlope pa)
  have zb := zero_linear b s.domain x (noSlope pb)
  have zf := zero_linear (paramProduct a b) s.domain x (fun _ _=>rfl)
  have mul : value (paramProduct a b) s.domain x y =
      (value a s.domain x y && value b s.domain x y) := by
    unfold value
    rw [za,zb,zf]
    simp [paramProduct]
  rw [subParam,wire_extend,final_value,mul]
  simp [a,b,lookup_value,evalInst,and_,readsA,readsB,TapeKernel.read]

theorem param_ok {Y : Type} (g : Instruction) (s : State Y) {B : List (Fun Y)}
    (prior : ParamProgram B s.pool s.cost) (inS : inSpan s.pool s.forms) :
    ParamProgram B (subParam g s).pool (subParam g s).cost ∧
      inSpan (subParam g s).pool (subParam g s).forms := by
  have sa := lookup_inSpan inS (readsA g)
  have sb := lookup_inSpan inS (readsB g)
  refine ⟨ParamProgram.mul prior sa sb,?_⟩
  apply extend_span
  · exact fun f hf=>(inS f hf).weaken (fun a ha=>List.mem_append_left _ ha)
  · exact final_span (m:=paramProduct (Lookup s.forms (readsA g)) (Lookup s.forms (readsB g))) (sa.weaken (fun a ha=>List.mem_append_left _ ha))
      (sb.weaken (fun a ha=>List.mem_append_left _ ha))
      (.generator (List.mem_append_right _ List.mem_cons_self)) _

def chosen {Y : Type} (g : Instruction) (s : State Y) (side : Bool) : Form Y :=
  if side then Lookup s.forms (readsA g) else Lookup s.forms (readsB g)
def other {Y : Type} (g : Instruction) (s : State Y) (side : Bool) : Form Y :=
  chosen g s (!side)

def subCut {Y : Type} (g : Instruction) (s : State Y) (side : Bool) (k : Nat) (b : Bool) : State Y :=
  let p := chosen g s side
  let a := other g s side
  let first := pull p p k b
  let second := pull p a k b
  ⟨s.domain.erase k,(pullAll p s.forms k b)++[finalForm g.bias first second (scale b second)],s.pool,s.cost⟩

theorem cut_ok {Y : Type} (g : Instruction) (s : State Y) (side : Bool) (k : Nat) (b : Bool)
    (h : inSpan s.pool s.forms) : inSpan s.pool (subCut g s side k b).forms := by
  have sp : Span s.pool (chosen g s side).offset := by
    cases side <;> exact lookup_inSpan h _
  have sa : Span s.pool (other g s side).offset := by
    cases side <;> exact lookup_inSpan h _
  have one := span_pull sp sp k b
  have two := span_pull sp sa k b
  exact extend_span (span_pullAll sp h k b) (final_span (m:=scale b (pull (chosen g s side) (other g s side) k b)) one two (two.scale b) g.bias)

theorem cut_shape {Y : Type} (g : Instruction) (s : State Y) (side : Bool)
    (paid_ : g.kind=true) (nd : s.domain.Nodup) {k : Nat} (hk : k∈s.domain)
    (hit : (chosen g s side).coeff k=true) (b : Bool) (x : Assign) (y : Y) :
    wire (subCut g s side k b).forms (s.domain.erase k) x y =
      let w := wire s.forms s.domain (branch (chosen g s side) s.domain k b x y) y
      w++[evalInst g w] := by
  let p := chosen g s side
  let a := other g s side
  let letX := branch p s.domain k b x y
  have v : value (scale b (pull p a k b)) (s.domain.erase k) x y =
      (value p s.domain letX y && value a s.domain letX y) :=
    (product_after_cut p a nd hk hit b x y).symm
  rw [subCut,wire_extend,wire_pull _ _ nd hk,final_value]
  change wire s.forms s.domain letX y ++ [value (scale b (pull p a k b)) (s.domain.erase k) x y ^^
    (g.bias && (value (pull p p k b) (s.domain.erase k) x y ^^ value (pull p a k b) (s.domain.erase k) x y))] = _
  rw [v,←substitution p p nd hk,←substitution p a nd hk]
  cases side <;>
    simp [letX,p,a,chosen,other,evalInst,TapeKernel.read,readsA,readsB,paid_,lookup_value,
      Bool.and_comm,Bool.xor_comm]

theorem lift_free {Y : Type} {g : Instruction} {t : List Instruction} {B : List (Fun Y)}
    {s u : State Y} (aff : g.kind=false) (h : Good B (subFree g s) u t) :
    Good B s u (g::t) := by
  rcases h with ⟨d,q,b,w,n,p,ins⟩
  refine ⟨d,q,?_,?_,n,p,ins⟩
  · simpa [subFree,paid,Instruction.cost,aff] using b
  · simp [subFree] at w
    simp
    omega

theorem lift_param {Y : Type} {g : Instruction} {t : List Instruction} {B : List (Fun Y)}
    {s u : State Y} (mul : g.kind=true) (h : Good B (subParam g s) u t) :
    Good B s u (g::t) := by
  rcases h with ⟨d,q,b,w,n,p,ins⟩
  simp only [subParam] at d q b w
  refine ⟨d,by omega,?_,?_,n,p,ins⟩
  · have hPaid : paid (g::t)=1+paid t := by simp [paid,Instruction.cost,mul]
    rw [hPaid]
    omega
  · simp at w ⊢
    omega

theorem lift_cut {Y : Type} {g : Instruction} {t : List Instruction} {B : List (Fun Y)}
    {s u : State Y} {j : Nat} (side b : Bool) (mul : g.kind=true) (hj : j∈s.domain)
    (h : Good B (subCut g s side j b) u t) :
    Good B s u (g::t) := by
  rcases h with ⟨d,q,budget,w,n,p,ins⟩
  have len := List.length_erase_of_mem hj
  simp only [subCut] at d q budget w
  have pos : 0<s.domain.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hj)
  refine ⟨by omega,q,?_,?_,n,p,ins⟩
  · have hPaid : paid (g::t)=1+paid t := by simp [paid,Instruction.cost,mul]
    rw [hPaid]
    omega
  · simp [pullAll] at w ⊢
    omega

                                                                            
                                                                           
                                                                      
                                               
theorem compile {Y : Type} (B : List (Fun Y)) (t : List Instruction) (s : State Y)
    (nd : s.domain.Nodup) (prog : ParamProgram B s.pool s.cost)
    (span_ : inSpan s.pool s.forms) :
    ∃ L : List (State Y),
      (∀ y test, (cube s.domain).countP (fun x=>test (run t (wire s.forms s.domain x y)))=
          count L y test) ∧ ∀ u∈L,Good B s u t := by
  classical
  induction t generalizing s with
  | nil =>
    refine ⟨[s],by intro y test; simp [run,count],?_⟩
    intro u hu
    have e := List.eq_of_mem_singleton hu
    subst u
    exact ⟨Nat.le_refl _,Nat.le_refl _,by simp [paid],by simp,nd,prog,span_⟩
  | cons g ts ih =>
    cases op : g.kind
    · have sp : inSpan s.pool (subFree g s).forms :=
        extend_span span_ (.plus (.const _) (linearInstr_span span_ _))
      obtain ⟨L,c,a⟩ := ih (subFree g s) nd prog sp
      refine ⟨L,?_ ,fun u hu=>lift_free op (a u hu)⟩
      intro y test
      rw [←c]
      apply congrArg (fun f=>(cube s.domain).countP f)
      funext x
      rw [show (subFree g s).domain=s.domain by rfl,free_shape g s op]
      rfl
    · by_cases hit : ∃ side : Bool,yesAt (chosen g s side) s.domain
      · obtain ⟨side,k,hk,ha⟩ := hit
        have nd0 : (s.domain.erase k).Nodup := nd.erase _
        obtain ⟨L0,c0,a0⟩ := ih (subCut g s side k false) nd0 prog (cut_ok g s side k false span_)
        obtain ⟨L1,c1,a1⟩ := ih (subCut g s side k true) nd0 prog (cut_ok g s side k true span_)
        refine ⟨L0++L1,?_,?_⟩
        · intro y test
          have appendCounts : count (L0++L1) y test=count L0 y test+count L1 y test := by
            simp [count,List.map_append,List.sum_append]
          rw [appendCounts,←c0 y test,←c1 y test,count_cut (chosen g s side) hk y]
          have perCut (b : Bool) :
              (cube (s.domain.erase k)).countP (fun x=>test
                (run (g::ts) (wire s.forms s.domain (branch (chosen g s side) s.domain k b x y) y))) =
              (cube (subCut g s side k b).domain).countP (fun x=>test
                (run ts (wire (subCut g s side k b).forms (subCut g s side k b).domain x y))) := by
            change (cube (s.domain.erase k)).countP _ = (cube (s.domain.erase k)).countP _
            apply congrArg (fun f=>(cube (s.domain.erase k)).countP f)
            funext x
            change _ = test (run ts (wire (subCut g s side k b).forms (s.domain.erase k) x y))
            rw [cut_shape g s side op nd hk ha b x y]
            rfl
          rw [perCut false,perCut true]
        · intro u hu
          rcases List.mem_append.mp hu with z|z
          · exact lift_cut side false op hk (a0 u z)
          · exact lift_cut side true op hk (a1 u z)
      · have na : ¬ yesAt (Lookup s.forms (readsA g)) s.domain :=
          fun h=>hit ⟨true,h⟩
        have nb : ¬ yesAt (Lookup s.forms (readsB g)) s.domain :=
          fun h=>hit ⟨false,h⟩
        obtain ⟨r,sp⟩ := param_ok g s prog span_
        obtain ⟨L,c,a⟩ := ih (subParam g s) nd r sp
        refine ⟨L,?_,fun u hu=>lift_param op (a u hu)⟩
        intro y test
        rw [←c]
        apply congrArg (fun f=>(cube s.domain).countP f)
        funext x
        rw [show (subParam g s).domain=s.domain by rfl,param_shape g s op na nb]
        rfl

end PEqualNP.Outside.L_meta_32580.Flatten

/- Source segment: ParamReify. -/


namespace PEqualNP.Outside.L_meta_32580.ParamReify
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.TapeKernel

def project (w : List Bool) (slots : List Nat) : List Bool :=
  slots.map (TapeKernel.read w)
def samples {Y : Type} (p : List (Fun Y)) (y : Y) : List Bool :=
  p.map (fun f=>f y)

theorem parity_append (f : Nat → Bool) (a b : List Nat) :
    parity f (a++b)=(parity f a ^^ parity f b) := by
  induction a with
  | nil => simp [parity]
  | cons x xs ih => simp [parity,ih,Bool.xor_assoc]

theorem span_address {Y : Type} {P : List (Fun Y)} {f : Fun Y} (h : Span P f) :
    ∃ bias : Bool, ∃ ports : List Nat, (∀ j∈ports,j<P.length) ∧
      ∀ y, f y=(bias ^^ evalParity (samples P y) ports) := by
  induction h with
  | const b => exact ⟨b,[],by simp,fun y=>by simp [evalParity,parity]⟩
  | @generator f mem =>
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
    refine ⟨false,[i],by simp [hi],?_⟩
    intro y
    simp only [evalParity,parity,Bool.xor_false,Bool.false_xor,TapeKernel.read,samples]
    rw [List.getElem?_map,List.getElem?_eq_getElem hi,eq]
    rfl
  | @plus f g a b ia ib =>
    obtain ⟨c,l,hl,el⟩ := ia
    obtain ⟨d,r,hr,er⟩ := ib
    refine ⟨c^^d,l++r,fun j m=>(List.mem_append.mp m).elim (hl j) (hr j),?_⟩
    intro y
    change (f y ^^ g y)=_
    rw [el,er]
    unfold evalParity
    rw [parity_append]
    cases c <;> cases d <;> cases parity (TapeKernel.read (samples P y)) l <;>
      cases parity (TapeKernel.read (samples P y)) r <;> decide

theorem run_append (a b : List Instruction) (w : List Bool) :
    run (a++b) w=run b (run a w) := by simp [run,List.foldl_append]

theorem run_length (t : List Instruction) (w : List Bool) :
    (run t w).length=w.length+t.length := by
  induction t generalizing w with
  | nil => simp [run]
  | cons a t ih =>
    change (run t (w++[evalInst a w])).length=w.length+(a::t).length
    rw [ih]
    simp; omega

theorem identity_project (w : List Bool) : project w (List.range w.length)=w := by
  apply List.ext_getElem (by simp [project])
  intro i hiL hi
  simp only [project,List.getElem_map,List.getElem_range,TapeKernel.read,List.getElem?_eq_getElem hi,Option.getD_some]

theorem read_project (w : List Bool) (loc : List Nat) (j : Nat) (h : j<loc.length) :
    TapeKernel.read (project w loc) j=TapeKernel.read w (loc[j]?.getD 0) := by
  simp only [TapeKernel.read,project,List.getElem?_map,List.getElem?_eq_getElem h,Option.map_some,Option.getD_some]

def address (loc : List Nat) (j : Nat) : Nat := loc[j]?.getD 0

theorem parity_address (w : List Bool) (P : List Bool) (loc ins : List Nat)
    (L : ∀ j∈ins,j<loc.length) (hP : project w loc=P) :
    evalParity w (ins.map (address loc))=evalParity P ins := by
  induction ins with
  | nil => rfl
  | cons j t ih =>
    have h := read_project w loc j (L _ List.mem_cons_self)
    rw [hP] at h
    simp only [List.map_cons,evalParity,parity]
    rw [show TapeKernel.read w (address loc j)=TapeKernel.read P j from h.symm]
    exact congrArg (fun a=>TapeKernel.read P j ^^ a) (ih (fun k m=>L k (List.mem_cons_of_mem _ m)))

theorem project_same_prefix (loc : List Nat) (w t : List Bool) (ok : ∀j∈loc,j<w.length) :
    project (w++t) loc=project w loc := by
  apply List.map_congr_left
  intro j hj
  simp only [TapeKernel.read,List.getElem?_append_left (ok j hj)]

theorem reify {Y : Type} {B P : List (Fun Y)} {cost : Nat} (before : ParamProgram B P cost) :
    ∃ tape : List Instruction, ∃ loc : List Nat,
      paid tape=cost ∧ loc.length=P.length ∧ (∀ j∈loc,j<B.length+tape.length) ∧
      ∀ y,project (run tape (samples B y)) loc=samples P y := by
  induction before with
  | initial =>
    refine ⟨[],List.range B.length,rfl,by simp,?_ ,?_⟩
    · simp
    · intro y
      simpa [samples,run] using identity_project (samples B y)
  | @mul P n f g p fSp gSp ih =>
    obtain ⟨t,loc,hp,hL,range,sem⟩ := ih
    obtain ⟨b,L,hBL,readL⟩ := span_address fSp
    obtain ⟨c,R,hBR,readR⟩ := span_address gSp
    let size := B.length+t.length
    let g0 : Instruction := ⟨false,b,L.map (address loc)⟩
    let g1 : Instruction := ⟨false,c,R.map (address loc)⟩
    let g2 : Instruction := ⟨true,false,[size,size+1]⟩
    let t' := t++[g0,g1,g2]
    refine ⟨t',loc++[size+2],?_,?_,?_,?_⟩
    · unfold paid t'
      simp only [List.map_append,List.sum_append]
      change (t.map Instruction.cost).sum+1=n+1
      rw [←paid,hp]
    · simp [hL]
    · intro z hz
      rcases List.mem_append.mp hz with h|h
      · have original := range z h
        simp [t'] at *
        omega
      · have e := List.eq_of_mem_singleton h
        subst z
        simp [size,t']
        omega
    · intro y
      let w := run t (samples B y)
      have wl : w.length=size := by simp [w,run_length,samples,size]
      have ok : ∀ j∈loc,j<w.length := fun j hj=>wl ▸ range j hj
      have good0 : evalInst g0 w=f y := by
        simp only [evalInst,g0,Bool.false_eq_true,ite_false]
        rw [parity_address w (samples P y) loc L (fun i m=>by rw [hL];exact hBL i m) (sem y)]
        exact (readL y).symm
      have good1 : evalInst g1 (w++[f y])=g y := by
        simp only [evalInst,g1,Bool.false_eq_true,ite_false]
        have psem : project (w++[f y]) loc=samples P y :=
          (project_same_prefix loc w _ ok).trans (sem y)
        rw [parity_address (w++[f y]) (samples P y) loc R (fun i m=>by rw [hL];exact hBR i m) psem]
        exact (readR y).symm
      have aa : TapeKernel.read ((w++[f y])++[g y]) size=f y := by
        unfold TapeKernel.read
        rw [List.getElem?_append_left (by simp [wl]),
          List.getElem?_append_right (by simp [wl])]
        simp [wl]
      have bb : TapeKernel.read ((w++[f y])++[g y]) (size+1)=g y := by
        unfold TapeKernel.read
        rw [List.getElem?_append_right (by simp [wl])]
        simp [wl]
      have good2 : evalInst g2 ((w++[f y])++[g y])=(f y&&g y) := by
        change ((TapeKernel.read ((w++[f y])++[g y]) size && TapeKernel.read ((w++[f y])++[g y]) (size+1)) ^^
          (false && (TapeKernel.read ((w++[f y])++[g y]) size ^^ TapeKernel.read ((w++[f y])++[g y]) (size+1))))=_
        rw [aa,bb]
        simp
      have ext : run t' (samples B y)=w++[f y,g y,f y&&g y] := by
        rw [show t'=t++[g0,g1,g2] by rfl,run_append]
        change ((w++[evalInst g0 w])++[evalInst g1 (w++[evalInst g0 w])])++
          [evalInst g2 ((w++[evalInst g0 w])++[evalInst g1 (w++[evalInst g0 w])])] = _
        rw [good0,good1,good2]
        simp [List.append_assoc]
      rw [ext]
      have p_old : project (w++[f y,g y,f y&&g y]) loc=samples P y :=
        (project_same_prefix loc w _ ok).trans (sem y)
      have last : TapeKernel.read (w++[f y,g y,f y&&g y]) (size+2)=(f y&&g y) := by
        unfold TapeKernel.read
        rw [List.getElem?_append_right (by simp [wl] <;> omega)]
        simp [wl]
      simp only [project,List.map_append,List.map_cons,List.map_nil] at p_old
      simp only [project,List.map_append,List.map_cons,List.map_nil,last,p_old,samples]

end PEqualNP.Outside.L_meta_32580.ParamReify

/- Source segment: TwoPhase. -/


namespace PEqualNP.Outside.L_meta_32580.TwoPhase
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.TapeKernel
open PEqualNP.Outside.L_meta_32580.Flatten PEqualNP.Outside.L_meta_32580.ParamReify

structure View (S : Type) where
  domain : List Nat
  values : List (Form S)

def view {S : Type} (u : State S) (loc : List Nat) : View S :=
  ⟨u.domain,loc.map (Lookup u.forms)⟩

theorem view_correct {S : Type} (u : State S) (loc : List Nat) (x : Assign) (s : S) :
    wire (view u loc).values (view u loc).domain x s=
      project (wire u.forms u.domain x s) loc := by
  simp [view,wire,project,List.map_map,Function.comp_def,lookup_value,TapeKernel.read]

def countView {S : Type} (L : List (View S)) (s : S) (test : List Bool → Bool) : Nat :=
  (L.map (fun u=>(cube u.domain).countP (fun x=>test (wire u.values u.domain x s)))).sum

                                                                          
                                                                          
                                                                    
                                                                       
                                                                        
                                            
theorem residual {Y S : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) (pack : Assign → S → Y)
    (d : List Nat) (nd : d.Nodup) (w : List (Form S))
    (raw : ∀ x s, wire w d x s=samples B (pack x s)) :
    ∃ L : List (View S),
      (∀ s test,(cube d).countP (fun x=>test (samples P (pack x s)))=countView L s test) ∧
      ∀ u∈L,u.domain.Nodup ∧ u.domain.length ≤ d.length ∧ d.length-u.domain.length ≤ q ∧
          u.values.length=P.length := by
  obtain ⟨t,loc,paid_eq,locL,_,sem⟩ := reify prior
  let originals := w.map Form.offset
  let initial : State S := ⟨d,w,originals,0⟩
  have ps : inSpan originals w := fun x hx => .generator (List.mem_map_of_mem hx)
  obtain ⟨L,how,ok⟩ := compile originals t initial nd (.initial) ps
  refine ⟨L.map (fun u=>view u loc),?_,?_⟩
  · intro s test
    have h := how s (fun ws=>test (project ws loc))
    change (cube d).countP (fun x=>test (project (run t (wire w d x s)) loc)) =
      count L s (fun ws=>test (project ws loc)) at h
    have same : (fun x=>test (project (run t (wire w d x s)) loc)) =
        (fun x=>test (samples P (pack x s))) := by
      funext x
      rw [raw x s,sem]
    rw [same] at h
    rw [h]
    unfold count countView
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro u _
    change (cube u.domain).countP (fun x=>test (project (wire u.forms u.domain x s) loc)) =
      (cube u.domain).countP (fun x=>test (wire (view u loc).values (view u loc).domain x s))
    simp only [view_correct]
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    obtain ⟨dim,_,r,_,nd',_,_⟩ := ok v hv
    change d.length-v.domain.length+(v.cost-0) ≤ paid t at r
    have q' : d.length-v.domain.length ≤ q := by
      rw [paid_eq] at r
      omega
    exact ⟨nd',dim,q',by simp [view,locL]⟩

end PEqualNP.Outside.L_meta_32580.TwoPhase

/- Source segment: Polarization. -/


namespace PEqualNP.Outside.L_meta_32580.Polarization
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.Translation

def rectangle (f : Assign → Bool) (u v x : Assign) : Bool :=
  ((f x ^^ f (shift u x)) ^^ f (shift v x)) ^^ f (shift u (shift v x))

theorem linear_shift {Y : Type} (a : Form Y) (d : List Nat) (u x : Assign) :
    linear a d (shift u x)=(linear a d u ^^ linear a d x) := by
  unfold linear
  have rewrite : parity (fun j=>a.coeff j && shift u x j) d=
      parity (fun j=>(a.coeff j && u j) ^^ (a.coeff j && x j)) d :=
    parity_congr (fun j _=>by simp [shift,Bool.and_xor_distrib_left])
  rw [rewrite,parity_xor]

theorem value_shift {Y : Type} (a : Form Y) (d : List Nat) (u x : Assign) (y : Y) :
    value a d (shift u x) y=(linear a d u ^^ value a d x y) := by
  simp only [value,linear_shift,Bool.xor_assoc]

theorem affine_zero_rect {Y : Type} (a : Form Y) (d : List Nat) (u v x : Assign) (y : Y) :
    rectangle (fun x=>value a d x y) u v x=false := by
  unfold rectangle
  simp only [value_shift]
  cases value a d x y <;> cases linear a d u <;> cases linear a d v <;> decide

theorem sign_annihilates {Y : Type} (a : Form Y) (d : List Nat) (u : Assign) (y : Y)
    (s : supported d u) (detect : linear a d u=true) :
    2*(cube d).countP (fun x=>value a d x y)=(cube d).length := by
  apply exactly_half s
  intro x
  rw [value_shift,detect,Bool.true_xor]

def productPolar {Y : Type} (a b : Form Y) (d : List Nat) (u v : Assign) : Bool :=
  (linear a d u && linear b d v) ^^ (linear a d v && linear b d u)

theorem product_rect {Y : Type} (a b : Form Y) (d : List Nat) (u v x : Assign) (y : Y) :
    rectangle (fun t=>value a d t y && value b d t y) u v x=productPolar a b d u v := by
  unfold rectangle productPolar
  simp only [value_shift]
  cases value a d x y <;> cases value b d x y <;> cases linear a d u <;>
    cases linear a d v <;> cases linear b d u <;> cases linear b d v <;> decide

theorem weighted_product_rect {Y : Type} (a b : Form Y) (g : Y → Bool) (d : List Nat)
    (u v x : Assign) (y : Y) :
    rectangle (fun t=>g y && (value a d t y && value b d t y)) u v x=
      (g y && productPolar a b d u v) := by
  cases w : g y
  · simp [rectangle,w]
  · simpa [w] using product_rect a b d u v x y

theorem rectangle_xor (f g : Assign → Bool) (u v x : Assign) :
    rectangle (fun t=>f t ^^ g t) u v x=(rectangle f u v x ^^ rectangle g u v x) := by
  simp only [rectangle]
  cases f x <;> cases f (shift u x) <;> cases f (shift v x) <;>
  cases f (shift u (shift v x)) <;> cases g x <;> cases g (shift u x) <;>
  cases g (shift v x) <;> cases g (shift u (shift v x)) <;> decide

structure Term (Y : Type) where
  coeff : Y → Bool
  a : Form Y
  b : Form Y

def evalTerm {Y : Type} (d : List Nat) (y : Y) (x : Assign) (t : Term Y) : Bool :=
  t.coeff y && (value t.a d x y && value t.b d x y)

def evalQuad {Y : Type} (d : List Nat) (y : Y) (x : Assign) : List (Term Y)  →  Bool
  | [] => false
  | t::ts => evalTerm d y x t ^^ evalQuad d y x ts

def polarTerms {Y : Type} (d : List Nat) (y : Y) (u v : Assign) : List (Term Y)  →  Bool
  | [] => false
  | t::ts => (t.coeff y && productPolar t.a t.b d u v) ^^ polarTerms d y u v ts

theorem rect_quad {Y : Type} (d : List Nat) (y : Y) (u v x : Assign) (ts : List (Term Y)) :
    rectangle (fun t=>evalQuad d y t ts) u v x=polarTerms d y u v ts := by
  induction ts with
  | nil => rfl
  | cons a t ih =>
    simp only [evalQuad,polarTerms,rectangle_xor,ih,evalTerm]
    rw [weighted_product_rect]

                                                                   
                                                                    
theorem quadratic_penalty {Y : Type} (az : Form Y) (d : List Nat) (y : Y) (u v : Assign)
    (ts : List (Term Y)) (su : supported d u) (sv : supported d v)
    (nz : polarTerms d y u v ts=true) :
    (cube d).length  ≤  4*(cube d).countP (fun x=>
      value az d x y ^^ evalQuad d y x ts) := by
  apply at_least_quarter su sv
  intro x
  change rectangle (fun z=>value az d z y ^^ evalQuad d y z ts) u v x=true
  rw [rectangle_xor,affine_zero_rect,rect_quad,nz,Bool.false_xor]

end PEqualNP.Outside.L_meta_32580.Polarization

/- Source segment: ChartGeometry. -/


namespace PEqualNP.Outside.L_meta_32580.ChartGeometry
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.Flatten PEqualNP.Outside.L_meta_32580.Polarization

theorem take_exact {T : Type} (l r : List T) : (l++r).take l.length=l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem run_extension (g : List Instruction) (w : List Bool) : ∃ v,run g w=w++v := by
  induction g generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons a t ih =>
    obtain ⟨r,h⟩ := ih (w++[evalInst a w])
    refine ⟨evalInst a w::r,?_⟩
    change run t (w++[evalInst a w])=w++evalInst a w::r
    rw [h,List.append_assoc]
    rfl

theorem wire_length {Y : Type} (w : List (Form Y)) (d : List Nat) (x : Assign) (y : Y) :
    (wire w d x y).length=w.length := List.length_map _

theorem run_retain {Y : Type} (g : List Instruction) (s : State Y) (x : Assign) (y : Y) :
    (run g (wire s.forms s.domain x y)).take s.forms.length=wire s.forms s.domain x y := by
  obtain ⟨r,h⟩ := run_extension g (wire s.forms s.domain x y)
  rw [h,←wire_length s.forms s.domain x y]
  exact take_exact _ _

theorem take_wire {Y : Type} (n : Nat) (w : List (Form Y)) (d : List Nat) (x : Assign) (y : Y) :
    (wire w d x y).take n=wire (w.take n) d x y := by
  induction w generalizing n with
  | nil => simp [wire]
  | cons h tl ih =>
    cases n
    · rfl
    · change value h d x y :: (wire tl d x y).take _ =
        value h d x y :: wire (tl.take _) d x y
      rw [ih]

                                                                            
                                                                            
theorem chart_inputs {Y : Type} (g : List Instruction) (s : State Y) (l : List (State Y))
    (nd : s.domain.Nodup)
    (counts : ∀ y test,(cube s.domain).countP (fun x=>test (run g (wire s.forms s.domain x y)))=
       count l y test)
    (faithful : ∀ y a, a∈cube s.domain  →  ∀ b,b∈cube s.domain → 
       wire s.forms s.domain a y=wire s.forms s.domain b y → a=b)
    {u : State Y} (hm : u∈l) (y : Y) :
    ∀ a∈cube u.domain, ∀ b∈cube u.domain,
      wire (u.forms.take s.forms.length) u.domain a y=
        wire (u.forms.take s.forms.length) u.domain b y  →  a=b := by
  apply chart_injective (l:=cube s.domain) (cube_nodup nd)
    (orig:=fun x=> wire s.forms s.domain x y) (ls:=l) (dom:=fun z=>cube z.domain)
    (localMap:=fun z x=>wire (z.forms.take s.forms.length) z.domain x y)
  · exact faithful y
  · intro test
    have h := counts y (fun ws=>test (ws.take s.forms.length))
    simpa only [run_retain,count,take_wire] using h
  · exact hm

theorem slope_injective {Y : Type} (w : List (Form Y)) (d : List Nat) (y : Y)
    (faithful : ∀ a∈cube d,∀ b∈cube d,wire w d a y=wire w d b y → a=b) :
    ∀ a∈cube d, ∀ b∈cube d, w.map (fun f=>linear f d a)=w.map (fun f=>linear f d b) → a=b := by
  intro a ha b hb same
  apply faithful a ha b hb
  unfold wire
  have go : ∀ l : List (Form Y), l.map (fun f=>linear f d a)=l.map (fun f=>linear f d b) → 
      l.map (fun f=>value f d a y)=l.map (fun f=>value f d b y) := by
    intro l
    induction l with
    | nil => intro; rfl
    | cons p ps ih =>
      simp only [List.map_cons,List.cons.injEq]
      intro h
      exact ⟨by simp only [value,h.1],ih h.2⟩
  exact go w same

end PEqualNP.Outside.L_meta_32580.ChartGeometry

/- Source segment: ResidualLift. -/


namespace PEqualNP.Outside.L_meta_32580.ResidualLift
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.TapeKernel
open PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.TwoPhase

                                                                         
                                                                          
                                                                         
                                                  
theorem lift {Y S : Type} {P : List (Fun Y)} (observations : List (Fun Y))
    (what : ∀ f∈observations,Span P f) :
    ∃ read : List Bool → List Bool, ∃ affine : List (Form S) → List (Form S),
      (∀ y,read (samples P y)=samples observations y) ∧
      (∀ ws,(affine ws).length=observations.length) ∧
      ∀ d ws x s, wire (affine ws) d x s=read (wire ws d x s) := by
  induction observations with
  | nil => exact ⟨fun _=>[],fun _=>[],fun _=>rfl,fun _=>rfl,fun _ _ _ _=>rfl⟩
  | cons o tail ih =>
    obtain ⟨bias,ports,scope,meaning⟩ := span_address (what o List.mem_cons_self)
    obtain ⟨read,affine,readOk,len,affOk⟩ := ih (fun f hf=>what f (List.mem_cons_of_mem _ hf))
    let read' (w : List Bool) := (bias ^^ evalParity w ports)::read w
    let aff' (w : List (Form S)) := (add (const bias) (linearInstr w ports))::affine w
    refine ⟨read',aff',?_,?_,?_⟩
    · intro y
      change (bias ^^ evalParity (samples P y) ports)::read (samples P y)=o y::samples tail y
      rw [←meaning,readOk]
    · intro ws
      simp [aff',len]
    · intro d ws x s
      change value (add (const bias) (linearInstr ws ports)) d x s::wire (affine ws) d x s=
        (bias ^^ evalParity (wire ws d x s) ports)::read (wire ws d x s)
      rw [add_value,const_value,linearInstr_ok,affOk]

theorem second_with_observations {Y S : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) (pack : Assign → S → Y)
    (d : List Nat) (nd : d.Nodup) (w : List (Form S))
    (raw : ∀ x s,wire w d x s=samples B (pack x s))
    (obs : List (Fun Y)) (obs_ok : ∀ f∈obs,Span P f) :
    ∃ L : List (View S),
      (∀ s test,(cube d).countP (fun x=>test (samples obs (pack x s)))=countView L s test) ∧
      ∀ u∈L,u.domain.Nodup ∧ u.domain.length ≤ d.length ∧
        d.length-u.domain.length ≤ q ∧ u.values.length=obs.length := by
  obtain ⟨L,counts,ok⟩ := residual prior pack d nd w raw
  obtain ⟨read,affine,readOk,len,affOk⟩ := lift (S:=S) obs obs_ok
  let act (u : View S) : View S := ⟨u.domain,affine u.values⟩
  refine ⟨L.map act,?_,?_⟩
  · intro s test
    have h := counts s (fun x=>test (read x))
    simp only [readOk] at h
    rw [h]
    simp only [countView,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro u _
    change (cube u.domain).countP (fun x=>test (read (wire u.values u.domain x s)))=
      (cube u.domain).countP (fun x=>test (wire (affine u.values) u.domain x s))
    simp only [affOk]
  · intro u hm
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    obtain ⟨a,b,c,_⟩ := ok v hv
    exact ⟨a,b,c,len _⟩

end PEqualNP.Outside.L_meta_32580.ResidualLift

/- Source segment: OrthogonalCount. -/


namespace PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.Polarization

def zero : Assign := fun _=>false
noncomputable def isZero (a : Assign) : Bool := @decide (a=zero) (Classical.propDecidable _)
def unit (j : Nat) : Assign := fun k=>decide (k=j)
def dot (d : List Nat) (u v : Assign) : Bool := parity (fun j=>u j && v j) d
def subgroup (d : List Nat) (U : Assign → Bool) : List Assign := (cube d).filter U
def ann (d : List Nat) (U : Assign → Bool) (v : Assign) : Bool :=
  !(subgroup d U).any (fun u=>dot d u v)

theorem shift_invol (u x : Assign) : shift u (shift u x)=x := by
  funext j
  unfold shift
  cases u j <;> cases x j <;> rfl

theorem shift_comm (a b : Assign) : shift a b = shift b a := by
  funext j
  exact Bool.xor_comm _ _

theorem dot_comm (d : List Nat) (a b : Assign) : dot d a b=dot d b a := by
  unfold dot
  apply parity_congr
  intro j _
  exact Bool.and_comm _ _

theorem dot_shift (d : List Nat) (a u x : Assign) :
    dot d a (shift u x)=(dot d a u ^^ dot d a x) := by
  exact linear_shift (Y:=Unit) ⟨a,fun _=>false⟩ d u x

theorem parity_zero (d : List Nat) : parity (fun _=>false) d=false := by
  induction d with
  | nil => rfl
  | cons j t ih => simpa [parity] using ih

theorem dot_zero (d : List Nat) (a : Assign) : dot d zero a=false := by
  exact parity_zero d

theorem unit_supported {d : List Nat} {j : Nat} (hj : j∈d) : supported d (unit j) := by
  intro k h
  have ne : k≠j := fun eq=>h (eq ▸ hj)
  simp [unit,ne]

theorem dot_unit {d : List Nat} {j : Nat} (nd : d.Nodup) (hj : j∈d) (a : Assign) :
    dot d a (unit j)=a j := by
  let f : Form Unit := ⟨a,fun _=>false⟩
  change linear f d (unit j)=a j
  rw [linear_split f hj]
  have go : linear f (d.erase j) (unit j)=false := by
    unfold linear
    have zz : parity (fun k=>f.coeff k && unit j k) (d.erase j) =
      parity (fun _=>false) (d.erase j) := by
      apply parity_congr
      intro k hk
      have ne : k≠j := fun eq=>erase_avoids nd hj (eq ▸ hk)
      simp [unit,ne]
    rw [zz,parity_zero]
  rw [go]
  simp [unit,f]

theorem ambient_halves {d : List Nat} (nd : d.Nodup) (u : Assign) (hu : supported d u)
    (nz : u≠zero) : 2*(cube d).countP (dot d u)=(cube d).length := by
  have existsJ : ∃ j,u j=true := by
    classical
    apply Classical.byContradiction
    intro n
    exact nz (funext (fun j=>Bool.eq_false_iff.mpr (fun hj=>n ⟨j,hj⟩)))
  obtain ⟨j,one⟩ := existsJ
  have hj : j∈d := by
    apply Classical.byContradiction
    intro miss
    rw [hu j miss] at one
    contradiction
  apply exactly_half (unit_supported hj)
  intro x
  rw [dot_shift,dot_unit nd hj,one,Bool.true_xor]

theorem subgroup_shift {d : List Nat} {U : Assign → Bool}
    (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    {u : Assign} (hu : u∈subgroup d U) :
    ((subgroup d U).map (shift u)).Perm (subgroup d U) := by
  obtain ⟨mem,hit⟩ := List.mem_filter.mp hu
  have stable : (fun x=> U (shift u x))=U := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have back := closed u (shift u x) hit h
      simpa only [shift_invol] using back
    · exact closed u x hit
  have tp := (cube_shift (mem_cube.mp mem)).filter U
  rw [List.filter_map] at tp
  change (((cube d).filter (fun x=>U (shift u x))).map (shift u)).Perm (subgroup d U) at tp
  rwa [stable] at tp

theorem subgroup_halves {d : List Nat} {U : Assign → Bool}
    (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    {u v : Assign} (hu : u∈subgroup d U) (hit : dot d u v=true) :
    2*(subgroup d U).countP (fun x=>dot d x v)=(subgroup d U).length := by
  let f := fun x=>dot d x v
  have iso := (subgroup_shift closed hu).countP_eq f
  have flips : (fun x=>f (shift u x))=(fun x=> !(f x)) := by
    funext x
    dsimp [f]
    rw [dot_comm d (shift u x) v,dot_shift,dot_comm d v u,dot_comm d v x,hit,Bool.true_xor]
  simp only [List.countP_map,Function.comp_def,flips] at iso
  have total := count_complement (subgroup d U) f
  change 2*(subgroup d U).countP f=_
  omega

theorem sum_add_map {A : Type} (l : List A) (f g : A → Nat) :
    (l.map (fun x=>f x+g x)).sum=(l.map f).sum+(l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    omega

theorem countP_cons_add {A : Type} (a : A) (l : List A) (p : A → Bool) :
    (a::l).countP p=(if p a then 1 else 0)+l.countP p := by
  cases h : p a <;> simp [List.countP_cons,h,Nat.succ_eq_add_one,Nat.add_comm]

theorem count_as_sum {A : Type} (l : List A) (p : A → Bool) :
    l.countP p=(l.map (fun a=>if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [countP_cons_add,List.map_cons,List.sum_cons,←ih]

theorem incidence_flip {A B : Type} (l : List A) (m : List B) (p : A → B → Bool) :
    (l.map (fun a=>m.countP (p a))).sum=(m.map (fun b=>l.countP (fun a=>p a b))).sum := by
  induction l with
  | nil =>
    induction m with
    | nil => rfl
    | cons b t ih =>
      change 0=0+(t.map (fun _=>0)).sum
      exact (Nat.zero_add _).symm ▸ ih
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons,countP_cons_add,sum_add_map,←count_as_sum,ih]

theorem sum_halves {A : Type} (l : List A) (f : A → Nat) (P : A → Bool) (M : Nat)
    (each : ∀ a∈l,2*f a + (if P a then M else 0)=M) :
    2*(l.map f).sum+(l.countP P)*M=l.length*M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun b hb => each b (List.mem_cons_of_mem _ hb))
    have ha := each a List.mem_cons_self
    cases hp : P a <;>
      simp only [List.map_cons,List.sum_cons,List.length_cons,countP_cons_add,
        Nat.mul_add,Nat.add_mul,hp,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq,
        Nat.one_mul,Nat.zero_mul] at ha ⊢ <;> omega

theorem ann_spec {d : List Nat} {U : Assign → Bool} {v : Assign} :
    ann d U v=true ↔ ∀ u∈subgroup d U,dot d u v=false := by
  have h (q : Bool) : (!q)=true ↔ q=false := by cases q <;> decide
  unfold ann
  rw [h,List.any_eq_false]
  exact forall_congr' (fun u=>forall_congr' (fun _=>Bool.eq_false_iff.symm))

theorem count_zero_point {d : List Nat} {U : Assign → Bool}
    (nd : d.Nodup) (U0 : U zero=true) :
    (subgroup d U).countP isZero=1 := by
  classical
  have in0 : zero∈cube d := mem_cube.mpr fun _ _=>rfl
  letI : DecidableEq Assign := fun a b=>Classical.propDecidable (a=b)
  have ndU : (subgroup d U).Nodup := (cube_nodup nd).filter U
  have h0 : (subgroup d U).count zero=1 := List.Nodup.count_of_mem ndU (List.mem_filter.mpr ⟨in0,U0⟩)
  exact h0

                                                                     
                                                                   
                                             
theorem cardinality {d : List Nat} (nd : d.Nodup) (U : Assign → Bool)
    (U0 : U zero=true) (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true) :
    (subgroup d U).length*(subgroup d (ann d U)).length=(cube d).length := by
  classical
  let B := cube d
  let H := subgroup d U
  let f := fun u : Assign=>B.countP (dot d u)
  let g := fun v : Assign=>H.countP (fun u=>dot d u v)
  have rows := sum_halves H f isZero B.length (by
    intro u hu
    by_cases hz : u=zero
    · subst u
      have ff : f zero=0 := List.countP_eq_zero.mpr (fun a ha=>by simp [dot_zero])
      simp [ff,isZero]
    · have half := ambient_halves nd u (mem_cube.mp (List.mem_filter.mp hu).1) hz
      simpa only [f,B,isZero,decide_eq_false hz,Bool.false_eq_true,ite_false,Nat.add_zero] using half)
  rw [count_zero_point nd U0,Nat.one_mul] at rows
  have cols := sum_halves B g (ann d U) H.length (by
    intro v _
    cases hv : ann d U v
    · have nn : H.any (fun u=>dot d u v)=true := by
        simpa [ann,H] using hv
      obtain ⟨u,hu,hit⟩ := List.any_eq_true.mp nn
      have half := subgroup_halves closed hu hit
      simpa only [g,H,hv,Bool.false_eq_true,ite_false,Nat.add_zero] using half
    · have zeroG : g v=0 := List.countP_eq_zero.mpr (fun a ha=>by
        rw [ann_spec.mp hv a ha]
        decide)
      simp only [zeroG,hv,ite_true,Nat.mul_zero,Nat.zero_add])
  rw [List.countP_eq_length_filter] at cols
  change 2*(B.map g).sum+(subgroup d (ann d U)).length*H.length=B.length*H.length at cols
  have sw := incidence_flip H B (dot d)
  change (H.map f).sum=(B.map g).sum at sw
  rw [←sw,Nat.mul_comm B.length H.length] at cols
  have eq : (subgroup d (ann d U)).length*H.length=B.length := by omega
  simpa only [Nat.mul_comm] using eq

end PEqualNP.Outside.L_meta_32580.OrthogonalCount

/- Source segment: ClippingInjection. -/


namespace PEqualNP.Outside.L_meta_32580.ClippingInjection
variable {K : Type}
abbrev Bits (K : Type) := K → Bool

def zero : Bits K := fun _=>false
def xor (a b : Bits K) : Bits K := fun j=>a j ^^ b j
def clip (m x : Bits K) : Bits K := fun i=>m i && x i
def extend (a b : Bits K) : Bits K := fun i=>a i || b i

noncomputable section

def repr (U : Bits K  →  Prop) (seen x : Bits K) : Bits K := by
  classical
  exact if h : ∃ r,U r ∧ clip seen r=x then Classical.choose h else zero

theorem representative {U : Bits K → Prop} {x : Bits K} (hx : U x) (seen : Bits K) :
    U (repr U seen (clip seen x)) ∧ clip seen (repr U seen (clip seen x))=clip seen x := by
  unfold repr
  split
  · rename_i exist
    exact Classical.choose_spec exist
  · rename_i no
    exact False.elim (no ⟨x,hx,rfl⟩)

def step (U : Bits K → Prop) (seen next x : Bits K) : Bits K :=
  clip next (xor x (repr U seen (clip seen x)))

def encode (U : Bits K → Prop) : Bits K → List (Bits K) → Bits K → Bits K
  | _,[],_ => zero
  | seen,q::tail,x => xor (step U seen q x) (encode U (extend seen q) tail x)

def cover : Bits K → List (Bits K) → Bits K
  | seen,[] => seen
  | seen,q::tail => cover (extend seen q) tail

theorem cover_old {seen : Bits K} {pending : List (Bits K)} {j : K} (h : seen j=true) :
    cover seen pending j=true := by
  induction pending generalizing seen with
  | nil => exact h
  | cons q tail ih =>
    exact ih (seen:=extend seen q) (by simp [extend,h])

theorem cover_mem {seen q : Bits K} {pending : List (Bits K)} {j : K}
    (h : q∈pending) (hit : q j=true) : cover seen pending j=true := by
  induction pending generalizing seen with
  | nil => simp at h
  | cons a tail ih =>
    rcases List.mem_cons.mp h with rfl|hh
    · exact cover_old (seen:=extend seen q) (pending:=tail) (by simp [extend,hit])
    · exact ih (seen:=extend seen a) hh

theorem step_old {U : Bits K → Prop} {x seen q : Bits K}
    (mem : U x) {j : K} (hit : seen j=true) : step U seen q x j=false := by
  have seenEq := congrFun (representative mem seen).2 j
  have same : repr U seen (clip seen x) j=x j := by
    simpa [clip,hit] using seenEq
  simp [step,clip,xor,same,Bool.xor_self]

theorem encode_old {U : Bits K → Prop} {x seen : Bits K} {pending : List (Bits K)}
    (mem : U x) {j : K} (hit : seen j=true) : encode U seen pending x j=false := by
  induction pending generalizing seen with
  | nil => rfl
  | cons q tail ih =>
    have later : extend seen q j=true := by simp [extend,hit]
    change (step U seen q x j ^^ encode U (extend seen q) tail x j)=false
    rw [step_old mem hit,ih later]
    rfl

                                                                   
                                             
theorem encode_mem (U W : Bits K → Prop)
    (uadd : ∀ a b,U a → U b → U (xor a b))
    (w0 : W zero) (wadd : ∀ a b,W a → W b → W (xor a b))
    (pending : List (Bits K)) (allowed : ∀ q∈pending,∀ x,U x → W (clip q x))
    (seen x : Bits K) (mem : U x) : W (encode U seen pending x) := by
  induction pending generalizing seen with
  | nil => exact w0
  | cons q tail ih =>
    apply wadd
    · exact allowed q List.mem_cons_self _ (uadd _ _ mem (representative mem seen).1)
    · exact ih (fun a ha=>allowed a (List.mem_cons_of_mem _ ha)) (extend seen q)

                                                                      
                                                                         
theorem recover {U : Bits K → Prop} {x y : Bits K} (ux : U x) (uy : U y)
    (pending : List (Bits K)) (seen : Bits K)
    (old : clip seen x=clip seen y)
    (coded : encode U seen pending x=encode U seen pending y) :
    clip (cover seen pending) x=clip (cover seen pending) y := by
  induction pending generalizing seen with
  | nil => exact old
  | cons q tail ih =>
    have sameRep : repr U seen (clip seen x)=repr U seen (clip seen y) :=
      congrArg (repr U seen) old
    have inQ {j : K} (jq : q j=true) : x j=y j := by
      have eq := congrFun coded j
      have hnew : extend seen q j=true := by simp [extend,jq]
      change (step U seen q x j ^^ encode U (extend seen q) tail x j)=
        (step U seen q y j ^^ encode U (extend seen q) tail y j) at eq
      rw [encode_old ux hnew,encode_old uy hnew] at eq
      simp only [Bool.xor_false,step,clip,jq,Bool.true_and,xor,sameRep] at eq
      exact Bool.xor_left_inj.mp eq
    have advance : clip (extend seen q) x=clip (extend seen q) y := by
      funext j
      cases s : seen j
      · cases h : q j
        · simp [clip,extend,s,h]
        · simp [clip,extend,s,h,inQ h]
      · have h := congrFun old j
        simpa [clip,extend,s] using h
    have stepEq : step U seen q x=step U seen q y := by
      funext j
      cases jq : q j
      · simp [step,clip,jq]
      · simp [step,clip,xor,jq,sameRep,inQ jq]
    have restEq : encode U (extend seen q) tail x=encode U (extend seen q) tail y := by
      funext j
      have z := congrFun coded j
      change (step U seen q x j ^^ encode U (extend seen q) tail x j)=
        (step U seen q y j ^^ encode U (extend seen q) tail y j) at z
      rw [stepEq] at z
      exact Bool.xor_right_inj.mp z
    exact ih (extend seen q) advance restEq

                                                                      
                                                                     
                              
theorem into_span (U W : Bits K → Prop)
    (uadd : ∀ a b,U a → U b → U (xor a b))
    (w0 : W zero) (wadd : ∀ a b,W a → W b → W (xor a b))
    (pending : List (Bits K)) (contain : ∀ q∈pending,∀ x,U x → W (clip q x))
    (covers : ∀ j, ∃ q∈pending,q j=true) :
    ∃ f : {x : Bits K // U x}  →  {y : Bits K // W y}, ∀ x y,f x=f y → x=y := by
  let f (x : {x : Bits K // U x}) : {y : Bits K // W y} :=
    ⟨encode U zero pending x.1,encode_mem U W uadd w0 wadd pending contain zero x.1 x.2⟩
  refine ⟨f,?_⟩
  intro x y h
  apply Subtype.ext
  have codeEq : encode U zero pending x.1=encode U zero pending y.1 := congrArg Subtype.val h
  have start : clip zero x.1=clip zero y.1 := rfl
  have stop := recover x.2 y.2 pending zero start codeEq
  funext j
  obtain ⟨q,m,hit⟩ := covers j
  have seenAll : cover zero pending j=true := cover_mem m hit
  have z := congrFun stop j
  simpa [clip,seenAll] using z

end
end PEqualNP.Outside.L_meta_32580.ClippingInjection

/- Source segment: IsotropyCount. -/


namespace PEqualNP.Outside.L_meta_32580.IsotropyCount
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry PEqualNP.Outside.L_meta_32580.Translation
open PEqualNP.Outside.L_meta_32580.OrthogonalCount

theorem add_supported {d : List Nat} {a b : Assign} (ha : supported d a) (hb : supported d b) :
    supported d (shift a b) := by
  intro j hj
  rw [shift,ha j hj,hb j hj]
  rfl

theorem clip_supported {d : List Nat} (q : Assign) {x : Assign} (hx : supported d x) :
    supported d (ClippingInjection.clip q x) := by
  intro j hj
  simp [ClippingInjection.clip,hx j hj]

theorem ann_zero (d : List Nat) (U : Assign → Bool) : ann d U zero=true := by
  apply ann_spec.mpr
  intro u hu
  rw [dot_comm,dot_zero]

theorem ann_add {d : List Nat} {U : Assign → Bool} {a b : Assign}
    (ha : ann d U a=true) (hb : ann d U b=true) : ann d U (shift a b)=true := by
  apply ann_spec.mpr
  intro u hu
  rw [dot_shift,ann_spec.mp ha u hu,ann_spec.mp hb u hu]
  rfl

theorem code_injective {d : List Nat} {S : Assign → Prop}
    {a b : Assign} (sa : S a) (sb : S b) (ha : supported d a) (hb : supported d b)
    (masks : List Assign) (covers : ∀ j∈d,∃ q∈masks,q j=true)
    (same : ClippingInjection.encode S zero masks a=ClippingInjection.encode S zero masks b) :
    a=b := by
  have start : ClippingInjection.clip zero a=ClippingInjection.clip zero b := rfl
  have recover := ClippingInjection.recover sa sb masks zero start same
  funext j
  by_cases hj : j∈d
  · obtain ⟨q,hq,one⟩ := covers j hj
    have mask : ClippingInjection.cover zero masks j=true := ClippingInjection.cover_mem hq one
    simpa [ClippingInjection.clip,mask] using congrFun recover j
  · rw [ha j hj,hb j hj]

                                                                             
                                                                            
                                                                         
                                                                              
theorem cardinal_bound {d : List Nat} (nd : d.Nodup) (U : Assign → Bool)
    (U0 : U zero=true) (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    (swap : Assign → Assign) (adds : ∀ a b,swap (shift a b)=shift (swap a) (swap b))
    (zero_swap : swap zero=zero)
    (inside : ∀ a,supported d a → supported d (swap a))
    (inj : ∀ a b,supported d a → supported d b → swap a=swap b → a=b)
    (masks : List Assign) (covers : ∀ j∈d,∃ q∈masks,q j=true)
    (iso : ∀ q∈masks,∀ x∈subgroup d U,∀ y∈subgroup d U,
      dot d y (swap (ClippingInjection.clip q x))=false) :
    (subgroup d U).length*(subgroup d U).length ≤ (cube d).length := by
  classical
  let S := fun a=>supported d a ∧ U a=true
  let W := fun a=>supported d a ∧ ann d U (swap a)=true
  have s_add : ∀ a b,S a → S b → S (ClippingInjection.xor a b) := by
    intro a b ha hb
    exact ⟨add_supported ha.1 hb.1,closed a b ha.2 hb.2⟩
  have w_zero : W ClippingInjection.zero :=
    ⟨fun _ _=>rfl,by change ann d U (swap zero)=true; rw [zero_swap]; exact ann_zero d U⟩
  have w_add : ∀ a b,W a → W b → W (ClippingInjection.xor a b) := by
    intro a b ha hb
    refine ⟨add_supported ha.1 hb.1,?_⟩
    change ann d U (swap (shift a b))=true
    rw [adds]
    exact ann_add ha.2 hb.2
  have w_masks : ∀ q∈masks,∀ x,S x → W (ClippingInjection.clip q x) := by
    intro q hq x hx
    refine ⟨clip_supported q hx.1,ann_spec.mpr (fun y hy=>?_ )⟩
    exact iso q hq x (List.mem_filter.mpr ⟨mem_cube.mpr hx.1,hx.2⟩) y hy
  let f := fun x=>swap (ClippingInjection.encode S zero masks x)
  have codes x (hx : x∈subgroup d U) : W (ClippingInjection.encode S zero masks x) := by
    have hh := List.mem_filter.mp hx
    exact ClippingInjection.encode_mem S W s_add w_zero w_add masks w_masks zero x
      ⟨mem_cube.mp hh.1,hh.2⟩
  have f_inj : ∀ a∈subgroup d U,∀ b∈subgroup d U,f a=f b → a=b := by
    intro a ha b hb equal
    have sa := List.mem_filter.mp ha
    have sb := List.mem_filter.mp hb
    apply code_injective (S:=S) ⟨mem_cube.mp sa.1,sa.2⟩ ⟨mem_cube.mp sb.1,sb.2⟩
      (mem_cube.mp sa.1) (mem_cube.mp sb.1) masks covers
    exact inj _ _ (codes a ha).1 (codes b hb).1 equal
  have image_nd := nodup_map_from (subgroup d U) ((cube_nodup nd).filter U) f f_inj
  have sub : (subgroup d U).map f ⊆ subgroup d (ann d U) := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
    exact List.mem_filter.mpr ⟨mem_cube.mpr (inside _ (codes a ha).1),(codes a ha).2⟩
  have le := List.Nodup.length_le_of_subset image_nd sub
  rw [List.length_map] at le
  rw [←cardinality nd U U0 closed]
  exact Nat.mul_le_mul_left _ le

theorem sqrt_power_bound {a v : Nat} (h : a*a ≤ 2^(2*v)) : a ≤ 2^v := by
  rw [show 2*v=v+v by omega,Nat.pow_add] at h
  apply Nat.le_of_not_gt
  intro small
  have positive : 0<a := Nat.zero_lt_of_lt small
  have h1 : 2^v*2^v ≤ 2^v*a := Nat.mul_le_mul_left _ (Nat.le_of_lt small)
  have h2 : 2^v*a<a*a := Nat.mul_lt_mul_of_pos_right small positive
  exact (Nat.not_lt_of_ge h) (Nat.lt_of_le_of_lt h1 h2)

end PEqualNP.Outside.L_meta_32580.IsotropyCount

/- Source segment: ProjectionCount. -/


namespace PEqualNP.Outside.L_meta_32580.ProjectionCount
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry PEqualNP.Outside.L_meta_32580.Translation
open PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.IsotropyCount
open PEqualNP.Outside.L_meta_32580.ClippingInjection (clip)

noncomputable def projected (d : List Nat) (U : Assign → Bool) (mask : Assign) (a : Assign) : Bool :=
  (subgroup d U).any (fun x=>@decide (clip mask x=a) (Classical.propDecidable _))

theorem projected_spec {d : List Nat} {U : Assign → Bool} {mask a : Assign} :
    projected d U mask a=true ↔ ∃ x∈subgroup d U, clip mask x=a := by
  simp only [projected,List.any_eq_true,decide_eq_true_eq]

theorem clip_zero (mask : Assign) : clip mask zero=zero := by
  funext j
  simp [clip,zero]

theorem clip_add (mask a b : Assign) :
    clip mask (shift a b)=shift (clip mask a) (clip mask b) := by
  funext j
  exact Bool.and_xor_distrib_left _ _ _

theorem subgroup_zero {d : List Nat} {U : Assign → Bool} (z : U zero=true) : zero∈subgroup d U :=
  List.mem_filter.mpr ⟨mem_cube.mpr (fun _ _=>rfl),z⟩

theorem project_zero (d : List Nat) {U : Assign → Bool} (mask : Assign) (z : U zero=true) :
    projected d U mask zero=true :=
  projected_spec.mpr ⟨zero,subgroup_zero z,clip_zero mask⟩

theorem subgroup_add {d : List Nat} {U : Assign → Bool}
    (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    {a b : Assign} (ha : a∈subgroup d U) (hb : b∈subgroup d U) :
    shift a b∈subgroup d U := by
  obtain ⟨ea,qa⟩ := List.mem_filter.mp ha
  obtain ⟨eb,qb⟩ := List.mem_filter.mp hb
  exact List.mem_filter.mpr ⟨mem_cube.mpr (add_supported (mem_cube.mp ea) (mem_cube.mp eb)),
    closed a b qa qb⟩

theorem project_add (d : List Nat) {U : Assign → Bool} (mask : Assign)
    (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true) :
    ∀ a b,projected d U mask a=true → projected d U mask b=true → 
      projected d U mask (shift a b)=true := by
  intro a b ha hb
  obtain ⟨x,hx,rfl⟩ := projected_spec.mp ha
  obtain ⟨y,hy,rfl⟩ := projected_spec.mp hb
  exact projected_spec.mpr ⟨shift x y,subgroup_add closed hx hy,clip_add mask x y⟩

theorem support_project {d : List Nat} {u : Assign} (hu : supported d u) (mask : Assign) :
    supported (d.filter mask) (clip mask u) := by
  intro j outside
  cases h : mask j
  · simp [clip,h]
  · have ne : j∉d := fun jj=>outside (List.mem_filter.mpr ⟨jj,h⟩)
    simp [clip,h,hu j ne]

theorem projection_mem {d : List Nat} {U : Assign → Bool} {x : Assign}
    (hx : x∈subgroup d U) (mask : Assign) :
    clip mask x∈subgroup (d.filter mask) (projected d U mask) :=
  List.mem_filter.mpr ⟨mem_cube.mpr (support_project (mem_cube.mp (List.mem_filter.mp hx).1) mask),
    projected_spec.mpr ⟨x,hx,rfl⟩⟩

theorem split_injective (mask : Assign) {x y : Assign}
    (a : clip mask x=clip mask y) (b : clip (fun j=> !(mask j)) x=clip (fun j=> !(mask j)) y) : x=y := by
  funext j
  cases h : mask j
  · simpa [clip,h] using congrFun b j
  · simpa [clip,h] using congrFun a j

theorem length_product {A B : Type} (l : List A) (r : List B) :
    (l.flatMap (fun a=>r.map (fun b=>(a,b)))).length=l.length*r.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,
      Nat.add_mul,Nat.one_mul,Nat.add_comm]

theorem projection_product {d : List Nat} (nd : d.Nodup) (U : Assign → Bool) (mask : Assign) :
    (subgroup d U).length  ≤ 
      (subgroup (d.filter mask) (projected d U mask)).length *
      (cube (d.filter (fun j=> !(mask j)))).length := by
  let v := subgroup (d.filter mask) (projected d U mask)
  let t := cube (d.filter (fun j=> !(mask j)))
  let f x := (clip mask x,clip (fun j=> !(mask j)) x)
  have doub : (List.map f (subgroup d U)).Nodup := by
    apply nodup_map_from _ ((cube_nodup nd).filter U)
    intro x hx y hy eq
    exact split_injective mask (congrArg Prod.fst eq) (congrArg Prod.snd eq)
  have sub : (List.map f (subgroup d U)) ⊆ v.flatMap (fun a=>t.map (fun b=>(a,b))) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
    refine List.mem_flatMap.mpr ⟨clip mask x,projection_mem hx mask,?_⟩
    apply List.mem_map.mpr
    exact ⟨clip (fun j=> !(mask j)) x,
      mem_cube.mpr (support_project (mem_cube.mp (List.mem_filter.mp hx).1) _),rfl⟩
  simpa only [List.length_map,length_product] using List.Nodup.length_le_of_subset doub sub

                                                                      
                                                                   
                                                                       
                                                                           
theorem active_codimension {d : List Nat} (nd : d.Nodup) (U : Assign → Bool)
    (U0 : U zero=true) (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    (mask : Assign) (v cuts : Nat) (pair_width : (d.filter mask).length=2*v)
    (large : 2^(d.length-cuts) ≤ (subgroup d U).length)
    (swap : Assign → Assign) (adds : ∀ a b,swap (shift a b)=shift (swap a) (swap b))
    (zero_swap : swap zero=zero)
    (inside : ∀ a,supported (d.filter mask) a → supported (d.filter mask) (swap a))
    (inj : ∀ a b,supported (d.filter mask) a → supported (d.filter mask) b → swap a=swap b → a=b)
    (masks : List Assign) (covers : ∀ j∈d.filter mask,∃ q∈masks,q j=true)
    (iso : ∀ q∈masks,∀ x∈subgroup d U,∀ y∈subgroup d U,
      dot (d.filter mask) (clip mask y) (swap (clip q (clip mask x)))=false) :
    v ≤ cuts := by
  let P := projected d U mask
  let active := d.filter mask
  let other := d.filter (fun j=> !(mask j))
  have h := cardinal_bound (nd.filter mask) P (project_zero d mask U0)
    (project_add d mask closed) swap adds zero_swap inside inj masks covers (by
      intro q hq x hx y hy
      obtain ⟨a,ha,ea⟩ := projected_spec.mp (List.mem_filter.mp hx).2
      obtain ⟨b,hb,eb⟩ := projected_spec.mp (List.mem_filter.mp hy).2
      rw [←ea,←eb]
      exact iso q hq a ha b hb)
  rw [cube_size,pair_width] at h
  have boundProj := sqrt_power_bound h
  have prod := projection_product nd U mask
  rw [cube_size] at prod
  have mul := Nat.mul_le_mul_right (2^other.length) boundProj
  have together := Nat.le_trans large (Nat.le_trans prod mul)
  rw [←Nat.pow_add] at together
  have size := count_complement d mask
  simp only [List.countP_eq_length_filter] at size
  have exponents := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp together
  change d.length-cuts ≤ v+other.length at exponents
  change active.length+other.length=d.length at size
  change active.length=2*v at pair_width
  omega

end PEqualNP.Outside.L_meta_32580.ProjectionCount

/- Source segment: AffineImage. -/


namespace PEqualNP.Outside.L_meta_32580.AffineImage
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.Polarization PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.ChartGeometry PEqualNP.Outside.L_meta_32580.ProjectionCount

noncomputable def image (d : List Nat) (f : Assign → Assign) (a : Assign) : Bool :=
  (cube d).any (fun x=>@decide (f x=a) (Classical.propDecidable _))

theorem image_spec {d : List Nat} {f : Assign → Assign} {a : Assign} :
    image d f a=true ↔ ∃ x∈cube d,f x=a := by
  simp only [image,List.any_eq_true,decide_eq_true_eq]

theorem image_zero (d : List Nat) {f : Assign → Assign} (f0 : f zero=zero) :
    image d f zero=true :=
  image_spec.mpr ⟨zero,mem_cube.mpr (fun _ _=>rfl),f0⟩

theorem image_add (d : List Nat) {f : Assign → Assign}
    (adds : ∀ a b,f (shift a b)=shift (f a) (f b)) :
    ∀ a b,image d f a=true → image d f b=true → image d f (shift a b)=true := by
  intro a b ha hb
  obtain ⟨x,hx,rfl⟩ := image_spec.mp ha
  obtain ⟨y,hy,rfl⟩ := image_spec.mp hb
  exact image_spec.mpr ⟨shift x y,mem_cube.mpr (IsotropyCount.add_supported
    (mem_cube.mp hx) (mem_cube.mp hy)),adds x y⟩

theorem image_card {d c : List Nat} (nd : d.Nodup) (nc : c.Nodup) (f : Assign → Assign)
    (inside : ∀ a∈cube d,supported c (f a))
    (inj : ∀ a∈cube d,∀ b∈cube d,f a=f b → a=b) :
    (subgroup c (image d f)).length=2^d.length := by
  have first := nodup_map_from _ (cube_nodup nd) f inj
  have last : (subgroup c (image d f)).Nodup := (cube_nodup nc).filter _
  have sets : ∀ a, a∈subgroup c (image d f) ↔ a∈List.map f (cube d) := by
    intro a
    constructor
    · intro h
      exact List.mem_map.mpr (image_spec.mp (List.mem_filter.mp h).2)
    · intro h
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      exact List.mem_filter.mpr ⟨mem_cube.mpr (inside x hx),image_spec.mpr ⟨x,hx,rfl⟩⟩
  have length_eq := ((List.perm_ext_iff_of_nodup last first).mpr sets).length_eq
  simpa only [List.length_map,cube_size] using length_eq

def slopeChart {Y : Type} (c d : List Nat) (w : Nat → Form Y) (x : Assign) : Assign :=
  fun j=> if j∈c then linear (w j) d x else false

theorem slope_support {Y : Type} (c d : List Nat) (w : Nat → Form Y) (x : Assign) :
    supported c (slopeChart c d w x) := by
  intro j hj
  simp [slopeChart,hj]

theorem slope_zero {Y : Type} (c d : List Nat) (w : Nat → Form Y) :
    slopeChart c d w zero=zero := by
  funext j
  by_cases h : j∈c
  · simp only [slopeChart,h,ite_true,linear]
    simpa only [zero,Bool.and_false] using parity_zero d
  · simp [slopeChart,h,zero]

theorem slope_add {Y : Type} (c d : List Nat) (w : Nat → Form Y) (a b : Assign) :
    slopeChart c d w (shift a b)=shift (slopeChart c d w a) (slopeChart c d w b) := by
  funext j
  by_cases h : j∈c
  · simp [slopeChart,h,shift,←linear_shift]
  · simp [slopeChart,h,shift]

theorem slope_inj {Y : Type} (c d : List Nat) (w : Nat → Form Y) (y : Y)
    (faithful : ∀ a∈cube d,∀ b∈cube d,
      TapeKernel.wire (c.map w) d a y=TapeKernel.wire (c.map w) d b y → a=b) :
    ∀ a∈cube d,∀ b∈cube d,slopeChart c d w a=slopeChart c d w b → a=b := by
  intro a ha b hb same
  apply slope_injective (c.map w) d y faithful a ha b hb
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  simpa [slopeChart,hj] using congrFun same j

                                                                     
                                                                        
                                                              
theorem faithful_rank {Y : Type} {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup)
    (w : Nat → Form Y) (y : Y)
    (faithful : ∀ a∈cube d,∀ b∈cube d,
      TapeKernel.wire (c.map w) d a y=TapeKernel.wire (c.map w) d b y → a=b) :
    let U := image d (slopeChart c d w)
    U zero=true ∧ (∀ a b,U a=true → U b=true → U (shift a b)=true) ∧
      (subgroup c U).length=2^d.length := by
  refine ⟨image_zero d (slope_zero c d w),image_add d (slope_add c d w),?_⟩
  exact image_card nd nc _ (fun a _=>slope_support c d w a) (slope_inj c d w y faithful)

end PEqualNP.Outside.L_meta_32580.AffineImage

/- Source segment: FrequencyFlat. -/


namespace PEqualNP.Outside.L_meta_32580.FrequencyFlat
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.Polarization PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffineImage

def affineChart {Y : Type} (c d : List Nat) (w : Nat → Form Y) (x : Assign) (y : Y) : Assign :=
  fun j=>if j∈c then value (w j) d x y else false

theorem affineChart_shift {Y : Type} (c d : List Nat) (w : Nat → Form Y) (u x : Assign) (t : Y) :
    affineChart c d w (shift u x) t=shift (slopeChart c d w u) (affineChart c d w x t) := by
  funext j
  by_cases hj : j∈c
  · simp only [affineChart,slopeChart,hj,ite_true,shift]
    exact value_shift (w j) d u x t
  · simp [affineChart,slopeChart,hj,shift]

def agrees {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y) (y : Assign) : Bool :=
  (cube d).all (fun u=>dot c (slopeChart c d w u) y == linear out d u)

theorem agrees_spec {Y : Type} {c d : List Nat} {w : Nat → Form Y} {out : Form Y} {y : Assign} :
    agrees c d w out y=true ↔
      ∀ u∈cube d,dot c (slopeChart c d w u) y=linear out d u := by
  simp only [agrees,List.all_eq_true,beq_iff_eq]

def discrepancy {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y)
    (x : Assign) (t : Y) (y : Assign) (bias : Bool) : Bool :=
  value out d x t ^^ (dot c (affineChart c d w x t) y ^^ bias)

theorem discrepancy_shift {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y)
    (u x : Assign) (t : Y) (y : Assign) (bias : Bool) :
    discrepancy c d w out (shift u x) t y bias=
      ((linear out d u ^^ dot c (slopeChart c d w u) y) ^^ discrepancy c d w out x t y bias) := by
  unfold discrepancy
  rw [value_shift,affineChart_shift,dot_comm c (shift _ _) y,dot_shift,
    dot_comm c y (slopeChart c d w u),dot_comm c y (affineChart c d w x t)]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

                                                                        
                                                                            
theorem outside_cancels {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y)
    (t : Y) (y : Assign) (bias : Bool) (no : agrees c d w out y=false) :
    2*(cube d).countP (fun x=>discrepancy c d w out x t y bias)=(cube d).length := by
  have ex : ∃ u∈cube d,dot c (slopeChart c d w u) y≠linear out d u := by
    apply Classical.byContradiction
    intro notex
    have yes := (agrees_spec (Y:=Y) (c:=c) (d:=d) (w:=w) (out:=out) (y:=y)).mpr (by
      intro u hu
      apply Classical.byContradiction
      intro ne
      exact notex ⟨u,hu,ne⟩)
    rw [no] at yes
    contradiction
  obtain ⟨u,hu,neq⟩ := ex
  apply exactly_half (mem_cube.mp hu)
  intro x
  rw [discrepancy_shift]
  generalize aE : linear out d u=a at *
  generalize bE : dot c (slopeChart c d w u) y=b at *
  cases a <;> cases b <;> simp_all

theorem within_constant {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y)
    (t : Y) (y : Assign) (bias : Bool) (yes : agrees c d w out y=true) :
    ∀ x∈cube d,discrepancy c d w out x t y bias=discrepancy c d w out zero t y bias := by
  intro x hx
  have same := agrees_spec.mp yes x hx
  have j := discrepancy_shift c d w out x zero t y bias
  have z : shift x zero=x := by funext k; simp [shift,zero]
  rw [z] at j
  simpa [same] using j

theorem shift_agrees {Y : Type} (c d : List Nat) (w : Nat → Form Y) (out : Form Y)
    (y0 : Assign) (base : agrees c d w out y0=true) (z : Assign) :
    agrees c d w out (shift y0 z)=ann c (image d (slopeChart c d w)) z := by
  apply Bool.eq_iff_iff.mpr
  rw [agrees_spec,ann_spec]
  constructor
  · intro agree h hh
    obtain ⟨u,hu,rfl⟩ := image_spec.mp (List.mem_filter.mp hh).2
    have r := agree u hu
    rw [dot_shift,agrees_spec.mp base u hu] at r
    generalize hEq : linear out d u=a at *
    generalize bEq : dot c (slopeChart c d w u) z=b at *
    cases a <;> cases b <;> simp_all
  · intro annih u hu
    have im : slopeChart c d w u∈subgroup c (image d (slopeChart c d w)) :=
      List.mem_filter.mpr ⟨mem_cube.mpr (slope_support c d w u),
        image_spec.mpr ⟨u,hu,rfl⟩⟩
    rw [dot_shift,agrees_spec.mp base u hu,annih _ im,Bool.xor_false]

theorem frequency_card {Y : Type} (c d : List Nat) (nc : c.Nodup) (nd : d.Nodup)
    (w : Nat → Form Y) (out : Form Y) (t : Y) (y0 : Assign)
    (supp : supported c y0) (base : agrees c d w out y0=true)
    (faithful : ∀ a∈cube d,∀ b∈cube d,
      TapeKernel.wire (c.map w) d a t=TapeKernel.wire (c.map w) d b t → a=b) :
    (cube c).countP (agrees c d w out)=2^(c.length-d.length) := by
  obtain ⟨zeroU,addU,sizeU⟩ := faithful_rank nc nd w t faithful
  let U := image d (slopeChart c d w)
  have hc := cardinality nc U zeroU addU
  have hp := count_shift supp (agrees c d w out)
  have sb : (fun x=>agrees c d w out (shift y0 x))=ann c U :=
    funext (shift_agrees c d w out y0 base)
  rw [sb,List.countP_eq_length_filter] at hp
  change (subgroup c (ann c U)).length=(cube c).countP (agrees c d w out) at hp
  have little : (subgroup c U).length ≤ (cube c).length := List.length_filter_le _ _
  change (subgroup c U).length=2^d.length at sizeU
  rw [sizeU,cube_size] at little
  have l := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp little
  rw [sizeU,cube_size,hp] at hc
  rw [show c.length=d.length+(c.length-d.length) from by omega,Nat.pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hc

end PEqualNP.Outside.L_meta_32580.FrequencyFlat

/- Source segment: FibreFlat. -/


namespace PEqualNP.Outside.L_meta_32580.FibreFlat
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffineImage PEqualNP.Outside.L_meta_32580.FrequencyFlat

theorem count_disjoint {A : Type} (l : List A) (f g : A → Bool)
    (none : ∀ x∈l,f x=true  →  g x=false) :
    l.countP f+l.countP g ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    have h := ih (fun x hx=>none x (List.mem_cons_of_mem _ hx))
    have r := none a List.mem_cons_self
    rw [countP_cons_add,countP_cons_add,List.length_cons]
    cases aF : f a <;> cases aG : g a <;> simp_all <;> omega

                                                                       
                                                                     
                                        
theorem at_most_half {Y : Type} {c xdom bd : List Nat} (w : Nat → Form Y) (out : Form Y)
    (pack : Assign → Assign) (u v : Assign) (uSupp : supported bd u)
    (moves : ∀ x,pack (shift u x)=shift (pack x) v)
    (not_direction : ann c (image xdom (slopeChart c xdom w)) v=false) :
    2*(cube bd).countP (fun x=>agrees c xdom w out (pack x)) ≤ (cube bd).length := by
  let p := fun x=>agrees c xdom w out (pack x)
  have none : ∀ x∈cube bd,p x=true → p (shift u x)=false := by
    intro a ha yes
    change agrees c xdom w out (pack a)=true at yes
    unfold p
    rw [moves,shift_agrees c xdom w out (pack a) yes,not_direction]
  have n := count_disjoint (cube bd) p (fun a=>p (shift u a)) none
  rw [count_shift uSupp p] at n
  change 2*(cube bd).countP p ≤ (cube bd).length
  omega

theorem pair_agreement {Y : Type} {c d : List Nat} {w : Nat → Form Y} {out : Form Y}
    {y0 y1 : Assign} (h0 : agrees c d w out y0=true) (h1 : agrees c d w out y1=true) :
    ann c (image d (slopeChart c d w)) (shift y0 y1)=true := by
  rw [←shift_agrees c d w out y0 h0,shift_invol]
  exact h1

inductive Generated (P : Assign → Prop) : Assign → Prop
  | base {x} : P x → Generated P x
  | zero : Generated P OrthogonalCount.zero
  | add {x y} : Generated P x → Generated P y → Generated P (shift x y)

theorem annihilator_span {c : List Nat} {U : Assign → Bool} (P : Assign → Prop)
    (announces : ∀ p,P p → ann c U p=true) :
    ∀ p,Generated P p → ann c U p=true := by
  intro p h
  induction h with
  | base px => exact announces _ px
  | zero => exact IsotropyCount.ann_zero c U
  | add _ _ hx hy => exact IsotropyCount.ann_add hx hy

                                                                     
                                                                 
                                                                     
theorem all_generated {Y : Type} {c d : List Nat} (w : Nat → Form Y) (out : Form Y)
    {a : Assign} (anchor : agrees c d w out a=true)
    (P : Assign → Prop) (hit : ∀ p,P p → agrees c d w out (shift a p)=true)
    {x : Assign} (hx : Generated P x) :
    agrees c d w out (shift a x)=true := by
  rw [shift_agrees c d w out a anchor]
  apply annihilator_span P _ x hx
  intro p hp
  rw [←shift_agrees c d w out a anchor]
  exact hit p hp

                                                               
                                                                 
                                                                      
theorem sum_outside {A : Type} (l : List A) (support : A → Bool) (losses : A → Nat) (n : Nat)
    (zeroScore : ∀ a∈l,support a=false → 2*losses a=n) :
    l.countP (fun a=> !(support a))*n ≤ 2*(l.map losses).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h := ih (fun b hb=>zeroScore b (List.mem_cons_of_mem _ hb))
    have z := zeroScore a List.mem_cons_self
    cases sp : support a <;> simp [sp,countP_cons_add,Nat.add_mul,Nat.mul_add] at z ⊢ <;> omega

theorem all_half_loss {A : Type} (l : List A) (support : A → Bool) (losses : A → Nat) (n : Nat)
    (cover : 2*l.countP support ≤ l.length)
    (zeroScore : ∀ a∈l,support a=false → 2*losses a=n) :
    l.length*n ≤ 4*(l.map losses).sum := by
  have r := count_complement l support
  have hc : l.length ≤ 2*l.countP (fun a=> !(support a)) := by omega
  have first := Nat.mul_le_mul_right n hc
  have second := Nat.mul_le_mul_left 2 (sum_outside l support losses n zeroScore)
  rw [Nat.mul_assoc] at first
  rw [←Nat.mul_assoc 2 2] at second
  exact Nat.le_trans first second

end PEqualNP.Outside.L_meta_32580.FibreFlat

/- Source segment: LinearExtension. -/


namespace PEqualNP.Outside.L_meta_32580.LinearExtension
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.ProjectionCount

theorem support_tail {k : Nat} {t : List Nat} {u : Assign}
    (h : supported (k::t) u) (h0 : u k=false) : supported t u := by
  intro j hj
  by_cases e : j=k
  · exact e ▸ h0
  · exact h j (fun m=>(List.mem_cons.mp m).elim e hj)

theorem support_cons {k : Nat} {t : List Nat} {u : Assign}
    (h : supported t u) (b : Bool) : supported (k::t) (put u k b) := by
  intro j hj
  have jn : j≠k := fun e=>hj (e ▸ List.mem_cons_self)
  have jt : j∉t := fun m=>hj (List.mem_cons_of_mem _ m)
  simp [put,jn,h j jt]

theorem subgroup_cons_mono {k : Nat} {t : List Nat} {U : Assign → Bool} {u : Assign}
    (h : u∈subgroup t U) : u∈subgroup (k::t) U := by
  obtain ⟨su,yes⟩ := List.mem_filter.mp h
  refine List.mem_filter.mpr ⟨mem_cube.mpr ?_,yes⟩
  exact fun j hj => mem_cube.mp su j (fun m=>hj (List.mem_cons_of_mem _ m))

theorem subgroup_tail {k : Nat} {t : List Nat} {U : Assign → Bool} {u : Assign}
    (h : u∈subgroup (k::t) U) (lo : u k=false) : u∈subgroup t U := by
  obtain ⟨supp,yes⟩ := List.mem_filter.mp h
  exact List.mem_filter.mpr ⟨mem_cube.mpr (support_tail (mem_cube.mp supp) lo),yes⟩

theorem dot_put {k : Nat} {t : List Nat} (hk : k∉t) (u a : Assign) (b : Bool) :
    dot (k::t) u (put a k b)=((u k&&b) ^^ dot t u a) := by
  unfold dot
  simp only [parity,put,ite_true]
  congr 1
  apply parity_congr
  intro j hj
  simp [show j≠k from fun e=>hk (e ▸ hj)]

theorem dot_shift_left (d : List Nat) (a b c : Assign) :
    dot d (shift a b) c=(dot d a c ^^ dot d b c) := by
  rw [dot_comm d (shift a b) c,dot_shift,dot_comm d c a,dot_comm d c b]

                                                                          
                                                                         
                                                         
theorem extend_label {d : List Nat} (nd : d.Nodup) (U : Assign → Bool)
    (U0 : U zero=true) (closed : ∀ a b,U a=true → U b=true → U (shift a b)=true)
    (label : Assign → Bool) (label0 : label zero=false)
    (linear_on : ∀ a∈subgroup d U,∀ b∈subgroup d U,
      label (shift a b)=(label a ^^ label b)) :
    ∃ a,supported d a ∧ ∀ u∈subgroup d U,dot d u a=label u := by
  induction d with
  | nil =>
    refine ⟨zero,(fun _ _=>rfl),?_⟩
    intro u hu
    have s := (List.mem_filter.mp hu).1
    change u∈[OrthogonalCount.zero] at s
    have z : u=zero := List.mem_singleton.mp s
    rw [z,label0]
    rfl
  | cons k t ih =>
    obtain ⟨kNo,tNd⟩ := List.nodup_cons.mp nd
    obtain ⟨a,sa,ea⟩ := ih tNd (fun u hu v hv=>linear_on u (subgroup_cons_mono hu) v (subgroup_cons_mono hv))
    by_cases pivot : ∃ v∈subgroup (k::t) U,v k=true
    · obtain ⟨v,hv,v1⟩ := pivot
      let bias := label v ^^ dot t v a
      refine ⟨put a k bias,support_cons sa _,?_⟩
      intro u hu
      rw [dot_put kNo]
      cases uK : u k
      · simpa only [uK,Bool.false_and,Bool.false_xor] using ea u (subgroup_tail hu uK)
      · have p := subgroup_add closed hu hv
        have cut : shift u v k=false := by simp [shift,uK,v1]
        have pe := ea (shift u v) (subgroup_tail p cut)
        rw [dot_shift_left,linear_on u hu v hv] at pe
        simp only [uK,Bool.true_and,bias]
        generalize dU : dot t u a=du at *
        generalize dV : dot t v a=dv at *
        generalize lU : label u=lu at *
        generalize lV : label v=lv at *
        cases du <;> cases dv <;> cases lu <;> cases lv <;> simp_all
    · refine ⟨put a k false,support_cons sa _,?_⟩
      intro u hu
      have low : u k=false := Bool.eq_false_iff.mpr (fun v=>pivot ⟨u,hu,v⟩)
      rw [dot_put kNo,low,Bool.false_and,Bool.false_xor]
      exact ea u (subgroup_tail hu low)

end PEqualNP.Outside.L_meta_32580.LinearExtension

/- Source segment: DualBasis. -/


namespace PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.Polarization PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffineImage PEqualNP.Outside.L_meta_32580.FrequencyFlat PEqualNP.Outside.L_meta_32580.LinearExtension

noncomputable def inverse (d : List Nat) (f : Assign → Assign) (u : Assign) : Assign := by
  classical
  exact if h : ∃ x∈cube d,f x=u then Classical.choose h else zero

theorem inverse_spec {d : List Nat} {f : Assign → Assign} {u : Assign}
    (h : image d f u=true) : inverse d f u∈cube d ∧ f (inverse d f u)=u := by
  unfold inverse
  split
  · rename_i hh
    exact Classical.choose_spec hh
  · rename_i nope
    exact False.elim (nope (image_spec.mp h))

theorem inverse_at {d : List Nat} {f : Assign → Assign}
    (inj : ∀ a∈cube d,∀ b∈cube d,f a=f b → a=b) {x : Assign} (hx : x∈cube d) :
    inverse d f (f x)=x := by
  have inv := inverse_spec (f:=f) (image_spec.mpr ⟨x,hx,rfl⟩)
  exact inj _ inv.1 x hx inv.2

                                                                       
                                                              
theorem transfer {Y : Type} {d c : List Nat} (nc : c.Nodup) (f : Assign → Assign)
    (inside : ∀ x∈cube d,supported c (f x))
    (inj : ∀ a∈cube d,∀ b∈cube d,f a=f b → a=b)
    (addF : ∀ a b,f (shift a b)=shift (f a) (f b)) (zeroF : f zero=zero)
    (out : Form Y) :
    ∃ dual,supported c dual ∧ ∀ a∈cube d,dot c (f a) dual=linear out d a := by
  classical
  let U := image d f
  let label := fun x=>linear out d (inverse d f x)
  have zeroL : label zero=false := by
    have zz := inverse_at inj (x:=zero) (mem_cube.mpr (fun _ _=>rfl))
    rw [zeroF] at zz
    simp [label,zz,linear,zero,parity_zero]
  have addL : ∀ a∈subgroup c U,∀ b∈subgroup c U,label (shift a b)=(label a ^^ label b) := by
    intro a ha b hb
    have ia := inverse_spec (List.mem_filter.mp ha).2
    have ib := inverse_spec (List.mem_filter.mp hb).2
    have ss : shift (inverse d f a) (inverse d f b)∈cube d :=
      mem_cube.mpr (IsotropyCount.add_supported (mem_cube.mp ia.1) (mem_cube.mp ib.1))
    have iz := inverse_at inj ss
    rw [addF,ia.2,ib.2] at iz
    simp [label,iz,linear_shift]
  obtain ⟨q,qs,rel⟩ := extend_label nc U (image_zero d zeroF) (image_add d addF) label zeroL addL
  refine ⟨q,qs,?_⟩
  intro a ha
  have insideU : f a∈subgroup c U :=
    List.mem_filter.mpr ⟨mem_cube.mpr (inside a ha),image_spec.mpr ⟨a,ha,rfl⟩⟩
  rw [rel _ insideU]
  simp [label,inverse_at inj ha]

theorem frequency_nonempty {Y : Type} (c d : List Nat) (nc : c.Nodup)
    (w : Nat → Form Y) (out : Form Y) (t : Y)
    (faithful : ∀ a∈cube d,∀ b∈cube d,
      TapeKernel.wire (c.map w) d a t=TapeKernel.wire (c.map w) d b t → a=b) :
    ∃ y,supported c y ∧ agrees c d w out y=true := by
  obtain ⟨y,hy,hu⟩ := transfer nc (slopeChart c d w) (fun a _=>slope_support c d w a)
    (slope_inj c d w t faithful) (slope_add c d w) (slope_zero c d w) out
  exact ⟨y,hy,agrees_spec.mpr hu⟩

def combine (d : List Nat) (g : Nat → Assign) (a : Assign) : Assign :=
  fun j=>parity (fun i=>a i && g i j) d

theorem combine_support {c d : List Nat} {g : Nat → Assign}
    (gen : ∀ i∈d,supported c (g i)) (a : Assign) : supported c (combine d g a) := by
  intro j hj
  unfold combine
  rw [←parity_zero d]
  apply parity_congr
  intro i hi
  simp [gen i hi j hj]

theorem combine_add (d : List Nat) (g : Nat → Assign) (a b : Assign) :
    combine d g (shift a b)=shift (combine d g a) (combine d g b) := by
  funext j
  unfold combine shift
  have := linear_shift (Y:=Unit) ⟨fun i=>g i j,fun _=>false⟩ d a b
  simpa [linear,shift,Bool.and_comm] using this

theorem combine_zero (d : List Nat) (g : Nat → Assign) : combine d g zero=zero := by
  funext j
  simp [combine,zero,parity_zero]

theorem linear_unit_form {Y : Type} {d : List Nat} (nd : d.Nodup) {j : Nat} (hj : j∈d) (x : Assign) :
    linear (Y:=Y) ⟨unit j,fun _=>false⟩ d x=x j := by
  change dot d (unit j) x=x j
  rw [dot_comm,dot_unit nd hj]

theorem combine_unit {d : List Nat} (nd : d.Nodup) {j : Nat} (hj : j∈d) (g : Nat → Assign) :
    combine d g (unit j)=g j := by
  funext i
  change dot d (unit j) (fun j=>g j i)=g j i
  rw [dot_comm,dot_unit nd hj]

theorem combine_dot (c d : List Nat) (g : Nat → Assign) (a y : Assign) :
    dot c (combine d g a) y=parity (fun j=>a j && dot c (g j) y) d := by
  induction d with
  | nil => exact dot_zero _ _
  | cons j t ih =>
    by_cases bit : a j=true
    · have e : combine (j::t) g a=shift (g j) (combine t g a) := by
        funext k
        simp [combine,parity,shift,bit]
      rw [e,dot_shift_left,ih]
      simp [parity,bit]
    · have b0 := Bool.eq_false_iff.mpr bit
      have e : combine (j::t) g a=combine t g a := by
        funext k
        simp [combine,parity,b0]
      rw [e,ih]
      simp [parity,b0]

theorem basis_dual {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup)
    (g : Nat → Assign) (supp : ∀ j∈d,supported c (g j))
    (ind : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    {j : Nat} (hj : j∈d) :
    ∃ dual,supported c dual ∧ ∀ a∈cube d,dot c (combine d g a) dual=a j := by
  obtain ⟨q,qs,h⟩ := transfer nc (combine d g) (fun a _=>combine_support supp a)
    ind (combine_add d g) (combine_zero d g) (Y:=Unit) ⟨unit j,fun _=>false⟩
  exact ⟨q,qs,fun a ha=>(h a ha).trans (linear_unit_form nd hj a)⟩

end PEqualNP.Outside.L_meta_32580.DualBasis

/- Source segment: AffineProjection. -/


namespace PEqualNP.Outside.L_meta_32580.AffineProjection
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffineImage PEqualNP.Outside.L_meta_32580.DualBasis PEqualNP.Outside.L_meta_32580.LinearExtension

def memberHull (d : List Nat) (basis : Nat → Assign) (anchor y : Assign) : Prop :=
  ∃ x∈cube d, y=shift anchor (combine d basis x)

def coordinates (c d : List Nat) (duals : Nat → Assign) (anchor y : Assign) : Assign :=
  fun j=>if j∈d then dot c (shift anchor y) (duals j) else false

def projectTo (c d : List Nat) (basis duals : Nat → Assign) (anchor y : Assign) : Assign :=
  shift anchor (combine d basis (coordinates c d duals anchor y))

theorem coordinates_supported (c d : List Nat) (duals : Nat → Assign) (anchor y : Assign) :
    supported d (coordinates c d duals anchor y) := by
  intro j nj
  simp [coordinates,nj]

theorem coordinates_decode {c d : List Nat} {g duals : Nat → Assign}
    (isDual : ∀ j∈d,∀ x∈cube d,dot c (combine d g x) (duals j)=x j)
    (anchor : Assign) {x : Assign} (hx : x∈cube d) :
    coordinates c d duals anchor (shift anchor (combine d g x))=x := by
  funext j
  by_cases hj : j∈d
  · simp [coordinates,hj,shift_invol,isDual j hj x hx]
  · simp [coordinates,hj,mem_cube.mp hx j hj]

theorem project_in (c d : List Nat) (g duals : Nat → Assign) (anchor y : Assign) :
    memberHull d g anchor (projectTo c d g duals anchor y) :=
  ⟨coordinates c d duals anchor y,mem_cube.mpr (coordinates_supported c d duals anchor y),rfl⟩

theorem project_hit_iff {c d : List Nat} {g duals : Nat → Assign}
    (isDual : ∀ j∈d,∀ x∈cube d,dot c (combine d g x) (duals j)=x j)
    (anchor y : Assign) :
    projectTo c d g duals anchor y=y ↔ memberHull d g anchor y := by
  constructor
  · intro eq
    exact eq ▸ project_in c d g duals anchor y
  · rintro ⟨x,hx,rfl⟩
    unfold projectTo
    rw [coordinates_decode isDual anchor hx]

theorem shift_self (a : Assign) : shift a a=zero := by
  funext j
  simp [shift,zero,Bool.xor_self]

theorem projected_pairing (c d : List Nat) (g duals : Nat → Assign) (anchor x y : Assign) :
    dot c x (projectTo c d g duals anchor y)=
      (dot c x anchor ^^ parity (fun j=>coordinates c d duals anchor y j && dot c (g j) x) d) := by
  unfold projectTo
  rw [dot_shift,dot_comm c x (combine d g _),combine_dot]

                                                                        
                                                                    
                                                                  
theorem choose_duals {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b) :
    ∃ duals : Nat → Assign,
      (∀ j∈d,supported c (duals j)) ∧
      ∀ j∈d,∀ a∈cube d,dot c (combine d g a) (duals j)=a j := by
  classical
  let duals (j : Nat) := if h : j∈d then Classical.choose (basis_dual nc nd g inside inj h) else zero
  refine ⟨duals,?_,?_⟩
  · intro j hj
    simp only [duals,dif_pos hj]
    exact (Classical.choose_spec (basis_dual nc nd g inside inj hj)).1
  · intro j hj
    simp only [duals,dif_pos hj]
    exact (Classical.choose_spec (basis_dual nc nd g inside inj hj)).2

                                                                    
                                                                     
theorem interpolate {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    (anchor : Assign) (b : Bool) (h : Nat → Bool) :
    ∃ coeff,supported c coeff ∧
      (b ^^ dot c (shift anchor anchor) coeff)=b ∧
      ∀ j∈d,(b ^^ dot c (shift anchor (shift anchor (g j))) coeff)=h j := by
  let f : Form Unit := ⟨fun j=>b ^^ h j,fun _=>false⟩
  obtain ⟨q,qs,match_⟩ := transfer nc (combine d g) (fun a _=>combine_support inside a)
    inj (combine_add d g) (combine_zero d g) f
  refine ⟨q,qs,by rw [shift_self,dot_zero,Bool.xor_false],?_⟩
  intro j hj
  rw [shift_invol]
  have e := match_ (unit j) (mem_cube.mpr (unit_supported hj))
  rw [combine_unit nd hj] at e
  change dot c (g j) q=dot d f.coeff (unit j) at e
  rw [dot_unit nd hj] at e
  rw [e]
  simp [f,←Bool.xor_assoc,Bool.xor_self]

                                                                       
                                                                       
                                                                     
theorem omit_nonanchor {d : List Nat} (nd : d.Nodup) (g : Nat → Assign)
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    (anchor : Assign) {j : Nat} (hj : j∈d) :
    ¬ memberHull (d.erase j) g anchor (shift anchor (g j)) := by
  intro inside
  obtain ⟨w,hw,eq⟩ := inside
  have ws := mem_cube.mp hw
  have wz := ws j (erase_avoids nd hj)
  have wd := (mem_cube (d:=d)).mpr (fun k nk=>ws k (fun m=>nk (List.mem_of_mem_erase m)))
  have eqW : combine d g w=combine (d.erase j) g w := by
    funext k
    unfold combine
    rw [parity_perm (List.perm_cons_erase hj),parity,wz,Bool.false_and,Bool.false_xor]
  have ww : combine d g (unit j)=combine d g w := by
    rw [combine_unit nd hj g,eqW]
    have aa := congrArg (shift anchor) eq
    simpa only [shift_invol] using aa
  have contradictionB := congrFun (inj _ (mem_cube.mpr (unit_supported hj)) _ wd ww) j
  simp [unit,wz] at contradictionB

def rebase (g : Nat → Assign) (j : Nat) (k : Nat) : Assign :=
  shift (g j) (g k)

theorem shift_assoc (a b c : Assign) : shift (shift a b) c=shift a (shift b c) := by
  funext j
  exact Bool.xor_assoc _ _ _

theorem shift_zero (a : Assign) : shift zero a=a := by
  funext j
  simp [shift,zero]

theorem erased_independent {d : List Nat} (nd : d.Nodup) (g : Nat → Assign)
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    {j : Nat} (hj : j∈d) :
    ∀ a∈cube (d.erase j),∀ b∈cube (d.erase j),
      combine (d.erase j) g a=combine (d.erase j) g b → a=b := by
  intro a ha b hb same
  have e := erase_avoids nd hj
  have general {x : Assign} (hx : x∈cube (d.erase j)) :
      x∈cube d ∧ combine d g x=combine (d.erase j) g x := by
    have xs := mem_cube.mp hx
    refine ⟨mem_cube.mpr (fun k n=>xs k (fun m=>n (List.mem_of_mem_erase m))),?_⟩
    funext k
    unfold combine
    rw [parity_perm (List.perm_cons_erase hj),parity,xs j e,Bool.false_and,Bool.false_xor]
  obtain ⟨ad,ae⟩ := general ha
  obtain ⟨bd,be⟩ := general hb
  exact inj _ ad _ bd (ae.trans (same.trans be.symm))

theorem rebased_independent {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    {j : Nat} (hj : j∈d) :
    ∀ a∈cube (d.erase j),∀ b∈cube (d.erase j),
      combine (d.erase j) (rebase g j) a=combine (d.erase j) (rebase g j) b → a=b := by
  obtain ⟨q,_,dual⟩ := choose_duals nc nd g inside inj
  have elem {i k : Nat} (hi : i∈d) (hk : k∈d) :
      dot c (g i) (q k)=unit i k := by
    have hk0 := dual k hk (unit i) (mem_cube.mpr (unit_supported hi))
    rwa [combine_unit nd hi] at hk0
  intro a ha b hb same
  funext k
  by_cases hk : k∈d.erase j
  · have kj : k≠j := fun e=>erase_avoids nd hj (e ▸ hk)
    have ne0 : unit j k=false := by simp [unit,kj]
    have dotNew (x : Assign) :
        dot c (combine (d.erase j) (rebase g j) x) (q k)=x k := by
      rw [combine_dot]
      have eq : parity (fun i=>x i && dot c (rebase g j i) (q k)) (d.erase j)=
          parity (fun i=>x i && unit k i) (d.erase j) := by
        apply parity_congr
        intro i hi
        rw [rebase,dot_shift_left,elem hj (List.mem_of_mem_erase hk),
          elem (List.mem_of_mem_erase hi) (List.mem_of_mem_erase hk),ne0,Bool.false_xor]
        have e : unit i k=unit k i := by simp [unit,eq_comm]
        rw [e]
      rw [eq]
      exact dot_unit (nd.erase j) hk x
    rw [←dotNew a,←dotNew b,same]
  · rw [mem_cube.mp ha k hk,mem_cube.mp hb k hk]

                                                                          
                                                                      
theorem omit_anchor {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    (anchor : Assign) {j : Nat} (hj : j∈d) :
    ¬ memberHull (d.erase j) (rebase g j) (shift anchor (g j)) anchor := by
  obtain ⟨q,_,_,dots⟩ := interpolate nc nd g inside inj anchor false (fun _=>true)
  have dot_g : ∀ i∈d,dot c (g i) q=true := by
    intro i hi
    simpa only [shift_invol,Bool.false_xor] using dots i hi
  rintro ⟨w,hw,eq⟩
  have part : combine (d.erase j) (rebase g j) w=g j := by
    have ex := congrArg (shift anchor) eq
    rw [shift_self,shift_assoc,shift_invol] at ex
    have jn := congrArg (shift (g j)) ex
    rw [shift_invol] at jn
    simpa only [shift_comm (g j) zero,shift_zero] using jn.symm
  have all : dot c (combine (d.erase j) (rebase g j) w) q=false := by
    rw [combine_dot,←parity_zero (d.erase j)]
    apply parity_congr
    intro i hi
    rw [rebase,dot_shift_left,dot_g j hj,dot_g i (List.mem_of_mem_erase hi)]
    simp
  rw [part,dot_g j hj] at all
  contradiction

end PEqualNP.Outside.L_meta_32580.AffineProjection

/- Source segment: ComposedPhase. -/


namespace PEqualNP.Outside.L_meta_32580.ComposedPhase
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.Translation
open PEqualNP.Outside.L_meta_32580.Polarization PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.FrequencyFlat

abbrev PortPair (Y : Type) := Form Y × Form Y

def pairsEval {I Y : Type} (d : List Nat) (form : I → PortPair Y) (weight : I → Bool) (ts : List I)
    (x : Assign) (s : Y) : Bool := match ts with
  | [] => false
  | t::tail => (weight t && (value (form t).1 d x s && value (form t).2 d x s)) ^^ pairsEval d form weight tail x s

def pairsPolar {I Y : Type} (d : List Nat) (form : I → PortPair Y) (weight : I → Bool) (ts : List I)
    (u v : Assign) : Bool := match ts with
  | [] => false
  | t::tail => (weight t && productPolar (form t).1 (form t).2 d u v) ^^ pairsPolar d form weight tail u v

theorem rect_pairs {I Y : Type} (d : List Nat) (form : I → PortPair Y) (weight : I → Bool) (ts : List I)
    (u v x : Assign) (s : Y) :
    rectangle (fun x=>pairsEval d form weight ts x s) u v x=pairsPolar d form weight ts u v := by
  induction ts with
  | nil => rfl
  | cons j t ih =>
    simp only [pairsEval,pairsPolar,rectangle_xor,ih]
    exact congrArg (fun b=>b ^^ pairsPolar d form weight t u v)
      (weighted_product_rect (form j).1 (form j).2 (fun _=>weight j) d u v x s)

theorem polar_add {I Y : Type} (d : List Nat) (form : I → PortPair Y) (w1 w2 : I → Bool) (ts : List I)
    (u v : Assign) :
    pairsPolar d form (fun p=>w1 p ^^ w2 p) ts u v =
      (pairsPolar d form w1 ts u v ^^ pairsPolar d form w2 ts u v) := by
  induction ts with
  | nil => rfl
  | cons a t ih =>
    simp only [pairsPolar,ih]
    cases w1 a <;> cases w2 a <;> cases productPolar (form a).1 (form a).2 d u v <;>
      cases pairsPolar d form w1 t u v <;> cases pairsPolar d form w2 t u v <;> decide

theorem dot_pairs {Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (x : Assign) (s : Y) :
    dot c (affineChart c d xs x s) (affineChart c d ys x s)=
      pairsEval d (fun j=>(xs j,ys j)) (fun _=>true) c x s := by
  have eq :
     dot c (affineChart c d xs x s) (affineChart c d ys x s)=
       parity (fun j=> value (xs j) d x s && value (ys j) d x s) c := by
    unfold dot
    apply parity_congr
    intro j hj
    simp [affineChart,hj]
  rw [eq]
  clear eq
  induction c with
  | nil => rfl
  | cons j t ih =>
    simp only [parity,pairsEval,Bool.true_and,ih]

def scorePhase {I Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (out : Form Y)
    (cols : List I) (form : I → PortPair Y) (word : Y → I → Bool)
    (x : Assign) (s : Y) : Bool :=
  value out d x s ^^
    (dot c (affineChart c d xs x s) (affineChart c d ys x s) ^^ pairsEval d form (word s) cols x s)

def fixedPolar {Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (u v : Assign) : Bool :=
  pairsPolar d (fun j=>(xs j,ys j)) (fun _=>true) c u v

                                                                    
                                                                        
                                                              
theorem score_rect {I Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (out : Form Y)
    (cols : List I) (form : I → PortPair Y) (word : Y → I → Bool)
    (u v x : Assign) (s : Y) :
    rectangle (fun x=>scorePhase c d xs ys out cols form word x s) u v x=
      (fixedPolar c d xs ys u v ^^ pairsPolar d form (word s) cols u v) := by
  have equal : (fun x=>scorePhase c d xs ys out cols form word x s) =
      (fun x=>value out d x s ^^ (pairsEval d (fun j=>(xs j,ys j)) (fun _=>true) c x s ^^ pairsEval d form (word s) cols x s)) := by
    funext x
    rw [scorePhase,dot_pairs]
  rw [equal,rectangle_xor,affine_zero_rect,Bool.false_xor,rectangle_xor,rect_pairs,rect_pairs]
  rfl

def good {I Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (cols : List I)
    (form : I → PortPair Y) (word : Y → I → Bool) (s : Y) : Prop :=
  ∀ u∈cube d,∀ v∈cube d,(fixedPolar c d xs ys u v ^^ pairsPolar d form (word s) cols u v)=false

theorem common_isotropy {I Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (cols : List I)
    (form : I → PortPair Y) (word : Y → I → Bool) (s t : Y)
    (s0 : good c d xs ys cols form word s) (t0 : good c d xs ys cols form word t)
    (u v : Assign) (hu : u∈cube d) (hv : v∈cube d) :
    pairsPolar d form (fun a=>word s a ^^ word t a) cols u v=false := by
  rw [polar_add]
  have se := s0 u hu v hv
  have te := t0 u hu v hv
  generalize h : fixedPolar c d xs ys u v=a at *
  generalize j : pairsPolar d form (word s) cols u v=b at *
  generalize k : pairsPolar d form (word t) cols u v=c at *
  cases a <;> cases b <;> cases c <;> simp_all

theorem bad_quarter {I Y : Type} (c d : List Nat) (xs ys : Nat → Form Y) (out : Form Y)
    (cols : List I) (form : I → PortPair Y) (word : Y → I → Bool) (s : Y)
    (bad : ¬good c d xs ys cols form word s) :
    (cube d).length ≤ 4*(cube d).countP (fun x=>scorePhase c d xs ys out cols form word x s) := by
  classical
  have ex : ∃ u∈cube d,∃ v∈cube d,
      (fixedPolar c d xs ys u v ^^ pairsPolar d form (word s) cols u v)=true := by
    apply Classical.byContradiction
    intro no
    apply bad
    intro u hu v hv
    exact Bool.eq_false_iff.mpr (fun h=>no ⟨u,hu,v,hv,h⟩)
  obtain ⟨u,hu,v,hv,wit⟩ := ex
  apply at_least_quarter (CubeGeometry.mem_cube.mp hu) (CubeGeometry.mem_cube.mp hv)
  intro x
  change rectangle (fun t=>scorePhase c d xs ys out cols form word t s) u v x=true
  rw [score_rect,wit]

end PEqualNP.Outside.L_meta_32580.ComposedPhase

/- Source segment: PairSlots. -/


namespace PEqualNP.Outside.L_meta_32580.PairSlots
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.ComposedPhase
open PEqualNP.Outside.L_meta_32580.AffineImage PEqualNP.Outside.L_meta_32580.ProjectionCount PEqualNP.Outside.L_meta_32580.Polarization
open PEqualNP.Outside.L_meta_32580.ClippingInjection (clip)

def left (i : Nat) := 2*i
def right (i : Nat) := 2*i+1
def pairCoordinates (I : List Nat) := I.flatMap (fun i=>[left i,right i])
def pairIndex (j : Nat) := j/2
def mate (j : Nat) := if j % 2=0 then j+1 else j-1
def swap (a : Assign) : Assign := fun j=>a (mate j)
def mask (w : Nat → Bool) : Assign := fun j=>w (pairIndex j)

theorem mate_left (i : Nat) : mate (left i)=right i := by
  unfold mate left right
  have e : 2*i % 2=0 := by omega
  simp [e]

theorem mate_right (i : Nat) : mate (right i)=left i := by
  unfold mate left right
  have e : (2*i+1) % 2≠0 := by omega
  simp [e]

theorem pairIndex_left (i : Nat) : pairIndex (left i)=i := by
  unfold pairIndex left
  omega

theorem pairIndex_right (i : Nat) : pairIndex (right i)=i := by
  unfold pairIndex right
  omega

theorem slot_either (j : Nat) : j=left (pairIndex j) ∨ j=right (pairIndex j) := by
  unfold left right pairIndex
  omega

theorem mate_invol (j : Nat) : mate (mate j)=j := by
  obtain h|h := slot_either j
  · rw [h,mate_left,mate_right]
  · rw [h,mate_right,mate_left]

theorem pairIndex_mate (j : Nat) : pairIndex (mate j)=pairIndex j := by
  obtain h|h := slot_either j
  · rw [h,mate_left,pairIndex_right,pairIndex_left]
  · rw [h,mate_right,pairIndex_left,pairIndex_right]

theorem mem_pairCoordinates {I : List Nat} {j : Nat} :
    j∈pairCoordinates I ↔ pairIndex j∈I := by
  constructor
  · rintro h
    obtain ⟨i,hi,q⟩ := List.mem_flatMap.mp h
    rcases (show j=left i∨j=right i by simpa using q) with rfl|rfl
    · rwa [pairIndex_left]
    · rwa [pairIndex_right]
  · intro h
    refine List.mem_flatMap.mpr ⟨pairIndex j,h,?_⟩
    exact List.mem_cons.mpr ((slot_either j).imp_right (fun eq=>List.mem_singleton.mpr eq))

theorem swap_support {I : List Nat} (a : Assign) (s : supported (pairCoordinates I) a) :
    supported (pairCoordinates I) (swap a) := by
  intro j hj
  apply s (mate j)
  rwa [mem_pairCoordinates,pairIndex_mate,←mem_pairCoordinates]

theorem swap_zero : swap zero=zero := rfl

theorem swap_add (a b : Assign) : swap (shift a b)=shift (swap a) (swap b) := rfl

theorem swap_inj (a b : Assign) (eq : swap a=swap b) : a=b := by
  funext j
  have q := congrFun eq (mate j)
  change a (mate (mate j))=b (mate (mate j)) at q
  rwa [mate_invol] at q

theorem pair_length (I : List Nat) : (pairCoordinates I).length=2*I.length := by
  induction I with
  | nil => rfl
  | cons i t ih =>
    change ([left i,right i]++pairCoordinates t).length=2*(i::t).length
    simp [ih]
    omega

theorem mask_left (w : Nat → Bool) (i : Nat) : mask w (left i)=w i := by
  unfold mask
  rw [pairIndex_left]

theorem mask_right (w : Nat → Bool) (i : Nat) : mask w (right i)=w i := by
  unfold mask
  rw [pairIndex_right]

theorem pair_cons (i : Nat) (t : List Nat) :
    pairCoordinates (i::t)=[left i,right i]++pairCoordinates t := rfl

theorem filter_pair (I : List Nat) (w : Nat → Bool) :
    (pairCoordinates I).filter (mask w)=pairCoordinates (I.filter w) := by
  induction I with
  | nil => rfl
  | cons i t ih =>
    cases g : w i <;> simp [pair_cons,mask_left,mask_right,g,ih]

def hyperbolic (I : List Nat) (w : Nat → Bool) (x y : Assign) : Bool :=
  parity (fun i=>w i && ((x (left i) && y (right i)) ^^ (x (right i) && y (left i)))) I

theorem hyperbolic_filter {I : List Nat} {active diff : Nat → Bool} (x y : Assign)
    (covers : ∀ i∈I,diff i=true → active i=true) :
    hyperbolic (I.filter active) diff x y=hyperbolic I diff x y := by
  induction I with
  | nil => rfl
  | cons i t ih =>
    have tail := ih (fun k hk=>covers k (List.mem_cons_of_mem _ hk))
    cases z : active i
    · have zeroD : diff i=false :=
        Bool.eq_false_iff.mpr (fun hh=>by have hit:=covers i List.mem_cons_self hh; simp [z] at hit)
      simp [hyperbolic,z,parity,zeroD] at tail ⊢
      exact tail
    · simp [hyperbolic,z,parity] at tail ⊢
      rw [tail]

                                                                      
                                                                      
                                                                       
theorem dot_swapped (I : List Nat) (active diff : Nat → Bool) (x y : Assign)
    (covers : ∀ i∈I,diff i=true → active i=true) :
    dot (pairCoordinates (I.filter active)) (clip (mask active) y)
      (swap (clip (mask diff) (clip (mask active) x)))=hyperbolic I diff x y := by
  rw [←hyperbolic_filter x y covers]
  have scope : ∀ i∈I.filter active,active i=true := fun _ h=>(List.mem_filter.mp h).2
  generalize hh : I.filter active=on at *
  clear hh covers
  induction on with
  | nil => rfl
  | cons i t ih =>
    have trueA := scope i List.mem_cons_self
    have tail := ih (fun j hj=>scope j (List.mem_cons_of_mem _ hj))
    change dot ([left i,right i]++pairCoordinates t) (clip (mask active) y)
      (swap (clip (mask diff) (clip (mask active) x)))=hyperbolic (i::t) diff x y
    unfold hyperbolic at tail ⊢
    change ((_&&_) ^^ ((_&&_) ^^ dot (pairCoordinates t) _ _))=_
    rw [tail]
    simp only [parity,clip,swap,mate_left,mate_right,mask_left,mask_right,trueA,Bool.true_and]
    generalize hD : diff i=a
    generalize hL : x (left i)=b
    generalize hR : x (right i)=c
    generalize hyL : y (left i)=d
    generalize hyR : y (right i)=e
    generalize tailBit : parity (fun i=>diff i &&
      ((x (left i) && y (right i)) ^^ (x (right i) && y (left i)))) t=z
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases z <;> decide

theorem form_hyperbolic {Y : Type} (I c d : List Nat) (obs : Nat → Form Y) (w : Nat → Bool)
    (u v : Assign) (scope : ∀ i∈I,left i∈c ∧ right i∈c) :
    pairsPolar d (fun i=>(obs (left i),obs (right i))) w I u v=
      hyperbolic I w (slopeChart c d obs u) (slopeChart c d obs v) := by
  unfold hyperbolic
  induction I with
  | nil => rfl
  | cons i t ih =>
    obtain ⟨lo,hi⟩ := scope i List.mem_cons_self
    have tail := ih (fun j hj=>scope j (List.mem_cons_of_mem _ hj))
    simp only [pairsPolar,parity,productPolar,slopeChart,lo,hi,ite_true,tail]
    have q (a b c d : Bool) : (a&&b ^^ c&&d)=(a&&b ^^ d&&c) := by
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
    rw [q]

end PEqualNP.Outside.L_meta_32580.PairSlots

/- Source segment: ColumnObstruction. -/


namespace PEqualNP.Outside.L_meta_32580.ColumnObstruction
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.AffineImage
open PEqualNP.Outside.L_meta_32580.ProjectionCount PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.ComposedPhase

noncomputable def varying {Y : Type} (E : List Y) (word : Y → Nat → Bool) (i : Nat) : Bool :=
  @decide (∃ s∈E,∃ t∈E,word s i≠word t i) (Classical.propDecidable _)

theorem varies {Y : Type} {E : List Y} {word : Y → Nat → Bool} {i : Nat} :
    varying E word i=true ↔ ∃ s∈E,∃ t∈E,word s i≠word t i := by
  simp only [varying,decide_eq_true_eq]

theorem vary_from {Y : Type} {E : List Y} {word : Y → Nat → Bool} {a : Y} (ha : a∈E) (i : Nat) :
    varying E word i=true ↔ ∃ s∈E,word a i≠word s i := by
  rw [varies]
  constructor
  · rintro ⟨s,hs,t,ht,diff⟩
    by_cases eq : word a i=word s i
    · exact ⟨t,ht,fun e=>diff (eq.symm.trans e)⟩
    · exact ⟨s,hs,eq⟩
  · rintro ⟨s,hs,diff⟩
    exact ⟨a,ha,s,hs,diff⟩

theorem xor_neq {a b : Bool} : (a ^^ b)=true ↔ a≠b := by cases a <;> cases b <;> decide

theorem fewer {I : Type} (x y : I → Bool) (l : List I)
    (count : l.countP x < l.countP y) : ∃ i∈l,y i=true ∧ x i=false := by
  classical
  apply Classical.byContradiction
  intro none
  have leFor : ∀ i∈l,y i=true → x i=true := by
    intro i hi h
    cases he : x i
    · exact False.elim (none ⟨i,hi,h,he⟩)
    · rfl
  have mono : ∀ l : List I,(∀ i∈l,y i=true → x i=true) → l.countP y ≤ l.countP x := by
    intro l
    induction l with
    | nil => intro; simp
    | cons i t ih =>
      intro h
      have r := ih (fun j hj=>h j (List.mem_cons_of_mem _ hj))
      have a := h i List.mem_cons_self
      rw [countP_cons_add,countP_cons_add]
      cases xi : x i <;> cases yi : y i <;> simp_all <;> omega
  exact (Nat.not_lt_of_ge (mono l leFor)) count

theorem active_coords {c I extra : List Nat} (layout : c=pairCoordinates I++extra)
    (noExtra : ∀ j∈extra,pairIndex j∉I) (active : Nat → Bool)
    (activeScope : ∀ i,active i=true → i∈I) :
    c.filter (mask active)=pairCoordinates (I.filter active) := by
  rw [layout,List.filter_append,filter_pair]
  have zz : extra.filter (mask active)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj yes
    exact noExtra _ hj (activeScope _ yes)
  rw [zz,List.append_nil]

theorem active_coords' {c I extra : List Nat} (layout : c=pairCoordinates I++extra)
    (noExtra : ∀ j∈extra,pairIndex j∉I) (active : Nat → Bool) :
    c.filter (mask (fun i=>decide (i∈I) && active i))=pairCoordinates (I.filter active) := by
  have F : I.filter (fun i=>decide (i∈I) && active i)=I.filter active := by
    apply List.filter_congr
    intro i hi
    simp [hi]
  rw [active_coords layout noExtra (fun i=>decide (i∈I)&&active i) (by
    intro i h
    exact decide_eq_true_eq.mp ((Bool.and_eq_true_iff.mp h).1))]
  rw [F]

                                                                    
                                                                   
                                                                     
theorem column_failure {Y : Type} (E : List Y) (I c extra d loc : List Nat)
    (nc : c.Nodup) (nd : d.Nodup)
    (layout : c=pairCoordinates I++extra) (noExtra : ∀ j∈extra,pairIndex j∉I)
    (raw : Nat → Form Y) (xs ys : Nat → Form Y) (out : Form Y) (word : Y → Nat → Bool)
    (sel : Y) (faithful : ∀ a∈cube d,∀ b∈cube d,
      TapeKernel.wire (c.map raw) d a sel=TapeKernel.wire (c.map raw) d b sel → a=b)
    (cuts : Nat) (freeEnough : c.length-cuts ≤ d.length) (short : cuts<I.countP (varying E word)) :
    let form := fun i=>(raw (left i),raw (right i))
    ∃ i∈I, varying E word i=true ∧ ∃ bias : Bool,∀ s∈E,word s i≠bias → 
      (cube d).length ≤ 4*(cube d).countP (fun x=>scorePhase loc d xs ys out I form word x s) := by
  classical
  let form := fun i=>(raw (left i),raw (right i))
  let isGood := good loc d xs ys I form word
  let G := E.filter (fun s=>decide (isGood s))
  have gSpec (s : Y) : s∈G ↔ s∈E ∧ isGood s := by simp [G]
  have slotScope : ∀ i∈I,left i∈c ∧ right i∈c := by
    intro i hi
    exact ⟨by rw [layout]; exact List.mem_append_left _ (mem_pairCoordinates.mpr (by simpa [pairIndex_left])),
      by rw [layout]; exact List.mem_append_left _ (mem_pairCoordinates.mpr (by simpa [pairIndex_right]))⟩
  by_cases ex : ∃ s,s∈G
  · obtain ⟨s0,hs0⟩ := ex
    let va := varying G word
    let chosen (i : Nat) := decide (i∈I) && va i
    let maskG := mask chosen
    let U := image d (slopeChart c d raw)
    let masks := G.map (fun s=>mask (fun i=>word s0 i ^^ word s i))
    obtain ⟨z,cl,Usize⟩ := faithful_rank nc nd raw sel faithful
    have coord : c.filter maskG=pairCoordinates (I.filter va) :=
      active_coords' layout noExtra va
    have cardA : (c.filter maskG).length=2*(I.countP va) := by
      rw [coord,pair_length,List.countP_eq_length_filter]
    have nottoo : I.countP va ≤ cuts := by
      refine active_codimension nc U z cl maskG _ _ cardA ?_ swap swap_add swap_zero ?_
        (fun a b _ _=>swap_inj a b) masks ?_ ?_
      · change _ ≤ (subgroup c U).length
        change (subgroup c U).length=2^d.length at Usize
        rw [Usize]
        exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mpr freeEnough
      · rw [coord]
        exact swap_support
      · intro j hj
        have hj' : pairIndex j∈I.filter va := mem_pairCoordinates.mp (coord ▸ hj)
        have on := (List.mem_filter.mp hj').2
        obtain ⟨s,hs,neq⟩ := (vary_from hs0 _).mp on
        refine ⟨mask (fun i=>word s0 i ^^ word s i),List.mem_map_of_mem hs,?_⟩
        unfold mask
        exact xor_neq.mpr neq
      · intro q hq a ha b hb
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
        obtain ⟨u,hu,rfl⟩ := image_spec.mp (List.mem_filter.mp ha).2
        obtain ⟨v,hv,rfl⟩ := image_spec.mp (List.mem_filter.mp hb).2
        let diff := fun i=>word s0 i ^^ word s i
        have diag : ∀ i∈I,diff i=true → chosen i=true := by
          intro i hi h
          have neq : word s0 i≠word s i := xor_neq.mp h
          have var : va i=true := (vary_from hs0 i).mpr ⟨s,hs,neq⟩
          simp [chosen,hi,var]
        have activeEq : I.filter chosen=I.filter va := by
          apply List.filter_congr
          intro i hi
          simp [chosen,hi]
        change dot (c.filter maskG) (ClippingInjection.clip maskG (slopeChart c d raw v))
          (swap (ClippingInjection.clip (mask diff)
            (ClippingInjection.clip maskG (slopeChart c d raw u))))=false
        rw [coord,←activeEq]
        change dot (pairCoordinates (I.filter chosen)) (ClippingInjection.clip (mask chosen) _)
          (swap (ClippingInjection.clip (mask diff) (ClippingInjection.clip (mask chosen) _)))=false
        rw [dot_swapped I chosen diff _ _ diag,←form_hyperbolic I c d raw diff u v slotScope]
        exact common_isotropy loc d xs ys I form word s0 s ((gSpec _).mp hs0).2
          ((gSpec _).mp hs).2 u v hu hv
    obtain ⟨i,hi,vi,notG⟩ := fewer va (varying E word) I (Nat.lt_of_le_of_lt nottoo short)
    refine ⟨i,hi,vi,word s0 i,?_⟩
    intro s he mismatch
    apply bad_quarter
    intro hg
    have hs := (gSpec s).mpr ⟨he,hg⟩
    have would : va i=true := (vary_from hs0 i).mpr ⟨s,hs,Ne.symm mismatch⟩
    rw [notG] at would
    contradiction
  · have p : 0<I.countP (varying E word) := Nat.lt_of_le_of_lt (Nat.zero_le cuts) short
    obtain ⟨i,hi,vary⟩ := List.countP_pos_iff.mp p
    refine ⟨i,hi,vary,false,?_⟩
    intro s hs _
    apply bad_quarter
    intro h
    exact ex ⟨s,(gSpec s).mpr ⟨hs,h⟩⟩

end PEqualNP.Outside.L_meta_32580.ColumnObstruction

/- Source segment: FrequencySplit. -/


namespace PEqualNP.Outside.L_meta_32580.FrequencySplit
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.AffineImage
open PEqualNP.Outside.L_meta_32580.FrequencyFlat PEqualNP.Outside.L_meta_32580.FibreFlat PEqualNP.Outside.L_meta_32580.DualBasis PEqualNP.Outside.L_meta_32580.AffineProjection

                                                                    
                                                                      
                                          
theorem frequency_cases {Y S : Type} {c xd bd : List Nat} (w : Nat → Form Y) (out : Form Y)
    (E : List S) (pack : S → Assign → Assign) (directions : Assign → Assign)
    (moves : ∀ s u x,pack s (shift u x)=shift (pack s x) (directions u)) :
    (∃ s∈E,∀ x∈cube bd,agrees c xd w out (pack s x)=false) ∨
    (∀ s∈E,2*(cube bd).countP (fun x=>agrees c xd w out (pack s x)) ≤ (cube bd).length) ∨
    (∀ s∈E,∀ x∈cube bd,agrees c xd w out (pack s x)=true) := by
  classical
  let U := image xd (slopeChart c xd w)
  by_cases miss : ∃ s∈E,∀ x∈cube bd,agrees c xd w out (pack s x)=false
  · exact .inl miss
  right
  by_cases escape : ∃ u∈cube bd,ann c U (directions u)=false
  · left
    intro s _
    obtain ⟨u,hu,no⟩ := escape
    exact at_most_half w out (pack s) u (directions u) (mem_cube.mp hu) (moves s u) no
  · right
    intro s hs x hx
    have meet : ∃ y∈cube bd,agrees c xd w out (pack s y)=true := by
      apply Classical.byContradiction
      intro no
      exact miss ⟨s,hs,fun y hy=>Bool.eq_false_iff.mpr (fun h=>no ⟨y,hy,h⟩)⟩
    obtain ⟨y,hy,hit⟩ := meet
    let u := shift y x
    have hu : u∈cube bd :=
      mem_cube.mpr (IsotropyCount.add_supported (mem_cube.mp hy) (mem_cube.mp hx))
    have good : ann c U (directions u)=true := by
      cases h : ann c U (directions u)
      · exact False.elim (escape ⟨u,hu,h⟩)
      · rfl
    have test := shift_agrees c xd w out (pack s y) hit (directions u)
    rw [←moves] at test
    have eq : shift u y=x := by
      dsimp [u]
      rw [shift_comm (shift y x) y,shift_invol]
    rwa [eq,good] at test

theorem generated_combine (d : List Nat) (g : Nat → Assign) (x : Assign) (P : Assign → Prop)
    (scope : ∀ i∈d,P (g i)) : Generated P (combine d g x) := by
  induction d with
  | nil => exact .zero
  | cons j t ih =>
    have tail := ih (fun i hi=>scope i (List.mem_cons_of_mem _ hi))
    cases h : x j
    · have same : combine (j::t) g x=combine t g x := by
        funext k
        simp [combine,parity,h]
      rwa [same]
    · have same : combine (j::t) g x=shift (g j) (combine t g x) := by
        funext k
        simp [combine,parity,shift,h]
      rw [same]
      exact .add (.base (scope _ List.mem_cons_self)) tail

                                                                      
                                                                        
                                                                      
                                                                      
theorem hull_cost {Y : Type} {c xd hd : List Nat} (nc : c.Nodup) (xdNd : xd.Nodup) (hdNd : hd.Nodup)
    (w : Nat → Form Y) (out : Form Y) (sample : Y)
    (faithful : ∀ a∈cube xd,∀ b∈cube xd,
      TapeKernel.wire (c.map w) xd a sample=TapeKernel.wire (c.map w) xd b sample → a=b)
    (y0 : Assign) (hasY : supported c y0) (hitY : agrees c xd w out y0=true)
    (g : Nat → Assign) (hasG : ∀ i∈hd,supported c (g i))
    (hitG : ∀ i∈hd,agrees c xd w out (shift y0 (g i))=true)
    (ind : ∀ a∈cube hd,∀ b∈cube hd,combine hd g a=combine hd g b → a=b) :
    hd.length ≤ c.length-xd.length := by
  let F := (cube c).filter (agrees c xd w out)
  let embed := fun x=>shift y0 (combine hd g x)
  have eInj : ∀ a∈cube hd,∀ b∈cube hd,embed a=embed b → a=b := by
    intro a ha b hb esp
    apply ind a ha b hb
    have p := congrArg (shift y0) esp
    simpa only [embed,shift_invol] using p
  have p := nodup_map_from (cube hd) (cube_nodup hdNd) embed eInj
  have sub : (cube hd).map embed ⊆ F := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    apply List.mem_filter.mpr
    refine ⟨mem_cube.mpr (IsotropyCount.add_supported hasY (combine_support hasG a)),?_⟩
    apply all_generated w out hitY (fun y=>∃ i∈hd,g i=y)
    · rintro y ⟨i,hi,rfl⟩
      exact hitG i hi
    · exact generated_combine hd g a _ (fun i hi=>⟨i,hi,rfl⟩)
  have small := List.Nodup.length_le_of_subset p sub
  rw [List.length_map,cube_size] at small
  change 2^hd.length ≤ ((cube c).filter (agrees c xd w out)).length at small
  rw [←List.countP_eq_length_filter,frequency_card c xd nc xdNd w out sample y0 hasY hitY faithful] at small
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp small

end PEqualNP.Outside.L_meta_32580.FrequencySplit

/- Source segment: CountProfile. -/


namespace PEqualNP.Outside.L_meta_32580.CountProfile
open PEqualNP.Outside.L_meta_32580.ColumnObstruction

structure Leaf (Y : Type) where
  mass : Nat
  errors : Y → Nat

def total {Y : Type} (E : List Y) (v : Leaf Y) : Nat := (E.map v.errors).sum

inductive Obstruction {Y : Type} (E : List Y) (I : List Nat) (word : Y → Nat → Bool) (v : Leaf Y) : Prop
  | missed {s} : s∈E  →  v.mass ≤ 2*v.errors s  →  Obstruction E I word v
  | allHalf : (∀ s∈E,v.mass ≤ 4*v.errors s)  →  Obstruction E I word v
  | column {i bias} : i∈I → varying E word i=true → 
      (∀ s∈E,word s i≠bias → v.mass ≤ 4*v.errors s) → Obstruction E I word v

theorem sum_ge {Y : Type} (E : List Y) (f : Y → Nat) {s : Y} (hs : s∈E) :
    f s ≤ (E.map f).sum := by
  induction E with
  | nil => simp at hs
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hs with rfl|ht
    · omega
    · have k := ih ht
      omega

theorem sum_ge_two {Y : Type} (E : List Y) (f : Y → Nat) {s t : Y}
    (hs : s∈E) (ht : t∈E) (ne : s≠t) :
    f s+f t ≤ (E.map f).sum := by
  induction E with
  | nil => simp at hs
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hs with h|hsl
    · subst a
      have ht0 := (List.mem_cons.mp ht).resolve_left (Ne.symm ne)
      have rr := sum_ge l f ht0
      omega
    · rcases List.mem_cons.mp ht with h|ht
      · subst a
        have ss := sum_ge l f hsl
        omega
      · have bb := ih hsl ht
        omega

theorem two_members {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length) :
    ∃ s∈E, ∃ t∈E,s≠t := by
  cases E with
  | nil => simp at len
  | cons s l =>
    cases l with
    | nil => simp at len
    | cons t l =>
      refine ⟨s,List.mem_cons_self,t,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
      intro same
      exact (List.nodup_cons.mp nd).1 (same.symm ▸ List.mem_cons_self)

theorem varying_mismatches {Y : Type} {E : List Y} {word : Y → Nat → Bool} {i : Nat}
    (var : varying E word i=true) (bias : Bool) :
    ∃ s∈E,word s i≠bias := by
  obtain ⟨s,hs,t,ht,neq⟩ := varies.mp var
  by_cases eq : word s i=bias
  · exact ⟨t,ht,fun e=>neq (eq.trans e.symm)⟩
  · exact ⟨s,hs,eq⟩

theorem uniform_leaf {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    {I : List Nat} {word : Y → Nat → Bool} {v : Leaf Y}
    (cert : Obstruction E I word v) :
    v.mass ≤ 4*total E v := by
  cases cert with
  | @missed s hs large =>
    have e := sum_ge E v.errors hs
    unfold total
    omega
  | allHalf p =>
    obtain ⟨s,hs,_,_,_⟩ := two_members nd len
    have h := p s hs
    have e := sum_ge E v.errors hs
    unfold total
    omega
  | @column i bias hi var p =>
    obtain ⟨s,hs,no⟩ := varying_mismatches var bias
    have h := p s hs no
    have e := sum_ge E v.errors hs
    unfold total
    omega

                                                                        
                                                                      
                                                                 
theorem equality_leaf {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    {I : List Nat} {word : Y → Nat → Bool} {v : Leaf Y} (pos : 0<v.mass)
    (cert : Obstruction E I word v) (eq : v.mass=4*total E v) :
    ∃ s∈E,∃ i∈I,∃ b : Bool, v.mass=4*v.errors s ∧
      ∀ t∈E, (word t i≠b ↔ t=s) ∧ (t≠s → v.errors t=0) := by
  cases cert with
  | @missed s hs large =>
    have e := sum_ge E v.errors hs
    unfold total at eq
    omega
  | allHalf p =>
    obtain ⟨s,hs,t,ht,ne⟩ := two_members nd len
    have sLarge := p s hs
    have tLarge := p t ht
    have e := sum_ge_two E v.errors hs ht ne
    unfold total at eq
    omega
  | @column i bias hi var p =>
    obtain ⟨s,hs,mis⟩ := varying_mismatches var bias
    have each := p s hs mis
    have e := sum_ge E v.errors hs
    have sx : v.mass=4*v.errors s := by unfold total at eq; omega
    refine ⟨s,hs,i,hi,bias,sx,?_⟩
    intro t ht
    have zeros (ne : t≠s) : v.errors t=0 := by
      have score := sum_ge_two E v.errors hs ht (Ne.symm ne)
      unfold total at eq
      omega
    refine ⟨⟨?_,?_⟩,zeros⟩
    · intro no
      apply Classical.byContradiction
      intro ne
      have h := p t ht no
      rw [zeros ne] at h
      omega
    · intro choice
      simpa [choice] using mis

theorem sum_total {Y : Type} (E : List Y) (v : List (Leaf Y)) :
    (v.map (total E)).sum=(E.map (fun y=>(v.map (fun a=>a.errors y)).sum)).sum := by
  induction v with
  | nil =>
    induction E with
    | nil => rfl
    | cons _ t ih =>
      change 0=(t.map (fun _=>0)).sum at ih
      change 0=0+(t.map (fun _=>0)).sum
      rw [←ih]
      rfl
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [OrthogonalCount.sum_add_map,ih]
    rfl

theorem mass_total {Y : Type} (E : List Y) (nd : E.Nodup) (len : 2 ≤ E.length)
    (I : List Nat) (word : Y → Nat → Bool) (leaves : List (Leaf Y))
    (obstruction : ∀ v∈leaves,Obstruction E I word v) :
    (leaves.map Leaf.mass).sum ≤ 4*(E.map (fun y=>(leaves.map (fun l=>l.errors y)).sum)).sum := by
  rw [←sum_total]
  induction leaves with
  | nil => simp
  | cons a t ih =>
    have z := uniform_leaf nd len (obstruction a List.mem_cons_self)
    have tail := ih (fun v m=>obstruction v (List.mem_cons_of_mem _ m))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    omega

end PEqualNP.Outside.L_meta_32580.CountProfile

/- Source segment: PositiveWeight. -/


namespace PEqualNP.Outside.L_meta_32580.PositiveWeight
open PEqualNP.Outside.L_meta_32580.CountProfile PEqualNP.Outside.L_meta_32580.ColumnObstruction

                                                                  
                                                                         
                                                                           
structure Laws (A : Type) [Zero A] [Add A] [LE A] where
  scale : Nat → A → A
  refl : ∀ a : A,a ≤ a
  le_trans : ∀ {a b c : A},a ≤ b → b ≤ c → a ≤ c
  total : ∀ a b : A,a ≤ b∨b ≤ a
  zero_add : ∀ a : A,0+a=a
  rightZero : ∀ a : A,a+0=a
  commutes : ∀ a b : A,a+b=b+a
  grouping : ∀ a b c : A,(a+b)+c=a+(b+c)
  monoAdd : ∀ {a b c d : A},a ≤ b → c ≤ d → a+c ≤ b+d
  scale_arg : ∀ (n : Nat) {a b : A},a ≤ b → scale n a ≤ scale n b
  scale_nat : ∀ {m n : Nat} {a : A},m ≤ n → 0 ≤ a → scale m a ≤ scale n a
  scale_zero : ∀ n,scale n 0=0
  zero_scale : ∀ a,scale 0 a=0
  one_scale : ∀ a,scale 1 a=a
  scale_add : ∀ n a b,scale n (a+b)=scale n a+scale n b
  scaleSum : ∀ n m a,scale (n+m) a=scale n a+scale m a
  mul_scale : ∀ n m a,scale (n*m) a=scale n (scale m a)

variable {A : Type} [Zero A] [Add A] [LE A] (L : Laws A)

def sum : List A → A
  | [] => 0
  | a::t => a+sum t

theorem nonneg_scale (n : Nat) {a : A} (p : 0 ≤ a) : 0 ≤ L.scale n a := by
  have u := L.scale_arg n p
  rwa [L.scale_zero] at u

theorem scale_comm (m n : Nat) (a : A) : L.scale m (L.scale n a)=L.scale n (L.scale m a) := by
  rw [←L.mul_scale,←L.mul_scale,Nat.mul_comm]

theorem twice (a : A) : L.scale 2 a=a+a := by
  rw [show 2=1+1 from rfl,L.scaleSum,L.one_scale]

theorem four (a : A) : L.scale 2 (L.scale 2 a)=L.scale 4 a :=
  (L.mul_scale 2 2 a).symm

include L

theorem sum_nonneg {Y : Type} (E : List Y) (f : Y → A) (pos : ∀ s∈E,0 ≤ f s) :
    0 ≤ sum (E.map f) := by
  induction E with
  | nil => exact L.refl 0
  | cons s t ih =>
    have p := L.monoAdd (pos s List.mem_cons_self) (ih (fun a ha=>pos a (List.mem_cons_of_mem _ ha)))
    rwa [L.zero_add] at p

theorem sum_mono {Y : Type} (E : List Y) (f g : Y → A) (lo : ∀ s∈E,f s ≤ g s) :
    sum (E.map f) ≤ sum (E.map g) := by
  induction E with
  | nil => exact L.refl 0
  | cons a t ih =>
    exact L.monoAdd (lo a List.mem_cons_self) (ih (fun s hs=>lo s (List.mem_cons_of_mem _ hs)))

theorem sum_single_le {Y : Type} (E : List Y) (f : Y → A) (pos : ∀ s∈E,0 ≤ f s)
    {s : Y} (hs : s∈E) : f s ≤ sum (E.map f) := by
  induction E with
  | nil => simp at hs
  | cons x t ih =>
    rcases List.mem_cons.mp hs with rfl|hh
    · have h := L.monoAdd (L.refl (f s)) (sum_nonneg L t f (fun y hy=>pos y (List.mem_cons_of_mem _ hy)))
      rwa [L.rightZero] at h
    · have h := L.monoAdd (pos x List.mem_cons_self) (ih (fun y hy=>pos y (List.mem_cons_of_mem _ hy)) hh)
      rwa [L.zero_add] at h

theorem sum_two_le {Y : Type} (E : List Y) (f : Y → A) (pos : ∀ s∈E,0 ≤ f s)
    {s t : Y} (hs : s∈E) (ht : t∈E) (ne : s≠t) : f s+f t ≤ sum (E.map f) := by
  induction E with
  | nil => simp at hs
  | cons x tl ih =>
    have bp : ∀ y∈tl,0 ≤ f y := fun y hy=>pos y (List.mem_cons_of_mem _ hy)
    rcases List.mem_cons.mp hs with h|hS
    · subst x
      have tN := (List.mem_cons.mp ht).resolve_left (Ne.symm ne)
      exact L.monoAdd (L.refl _) (sum_single_le L tl f bp tN)
    · rcases List.mem_cons.mp ht with h|hT
      · subst x
        rw [L.commutes (f s) (f t)]
        exact L.monoAdd (L.refl _) (sum_single_le L tl f bp hS)
      · have a := L.monoAdd (pos x List.mem_cons_self) (ih bp hS hT)
        rwa [L.zero_add] at a

theorem sum_scale {Y : Type} (E : List Y) (f : Y → A) (n : Nat) :
    L.scale n (sum (E.map f))=sum (E.map (fun x=>L.scale n (f x))) := by
  induction E with
  | nil => exact L.scale_zero _
  | cons a t ih =>
    change L.scale n (f a+sum (t.map f))=L.scale n (f a)+_
    rw [L.scale_add,ih]

def weightedError {Y : Type} (E : List Y) (μ : Y → A) (v : Leaf Y) : A :=
  sum (E.map (fun s=>L.scale (v.errors s) (μ s)))

def Opt2 {Y : Type} (E : List Y) (I : List Nat) (word : Y → Nat → Bool)
    (μ : Y → A) (v : A) : Prop :=
  (∃ s∈E,v=L.scale 2 (μ s)) ∨
  (∃ i∈I,varying E word i=true ∧ ∃ b : Bool,
    v=sum (E.map (fun s=>if word s i≠b then μ s else 0)))

theorem low_weight {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    (μ : Y → A) (pos : ∀ s∈E,0 ≤ μ s) : ∃ s∈E,L.scale 2 (μ s) ≤ sum (E.map μ) := by
  obtain ⟨s,hs,t,ht,ne⟩ := two_members nd len
  have h := sum_two_le L E μ pos hs ht ne
  rcases L.total (μ s) (μ t) with p|p
  · refine ⟨s,hs,?_⟩
    rw [twice L]
    exact L.le_trans (L.monoAdd (L.refl _) p) h
  · refine ⟨t,ht,?_⟩
    rw [twice L]
    exact L.le_trans (L.monoAdd p (L.refl _)) h

theorem abstract_lower {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    {I : List Nat} {word : Y → Nat → Bool} {v : Leaf Y}
    (cert : Obstruction E I word v) (μ : Y → A) (pos : ∀ s∈E,0 ≤ μ s) (p : A)
    (minimal : ∀ w,Opt2 L E I word μ w → p ≤ w) :
    L.scale v.mass p ≤ L.scale 4 (weightedError L E μ v) := by
  cases cert with
  | @missed s hs atLeast =>
    have p0 := minimal _ (.inl ⟨s,hs,rfl⟩)
    apply L.le_trans (L.scale_arg _ p0)
    have eq : L.scale v.mass (L.scale 2 (μ s))=L.scale 2 (L.scale v.mass (μ s)) :=
      scale_comm L v.mass 2 (μ s)
    rw [eq]
    have go := L.scale_arg 2 (L.scale_nat atLeast (pos s hs))
    rw [L.mul_scale, four L] at go
    apply L.le_trans go
    apply L.scale_arg
    apply sum_single_le L E _ (fun a ha=>nonneg_scale L _ (pos a ha)) hs
  | allHalf bound =>
    obtain ⟨s,hs,x⟩ := low_weight L nd len μ pos
    have lower := minimal _ (.inl ⟨s,hs,rfl⟩)
    apply L.le_trans (L.scale_arg _ (L.le_trans lower x))
    unfold weightedError
    rw [sum_scale, sum_scale]
    apply sum_mono L
    intro j hj
    rw [←L.mul_scale]
    exact L.scale_nat (bound j hj) (pos j hj)
  | @column i bit hi varies bound =>
    let lower (s : Y) := if word s i≠bit then μ s else 0
    have minimal' := minimal (sum (E.map lower)) (.inr ⟨i,hi,varies,bit,rfl⟩)
    apply L.le_trans (L.scale_arg _ minimal')
    unfold weightedError
    rw [sum_scale,sum_scale]
    apply sum_mono L
    intro s hs
    by_cases h : word s i≠bit
    · simp only [lower,ite_eq_left h,←L.mul_scale]
      exact L.scale_nat (bound s hs h) (pos s hs)
    · have eq : word s i=bit := Classical.byContradiction h
      simp [lower,eq,L.scale_zero]
      exact nonneg_scale L 4 (nonneg_scale L _ (pos s hs))

end PEqualNP.Outside.L_meta_32580.PositiveWeight

/- Source segment: MathlibReduction. -/

  
                                                          
                                                                  
                                                                    
                                                                  
  

namespace PEqualNP.Outside.L_meta_32580.MathlibReduction
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.ZMod2Bridge

                                                                 
                                                        
theorem selector_independent {k : Nat} (E : Finset (Fin k → F)) (a : Fin k → F) (ha : a∈E)
    (hd : E.card=Module.finrank F (Submodule.span F
      (Set.image (fun s=>s-a) (↑E : Set (Fin k → F))))+1) :
    LinearIndependent F (fun s : ↥(E.erase a)=>(s : Fin k → F)-a) := by
  classical
  let b : ↥(E.erase a) → (Fin k → F) := fun s=>(s : Fin k → F)-a
  let W := Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Fin k → F)))
  have same : Submodule.span F (Set.range b)=W := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨s,rfl⟩
      exact Submodule.subset_span ⟨s.val,Finset.mem_of_mem_erase s.property,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨s,hs,rfl⟩
      by_cases eq : s=a
      · subst s
        change a-a∈Submodule.span F (Set.range b)
        rw [sub_self]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨s,Finset.mem_erase.mpr ⟨eq,hs⟩⟩,rfl⟩
  change LinearIndependent F b
  apply (linearIndependent_iff_card_eq_finrank_span).mpr
  rw [Set.finrank,same,Fintype.card_coe,Finset.card_erase_of_mem ha]
  change E.card-1=Module.finrank F W
  change E.card=Module.finrank F W+1 at hd
  omega

theorem finite_to_parity {n : Nat} (f : Fin n → F) :
    toBit (∑ j, f j) = parity (fun j => if h:j<n then toBit (f ⟨j,h⟩) else false) (List.range n) := by
  induction n with
  | zero => simp [toBit,parity]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,to_add,List.range_succ,parity_append]
    have step : parity (fun j=>if h:j<n+1 then toBit (f ⟨j,h⟩) else false) (List.range n) =
        toBit (∑ j : Fin n,f j.castSucc) := by
      rw [ih]
      apply parity_congr
      intro i hi
      have h : i<n := List.mem_range.mp hi
      simp [h,Nat.lt_succ_of_lt h]
    rw [step]
    simp [parity,Fin.val_last] <;> rfl

                                                                            
theorem dot_to_bit {n : Nat} (a b : Fin n → F) :
    toBit (dotProduct a b)=PEqualNP.Outside.L_meta_32580.OrthogonalCount.dot (List.range n) (pack a) (pack b) := by
  unfold dotProduct PEqualNP.Outside.L_meta_32580.OrthogonalCount.dot
  rw [finite_to_parity]
  apply parity_congr
  intro i hi
  have h : i<n := List.mem_range.mp hi
  simp [pack,h,to_mul]

theorem functional_row {n : Nat} (L : (Fin n → F) →ₗ[F] F) (x : Fin n → F) :
    L x=dotProduct (fun i=>L (Pi.single i 1)) x := by
  calc
    L x = L (∑ i, Pi.single i (x i)) := by rw [LinearMap.sum_single_apply]
    _ = ∑ i,L (Pi.single i (x i)) := map_sum L _ _
    _ = _ := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i _
      have eq : Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → F) := by
        ext j
        by_cases h : j=i <;> simp [Pi.single_apply,h]
      rw [eq,map_smul]
      simp [mul_comm]

                                                                         
theorem linear_forms_affine {n : Nat} (L : (Fin n → F) →ₗ[F] F) :
    PEqualNP.Outside.L_meta_32580.TapeKernel.Span ((List.range n).map (fun j x=>pack x j)) (fun x=>toBit (L x)) := by
  let B : List ((Fin n → F) → Bool) := (List.range n).map (fun j x=>pack x j)
  let row : Fin n → F := fun i=>L (Pi.single i 1)
  have equation : ∀ x,L x=dotProduct row x := functional_row L
  have basic (i : Nat) (hi : i∈List.range n) :
      PEqualNP.Outside.L_meta_32580.TapeKernel.Span B (fun x=>pack row i && pack x i) :=
    (PEqualNP.Outside.L_meta_32580.TapeKernel.Span.generator (List.mem_map_of_mem hi)).scale (pack row i)
  have par : ∀ t : List Nat,(∀ i∈t,i∈List.range n)  → 
    PEqualNP.Outside.L_meta_32580.TapeKernel.Span B (fun x=>parity (fun j=>pack row j && pack x j) t) := by
    intro t
    induction t with
    | nil => intro _; exact .const false
    | cons a t ih =>
      intro scope
      exact .plus (basic a (scope a List.mem_cons_self))
        (ih (fun i hi=>scope i (List.mem_cons_of_mem _ hi)))
  have actual : (fun x=>toBit (L x))=(fun x=>
      parity (fun j=>pack row j && pack x j) (List.range n)) := by
    funext x
    rw [equation,dot_to_bit]
    rfl
  rw [actual]
  exact par _ (fun _ h=>h)

noncomputable def realLaws : PEqualNP.Outside.L_meta_32580.PositiveWeight.Laws ℝ where
  scale n r := (n:ℝ)*r
  refl := le_refl
  le_trans := le_trans
  total := le_total
  zero_add := zero_add
  rightZero := add_zero
  commutes := add_comm
  grouping := add_assoc
  monoAdd := add_le_add
  scale_arg n _ _ h := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
  scale_nat {m n a} h ha := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) ha
  scale_zero n := mul_zero _
  zero_scale a := by simp
  one_scale a := by simp
  scale_add n a b := mul_add _ _ _
  scaleSum n m a := by push_cast; exact add_mul _ _ _
  mul_scale n m a := by push_cast; exact mul_assoc _ _ _

                                                                     
                                                                       
theorem signed_count {A : Type} [Fintype A] (bad : A → Bool) :
    (∑ a : A, if bad a then (-1:ℝ) else 1) =
      (Fintype.card A:ℝ)-2*((Finset.univ.filter (fun a=>bad a=true)).card:ℝ) := by
  classical
  have code (a : A) : (if bad a then (-1:ℝ) else 1)
      = 1-2*(if bad a=true then (1:ℝ) else 0) := by cases bad a <;> norm_num
  simp_rw [code]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_filter]
  simp

end PEqualNP.Outside.L_meta_32580.MathlibReduction

/- Source segment: FirstFold. -/


namespace PEqualNP.Outside.L_meta_32580.FirstFold
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.FrequencyFlat PEqualNP.Outside.L_meta_32580.FibreFlat PEqualNP.Outside.L_meta_32580.FrequencySplit
open PEqualNP.Outside.L_meta_32580.CountProfile

def count2 (d1 d2 : List Nat) (f : Assign → Assign → Bool) : Nat :=
  ((cube d2).map (fun y=>(cube d1).countP (fun x=>f x y))).sum

def xIntegrate {Y S : Type} (c xd bd : List Nat) (w : Nat → Form Y) (out : Form Y)
    (y : S → Assign → Assign) (param : S → Assign → Y) (phase : S → Assign → Bool) :
    Leaf S :=
  ⟨(cube bd).length*(cube xd).length, fun s=>
    count2 xd bd (fun x b=>discrepancy c xd w out x (param s b) (y s b) (phase s b))⟩

theorem all_false_count {A : Type} (l : List A) (p : A → Bool)
    (no : ∀ a∈l,p a=false) : l.countP p=0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  simp [no a ha]

theorem count_constant {A : Type} (l : List A) (p : A → Bool) (e : Bool)
    (is_const : ∀ a∈l,p a=e) :
    l.countP p=if e then l.length else 0 := by
  cases e
  · simp only [Bool.false_eq_true,ite_false]
    exact all_false_count l p is_const
  · simp only [ite_true]
    exact List.countP_eq_length.mpr is_const

theorem x_curves {Y S : Type} (c xd bd : List Nat) (w : Nat → Form Y) (out : Form Y)
    (E : List S) (I : List Nat) (word : S → Nat → Bool) (y : S → Assign → Assign)
    (param : S → Assign → Y) (phase : S → Assign → Bool) (directions : Assign → Assign)
    (moves : ∀ s u x,y s (shift u x)=shift (y s x) (directions u)) :
    Obstruction E I word (xIntegrate c xd bd w out y param phase) ∨
    (∀ s∈E,∀ x∈cube bd,agrees c xd w out (y s x)=true) := by
  rcases frequency_cases w out E y directions moves with miss|small|full
  · left
    obtain ⟨s,hs,none⟩ := miss
    apply Obstruction.missed hs
    have zeroScore (a : Assign) (ha : a∈cube bd) :
        2*(cube xd).countP (fun x=>discrepancy c xd w out x (param s a) (y s a) (phase s a)) =
          (cube xd).length :=
      outside_cancels c xd w out (param s a) (y s a) (phase s a) (none a ha)
    have t := sum_outside (cube bd) (fun _=>false)
      (fun a=>(cube xd).countP (fun x=>discrepancy c xd w out x (param s a) (y s a) (phase s a)))
      (cube xd).length (fun a ha _=>zeroScore a ha)
    simpa [xIntegrate,count2] using t
  · left
    apply Obstruction.allHalf
    intro s hs
    have t := all_half_loss (cube bd) (fun a=>agrees c xd w out (y s a))
      (fun a=>(cube xd).countP (fun x=>discrepancy c xd w out x (param s a) (y s a) (phase s a)))
      (cube xd).length (small s hs)
      (fun a ha=>outside_cancels c xd w out (param s a) (y s a) (phase s a))
    exact t
  · exact .inr full

                                                                      
                                                                 
                                                                    
                                                  
theorem x_const {Y S : Type} (c xd bd : List Nat) (w : Nat → Form Y) (out : Form Y)
    (s : S) (y : S → Assign → Assign)
    (param : S → Assign → Y) (phase : S → Assign → Bool)
    (all : ∀ a∈cube bd,agrees c xd w out (y s a)=true) :
    (xIntegrate c xd bd w out y param phase).errors s=
      (cube xd).length*(cube bd).countP (fun b=>
        discrepancy c xd w out zero (param s b) (y s b) (phase s b)) := by
  let p := fun b=>discrepancy c xd w out zero (param s b) (y s b) (phase s b)
  let f := fun a=>(cube xd).countP (fun x=>
    discrepancy c xd w out x (param s a) (y s a) (phase s a))
  have localConst (b : Assign) (hb : b∈cube bd) :
      f b=if p b then (cube xd).length else 0 :=
    count_constant (cube xd)
      (fun x=>discrepancy c xd w out x (param s b) (y s b) (phase s b)) _
      (within_constant c xd w out (param s b) (y s b) (phase s b) (all b hb))
  change ((cube bd).map f).sum=(cube xd).length*(cube bd).countP p
  have h : ∀ L : List Assign,(∀ b∈L,f b=(if p b then (cube xd).length else 0))  → 
    (L.map f).sum=(cube xd).length*L.countP p := by
    intro L
    induction L with
    | nil => intro; simp
    | cons z zs ih =>
      intro all
      have next := ih (fun b hb=>all b (List.mem_cons_of_mem _ hb))
      have this := all z List.mem_cons_self
      simp only [List.map_cons,List.sum_cons,this,next,countP_cons_add,Nat.mul_add]
      cases e : p z <;> simp [e]
  exact h _ localConst

theorem row_col_sum {A B : Type} (rows : List A) (cols : List B) (f : A → B → Nat) :
    (rows.map (fun x=>(cols.map (f x)).sum)).sum =
      (cols.map (fun y=>(rows.map (fun x=>f x y)).sum)).sum := by
  induction rows with
  | nil =>
    induction cols with
    | nil => rfl
    | cons a t ih => change 0=0+(t.map (fun _=>0)).sum; exact (Nat.zero_add _).symm ▸ ih
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons,OrthogonalCount.sum_add_map,ih]

theorem count_split {A B R : Type} (rows : List A) (cols : List B) (pieces : List R)
    (test : A → B → Bool) (part : R → A → Nat)
    (eq : ∀ a∈rows,cols.countP (test a)=(pieces.map (fun p=>part p a)).sum) :
    (rows.map (fun a=>cols.countP (test a))).sum =
      (pieces.map (fun p=>(rows.map (part p)).sum)).sum := by
  rw [List.map_congr_left eq]
  exact row_col_sum rows pieces (fun a p=>part p a)

end PEqualNP.Outside.L_meta_32580.FirstFold

/- Source segment: CircuitAdapter. -/


namespace PEqualNP.Outside.L_meta_32580.CircuitAdapter
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32580.TapeKernel

def Legal (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
      (g.op=.and∨g.op=.or∨g.op=.mod 2∨(g.op=.not∧g.inputs.length=1))

noncomputable def paidGate (h : Gate) : Bool :=
  @decide ((h.op=.and∨h.op=.or)∧h.inputs.length=2) (Classical.propDecidable _)

noncomputable def publicCost (gs : List Gate) : Nat := gs.countP paidGate

def affine (b : Bool) (pins : List Nat) : Instruction := ⟨false,b,pins⟩
def product (isOr : Bool) (i j : Nat) : Instruction := ⟨true,isOr,[i,j]⟩

def normalize : Gate → Instruction
  | ⟨.and,[]⟩ => affine true []
  | ⟨.and,[i]⟩ => affine false [i]
  | ⟨.and,[i,j]⟩ => product false i j
  | ⟨.or,[i]⟩ => affine false [i]
  | ⟨.or,[i,j]⟩ => product true i j
  | ⟨.mod _,pins⟩ => affine true pins
  | ⟨.not,[i]⟩ => affine true [i]
  | _ => affine false []

theorem cost_one (g : Gate) : (normalize g).cost=(paidGate g).toNat := by
  classical
  obtain ⟨o,p⟩ := g
  cases o <;>
    cases p with
    | nil => simp [normalize,affine,paidGate,Instruction.cost]
    | cons x xs =>
      cases xs with
      | nil => simp [normalize,affine,paidGate,Instruction.cost]
      | cons y ys =>
        cases ys with
        | nil => simp [normalize,affine,product,paidGate,Instruction.cost]
        | cons z zs =>
          have no : zs.length+1+1+1≠2 := by omega
          simp [normalize,affine,product,paidGate,Instruction.cost,no]

theorem cost (g : List Gate) : paid (g.map normalize)=publicCost g := by
  classical
  unfold publicCost
  induction g with
  | nil => rfl
  | cons a l ih =>
    change (normalize a).cost + paid (l.map normalize)=(a::l).countP paidGate
    rw [cost_one,ih]
    cases h : paidGate a <;> simp [List.countP_cons,h] <;> omega

theorem bool_or_gate (x y : Bool) : ((x&&y) ^^ (x^^y))=(x||y) := by
  cases x <;> cases y <;> decide

theorem exactOne (g : Gate) (h : Legal g) (w : List Bool) :
    evalInst (normalize g) w=g.op.eval (g.inputs.map fun i=>w.getD i false) := by
  obtain ⟨op,pins⟩ := g
  rcases h with ⟨len,op⟩
  rcases op with rfl|rfl|rfl|⟨rfl,one⟩
  · cases pins with
    | nil => simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval]
    | cons a t =>
      cases t with
      | nil => simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
      | cons b t =>
        cases t with
        | nil => simp [normalize,product,evalInst,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
        | cons x xs => simp at len <;> omega
  · cases pins with
    | nil => simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval]
    | cons a t =>
      cases t with
      | nil => simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
      | cons b t =>
        cases t with
        | nil =>
          simp only [normalize,product,evalInst,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
          simpa using bool_or_gate (w[a]?.getD false) (w[b]?.getD false)
        | cons x xs => simp at len <;> omega
  · cases pins with
    | nil => simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval]
    | cons a t =>
      cases t with
      | nil =>
        simp only [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
        change (true ^^ (w[a]?.getD false ^^ false)) = decide ([w[a]?.getD false].count true % 2=0)
        cases w[a]?.getD false <;> decide
      | cons b t =>
        cases t with
        | nil =>
          simp only [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
          change (true ^^ (w[a]?.getD false ^^ (w[b]?.getD false ^^ false))) =
            decide ([w[a]?.getD false,w[b]?.getD false].count true % 2=0)
          cases w[a]?.getD false <;> cases w[b]?.getD false <;> decide
        | cons x xs => simp at len <;> omega
  · cases pins with
    | nil => simp at one <;> omega
    | cons a t =>
      cases t with
      | nil =>
        simp [normalize,affine,evalInst,evalParity,AffinePivot.parity,GateOp.eval,TapeKernel.read,List.getD_eq_getElem?_getD]
      | cons b xs => simp at one <;> omega

theorem normalize_wires (gs : List Gate) (w : List Bool) (h : ∀ g∈gs,Legal g) :
    run (gs.map normalize) w = Circuit.wires ⟨gs,0⟩ w := by
  induction gs generalizing w with
  | nil => rfl
  | cons a t ih =>
    unfold run Circuit.wires
    simp only [List.map_cons,List.foldl_cons]
    rw [exactOne a (h a List.mem_cons_self)]
    exact ih _ (fun g mem=>h g (List.mem_cons_of_mem _ mem))

theorem normalize_eval (C : Circuit) (w : List Bool) (h : ∀ g∈C.gates,Legal g) :
    TapeKernel.read (run (C.gates.map normalize) w) C.output=C.eval w := by
  rw [normalize_wires _ _ h]
  simp [TapeKernel.read,Circuit.eval,Circuit.wires,List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_32580.CircuitAdapter

/- Source segment: CircuitEmit. -/


namespace PEqualNP.Outside.L_meta_32580.CircuitEmit
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify
open PEqualNP.Outside.L_meta_32580.CircuitAdapter

def bitsRun (G : List Gate) (w : List Bool) : List Bool := (Circuit.mk G 0).wires w
def gateValue (a : Gate) (w : List Bool) : Bool := a.op.eval (a.inputs.map (TapeKernel.read w))

inductive Bank : Nat → List Gate → Prop
  | nil (n : Nat) : Bank n []
  | cons {n : Nat} {a : Gate} {tail : List Gate} :
      (∀ j∈a.inputs,j<n)  →  Bank (n+1) tail  →  Bank n (a::tail)

theorem bank_append {n : Nat} {a b : List Gate} (h : Bank n a)
    (end_ : Bank (n+a.length) b) : Bank n (a++b) := by
  induction h with
  | nil n => exact end_
  | @cons n c tl cOk tOk ih =>
    apply Bank.cons cOk
    apply ih
    rwa [show (n+1)+tl.length=n+(c::tl).length from by simp; omega]

theorem bank_reads {n : Nat} {t : List Gate} (ok : Bank n t) :
    ∀ j < t.length, ∀ i ∈ (t.getD j ⟨.or,[]⟩).inputs, i<n+j := by
  induction ok with
  | nil _ => intro j lt; simp at lt
  | @cons n c t hc _ ih =>
    intro j lt i mem
    cases j with
    | zero => exact hc i mem
    | succ j =>
      have lt' : j<t.length := by simp at lt; omega
      have h := ih j lt' i (show i∈(t.getD j ⟨.or,[]⟩).inputs from mem)
      omega

theorem run_cons (G : List Gate) (a : Gate) (w : List Bool) :
    bitsRun (a::G) w=bitsRun G (w++[gateValue a w]) := by
  simp only [bitsRun,Circuit.wires,List.foldl_cons,gateValue,TapeKernel.read,List.getD_eq_getElem?_getD]
  rfl

theorem gate_append (G H : List Gate) (w : List Bool) :
    bitsRun (G++H) w=bitsRun H (bitsRun G w) := by
  simp [bitsRun,Circuit.wires,List.foldl_append]

theorem gate_len (G : List Gate) (w : List Bool) : (bitsRun G w).length=w.length+G.length := by
  induction G generalizing w with
  | nil => rfl
  | cons a t ih =>
    rw [run_cons,ih]
    simp; omega

theorem gate_ext (G : List Gate) (w : List Bool) : ∃ h,bitsRun G w=w++h := by
  induction G generalizing w with
  | nil => exact ⟨[],by simp [bitsRun,Circuit.wires]⟩
  | cons a t ih =>
    obtain ⟨h,eq⟩ := ih (w++[gateValue a w])
    refine ⟨gateValue a w::h,?_⟩
    rw [run_cons,eq,List.append_assoc]
    rfl

theorem read_ext (G : List Gate) (w : List Bool) {j : Nat} (h : j<w.length) :
    TapeKernel.read (bitsRun G w) j=TapeKernel.read w j := by
  obtain ⟨t,e⟩ := gate_ext G w
  simp [TapeKernel.read,e,List.getElem?_append_left h]

theorem read_new (w : List Bool) (z : Bool) :
    TapeKernel.read (w++[z]) w.length=z := by
  simp [TapeKernel.read,List.getElem?_append_right]

def constant (b : Bool) : Gate := ⟨if b then .and else .or,[]⟩
def xorEven (i j : Nat) : Gate := ⟨.mod 2,[i,j]⟩
def neg (i : Nat) : Gate := ⟨.not,[i]⟩
def conj (i j : Nat) : Gate := ⟨.and,[i,j]⟩

theorem eval_constant (b : Bool) (w : List Bool) : gateValue (constant b) w=b := by
  cases b <;> rfl

theorem eval_mod2 (i j : Nat) (w : List Bool) :
    gateValue (xorEven i j) w= !(TapeKernel.read w i ^^ TapeKernel.read w j) := by
  unfold gateValue
  change decide ([TapeKernel.read w i,TapeKernel.read w j].count true % 2=0)=_
  cases TapeKernel.read w i <;> cases TapeKernel.read w j <;> decide

theorem eval_neg (i : Nat) (w : List Bool) : gateValue (neg i) w= !(TapeKernel.read w i) := rfl
theorem eval_conj (i j : Nat) (w : List Bool) :
    gateValue (conj i j) w=(TapeKernel.read w i && TapeKernel.read w j) := by
  simp [gateValue,conj,GateOp.eval]

def shiftParity (n : Nat) (b : Bool) : List Nat → List Gate
  | [] => [constant b]
  | j::tail =>
    let old := shiftParity n b tail
    old++[xorEven j (n+old.length-1),neg (n+old.length)]

theorem shiftParity_pos (n : Nat) (b : Bool) (l : List Nat) : 0<(shiftParity n b l).length := by
  cases l with
  | nil => simp [shiftParity]
  | cons j t => simp [shiftParity]

theorem shiftParity_bank (n : Nat) (b : Bool) (l : List Nat)
    (scope : ∀ i∈l,i<n) : Bank n (shiftParity n b l) := by
  induction l with
  | nil =>
    apply Bank.cons _ (Bank.nil _)
    simp [constant]
  | cons j t ih =>
    unfold shiftParity
    apply bank_append (ih fun i hi=>scope i (List.mem_cons_of_mem _ hi))
    apply Bank.cons
    · have base := scope j List.mem_cons_self
      have pos := shiftParity_pos n b t
      intro v hv
      rcases (show v=j ∨ v=n+(shiftParity n b t).length-1 by simpa [xorEven] using hv) with rfl|rfl <;> omega
    · apply Bank.cons _ (Bank.nil _)
      simp [neg]

theorem shiftParity_legal (n : Nat) (b : Bool) (l : List Nat) :
    ∀ x∈shiftParity n b l, Legal x := by
  induction l with
  | nil =>
    intro x hx
    obtain rfl : x=constant b := by simpa [shiftParity] using hx
    cases b <;> simp [Legal,constant]
  | cons a t ih =>
    intro x hx
    rcases List.mem_append.mp (show x∈shiftParity n b t++_ from hx) with hi|hi
    · exact ih x hi
    · rcases (show x=xorEven a (n+(shiftParity n b t).length-1) ∨
          x=neg (n+(shiftParity n b t).length) by simpa using hi) with rfl|rfl <;>
          simp [Legal,xorEven,neg]

theorem shiftParity_free (n : Nat) (b : Bool) (l : List Nat) :
    publicCost (shiftParity n b l)=0 := by
  classical
  induction l with
  | nil => cases b <;> simp [publicCost,shiftParity,constant,paidGate]
  | cons a t ih =>
    simp [shiftParity,publicCost,List.countP_append,xorEven,neg,paidGate,
      show List.countP paidGate (shiftParity n b t)=0 from ih]

theorem shiftParity_out (n : Nat) (b : Bool) (l : List Nat) (w : List Bool)
    (len : w.length=n) (scope : ∀ i∈l,i<n) :
    TapeKernel.read (bitsRun (shiftParity n b l) w) (n+(shiftParity n b l).length-1)=
      (b ^^ evalParity w l) := by
  induction l with
  | nil =>
    unfold shiftParity
    rw [run_cons,eval_constant]
    simpa [bitsRun,Circuit.wires,evalParity,parity,len] using read_new w b
  | cons j tail ih =>
    let old := shiftParity n b tail
    let new := bitsRun old w
    let m := n+old.length
    have lenNew : new.length=m := by
      simp [new,gate_len,len,m]
    have rOld : TapeKernel.read new (m-1)=(b ^^ evalParity w tail) :=
      ih (fun i hi=>scope i (List.mem_cons_of_mem _ hi))
    have here : j<n := scope j List.mem_cons_self
    have rJ : TapeKernel.read new j=TapeKernel.read w j :=
      read_ext old w (by omega)
    have last : n+(shiftParity n b (j::tail)).length-1=m+1 := by
      simp [shiftParity,old,m]
      omega
    rw [last]
    change TapeKernel.read (bitsRun (old++[xorEven j (m-1),neg m]) w) (m+1)=_
    rw [gate_append,run_cons,eval_mod2,run_cons,eval_neg]
    rw [rOld,rJ]
    let bit := !(TapeKernel.read w j ^^ (b ^^ evalParity w tail))
    change TapeKernel.read (new++[bit]++[!(TapeKernel.read (new++[bit]) m)]) (m+1)=_
    have this : TapeKernel.read (new++[bit]) m=bit := by
      rw [←lenNew]
      exact read_new _ _
    have that : (new++[bit]).length=m+1 := by simp [lenNew]
    rw [this,←that,read_new]
    change (!bit)=(b ^^ (TapeKernel.read w j ^^ evalParity w tail))
    simp [bit,Bool.xor_left_comm]

end PEqualNP.Outside.L_meta_32580.CircuitEmit

/- Source segment: CircuitCompile. -/


namespace PEqualNP.Outside.L_meta_32580.CircuitCompile
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.CircuitAdapter PEqualNP.Outside.L_meta_32580.CircuitEmit

theorem cost_append (G H : List Gate) : publicCost (G++H)=publicCost G+publicCost H := by
  simp [publicCost,List.countP_append]

theorem conj_charge (a b : Nat) : publicCost [conj a b]=1 := by
  simp [publicCost,paidGate,conj]

theorem legal_append {G H : List Gate}
    (g : ∀ j∈G,Legal j) (h : ∀ j∈H,Legal j) : ∀ j∈G++H,Legal j := by
  intro j hj
  exact (List.mem_append.mp hj).elim (g _) (h _)

theorem address_lt {loc : List Nat} {n j : Nat}
    (scope : ∀ i∈loc,i<n) (hj : j<loc.length) : address loc j<n := by
  unfold address
  rw [List.getElem?_eq_getElem hj,Option.getD_some]
  exact scope _ (List.getElem_mem hj)

theorem retain_at {B : List Bool} {G A : List Gate} {j : Nat} (lt : j<B.length+G.length) :
    TapeKernel.read (bitsRun (G++A) B) j=TapeKernel.read (bitsRun G B) j := by
  rw [gate_append]
  apply read_ext
  rwa [gate_len]

theorem retain_loc {B : List Bool} {G A : List Gate} {loc : List Nat}
    (lt : ∀ j∈loc,j<B.length+G.length) :
    project (bitsRun (G++A) B) loc=project (bitsRun G B) loc := by
  apply List.map_congr_left
  exact fun j hj=>retain_at (lt j hj)

theorem emitSpan {Y : Type} {B P : List (Fun Y)} {f : Fun Y} (h : Span P f)
    (G : List Gate) (loc : List Nat) (locL : loc.length=P.length)
    (scope : ∀ j∈loc,j<B.length+G.length)
    (sem : ∀ y,project (bitsRun G (samples B y)) loc=samples P y) :
    ∃ A : List Gate, ∃ j : Nat,
      Bank (B.length+G.length) A ∧ (∀ c∈A,Legal c) ∧ publicCost A=0 ∧
      j<B.length+(G++A).length ∧
      ∀ y,TapeKernel.read (bitsRun (G++A) (samples B y)) j=f y := by
  obtain ⟨b,l,range,view⟩ := span_address h
  let n := B.length+G.length
  let ports := l.map (address loc)
  let A := shiftParity n b ports
  let j := n+A.length-1
  have all : ∀ v∈ports,v<n := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    apply address_lt scope
    rw [locL]
    exact range x hx
  refine ⟨A,j,shiftParity_bank n b ports all,shiftParity_legal n b ports,
    shiftParity_free n b ports,?_,?_⟩
  · have ap : 0<A.length := shiftParity_pos n b ports
    simp [j,n]
    omega
  · intro y
    rw [gate_append]
    have len : (bitsRun G (samples B y)).length=n := by simp [gate_len,n,samples]
    change TapeKernel.read (bitsRun (shiftParity n b ports) (bitsRun G (samples B y)))
      (n+(shiftParity n b ports).length-1)=f y
    rw [shiftParity_out n b ports _ len all,view y]
    rw [parity_address _ _ loc l (fun j hj=>locL ▸ range j hj) (sem y)]

                                                                           
                                                                       
                                                         
theorem emitProgram {Y : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) :
    ∃ G : List Gate, ∃ loc : List Nat,
      Bank B.length G ∧ (∀ j∈G,Legal j) ∧ publicCost G=q ∧ loc.length=P.length ∧
      (∀ j∈loc,j<B.length+G.length) ∧
      ∀ y,project (bitsRun G (samples B y)) loc=samples P y := by
  induction prior with
  | initial =>
    refine ⟨[],List.range B.length,.nil _,by simp,rfl,by simp,by simp,?_⟩
    intro y
    simpa [bitsRun,Circuit.wires,samples] using identity_project (samples B y)
  | @mul P q f g prior fSpan gSpan ih =>
    obtain ⟨G,loc,Gbank,Glegal,Gq,locL,below,sem⟩ := ih
    obtain ⟨A,i,Abank,Alegal,Aq,iread,is_f⟩ := emitSpan (B:=B) fSpan G loc locL below sem
    let G1 := G++A
    have loc1 : ∀ j∈loc,j<B.length+G1.length := by
      intro j hj
      have p := below j hj
      simp [G1]
      omega
    have sem1 : ∀ y,project (bitsRun G1 (samples B y)) loc=samples P y := by
      intro y
      change project (bitsRun (G++A) (samples B y)) loc=samples P y
      rw [retain_loc (fun j hj=>by simpa [samples] using below j hj)]
      exact sem y
    obtain ⟨D,j,Dbank,Dlegal,Dq,jread,is_g⟩ := emitSpan (B:=B) gSpan G1 loc locL loc1 sem1
    let G2 := G1++D
    let n := B.length+G2.length
    let c := conj i j
    have ic : i<n := by
      have : i<B.length+G1.length := iread
      simp [n,G2]
      omega
    have tailB : Bank n [c] := by
      apply Bank.cons _ (Bank.nil _)
      intro v hv
      rcases (show v=i∨v=j by simpa [c,conj] using hv) with rfl|rfl
      · exact ic
      · exact jread
    have G1B : Bank B.length G1 := bank_append Gbank Abank
    have G2B : Bank B.length G2 := bank_append G1B Dbank
    have cL : ∀ a∈[c],Legal a := by
      intro a ha
      obtain rfl : a=c := by simpa using ha
      simp [c,conj,Legal]
    refine ⟨G2++[c],loc++[n],bank_append G2B tailB,
      legal_append (legal_append (legal_append Glegal Alegal) Dlegal) cL,?_,?_,?_,?_⟩
    · unfold G2 G1 c
      simp [cost_append,Gq,Aq,Dq,conj_charge]
    · simp [locL]
    · intro i hi
      rcases List.mem_append.mp hi with h|h
      · have th := loc1 i h
        simp [G2]
        omega
      · obtain rfl : i=n := by simpa using h
        simp [n]
    · intro y
      change (loc++[n]).map (TapeKernel.read (bitsRun (G2++[c]) (samples B y))) =
        (P++[fun y=>f y&&g y]).map (fun h=>h y)
      simp only [List.map_append,List.map_cons,List.map_nil]
      change project (bitsRun (G2++[c]) (samples B y)) loc ++
        [TapeKernel.read (bitsRun (G2++[c]) (samples B y)) n] =
          samples P y++[f y&&g y]
      have all : ∀ z∈loc,z<(samples B y).length+G2.length := by
        intro z hz
        have bL := loc1 z hz
        simp [samples,G2]
        omega
      rw [retain_loc all]
      have hKeep : project (bitsRun G2 (samples B y)) loc=samples P y := by
        change project (bitsRun (G1++D) (samples B y)) loc=samples P y
        rw [retain_loc (fun v hv=>by simpa [samples] using loc1 v hv),sem1]
      rw [hKeep]
      have semF : TapeKernel.read (bitsRun G2 (samples B y)) i=f y := by
        change TapeKernel.read (bitsRun (G1++D) (samples B y)) i=f y
        rw [retain_at (by simpa [samples,G1] using iread)]
        exact is_f y
      have semG : TapeKernel.read (bitsRun G2 (samples B y)) j=g y := is_g y
      have evalOut : TapeKernel.read (bitsRun (G2++[c]) (samples B y)) n=(f y&&g y) := by
        rw [gate_append,run_cons]
        have bl : (bitsRun G2 (samples B y)).length=n := by simp [gate_len,samples,n]
        rw [←bl]
        change TapeKernel.read (bitsRun G2 (samples B y)++[gateValue c _]) _=_
        rw [read_new]
        rw [show c=conj i j from rfl,eval_conj,semF,semG]
      rw [evalOut]

theorem emitCircuit {Y : Type} {B P : List (Fun Y)} {q : Nat} {f : Fun Y}
    (prior : ParamProgram B P q) (fSpan : Span P f) :
    ∃ C : Circuit, Bank B.length C.gates ∧ (∀ j∈C.gates,Legal j) ∧
      publicCost C.gates=q ∧ ∀ y,C.eval (samples B y)=f y := by
  obtain ⟨G,loc,Gbank,Glegal,Gq,locL,scope,sem⟩ := emitProgram prior
  obtain ⟨A,i,Abank,Alegal,Aq,readScope,ea⟩ := emitSpan (B:=B) fSpan G loc locL scope sem
  refine ⟨⟨G++A,i⟩,bank_append Gbank Abank,legal_append Glegal Alegal,
    by simp [cost_append,Gq,Aq],?_⟩
  intro y
  simpa [Circuit.eval,bitsRun,Circuit.wires,TapeKernel.read,List.getD_eq_getElem?_getD] using ea y

end PEqualNP.Outside.L_meta_32580.CircuitCompile

/- Source segment: CircuitFlatten. -/


namespace PEqualNP.Outside.L_meta_32580.CircuitFlatten
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.Flatten PEqualNP.Outside.L_meta_32580.ChartGeometry
open PEqualNP.Outside.L_meta_32580.CircuitAdapter

def bits (n : Nat) (a : Assign) : List Bool := (List.range n).map a

theorem bits_injective {n : Nat} {a b : Assign} (ha : a∈cube (List.range n))
    (hb : b∈cube (List.range n)) (eq : bits n a=bits n b) : a=b := by
  funext j
  by_cases h : j<n
  · have e := congrArg (fun l : List Bool=>l[j]?.getD false) eq
    simpa [bits,List.getElem?_map,List.getElem?_range,h] using e
  · have hn : j∉List.range n := by simp [h]
    rw [mem_cube.mp ha j hn,mem_cube.mp hb j hn]

def rawX {Y : Type} (j : Nat) : Form Y := ⟨unit j,fun _=>false⟩
def rawY {Y : Type} (ybit : Nat → Y → Bool) (j : Nat) : Form Y := ⟨zero,ybit j⟩
def raw {Y : Type} (n : Nat) (ybit : Nat → Y → Bool) : List (Form Y) :=
  (List.range n).map rawX ++ (List.range n).map (rawY ybit)

theorem raw_sem {Y : Type} (n : Nat) (ybit : Nat → Y → Bool) (x : Assign) (y : Y) :
    wire (raw n ybit) (List.range n) x y=bits n x ++ bits n (fun j=>ybit j y) := by
  unfold raw wire bits
  rw [List.map_append,List.map_map,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp [Function.comp_def,rawX,value,linear_unit_form List.nodup_range hj]
  · apply List.map_congr_left
    intro j _
    simp [Function.comp_def,rawY,value,linear,zero,parity_zero]

def coordinates {Y : Type} (u : State Y) (i : Nat) : Form Y := Lookup u.forms i
def output {Y : Type} (u : State Y) (C : Circuit) : Form Y := Lookup u.forms C.output

theorem range_lookup {Y : Type} (w : List (Form Y)) (n : Nat) (hw : n ≤ w.length) :
    (List.range n).map (Lookup w)=w.take n := by
  apply List.ext_getElem (by simp [Nat.min_eq_left hw])
  intro i h1 h2
  have lt : i<n := by simpa using h1
  have tp : i<w.length := Nat.lt_of_lt_of_le lt hw
  simp [Lookup,List.getElem?_eq_getElem tp]

                                                                          
                                                                       
                                              
theorem first {Y : Type} (n : Nat) (C : Circuit) (valid : ∀ g∈C.gates,Legal g)
    (ybit : Nat → Y → Bool) :
    ∃ L : List (State Y),
      (∀ y (test : List Bool → Bool → Bool),(cube (List.range n)).countP (fun x=>test (bits n x) 
        (C.eval (bits n x++bits n (fun j=>ybit j y))))=
        (L.map (fun u=>(cube u.domain).countP (fun x=>
          test (wire ((List.range n).map (coordinates u)) u.domain x y)
            (value (output u C) u.domain x y)))).sum) ∧
      ∀ u∈L,u.domain.Nodup ∧ u.domain.length ≤ n ∧ n-u.domain.length+u.cost ≤ publicCost C.gates ∧
        ParamProgram ((raw n ybit).map Form.offset) u.pool u.cost ∧ inSpan u.pool u.forms ∧
        ∀ y a,a∈cube u.domain → ∀ b,b∈cube u.domain → 
          wire ((List.range n).map (coordinates u)) u.domain a y=
            wire ((List.range n).map (coordinates u)) u.domain b y → a=b := by
  let w := raw n ybit
  let start : State Y := ⟨List.range n,w,w.map Form.offset,0⟩
  let g := C.gates.map normalize
  have sp : inSpan start.pool start.forms := fun f hf=>.generator (List.mem_map_of_mem hf)
  obtain ⟨L,counts,ok⟩ := compile start.pool g start List.nodup_range ParamProgram.initial sp
  have width : n ≤ start.forms.length := by simp [start,w,raw]
  have occurs (u : State Y) (hu : u∈L) : n ≤ u.forms.length := by
    obtain ⟨_,_,_,len,_,_,_⟩ := ok u hu
    omega
  have firstN (x : Assign) (y : Y) : (wire start.forms start.domain x y).take n=bits n x := by
    change (wire (raw n ybit) (List.range n) x y).take n=bits n x
    rw [raw_sem]
    have e : (bits n x).length=n := by simp [bits]
    simpa only [e] using take_exact (bits n x) (bits n (fun j=>ybit j y))
  have path (u : State Y) (hu : u∈L) :
      (List.range n).map (coordinates u)=u.forms.take n := range_lookup _ n (occurs u hu)
  refine ⟨L,?_,?_⟩
  · intro y test
    let f : List Bool → Bool := fun ws=>test (ws.take n) (TapeKernel.read ws C.output)
    have cnt := counts y f
    have inp (x : Assign) :
        f (run g (wire start.forms start.domain x y))=test (bits n x)
          (C.eval (bits n x++bits n (fun j=>ybit j y))) := by
      unfold f
      congr 1
      · obtain ⟨ext,ex⟩ := run_extension g (wire start.forms start.domain x y)
        rw [ex]
        have below : n ≤ (wire start.forms start.domain x y).length := by rwa [wire_length]
        rw [List.take_append_of_le_length below,firstN]
      · dsimp [start,w,g]
        rw [raw_sem,normalize_eval _ _ valid]
    simp only [inp] at cnt
    have rhs : count L y f=(L.map (fun u=>(cube u.domain).countP (fun x=>
        test (wire ((List.range n).map (coordinates u)) u.domain x y)
          (value (output u C) u.domain x y)))).sum := by
      unfold count
      congr 1
      apply List.map_congr_left
      intro u hu
      congr 1
      funext x
      simp [f,path u hu,take_wire,output,lookup_value,TapeKernel.read]
    rw [rhs] at cnt
    exact cnt
  · intro u hu
    obtain ⟨dim,_,charge,_,nd,prog,spans⟩ := ok u hu
    have fuel : n-u.domain.length+u.cost ≤ publicCost C.gates := by
      change (List.range n).length-u.domain.length+(u.cost-0) ≤ paid g at charge
      simpa [g,cost] using charge
    refine ⟨nd,by simpa [start] using dim,fuel,prog,spans,?_⟩
    intro y
    apply chart_injective (l:=cube (List.range n)) (cube_nodup List.nodup_range)
      (orig:=bits n) (ls:=L) (dom:=fun v=>cube v.domain)
      (localMap:=fun v x=>wire ((List.range n).map (coordinates v)) v.domain x y)
      (c:=u)
    · exact fun a ha b hb=>bits_injective ha hb
    · intro P
      have cp := counts y (fun z=>P (z.take n))
      have test_eq : ∀ x,
          (run g (wire start.forms start.domain x y)).take n=bits n x := by
        intro x
        obtain ⟨tail,ht⟩ := run_extension g (wire start.forms start.domain x y)
        rw [ht,List.take_append_of_le_length (by rwa [wire_length]),firstN]
      simp only [test_eq] at cp
      rw [cp]
      unfold count
      congr 1
      apply List.map_congr_left
      intro v hv
      rw [path v hv]
      simp [take_wire]
    · exact hu

end PEqualNP.Outside.L_meta_32580.CircuitFlatten

/- Source segment: SecondChartShapes. -/


namespace PEqualNP.Outside.L_meta_32580.SecondChartShapes
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.Flatten PEqualNP.Outside.L_meta_32580.ChartGeometry
open PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.TwoPhase PEqualNP.Outside.L_meta_32580.ResidualLift
open PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.CircuitFlatten

theorem pairs_append (I J : List Nat) :
    pairCoordinates (I++J)=pairCoordinates I++pairCoordinates J := by
  simp [pairCoordinates,List.flatMap_append]

theorem pairs_range (m : Nat) : pairCoordinates (List.range m)=List.range (2*m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ,pairs_append,ih,show 2*(m+1)=2*m+2 from by omega]
    simp [List.range_succ,pair_cons,pairCoordinates,left,right,List.append_assoc]

theorem base_layout (m r : Nat) :
    List.range (2*m+r)=pairCoordinates (List.range m)++List.range' (2*m) r := by
  rw [pairs_range,List.range_eq_range' (n:=2*m+r),List.range_eq_range' (n:=2*m)]
  simpa only [Nat.zero_add] using (@List.range'_append_1 0 (2*m) r).symm

theorem outside_pairs (m r : Nat) :
    ∀ j∈List.range' (2*m) r,pairIndex j∉List.range m := by
  intro j hj h
  obtain ⟨less,_⟩ := List.mem_range'_1.mp hj
  have inside := List.mem_range.mp h
  simp only [pairIndex] at inside
  omega

def observed {Y : Type} (n : Nat) (coords : Nat → Fun Y) (rest : List (Fun Y)) : List (Fun Y) :=
  (List.range n).map coords++rest

theorem observed_take {Y : Type} (n : Nat) (coords : Nat → Fun Y) (rest : List (Fun Y)) (y : Y) :
    (samples (observed n coords rest) y).take n=bits n (fun j=>coords j y) := by
  unfold observed samples bits
  simp only [List.map_append,List.map_map,Function.comp_def]
  have h : ((List.range n).map (fun j=>coords j y)).length=n := by simp
  simpa only [h] using take_exact ((List.range n).map (fun j=>coords j y)) (rest.map (fun f=>f y))

def baseForm {S : Type} (u : View S) (i : Nat) : Form S := Lookup u.values i

                                                                       
                                                                    
                                                                   
                                                              
theorem build_second {Y S : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) (pack : Assign → S → Y)
    (n : Nat) (w : List (Form S))
    (wire_s : ∀ x s,wire w (List.range n) x s=samples B (pack x s))
    (coords : Nat → Fun Y) (rest : List (Fun Y))
    (obs_ok : ∀ f∈observed n coords rest,Span P f)
    (raw_formula : ∀ s x j,j<n → coords j (pack x s)=x j) :
    ∃ L : List (View S),
      (∀ s test,(cube (List.range n)).countP
        (fun x=>test (samples (observed n coords rest) (pack x s)))=countView L s test) ∧
      ∀ u∈L,u.domain.Nodup ∧ u.domain.length ≤ n ∧ n-u.domain.length ≤ q ∧
        u.values.length=(observed n coords rest).length ∧
        ∀ s a,a∈cube u.domain → ∀ b,b∈cube u.domain → 
          wire ((List.range n).map (baseForm u)) u.domain a s=
            wire ((List.range n).map (baseForm u)) u.domain b s → a=b := by
  obtain ⟨L,carry,well⟩ := second_with_observations prior pack (List.range n) List.nodup_range w
    wire_s (observed n coords rest) obs_ok
  have slice (u : View S) (hu : u∈L) :
      (List.range n).map (baseForm u)=u.values.take n := by
    apply range_lookup
    obtain ⟨_,_,_,len⟩ := well u hu
    simp [len,observed]
  have prefixSem (s : S) (x : Assign) : (samples (observed n coords rest) (pack x s)).take n=bits n x := by
    rw [observed_take]
    apply List.map_congr_left
    exact fun j hj=>raw_formula s x j (List.mem_range.mp hj)
  refine ⟨L,carry,?_⟩
  intro u hu
  obtain ⟨nd,dim,paid,len⟩ := well u hu
  refine ⟨nd,by simpa using dim,by simpa using paid,len,?_⟩
  intro s
  apply chart_injective (l:=cube (List.range n)) (cube_nodup List.nodup_range)
    (orig:=bits n) (ls:=L) (dom:=fun v=>cube v.domain)
    (localMap:=fun v x=>wire ((List.range n).map (baseForm v)) v.domain x s)
    (c:=u)
  · exact fun a ha b hb=>bits_injective ha hb
  · intro P
    have t := carry s (fun xs=>P (xs.take n))
    simp only [prefixSem] at t
    rw [t]
    unfold countView
    congr 1
    apply List.map_congr_left
    intro v hv
    simp [slice v hv,take_wire]
  · exact hu

end PEqualNP.Outside.L_meta_32580.SecondChartShapes

/- Source segment: WeightedCounts. -/


namespace PEqualNP.Outside.L_meta_32580.WeightedCounts
open PEqualNP.Outside.L_meta_32580.ColumnObstruction PEqualNP.Outside.L_meta_32580.CountProfile PEqualNP.Outside.L_meta_32580.OrthogonalCount

def wtError {Y : Type} (E : List Y) (μ : Y → Nat) (v : Leaf Y) : Nat :=
  (E.map (fun s=>μ s*v.errors s)).sum

def weight {Y : Type} (E : List Y) (μ : Y → Nat) : Nat := (E.map μ).sum

def OptionDouble {Y : Type} (E : List Y) (I : List Nat) (word : Y → Nat → Bool)
    (μ : Y → Nat) (p : Nat) : Prop :=
  (∃ x∈E,p=2*μ x) ∨
    (∃ i∈I,varying E word i=true ∧ ∃ b : Bool,
      p=weight E (fun s=>if word s i≠b then μ s else 0))

theorem sum_mul {Y : Type} (E : List Y) (f : Y → Nat) (p : Nat) :
    (E.map f).sum*p=(E.map (fun x=>f x*p)).sum := by
  induction E with
  | nil => simp
  | cons a t ih => simp only [List.map_cons,List.sum_cons,Nat.add_mul,ih]

theorem mul_sum {Y : Type} (E : List Y) (f : Y → Nat) (p : Nat) :
    p*(E.map f).sum=(E.map (fun x=>p*f x)).sum := by
  induction E with
  | nil => simp
  | cons a t ih => simp only [List.map_cons,List.sum_cons,Nat.mul_add,ih]

theorem sum_le {Y : Type} (E : List Y) (f g : Y → Nat) (lo : ∀ s∈E,f s ≤ g s) :
    (E.map f).sum ≤ (E.map g).sum := by
  induction E with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (lo a List.mem_cons_self) (ih (fun s hs=>lo s (List.mem_cons_of_mem _ hs)))

theorem some_half {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length) (μ : Y → Nat) :
    ∃ s∈E,2*μ s ≤ weight E μ := by
  obtain ⟨s,hs,t,ht,ne⟩ := two_members nd len
  have h := sum_ge_two E μ hs ht ne
  have hh : μ s+μ t ≤ weight E μ := h
  by_cases good : 2*μ s ≤ weight E μ
  · exact ⟨s,hs,good⟩
  · exact ⟨t,ht,by omega⟩

theorem profile_lower {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    {I : List Nat} {word : Y → Nat → Bool} {v : Leaf Y}
    (cert : Obstruction E I word v) (μ : Y → Nat) (p : Nat)
    (minimal : ∀ k,OptionDouble E I word μ k → p ≤ k) :
    p*v.mass ≤ 4*wtError E μ v := by
  cases cert with
  | @missed s hs larger =>
    have h := minimal _ (.inl ⟨s,hs,rfl⟩)
    have h1 := Nat.mul_le_mul_right v.mass h
    have h2 := Nat.mul_le_mul_left (2*μ s) larger
    have h3 : μ s*v.errors s ≤ wtError E μ v := sum_ge E (fun s=>μ s*v.errors s) hs
    have h4₀ := Nat.mul_le_mul_left 4 h3
    have h4 : (2*μ s)*(2*v.errors s) ≤ 4*wtError E μ v := by
      rw [show (2*μ s)*(2*v.errors s)=4*(μ s*v.errors s) by
        calc
          _ = 2*(μ s*(2*v.errors s)) := Nat.mul_assoc _ _ _
          _ = 2*(2*(μ s*v.errors s)) := congrArg (fun a=>2*a) (Nat.mul_left_comm _ _ _)
          _ = 4*(μ s*v.errors s) := (Nat.mul_assoc 2 2 (μ s*v.errors s)).symm]
      exact h4₀
    exact Nat.le_trans h1 (Nat.le_trans h2 h4)
  | allHalf f =>
    obtain ⟨s,hs,small⟩ := some_half nd len μ
    have h := minimal _ (.inl ⟨s,hs,rfl⟩)
    have w : p*v.mass ≤ weight E μ*v.mass := Nat.mul_le_mul_right _ (Nat.le_trans h small)
    apply Nat.le_trans w
    unfold weight wtError
    rw [sum_mul,mul_sum]
    apply sum_le
    intro x hx
    rw [←Nat.mul_assoc,Nat.mul_comm 4 (μ x),Nat.mul_assoc]
    exact Nat.mul_le_mul_left (μ x) (f x hx)
  | @column i bit hi var f =>
    let p' := fun s=>if word s i≠bit then μ s else 0
    have pL := minimal _ (.inr ⟨i,hi,var,bit,rfl⟩)
    have w : p*v.mass ≤ weight E p'*v.mass := Nat.mul_le_mul_right _ pL
    apply Nat.le_trans w
    unfold weight wtError
    rw [sum_mul,mul_sum]
    apply sum_le
    intro x hx
    by_cases e : word x i≠bit
    · have q := Nat.mul_le_mul_left (μ x) (f x hx e)
      simpa [p',e,Nat.mul_left_comm] using q
    · have eq : word x i=bit := Classical.byContradiction e
      simp [p',eq]

theorem linear_errors {Y : Type} (E : List Y) (μ : Y → Nat) (v : List (Leaf Y)) :
    (v.map (wtError E μ)).sum=(E.map (fun y=>μ y*(v.map (fun a=>a.errors y)).sum)).sum := by
  induction v with
  | nil =>
    induction E with
    | nil => rfl
    | cons _ t ih =>
      change 0=(t.map (fun _=>0)).sum at ih
      simp only [List.map_cons,List.map_nil,List.sum_nil,Nat.mul_zero,List.sum_cons,
        Nat.zero_add]
      exact ih
  | cons a t ih =>
    unfold wtError at *
    simp only [List.map_cons,List.sum_cons,Nat.mul_add,sum_add_map,ih]

                                                                      
                                                                       
                                                             
theorem weighted_total {Y : Type} {E : List Y} (nd : E.Nodup) (len : 2 ≤ E.length)
    {I : List Nat} {word : Y → Nat → Bool} (v : List (Leaf Y))
    (certs : ∀ g∈v,Obstruction E I word g) (μ : Y → Nat) (p : Nat)
    (minimum : ∀ k,OptionDouble E I word μ k → p ≤ k) :
    p*(v.map Leaf.mass).sum ≤ 4*(E.map (fun y=>μ y*(v.map (fun a=>a.errors y)).sum)).sum := by
  rw [←linear_errors]
  induction v with
  | nil => simp
  | cons a t ih =>
    have h := profile_lower nd len (certs a List.mem_cons_self) μ p minimum
    have tH := ih (fun l hl=>certs l (List.mem_cons_of_mem _ hl))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add h tH

end PEqualNP.Outside.L_meta_32580.WeightedCounts

/- Source segment: RefineProfiles. -/


namespace PEqualNP.Outside.L_meta_32580.RefineProfiles
open PEqualNP.Outside.L_meta_32580.CountProfile

def merge {Y : Type} (parts : List (Leaf Y)) : Leaf Y :=
  ⟨(parts.map Leaf.mass).sum,fun s=>(parts.map (fun a=>a.errors s)).sum⟩

def agrees {Y : Type} (E : List Y) (whole : Leaf Y) (parts : List (Leaf Y)) : Prop :=
  (merge parts).mass=whole.mass ∧ ∀ s∈E,(merge parts).errors s=whole.errors s

def result {Y : Type} (E : List Y) (I : List Nat) (word : Y → Nat → Bool)
    (whole : Leaf Y) (parts : List (Leaf Y)) : Prop :=
  agrees E whole parts ∧ ∀ h∈parts,0<h.mass ∧ Obstruction E I word h

theorem singleton {Y : Type} (E : List Y) (I : List Nat) (word : Y → Nat → Bool)
    (whole : Leaf Y) (pos : 0<whole.mass) (has : Obstruction E I word whole) :
    result E I word whole [whole] := by
  exact ⟨⟨by simp [merge],fun s _=>by simp [merge]⟩,
    fun h hh=>by simpa using (show h=whole from List.mem_singleton.mp hh) ▸ And.intro pos has⟩

theorem sum_join {A B : Type} (L : List A) (pieces : A → List B) (score : B → Nat) :
    ((L.flatMap pieces).map score).sum=(L.map (fun a=>((pieces a).map score).sum)).sum := by
  induction L with
  | nil => rfl
  | cons a t ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

                                                                    
                                                                  
                                                  
theorem refine_all {Y : Type} (E : List Y) {I : List Nat} {word : Y → Nat → Bool}
    (whole : Leaf Y) (stage : List (Leaf Y)) (outer : agrees E whole stage)
    (refinement : ∀ a∈stage,∃ parts,result E I word a parts) :
    ∃ good,result E I word whole good := by
  classical
  let choose (a : Leaf Y) := if ha:a∈stage then Classical.choose (refinement a ha) else []
  have sem (a : Leaf Y) (ha : a∈stage) : result E I word a (choose a) := by
    simp only [choose,dite_eq_left ha]
    exact Classical.choose_spec (refinement a ha)
  refine ⟨stage.flatMap choose,⟨?_,?_⟩,?_⟩
  · calc
      (merge (stage.flatMap choose)).mass = (stage.map (fun a=>(merge (choose a)).mass)).sum :=
        sum_join stage choose Leaf.mass
      _ = (merge stage).mass := congrArg List.sum (List.map_congr_left (fun a ha=>(sem a ha).1.1))
      _ = whole.mass := outer.1
  · intro s hs
    calc
      (merge (stage.flatMap choose)).errors s =
        (stage.map (fun a=>(merge (choose a)).errors s)).sum :=
        sum_join stage choose (fun b=>b.errors s)
      _ = (merge stage).errors s :=
        congrArg List.sum (List.map_congr_left (fun a ha=>(sem a ha).1.2 s hs))
      _ = whole.errors s := outer.2 s hs
  · intro h hh
    obtain ⟨a,ha,m⟩ := List.mem_flatMap.mp hh
    exact (sem a ha).2 h m

theorem residual_short {hull cuts q p cols : Nat}
    (large : hull ≤ cuts) (paid : cuts+q ≤ p) (short : p<hull+cols) :
    q<cols := by omega

theorem score_not_perfect {Y : Type} {E : List Y} {I : List Nat} {word : Y → Nat → Bool}
    (nd : E.Nodup) (nontrivial : 2 ≤ E.length) (whole : Leaf Y) (positive : 0<whole.mass)
    (parts : List (Leaf Y)) (p : result E I word whole parts) :
    ¬∀ s∈E,whole.errors s=0 := by
  intro no
  have mass := mass_total E nd nontrivial I word parts (fun a ha=>(p.2 a ha).2)
  change (merge parts).mass ≤ 4*(E.map (merge parts).errors).sum at mass
  rw [p.1.1] at mass
  have z : E.map (merge parts).errors=E.map (fun _=>0) := by
    apply List.map_congr_left
    intro s hs
    rw [p.1.2 s hs,no s hs]
  have empty (l : List Y) : (l.map (fun _=>0)).sum=0 := by induction l <;> simp_all
  rw [z,empty] at mass
  omega

def scaled {Y : Type} (k : Nat) (a : Leaf Y) : Leaf Y :=
  ⟨k*a.mass,fun s=>k*a.errors s⟩

theorem scaled_obs {Y : Type} {E : List Y} {I : List Nat} {word : Y → Nat → Bool}
    {a : Leaf Y} (k : Nat) (cert : Obstruction E I word a) :
    Obstruction E I word (scaled k a) := by
  cases cert with
  | @missed s hs lo =>
    apply Obstruction.missed hs
    change k*a.mass ≤ 2*(k*a.errors s)
    rw [Nat.mul_left_comm 2]
    exact Nat.mul_le_mul_left k lo
  | allHalf p =>
    apply Obstruction.allHalf
    intro s hs
    change k*a.mass ≤ 4*(k*a.errors s)
    rw [Nat.mul_left_comm 4]
    exact Nat.mul_le_mul_left k (p s hs)
  | @column i bias hi va p =>
    apply Obstruction.column hi va
    intro s hs yes
    change k*a.mass ≤ 4*(k*a.errors s)
    rw [Nat.mul_left_comm 4]
    exact Nat.mul_le_mul_left k (p s hs yes)

theorem scale_result {Y : Type} {E : List Y} {I : List Nat} {word : Y → Nat → Bool}
    {whole : Leaf Y} {parts : List (Leaf Y)} (k : Nat) (h : 0<k)
    (r : result E I word whole parts) :
    result E I word (scaled k whole) (parts.map (scaled k)) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · change ((parts.map (scaled k)).map Leaf.mass).sum=k*whole.mass
    simp only [List.map_map,Function.comp_def,scaled,←WeightedCounts.mul_sum]
    exact congrArg (Nat.mul k) r.1.1
  · intro s hs
    change ((parts.map (scaled k)).map (fun a=>a.errors s)).sum=k*whole.errors s
    simp only [List.map_map,Function.comp_def,scaled,←WeightedCounts.mul_sum]
    exact congrArg (Nat.mul k) (r.1.2 s hs)
  · intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact ⟨Nat.mul_pos h (r.2 v hv).1,scaled_obs k (r.2 v hv).2⟩

end PEqualNP.Outside.L_meta_32580.RefineProfiles

/- Source segment: ComposedTransport. -/


namespace PEqualNP.Outside.L_meta_32580.ComposedTransport
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.PairSlots
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.TwoPhase
open PEqualNP.Outside.L_meta_32580.ChartGeometry PEqualNP.Outside.L_meta_32580.ComposedPhase PEqualNP.Outside.L_meta_32580.ColumnObstruction
open PEqualNP.Outside.L_meta_32580.CircuitFlatten PEqualNP.Outside.L_meta_32580.CountProfile PEqualNP.Outside.L_meta_32580.RefineProfiles

structure Atom {Y S : Type} (P : List (Fun Y)) (f : Fun Y) where
  query : List Bool → Bool
  atChart : List (Form S) → Form S
  faithful : ∀ y,query (samples P y)=f y
  pull : ∀ w d x s,value (atChart w) d x s=query (wire w d x s)

theorem atom_exists {Y S : Type} {P : List (Fun Y)} {f : Fun Y} (h : Span P f) :
    Nonempty (Atom (S:=S) P f) := by
  obtain ⟨b,l,_,meaning⟩ := span_address h
  refine ⟨⟨fun w=>b ^^ evalParity w l,fun w=>add (const b) (linearInstr w l),
    fun y=>(meaning y).symm,?_⟩⟩
  intro w d x s
  rw [add_value,const_value,linearInstr_ok]

noncomputable def atom {Y S : Type} {P : List (Fun Y)} {f : Fun Y} (h : Span P f) :
    Atom (S:=S) P f := Classical.choice (atom_exists h)

structure FormData {Y S : Type} (P : List (Fun Y)) where
  xOffset : Nat → Fun Y
  yValue : Nat → Fun Y
  baseValue : Nat → Fun Y
  outOffset : Fun Y
  hx : ∀ j,Span P (xOffset j)
  hy : ∀ j,Span P (yValue j)
  hb : ∀ j,Span P (baseValue j)
  ho : Span P outOffset
  h : S → Bool
  word : S → Nat → Bool

noncomputable def queryPhase {Y S : Type} {P : List (Fun Y)}
    (D : FormData (S:=S) P) (loc I : List Nat) (s : S) (w : List Bool) : Bool :=
  ((atom (S:=S) D.ho).query w ^^ D.h s) ^^
    (dot loc (fun j=>(atom (S:=S) (D.hx j)).query w)
      (fun j=>(atom (S:=S) (D.hy j)).query w) ^^
      parity (fun j=>D.word s j &&
        ((atom (S:=S) (D.hb (left j))).query w && (atom (S:=S) (D.hb (right j))).query w)) I)

def originalPhase {Y S : Type} {P : List (Fun Y)}
    (D : FormData (S:=S) P) (loc I : List Nat) (s : S) (y : Y) : Bool :=
  (D.outOffset y ^^ D.h s) ^^
    (dot loc (fun j=>D.xOffset j y) (fun j=>D.yValue j y) ^^
      parity (fun j=>D.word s j && (D.baseValue (left j) y && D.baseValue (right j) y)) I)

theorem query_exact {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (loc I : List Nat) (s : S) (y : Y) :
    queryPhase D loc I s (samples P y)=originalPhase D loc I s y := by
  unfold queryPhase originalPhase
  simp only [Atom.faithful]

noncomputable def xForms {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S) (j : Nat) :
    Form S := (atom (D.hx j)).atChart v.values
noncomputable def yForms {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S) (j : Nat) :
    Form S := (atom (D.hy j)).atChart v.values
noncomputable def bForms {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S) (j : Nat) :
    Form S := (atom (D.hb j)).atChart v.values
noncomputable def oForm {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S) : Form S :=
  let a := (atom (S:=S) D.ho).atChart v.values
  ⟨a.coeff,fun s=>a.offset s ^^ D.h s⟩

theorem form_out {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S) (x : Assign) (s : S) :
    value (oForm D v) v.domain x s=
      ((atom (S:=S) D.ho).query (wire v.values v.domain x s) ^^ D.h s) := by
  rw [←(atom (S:=S) D.ho).pull]
  simp [oForm,value,linear]

theorem pair_form_eval {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P) (v : View S)
    (I : List Nat) (x : Assign) (s : S) :
    pairsEval v.domain (fun j=>(bForms D v (left j),bForms D v (right j))) (D.word s) I x s=
      parity (fun j=>D.word s j &&
        ((atom (S:=S) (D.hb (left j))).query (wire v.values v.domain x s) &&
          (atom (S:=S) (D.hb (right j))).query (wire v.values v.domain x s))) I := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [pairsEval,parity,ih]
    simp only [bForms,Atom.pull]

theorem chart_exact {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (loc I : List Nat) (v : View S) (x : Assign) (s : S) :
    queryPhase D loc I s (wire v.values v.domain x s)=
      scorePhase loc v.domain (xForms D v) (yForms D v) (oForm D v) I
        (fun j=>(bForms D v (left j),bForms D v (right j))) D.word x s := by
  unfold queryPhase scorePhase
  rw [form_out,pair_form_eval]
  have eq := show dot loc (FrequencyFlat.affineChart loc v.domain (xForms D v) x s)
      (FrequencyFlat.affineChart loc v.domain (yForms D v) x s)=
    dot loc (fun j=>(atom (S:=S) (D.hx j)).query (wire v.values v.domain x s))
      (fun j=>(atom (S:=S) (D.hy j)).query (wire v.values v.domain x s)) from by
    unfold dot
    apply parity_congr
    intro j hj
    simp [FrequencyFlat.affineChart,hj,xForms,yForms,Atom.pull]
  rw [eq]

noncomputable def queryBase {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (n : Nat) (w : List Bool) : List Bool :=
  (List.range n).map (fun j=>(atom (S:=S) (D.hb j)).query w)

theorem basic_exact {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (n : Nat) (v : View S) (x : Assign) (s : S) :
    wire ((List.range n).map (bForms D v)) v.domain x s=
      queryBase D n (wire v.values v.domain x s) := by
  simp [queryBase,wire,bForms,List.map_map,Function.comp_def,Atom.pull]

theorem chart_base_injective {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (pack : Assign → S → Y) (n : Nat) (L : List (View S))
    (counts : ∀ s test,(cube (List.range n)).countP (fun x=>test (samples P (pack x s)))=
      countView L s test)
    (raw_formula : ∀ s x j,j<n → D.baseValue j (pack x s)=x j)
    {v : View S} (hv : v∈L) (s : S) :
    ∀ a∈cube v.domain,∀ b∈cube v.domain,
       wire ((List.range n).map (bForms D v)) v.domain a s=
       wire ((List.range n).map (bForms D v)) v.domain b s → a=b := by
  apply chart_injective (l:=cube (List.range n)) (cube_nodup List.nodup_range)
    (orig:=bits n) (ls:=L) (dom:=fun v=>cube v.domain)
    (localMap:=fun v x=>wire ((List.range n).map (bForms D v)) v.domain x s)
    (c:=v)
  · exact fun a ha b hb=>bits_injective ha hb
  · intro test
    have a := counts s (fun w=>test (queryBase D n w))
    have orig (x : Assign) : queryBase D n (samples P (pack x s))=bits n x := by
      apply List.map_congr_left
      intro j hj
      rw [Atom.faithful,raw_formula s x j (List.mem_range.mp hj)]
    simpa only [orig,basic_exact,countView] using a
  · exact hv

noncomputable def piece {Y S : Type} {P : List (Fun Y)} (D : FormData (S:=S) P)
    (loc I : List Nat) (v : View S) : Leaf S :=
  ⟨(cube v.domain).length,fun s=>(cube v.domain).countP (fun x=>
    scorePhase loc v.domain (xForms D v) (yForms D v) (oForm D v) I
      (fun j=>(bForms D v (left j),bForms D v (right j))) D.word x s)⟩

                                                                        
                                                                       
theorem second_partition {Y S : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) (pack : Assign → S → Y)
    (m r : Nat) (loc : List Nat) (D : FormData (S:=S) P)
    (E : List S) (sample : S) (raw : List (Form S))
    (wire_s : ∀ x s,wire raw (List.range (2*m+r)) x s=samples B (pack x s))
    (raw_formula : ∀ s x j,j<2*m+r → D.baseValue j (pack x s)=x j)
    (short : q<(List.range m).countP (varying E D.word)) :
    let c := List.range (2*m+r)
    let I := List.range m
    let whole : Leaf S := ⟨(cube c).length,fun s=>(cube c).countP (fun x=>
      originalPhase D loc I s (pack x s))⟩
    ∃ parts,result E I D.word whole parts := by
  let n := 2*m+r
  let c := List.range n
  let I := List.range m
  obtain ⟨L,carry,well⟩ := residual prior pack c List.nodup_range raw wire_s
  let parts := L.map (piece D loc I)
  refine ⟨parts,⟨?_,?_⟩,?_⟩
  · have how := carry sample (fun _=>true)
    simpa [parts,merge,piece,countView,List.map_map,Function.comp_def] using how.symm
  · intro s hs
    have how := carry s (queryPhase D loc I s)
    simpa [parts,merge,piece,countView,List.map_map,Function.comp_def,query_exact,chart_exact] using how.symm
  · intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    obtain ⟨nd,dim,paid,_⟩ := well v hv
    have base := chart_base_injective D pack n L carry raw_formula hv sample
    obtain ⟨i,hi,var,bias,bound⟩ := column_failure E I c (List.range' (2*m) r) v.domain loc
      List.nodup_range nd (SecondChartShapes.base_layout m r) (SecondChartShapes.outside_pairs m r)
      (bForms D v) (xForms D v) (yForms D v) (oForm D v) D.word sample base q (by
        simp [c] at paid ⊢
        omega) short
    refine ⟨?_,.column hi var bound⟩
    simp [piece,cube_size,Nat.pow_pos]

end PEqualNP.Outside.L_meta_32580.ComposedTransport

/- Source segment: BoolLower. -/


namespace PEqualNP.Outside.L_meta_32580.BoolLower
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.FrequencyFlat
open PEqualNP.Outside.L_meta_32580.FrequencySplit PEqualNP.Outside.L_meta_32580.FibreFlat PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.Flatten PEqualNP.Outside.L_meta_32580.ChartGeometry
open PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.CircuitAdapter PEqualNP.Outside.L_meta_32580.CircuitFlatten
open PEqualNP.Outside.L_meta_32580.FirstFold PEqualNP.Outside.L_meta_32580.ComposedTransport PEqualNP.Outside.L_meta_32580.PairSlots
open PEqualNP.Outside.L_meta_32580.CountProfile PEqualNP.Outside.L_meta_32580.RefineProfiles PEqualNP.Outside.L_meta_32580.ColumnObstruction

structure Input {Y S : Type} (n m r : Nat) where
  pack : Assign → S → Y
  yValue : Nat → Fun Y
  baseValue : Nat → Fun Y
  h : S → Bool
  word : S → Nat → Bool
  direction : Assign → Assign
  moves : ∀ s u x,
    (fun j=>yValue j (pack (shift u x) s))=shift (fun j=>yValue j (pack x s)) (direction u)
  support_y : ∀ y,supported (List.range n) (fun j=>yValue j y)
  base_ideal : ∀ s x j,j<2*m+r → baseValue j (pack x s)=x j
  form_base : ∀ j,Span ((raw n yValue).map Form.offset) (baseValue j)
  affineY : List (Form S)
  affine_correct : ∀ x s,wire affineY (List.range (2*m+r)) x s=
    samples ((raw n yValue).map Form.offset) (pack x s)

structure HullData {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (E : List S) (width : Nat) where
  anchor : Assign
  anchor_supported : supported (List.range n) anchor
  generator : Nat → Assign
  gen_supported : ∀ j∈List.range width,supported (List.range n) (generator j)
  independent : ∀ a∈cube (List.range width),∀ b∈cube (List.range width),
    combine (List.range width) generator a=combine (List.range width) generator b → a=b
  anchor_fibre : ∃ s∈E,∃ b∈cube (List.range (2*m+r)),anchor=(fun j=>D.yValue j (D.pack b s))
  generator_fibre : ∀ j∈List.range width,∃ s∈E,∃ b∈cube (List.range (2*m+r)),
    shift anchor (generator j)=(fun i=>D.yValue i (D.pack b s))

theorem base_bank {Y : Type} {B P : List (Fun Y)} {q : Nat}
    (prior : ParamProgram B P q) : ∀ f∈B,f∈P := by
  induction prior with
  | initial => exact fun _ h=>h
  | mul _ _ _ ih =>
    intro f hf
    exact List.mem_append_left _ (ih f hf)

theorem y_span {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r) (j : Nat) :
    Span ((raw n D.yValue).map Form.offset) (D.yValue j) := by
  by_cases h : j<n
  · apply Span.generator
    apply List.mem_map.mpr
    refine ⟨rawY D.yValue j,?_,rfl⟩
    apply List.mem_append_right
    exact List.mem_map_of_mem (List.mem_range.mpr h)
  · have hz : D.yValue j=(fun _=>false) := by
      funext y
      exact D.support_y y j (by simp [h])
    rw [hz]
    exact .const false

def tailPhase {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r) (s : S) (b : Assign) : Bool :=
  D.h s ^^ parity (fun i=>D.word s i && (b (left i) && b (right i))) (List.range m)

def actualError {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (s : S) (x b : Assign) : Bool :=
  C.eval (bits n x++bits n (fun j=>D.yValue j (D.pack b s))) ^^
    (dot (List.range n) x (fun j=>D.yValue j (D.pack b s)) ^^ tailPhase D s b)

def actualLeaf {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r) (C : Circuit) : Leaf S :=
  ⟨(cube (List.range (2*m+r))).length*(cube (List.range n)).length,
    fun s=>count2 (List.range n) (List.range (2*m+r)) (actualError D C s)⟩

def xLeaf {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (u : State Y) : Leaf S :=
  xIntegrate (List.range n) u.domain (List.range (2*m+r)) (coordinates u) (output u C)
    (fun s b j=>D.yValue j (D.pack b s)) (fun s b=>D.pack b s) (tailPhase D)

theorem read_bits (n : Nat) (a : Assign) {j : Nat} (hj : j∈List.range n) :
    TapeKernel.read (bits n a) j=a j := by
  have h := List.mem_range.mp hj
  simp [TapeKernel.read,bits,List.getElem?_map,List.getElem?_range,h]

theorem read_wire_range {Y : Type} (n : Nat) (forms : Nat → Form Y) (d : List Nat)
    (x : Assign) (y : Y) {j : Nat} (hj : j∈List.range n) :
    TapeKernel.read (wire ((List.range n).map forms) d x y) j=value (forms j) d x y := by
  have h := List.mem_range.mp hj
  simp [TapeKernel.read,wire,List.getElem?_map,List.getElem?_range,h]

theorem zero_lift {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (u : State Y) (Fu : FormData (S:=S) u.pool)
    (hx : Fu.xOffset=fun j=>(coordinates u j).offset)
    (hy : Fu.yValue=D.yValue) (hb : Fu.baseValue=D.baseValue)
    (ho : Fu.outOffset=(output u C).offset) (hh : Fu.h=D.h) (hw : Fu.word=D.word)
    (s : S) (b : Assign) :
    discrepancy (List.range n) u.domain (coordinates u) (output u C) zero
      (D.pack b s) (fun j=>D.yValue j (D.pack b s)) (tailPhase D s b)=
      originalPhase Fu (List.range n) (List.range m) s (D.pack b s) := by
  unfold discrepancy originalPhase tailPhase
  rw [hx,hy,hb,ho,hh,hw]
  have d0 {T : Type} (f : Form T) (y : T) : value f u.domain zero y=f.offset y := by
    simp only [value,linear,zero,Bool.and_false,parity_zero,Bool.false_xor]
  rw [d0]
  have dot0 : dot (List.range n) (affineChart (List.range n) u.domain (coordinates u) zero (D.pack b s))
      (fun j=>D.yValue j (D.pack b s)) =
      dot (List.range n) (fun j=>(coordinates u j).offset (D.pack b s))
      (fun j=>D.yValue j (D.pack b s)) := by
    unfold dot
    apply parity_congr
    intro j hj
    simp [affineChart,hj,d0]
  rw [dot0]
  have phase0 :
      parity (fun i=>D.word s i && (D.baseValue (left i) (D.pack b s) &&
        D.baseValue (right i) (D.pack b s))) (List.range m) =
      parity (fun i=>D.word s i && (b (left i)&&b (right i))) (List.range m) := by
    apply parity_congr
    intro i hi
    have low := List.mem_range.mp hi
    rw [D.base_ideal s b (left i) (by simp [left]; omega),
      D.base_ideal s b (right i) (by simp [right]; omega)]
  rw [phase0]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

                                                                    
                                                                     
                                                                          
                                                                             
theorem lower {Y S : Type} {n m r hlen : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (E : List S) (H : HullData D E hlen) (C : Circuit) (legal : ∀ g∈C.gates,Legal g)
    (short : publicCost C.gates<hlen+(List.range m).countP (varying E D.word)) :
    ∃ L,result E (List.range m) D.word (actualLeaf D C) L := by
  let c := List.range n
  let bd := List.range (2*m+r)
  let I := List.range m
  obtain ⟨s0,hs0,b0,hb0,hy0⟩ := H.anchor_fibre
  obtain ⟨L,carry,ok⟩ := first n C legal D.yValue
  have weight (y : Y) : (cube c).length=(L.map (fun u=>(cube u.domain).length)).sum := by
    simpa [c] using carry y (fun _ _=>true)
  have overall : RefineProfiles.agrees E (actualLeaf D C) (L.map (xLeaf D C)) := by
    refine ⟨?_,?_⟩
    · change ((L.map (xLeaf D C)).map Leaf.mass).sum=(cube bd).length*(cube c).length
      simp only [List.map_map,Function.comp_def,xLeaf,xIntegrate,←WeightedCounts.mul_sum]
      rw [weight (D.pack b0 s0)]
    · intro s hs
      let testFor (b : Assign) (values : List Bool) (out : Bool) :=
        out ^^ (dot c (TapeKernel.read values) (fun j=>D.yValue j (D.pack b s)) ^^ tailPhase D s b)
      have law (b : Assign) :
          (cube c).countP (fun x=>actualError D C s x b)=
            (L.map (fun u=>(cube u.domain).countP (fun x=>
               discrepancy c u.domain (coordinates u) (output u C) x (D.pack b s)
                (fun j=>D.yValue j (D.pack b s)) (tailPhase D s b)))).sum := by
        have hp := carry (D.pack b s) (testFor b)
        have left (x : Assign) :
            testFor b (bits n x) (C.eval (bits n x++bits n (fun j=>D.yValue j (D.pack b s))))=
               actualError D C s x b := by
          unfold testFor actualError
          have dotL : dot c (TapeKernel.read (bits n x)) (fun j=>D.yValue j (D.pack b s))=
              dot c x (fun j=>D.yValue j (D.pack b s)) := by
            unfold dot
            apply parity_congr
            intro j hj
            rw [read_bits n x hj]
          rw [dotL]
        have right (u : State Y) (x : Assign) :
            testFor b (wire (c.map (coordinates u)) u.domain x (D.pack b s))
                (value (output u C) u.domain x (D.pack b s)) =
              discrepancy c u.domain (coordinates u) (output u C) x (D.pack b s)
                (fun j=>D.yValue j (D.pack b s)) (tailPhase D s b) := by
          unfold testFor discrepancy
          have dotR : dot c (TapeKernel.read (wire (c.map (coordinates u)) u.domain x (D.pack b s)))
              (fun j=>D.yValue j (D.pack b s)) =
            dot c (affineChart c u.domain (coordinates u) x (D.pack b s))
              (fun j=>D.yValue j (D.pack b s)) := by
            unfold dot
            apply parity_congr
            intro j hj
            rw [read_wire_range n (coordinates u) u.domain x (D.pack b s) hj]
            simp [affineChart,hj]
          rw [dotR]
        simpa only [c,left,right] using hp
      change ((L.map (xLeaf D C)).map (fun a=>a.errors s)).sum=
        ((cube bd).map (fun b=>(cube c).countP (fun x=>actualError D C s x b))).sum
      rw [List.map_map,Function.comp_def]
      exact (count_split (cube bd) (cube c) L (fun b x=>actualError D C s x b)
        (fun u b=>(cube u.domain).countP (fun x=>discrepancy c u.domain (coordinates u)
          (output u C) x (D.pack b s) (fun j=>D.yValue j (D.pack b s)) (tailPhase D s b))) (fun b _=>law b)).symm
  apply refine_all E (actualLeaf D C) (L.map (xLeaf D C)) overall
  intro z hz
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
  obtain ⟨uNd,uDim,fuel,prog,inScope,faithful⟩ := ok u hu
  have pos : 0<(cube u.domain).length := by rw [cube_size]; exact Nat.pow_pos (by decide)
  have bpos : 0<(cube bd).length := by rw [cube_size]; exact Nat.pow_pos (by decide)
  rcases x_curves c u.domain bd (coordinates u) (output u C) E I D.word
    (fun s b j=>D.yValue j (D.pack b s)) (fun s b=>D.pack b s) (tailPhase D)
    D.direction D.moves with done|all
  · exact ⟨[xLeaf D C u],singleton E I D.word _ (Nat.mul_pos bpos pos) done⟩
  · have hitA : FrequencyFlat.agrees c u.domain (coordinates u) (output u C) H.anchor=true := by
      rw [hy0]
      exact all s0 hs0 b0 hb0
    have hitG : ∀ j∈List.range hlen,FrequencyFlat.agrees c u.domain (coordinates u)
        (output u C) (shift H.anchor (H.generator j))=true := by
      intro j hj
      obtain ⟨s,hs,b,hb,eq⟩ := H.generator_fibre j hj
      rw [eq]
      exact all s hs b hb
    have many := hull_cost List.nodup_range uNd List.nodup_range (coordinates u) (output u C)
      (D.pack b0 s0) (faithful (D.pack b0 s0)) H.anchor H.anchor_supported hitA
      H.generator H.gen_supported hitG H.independent
    rw [List.length_range,List.length_range] at many
    have less := residual_short many fuel short
    let FData : FormData (S:=S) u.pool :=
      ⟨fun j=>(coordinates u j).offset,D.yValue,D.baseValue,(output u C).offset,
        fun j=>lookup_inSpan inScope j,fun j=>(y_span D j).weaken (base_bank prog),
        fun j=>(D.form_base j).weaken (base_bank prog),lookup_inSpan inScope C.output,D.h,D.word⟩
    obtain ⟨parts,ex⟩ := second_partition prog D.pack m r c FData E s0 D.affineY
        D.affine_correct D.base_ideal less
    have lifted := scale_result (cube u.domain).length pos ex
    refine ⟨_,⟨?_,?_⟩,lifted.2⟩
    · refine lifted.1.1.trans ?_
      exact Nat.mul_comm _ _
    · intro s hs
      rw [lifted.1.2 s hs]
      change (cube u.domain).length*(cube bd).countP (fun b=>originalPhase FData c I s (D.pack b s))=
        (xLeaf D C u).errors s
      rw [xLeaf,x_const c u.domain bd (coordinates u) (output u C) s
        (fun s b j=>D.yValue j (D.pack b s)) (fun s b=>D.pack b s) (tailPhase D) (all s hs)]
      congr 2
      funext b
      exact (zero_lift D C u FData rfl rfl rfl rfl rfl rfl s b).symm

end PEqualNP.Outside.L_meta_32580.BoolLower

/- Source segment: ExactInput. -/

  
                                                                         
                                                                        
  

namespace PEqualNP.Outside.L_meta_32580.ExactInput
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.PairSlots
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.CircuitFlatten
open PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.MathlibReduction

abbrev Vec (n : Nat) := Fin n → F
abbrev Tuple (m r : Nat) := Vec m × (Vec m × Vec r)
abbrev Wiring (n k m r : Nat) := Vec n ≃ₗ[F] Vec k × Tuple m r

def tupleOf (m r : Nat) (x : Assign) : Tuple m r :=
  (fun i=>ofBit (x (left i.val)),(fun i=>ofBit (x (right i.val)),fun j=>ofBit (x (2*m+j.val))))

def selected (n k m r : Nat) (e : Wiring n k m r) (x : Assign) (s : Vec k) : Vec n :=
  e.symm (s,tupleOf m r x)

def tupleRead (m r : Nat) (j : Nat) (t : Tuple m r) : Bool :=
  if h : pairIndex j<m then
    if j  %  2=0 then toBit (t.1 ⟨pairIndex j,h⟩)
    else toBit (t.2.1 ⟨pairIndex j,h⟩)
  else if h : j-2*m<r then toBit (t.2.2 ⟨j-2*m,h⟩) else false

def baseRead (n k m r : Nat) (e : Wiring n k m r) (j : Nat) (y : Vec n) : Bool :=
  tupleRead m r j (e y).2

theorem tuple_read_of (m r : Nat) (x : Assign) (j : Nat) (hj : j<2*m+r) :
    tupleRead m r j (tupleOf m r x)=x j := by
  unfold tupleRead
  by_cases h : pairIndex j<m
  · rw [dite_eq_left h]
    rcases slot_either j with jLeft|jRight
    · have even : j  %  2=0 := by unfold left pairIndex at jLeft; omega
      rw [if_pos even]
      change toBit (ofBit (x (left (pairIndex j))))=x j
      rw [to_of,←jLeft]
    · have odd : j  %  2≠0 := by unfold right pairIndex at jRight; omega
      rw [if_neg odd]
      change toBit (ofBit (x (right (pairIndex j))))=x j
      rw [to_of,←jRight]
  · have p : 2*m  ≤  j := by unfold pairIndex at h; omega
    have q : j-2*m<r := by omega
    have eq : 2*m+(j-2*m)=j := by omega
    rw [dite_eq_right h,dite_eq_left q]
    change toBit (ofBit (x (2*m+(j-2*m))))=x j
    rw [to_of,eq]

theorem of_xor (a b : Bool) : ofBit (a ^^ b)=ofBit a+ofBit b := by
  rw [←of_to (ofBit a+ofBit b),to_add,to_of,to_of]

theorem tuple_add (m r : Nat) (a b : Assign) :
    tupleOf m r (shift a b)=tupleOf m r a+tupleOf m r b := by
  ext i <;> exact of_xor _ _

theorem tuple_zero (m r : Nat) : tupleOf m r zero=0 := by
  ext i <;> simp [tupleOf,zero,ofBit]

theorem selected_add (n k m r : Nat) (e : Wiring n k m r) (u x : Assign) (s : Vec k) :
    selected n k m r e (shift u x) s =
      selected n k m r e x s+selected n k m r e u 0 := by
  unfold selected
  rw [tuple_add,←map_add]
  congr 2 <;> simp [add_comm]

theorem base_selected (n k m r : Nat) (e : Wiring n k m r)
    (s : Vec k) (x : Assign) (j : Nat) (hj : j<2*m+r) :
    baseRead n k m r e j (selected n k m r e x s)=x j := by
  unfold baseRead selected
  rw [LinearEquiv.apply_symm_apply]
  exact tuple_read_of m r x j hj

theorem bank_of_y {n : Nat} {f : Fun (Vec n)}
    (sp : Span ((List.range n).map (fun j y=>ZMod2Bridge.pack y j)) f) :
    Span ((raw n (fun j y=>ZMod2Bridge.pack y j)).map Form.offset) f := by
  apply sp.weaken
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
  exact List.mem_map.mpr ⟨rawY (fun j y=>ZMod2Bridge.pack y j) j,
     List.mem_append_right _ (List.mem_map_of_mem hj),rfl⟩

theorem base_affine_raw {n k m r : Nat} (e : Wiring n k m r) (j : Nat) :
    Span ((List.range n).map (fun j y=>ZMod2Bridge.pack y j))
      (baseRead n k m r e j) := by
  classical
  unfold baseRead tupleRead
  split
  · rename_i hm
    split
    · let L : Vec n→ₗ[F] F := {
        toFun := fun y=>(e y).2.1 ⟨pairIndex j,hm⟩
        map_add' := by intro; simp
        map_smul' := by intro; simp }
      exact linear_forms_affine L
    · let L : Vec n→ₗ[F] F := {
        toFun := fun y=>(e y).2.2.1 ⟨pairIndex j,hm⟩
        map_add' := by intro; simp
        map_smul' := by intro; simp }
      exact linear_forms_affine L
  · split
    · rename_i hr
      let L : Vec n→ₗ[F] F := {
        toFun := fun y=>(e y).2.2.2 ⟨j-2*m,hr⟩
        map_add' := by intro; simp
        map_smul' := by intro; simp }
      exact linear_forms_affine L
    · exact .const false

theorem base_affine {n k m r : Nat} (e : Wiring n k m r) (j : Nat) :
    Span ((raw n (fun j y=>ZMod2Bridge.pack y j)).map Form.offset)
      (baseRead n k m r e j) :=
  bank_of_y (base_affine_raw e j)

theorem pack_unpack_inside {n : Nat} (x : Assign) {j : Nat} (ok : j<n) :
    ZMod2Bridge.pack (unpack (n:=n) x) j=x j := by
  simp [ZMod2Bridge.pack,unpack,ok,to_of]

def tupleLinear (m r : Nat) : Vec (2*m+r)→ₗ[F] Tuple m r where
  toFun x :=
    (fun i=>x ⟨left i.val,by unfold left; omega⟩,
      (fun i=>x ⟨right i.val,by unfold right; omega⟩,fun j=>x ⟨2*m+j.val,by omega⟩))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem tupleUnpack (m r : Nat) (x : Assign) :
    tupleLinear m r (unpack (n:=2*m+r) x)=tupleOf m r x := rfl

theorem raw_affine {n k m r : Nat} (e : Wiring n k m r) :
    ∃ f : Nat → Form (Vec k),∀ j∈List.range n,∀ x s,
      value (f j) (List.range (2*m+r)) x s=
        ZMod2Bridge.pack (selected n k m r e x s) j := by
  classical
  let L (j : Fin n) : Vec (2*m+r)→ₗ[F] F := {
    toFun := fun x=>e.symm (0,tupleLinear m r x) j
    map_add' := by
      intro x y
      rw [map_add]
      have eq : ((0 : Vec k),tupleLinear m r x+tupleLinear m r y)=
          ((0 : Vec k),tupleLinear m r x)+((0 : Vec k),tupleLinear m r y) := by
        change ((0 : Vec k),_)=(0+0,_)
        rw [zero_add]
      rw [eq,map_add] <;> rfl
    map_smul' := by
      intro t x
      rw [map_smul]
      have eq : ((0 : Vec k),t • tupleLinear m r x)=
          t • ((0 : Vec k),tupleLinear m r x) := by
        change ((0 : Vec k),_)=(t • 0,_)
        rw [smul_zero]
      rw [eq,map_smul] <;> rfl }
  let coeff (j : Fin n) :=
    ZMod2Bridge.pack (fun i : Fin (2*m+r)=>L j (Pi.single i 1))
  let f (j : Nat) : Form (Vec k) :=
    if h:j<n then ⟨coeff ⟨j,h⟩,fun s=>toBit (e.symm (s,0) ⟨j,h⟩)⟩ else TapeKernel.const false
  refine ⟨f,?_⟩
  intro j hj x s
  have h : j<n := List.mem_range.mp hj
  let i : Fin n := ⟨j,h⟩
  have direct : selected n k m r e x s=e.symm (0,tupleOf m r x)+e.symm (s,0) := by
    unfold selected
    rw [←map_add]
    simp
  have lin : linear ⟨coeff i,fun s=>toBit (e.symm (s,0) i)⟩ (List.range (2*m+r)) x =
      toBit (L i (unpack (n:=2*m+r) x)) := by
    rw [functional_row,dot_to_bit]
    unfold linear PEqualNP.Outside.L_meta_32580.OrthogonalCount.dot
    apply parity_congr
    intro j hj
    rw [pack_unpack_inside x (List.mem_range.mp hj)] <;> rfl
  have comp : L i (unpack (n:=2*m+r) x)=e.symm (0,tupleOf m r x) i := by
    change e.symm (0,tupleLinear m r (unpack (n:=2*m+r) x)) i=_
    rw [tupleUnpack]
  simp only [f,h,dite_eq_left, value,ZMod2Bridge.pack,direct,Pi.add_apply,to_add]
  rw [lin,comp]

theorem exact_model {n k m r : Nat} (e : Wiring n k m r)
    (A : Fin m → Vec k) (h : Vec k → F) :
    ∃ D : Input (Y:=Vec n) (S:=Vec k) n m r,
      D.pack=selected n k m r e ∧
      D.yValue=(fun j y=>ZMod2Bridge.pack y j) ∧
      D.h=(fun s=>toBit (h s)) ∧
      ∀ s (i : Fin m),D.word s i=toBit (dotProduct (A i) s) := by
  obtain ⟨f,meaning⟩ := raw_affine e
  let w := (List.range n).map (fun _=>TapeKernel.const (Y:=Vec k) false)++(List.range n).map f
  refine ⟨{
    pack := selected n k m r e
    yValue := fun j y=>ZMod2Bridge.pack y j
    baseValue := baseRead n k m r e
    h := fun s=>toBit (h s)
    word := fun s i=>if h:i<m then toBit (dotProduct (A ⟨i,h⟩) s) else false
    direction := fun x=>ZMod2Bridge.pack (selected n k m r e x 0)
    moves := by intro s u x; rw [selected_add,pack_add]
    support_y := fun y=>mem_cube.mp (pack_mem y)
    base_ideal := base_selected n k m r e
    form_base := base_affine e
    affineY := w
    affine_correct := ?_
  },rfl,rfl,rfl,?_⟩
  · intro x s
    unfold w wire samples raw
    simp only [List.map_append,List.map_map,Function.comp_def]
    congr 1
    · apply List.map_congr_left
      intro j hj
      simp [rawX,const_value]
    · apply List.map_congr_left
      intro j hj
      exact meaning j hj x s
  · intro s i
    simp [i.isLt]

end PEqualNP.Outside.L_meta_32580.ExactInput

/- Source segment: ExactHull. -/

                                                            

namespace PEqualNP.Outside.L_meta_32580.ExactHull
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.MathlibReduction PEqualNP.Outside.L_meta_32580.ExactInput

def embedGenerators {n h : Nat} (L : Vec h→ₗ[F] Vec n) (j : Nat) : Assign :=
  if hj:j<h then ZMod2Bridge.pack (L (Pi.single ⟨j,hj⟩ 1)) else zero

theorem generator_supported {n h : Nat} (L : Vec h→ₗ[F] Vec n) (j : Nat) :
    supported (List.range n) (embedGenerators L j) := by
  unfold embedGenerators
  split
  · exact mem_cube.mp (pack_mem _)
  · exact fun _ _=>rfl

theorem combine_embed {n h : Nat} (L : Vec h→ₗ[F] Vec n) (x : Assign) :
    combine (List.range h) (embedGenerators L) x=ZMod2Bridge.pack (L (unpack (n:=h) x)) := by
  funext j
  by_cases jn : j<n
  · let j' : Fin n := ⟨j,jn⟩
    let l : Vec h→ₗ[F] F := {
      toFun := fun v=>L v j'
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    have q := congrArg toBit (functional_row l (unpack (n:=h) x))
    rw [dot_to_bit] at q
    unfold combine
    rw [ZMod2Bridge.pack,dite_eq_left jn]
    change _=toBit (l (unpack (n:=h) x))
    rw [q]
    unfold dot
    apply parity_congr
    intro i hi
    have hI := List.mem_range.mp hi
    rw [pack_unpack_inside x hI]
    simp [embedGenerators,hI,ZMod2Bridge.pack,jn,l,j',Bool.and_comm]
  · have hn : j∉List.range n := by simpa only [List.mem_range] using jn
    have b := combine_support (c:=List.range n) (d:=List.range h)
      (g:=embedGenerators L) (fun i _=>generator_supported L i) x j hn
    rw [b]
    simp [ZMod2Bridge.pack,jn]

theorem embed_independent {n h : Nat} (L : Vec h→ₗ[F] Vec n) (inj : Function.Injective L) :
    ∀ a∈cube (List.range h),∀ b∈cube (List.range h),
      combine (List.range h) (embedGenerators L) a=combine (List.range h) (embedGenerators L) b → a=b := by
  intro a ha b hb eq
  rw [combine_embed,combine_embed] at eq
  have mapped := congrArg (unpack (n:=n)) eq
  rw [unpack_pack,unpack_pack] at mapped
  have lower := inj mapped
  have nn := congrArg (ZMod2Bridge.pack (n:=h)) lower
  rwa [pack_unpack ha,pack_unpack hb] at nn

                                                                       
                                                                   
                                                           
theorem hull_from_embedding {n m r h : Nat} {S : Type} (D : Input (Y:=Vec n) (S:=S) n m r)
    (yValue : D.yValue=(fun j y=>ZMod2Bridge.pack y j))
    (E : List S) (L : Vec h→ₗ[F] Vec n) (inj : Function.Injective L)
    (a : Vec n)
    (a_t : ∃ s∈E,∃ b∈cube (List.range (2*m+r)),a=D.pack b s)
    (each : ∀ j : Fin h,∃ s∈E,∃ b∈cube (List.range (2*m+r)),
      a+L (Pi.single j 1)=D.pack b s) :
    Nonempty (HullData D E h) := by
  refine ⟨{
    anchor := ZMod2Bridge.pack a
    anchor_supported := mem_cube.mp (pack_mem a)
    generator := embedGenerators L
    gen_supported := fun j _=>generator_supported L j
    independent := embed_independent L inj
    anchor_fibre := ?_
    generator_fibre := ?_
  }⟩
  · obtain ⟨s,hs,b,hb,eq⟩ := a_t
    exact ⟨s,hs,b,hb,by rw [eq,yValue]⟩
  · intro j hj
    have jn := List.mem_range.mp hj
    obtain ⟨s,hs,b,hb,eq⟩ := each ⟨j,jn⟩
    refine ⟨s,hs,b,hb,?_⟩
    rw [embedGenerators,dite_eq_left jn,←pack_add,eq,yValue]

theorem tupleLinear_injective (m r : Nat) : Function.Injective (tupleLinear m r) := by
  intro x y same
  funext i
  by_cases h : PairSlots.pairIndex i.val<m
  · let f : Fin m := ⟨PairSlots.pairIndex i.val,h⟩
    rcases PairSlots.slot_either i.val with left|right
    · have e := congrArg (fun u : Tuple m r=>u.1 f) same
      have fEq : (⟨PairSlots.left f.val,by unfold PairSlots.left; omega⟩ : Fin (2*m+r))=i :=
        Fin.ext left.symm
      simpa only [tupleLinear,LinearMap.coe_mk,AddHom.coe_mk,fEq] using e
    · have e := congrArg (fun u : Tuple m r=>u.2.1 f) same
      have fEq : (⟨PairSlots.right f.val,by unfold PairSlots.right; omega⟩ : Fin (2*m+r))=i :=
        Fin.ext right.symm
      simpa only [tupleLinear,LinearMap.coe_mk,AddHom.coe_mk,fEq] using e
  · have p : 2*m  ≤  i.val := by unfold PairSlots.pairIndex at h; omega
    have q : i.val-2*m<r := by omega
    let f : Fin r := ⟨i.val-2*m,q⟩
    have eq : 2*m+f.val=i.val := by dsimp [f]; omega
    have e := congrArg (fun u : Tuple m r=>u.2.2 f) same
    have fEq : (⟨2*m+f.val,by omega⟩ : Fin (2*m+r))=i := Fin.ext eq
    simpa only [tupleLinear,LinearMap.coe_mk,AddHom.coe_mk,fEq] using e

def front {b d : Nat} (x : Vec (b+d)) : Vec b := fun i=>x (i.castAdd d)
def rear {b d : Nat} (x : Vec (b+d)) : Vec d := fun i=>x (i.natAdd b)

theorem front_single_left {b d : Nat} (i : Fin b) :
    front (b:=b) (d:=d) (Pi.single (i.castAdd d) (1:F))=Pi.single i 1 := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [front,Pi.single_apply]
  · have e : j.castAdd d≠i.castAdd d := fun e=>hj (Fin.ext (congrArg (fun x : Fin (b+d)=>x.val) e))
    simp [front,Pi.single_apply,hj,e]

theorem rear_single_left {b d : Nat} (i : Fin b) :
    rear (b:=b) (d:=d) (Pi.single (i.castAdd d) (1:F))=0 := by
  funext j
  have e : j.natAdd b≠i.castAdd d := by
    intro e
    have vv := congrArg Fin.val e
    simp at vv
    omega
  simp [rear,Pi.single_apply,e]

theorem front_single_right {b d : Nat} (i : Fin d) :
    front (b:=b) (d:=d) (Pi.single (i.natAdd b) (1:F))=0 := by
  funext j
  have e : j.castAdd d≠i.natAdd b := by
    intro e
    have vv := congrArg Fin.val e
    simp at vv
    omega
  simp [front,Pi.single_apply,e]

theorem rear_single_right {b d : Nat} (i : Fin d) :
    rear (b:=b) (d:=d) (Pi.single (i.natAdd b) (1:F))=Pi.single i 1 := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [rear,Pi.single_apply]
  · have e : j.natAdd b≠i.natAdd b := by
      intro e
      apply hj
      apply Fin.ext
      have vv := congrArg Fin.val e
      simp at vv
      omega
    simp [rear,Pi.single_apply,hj,e]

theorem unpack_unit_eq {b : Nat} (i : Fin b) :
    unpack (n:=b) (unit i.val)=Pi.single i 1 := by
  funext j
  by_cases e : j=i
  · subst j
    simp [unpack,unit,ofBit,Pi.single_apply]
  · have f : j.val≠i.val := fun h=>e (Fin.ext h)
    simp [unpack,unit,ofBit,Pi.single_apply,e,f]

noncomputable def exactEmbedding {n k m r d : Nat} (e : Wiring n k m r) (w : Fin d → Vec k) :
    Vec (2*m+r+d)→ₗ[F] Vec n where
  toFun x := e.symm (Fintype.linearCombination F w (rear x),tupleLinear m r (front x))
  map_add' := by
    intro x y
    have ff : front (b:=2*m+r) (d:=d) (x+y)=front x+front y := rfl
    have rr : rear (b:=2*m+r) (d:=d) (x+y)=rear x+rear y := rfl
    rw [ff,rr,map_add,map_add]
    exact e.symm.map_add
      (Fintype.linearCombination F w (rear x), tupleLinear m r (front x))
      (Fintype.linearCombination F w (rear y), tupleLinear m r (front y))
  map_smul' := by
    intro q x
    have ff : front (b:=2*m+r) (d:=d) (q • x)=q • front x := rfl
    have rr : rear (b:=2*m+r) (d:=d) (q • x)=q • rear x := rfl
    rw [ff,rr,map_smul,map_smul]
    exact e.symm.map_smul q
      (Fintype.linearCombination F w (rear x), tupleLinear m r (front x))

theorem exactEmbedding_injective {n k m r d : Nat} (e : Wiring n k m r) (w : Fin d → Vec k)
    (ind : LinearIndependent F w) : Function.Injective (exactEmbedding e w) := by
  intro x y same
  have q := e.symm.injective same
  have q1 := congrArg Prod.fst q
  have q2 := congrArg Prod.snd q
  have rr : rear x=rear y := ind.fintypeLinearCombination_injective q1
  have ff : front x=front y := tupleLinear_injective m r q2
  funext j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j
  · exact congrFun ff i
  · exact congrFun rr i

                                                                         
                                                                       
theorem exact_hull {n k m r d : Nat} (e : Wiring n k m r)
    (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (dDef : d=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k)))))
    (dCard : E.card=d+1) (D : Input (Y:=Vec n) (S:=Vec k) n m r)
    (pD : D.pack=selected n k m r e) (yD : D.yValue=(fun j y=>ZMod2Bridge.pack y j)) :
    Nonempty (HullData D E.toList (2*m+r+d)) := by
  classical
  have card : (E.erase a).card=d := by rw [Finset.card_erase_of_mem ha,dCard]; omega
  let en : Fin d≃↥(E.erase a) := (Finset.equivFinOfCardEq card).symm
  let w : Fin d → Vec k := fun i=>(en i).val-a
  have dCard' : E.card=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+1 :=
    dCard.trans (congrArg (fun j=>j+1) dDef)
  have ind := (selector_independent E a ha dCard').comp en en.injective
  let l := exactEmbedding e w
  let aY := selected n k m r e zero a
  apply hull_from_embedding D yD E.toList l (exactEmbedding_injective e w ind) aY
  · exact ⟨a,by simpa using ha,zero,mem_cube.mpr (fun _ _=>rfl),by rw [pD]⟩
  · intro j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j
    · refine ⟨a,by simpa using ha,unit i.val,mem_cube.mpr (unit_supported (by simp)),?_⟩
      rw [pD]
      change aY+e.symm (Fintype.linearCombination F w
        (rear (Pi.single (i.castAdd d) 1)),tupleLinear m r (front (Pi.single (i.castAdd d) 1)))=
          selected n k m r e (unit i.val) a
      rw [rear_single_left,front_single_left,map_zero,←unpack_unit_eq i,tupleUnpack]
      unfold aY selected
      rw [←map_add,tuple_zero]
      simp
    · let s : Vec k := (en i).val
      have hs : s∈E := Finset.mem_of_mem_erase (en i).property
      refine ⟨s,by simpa using hs,zero,mem_cube.mpr (fun _ _=>rfl),?_⟩
      rw [pD]
      change aY+e.symm (Fintype.linearCombination F w
        (rear (Pi.single (i.natAdd (2*m+r)) 1)),tupleLinear m r (front (Pi.single (i.natAdd (2*m+r)) 1)))=
          selected n k m r e zero s
      rw [rear_single_right,front_single_right,Fintype.linearCombination_apply_single,one_smul,map_zero]
      unfold aY selected
      rw [←map_add,tuple_zero]
      simp [w,s,sub_eq_add_neg,add_comm,add_left_comm,add_assoc]

end PEqualNP.Outside.L_meta_32580.ExactHull

/- Source segment: ExactScore. -/

                                                                            

namespace PEqualNP.Outside.L_meta_32580.ExactScore
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.FirstFold PEqualNP.Outside.L_meta_32580.CircuitFlatten
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.MathlibReduction PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.BoolLower

def tuplePack (m r : Nat) (t : Tuple m r) : Assign :=
  fun j=>tupleRead m r j t

theorem pack_tuple_mem (m r : Nat) (t : Tuple m r) :
    tuplePack m r t∈cube (List.range (2*m+r)) := by
  apply mem_cube.mpr
  intro j hj
  have no : ¬j<2*m+r := by simpa only [List.mem_range] using hj
  have no1 : ¬pairIndex j<m := by unfold pairIndex; omega
  have no2 : ¬j-2*m<r := by omega
  simp [tuplePack,tupleRead,no1,no2]

theorem tuple_pack_inv (m r : Nat) (t : Tuple m r) :
    tupleOf m r (tuplePack m r t)=t := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    have even : left i.val % 2=0 := by unfold left; omega
    simp [tupleOf,tuplePack,tupleRead,pairIndex_left,i.isLt,even,of_to]
  · funext i
    have odd : right i.val % 2≠0 := by unfold right; omega
    simp [tupleOf,tuplePack,tupleRead,pairIndex_right,i.isLt,odd,of_to]
  · funext i
    have no : ¬pairIndex (2*m+i.val)<m := by unfold pairIndex; omega
    simp [tupleOf,tuplePack,tupleRead,no,i.isLt,of_to]

theorem pack_tuple_inv (m r : Nat) {x : Assign} (hx : x∈cube (List.range (2*m+r))) :
    tuplePack m r (tupleOf m r x)=x := by
  funext i
  by_cases go : i<2*m+r
  · exact tuple_read_of m r x i go
  · have h : i∉List.range (2*m+r) := by simp [go]
    exact (mem_cube.mp (pack_tuple_mem m r _) i h).trans (mem_cube.mp hx i h).symm

def pairs {A B : Type} (l : List A) (r : List B) : List (A×B) :=
  r.flatMap (fun b=>l.map (fun a=>(a,b)))

theorem pairs_nodup {A B : Type} {l : List A} {r : List B} (hl : l.Nodup) (hr : r.Nodup) :
    (pairs l r).Nodup := by
  unfold pairs
  rw [List.nodup_iff_pairwise_ne,List.pairwise_flatMap]
  refine ⟨fun b _=>nodup_map_from l hl (fun a=>(a,b)) (fun _ _ _ _ h=>congrArg Prod.fst h),?_⟩
  exact (List.nodup_iff_pairwise_ne.mp hr).imp_of_mem (fun {a b} _ _ ne x hx y hy eq=>by
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hy
      exact ne (congrArg Prod.snd eq))

theorem pairs_count {A B : Type} (l : List A) (r : List B) (f : A×B → Bool) :
    (pairs l r).countP f=(r.map (fun b=>l.countP (fun a=>f (a,b)))).sum := by
  simp only [pairs,List.countP_flatMap,List.countP_map,Function.comp_def]

theorem complete_pairs {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (l : List A) (r : List B) (allL : ∀ a,a∈l) (allR : ∀ b,b∈r) :
    (pairs l r).toFinset=Finset.univ := by
  ext z
  refine ⟨fun _=>Finset.mem_univ _,fun _=>?_⟩
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr ⟨z.2,allR _,List.mem_map.mpr ⟨z.1,allL _,by cases z; rfl⟩⟩

def fieldError {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (C : Circuit) (s : Vec k) (x : Vec n) (t : Tuple m r) : Bool :=
  let y := e.symm (s,t)
  let value := dotProduct x y + h s + ∑ i, dotProduct (A i) s * t.1 i * t.2.1 i
  C.eval (List.ofFn (fun j=>toBit (x j))++List.ofFn (fun j=>toBit (y j))) ^^ toBit value

theorem field_error_agrees {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (D : Input (Y:=Vec n) (S:=Vec k) n m r)
    (pD : D.pack=selected n k m r e) (yD : D.yValue=(fun j y=>ZMod2Bridge.pack y j))
    (hD : D.h=(fun s=>toBit (h s))) (wD : ∀ s (i : Fin m),D.word s i=toBit (dotProduct (A i) s))
    (C : Circuit) (s : Vec k) (x b : Assign) (xs : x∈cube (List.range n)) :
    fieldError e A h C s (unpack x) (tupleOf m r b)=actualError D C s x b := by
  unfold fieldError actualError tailPhase
  rw [pD,yD,hD]
  simp only [selected,to_add,Bool.xor_assoc]
  have q1 := bits_pack (unpack (n:=n) x)
  rw [pack_unpack xs] at q1
  have q2 := bits_pack (e.symm (s,tupleOf m r b))
  rw [show List.ofFn (fun j : Fin n=>toBit (unpack x j))=bits n x from q1,
    show List.ofFn (fun j : Fin n=>toBit (e.symm (s,tupleOf m r b) j))=
       bits n (ZMod2Bridge.pack (e.symm (s,tupleOf m r b))) from q2]
  rw [dot_to_bit,pack_unpack xs,finite_to_parity]
  have p : parity (fun j=>if h:j<m then
      toBit (dotProduct (A ⟨j,h⟩) s * (tupleOf m r b).1 ⟨j,h⟩ * (tupleOf m r b).2.1 ⟨j,h⟩)
      else false) (List.range m) =
      parity (fun j=>D.word s j && (b (left j) && b (right j))) (List.range m) := by
    apply parity_congr
    intro j hj
    have h := List.mem_range.mp hj
    simp only [h,dite_eq_left,to_mul,tupleOf,to_of,Pi.zero_apply,←Bool.and_assoc,wD s ⟨j,h⟩]
  rw [p]

theorem error_card {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (D : Input (Y:=Vec n) (S:=Vec k) n m r)
    (pD : D.pack=selected n k m r e) (yD : D.yValue=(fun j y=>ZMod2Bridge.pack y j))
    (hD : D.h=(fun s=>toBit (h s))) (wD : ∀ s (i : Fin m),D.word s i=toBit (dotProduct (A i) s))
    (C : Circuit) (s : Vec k) :
    (Finset.univ.filter (fun z : (Vec n)×Tuple m r=>fieldError e A h C s z.1 z.2=true)).card=
      (actualLeaf D C).errors s := by
  classical
  let L := (cube (List.range n)).map (unpack (n:=n))
  let R := (cube (List.range (2*m+r))).map (tupleOf m r)
  have ndL : L.Nodup := nodup_map_from _ (cube_nodup List.nodup_range) _ (by
    intro a ha b hb q
    have q' := congrArg (ZMod2Bridge.pack (n:=n)) q
    rwa [pack_unpack ha,pack_unpack hb] at q')
  have ndR : R.Nodup := nodup_map_from _ (cube_nodup List.nodup_range) _ (by
    intro a ha b hb q
    have q' := congrArg (tuplePack m r) q
    rwa [pack_tuple_inv m r ha,pack_tuple_inv m r hb] at q')
  have univL : ∀ a,a∈L := fun a=>List.mem_map.mpr ⟨ZMod2Bridge.pack a,pack_mem a,unpack_pack a⟩
  have univR : ∀ b,b∈R := fun b=>List.mem_map.mpr ⟨tuplePack m r b,pack_tuple_mem m r b,tuple_pack_inv m r b⟩
  rw [←complete_pairs L R univL univR]
  rw [(pairs_nodup ndL ndR).card_eq_countP]
  simp only [decide_eq_true_eq,pairs_count,List.countP_map,List.map_map,Function.comp_def,L,R]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply List.countP_congr
  intro x hx
  rw [field_error_agrees e A h D pD yD hD wD C s x b hx,decide_eq_true_eq]

theorem mass_eq {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r) (C : Circuit) :
    (actualLeaf D C).mass=2^(n+(2*m+r)) := by
  simp [actualLeaf,cube_size,pow_add,Nat.mul_comm]

noncomputable def fieldScore {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (C : Circuit) (s : Vec k) : ℝ :=
  (∑ x : Vec n, ∑ b : Vec m, ∑ c : Vec m, ∑ z : Vec r,
    let y := e.symm (s,(b,(c,z)))
    let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
    if C.eval (List.ofFn (fun j : Fin n=>decide (x j=1))++
        List.ofFn (fun j : Fin n=>decide (y j=1))) = decide (v=1) then (1:ℝ) else -1) /
    2^(n+(2*m+r))

theorem sign_error (actual target : Bool) :
    (if actual=target then (1:ℝ) else -1)=
      (if actual ^^ target then (-1:ℝ) else 1) := by
  cases actual <;> cases target <;> rfl

theorem fieldScore_bad {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (C : Circuit) (s : Vec k) :
    fieldScore e A h C s =
      (∑ z : Vec n × Tuple m r, if fieldError e A h C s z.1 z.2 then (-1:ℝ) else 1) /
        2^(n+(2*m+r)) := by
  unfold fieldScore
  simp only [Fintype.sum_prod_type]
  apply congrArg (fun t : ℝ=>t/2^(n+(2*m+r)))
  refine Finset.sum_congr rfl (fun x _=>?_)
  refine Finset.sum_congr rfl (fun b _=>?_)
  refine Finset.sum_congr rfl (fun c _=>?_)
  refine Finset.sum_congr rfl (fun z _=>?_)
  exact sign_error _ _

theorem fieldSample_card (n m r : Nat) :
    Fintype.card (Vec n × Tuple m r)=2^(n+(2*m+r)) := by
  simp only [Vec,Tuple,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card,F]
  rw [show n+(2*m+r)=n+(m+(m+r)) from by omega]
  simp only [pow_add]

theorem field_loss_formula {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (D : Input (Y:=Vec n) (S:=Vec k) n m r)
    (pD : D.pack=selected n k m r e) (yD : D.yValue=(fun j y=>ZMod2Bridge.pack y j))
    (hD : D.h=(fun s=>toBit (h s))) (wD : ∀ s (i : Fin m),D.word s i=toBit (dotProduct (A i) s))
    (C : Circuit) (s : Vec k) :
    1-fieldScore e A h C s = 2*((actualLeaf D C).errors s:ℝ)/(actualLeaf D C).mass := by
  rw [fieldScore_bad,signed_count,error_card e A h D pD yD hD wD C s,fieldSample_card,mass_eq]
  push_cast
  have hh : (2:ℝ)^(n+(2*m+r))≠0 := by positivity
  field_simp [hh]
  ring

end PEqualNP.Outside.L_meta_32580.ExactScore

/- Source segment: ProfileCore. -/


namespace PEqualNP.Outside.L_meta_32580.Profile
open scoped BigOperators
noncomputable section
variable {S I J : Type*}

def varies (E : Finset S) (word : I → S → Bool) (i : I) : Prop :=
  ∃ s∈E, ∃ t∈E, word i s≠word i t

def isolates (E : Finset S) (word : I → S → Bool) (u : S) : Prop :=
  ∃ i b, ∀ s∈E, word i s≠b ↔ s=u

def loss (E : Finset S) (μ ell : S → ℝ) : ℝ := ∑ s∈E, μ s * ell s

def column (E : Finset S) (word : I → S → Bool) (μ : S → ℝ) (i : I) (b : Bool) : ℝ :=
  (∑ s∈E, if word i s≠b then μ s else 0) / 2

def OptionValue (E : Finset S) (word : I → S → Bool) (μ : S → ℝ) (v : ℝ) : Prop :=
  (∃ s∈E, v=μ s) ∨ ∃ i b, varies E word i ∧ v=column E word μ i b

                                                                       
structure Leaf (E : Finset S) (word : I → S → Bool) (ell : S → ℝ) : Prop where
  nonneg : ∀ s∈E, 0 ≤ ell s
  obstruction :
    (∃ u∈E, 1 ≤ ell u) ∨
    (∀ s∈E, (1/2:ℝ) ≤ ell s) ∨
    ∃ i b, varies E word i ∧ ∀ s∈E, word i s≠b  →  (1/2:ℝ) ≤ ell s

structure Mix (E : Finset S) (word : I → S → Bool) (T : Finset J)
    (w : J → ℝ) (ell : J → S → ℝ) (avg : S → ℝ) : Prop where
  nonnegWeight : ∀ j∈T, 0 ≤ w j
  totalWeight : ∑ j∈T,w j=1
  leaf : ∀ j∈T, Leaf E word (ell j)
  combines : ∀ s∈E, avg s=∑ j∈T,w j*ell j s

theorem mismatch_exists {E : Finset S} {word : I → S → Bool} {i : I} (h : varies E word i)
    (b : Bool) : ∃ x∈E, word i x≠b := by
  obtain ⟨x,hx,y,hy,diff⟩ := h
  by_cases e : word i x=b
  · exact ⟨y,hy,fun k=>diff (e.trans k.symm)⟩
  · exact ⟨x,hx,e⟩

theorem half_fits_some (E : Finset S) (hE : 2 ≤ E.card) (μ : S → ℝ) (nonneg : ∀ s∈E, 0 ≤ μ s) :
    ∃ s∈E, μ s ≤ (∑ x∈E,μ x)/2 := by
  classical
  have pos : 0<E.card := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp pos
  have rest : 0<(E.erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp rest
  have hve := Finset.mem_erase.mp hv
  have below : μ v ≤ ∑ x∈E.erase u,μ x :=
    Finset.single_le_sum (fun s hs=>nonneg s (Finset.mem_of_mem_erase hs)) hv
  have split := Finset.sum_erase_add _ μ hu
  by_cases some : μ u ≤ (∑ x∈E,μ x)/2
  · exact ⟨u,hu,some⟩
  · exact ⟨v,hve.2,by linarith⟩

theorem Leaf.lower {E : Finset S} {word : I → S → Bool} {ell μ : S → ℝ}
    (g : Leaf E word ell) (hE : 2 ≤ E.card) (μ0 : ∀ s∈E,0 ≤ μ s) {v : ℝ}
    (minimum : ∀ z, OptionValue E word μ z  →  v ≤ z) : v ≤ loss E μ ell := by
  classical
  have nonneg : ∀ s∈E,0 ≤ μ s*ell s := fun s hs=>mul_nonneg (μ0 s hs) (g.nonneg s hs)
  rcases g.obstruction with ⟨u,hu,hu1⟩ | global | ⟨i,b,vr,mis⟩
  · have p := minimum _ (Or.inl ⟨u,hu,rfl⟩)
    have q : μ u ≤ μ u*ell u := by
      simpa using mul_le_mul_of_nonneg_left hu1 (μ0 u hu)
    exact p.trans (q.trans (Finset.single_le_sum nonneg hu))
  · obtain ⟨s,hs,small⟩ := half_fits_some E hE μ μ0
    apply (minimum _ (Or.inl ⟨s,hs,rfl⟩)).trans (small.trans ?_)
    rw [div_eq_mul_inv,Finset.sum_mul]
    exact Finset.sum_le_sum (fun x hx=>mul_le_mul_of_nonneg_left (by
      simpa [div_eq_mul_inv] using global x hx) (μ0 x hx))
  · apply (minimum _ (Or.inr ⟨i,b,vr,rfl⟩)).trans
    unfold column loss
    rw [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s hs
    by_cases h : word i s≠b
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_left (by simpa [div_eq_mul_inv] using mis s hs h) (μ0 s hs)
    · simpa [h] using nonneg s hs

theorem Leaf.uniform {E : Finset S} {word : I → S → Bool} {ell : S → ℝ}
    (g : Leaf E word ell) (hE : 2 ≤ E.card) : (1/2:ℝ) ≤ ∑ s∈E,ell s := by
  classical
  rcases g.obstruction with ⟨u,hu,one⟩ | half | ⟨i,b,var,m⟩
  · have q := Finset.single_le_sum g.nonneg hu
    linarith
  · have q : ∑ s∈E,(1/2:ℝ)  ≤  ∑ s∈E,ell s := Finset.sum_le_sum half
    have e : (2:ℝ)  ≤  E.card := by exact_mod_cast hE
    simp only [Finset.sum_const,nsmul_eq_mul] at q
    linarith
  · obtain ⟨u,hu,hit⟩ := mismatch_exists var b
    exact (m u hu hit).trans (Finset.single_le_sum g.nonneg hu)

theorem Leaf.isolates_of_equal {E : Finset S} {word : I → S → Bool} {ell : S → ℝ}
    (g : Leaf E word ell) (hE : 2 ≤ E.card) (equal : ∑ s∈E,ell s=(1/2:ℝ))
    {u : S} (hu : u∈E) (lossU : 0<ell u) : isolates E word u := by
  classical
  rcases g.obstruction with ⟨s,hs,one⟩ | half | ⟨i,b,var,m⟩
  · have q := Finset.single_le_sum g.nonneg hs
    linarith
  · have q : ∑ s∈E,(1/2:ℝ)  ≤  ∑ s∈E,ell s := Finset.sum_le_sum half
    have ec : (2:ℝ)  ≤  E.card := by exact_mod_cast hE
    simp only [Finset.sum_const,nsmul_eq_mul] at q
    linarith
  · have same (s : S) (hs : s∈E) (hm : word i s≠b) : s=u := by
      by_contra ne
      have uEr : u∈E.erase s := Finset.mem_erase.mpr ⟨Ne.symm ne,hu⟩
      have small : ell u ≤ ∑ x∈E.erase s,ell x :=
        Finset.single_le_sum (fun j hj=>g.nonneg j (Finset.mem_of_mem_erase hj)) uEr
      have split := Finset.sum_erase_add _ ell hs
      have sHalf := m s hs hm
      linarith
    obtain ⟨s,hs,hm⟩ := mismatch_exists var b
    have eq := same s hs hm
    exact ⟨i,b,fun t ht=>⟨same t ht,fun k=>k.symm ▸ (eq ▸ hm)⟩⟩

theorem Mix.linear {E : Finset S} {word : I → S → Bool} {T : Finset J}
    {w : J → ℝ} {ell : J → S → ℝ} {avg μ : S → ℝ} (m : Mix E word T w ell avg) :
    loss E μ avg=∑ j∈T,w j*loss E μ (ell j) := by
  unfold loss
  calc
    _ = ∑ s∈E,∑ j∈T,μ s*(w j*ell j s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [m.combines s hs,Finset.mul_sum]
    _ = ∑ j∈T,∑ s∈E,μ s*(w j*ell j s) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ac_rfl

theorem Mix.lower {E : Finset S} {word : I → S → Bool} {T : Finset J}
    {w : J → ℝ} {ell : J → S → ℝ} {avg μ : S → ℝ} (m : Mix E word T w ell avg)
    (hE : 2 ≤ E.card) (μ0 : ∀s∈E,0 ≤ μ s) {v : ℝ}
    (low : ∀ z,OptionValue E word μ z  →  v ≤ z) : v ≤ loss E μ avg := by
  rw [m.linear]
  calc
    v = ∑ j∈T,w j*v := by rw [←Finset.sum_mul,m.totalWeight,one_mul]
    _  ≤  _ := Finset.sum_le_sum
      (fun j hj => mul_le_mul_of_nonneg_left ((m.leaf j hj).lower hE μ0 low) (m.nonnegWeight _ hj))

theorem Mix.uniform {E : Finset S} {word : I → S → Bool} {T : Finset J}
    {w : J → ℝ} {ell : J → S → ℝ} {avg : S → ℝ} (m : Mix E word T w ell avg) (hE : 2 ≤ E.card) :
    (1/2:ℝ) ≤ ∑ s∈E,avg s := by
  have f := m.linear (μ:=fun _=>1)
  simp only [loss,one_mul] at f
  rw [f]
  calc
    (1/2:ℝ) = ∑ j∈T,w j*(1/2:ℝ) := by rw [←Finset.sum_mul,m.totalWeight,one_mul]
    _  ≤  _ := Finset.sum_le_sum (fun j hj=>mul_le_mul_of_nonneg_left
      ((m.leaf j hj).uniform hE) (m.nonnegWeight j hj))

theorem Mix.isolation {E : Finset S} {word : I → S → Bool} {T : Finset J}
    {w : J → ℝ} {ell : J → S → ℝ} {avg : S → ℝ} (m : Mix E word T w ell avg) (hE : 2 ≤ E.card)
    (upper : ∀ s∈E,avg s ≤ 1/(2*(E.card:ℝ))) : ∀ u∈E,isolates E word u := by
  classical
  let top : ℝ := 1/(2*(E.card:ℝ))
  have npos : 0<E.card := by omega
  have cpos : (0:ℝ)<E.card := by exact_mod_cast npos
  have top_pos : 0<top := by dsimp [top]; positivity
  have total_top : (∑ _s∈E,top)=(1/2:ℝ) := by
    simp only [Finset.sum_const,nsmul_eq_mul,top]
    field_simp
  have lower := m.uniform hE
  have upper_sum := Finset.sum_le_sum upper
  change (∑ s∈E,avg s)  ≤  ∑ _s∈E,top at upper_sum
  rw [total_top] at upper_sum
  have exactSum := le_antisymm upper_sum lower
  intro u hu
  have sumZero : (∑ s∈E,(top-avg s))=0 := by
    rw [Finset.sum_sub_distrib,total_top,exactSum,sub_self]
  have allPoint := (Finset.sum_eq_zero_iff_of_nonneg (fun s hs=>sub_nonneg.mpr (upper s hs))).mp sumZero
  have uPos : 0<avg u := by have := allPoint u hu; linarith
  have find : ∃ j∈T,0<w j*ell j u := by
    by_contra fail
    push_neg at fail
    have le : (∑ j∈T,w j*ell j u) ≤ ∑ _j∈T,(0:ℝ) := Finset.sum_le_sum fail
    rw [←m.combines u hu] at le
    simp at le
    linarith
  obtain ⟨j,hj,positive⟩ := find
  have m0 := m.nonnegWeight j hj
  have x0 := (m.leaf j hj).nonneg u hu
  have ww : 0<w j := by
    by_contra no
    have z : w j=0 := le_antisymm (le_of_not_gt no) m0
    simp [z] at positive
  have ellPos : 0<ell j u := by
    by_contra no
    have z : ell j u=0 := le_antisymm (le_of_not_gt no) x0
    simp [z] at positive
  have linear := m.linear (μ:=fun _=>1)
  simp only [loss,one_mul] at linear
  have sumGap : (∑ k∈T, w k*((∑ s∈E,ell k s)-1/2))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul] 
    rw [←linear,m.totalWeight,exactSum,one_mul,sub_self]
  have nonnegGap : ∀ k∈T,0 ≤ w k*((∑ s∈E,ell k s)-1/2) := fun k hk=>
    mul_nonneg (m.nonnegWeight k hk) (sub_nonneg.mpr ((m.leaf k hk).uniform hE))
  have each := (Finset.sum_eq_zero_iff_of_nonneg nonnegGap).mp sumGap j hj
  have zero := (mul_eq_zero.mp each).resolve_left (ne_of_gt ww)
  exact (m.leaf j hj).isolates_of_equal hE (sub_eq_zero.mp zero) hu ellPos

theorem minimum_exists [Fintype I] (E : Finset S) (word : I → S → Bool) (μ : S → ℝ)
    (hne : E.Nonempty) :
    ∃ v, OptionValue E word μ v ∧ ∀ z, OptionValue E word μ z  →  v ≤ z := by
  classical
  let P := E.image μ
  let D : Finset (I×Bool) := Finset.univ.filter (fun j=>varies E word j.1)
  let C := D.image (fun j=>column E word μ j.1 j.2)
  let opts := P∪C
  have exact_mem (u : ℝ) : u∈opts ↔ OptionValue E word μ u := by
    change u∈P∪C ↔ _
    rw [Finset.mem_union]
    constructor
    · intro m
      rcases m with m|m
      · obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp m
        exact Or.inl ⟨s,hs,eq.symm⟩
      · obtain ⟨⟨i,b⟩,hi,eq⟩ := Finset.mem_image.mp m
        exact Or.inr ⟨i,b,(Finset.mem_filter.mp hi).2,eq.symm⟩
    · intro m
      rcases m with ⟨s,hs,eq⟩|⟨i,b,hi,eq⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨s,hs,eq.symm⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨(i,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,eq.symm⟩)
  obtain ⟨s,hs⟩ := hne
  have nonempty : opts.Nonempty := ⟨μ s,(exact_mem _).mpr (Or.inl ⟨s,hs,rfl⟩)⟩
  exact ⟨opts.min' nonempty,(exact_mem _).mp (Finset.min'_mem _ _),
    fun z hz=>Finset.min'_le _ _ ((exact_mem _).mpr hz)⟩

end
end PEqualNP.Outside.L_meta_32580.Profile

/- Source segment: FieldProfiles. -/

                                                               
                                                                        

namespace PEqualNP.Outside.L_meta_32580.FieldProfiles
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.ColumnObstruction PEqualNP.Outside.L_meta_32580.CountProfile PEqualNP.Outside.L_meta_32580.RefineProfiles
open PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.ExactScore PEqualNP.Outside.L_meta_32580.ExactInput
open PEqualNP.CircuitLowerBounds

theorem sum_list {A R : Type} [AddCommMonoid R] (l : List A) (f : A → R) :
    (∑ j : Fin l.length,f l[j])=(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change (∑ i : Fin (l.length+1), f (a::l)[i])=f a+(l.map f).sum
    rw [Fin.sum_univ_succ]
    change f a+(∑ i : Fin l.length,f l[i])=f a+(l.map f).sum
    rw [ih]

theorem varies_project {S : Type} (E : Finset S) (word : S → Nat → Bool) (i : Nat) :
    varying E.toList word i=true ↔ PEqualNP.Outside.L_meta_32580.Profile.varies E (fun j s=>word s j) i := by
  rw [varies]
  simp [PEqualNP.Outside.L_meta_32580.Profile.varies]

theorem leaf_real {S : Type} (E : Finset S) {m : Nat} (word : S → Nat → Bool)
    (a : Leaf S) (pos : 0<a.mass)
    (cert : Obstruction E.toList (List.range m) word a) :
    PEqualNP.Outside.L_meta_32580.Profile.Leaf E (fun (i : Fin m) s=>word s i.val)
      (fun s=>2*(a.errors s:ℝ)/(a.mass:ℝ)) := by
  have mpos : (0:ℝ)<a.mass := by exact_mod_cast pos
  refine ⟨fun s _=>by positivity,?_⟩
  cases cert with
  | @missed s hs enough =>
    left
    refine ⟨s,by simpa using hs,?_⟩
    rw [le_div_iff₀ mpos,one_mul]
    exact_mod_cast enough
  | allHalf proof =>
    right;left
    intro s hs
    have q := proof s (by simpa using hs)
    have q' : (a.mass:ℝ) ≤ 4*(a.errors s:ℝ) := by exact_mod_cast q
    rw [le_div_iff₀ mpos]
    linarith
  | @column i b hi vi proof =>
    right;right
    let i' : Fin m := ⟨i,List.mem_range.mp hi⟩
    refine ⟨i',b,?_,?_⟩
    · exact (varies_project E word i).mp vi
    · intro s hs hmis
      have q := proof s (by simpa using hs) hmis
      have p : (a.mass:ℝ) ≤ 4*(a.errors s:ℝ) := by exact_mod_cast q
      rw [le_div_iff₀ mpos]
      linarith

theorem leaf_mixture {S : Type} (E : Finset S) {m : Nat} (word : S → Nat → Bool)
    (whole : Leaf S) (pm : 0<whole.mass) (L : List (Leaf S))
    (cover : result E.toList (List.range m) word whole L) :
    let w : Fin L.length → ℝ := fun j=>(L[j].mass:ℝ)/(whole.mass:ℝ)
    let ell : Fin L.length → S → ℝ := fun j s=>2*(L[j].errors s:ℝ)/(L[j].mass:ℝ)
    PEqualNP.Outside.L_meta_32580.Profile.Mix E (fun (i : Fin m) s=>word s i.val) Finset.univ w ell
      (fun s=>2*(whole.errors s:ℝ)/(whole.mass:ℝ)) := by
  have wm : (0:ℝ)<whole.mass := by exact_mod_cast pm
  refine ⟨?_,?_,?_,?_⟩
  · intro j _
    positivity
  · change ∑ j : Fin L.length,(L[j].mass:ℝ)/(whole.mass:ℝ)=1
    simp_rw [div_eq_mul_inv]
    rw [←Finset.sum_mul]
    have mass : ∑ j : Fin L.length,(L[j].mass:ℝ)=(whole.mass:ℝ) := by
      calc
        _ = (L.map (fun a : Leaf S => (a.mass:ℝ))).sum :=
          sum_list L (fun a : Leaf S => (a.mass:ℝ))
        _ = (whole.mass:ℝ) := by
          have nc : (L.map Leaf.mass).sum=whole.mass := cover.1.1
          simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
            congrArg (fun z : Nat => (z:ℝ)) nc
    rw [mass,←div_eq_mul_inv,div_self (ne_of_gt wm)]
  · intro j _
    have z := cover.2 L[j] (List.getElem_mem j.isLt)
    exact leaf_real E word L[j] z.1 z.2
  · intro s hs
    change 2*(whole.errors s:ℝ)/(whole.mass:ℝ)=
      ∑ j : Fin L.length,(L[j].mass:ℝ)/(whole.mass:ℝ)*
        (2*(L[j].errors s:ℝ)/(L[j].mass:ℝ))
    have each (j : Fin L.length) :
      (L[j].mass:ℝ)/(whole.mass:ℝ)*(2*(L[j].errors s:ℝ)/(L[j].mass:ℝ))=
        2*(L[j].errors s:ℝ)/(whole.mass:ℝ) := by
      have p : (0:ℝ)<L[j].mass := by
        exact_mod_cast (cover.2 L[j] (List.getElem_mem j.isLt)).1
      field_simp [ne_of_gt p,ne_of_gt wm]
    simp_rw [each,div_eq_mul_inv]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    have errors : ∑ j : Fin L.length,(L[j].errors s:ℝ)=(whole.errors s:ℝ) := by
      calc
        _ = (L.map (fun a : Leaf S => (a.errors s:ℝ))).sum :=
          sum_list L (fun a : Leaf S => (a.errors s:ℝ))
        _ = (whole.errors s:ℝ) := by
          have nc : (L.map (fun h => h.errors s)).sum=whole.errors s :=
            cover.1.2 s (by simpa using hs)
          simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
            congrArg (fun z : Nat => (z:ℝ)) nc
    rw [errors]

theorem compose_uniform_families {S I J : Type} [Fintype J] (K : J → Type)
    [∀ j,Fintype (K j)] (E : Finset S) (word : I → S → Bool)
    (a : J → ℝ) (w : ∀ j,K j → ℝ) (ell : ∀ j,K j → S → ℝ) (avg : J → S → ℝ)
    (apos : ∀ j,0 ≤ a j) (anorm : ∑ j,a j=1)
    (families : ∀ j,PEqualNP.Outside.L_meta_32580.Profile.Mix E word Finset.univ (w j) (ell j) (avg j)) :
    PEqualNP.Outside.L_meta_32580.Profile.Mix E word (Finset.univ : Finset (Sigma K))
      (fun j=>a j.1*w j.1 j.2) (fun j=>ell j.1 j.2)
      (fun s=>∑ j,a j*avg j s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j _
    exact mul_nonneg (apos j.1) ((families j.1).nonnegWeight j.2 (by simp))
  · rw [Fintype.sum_sigma]
    simp_rw [←Finset.mul_sum]
    simpa only [(fun j=>(families j).totalWeight),mul_one] using anorm
  · intro j _
    exact (families j.1).leaf j.2 (by simp)
  · intro s hs
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [(families j).combines s hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring

end PEqualNP.Outside.L_meta_32580.FieldProfiles

/- Source segment: ExactDefinitions. -/

                                                             

namespace PEqualNP.Outside.L_meta_32580.ExactDefinitions
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput
open PEqualNP.Outside.L_meta_32580.CircuitAdapter PEqualNP.Outside.L_meta_32580.ColumnObstruction

theorem bit_injective : Function.Injective toBit := by
  intro a b e
  have z := congrArg ofBit e
  rwa [of_to,of_to] at z

theorem vary_exact {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (A : Fin m → Vec k) (word : Vec k → Nat → Bool)
    (w : ∀ s (i : Fin m),word s i=toBit (dotProduct (A i) s))
    (i : Fin m) :
    varying E.toList word i.val=true ↔ ∃ s∈E,dotProduct (A i) s≠dotProduct (A i) a := by
  rw [vary_from (by simpa using ha)]
  constructor
  · rintro ⟨s,hs,p⟩
    refine ⟨s,by simpa using hs,?_⟩
    rw [w a i,w s i] at p
    exact fun z=>p (congrArg toBit z.symm)
  · rintro ⟨s,hs,p⟩
    refine ⟨s,by simpa using hs,?_⟩
    rw [w a i,w s i]
    exact fun z=>p (bit_injective z.symm)

theorem list_range_ofFn (n : Nat) :
    List.ofFn (fun i : Fin n=>i.val)=List.range n := by
  apply List.ext_getElem (by simp)
  intro j hl hr
  simp

theorem count_fin_col (m : Nat) (p : Nat → Bool) :
    (List.range m).countP p=((Finset.univ : Finset (Fin m)).filter (fun i=>p i.val=true)).card := by
  classical
  let l := List.ofFn (id : Fin m → Fin m)
  have nd : l.Nodup := List.nodup_ofFn_ofInjective fun _ _ h=>h
  have univ : l.toFinset=(Finset.univ : Finset (Fin m)) := by
    ext j
    rw [List.mem_toFinset]
    simp [l]
  have h := nd.card_eq_countP (P:=fun i=>p i.val=true)
  rw [univ] at h
  have eq : (l.map Fin.val) = List.range m := by
    change ((List.ofFn (id : Fin m → Fin m)).map Fin.val)=List.range m
    rw [List.map_ofFn]
    exact list_range_ofFn m
  have pEq : (fun i : Fin m=>decide (p i.val=true))=(fun i : Fin m=>p i.val) :=
    funext (fun i=>by cases p i.val <;> decide)
  change ((Finset.univ : Finset (Fin m)).filter (fun i=>p i.val=true)).card =
    l.countP (fun i=>decide (p i.val=true)) at h
  rw [pEq] at h
  rw [←eq,List.countP_map]
  exact h.symm

theorem varying_count_exact {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (A : Fin m → Vec k) (word : Vec k → Nat → Bool)
    (w : ∀ s (i : Fin m),word s i=toBit (dotProduct (A i) s)) :
    (List.range m).countP (varying E.toList word)=
      ((Finset.univ : Finset (Fin m)).filter fun i=>
        ∃ s∈E,dotProduct (A i) s≠dotProduct (A i) a).card := by
  classical
  rw [count_fin_col]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact vary_exact E a ha A word w i

theorem cost_literal (C : Circuit) :
    publicCost C.gates=C.gates.countP
      (fun g=>@decide ((g.op=.and∨g.op=.or)∧g.inputs.length=2) (Classical.propDecidable _)) := rfl

theorem readback_literal {width : Nat} {C : Circuit}
    (law : ∀ j<C.gates.length,∀ i∈(C.gates.getD j ⟨.or,[]⟩).inputs,i<width+j) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C := law

end PEqualNP.Outside.L_meta_32580.ExactDefinitions

/- Source segment: ExactGame. -/

                                                                        
                                                                           
                                                  

namespace PEqualNP.Outside.L_meta_32580.ExactGame
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.Profile PEqualNP.Outside.L_meta_32580.FieldProfiles

noncomputable section
variable {C S I : Type} [DecidableEq S]

def packet (E : Finset S) (word : I → S → Bool) (ell : S → ℝ) : Prop :=
  ∃ N : Nat, ∃ w : Fin N → ℝ, ∃ leaves : Fin N → S → ℝ,
    Mix E word Finset.univ w leaves ell

structure Options (E : Finset S) (word : I → S → Bool) (price : Nat)
    (fits : Nat → C → Prop) (err : C → S → ℝ) : Prop where
  perfect : ∃ c,fits price c ∧ (∀ s∈E,err c s=0)
  point : ∀ u∈E,∃ c,fits (price-1) c ∧ ∀ s∈E,err c s=if s=u then 1 else 0
  column : ∀ i b,varies E word i → ∃ c,fits (price-1) c ∧
    (∀ s∈E,err c s=if word i s≠b then (1/2:ℝ) else 0)

def feasible (E : Finset S) (fits : Nat → C → Prop) (err : C → S → ℝ)
    (p : Nat) (score : ℝ) : Prop :=
  ∃ N : Nat,∃ c : Fin N → C,∃ w : Fin N → ℝ,
    (∀ j,fits p (c j)∧0 ≤ w j) ∧ (∑ j,w j)=1 ∧
      ∀ s∈E,score ≤ ∑ j,w j*(1-err (c j) s)

theorem perfect_iff {E : Finset S} {word : I → S → Bool} {price p : Nat} (ht : 2 ≤ E.card)
    {fits : Nat → C → Prop} {err : C → S → ℝ} (upper : Options E word price fits err)
    (mon : ∀ {a b c},a ≤ b → fits a c → fits b c)
    (lower : ∀ c,fits (price-1) c → packet E word (err c)) :
    (∃ c,fits p c ∧ ∀ s∈E,err c s=0)↔price ≤ p := by
  constructor
  · rintro ⟨c,hc,zero⟩
    by_contra short
    have pt : p ≤ price-1 := by omega
    obtain ⟨N,w,ell,has⟩ := lower c (mon pt hc)
    have r := has.uniform ht
    have z : (∑ s∈E,err c s)=0 := Finset.sum_eq_zero zero
    rw [z] at r
    linarith
  · intro enough
    obtain ⟨c,hc,h0⟩ := upper.perfect
    exact ⟨c,mon enough hc,h0⟩

theorem weighted [Fintype I] {E : Finset S} {word : I → S → Bool} {price : Nat}
    (ht : 2 ≤ E.card) {fits : Nat → C → Prop} {err : C → S → ℝ} (upper : Options E word price fits err)
    (lower : ∀ c,fits (price-1) c → packet E word (err c))
    (μ : S → ℝ) (μ0 : ∀ s∈E,0 ≤ μ s) :
    ∃ v : ℝ,OptionValue E word μ v ∧
      (∀ u,OptionValue E word μ u → v ≤ u) ∧
      (∀ c,fits (price-1) c → v ≤ loss E μ (err c)) ∧
      ∃ c,fits (price-1) c∧loss E μ (err c)=v := by
  classical
  obtain ⟨v,choice,small⟩ := minimum_exists E word μ (Finset.card_pos.mp (by omega))
  refine ⟨v,choice,small,?_,?_⟩
  · intro c hc
    obtain ⟨N,w,ell,part⟩ := lower c hc
    exact part.lower ht μ0 small
  · rcases choice with ⟨u,hu,rfl⟩|⟨i,b,var,rfl⟩
    · obtain ⟨c,hc,hcL⟩ := upper.point u hu
      refine ⟨c,hc,?_⟩
      unfold loss
      have formula : ∀ s∈E,μ s*err c s=if s=u then μ u else 0 := by
        intro s hs
        rw [hcL s hs]
        split <;> simp_all
      rw [Finset.sum_congr rfl formula]
      simp [hu]
    · obtain ⟨c,hc,he⟩ := upper.column i b var
      refine ⟨c,hc,?_⟩
      unfold loss column
      have eq : ∀ s∈E,μ s*err c s=(if word i s≠b then μ s else 0)*(1/2:ℝ) := by
        intro s hs
        rw [he s hs]
        by_cases h : word i s≠b <;> simp [h]
      rw [Finset.sum_congr rfl eq,←Finset.sum_mul]
      ring

theorem feasible_profile {E : Finset S} {word : I → S → Bool} {price : Nat}
    {fits : Nat → C → Prop} {err : C → S → ℝ}
    (lower : ∀ c,fits (price-1) c → packet E word (err c)) (score : ℝ)
    (f : feasible E fits err (price-1) score) :
    ∃ avg, packet E word avg ∧ ∀ s∈E,avg s ≤ 1-score := by
  classical
  obtain ⟨N,c,w,fees,norm,tests⟩ := f
  have pack : ∀ j,packet E word (err (c j)) := fun j=>lower _ (fees j).1
  choose K w' leaf p using pack
  let J := Sigma (fun j : Fin N=>Fin (K j))
  let avg := fun s=>∑ j,w j*err (c j) s
  have r := compose_uniform_families (fun j : Fin N=>Fin (K j)) E word w w' leaf
    (fun j=>err (c j)) (fun j=>(fees j).2) norm p
  let e : J≃Fin (Fintype.card J) := Fintype.equivFin J
  have mixture : packet E word avg := by
    refine ⟨Fintype.card J,fun i=>w (e.symm i).1*w' (e.symm i).1 (e.symm i).2,
      fun i=>leaf (e.symm i).1 (e.symm i).2,⟨?_,?_,?_,?_⟩⟩
    · intro i hi
      exact r.nonnegWeight (e.symm i) (by simp)
    · exact (Equiv.sum_comp e.symm (fun z : J=>w z.1*w' z.1 z.2)).trans r.totalWeight
    · intro i _
      exact r.leaf (e.symm i) (by simp)
    · intro s hs
      exact (r.combines s hs).trans
        (Equiv.sum_comp e.symm (fun z : J=>w z.1*w' z.1 z.2*leaf z.1 z.2 s)).symm
  refine ⟨avg,mixture,?_⟩
  intro s hs
  have z := tests s hs
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,norm] at z
  change _ ≤ 1-score
  linarith

theorem feasible_bound {E : Finset S} {word : I → S → Bool} {price : Nat} (ht : 2 ≤ E.card)
    {fits : Nat → C → Prop} {err : C → S → ℝ}
    (lower : ∀ c,fits (price-1) c → packet E word (err c)) (score : ℝ)
    (f : feasible E fits err (price-1) score) :
    score ≤ 1-1/(2*(E.card:ℝ)) := by
  obtain ⟨avg,⟨N,w,leaf,m⟩,upper⟩ := feasible_profile lower score f
  have low := m.uniform ht
  have total := Finset.sum_le_sum upper
  simp only [Finset.sum_const,nsmul_eq_mul] at total
  have n0 : (0:ℝ)<E.card := by exact_mod_cast (show 0<E.card by omega)
  have b0 : (1:ℝ)/(2*(E.card:ℝ)) ≤ 1-score := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(E.card:ℝ))).mpr
    linarith
  linarith

theorem feasible_isolates {E : Finset S} {word : I → S → Bool} {price : Nat} (ht : 2 ≤ E.card)
    {fits : Nat → C → Prop} {err : C → S → ℝ}
    (lower : ∀ c,fits (price-1) c → packet E word (err c))
    (f : feasible E fits err (price-1) (1-1/(2*(E.card:ℝ)))) :
    ∀ u∈E,isolates E word u := by
  obtain ⟨avg,⟨N,w,leaf,m⟩,upper⟩ := feasible_profile lower _ f
  exact m.isolation ht (fun s hs=>by have z:=upper s hs; linarith)

theorem isolates_feasible {E : Finset S} {word : I → S → Bool} {price : Nat} (ht : 2 ≤ E.card)
    {fits : Nat → C → Prop} {err : C → S → ℝ} (upper : Options E word price fits err)
    (cond : ∀ u∈E,isolates E word u) :
    feasible E fits err (price-1) (1-1/(2*(E.card:ℝ))) := by
  classical
  have realizer (u : E) : ∃ c,fits (price-1) c ∧
    ∀ s∈E,err c s=if s=(u:S) then (1/2:ℝ) else 0 := by
    obtain ⟨i,b,h⟩ := cond u u.property
    have rest : 0<(E.erase (u:S)).card := by
      rw [Finset.card_erase_of_mem u.property]
      omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp rest
    obtain ⟨ne,hvE⟩ := Finset.mem_erase.mp hv
    have hit : word i (u:S)≠b := (h u u.property).mpr rfl
    have matchedBit : word i v=b := by
      by_contra no
      exact ne ((h v hvE).mp no)
    have vary : varies E word i := ⟨u,u.property,v,hvE,fun e=>hit (e.trans matchedBit)⟩
    obtain ⟨c,hc,he⟩ := upper.column i b vary
    exact ⟨c,hc,fun s hs=>by rw [he s hs]; simp [h s hs]⟩
  choose c legal law using realizer
  let idx : Fin E.card≃E := (Finset.equivFinOfCardEq rfl).symm
  let w : ℝ := 1/(E.card:ℝ)
  have e0 : (E.card:ℝ)≠0 := by exact_mod_cast (show E.card≠0 by omega)
  have wn : ∑ _j : Fin E.card,w=1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,w]
    field_simp [e0]
  refine ⟨E.card,fun j=>c (idx j),fun _=>w,fun j=>⟨legal _,by positivity⟩,wn,?_⟩
  intro s hs
  have error : (∑ j : Fin E.card,w*err (c (idx j)) s)=1/(2*(E.card:ℝ)) := by
    let us : E := ⟨s,hs⟩
    have chooseNorm (u : E) : err (c u) s=if u=us then (1/2:ℝ) else 0 := by
      rw [law u s hs]
      simp [us,Subtype.ext_iff,eq_comm]
    have norm : (∑ u : E,w*err (c u) s)=1/(2*(E.card:ℝ)) := by
      simp_rw [chooseNorm]
      rw [Finset.sum_eq_single us]
      · simp [w] <;> field_simp [e0]
      · intro u hu hu'
        simp [hu']
      · simp
    exact (Equiv.sum_comp idx (fun u : E=>w*err (c u) s)).trans norm
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,wn,error,le_refl]

end
end PEqualNP.Outside.L_meta_32580.ExactGame

/- Source segment: ProjectLower. -/

                                                                        
                                                                            

namespace PEqualNP.Outside.L_meta_32580.ProjectLower
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.ExactHull
open PEqualNP.Outside.L_meta_32580.ExactScore PEqualNP.Outside.L_meta_32580.ExactDefinitions PEqualNP.Outside.L_meta_32580.FieldProfiles
open PEqualNP.Outside.L_meta_32580.ExactGame PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.CircuitAdapter

def wordBit {k m : Nat} (A : Fin m → Vec k) (i : Fin m) (s : Vec k) : Bool :=
  toBit (dotProduct (A i) s)

noncomputable def price {k m : Nat} (r : Nat) (A : Fin m → Vec k) (E : Finset (Vec k))
    (a : Vec k) : Nat :=
  2*m+r+
    Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+
    ((Finset.univ : Finset (Fin m)).filter fun i=>
      ∃ s∈E,dotProduct (A i) s≠dotProduct (A i) a).card

theorem project_packet {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (hcard : E.card=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+1)
    (C : Circuit) (legal : ∀ g∈C.gates,Legal g) (short : publicCost C.gates<price r A E a) :
    packet E (wordBit A) (fun s=>1-fieldScore e A h C s) := by
  classical
  let d := Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))
  obtain ⟨D,packDef,yDef,hDef,wDef⟩ := exact_model e A h
  obtain ⟨H⟩ := exact_hull e E a ha (d:=d) rfl hcard D packDef yDef
  have small : publicCost C.gates<2*m+r+d+(List.range m).countP (ColumnObstruction.varying E.toList D.word) := by
    simpa only [price,d,varying_count_exact E a ha A D.word wDef] using short
  obtain ⟨L,how⟩ := lower D E.toList H C legal small
  have pos : 0<(actualLeaf D C).mass := by rw [mass_eq]; positivity
  have fe := leaf_mixture E D.word (actualLeaf D C) pos L how
  refine ⟨L.length,fun j=>(L[j].mass:ℝ)/((actualLeaf D C).mass:ℝ),
    fun j s=>2*(L[j].errors s:ℝ)/(L[j].mass:ℝ),?_⟩
  have wf : (fun (i : Fin m) s=>D.word s i.val)=wordBit A := by
    funext i s
    exact wDef s i
  have lf : (fun s=>2*((actualLeaf D C).errors s:ℝ)/(actualLeaf D C).mass) =
      fun s=>1-fieldScore e A h C s := by
    funext s
    exact (field_loss_formula e A h D packDef yDef hDef wDef C s).symm
  rw [wf,lf] at fe
  exact fe

end PEqualNP.Outside.L_meta_32580.ProjectLower

/- Source segment: UpperPattern. -/


namespace PEqualNP.Outside.L_meta_32580.UpperPattern
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.CircuitAdapter
open PEqualNP.Outside.L_meta_32580.CircuitEmit PEqualNP.Outside.L_meta_32580.CircuitCompile

inductive Coefficient (Y : Type) where
  | fixed (bit : Bool)
  | varying (f : Fun Y)

def Coefficient.value {Y : Type} : Coefficient Y → Fun Y
  | .fixed b => fun _=>b
  | .varying f => f

def Coefficient.extra {Y : Type} : Coefficient Y → Nat
  | .fixed _ => 0
  | .varying _ => 1

structure Cell (Y : Type) where
                                                      
  x : Fun Y
                                                                       
  b : Fun Y
                                                                     
  c : Fun Y
                                                                 
  a : Coefficient Y

def Cell.value {Y : Type} (t : Cell Y) (y : Y) : Bool :=
  t.b y && (t.x y ^^ (t.a.value y && t.c y))

def Cell.cost {Y : Type} (t : Cell Y) : Nat := 1+t.a.extra

def affineCell {Y : Type} (P : List (Fun Y)) (t : Cell Y) : Prop :=
  Span P t.x ∧ Span P t.b ∧ Span P t.c ∧ Span P t.a.value

def cellsCost {Y : Type} (cells : List (Cell Y)) : Nat := (cells.map Cell.cost).sum

def cellsEval {Y : Type} (z : Fun Y) : List (Cell Y) → Fun Y
  | [] => z
  | a::t => fun y=>a.value y ^^ cellsEval z t y

theorem affine_weaken {Y : Type} {P Q : List (Fun Y)} {c : Cell Y} (h : affineCell P c)
    (sub : ∀ f∈P,f∈Q) : affineCell Q c :=
  ⟨h.1.weaken sub,h.2.1.weaken sub,h.2.2.1.weaken sub,h.2.2.2.weaken sub⟩

                                                                   
                                                                    
theorem fuse {Y : Type} {B P : List (Fun Y)} {q : Nat} (t : Cell Y)
    (h : affineCell P t) (prior : ParamProgram B P q) :
    ∃ Q, ParamProgram B Q (q+t.cost) ∧ (∀ f∈P,f∈Q) ∧ Span Q t.value := by
  obtain ⟨x,b,c,a⟩ := t
  rcases h with ⟨hx,hb,hc,ha⟩
  cases a with
  | fixed u =>
    have produced : ParamProgram B (P++[(⟨x,b,c,.fixed u⟩ : Cell Y).value]) (q+1) :=
      .mul prior hb (.plus hx (hc.scale u))
    exact ⟨_,produced,fun f hf=>List.mem_append_left _ hf,
      .generator (List.mem_append_right _ List.mem_cons_self)⟩
  | varying w =>
    let f : Fun Y := fun y=>w y&&c y
    let Q := P++[f]
    have before : ParamProgram B Q (q+1) := .mul prior ha hc
    have sub : ∀ z∈P,z∈Q := fun z hz=>List.mem_append_left _ hz
    have x' : Span Q x := hx.weaken sub
    have b' : Span Q b := hb.weaken sub
    have f' : Span Q f := .generator (List.mem_append_right _ List.mem_cons_self)
    have after : ParamProgram B (Q++[(⟨x,b,c,.varying w⟩ : Cell Y).value]) (q+1+1) :=
      .mul before b' (.plus x' f')
    exact ⟨_,after,fun z hz=>List.mem_append_left _ (sub z hz),
      .generator (List.mem_append_right _ List.mem_cons_self)⟩

theorem build {Y : Type} {B P : List (Fun Y)} {q : Nat} (cells : List (Cell Y))
    (legal : ∀ c∈cells,affineCell P c) (prior : ParamProgram B P q)
    (z : Fun Y) (z_affine : Span P z) :
    ∃ Q, ParamProgram B Q (q+cellsCost cells) ∧ (∀ f∈P,f∈Q) ∧
      Span Q (cellsEval z cells) := by
  induction cells generalizing P q with
  | nil => exact ⟨P,prior,fun _ h=>h,z_affine⟩
  | cons h t ih =>
    obtain ⟨Q,pa,sub,hQ⟩ := fuse h (legal h List.mem_cons_self) prior
    obtain ⟨R,rb,rs,tR⟩ := ih (fun c hc=>affine_weaken (legal c (List.mem_cons_of_mem _ hc)) sub)
       pa (z_affine.weaken sub)
    have adj : q+h.cost+cellsCost t=q+cellsCost (h::t) := by
      simp [cellsCost,Nat.add_assoc]
    rw [adj] at rb
    exact ⟨R,rb,fun f hf=>rs f (sub f hf),.plus (hQ.weaken rs) tR⟩

                                                                     
                                                                
                                                          
theorem construct {Y : Type} (B : List (Fun Y)) (z : Fun Y) (cells : List (Cell Y))
    (z_affine : Span B z) (legal : ∀ c∈cells,affineCell B c) :
    ∃ C : Circuit,
      (∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨.or,[]⟩).inputs, i<B.length+j) ∧
      (∀ j∈C.gates,Legal j) ∧ publicCost C.gates=cellsCost cells ∧
      ∀ y,C.eval (samples B y)=cellsEval z cells y := by
  obtain ⟨Q,p,_,s⟩ := build cells legal ParamProgram.initial z z_affine
  obtain ⟨C,bk,l,c,e⟩ := emitCircuit p s
  exact ⟨C,bank_reads bk,l,by simpa using c,e⟩

end PEqualNP.Outside.L_meta_32580.UpperPattern

/- Source segment: CellAggregation. -/


namespace PEqualNP.Outside.L_meta_32580.CellAggregation
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.UpperPattern

def cells {Y : Type} (left : Nat → Nat) (I rest : List Nat) (b x c : Nat → Fun Y)
    (w : Nat → Coefficient Y) : List (Cell Y) :=
  I.map (fun i=>⟨x (left i),b (left i),c i,w i⟩) ++
    rest.map (fun j=>⟨x j,b j,fun _=>false,.fixed false⟩)

def hasFee {Y : Type} (w : Nat → Coefficient Y) (i : Nat) : Bool :=
  match w i with
  | .fixed _ => false
  | .varying _ => true

theorem cells_exactCost {Y : Type} (left : Nat → Nat) (I rest : List Nat) (b x c : Nat → Fun Y)
    (w : Nat → Coefficient Y) :
    cellsCost (cells left I rest b x c w)=I.length+rest.length+I.countP (hasFee w) := by
  unfold cellsCost cells
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def]
  have ordinary : (rest.map (fun j=>Cell.cost (⟨x j,b j,fun _=>false,.fixed false⟩ : Cell Y))).sum=rest.length := by
    induction rest with
    | nil => rfl
    | cons j t ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      change 1+t.length=t.length+1
      omega
  have paid : (I.map (fun i=>Cell.cost (⟨x (left i),b (left i),c i,w i⟩ : Cell Y))).sum=
      I.length+I.countP (hasFee w) := by
    induction I with
    | nil => rfl
    | cons a t ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      cases hw : w a <;> simp [Cell.cost,Coefficient.extra,hasFee,hw,List.countP_cons] <;> omega
  rw [ordinary,paid]
  omega

theorem cells_append {Y : Type} (T U : List (Cell Y)) (acc : Fun Y) (v : Y) :
    cellsEval acc (T++U) v=cellsEval (cellsEval acc U) T v := by
  induction T with
  | nil => rfl
  | cons a t ih => simp [cellsEval,ih]

theorem ordinary_eval {Y : Type} (L : List Nat) (b x : Nat → Fun Y) (acc : Fun Y) (v : Y) :
    cellsEval acc (L.map (fun j=>⟨x j,b j,fun _=>false,.fixed false⟩)) v=
      (parity (fun j=>b j v && x j v) L ^^ acc v) := by
  induction L with
  | nil => simp [cellsEval,parity]
  | cons j t ih =>
    simp [cellsEval,parity,Cell.value,Coefficient.value,ih,Bool.xor_assoc]

theorem fused_eval {Y : Type} (left : Nat → Nat) (L : List Nat) (b x c : Nat → Fun Y) (w : Nat → Coefficient Y)
    (acc : Fun Y) (v : Y) :
    cellsEval acc (L.map (fun i=>⟨x (left i),b (left i),c i,w i⟩)) v=
      ((parity (fun i=>b (left i) v && x (left i) v) L ^^
         parity (fun i=>(w i).value v && (b (left i) v && c i v)) L) ^^ acc v) := by
  induction L with
  | nil => simp [cellsEval,parity]
  | cons i t ih =>
    simp only [List.map_cons,cellsEval,Cell.value,ih,parity]
    simp only [Bool.and_xor_distrib_left,Bool.and_assoc,Bool.and_left_comm,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

theorem parity_map_rule {A : Type} (f : Nat → Bool) (h : A → Nat) :
    ∀ l : List A, parity f (l.map h) =
      (l.foldr (fun a out=>f (h a) ^^ out) false) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp [parity,ih]

theorem parity_mapped (l : List Nat) (h : Nat → Nat) (q : Nat → Bool) :
    parity (fun i=>q (h i)) l=parity q (l.map h) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons,parity,ih]

end PEqualNP.Outside.L_meta_32580.CellAggregation

/- Source segment: UpperProjectionProof. -/


namespace PEqualNP.Outside.L_meta_32580.UpperProjectionProof
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.AffineProjection
open PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify PEqualNP.Outside.L_meta_32580.CircuitAdapter
open PEqualNP.Outside.L_meta_32580.UpperPattern PEqualNP.Outside.L_meta_32580.CellAggregation
theorem finish_bits (l r c xa hv : Bool) :
    ((l ^^ c) ^^ (r ^^ (xa ^^ hv)))=((xa ^^ (l ^^ r)) ^^ (hv ^^ c)) := by
  cases l <;> cases r <;> cases c <;> cases xa <;> cases hv <;> rfl

set_option maxHeartbeats 45000 in
                                                                         
                                                                       
                                                                    
theorem upper {Y : Type} (B : List (Fun Y)) (c I rest : List Nat) (left : Nat → Nat) (g duals : Nat → Assign)
    (a : Assign) (x y : Y → Assign) (partner : Nat → Fun Y) (w : Nat → Coefficient Y)
    (h : Fun Y)
    (hAffine : Span B h)
    (xAffine : ∀ j,Span B (fun v=>dot c (g j) (x v)))
    (yAffine : ∀ j,Span B (fun v=>coordinates c ((I.map left)++rest) duals a (y v) j))
    (anchorAffine : Span B (fun v=>dot c (x v) a))
    (cAffine : ∀ i,Span B (partner i)) (wAffine : ∀ i,Span B (w i).value) :
    ∃ C : Circuit, (∀ j<C.gates.length,∀ p∈(C.gates.getD j ⟨.or,[]⟩).inputs,p<B.length+j) ∧
      (∀ j∈C.gates,Legal j) ∧ publicCost C.gates=I.length+rest.length+I.countP (hasFee w) ∧
      ∀ v,C.eval (samples B v)=
        (dot c (x v) (projectTo c ((I.map left)++rest) g duals a (y v)) ^^
          (h v ^^ parity (fun i=>(w i).value v &&
            (coordinates c ((I.map left)++rest) duals a (y v) (left i) && partner i v)) I)) := by
  let hd := (I.map left)++rest
  let xs : Nat → Fun Y := fun j v=>dot c (g j) (x v)
  let ys : Nat → Fun Y := fun j v=>coordinates c hd duals a (y v) j
  let adjust : Fun Y := fun v=>dot c (x v) a ^^ h v
  let cs := cells left I rest ys xs partner w
  have adj : Span B adjust := .plus anchorAffine hAffine
  have ca : ∀ p∈cs,affineCell B p := by
    intro p hp
    rcases List.mem_append.mp hp with hi|hr
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
      exact ⟨xAffine _,yAffine _,cAffine _,wAffine _⟩
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
      exact ⟨xAffine _,yAffine _,.const false,.const false⟩
  obtain ⟨C,back,legal,price,sem⟩ := construct B adjust cs adj ca
  refine ⟨C,back,legal,price.trans (cells_exactCost left I rest ys xs partner w),?_⟩
  intro v
  rw [sem]
  let lc := I.map (fun i=>(⟨xs (left i),ys (left i),partner i,w i⟩ : Cell Y))
  let rc := rest.map (fun j=>(⟨xs j,ys j,fun _=>false,.fixed false⟩ : Cell Y))
  let l := parity (fun i=>ys (left i) v && xs (left i) v) I
  let r := parity (fun j=>ys j v && xs j v) rest
  let t := parity (fun i=>(w i).value v && (ys (left i) v && partner i v)) I
  let xa := dot c (x v) a
  change cellsEval adjust (lc++rc) v =
    (dot c (x v) (projectTo c hd g duals a (y v)) ^^ (h v ^^ t))
  have leftEq : cellsEval (cellsEval adjust rc) lc v=
      ((l^^t) ^^ cellsEval adjust rc v) :=
    fused_eval left I ys xs partner w (cellsEval adjust rc) v
  have rightEq : cellsEval adjust rc v=(r^^(xa^^h v)) :=
    ordinary_eval rest ys xs adjust v
  have pSum : parity (fun j=>ys j v && xs j v) hd=(l^^r) := by
    unfold hd
    rw [parity_append,←parity_mapped I left (fun j=>ys j v && xs j v)]
  have fq : dot c (x v) (projectTo c hd g duals a (y v))=(xa^^(l^^r)) := by
    have cEq := projected_pairing c hd g duals a (x v) (y v)
    change dot c (x v) (projectTo c hd g duals a (y v))=
      (xa^^parity (fun j=>ys j v && xs j v) hd) at cEq
    rw [pSum] at cEq
    exact cEq
  rw [cells_append,leftEq,rightEq,fq]
  exact finish_bits l r t xa (h v)

end PEqualNP.Outside.L_meta_32580.UpperProjectionProof

/- Source segment: SelectiveRebase. -/


namespace PEqualNP.Outside.L_meta_32580.SelectiveRebase
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffineProjection

                                                                     
                                                                  
                                                        
def selectRebase (g : Nat → Assign) (marked : Nat → Bool) (newAnchor i : Nat) : Assign :=
  if marked i then shift (g newAnchor) (g i) else g i

theorem select_independent {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    (marked : Nat → Bool) {j : Nat} (hj : j∈d) :
    ∀ a∈cube (d.erase j),∀ b∈cube (d.erase j),
      combine (d.erase j) (selectRebase g marked j) a=
        combine (d.erase j) (selectRebase g marked j) b → a=b := by
  obtain ⟨q,_,dual⟩ := choose_duals nc nd g inside inj
  have elem {i k : Nat} (hi : i∈d) (hk : k∈d) :
      dot c (g i) (q k)=unit i k := by
    have qq := dual k hk (unit i) (mem_cube.mpr (unit_supported hi))
    rwa [combine_unit nd hi] at qq
  intro a ha b hb same
  funext k
  by_cases hk : k∈d.erase j
  · have kj : k≠j := fun e=>erase_avoids nd hj (e ▸ hk)
    have picked : unit j k=false := by simp [unit,kj]
    have readNew (x : Assign) :
        dot c (combine (d.erase j) (selectRebase g marked j) x) (q k)=x k := by
      rw [combine_dot]
      have eq : parity (fun i=>x i && dot c (selectRebase g marked j i) (q k)) (d.erase j)=
          parity (fun i=>x i && unit k i) (d.erase j) := by
        apply parity_congr
        intro i hi
        have e : unit i k=unit k i := by simp [unit,eq_comm]
        cases flag : marked i <;> simp [selectRebase,flag,LinearExtension.dot_shift_left,
          elem hj (List.mem_of_mem_erase hk),elem (List.mem_of_mem_erase hi) (List.mem_of_mem_erase hk),
          picked,e]
      rw [eq]
      exact dot_unit (nd.erase j) hk x
    rw [←readNew a,←readNew b,same]
  · rw [mem_cube.mp ha k hk,mem_cube.mp hb k hk]

theorem retained_hyperplane {c d : List Nat} (nc : c.Nodup) (nd : d.Nodup) (g : Nat → Assign)
    (inside : ∀ j∈d,supported c (g j))
    (inj : ∀ a∈cube d,∀ b∈cube d,combine d g a=combine d g b → a=b)
    (marked : Nat → Bool) (a : Assign) {j : Nat} (hj : j∈d) (mark_j : marked j=true) :
    ∃ q,supported c q ∧
      (∀ x∈cube d,
        (∀ i∈d,marked i=true → x i=false)  → 
        dot c (shift a (shift a (combine d g x))) q=false) ∧
      (∀ y,memberHull (d.erase j) (selectRebase g marked j) (shift a (g j)) y  → 
        dot c (shift a y) q=true) := by
  obtain ⟨q,supp,_,match_⟩ := interpolate nc nd g inside inj a false marked
  have e : ∀ i∈d,dot c (g i) q=marked i := by
    intro i hi
    simpa only [shift_invol,Bool.false_xor] using match_ i hi
  refine ⟨q,supp,?_,?_⟩
  · intro x hx all
    rw [shift_invol,combine_dot,←parity_zero d]
    apply parity_congr
    intro i hi
    rw [e i hi]
    cases flag : marked i
    · simp
    · simp [all i hi flag]
  · rintro y ⟨w,hw,rfl⟩
    rw [shift_assoc a (g j),shift_invol]
    rw [LinearExtension.dot_shift_left,e j hj,mark_j]
    have vanish : dot c (combine (d.erase j) (selectRebase g marked j) w) q=false := by
      rw [combine_dot,←parity_zero (d.erase j)]
      apply parity_congr
      intro i hi
      have keep := e i (List.mem_of_mem_erase hi)
      cases f : marked i <;>
        simp [selectRebase,f,LinearExtension.dot_shift_left,e j hj,mark_j,keep]
    rw [vanish]
    rfl

end PEqualNP.Outside.L_meta_32580.SelectiveRebase

/- Source segment: FibreBasis. -/


namespace PEqualNP.Outside.L_meta_32580.FibreBasis
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.SelectiveRebase

def label (g : Nat → Assign) : Option Nat → Assign
  | none=>zero
  | some j=>g j

def coeff (β : Assign) : Option Nat → Assign
  | none=>β
  | some j=>shift β (unit j)

theorem combine_join (B D : List Nat) (g : Nat → Assign) (x : Assign) :
    combine (B++D) g x=shift (combine B g x) (combine D g x) := by
  funext j
  exact ParamReify.parity_append _ _ _

theorem combine_supported_left {B D : List Nat} (g : Nat → Assign) (x : Assign)
    (no : ∀ j∈D,x j=false) : combine (B++D) g x=combine B g x := by
  rw [combine_join]
  have z : combine D g x=zero := by
    funext j
    change parity (fun i=>x i && g i j) D=false
    rw [←parity_zero D]
    apply parity_congr
    intro i hi
    rw [no i hi,Bool.false_and]
  rw [z,shift_comm,shift_zero]

theorem combine_restrict {B : List Nat} (g h : Nat → Assign)
    (same : ∀ j∈B,g j=h j) (β : Assign) : combine B g β=combine B h β := by
  funext k
  apply parity_congr
  intro i hi
  rw [same i hi]

theorem coeff_induces {B S : List Nat} (Bnd : (B++S).Nodup)
    (apart : ∀ j∈S,j∉B) (g : Nat → Assign)
    (β : Assign) (β_in : β∈cube B) (s : Option Nat) (scope : ∀ j,s=some j → j∈S) :
    coeff β s∈cube (B++S) ∧
      (∀ i∈B,coeff β s i=β i) ∧
      combine (B++S) g (coeff β s)=shift (combine B g β) (label g s) := by
  have bx : supported (B++S) β := by
    intro j hj
    exact mem_cube.mp β_in j (fun mj=>hj (List.mem_append_left _ mj))
  have x0 : combine (B++S) g β=combine B g β :=
    combine_supported_left g β (fun j hj=>mem_cube.mp β_in j (apart j hj))
  cases s with
  | none =>
    refine ⟨mem_cube.mpr bx,fun _ _=>rfl,?_⟩
    change combine (B++S) g β=shift (combine B g β) zero
    rw [x0,shift_comm,shift_zero]
  | some j =>
    have js := scope j rfl
    have jt : j∈B++S := List.mem_append_right _ js
    refine ⟨mem_cube.mpr (IsotropyCount.add_supported bx (unit_supported jt)),?_,?_⟩
    · intro i hi
      have neq : i≠j := fun e=>apart j js (e ▸ hi)
      simp [coeff,shift,unit,neq]
    · change combine (B++S) g (shift β (unit j))=shift (combine B g β) (g j)
      rw [combine_add,x0,combine_unit Bnd jt]

theorem delete_preserve {D : List Nat} (nd : D.Nodup) (g : Nat → Assign) {j : Nat}
    (hj : j∈D) (β : Assign) (support : β∈cube (D.erase j)) :
    β∈cube D ∧ combine D g β=combine (D.erase j) g β := by
  refine ⟨mem_cube.mpr (fun i none=>mem_cube.mp support i (fun h=>none (List.mem_of_mem_erase h))),?_⟩
  funext k
  unfold combine
  rw [parity_perm (List.perm_cons_erase hj),parity,mem_cube.mp support j (erase_avoids nd hj),
    Bool.false_and,Bool.false_xor]

                                                                   
                                                   
theorem delete_fibre_off {B S : List Nat} (nd : (B++S).Nodup)
    (apart : ∀ j∈S,j∉B) (g : Nat → Assign)
    (ind : ∀ a∈cube (B++S),∀ b∈cube (B++S),
      combine (B++S) g a=combine (B++S) g b → a=b)
    (a : Assign) {j : Nat} (hj : j∈S) (β : Assign) (β_ok : β∈cube B) :
    ¬memberHull ((B++S).erase j) g a
      (shift a (shift (combine B g β) (g j))) := by
  intro y
  obtain ⟨z,hz,eq⟩ := y
  have jt : j∈B++S := List.mem_append_right _ hj
  obtain ⟨z0,zt⟩ := delete_preserve nd g jt z hz
  obtain ⟨β1,_,bLaw⟩ := coeff_induces nd apart g β β_ok (some j)
    (fun i e=>by cases e; exact hj)
  change combine (B++S) g (coeff β (some j))=shift (combine B g β) (g j) at bLaw
  have same := congrArg (shift a) eq
  rw [shift_invol,shift_invol,←bLaw,←zt] at same
  have bad := congrFun (ind _ β1 _ z0 same) j
  have zb : z j=false := mem_cube.mp hz j (erase_avoids nd jt)
  have βb : β j=false := mem_cube.mp β_ok j (apart _ hj)
  simp [coeff,shift,unit,βb,zb] at bad

                                                                      
                                                                       
theorem drop_anchor_fibre_off {c B S : List Nat} (nc : c.Nodup) (nd : (B++S).Nodup)
    (apart : ∀ j∈S,j∉B) (g : Nat → Assign)
    (inside : ∀ j∈B++S,supported c (g j))
    (ind : ∀ a∈cube (B++S),∀ b∈cube (B++S),
      combine (B++S) g a=combine (B++S) g b → a=b)
    (a : Assign) {j : Nat} (hj : j∈S) (β : Assign) (β_ok : β∈cube B) :
    ¬memberHull ((B++S).erase j) (selectRebase g (fun i=>decide (i∈S)) j)
      (shift a (g j)) (shift a (combine B g β)) := by
  obtain ⟨q,_,zeroB,one⟩ := retained_hyperplane nc nd g inside ind
    (fun i=>decide (i∈S)) a (List.mem_append_right _ hj) (by simpa using hj)
  intro bad
  have h1 := one _ bad
  have bb : β∈cube (B++S) := mem_cube.mpr
    (fun i hi=>mem_cube.mp β_ok i (fun yes=>hi (List.mem_append_left _ yes)))
  have zeros : ∀ i∈B++S,decide (i∈S)=true → β i=false :=
    fun i _ hit=>mem_cube.mp β_ok i (apart i (decide_eq_true_eq.mp hit))
  have h0 := zeroB β bb zeros
  rw [combine_supported_left g β (fun i hi=>mem_cube.mp β_ok i (apart i hi))] at h0
  rw [h0] at h1
  contradiction

end PEqualNP.Outside.L_meta_32580.FibreBasis

/- Source segment: AffineRawCost. -/


namespace PEqualNP.Outside.L_meta_32580.AffineRawCost
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify
open PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.UpperPattern PEqualNP.Outside.L_meta_32580.CellAggregation

def rawBank {Y : Type} (ambient : List Nat) (x y : Y → Assign) : List (Fun Y) :=
  ambient.map (fun j v=>x v j)++ambient.map (fun j v=>y v j)

theorem dot_from_bank {Y : Type} (B : List (Fun Y)) (c : List Nat) (f : Y → Assign)
    (get : ∀ j∈c,Span B (fun v=>f v j)) (a : Assign) :
    Span B (fun v=>dot c a (f v)) := by
  induction c with
  | nil => exact .const false
  | cons j t ih =>
    have head := (get j List.mem_cons_self).scale (a j)
    apply Span.plus head
    exact ih (fun j hj=>get j (List.mem_cons_of_mem _ hj))

theorem coord_from_bank {Y : Type} (B : List (Fun Y)) (c d : List Nat) (f : Y → Assign)
    (get : ∀ j∈c,Span B (fun v=>f v j)) (q : Nat → Assign) (a : Assign) (i : Nat) :
    Span B (fun v=>coordinates c d q a (f v) i) := by
  by_cases hi : i∈d
  · have eq : (fun v=>coordinates c d q a (f v) i)=
        (fun v=>dot c a (q i) ^^ dot c (q i) (f v)) := by
      funext v
      rw [coordinates,if_pos hi,LinearExtension.dot_shift_left,dot_comm c (f v) (q i)]
    rw [eq]
    exact .plus (.const _) (dot_from_bank B c f get (q i))
  · have eq : (fun v=>coordinates c d q a (f v) i)=(fun _=>false) := by
      funext v; simp [coordinates,hi]
    rw [eq]
    exact .const false

theorem x_raw {Y : Type} (c : List Nat) (x y : Y → Assign) (j : Nat) (hj : j∈c) :
    Span (rawBank c x y) (fun v=>x v j) :=
  .generator (List.mem_append_left _ (List.mem_map_of_mem hj))

theorem y_raw {Y : Type} (c : List Nat) (x y : Y → Assign) (j : Nat) (hj : j∈c) :
    Span (rawBank c x y) (fun v=>y v j) :=
  .generator (List.mem_append_right _ (List.mem_map_of_mem hj))

theorem combine_perm {u v : List Nat} (p : u.Perm v) (g : Nat → Assign) (x : Assign) :
    combine u g x=combine v g x := by
  funext j
  exact parity_perm p _

theorem cube_perm {u v : List Nat} (p : u.Perm v) (nd : u.Nodup) :
    (cube u).Perm (cube v) := by
  apply (List.perm_ext_iff_of_nodup (cube_nodup nd) (cube_nodup (p.nodup nd))).mpr
  intro x
  simp only [mem_cube,supported,p.mem_iff]

theorem hull_perm {u v : List Nat} (p : u.Perm v) (nd : u.Nodup) (g : Nat → Assign) (a y : Assign) :
    memberHull u g a y ↔ memberHull v g a y := by
  have q := cube_perm p nd
  constructor <;> rintro ⟨x,hx,t⟩
  · exact ⟨x,q.mem_iff.mp hx,t.trans (congrArg (shift a) (combine_perm p g x))⟩
  · exact ⟨x,q.mem_iff.mpr hx,t.trans (congrArg (shift a) (combine_perm p.symm g x))⟩

theorem paired_first {B : List Nat} (nd : B.Nodup) (I : List Nat) (ndI : I.Nodup)
    (all : ∀ i∈I,left i∈B) :
    ∃ tail : List Nat,(I.map left++tail).Perm B := by
  let isLeft := fun j=>decide (j∈I.map left)
  let tail := B.filter (fun j=> !(isLeft j))
  have ndleft : (I.map left).Nodup := nodup_map_from _ ndI left (by
    intro i hi j hj eq
    unfold left at eq
    omega)
  have apart : ∀ j∈I.map left,∀ k∈tail,j≠k := by
    intro j hj k hk eq
    subst k
    have f : (!(isLeft j))=true := (List.mem_filter.mp hk).2
    have on : isLeft j=true := decide_eq_true_eq.mpr hj
    rw [on] at f
    contradiction
  have ndAll : (I.map left++tail).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_append]
    exact ⟨ndleft,nd.filter _,apart⟩
  refine ⟨tail,(List.perm_ext_iff_of_nodup ndAll nd).mpr ?_⟩
  intro j
  constructor
  · intro h
    rcases List.mem_append.mp h with a|b
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp a
      exact all i hi
    · exact (List.mem_filter.mp b).1
  · intro hb
    by_cases q : j∈I.map left
    · exact List.mem_append_left _ q
    · have off : isLeft j=false := decide_eq_false q
      exact List.mem_append_right _ (List.mem_filter.mpr ⟨hb,by
        change (!(isLeft j))=true
        rw [off] <;> rfl⟩)

                                                                  
                                                                          
theorem emit {Y : Type} (c d I rest : List Nat) (same : (I.map left++rest).Perm d)
    (g duals : Nat → Assign) (a : Assign) (x y : Y → Assign)
    (partner : Nat → Fun Y) (w : Nat → Coefficient Y) (h : Fun Y)
    (hAffine : Span (rawBank c x y) h)
    (cAffine : ∀ i,Span (rawBank c x y) (partner i))
    (wAffine : ∀ i,Span (rawBank c x y) (w i).value) :
    ∃ C : Circuit,
      (∀ j<C.gates.length,∀ p∈(C.gates.getD j ⟨.or,[]⟩).inputs,p<(rawBank c x y).length+j) ∧
      (∀ j∈C.gates,PEqualNP.Outside.L_meta_32580.CircuitAdapter.Legal j) ∧
      PEqualNP.Outside.L_meta_32580.CircuitAdapter.publicCost C.gates=d.length+I.countP (hasFee w) ∧
      ∀ v,C.eval (samples (rawBank c x y) v)=
        (dot c (x v) (projectTo c (I.map left++rest) g duals a (y v)) ^^
          (h v ^^ parity (fun i=>(w i).value v &&
            (coordinates c (I.map left++rest) duals a (y v) (left i) && partner i v)) I)) := by
  have xx := fun j=>dot_from_bank (rawBank c x y) c x (x_raw c x y) (g j)
  have yy := fun j=>coord_from_bank (rawBank c x y) c (I.map left++rest) y
    (y_raw c x y) duals a j
  have anc : Span (rawBank c x y) (fun v=>dot c (x v) a) := by
    have eq : (fun v=>dot c (x v) a)=(fun v=>dot c a (x v)) := funext (fun v=>dot_comm _ _ _)
    rw [eq]
    exact dot_from_bank (rawBank c x y) c x (x_raw c x y) a
  obtain ⟨C,reads,valid,cost,sem⟩ := UpperProjectionProof.upper (rawBank c x y)
     c I rest left g duals a x y partner w h hAffine xx yy anc cAffine wAffine
  have len := same.length_eq
  simp only [List.length_append,List.length_map] at len
  rw [len] at cost
  exact ⟨C,reads,valid,cost,sem⟩

end PEqualNP.Outside.L_meta_32580.AffineRawCost

/- Source segment: FieldUpperAffine. -/

                                                       

namespace PEqualNP.Outside.L_meta_32580.FieldUpperAffine
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.AffineProjection
open PEqualNP.Outside.L_meta_32580.UpperPattern PEqualNP.Outside.L_meta_32580.AffineRawCost PEqualNP.Outside.L_meta_32580.CellAggregation
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.MathlibReduction
open PEqualNP.Outside.L_meta_32580.ExactDefinitions PEqualNP.Outside.L_meta_32580.ProjectLower

def rawInput (n : Nat) : List (Fun (Vec n × Vec n)) :=
  rawBank (List.range n) (fun v=>ZMod2Bridge.pack v.1) (fun v=>ZMod2Bridge.pack v.2)

theorem pullback {Y X : Type} {B : List (Fun Y)} {f : Fun Y} (h : Span B f) (g : X → Y) :
    Span (B.map (fun f=>f∘g)) (f∘g) := by
  induction h with
  | const b => exact .const b
  | generator pre => exact .generator (List.mem_map_of_mem pre)
  | plus l r il ir => exact .plus il ir

theorem pull_y {n : Nat} {f : Fun (Vec n)}
    (h : Span ((List.range n).map (fun j y=>ZMod2Bridge.pack y j)) f) :
    Span (rawInput n) (fun v=>f v.2) := by
  apply (pullback h Prod.snd).weaken
  intro g hg
  apply List.mem_append_right
  simpa only [List.map_map,Function.comp_def] using hg

theorem partner_affine {n k m r : Nat} (e : Wiring n k m r) (j : Nat) :
    Span (rawInput n) (fun v=>baseRead n k m r e j v.2) :=
  pull_y (base_affine_raw e j)

theorem word_affine {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (i : Fin m) :
    Span (rawInput n) (fun v=>wordBit A i (e v.2).1) := by
  let L : Vec n→ₗ[F] F := {
    toFun := fun y=>dotProduct (A i) (e y).1
    map_add' := by intros; simp [dotProduct_add]
    map_smul' := by intros; simp [dotProduct_smul] }
  exact pull_y (linear_forms_affine L)

theorem bias_affine {n : Nat} (a dual : Assign) (b : Bool) :
    Span (rawInput n) (fun v=>b ^^ dot (List.range n) (shift a (ZMod2Bridge.pack v.2)) dual) := by
  have p : (fun v : Vec n×Vec n=>b ^^ dot (List.range n) (shift a (ZMod2Bridge.pack v.2)) dual)=
      fun v=> (b ^^ dot (List.range n) a dual) ^^ dot (List.range n) dual (ZMod2Bridge.pack v.2) := by
    funext v
    rw [LinearExtension.dot_shift_left,dot_comm (List.range n) (ZMod2Bridge.pack v.2) dual,Bool.xor_assoc]
  rw [p]
  let xs : (Vec n × Vec n)  →  Assign := fun v => ZMod2Bridge.pack v.1
  let ys : (Vec n × Vec n)  →  Assign := fun v => ZMod2Bridge.pack v.2
  have rawY (j : Nat) (hj : j ∈ List.range n) :
      Span (rawInput n) (fun v => ys v j) :=
    y_raw (List.range n) xs ys j hj
  exact .plus (.const _) (dot_from_bank (rawInput n) (List.range n) ys rawY dual)

noncomputable def policy {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k)
    (vary : Nat → Bool) (bias : Nat → Bool) (j : Nat) : Coefficient (Vec n×Vec n) :=
  if hj : j<m then
    if vary j then .varying (fun v=>wordBit A ⟨j,hj⟩ (e v.2).1) else .fixed (bias j)
  else .fixed false

theorem policy_affine {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k)
    (vary bias : Nat → Bool) (j : Nat) :
    Span (rawInput n) (policy e A vary bias j).value := by
  unfold policy
  split
  · rename_i hi
    split
    · exact word_affine e A ⟨j,hi⟩
    · exact .const _
  · exact .const _

theorem policy_charges {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k)
    (vary bias : Nat → Bool) {j : Nat} (hj : j<m) :
    hasFee (policy e A vary bias) j=vary j := by
  unfold hasFee policy
  rw [dite_eq_left hj]
  cases h : vary j <;> rfl

theorem policy_word {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k)
    (vary bias : Nat → Bool) (i : Fin m) (v : Vec n×Vec n) :
    (policy e A vary bias i).value v=
      if vary i then wordBit A i (e v.2).1 else bias i := by
  unfold policy
  rw [dite_eq_left i.isLt]
  cases h : vary i <;> rfl

end PEqualNP.Outside.L_meta_32580.FieldUpperAffine

/- Source segment: FibreSelection. -/


namespace PEqualNP.Outside.L_meta_32580.FibreSelection
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.SelectiveRebase PEqualNP.Outside.L_meta_32580.FibreBasis

structure Target {S : Type} (ambient base sel : List Nat) (E : List S) where
  y : S → Assign → Assign
  p0 : Assign
  g : Nat → Assign
  tags : S → Option Nat
  support0 : supported ambient p0
  supports : ∀ i∈base++sel,supported ambient (g i)
  independent : ∀ x∈cube (base++sel),∀ y∈cube (base++sel),
    combine (base++sel) g x=combine (base++sel) g y → x=y
  distinct : (base++sel).Nodup
  apart : ∀ j∈sel,j∉base
  validTag : ∀ s∈E,∀ j,tags s=some j → j∈sel
  injective : ∀ s∈E,∀ t∈E,tags s=tags t → s=t
  shape : ∀ s∈E,∀ b∈cube base,y s b=shift p0 (shift (combine base g b) (label g (tags s)))

structure Recipe {S : Type} {ambient base sel : List Nat} {E : List S} (T : Target ambient base sel E)
    (skip : Option S) where
  domain : List Nat
  dir : Nat → Assign
  anchor : Assign
  nd : domain.Nodup
  includes : ∀ i∈base,i∈domain
  width : domain.length=(base++sel).length-(if skip.isSome then 1 else 0)
  support : supported ambient anchor
  supports : ∀ j∈domain,supported ambient (dir j)
  inj : ∀ x∈cube domain,∀ y∈cube domain,combine domain dir x=combine domain dir y → x=y
  cover : ∀ s∈E,skip≠some s → ∀ b∈cube base,∃ coef∈cube domain,
    T.y s b=shift anchor (combine domain dir coef) ∧ ∀ i∈base,coef i=b i
  omitted : ∀ s,skip=some s → ∀ b∈cube base,¬memberHull domain dir anchor (T.y s b)

def full {S : Type} {c B D : List Nat} {E : List S} (T : Target c B D E) : Recipe T none where
  domain := B++D
  dir := T.g
  anchor := T.p0
  nd := T.distinct
  includes := fun _ h=>List.mem_append_left _ h
  width := by simp
  support := T.support0
  supports := T.supports
  inj := T.independent
  cover := by
    intro s hs _ b hb
    obtain ⟨r,coords,eq⟩ := coeff_induces T.distinct T.apart T.g b hb (T.tags s) (T.validTag s hs)
    exact ⟨coeff b (T.tags s),r,(T.shape s hs b hb).trans (congrArg (shift T.p0) eq.symm),coords⟩
  omitted := by intro _ h; cases h

                                                                        
                                                                      
                                                                
                               
theorem remove {S : Type} {c B D : List Nat} {E : List S}
    (nc : c.Nodup) (nd : E.Nodup) (len : 2 ≤ E.length) (T : Target c B D E)
    (u : S) (hu : u∈E) :
    Nonempty (Recipe T (some u)) := by
  classical
  cases tag : T.tags u with
  | some j =>
    have jD := T.validTag u hu j tag
    have jAll := List.mem_append_right B jD
    have rem : (B++D).erase j=B++D.erase j := List.erase_append_right D (T.apart j jD)
    have both : (B++D.erase j).Nodup := by rw [←rem]; exact T.distinct.erase _
    have inside := erased_independent T.distinct T.g T.independent jAll
    rw [rem] at inside
    refine ⟨{
      domain := B++D.erase j
      dir := T.g
      anchor := T.p0
      nd := both
      includes := fun _ h=>List.mem_append_left _ h
      width := ?_
      support := T.support0
      supports := by intro i hi; rw [←rem] at hi; exact T.supports i (List.mem_of_mem_erase hi)
      inj := inside
      cover := ?_
      omitted := ?_
    }⟩
    · rw [←rem,List.length_erase_of_mem jAll]
      rfl
    · intro s hs no b hb
      have valid : ∀ k,T.tags s=some k → k∈D.erase j := by
        intro k match_
        have kD := T.validTag s hs k match_
        have ne : k≠j := by
          intro eq
          subst k
          have sU := T.injective s hs u hu (match_.trans tag.symm)
          exact no (congrArg some sU.symm)
        have m := (List.perm_cons_erase jD).mem_iff.mp kD
        exact (List.mem_cons.mp m).resolve_left ne
      obtain ⟨each,read,calc_⟩ := coeff_induces both
        (fun k hk=>T.apart k (List.mem_of_mem_erase hk)) T.g b hb (T.tags s) valid
      exact ⟨coeff b (T.tags s),each,(T.shape s hs b hb).trans (congrArg (shift T.p0) calc_.symm),read⟩
    · intro s someEq b hb
      have eq : u=s := Option.some.inj someEq
      subst s
      rw [T.shape u hu b hb,tag]
      change ¬ memberHull (B++D.erase j) T.g T.p0
        (shift T.p0 (shift (combine B T.g b) (T.g j)))
      rw [←rem]
      exact delete_fibre_off T.distinct T.apart T.g T.independent T.p0 jD b hb
  | none =>
    obtain ⟨s,hs,t,ht,st⟩ := CountProfile.two_members nd len
    have another : ∃ v∈E,v≠u := by
      by_cases eq : s=u
      · exact ⟨t,ht,fun z=>st (eq.trans z.symm)⟩
      · exact ⟨s,hs,eq⟩
    obtain ⟨v,hv,vu⟩ := another
    have someJ : ∃ j,T.tags v=some j := by
      cases x : T.tags v with
      | none => exact False.elim (vu (T.injective v hv u hu (x.trans tag.symm)))
      | some j => exact ⟨j,rfl⟩
    obtain ⟨j,jtag⟩ := someJ
    have jD := T.validTag v hv j jtag
    have jAll := List.mem_append_right B jD
    have rem : (B++D).erase j=B++D.erase j := List.erase_append_right D (T.apart j jD)
    let marked := fun i=>decide (i∈D)
    let g := selectRebase T.g marked j
    let a := shift T.p0 (T.g j)
    have both : (B++D.erase j).Nodup := by rw [←rem]; exact T.distinct.erase _
    have inside := select_independent nc T.distinct T.g T.supports T.independent marked jAll
    rw [rem] at inside
    have onBase : ∀ i∈B,g i=T.g i := by
      intro i hi
      have nope : i∉D := fun s=>T.apart i s hi
      simp [g,selectRebase,marked,nope]
    refine ⟨{
      domain := B++D.erase j
      dir := g
      anchor := a
      nd := both
      includes := fun _ h=>List.mem_append_left _ h
      width := by rw [←rem,List.length_erase_of_mem jAll]; rfl
      support := IsotropyCount.add_supported T.support0 (T.supports _ jAll)
      supports := ?_
      inj := inside
      cover := ?_
      omitted := ?_
    }⟩
    · intro i hi
      rw [←rem] at hi
      have a := T.supports i (List.mem_of_mem_erase hi)
      unfold g selectRebase
      split
      · exact IsotropyCount.add_supported (T.supports _ jAll) a
      · exact a
    · intro s hs no b hb
      have someK : ∃ k,T.tags s=some k := by
        cases x : T.tags s with
        | none =>
          have eq := T.injective s hs u hu (x.trans tag.symm)
          exact False.elim (no (congrArg some eq.symm))
        | some k => exact ⟨k,rfl⟩
      obtain ⟨k,ktag⟩ := someK
      have kD := T.validTag s hs k ktag
      let effective : Option Nat := if k=j then none else some k
      have sane : ∀ z,effective=some z → z∈D.erase j := by
        intro z zz
        by_cases eq : k=j
        · simp [effective,eq] at zz
        · have aa : k=z := by simpa [effective,eq] using zz
          subst z
          exact (List.mem_cons.mp ((List.perm_cons_erase jD).mem_iff.mp kD)).resolve_left eq
      obtain ⟨fits,read,calc_⟩ := coeff_induces both
        (fun i hi=>T.apart i (List.mem_of_mem_erase hi)) g b hb effective sane
      refine ⟨coeff b effective,fits,?_,read⟩
      rw [T.shape s hs b hb,ktag,calc_,combine_restrict g T.g onBase]
      change shift T.p0 (shift (combine B T.g b) (T.g k)) =
        shift (shift T.p0 (T.g j)) (shift (combine B T.g b) (label g effective))
      by_cases eq : k=j
      · subst k
        simp only [effective,ite_true,label]
        funext i
        simp only [shift,zero,Bool.false_xor,Bool.xor_false,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
      · have flag : marked k=true := decide_eq_true_eq.mpr kD
        have seq : g k=shift (T.g j) (T.g k) := by
          unfold g selectRebase
          rw [if_pos flag]
        simp only [effective,if_neg eq,label,seq]
        funext i
        simp only [shift]
        cases T.p0 i <;> cases (combine B T.g b) i <;> cases T.g j i <;> cases T.g k i <;> rfl
    · intro s someEq b hb
      have eq : u=s := Option.some.inj someEq
      subst s
      rw [T.shape u hu b hb,tag]
      simp only [label]
      rw [shift_comm (combine B T.g b) zero,shift_zero,←rem]
      exact drop_anchor_fibre_off nc T.distinct T.apart T.g T.supports T.independent
        T.p0 jD b hb

end PEqualNP.Outside.L_meta_32580.FibreSelection

/- Source segment: FieldTarget. -/

                                                                 

namespace PEqualNP.Outside.L_meta_32580.FieldTarget
open scoped BigOperators
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.FibreBasis PEqualNP.Outside.L_meta_32580.FibreSelection
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.ExactHull PEqualNP.Outside.L_meta_32580.MathlibReduction

theorem axis_ranges (b d : Nat) : List.range b++List.range' b d=List.range (b+d) := by
  rw [List.range_eq_range' (n:=b),List.range_eq_range' (n:=b+d)]
  simpa only [Nat.zero_add] using (@List.range'_append_1 0 b d)

theorem pack_zero {n : Nat} : ZMod2Bridge.pack (n:=n) 0=zero := by
  funext j
  by_cases hj : j<n <;> simp [ZMod2Bridge.pack,hj,zero,toBit]

theorem rear_beta_zero {b d : Nat} {u : Assign} (supp : u∈cube (List.range b)) :
    rear (b:=b) (d:=d) (unpack (n:=b+d) u)=0 := by
  funext j
  have no : b+j.val∉List.range b := by simp only [List.mem_range]; omega
  have h := mem_cube.mp supp (b+j.val) no
  simp [rear,unpack,Fin.val_natAdd,h,ofBit]

theorem base_combo {n k m r d : Nat} (e : Wiring n k m r) (w : Fin d → Vec k)
    {u : Assign} (inB : u∈cube (List.range (2*m+r))) :
    let L := exactEmbedding e w
    combine (List.range (2*m+r)) (embedGenerators L) u =
      ZMod2Bridge.pack (selected n k m r e u 0) := by
  let B := List.range (2*m+r)
  let J := List.range' (2*m+r) d
  let L := exactEmbedding e w
  have none : ∀ j∈J,u j=false := by
    intro j hj
    have h := (List.mem_range'_1.mp hj).1
    exact mem_cube.mp inB j (fun e=>Nat.not_lt_of_ge h (List.mem_range.mp e))
  change combine B (embedGenerators L) u=ZMod2Bridge.pack (selected n k m r e u 0)
  rw [←combine_supported_left (B:=B) (D:=J) (embedGenerators L) u none]
  change combine (List.range (2*m+r)++List.range' (2*m+r) d) (embedGenerators L) u=_
  rw [axis_ranges,combine_embed]
  have fw : front (b:=2*m+r) (d:=d) (unpack (n:=2*m+r+d) u)=unpack (n:=2*m+r) u := rfl
  show ZMod2Bridge.pack (e.symm (Fintype.linearCombination F w (rear (unpack (n:=2*m+r+d) u)),
      tupleLinear m r (front (unpack (n:=2*m+r+d) u)))) =
    ZMod2Bridge.pack (selected n k m r e u 0)
  rw [rear_beta_zero inB,fw,map_zero,tupleUnpack]
  rfl

theorem sel_generator {n k m r d : Nat} (e : Wiring n k m r) (w : Fin d → Vec k) (i : Fin d) :
    embedGenerators (exactEmbedding e w) (2*m+r+i.val)=
      ZMod2Bridge.pack (e.symm (w i,0)) := by
  have hv : 2*m+r+i.val<2*m+r+d := by omega
  unfold embedGenerators
  rw [dite_eq_left hv]
  change ZMod2Bridge.pack (e.symm (Fintype.linearCombination F w
     (rear (Pi.single (i.natAdd (2*m+r)) 1)),
     tupleLinear m r (front (Pi.single (i.natAdd (2*m+r)) 1))))=_
  rw [rear_single_right,front_single_right,Fintype.linearCombination_apply_single,one_smul,map_zero]

theorem exact_target {n k m r d : Nat} (e : Wiring n k m r)
    (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (dDef : d=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k)))))
    (dCard : E.card=d+1) :
    ∃ T : Target (List.range n) (List.range (2*m+r)) (List.range' (2*m+r) d) E.toList,
      ∀ s b,T.y s b=ZMod2Bridge.pack (selected n k m r e b s) := by
  classical
  have card : (E.erase a).card=d := by rw [Finset.card_erase_of_mem ha,dCard]; omega
  let en : ↥(E.erase a)≃Fin d := Finset.equivFinOfCardEq card
  let w : Fin d → Vec k := fun i=>(en.symm i).val-a
  have dCard' : E.card=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+1 :=
    dCard.trans (congrArg (fun j=>j+1) dDef)
  have ind := (selector_independent E a ha dCard').comp en.symm en.symm.injective
  let L := exactEmbedding e w
  let g := embedGenerators L
  let B := List.range (2*m+r)
  let J := List.range' (2*m+r) d
  let zeroY := ZMod2Bridge.pack (e.symm (a,0))
  let tag (s : Vec k) := if h:s∈E.erase a then some (2*m+r+(en ⟨s,h⟩).val) else none
  have eqAxes : B++J=List.range (2*m+r+d) := axis_ranges _ _
  refine ⟨{
    y := fun s b=>ZMod2Bridge.pack (selected n k m r e b s)
    p0 := zeroY
    g := g
    tags := tag
    support0 := mem_cube.mp (pack_mem _)
    supports := fun j _=>generator_supported L j
    independent := ?_
    distinct := ?_
    apart := ?_
    validTag := ?_
    injective := ?_
    shape := ?_
  },fun _ _=>rfl⟩
  · rw [eqAxes]
    exact embed_independent L (exactEmbedding_injective e w ind)
  · rw [eqAxes]
    exact List.nodup_range
  · intro i hi m
    have h1 := (List.mem_range'_1.mp hi).1
    have h2 := List.mem_range.mp m
    omega
  · intro s _ j eq
    unfold tag at eq
    split at eq
    · rename_i h
      have e' := Option.some.inj eq
      subst j
      apply List.mem_range'_1.mpr
      have n := (en ⟨s,h⟩).isLt
      omega
    · cases eq
  · intro s hs t ht eq
    by_cases sh : s∈E.erase a <;> by_cases th : t∈E.erase a
    · have h : (en ⟨s,sh⟩).val=(en ⟨t,th⟩).val := by
        simp only [tag,dite_eq_left sh,dite_eq_left th,Option.some.injEq] at eq
        omega
      exact congrArg Subtype.val (en.injective (Fin.ext h))
    · dsimp only [tag] at eq
      rw [dite_eq_left sh,dite_eq_right th] at eq
      contradiction
    · dsimp only [tag] at eq
      rw [dite_eq_right sh,dite_eq_left th] at eq
      contradiction
    · have ss : s=a := by
        by_contra bad
        exact sh (Finset.mem_erase.mpr ⟨bad,by simpa using hs⟩)
      have tt : t=a := by
        by_contra bad
        exact th (Finset.mem_erase.mpr ⟨bad,by simpa using ht⟩)
      exact ss.trans tt.symm
  · intro s hs b hb
    have what := base_combo e w hb
    change ZMod2Bridge.pack (selected n k m r e b s)=
      shift zeroY (shift (combine B g b) (label g (tag s)))
    rw [what]
    by_cases h:s∈E.erase a
    · let j := en ⟨s,h⟩
      have wj : w j=s-a := by simp [w,j]
      have gJ : label g (tag s)=ZMod2Bridge.pack (e.symm (s-a,0)) := by
        simp only [tag,dite_eq_left h,label]
        change embedGenerators (exactEmbedding e w) (2*m+r+j.val)=_
        rw [sel_generator e w j,wj]
      rw [gJ,←pack_add]
      simp only [zeroY,selected]
      rw [←pack_add,←map_add,←map_add]
      simp [sub_eq_add_neg,add_assoc,add_left_comm,add_comm]
    · have eq : s=a := by
        by_contra ne
        exact h (Finset.mem_erase.mpr ⟨ne,by simpa using hs⟩)
      subst s
      simp only [tag,dite_eq_right h,label]
      have P : ∀ v : Assign,shift v zero=v := fun v=>by rw [shift_comm,AffineProjection.shift_zero]
      rw [P,←pack_add]
      simp only [zeroY,selected]
      rw [←map_add]
      simp

end PEqualNP.Outside.L_meta_32580.FieldTarget

/- Source segment: FibreH. -/


namespace PEqualNP.Outside.L_meta_32580.FibreH
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.FibreSelection PEqualNP.Outside.L_meta_32580.FibreBasis

                                                                          
                                                                       
theorem h_interpolates {S : Type} {c B J : List Nat} {E : List S} (nc : c.Nodup)
    (T : Target c B J E) (hv : S → Bool) :
    ∃ b q,supported c q ∧
      ∀ s∈E,∀ x∈cube B, (b ^^ dot c (shift T.p0 (T.y s x)) q)=hv s := by
  classical
  let b : Bool := if h : ∃ s∈E,T.tags s=none then hv (Classical.choose h) else false
  let g (j : Nat) : Bool :=
    if j∈B then b else if h : ∃ s∈E,T.tags s=some j then hv (Classical.choose h) else b
  have bas (s : S) (hs : s∈E) (q : T.tags s=none) : b=hv s := by
    have ex : ∃ v∈E,T.tags v=none := ⟨s,hs,q⟩
    simp only [b,dite_eq_left ex]
    have eq := T.injective _ (Classical.choose_spec ex).1 s hs
      ((Classical.choose_spec ex).2.trans q.symm)
    rwa [eq]
  have sep (s : S) (hs : s∈E) {i : Nat} (hi : T.tags s=some i) : g i=hv s := by
    have no : i∉B := T.apart i (T.validTag s hs i hi)
    have ex : ∃ t∈E,T.tags t=some i := ⟨s,hs,hi⟩
    simp only [g,ite_eq_right no,dite_eq_left ex]
    have eq := T.injective _ (Classical.choose_spec ex).1 s hs
      ((Classical.choose_spec ex).2.trans hi.symm)
    rwa [eq]
  obtain ⟨q,qs,_,ones⟩ := interpolate nc T.distinct T.g T.supports T.independent T.p0 b g
  have value (i : Nat) (hi : i∈B++J) :
      (b ^^ dot c (T.g i) q)=g i := by simpa only [shift_invol] using ones i hi
  have zeroBase (x : Assign) : dot c (combine B T.g x) q=false := by
    rw [combine_dot,←parity_zero B]
    apply parity_congr
    intro i hi
    have hh := value i (List.mem_append_left _ hi)
    have good : g i=b := by simp [g,hi]
    rw [good] at hh
    have z : dot c (T.g i) q=false := by
      generalize h : dot c (T.g i) q=bb at *
      cases b <;> cases bb <;> simp_all
    rw [z,Bool.and_false]
  refine ⟨b,q,qs,?_⟩
  intro s hs x hx
  rw [T.shape s hs x hx,shift_invol,LinearExtension.dot_shift_left,zeroBase,Bool.false_xor]
  cases tag : T.tags s with
  | none =>
    rw [label,dot_zero,Bool.xor_false]
    exact bas s hs tag
  | some j =>
    rw [label,value _ (List.mem_append_right _ (T.validTag s hs j tag))]
    exact sep s hs tag

end PEqualNP.Outside.L_meta_32580.FibreH

/- Source segment: OptionRealizers. -/


namespace PEqualNP.Outside.L_meta_32580.OptionRealizers
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.Polarization PEqualNP.Outside.L_meta_32580.OrthogonalCount
open PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.DualBasis PEqualNP.Outside.L_meta_32580.FirstFold

theorem bit_half {d : List Nat} {i : Nat} (hi : i∈d) :
    2*(cube d).countP (fun x=>x i)=(cube d).length := by
  apply exactly_half (unit_supported hi)
  intro x
  simp [shift,unit,Bool.true_xor]

                                                                   
                                                                      
                                                           
theorem two_bits_quarter {d : List Nat} (nd : d.Nodup) {i j : Nat}
    (hi : i∈d) (hj : j∈d) (ne : i≠j) :
    4*(cube d).countP (fun x=>x i && x j)=(cube d).length := by
  let p : Assign → Bool := fun x=>x i && x j
  have cp := (pivot_free hi).countP_eq p
  change (cube d).countP p=((cube (d.erase i)).flatMap (fun x=>[put x i false,put x i true])).countP p at cp
  rw [pair_count] at cp
  have zeroBranch : (fun x=>p (put x i false))=(fun _=>false) := by
    funext x
    simp [p,put]
  have oneBranch : (fun x=>p (put x i true))=(fun x=>x j) := by
    funext x
    simp [p,put,Ne.symm ne]
  rw [zeroBranch,oneBranch] at cp
  have je : j∈d.erase i := by
    have perm := List.perm_cons_erase hi
    have mv := perm.mem_iff.mp hj
    exact (List.mem_cons.mp mv).resolve_left (Ne.symm ne)
  have bit := bit_half je
  have size := (pivot_free hi).length_eq
  rw [show ((cube (d.erase i)).flatMap (two i)).length=2*(cube (d.erase i)).length from by
    suffices ∀ t : List Assign, (t.flatMap (two i)).length=2*t.length from this _
    intro t
    induction t with
    | nil => rfl
    | cons x t ih => simp [two,List.flatMap_cons,ih]; omega] at size
  have xx : (cube (d.erase i)).countP (fun _=>false)=0 := by simp
  rw [xx,Nat.zero_add] at cp
  change 4*(cube d).countP p=(cube d).length
  omega

theorem nonzero_difference {a b : Assign} (diff : a≠b) : shift a b≠zero := by
  intro eq
  apply diff
  have h := congrArg (shift a) eq
  rw [shift_invol,shift_comm a zero,shift_zero] at h
  exact h.symm

                                                                
                                                                        
theorem frequency_miss {d : List Nat} (nd : d.Nodup) (a b : Assign)
    (sa : supported d a) (sb : supported d b) (diff : a≠b)
    (bias : Bool) :
    2*(cube d).countP (fun x=>dot d x (shift a b) ^^ bias)=(cube d).length := by
  have main := ambient_halves nd (shift a b) (IsotropyCount.add_supported sa sb)
    (nonzero_difference diff)
  have norm : (fun x=>dot d x (shift a b) ^^ bias)=
      (fun x=>dot d (shift a b) x ^^ bias) :=
    funext (fun x=>congrArg (fun a=>a ^^ bias) (dot_comm d x (shift a b)))
  rw [norm]
  cases bias with
  | false => simpa using main
  | true =>
    have comp := count_complement (cube d) (dot d (shift a b))
    simp only [Bool.xor_true]
    omega

theorem project_cancels {c hd : List Nat} (nc : c.Nodup) (g duals : Nat → Assign)
    (a y : Assign) (sa : supported c a) (sy : supported c y)
    (gen : ∀ j∈hd,supported c (g j))
    (basis_duals : ∀ j∈hd,∀ x∈cube hd,dot c (combine hd g x) (duals j)=x j)
    (offHull : ¬memberHull hd g a y) (bias : Bool) :
    2*(cube c).countP (fun x=>dot c x (shift y (projectTo c hd g duals a y)) ^^ bias)=(cube c).length := by
  apply frequency_miss nc y (projectTo c hd g duals a y) sy
  · exact IsotropyCount.add_supported sa (combine_support gen _)
  · exact fun e=>offHull ((project_hit_iff basis_duals a y).mp e.symm)

end PEqualNP.Outside.L_meta_32580.OptionRealizers

/- Source segment: UpperLossCounts. -/


namespace PEqualNP.Outside.L_meta_32580.UpperLossCounts
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.OptionRealizers
open PEqualNP.Outside.L_meta_32580.FirstFold PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.CircuitFlatten PEqualNP.Outside.L_meta_32580.PairSlots

theorem interpreted_discrepancy {Y S : Type} {n m r : Nat}
    (D : Input (Y:=Y) (S:=S) n m r) (C : Circuit) (s : S)
    (pro : Assign → Assign) (frozen : Assign → Bool)
    (formula : ∀ x b,C.eval (bits n x++bits n (fun j=>D.yValue j (D.pack b s)))=
      (dot (List.range n) x (pro b) ^^ frozen b)) :
    ∀ x b,actualError D C s x b =
      (dot (List.range n) x (shift (pro b) (fun j=>D.yValue j (D.pack b s))) ^^
       (frozen b ^^ tailPhase D s b)) := by
  intro x b
  rw [actualError,formula,dot_shift]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

theorem count_aligned (dx db : List Nat) (f : Assign → Assign → Bool) (p : Assign → Bool)
    (all : ∀ b∈cube db,∀ x∈cube dx,f x b=p b) :
    count2 dx db f=(cube dx).length*(cube db).countP p := by
  have c (b : Assign) (hb : b∈cube db) : (cube dx).countP (fun x=>f x b)=
      (if p b then (cube dx).length else 0) :=
    count_constant _ _ _ (all b hb)
  unfold count2
  rw [List.map_congr_left c]
  induction (cube db) with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons,List.sum_cons,countP_cons_add,Nat.mul_add,ih]
    cases q : p b <;> simp [q]

                                                                    
theorem exactly_fits {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (s : S)
    (formula : ∀ b∈cube (List.range (2*m+r)),∀ x∈cube (List.range n),
      C.eval (bits n x++bits n (fun j=>D.yValue j (D.pack b s)))=
        (dot (List.range n) x (fun j=>D.yValue j (D.pack b s)) ^^ tailPhase D s b)) :
    (actualLeaf D C).errors s=0 := by
  unfold actualLeaf
  have q := count_aligned (List.range n) (List.range (2*m+r)) (actualError D C s)
    (fun _=>false) (by intro b hb x hx; simp [actualError,formula b hb x hx])
  simpa using q

                                                                     
                                                                        
theorem frozen_column {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (s : S) {i : Nat} (hi : i<m)
    (formula : ∀ b∈cube (List.range (2*m+r)),∀ x∈cube (List.range n),
      actualError D C s x b=(b (left i) && b (right i))) :
    4*(actualLeaf D C).errors s=(actualLeaf D C).mass := by
  let dx := List.range n
  let db := List.range (2*m+r)
  let p : Assign → Bool := fun b=>b (left i) && b (right i)
  have q := count_aligned dx db (actualError D C s) p formula
  have a : left i∈db := by simp [db,left]; omega
  have b : right i∈db := by simp [db,right]; omega
  have ne : left i≠right i := by simp [left,right]
  have fraction := two_bits_quarter (d:=db) List.nodup_range a b ne
  change 4*(cube db).countP p=(cube db).length at fraction
  change 4*count2 dx db (actualError D C s)=(cube db).length*(cube dx).length
  rw [q,Nat.mul_left_comm 4,fraction,Nat.mul_comm]

                                                                    
                                                                  
                                                            
theorem dropped_point {Y S : Type} {n m r : Nat} (D : Input (Y:=Y) (S:=S) n m r)
    (C : Circuit) (s : S) (proj : Assign → Assign) (pay : Assign → Bool)
    (supp : ∀ b∈cube (List.range (2*m+r)),supported (List.range n) (proj b))
    (miss : ∀ b∈cube (List.range (2*m+r)),proj b≠fun j=>D.yValue j (D.pack b s))
    (formula : ∀ x b,C.eval (bits n x++bits n (fun j=>D.yValue j (D.pack b s)))=
      (dot (List.range n) x (proj b) ^^ pay b)) :
    2*(actualLeaf D C).errors s=(actualLeaf D C).mass := by
  let dx := List.range n
  let db := List.range (2*m+r)
  let err (b : Assign) := (cube dx).countP (fun x=>actualError D C s x b)
  have each : ∀ b∈cube db,2*err b=(cube dx).length := by
    intro b hb
    have q := frequency_miss List.nodup_range (proj b) (fun j=>D.yValue j (D.pack b s)) (supp b hb)
      (D.support_y _) (miss b hb) (pay b ^^ tailPhase D s b)
    simpa only [err,interpreted_discrepancy D C s proj pay formula] using q
  have summed := sum_halves (cube db) err (fun _=>false) (cube dx).length (by
    intro b hb
    simpa using each b hb)
  simpa [actualLeaf,count2,err,dx,db] using summed

end PEqualNP.Outside.L_meta_32580.UpperLossCounts

/- Source segment: FieldRecipeCircuit. -/

                                                

namespace PEqualNP.Outside.L_meta_32580.FieldRecipeCircuit
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.CubeGeometry
open PEqualNP.Outside.L_meta_32580.Translation PEqualNP.Outside.L_meta_32580.OrthogonalCount PEqualNP.Outside.L_meta_32580.AffineProjection PEqualNP.Outside.L_meta_32580.DualBasis
open PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.TapeKernel PEqualNP.Outside.L_meta_32580.ParamReify
open PEqualNP.Outside.L_meta_32580.AffineRawCost PEqualNP.Outside.L_meta_32580.FibreSelection PEqualNP.Outside.L_meta_32580.FibreH
open PEqualNP.Outside.L_meta_32580.CellAggregation (hasFee)
open PEqualNP.Outside.L_meta_32580.CircuitAdapter PEqualNP.Outside.L_meta_32580.CircuitFlatten PEqualNP.Outside.L_meta_32580.FieldUpperAffine
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.ProjectLower

def packed {n k m r : Nat} (e : Wiring n k m r) (s : Vec k) (b : Assign) : Assign :=
  ZMod2Bridge.pack (selected n k m r e b s)

def wordVal {k m : Nat} (A : Fin m → Vec k) (vary bias : Nat → Bool) (s : Vec k) (i : Nat) : Bool :=
  if hi : i<m then if vary i then wordBit A ⟨i,hi⟩ s else bias i else false

theorem policy_eval_selected {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k)
    (vary bias : Nat → Bool) (s : Vec k) (b : Assign) (x : Vec n) {i : Nat} (hi : i<m) :
    (policy e A vary bias i).value (x,selected n k m r e b s)=wordVal A vary bias s i := by
  rw [policy_word e A vary bias ⟨i,hi⟩]
  simp [wordVal,hi,selected]

theorem bank_inputs {n : Nat} (x y : Vec n) :
    samples (rawInput n) (x,y)=bits n (ZMod2Bridge.pack x)++bits n (ZMod2Bridge.pack y) := by
  simp [samples,rawInput,rawBank,bits,List.map_map,Function.comp_def]

theorem bits_unpack {n : Nat} (x : Assign) : bits n (ZMod2Bridge.pack (unpack (n:=n) x))=bits n x := by
  apply List.map_congr_left
  exact fun j hj=>pack_unpack_inside x (List.mem_range.mp hj)

theorem dot_unpack {n : Nat} (x y : Assign) :
    dot (List.range n) (ZMod2Bridge.pack (unpack (n:=n) x)) y=dot (List.range n) x y := by
  apply parity_congr
  intro j hj
  rw [pack_unpack_inside x (List.mem_range.mp hj)]

theorem yield_recipe {n k m r d : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (E : List (Vec k)) (T : Target (List.range n) (List.range (2*m+r)) (List.range' (2*m+r) d) E)
    (tEq : ∀ s b,T.y s b=packed e s b) (skip : Option (Vec k)) (R : Recipe T skip)
    (vary bias : Nat → Bool) :
    ∃ C : Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
      (∀ g∈C.gates,Legal g) ∧
      publicCost C.gates=R.domain.length+(List.range m).countP vary ∧
      (∀ s∈E,skip≠some s → ∀ b∈cube (List.range (2*m+r)),∀ x,
        C.eval (bits n x++bits n (packed e s b)) =
          (dot (List.range n) x (packed e s b) ^^
           (toBit (h s) ^^ parity (fun i=>wordVal A vary bias s i&&(b (left i)&&b (right i))) (List.range m)))) ∧
      (∀ s,skip=some s → ∃ proj : Assign → Assign,∃ pay : Assign → Bool,
        (∀ b∈cube (List.range (2*m+r)),supported (List.range n) (proj b)) ∧
        (∀ b∈cube (List.range (2*m+r)),proj b≠packed e s b) ∧
        ∀ x b,C.eval (bits n x++bits n (packed e s b)) =
          (dot (List.range n) x (proj b) ^^ pay b)) := by
  classical
  let c := List.range n
  let I := List.range m
  let bdom := List.range (2*m+r)
  have left_in (i : Nat) (hi : i∈I) : left i∈bdom := by
    have m := List.mem_range.mp hi
    simp [bdom,left]
    omega
  have right_in (i : Nat) (hi : i∈I) : right i∈bdom := by
    have m := List.mem_range.mp hi
    simp [bdom,right]
    omega
  obtain ⟨tail,p⟩ := paired_first R.nd I List.nodup_range (fun i hi=>R.includes _ (left_in i hi))
  let hd := I.map left++tail
  have hdNd : hd.Nodup := p.symm.nodup R.nd
  have hn : ∀ j∈hd,supported c (R.dir j) := fun j jh=>R.supports j (p.mem_iff.mp jh)
  have cp := cube_perm p hdNd
  have inj : ∀ a∈cube hd,∀ b∈cube hd,combine hd R.dir a=combine hd R.dir b → a=b := by
    intro a ha b hb eq
    apply R.inj a (cp.mem_iff.mp ha) b (cp.mem_iff.mp hb)
    change combine (I.map left ++ tail) R.dir a = combine (I.map left ++ tail) R.dir b at eq
    simpa only [combine_perm p R.dir] using eq
  obtain ⟨dual,_,hdDual⟩ := choose_duals List.nodup_range hdNd R.dir hn inj
  obtain ⟨bit,q,_,hfit⟩ := h_interpolates List.nodup_range T (fun s=>toBit (h s))
  let costWord := policy e A vary bias
  let partner : Nat → Fun (Vec n×Vec n) := fun i v=>baseRead n k m r e (right i) v.2
  let hApprox : Fun (Vec n×Vec n) := fun v=>bit ^^ dot c (shift T.p0 (ZMod2Bridge.pack v.2)) q
  let xs := fun v : Vec n×Vec n=>ZMod2Bridge.pack v.1
  let ys := fun v : Vec n×Vec n=>ZMod2Bridge.pack v.2
  obtain ⟨C,reads,lg,fee,law⟩ := AffineRawCost.emit c R.domain I tail p R.dir dual R.anchor xs ys partner
    costWord hApprox (bias_affine T.p0 q bit) (fun i=>partner_affine e (right i))
    (policy_affine e A vary bias)
  have fleg : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C := by
    apply ExactDefinitions.readback_literal
    simpa [rawBank,c,Nat.two_mul] using reads
  have wordCost : I.countP (hasFee costWord) = I.countP vary := by
    apply List.countP_congr
    intro i hi
    change hasFee (policy e A vary bias) i ↔ vary i
    rw [policy_charges e A vary bias (List.mem_range.mp hi)]
  have cst : publicCost C.gates=R.domain.length+I.countP vary := by
    rw [fee,wordCost]
  let P := fun s b=>projectTo c hd R.dir dual R.anchor (packed e s b)
  let payment := fun s b=>hApprox (0,selected n k m r e b s) ^^
    parity (fun i=>wordVal A vary bias s i &&
      (coordinates c hd dual R.anchor (packed e s b) (left i) && b (right i))) I
  have formula (s : Vec k) (x b : Assign) :
      C.eval (bits n x++bits n (packed e s b))=(dot c x (P s b) ^^ payment s b) := by
    have q1 := law (unpack (n:=n) x,selected n k m r e b s)
    change C.eval (samples (rawInput n) (unpack (n:=n) x,selected n k m r e b s))= _ at q1
    rw [bank_inputs,bits_unpack] at q1
    change C.eval (bits n x++bits n (packed e s b))=
      (dot c (ZMod2Bridge.pack (unpack (n:=n) x)) (P s b) ^^ _) at q1
    rw [dot_unpack] at q1
    rw [q1]
    unfold payment
    congr 2
    apply parity_congr
    intro i hi
    rw [policy_eval_selected e A vary bias s b (unpack x) (List.mem_range.mp hi)]
    rw [show partner i (unpack (n:=n) x,selected n k m r e b s)=b (right i) from
       base_selected n k m r e s b (right i) (List.mem_range.mp (right_in i hi))] <;> rfl
  refine ⟨C,fleg,lg,cst,?_,?_⟩
  · intro s hs keep b hb x
    obtain ⟨co,hco,form,read⟩ := R.cover s hs keep b hb
    have eY : packed e s b=shift R.anchor (combine hd R.dir co) := by
      calc
        packed e s b = T.y s b := (tEq s b).symm
        _ = shift R.anchor (combine R.domain R.dir co) := form
        _ = shift R.anchor (combine hd R.dir co) :=
          congrArg (shift R.anchor) (combine_perm p R.dir co).symm
    have mem_co : co∈cube hd := cp.mem_iff.mpr hco
    have coords := coordinates_decode hdDual R.anchor mem_co
    have fx : P s b=packed e s b := (project_hit_iff hdDual R.anchor (packed e s b)).mpr ⟨co,mem_co,eY⟩
    have bval : hApprox (0,selected n k m r e b s)=toBit (h s) := by
      change (bit ^^ dot c (shift T.p0 (packed e s b)) q) = toBit (h s)
      rw [←tEq s b]
      exact hfit s hs b hb
    rw [formula,fx]
    dsimp only [payment]
    rw [bval]
    congr 2
    apply parity_congr
    intro i hi
    have co_i := congrFun coords (left i)
    rw [←eY] at co_i
    rw [co_i,read _ (left_in i hi)]
  · intro s hit
    refine ⟨P s,payment s,?_,?_,formula s⟩
    · intro b _
      exact IsotropyCount.add_supported R.support (combine_support hn _)
    · intro b hb eq
      have hh := (project_hit_iff hdDual R.anchor (packed e s b)).mp eq
      have q := (hull_perm p hdNd R.dir R.anchor (packed e s b)).mp hh
      rw [←tEq s b] at q
      exact R.omitted s hit b hb q

end PEqualNP.Outside.L_meta_32580.FieldRecipeCircuit

/- Source segment: FieldOptions. -/

                                                                      
                                                                    

namespace PEqualNP.Outside.L_meta_32580.FieldOptions
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.AffinePivot PEqualNP.Outside.L_meta_32580.CubePivot PEqualNP.Outside.L_meta_32580.Translation
open PEqualNP.Outside.L_meta_32580.PairSlots PEqualNP.Outside.L_meta_32580.TapeKernel
open PEqualNP.Outside.L_meta_32580.UpperLossCounts PEqualNP.Outside.L_meta_32580.FibreSelection PEqualNP.Outside.L_meta_32580.ColumnObstruction
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.ExactHull PEqualNP.Outside.L_meta_32580.FieldTarget
open PEqualNP.Outside.L_meta_32580.FieldRecipeCircuit PEqualNP.Outside.L_meta_32580.ExactScore PEqualNP.Outside.L_meta_32580.ExactDefinitions
open PEqualNP.Outside.L_meta_32580.CircuitAdapter PEqualNP.Outside.L_meta_32580.BoolLower PEqualNP.Outside.L_meta_32580.ProjectLower

def fits (n p : Nat) (C : Circuit) : Prop :=
  (PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    (∀ j∈C.gates,Legal j)) ∧ publicCost C.gates ≤ p

theorem count_drop {I : List Nat} (nd : I.Nodup) (p : Nat → Bool) {i : Nat} (hi : i∈I)
    (hit : p i=true) :
    I.countP (fun j=>if j=i then false else p j)+1=I.countP p := by
  let pay := fun j=>if j=i then false else p j
  have pi := List.perm_cons_erase hi
  rw [pi.countP_eq pay,pi.countP_eq p]
  have t : (I.erase i).countP pay=(I.erase i).countP p := by
    apply List.countP_congr
    intro j hj
    have ne : j≠i := fun e=>erase_avoids nd hi (e ▸ hj)
    simp [pay,ne]
  rw [List.countP_cons,List.countP_cons,t]
  simp [pay,hit]

theorem parity_single {I : List Nat} {i : Nat} (nd : I.Nodup) (hi : i∈I) (f : Nat → Bool)
    (zero : ∀ j∈I,j≠i → f j=false) :
    parity f I=f i := by
  rw [parity_perm (List.perm_cons_erase hi),parity]
  have t : parity f (I.erase i)=false := by
    rw [←OrthogonalCount.parity_zero (I.erase i)]
    apply parity_congr
    intro j hj
    exact zero j (List.mem_of_mem_erase hj) (fun eq=>erase_avoids nd hi (eq ▸ hj))
  rw [t,Bool.xor_false]

theorem default_word {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (A : Fin m → Vec k) (word : Vec k → Nat → Bool)
    (wordDef : ∀ s (i : Fin m),word s i=toBit (dotProduct (A i) s))
    (s : Vec k) (hs : s∈E) (i : Nat) (hi : i<m) :
    wordVal A (varying E.toList word) (word a) s i=word s i := by
  unfold wordVal
  rw [dite_eq_left hi]
  cases b : varying E.toList word i
  · have z : word a i=word s i := by
      by_contra bad
      have hit := (vary_from (E:=E.toList) (word:=word) (a:=a) (by simpa using ha) i).mpr
        ⟨s,by simpa using hs,bad⟩
      rw [b] at hit
      contradiction
    simpa [b] using z
  · simp [b,wordDef s (⟨i,hi⟩ : Fin m),wordBit]

theorem cancel_common_prefix (p q u v : Bool) :
    ((p ^^ (q ^^ u)) ^^ (p ^^ (q ^^ v))) = (u ^^ v) := by
  cases p <;> cases q <;> cases u <;> cases v <;> rfl

theorem projected_options {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (dpos : 0<Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k)))))
    (hcard : E.card=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+1) :
    ExactGame.Options E (wordBit A) (price r A E a) (fits n) (fun C s=>1-fieldScore e A h C s) := by
  classical
  let d := Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))
  let I := List.range m
  obtain ⟨D,pD,yD,hD,wD⟩ := exact_model e A h
  obtain ⟨T,Te⟩ := exact_target e E a ha (d:=d) rfl hcard
  let v := varying E.toList D.word
  let b0 := D.word a
  have known : ∀ s∈E,∀ i∈I,wordVal A v b0 s i=D.word s i := by
    intro s hs i hi
    exact default_word E a ha A D.word wD s hs i (List.mem_range.mp hi)
  have price_eq : price r A E a=2*m+r+d+I.countP v := by
    unfold price
    rw [varying_count_exact E a ha A D.word wD]
  have pos : ∀ C,0<(actualLeaf D C).mass := by
    intro C
    rw [mass_eq]
    positivity
  have regime : ∀ C s,1-fieldScore e A h C s=
      2*((actualLeaf D C).errors s:ℝ)/((actualLeaf D C).mass:ℝ) :=
    field_loss_formula e A h D pD yD hD wD
  have err_zero {C : Circuit} {s : Vec k} (he : (actualLeaf D C).errors s=0) :
      1-fieldScore e A h C s=0 := by rw [regime,he]; simp
  have fieldPacked (s : Vec k) (b : Assign) :
      (fun i=>D.yValue i (D.pack b s))=packed e s b := by rw [pD,yD]; rfl
  have covered_zero {C : Circuit} {s : Vec k} {vv bb : Nat → Bool}
      (good : ∀ i∈I,wordVal A vv bb s i=D.word s i)
      (law : ∀ b∈cube (List.range (2*m+r)),∀ x,C.eval
        (CircuitFlatten.bits n x++CircuitFlatten.bits n (packed e s b))=
        (OrthogonalCount.dot (List.range n) x (packed e s b) ^^
         (toBit (h s) ^^ parity (fun i=>wordVal A vv bb s i && (b (left i)&&b (right i))) I))) :
      1-fieldScore e A h C s=0 := by
    apply err_zero
    apply exactly_fits D C s
    intro b hb x hx
    rw [fieldPacked,law b hb x]
    unfold tailPhase
    rw [hD]
    congr 2
    exact parity_congr (fun i hi=>by rw [good i hi])
  refine ⟨?_,?_,?_⟩
  · let R := full T
    obtain ⟨C,reads,lg,fee,yes,off⟩ := yield_recipe e A h E.toList T Te none R v b0
    have ww : R.domain.length=2*m+r+d := by
      simpa [List.length_append] using R.width
    refine ⟨C,⟨⟨reads,lg⟩,by rw [fee,ww,price_eq]⟩,?_⟩
    intro s hs
    exact covered_zero (known s hs) (yes s (by simpa using hs) (by simp))
  · intro u hu
    have two : 2 ≤ E.toList.length := by simp; omega
    obtain ⟨R⟩ := remove List.nodup_range (Finset.nodup_toList _) two T u (by simpa using hu)
    obtain ⟨C,reads,lg,fee,yes,off⟩ := yield_recipe e A h E.toList T Te (some u) R v b0
    have ww : R.domain.length=2*m+r+d-1 := by
      simpa [List.length_append] using R.width
    refine ⟨C,⟨⟨reads,lg⟩,?_⟩,?_⟩
    · rw [fee,ww,price_eq]
      change (2*m+r+d-1)+I.countP v  ≤  2*m+r+d+I.countP v-1
      have hd : 0 < d := dpos
      omega
    · intro s hs
      by_cases isu : s=u
      · subst s
        rw [if_pos rfl,regime]
        obtain ⟨pr,pp,sp,miss,sem⟩ := off u rfl
        have hit := dropped_point D C u pr pp sp
          (fun b hb=>by simpa [fieldPacked u b] using miss b hb)
          (fun x b=>by simpa [fieldPacked u b] using sem x b)
        have q : (2:ℝ)*((actualLeaf D C).errors u:ℝ)=(actualLeaf D C).mass := by exact_mod_cast hit
        rw [q,div_self (by exact_mod_cast Nat.ne_of_gt (pos C))]
      · rw [if_neg isu]
        exact covered_zero (known s hs) (yes s (by simpa using hs) (by simpa [eq_comm] using isu))
  · intro j bit var
    have word_agree (s : Vec k) : D.word s j.val = wordBit A j s := wD s j
    have jI : j.val ∈ I := List.mem_range.mpr j.isLt
    have jVar : v j=true := by
      apply (FieldProfiles.varies_project E D.word j.val).mpr
      rcases var with ⟨s,hs,t,ht,ne⟩
      refine ⟨s,hs,t,ht,?_⟩
      change D.word s j.val ≠ D.word t j.val
      rwa [word_agree s,word_agree t]
    let vv : Nat → Bool := fun i=>if i=j.val then false else v i
    let bb : Nat → Bool := fun i=>if i=j.val then bit else b0 i
    let R := full T
    obtain ⟨C,reads,lg,fee,yes,off⟩ := yield_recipe e A h E.toList T Te none R vv bb
    have ww : R.domain.length=2*m+r+d := by simpa [List.length_append] using R.width
    have cv : I.countP vv+1=I.countP v := count_drop List.nodup_range v jI jVar
    refine ⟨C,⟨⟨reads,lg⟩,?_⟩,?_⟩
    · rw [fee,ww,price_eq]
      change 2*m+r+d+I.countP vv  ≤  2*m+r+d+I.countP v-1
      omega
    · intro s hs
      have this (i : Nat) (hi : i∈I) :
          wordVal A vv bb s i=(if i=j.val then bit else D.word s i) := by
        have h : i<m := List.mem_range.mp hi
        by_cases ne : i=j.val
        · simp [wordVal,h,vv,bb,ne]
        · have kk := known s hs i hi
          simpa [wordVal,vv,bb,h,ne] using kk
      have hz (b : Assign) (hb : b∈cube (List.range (2*m+r))) (x : Assign) :
          actualError D C s x b=
            ((bit ^^ D.word s j.val) && (b (left j.val)&&b (right j.val))) := by
        have tr := yes s (by simpa using hs) (by simp) b hb x
        unfold actualError tailPhase
        rw [fieldPacked,tr,hD]
        have phase :
            (parity (fun i=>wordVal A vv bb s i && (b (left i)&&b (right i))) I ^^
              parity (fun i=>D.word s i && (b (left i)&&b (right i))) I)=
              ((bit ^^ D.word s j.val) && (b (left j.val)&&b (right j.val))) := by
          rw [←parity_xor]
          rw [parity_single (I:=I) (i:=j.val) List.nodup_range jI]
          · rw [this j.val jI,if_pos rfl,Bool.and_xor_distrib_right]
          · intro i hi ne
            rw [this i hi,if_neg ne,Bool.xor_self]
        rw [cancel_common_prefix]
        exact phase
      by_cases issue : wordBit A j s≠bit
      · rw [if_pos issue,regime]
        have flag : (bit ^^ D.word s j.val)=true :=
          xor_neq.mpr (by rw [word_agree s]; exact Ne.symm issue)
        have hm := frozen_column D C s j.isLt (fun b hb x _=>by simpa [flag] using hz b hb x)
        have mm : (4:ℝ)*((actualLeaf D C).errors s:ℝ)=(actualLeaf D C).mass := by exact_mod_cast hm
        apply (div_eq_iff (by exact_mod_cast Nat.ne_of_gt (pos C))).mpr
        linarith
      · rw [if_neg issue]
        apply err_zero
        have same : wordBit A j s=bit := Classical.byContradiction issue
        have flag : (bit ^^ D.word s j.val)=false := by rw [word_agree s,same,Bool.xor_self]
        unfold actualLeaf
        have q := count_aligned (List.range n) (List.range (2*m+r)) (actualError D C s)
          (fun _=>false) (fun b hb x _=>by simpa [flag] using hz b hb x)
        simpa using q

end PEqualNP.Outside.L_meta_32580.FieldOptions

/- Source segment: MainFacade. -/

                                                     

namespace PEqualNP.Outside.L_meta_32580.MainFacade
open scoped BigOperators
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32580.ZMod2Bridge PEqualNP.Outside.L_meta_32580.ExactInput PEqualNP.Outside.L_meta_32580.ExactScore
open PEqualNP.Outside.L_meta_32580.FieldOptions PEqualNP.Outside.L_meta_32580.ExactDefinitions PEqualNP.Outside.L_meta_32580.ProjectLower

noncomputable def fieldOption {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (A : Fin m → Vec k)
    (μ : Vec k → ℝ) (v : ℝ) : Prop :=
  (∃ u∈E,v=μ u) ∨ ∃ (i : Fin m) (b : F), (∃ s∈E,dotProduct (A i) s≠dotProduct (A i) a) ∧
    v=(∑ s∈E,if dotProduct (A i) s≠b then μ s else 0)/2

def fieldIsolate {k m : Nat} (E : Finset (Vec k)) (A : Fin m → Vec k) (u : Vec k) : Prop :=
  ∃ (i : Fin m) (b : F),∀ s∈E,dotProduct (A i) s≠b ↔ s=u

noncomputable def fieldFeasible {n k m r : Nat} (e : Wiring n k m r)
    (A : Fin m → Vec k) (h : Vec k → F) (E : Finset (Vec k)) (p : Nat) (v : ℝ) : Prop :=
  ∃ N : Nat,∃ C : Fin N → Circuit,∃ w : Fin N → ℝ,
    (∀ j,fits n p (C j) ∧ 0 ≤ w j) ∧ (∑ j,w j)=1 ∧
      ∀ s∈E,v ≤ ∑ j,w j*fieldScore e A h (C j) s

theorem variation_eq {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (A : Fin m → Vec k) (i : Fin m) :
    PEqualNP.Outside.L_meta_32580.Profile.varies E (wordBit A) i ↔ ∃ s∈E,dotProduct (A i) s≠dotProduct (A i) a := by
  constructor
  · rintro ⟨s,hs,t,ht,ne⟩
    by_cases he : dotProduct (A i) s=dotProduct (A i) a
    · exact ⟨t,ht,fun ee=>ne (congrArg toBit (he.trans ee.symm))⟩
    · exact ⟨s,hs,he⟩
  · rintro ⟨s,hs,ne⟩
    exact ⟨s,hs,a,ha,fun e=>ne (bit_injective e)⟩

theorem bit_not_iff {x b : F} : toBit x≠toBit b ↔ x≠b :=
  ⟨fun h e=>h (congrArg toBit e),fun h e=>h (bit_injective e)⟩

theorem isolate_exact {k m : Nat} (E : Finset (Vec k)) (A : Fin m → Vec k) (u : Vec k) :
    PEqualNP.Outside.L_meta_32580.Profile.isolates E (wordBit A) u ↔ fieldIsolate E A u := by
  constructor
  · rintro ⟨i,b,h⟩
    refine ⟨i,ofBit b,?_⟩
    intro s hs
    simpa only [wordBit,←bit_not_iff,to_of] using h s hs
  · rintro ⟨i,b,h⟩
    refine ⟨i,toBit b,?_⟩
    intro s hs
    simpa only [wordBit,bit_not_iff] using h s hs

theorem option_exact {k m : Nat} (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (A : Fin m → Vec k) (μ : Vec k → ℝ) (v : ℝ) :
    PEqualNP.Outside.L_meta_32580.Profile.OptionValue E (wordBit A) μ v ↔ fieldOption E a A μ v := by
  classical
  constructor
  · rintro (⟨s,hs,e⟩|⟨i,b,var,e⟩)
    · exact .inl ⟨s,hs,e⟩
    · right
      refine ⟨i,ofBit b,(variation_eq E a ha A i).mp var,?_⟩
      apply e.trans
      unfold PEqualNP.Outside.L_meta_32580.Profile.column
      apply congrArg (fun x : ℝ=>x/2)
      apply Finset.sum_congr rfl
      intro t ht
      have h : (wordBit A i t≠b) ↔ dotProduct (A i) t≠ofBit b := by
        change (toBit (dotProduct (A i) t)≠b) ↔ _
        rw [←bit_not_iff,to_of]
      by_cases hh : wordBit A i t≠b
      · rw [if_pos hh,if_pos (h.mp hh)]
      · rw [if_neg hh,if_neg (fun no=>hh (h.mpr no))]
  · rintro (⟨s,hs,e⟩|⟨i,b,var,e⟩)
    · exact .inl ⟨s,hs,e⟩
    · right
      refine ⟨i,toBit b,(variation_eq E a ha A i).mpr var,?_⟩
      simpa only [PEqualNP.Outside.L_meta_32580.Profile.column,wordBit,bit_not_iff] using e

theorem feasible_exact {n k m r : Nat} (e : Wiring n k m r)
    (A : Fin m → Vec k) (h : Vec k → F) (E : Finset (Vec k)) (p : Nat) (v : ℝ) :
    ExactGame.feasible E (fits n) (fun C s=>1-fieldScore e A h C s) p v ↔
      fieldFeasible e A h E p v := by
  unfold ExactGame.feasible fieldFeasible
  simp only [sub_sub_cancel]

theorem facade {n k m r : Nat} (e : Wiring n k m r) (A : Fin m → Vec k) (h : Vec k → F)
    (E : Finset (Vec k)) (a : Vec k) (ha : a∈E)
    (dpos : 0<Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k)))))
    (hcard : E.card=Module.finrank F (Submodule.span F (Set.image (fun s=>s-a) (↑E : Set (Vec k))))+1) :
    (∀ p, (∃ C : Circuit,fits n p C ∧ ∀ s∈E,fieldScore e A h C s=1) ↔ price r A E a ≤ p) ∧
    (∀ μ : Vec k → ℝ, (∀ s∈E,0 ≤ μ s) → 
      ∃ v : ℝ,fieldOption E a A μ v ∧
        (∀ w,fieldOption E a A μ w → v ≤ w) ∧
        (∀ C : Circuit,fits n (price r A E a-1) C → v ≤ ∑ s∈E,μ s*(1-fieldScore e A h C s)) ∧
        ∃ C : Circuit,fits n (price r A E a-1) C ∧
          (∑ s∈E,μ s*(1-fieldScore e A h C s))=v) ∧
    (∀ b,fieldFeasible e A h E (price r A E a-1) b → b ≤ 1-1/(2*(E.card:ℝ))) ∧
    ((fieldFeasible e A h E (price r A E a-1) (1-1/(2*(E.card:ℝ)))) ↔
      ∀ u∈E,fieldIsolate E A u) := by
  classical
  let P := price r A E a
  let err := fun (C : Circuit) s=>1-fieldScore e A h C s
  have e2 : 2 ≤ E.card := by omega
  have pos : 0<P := by dsimp [P,price]; omega
  have mono : ∀ {p q C},p ≤ q → fits n p C → fits n q C := by
    intro p q C small law
    exact ⟨law.1,Nat.le_trans law.2 small⟩
  have upper := projected_options e A h E a ha dpos hcard
  have lower : ∀ C,fits n (P-1) C → ExactGame.packet E (wordBit A) (err C) := by
    intro C law
    exact project_packet e A h E a ha hcard C law.1.2 (by
      have le := law.2
      change _ ≤ P-1 at le
      change _<P
      omega)
  refine ⟨?_,?_,?_,?_⟩
  · intro p
    have z (C : Circuit) (s : Vec k) : err C s=0 ↔ fieldScore e A h C s=1 := by
      change 1-fieldScore e A h C s=0 ↔ fieldScore e A h C s=1
      rw [sub_eq_zero,eq_comm]
    have perfect := ExactGame.perfect_iff (p:=p) e2 upper mono lower
    constructor
    · rintro ⟨C,legal,score⟩
      exact perfect.mp ⟨C,legal,fun s hs=>(z C s).mpr (score s hs)⟩
    · intro cap
      obtain ⟨C,legal,zero⟩ := perfect.mpr cap
      exact ⟨C,legal,fun s hs=>(z C s).mp (zero s hs)⟩
  · intro μ μ0
    obtain ⟨v,hv,low,lc,C,cfits,eval⟩ := ExactGame.weighted e2 upper lower μ μ0
    refine ⟨v,(option_exact E a ha A μ v).mp hv,?_ ,lc,C,cfits,eval⟩
    intro w hw
    exact low w ((option_exact E a ha A μ w).mpr hw)
  · intro b hb
    exact ExactGame.feasible_bound e2 lower b ((feasible_exact e A h E _ _).mpr hb)
  · constructor
    · intro feasible u hu
      exact (isolate_exact E A u).mp (ExactGame.feasible_isolates e2 lower
        ((feasible_exact e A h E _ _).mpr feasible) u hu)
    · intro demand
      exact (feasible_exact e A h E _ _).mp (ExactGame.isolates_feasible e2 upper
        (fun u hu=>(isolate_exact E A u).mpr (demand u hu)))

end PEqualNP.Outside.L_meta_32580.MainFacade

theorem PEqualNP.Outside.L_meta_32580 :
∀ k m r : ℕ,
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
    let word := fun (s : S) (i : Fin m) => dotProduct (A i) s
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, ∑ c : D, ∑ z : Z,
        let y := e.symm (s,(b,(c,z)))
        let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
        if C.eval (bits n x ++ bits n y) = decide (v = 1) then (1 : ℝ) else -1) / 2^(n+base)
    let fits := fun (p : ℕ) (C : Circ) => legal (2*n) C ∧ cost C ≤ p
    ∀ (E : Finset S) (a : S), a ∈ E →
      let W := Submodule.span F (Set.image (fun s : S => s-a) (↑E : Set S))
      let d := Module.finrank F W
      let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∃ s ∈ E, word s i ≠ word a i)).card
      let price := base+d+varying
      let isolate := fun (u : S) => ∃ (i : Fin m) (v : F),
        ∀ s ∈ E, (word s i ≠ v ↔ s = u)
      let feasible := fun (p : ℕ) (b : ℝ) =>
        ∃ (N : ℕ) (C : Fin N → Circ) (w : Fin N → ℝ),
          (∀ i, fits p (C i) ∧ 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
          ∀ s ∈ E, b ≤ ∑ i, w i * score (C i) s
      0 < d → E.card = d+1 →
        (∀ p : ℕ, (∃ C : Circ, fits p C ∧ ∀ s ∈ E, score C s = 1) ↔ price ≤ p) ∧
        (∀ μ : S → ℝ, (∀ s ∈ E, 0 ≤ μ s) →
          let option := fun (v : ℝ) => (∃ u ∈ E, v = μ u) ∨
            ∃ (i : Fin m) (b : F), (∃ u ∈ E, word u i ≠ word a i) ∧
              v = (∑ s ∈ E, if word s i ≠ b then μ s else 0) / 2
          let loss := fun (C : Circ) => ∑ s ∈ E, μ s * (1-score C s)
          ∃ v : ℝ, option v ∧ (∀ w : ℝ, option w → v ≤ w) ∧
            (∀ C : Circ, fits (price-1) C → v ≤ loss C) ∧
            ∃ C : Circ, fits (price-1) C ∧ loss C = v) ∧
        (∀ b : ℝ, feasible (price-1) b → b ≤ 1-1/(2*(E.card : ℝ))) ∧
        (feasible (price-1) (1-1/(2*(E.card : ℝ))) ↔ ∀ u ∈ E, isolate u) := by
  intro k m r
  try dsimp only
  intro e A h
  try dsimp only
  intro E a ha
  try dsimp only
  intro hd hcard
  exact PEqualNP.Outside.L_meta_32580.MainFacade.facade e A h E a ha hd hcard
