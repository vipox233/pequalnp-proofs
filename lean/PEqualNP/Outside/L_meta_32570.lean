import PEqualNP.Defs

open scoped BigOperators

/- 
Two-bank parity-tree price.
The history-cell construction is adapted from the L-meta-32058 proof.
The finite binary coefficient method uses ideas from the L-meta-29946 proof.
-/








namespace PEqualNP.Outside.L_meta_32570_aux.Credited32058
abbrev H := List Bool

def cut (b : Bool) : List H → List H
  | [] => []
  | []::ns => cut b ns
  | (a::p)::ns => if a=b then p::cut b ns else cut b ns

theorem mem_cut (b : Bool) (p : H) (ns : List H) :
    p∈cut b ns ↔ (b::p)∈ns := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil => simp [cut,ih]
    | cons a h =>
      by_cases eq : a=b
      · subst a; simp [cut,ih]
      · have ne : b≠a := Ne.symm eq
        simp [cut,eq,ne,ih]

theorem cut_budget (ns : List H) :
    (cut false ns).length+(cut true ns).length+(if []∈ns then 1 else 0) ≤ ns.length := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil =>
      simp only [cut,List.mem_cons,true_or,ite_true,List.length_cons]
      have h := Nat.le_add_right ((cut false ns).length+(cut true ns).length)
        (if []∈ns then 1 else 0)
      omega
    | cons a h =>
      cases a <;> simp [cut] at ih ⊢ <;> omega

def leaves (ns : List H) : Nat → List H
  | 0 => [[]]
  | d+1 => if []∈ns then
      (leaves (cut false ns) d).map (false::·) ++
      (leaves (cut true ns) d).map (true::·)
    else [[]]

theorem leaf_budget (d : Nat) (ns : List H) : (leaves ns d).length ≤ ns.length+1 := by
  induction d generalizing ns with
  | zero => simp [leaves]
  | succ d ih =>
    by_cases h : []∈ns
    · have l := ih (cut false ns)
      have r := ih (cut true ns)
      have b := cut_budget ns
      simp only [h,ite_true] at b
      simp only [leaves,h,ite_true,List.length_append,List.length_map]
      omega
    · simp [leaves,h]

def advance (ns : List H) (answer : H → Bool) (p : H) : H :=
  if p∈ns then p++[answer p] else p

def follow (ns : List H) (answer : H → Bool) : Nat → H → H
  | 0,p => p
  | d+1,p => follow ns answer d (advance ns answer p)

theorem no_node (ns : List H) (Q : H → Bool) (d : Nat) (p : H)
    (h : p∉ns) : follow ns Q d p=p := by
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
    by_cases h : []∈ns
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
        if p∈ns then p++[Q p] else p) [] ∈ ls := by
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
    by_cases h : p∈ns
    · refine ⟨Q p::r,?_⟩
      simpa only [follow,advance,h,ite_true,List.append_assoc,List.cons_append,List.nil_append] using hr
    · refine ⟨r,?_⟩
      simpa only [follow,advance,h,ite_false] using hr

theorem reachable_leaf_cell (ns : List H) (Q : H → Bool) (d : Nat) (p : H) :
    ∃ checks : List (H × Bool), ∀ R : H → Bool,
      follow ns R d p = follow ns Q d p ↔ ∀ z∈checks, R z.1=z.2 := by
  induction d generalizing p with
  | zero => exact ⟨[],fun _ => by simp [follow]⟩
  | succ d ih =>
    by_cases h : p∈ns
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

end PEqualNP.Outside.L_meta_32570_aux.Credited32058



namespace PEqualNP.Outside.L_meta_32570_aux.Credited32058.Fixed
open PEqualNP.Outside.L_meta_32570_aux.Credited32058

def nodes : Nat → List H
  | 0 => []
  | d+1 => [] :: (nodes d).map (false::·) ++ (nodes d).map (true::·)

theorem membership (d : Nat) (p : H) : p∈nodes d ↔ p.length<d := by
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

theorem depth_le (d : Nat) : d≤(nodes d).length := by
  induction d with
  | zero => simp
  | succ d ih => simp only [nodes,List.length_cons,List.length_append,List.length_map];omega

theorem final_length (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H)
    (hp : p.length≤d) :
    (follow (nodes d) (fun a=>A a.length) fuel p).length =
      min d (p.length+fuel) := by
  induction fuel generalizing p with
  | zero => simp [follow,Nat.min_eq_right hp]
  | succ fuel ih =>
    by_cases e : p.length<d
    · have he := (membership d p).mpr e
      simp only [follow,advance,he,ite_true]
      rw [ih (p++[A p.length]) (by simp;omega)]
      simp only [List.length_append,List.length_cons,List.length_nil]
      congr 1
      omega
    · have he : p∉nodes d := fun h=>(Nat.not_lt.mpr (Nat.le_of_not_gt e)) ((membership d p).mp h)
      rw [no_node _ _ _ _ he,Nat.min_eq_left (by omega)]
      omega

theorem answer_get (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H)
    (j : Nat) (hj : p.length≤j)
    (hr : j < (follow (nodes d) (fun a=>A a.length) fuel p).length) :
    (follow (nodes d) (fun a=>A a.length) fuel p)[j]=A j := by
  induction fuel generalizing p with
  | zero =>
    change j<p.length at hr
    omega
  | succ fuel ih =>
    by_cases e : p∈nodes d
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

theorem fixed_history (d : Nat) (A : Nat → Bool) (fuel : Nat) (hf : d≤fuel) :
    let p := (List.range fuel).foldl (fun p _ =>
      if p∈nodes d then p++[A p.length] else p) []
    p.length=d ∧ ∀ j : Nat, j<d → p[j]?=some (A j) := by
  dsimp only
  have e := fold_follow (nodes d) (fun a=>A a.length) (List.range fuel) []
  have len : (follow (nodes d) (fun a=>A a.length) fuel []).length=d := by
    rw [final_length _ _ _ _ (by simp),List.length_nil,Nat.zero_add,Nat.min_eq_left hf]
  simp only [List.length_range] at e
  refine ⟨e ▸ len,?_⟩
  intro j hj
  change ((List.range fuel).foldl (fun q _ => advance (nodes d) (fun a=>A a.length) q) [])[j]? = _
  rw [e,List.getElem?_eq_getElem (by omega),answer_get d A fuel [] j (by simp) (by omega)]

end PEqualNP.Outside.L_meta_32570_aux.Credited32058.Fixed



namespace PEqualNP.Outside.L_meta_32570_aux

def bit (a : Bool) : Nat := if a then 1 else 0
def prodErr (a b residual : Bool) : Bool := (a && b) ^^ residual
def xor4 (a b c d : Bool) : Bool := ((a ^^ b) ^^ c) ^^ d


theorem quadratic_square (a b c l m : Bool) :
    xor4 (prodErr a b c) (prodErr (!a) b (c ^^ l))
      (prodErr a (!b) (c ^^ m))
      (prodErr (!a) (!b) ((c ^^ l) ^^ m)) = true := by
  cases a <;> cases b <;> cases c <;> cases l <;> cases m <;> rfl

theorem one_of_xor4 (a b c d : Bool) (h : xor4 a b c d = true) :
    1 ≤ bit a + bit b + bit c + bit d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [xor4, bit] at h ⊢


theorem shift_product (a b a₀ b₀ : Bool) :
    ((a ^^ a₀) && (b ^^ b₀)) =
      (((a && b) ^^ (a && b₀)) ^^ (a₀ && b)) ^^ (a₀ && b₀) := by
  cases a <;> cases b <;> cases a₀ <;> cases b₀ <;> rfl



theorem clean_product (a b : Bool) (pick : Fin 3)
    (h : (if pick.val=0 then a else if pick.val=1 then b else a ^^ b)=false) :
    (a && b) = (if pick.val=2 then a else false) := by
  have q : pick.val=0 ∨ pick.val=1 ∨ pick.val=2 := by have := pick.isLt; omega
  rcases q with q | q | q <;> cases a <;> cases b <;> simp_all

def sumOn {α : Type u} (f : α → Nat) : List α → Nat
  | [] => 0
  | a::as => f a + sumOn f as

@[simp] theorem sumOn_nil {α} (f : α → Nat) : sumOn f []=0 := rfl
@[simp] theorem sumOn_cons {α} (f : α → Nat) (a : α) (xs : List α) :
  sumOn f (a::xs)=f a+sumOn f xs := rfl

theorem sumOn_const {α} (xs : List α) (c : Nat) :
    sumOn (fun _ => c) xs = c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_succ,Nat.add_comm]

theorem sumOn_add {α} (xs : List α) (f g : α → Nat) :
    sumOn (fun x => f x + g x) xs = sumOn f xs + sumOn g xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem sumOn_mul {α} (xs : List α) (f : α → Nat) (c : Nat) :
    sumOn (fun x => c * f x) xs = c * sumOn f xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]

theorem sumOn_le {α} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : sumOn f xs ≤ sumOn g xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [sumOn_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem sumOn_map {α β} (xs : List α) (t : α → β) (f : β → Nat) :
    sumOn f (xs.map t) = sumOn (fun x => f (t x)) xs := by
  induction xs <;> simp_all

theorem sumOn_perm {α} {xs ys : List α} (h : List.Perm xs ys) (f : α → Nat) :
    sumOn f xs = sumOn f ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y xs => simp; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem sumOn_bits {α} (xs : List α) (f : α → Bool) :
    sumOn (fun x => bit (f x)) xs = (xs.filter f).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [sumOn_cons,ih]
    cases h : f x <;> simp [h,bit,Nat.add_comm]



theorem quarter {α} (xs : List α) (err : α → Bool) (t u v : α → α)
    (ht : List.Perm (xs.map t) xs) (hu : List.Perm (xs.map u) xs)
    (hv : List.Perm (xs.map v) xs)
    (quad : ∀ x ∈ xs, xor4 (err x) (err (t x)) (err (u x)) (err (v x)) = true) :
    xs.length ≤ 4 * sumOn (fun x => bit (err x)) xs := by
  let e := fun x => bit (err x)
  have le := sumOn_le xs (fun _ => 1)
      (fun x => e x + e (t x) + e (u x) + e (v x))
      (fun x hx => one_of_xor4 _ _ _ _ (quad x hx))
  have ht' := sumOn_perm ht e
  have hu' := sumOn_perm hu e
  have hv' := sumOn_perm hv e
  rw [sumOn_map] at ht' hu' hv'
  rw [sumOn_const, Nat.one_mul, sumOn_add, sumOn_add, sumOn_add] at le
  have first : sumOn (fun x => e (t x)) xs = sumOn e xs := ht'
  have second : sumOn (fun x => e (u x)) xs = sumOn e xs := hu'
  have third : sumOn (fun x => e (v x)) xs = sumOn e xs := hv'
  change xs.length ≤ 4 * sumOn e xs
  omega

theorem sumOn_flip {α β} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOn (fun x => sumOn (f x) ys) xs =
    sumOn (fun y => sumOn (fun x => f x y) xs) ys := by
  induction xs with
  | nil => simp [sumOn_const]
  | cons x xs ih =>
    simp only [sumOn_cons,ih,sumOn_add]


theorem exception_bound {α β} (xs : List α) (ys : List β) (err : α → β → Bool)
    (bad : β → Bool) (e : Nat) (hx : 0 < xs.length)
    (perPoint : ∀ x ∈ xs, (ys.filter (err x)).length ≤ e)
    (exception : ∀ y ∈ ys, bad y = true →
      xs.length ≤ 4 * sumOn (fun x => bit (err x y)) xs) :
    (ys.filter bad).length ≤ 4*e := by
  have left := sumOn_le ys (fun y => xs.length * bit (bad y))
    (fun y => 4 * sumOn (fun x => bit (err x y)) xs) (by
      intro y hy
      cases h : bad y
      · simp [bit]
      · simpa [bit,h] using exception y hy h)
  have right := sumOn_le xs (fun x => sumOn (fun y => bit (err x y)) ys)
      (fun _ => e) (fun x h => by simpa [sumOn_bits] using perPoint x h)
  rw [sumOn_mul,sumOn_bits,sumOn_mul,←sumOn_flip] at left
  rw [sumOn_const] at right
  have q := Nat.le_trans left (Nat.mul_le_mul_left 4 right)
  have q' : (ys.filter bad).length * xs.length ≤ (4*e) * xs.length := by
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using q
  exact Nat.le_of_mul_le_mul_right q' hx

end PEqualNP.Outside.L_meta_32570_aux



namespace PEqualNP.Outside.L_meta_32570_aux.Boundary

def ix (k : Nat) (h : 0<k) (n : Nat) : Fin k :=
  ⟨n % k,Nat.mod_lt _ h⟩

def repeatWindow {α} {k : Nat} (h : 0<k) (x : Fin k → α) (i : Fin (k+6)) : α :=
  x (ix k h i.val)

def head {α} {k : Nat} (x : Fin (k+6) → α) (i : Fin k) : α :=
  x ⟨i.val,by have := i.isLt; omega⟩

def agrees {α} {k : Nat} (x : Fin (k+6) → α) : Prop :=
  ∀ i : Fin 6, x ⟨i.val,by have := i.isLt; omega⟩ =
    x ⟨k+i.val,by have := i.isLt; omega⟩

theorem repeat_agrees {α} {k : Nat} (h : 0<k) (x : Fin k → α) :
    agrees (repeatWindow h x) := by
  intro i
  simp [repeatWindow,ix,Nat.add_mod_left]

theorem head_repeat {α} {k : Nat} (h : 0<k) (x : Fin k → α) :
    head (repeatWindow h x)=x := by
  funext i
  simp [head,repeatWindow,ix,Nat.mod_eq_of_lt i.isLt]

theorem agrees_periodic {α} {k : Nat} (h : 0<k) (x : Fin (k+6) → α)
    (hs : agrees x) : repeatWindow h (head x)=x := by
  have recur : ∀ n (hn : n<k+6),
      x ⟨n,hn⟩ = x ⟨n%k,by have := Nat.mod_lt n h; omega⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases lt : n<k
      · simp [Nat.mod_eq_of_lt lt]
      · let i := n-k
        have hi : i<6 := by dsimp [i]; omega
        have eq : k+i=n := by dsimp [i]; omega
        have il : i<n := by dsimp [i]; omega
        have ag := hs ⟨i,hi⟩
        change x ⟨i,by omega⟩=x ⟨k+i,by omega⟩ at ag
        have knot : (⟨k+i,by omega⟩ : Fin (k+6))=⟨n,hn⟩ := Fin.ext eq
        rw [knot] at ag
        rw [← ag,ih i il (by omega)]
        congr 1
        apply Fin.ext
        change i%k=n%k
        rw [←eq,Nat.add_mod_left]
  funext i
  exact (recur i.val i.isLt).symm



theorem unique_window {α} {k : Nat} (h : 0 < k) (x : Fin k → α) :
    ∃ y : Fin (k+6) → α, agrees y ∧ head y=x ∧
       (∀ z : Fin (k+6) → α, agrees z → head z=x → z=y) := by
  refine ⟨repeatWindow h x,repeat_agrees h x,head_repeat h x,?_⟩
  intro y hp hx
  rw [←hx,agrees_periodic h y hp]

end PEqualNP.Outside.L_meta_32570_aux.Boundary



namespace PEqualNP.Outside.L_meta_32570_aux.Operands




def idx (k : Nat) (hk : 0<k) (i : Nat) : Fin k := ⟨i%k,Nat.mod_lt _ hk⟩

theorem mod_left (a b k : Nat) : (a%k+b)%k=(a+b)%k := by
  rw [Nat.add_mod (a%k) b k,Nat.mod_mod]
  exact (Nat.add_mod a b k).symm

theorem at_add (k : Nat) (hk : 0<k) (a b : Nat) :
    idx k hk ((idx k hk a).val+b)=idx k hk (a+b) :=
  Fin.ext (mod_left a b k)

theorem back_after {k : Nat} (hk : 0<k) (i d : Nat) :
    idx k hk ((idx k hk (i+d)).val+k-d%k)=idx k hk i := by
  apply Fin.ext
  change (((i+d)%k+k-d%k)%k) = i%k
  rw [Nat.add_mod_eq_sub (a:=i) (b:=d)]
  have hi := Nat.mod_lt i hk
  have hd := Nat.mod_lt d hk
  split
  · rw [show i%k+d%k-0+k-d%k=i%k+k by omega,Nat.add_mod_right,Nat.mod_mod]
  · rw [show i%k+d%k-k+k-d%k=i%k by omega,Nat.mod_mod]

theorem back_at {k : Nat} (hk : 0<k) (i d : Nat) (h : d ≤ i) :
    idx k hk ((idx k hk i).val+k-d%k)=idx k hk (i-d) := by
  have eq : i-d+d=i := by omega
  simpa only [eq] using back_after hk (i-d) d

def rot {k : Nat} (hk : 0<k) (s : Nat) (x : Fin k→Bool) (i : Fin k) : Bool :=
  x (idx k hk (i.val+k-s%k))

def mix {k : Nat} (hk : 0<k) (g : Nat) (x : Fin k→Bool) (i : Fin k) : Bool :=
  (x i ^^ x (idx k hk (i.val+g))) ^^ x (idx k hk (i.val+k-g%k))

theorem rot_at {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i s : Nat) (h : s ≤ i) :
    rot hk s x (idx k hk i)=x (idx k hk (i-s)) := by
  rw [rot,back_at hk i s h]

theorem unwrapped {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i g s : Nat)
    (h : g+s ≤ i) :
    mix hk g (rot hk s x) (idx k hk i)=
      ((x (idx k hk (i-s)) ^^ x (idx k hk (i+g-s))) ^^ x (idx k hk (i-g-s))) := by
  rw [mix,at_add,back_at hk i g (by omega),rot_at hk x i s (by omega),
    rot_at hk x (i+g) s (by omega),rot_at hk x (i-g) s (by omega)]

def site {k : Nat} (hk : 0<k) (i : Nat) : Fin k := idx k hk (i+4)
def op {k : Nat} (hk : 0<k) (bank second : Bool) (x : Fin k→Bool) (i : Nat) : Bool :=
  mix hk (if bank then 2 else 1) (rot hk (if bank then 3 else 1) x)
    (idx k hk ((site hk i).val + if second then 2 else 1))

theorem perm3 (a b c : Bool) : ((a ^^ b) ^^ c) = ((c ^^ a) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem first_false {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i : Nat) :
    op hk false false x i =
      ((x (idx k hk (i+3)) ^^ x (idx k hk (i+4))) ^^ x (idx k hk (i+5))) := by
  change mix hk 1 (rot hk 1 x) (idx k hk ((idx k hk (i+4)).val+1))=_
  rw [at_add,unwrapped hk x _ 1 1 (by omega)]
  have a : i+4+1-1=i+4 := by omega
  have b : i+4+1+1-1=i+5 := by omega
  have c : i+4+1-1-1=i+3 := by omega
  rw [c,a,b,perm3]

theorem second_false {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i : Nat) :
    op hk false true x i =
      ((x (idx k hk (i+4)) ^^ x (idx k hk (i+5))) ^^ x (idx k hk (i+6))) := by
  change mix hk 1 (rot hk 1 x) (idx k hk ((idx k hk (i+4)).val+2))=_
  rw [at_add,unwrapped hk x _ 1 1 (by omega)]
  have a : i+4+2-1=i+5 := by omega
  have b : i+4+2+1-1=i+6 := by omega
  have c : i+4+2-1-1=i+4 := by omega
  rw [c,a,b,perm3]

theorem first_true {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i : Nat) :
    op hk true false x i =
      ((x (idx k hk i) ^^ x (idx k hk (i+2))) ^^ x (idx k hk (i+4))) := by
  change mix hk 2 (rot hk 3 x) (idx k hk ((idx k hk (i+4)).val+1))=_
  rw [at_add,unwrapped hk x _ 2 3 (by omega)]
  have a : i+4+1-3=i+2 := by omega
  have b : i+4+1+2-3=i+4 := by omega
  have c : i+4+1-2-3=i := by omega
  rw [c,a,b,perm3]

theorem second_true {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i : Nat) :
    op hk true true x i =
      ((x (idx k hk (i+1)) ^^ x (idx k hk (i+3))) ^^ x (idx k hk (i+5))) := by
  change mix hk 2 (rot hk 3 x) (idx k hk ((idx k hk (i+4)).val+2))=_
  rw [at_add,unwrapped hk x _ 2 3 (by omega)]
  have a : i+4+2-3=i+3 := by omega
  have b : i+4+2+2-3=i+5 := by omega
  have c : i+4+2-2-3=i+1 := by omega
  rw [c,a,b,perm3]

def mask (b second : Bool) : Nat :=
  if b then (if second then 42 else 21) else (if second then 112 else 56)

def localDot (m : Nat) (r : Nat → Bool) : Bool :=
  (List.range 7).foldl (fun b j=> b ^^ (m.testBit j && r j)) false

theorem operand_mask {k : Nat} (hk : 0<k) (x : Fin k→Bool) (i : Nat) (b second : Bool) :
    op hk b second x i = localDot (mask b second) (fun j=>x (idx k hk (i+j))) := by
  have ls : List.range 7=[0,1,2,3,4,5,6] := rfl
  cases b <;> cases second
  · rw [first_false]; simp [localDot,ls,mask,Nat.testBit]
  · rw [second_false]; simp [localDot,ls,mask,Nat.testBit]
  · rw [first_true]; simp [localDot,ls,mask,Nat.testBit]
  · rw [second_true]; simp [localDot,ls,mask,Nat.testBit]

end PEqualNP.Outside.L_meta_32570_aux.Operands



namespace PEqualNP.Outside.L_meta_32570_aux.Zipper


def shift (n : Nat) : Nat := n%64 + 128*(n/64)

theorem shift_low (n j : Nat) (h : j<6) :
    (shift n).testBit j = n.testBit j := by
  have hn : n%64 < 2^7 := by have := Nat.mod_lt n (by decide : 0<64); omega
  unfold shift
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add (n/64) hn]
  change (if j<7 then (n % 2^6).testBit j else (n/64).testBit (j-7)) = _
  rw [ite_eq_left (by omega),Nat.testBit_mod_two_pow]
  simp [h]

theorem shift_gap (n : Nat) : (shift n).testBit 6 = false := by
  have hn : n%64 < 2^7 := by have := Nat.mod_lt n (by decide : 0<64); omega
  unfold shift
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add (n/64) hn]
  exact Nat.testBit_lt_two_pow (show n%64<2^6 from Nat.mod_lt n (by decide))

theorem shift_high (n j : Nat) (h : 6≤j) :
    (shift n).testBit (j+1) = n.testBit j := by
  have hn : n%64 < 2^7 := by have := Nat.mod_lt n (by decide : 0<64); omega
  unfold shift
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add (n/64) hn]
  rw [ite_eq_right (by omega : ¬ j+1<7)]
  change (n/2^6).testBit (j+1-7) = n.testBit j
  rw [Nat.testBit_div_two_pow,show j+1-7+6=j by omega]

theorem shift_inj {a b : Nat} (h : shift a=shift b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases low : j<6
  · rw [←shift_low a j low,←shift_low b j low,h]
  · rw [←shift_high a j (by omega),←shift_high b j (by omega),h]

theorem shift_xor (a b : Nat) : shift (a ^^^ b) = shift a ^^^ shift b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  by_cases low : j<6
  · rw [shift_low _ _ low,shift_low a _ low,shift_low b _ low,Nat.testBit_xor]
  · by_cases gap : j=6
    · subst j; simp [shift_gap]
    · have tj : j-1+1=j := by omega
      rw [←tj,shift_high _ _ (by omega),shift_high a _ (by omega),shift_high b _ (by omega),
        Nat.testBit_xor]

theorem tail_bit (n j : Nat) : (n/2).testBit j = n.testBit (j+1) :=
  Nat.testBit_div_two n j

theorem seed_paired (v j : Nat) (hv : v<64) (hj : j<6) :
    (v+64*v).testBit j = v.testBit j ∧
    (v+64*v).testBit (j+6) = v.testBit j := by
  rw [Nat.add_comm]
  have low := Nat.testBit_two_pow_mul_add v (i:=6) hv j
  have high := Nat.testBit_two_pow_mul_add v (i:=6) hv (j+6)
  constructor
  · simpa [hj] using low
  · rwa [ite_eq_right (by omega),Nat.add_sub_cancel] at high

theorem seed_extent (v : Nat) (hv : v<64) : v+64*v < 2^12 := by omega

theorem operand_packed (m j : Nat) (hm : m<128) (hi : 7≤j) :
    m + 2^j = m ^^^ 2^j := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hmp : m<2^j :=
    Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0<2) hi)
  have e := Nat.testBit_two_pow_mul_add 1 hmp n
  rw [Nat.mul_one] at e
  rw [Nat.add_comm,e,Nat.testBit_xor]
  by_cases low : n<j
  · simp [low,Nat.testBit_two_pow_of_ne (by omega : j≠n)]
  · have hm' : m<2^n :=
      Nat.lt_of_lt_of_le hmp (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
    rw [ite_eq_right low,Nat.testBit_lt_two_pow hm',Bool.false_xor]
    change (2^0).testBit (n-j) = (2^j).testBit n
    rw [Nat.testBit_two_pow,Nat.testBit_two_pow]
    simp only [decide_eq_decide]
    omega

theorem check_low (n j : Nat) (h : j<12) : (4096*n).testBit j=false := by
  change (2^12*n).testBit j=false
  rw [Nat.testBit_two_pow_mul]
  simp [show ¬ 12≤j by omega]

theorem check_high (n j : Nat) : (4096*n).testBit (12+j)=n.testBit j := by
  change (2^12*n).testBit (12+j)=n.testBit j
  rw [Nat.testBit_two_pow_mul]
  simp [show 12+j-12=j by omega]

def Even (v : Nat) : Prop := v%2=0
instance (v) : Decidable (Even v) := inferInstanceAs (Decidable (v%2=0))
def Adjoin (H : Nat → Prop) (r v : Nat) : Prop := H v ∨ H (v ^^^ r)
def evenPart (H : Nat → Prop) (v : Nat) : Prop := H v ∧ Even v

theorem xor_cancel (v r : Nat) : (v ^^^ r) ^^^ r = v := by
  rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem adjoin_image (H : Nat → Prop) (r v : Nat) :
    Adjoin H r v ↔ H v ∨ ∃ u, H u ∧ u ^^^ r=v := by
  constructor
  · rintro (h|h)
    · exact .inl h
    · exact .inr ⟨v^^^r,h,xor_cancel v r⟩
  · rintro (h|⟨u,h,rfl⟩)
    · exact .inl h
    · exact .inr (by simpa only [xor_cancel] using h)

theorem even_xor_iff (v r : Nat) (hr : Even r) :
    Even (v ^^^ r) ↔ Even v := by
  unfold Even at *
  rw [Nat.mod_two_eq_zero_iff_testBit_zero,Nat.testBit_xor,
    Nat.mod_two_eq_zero_iff_testBit_zero.mp hr,Bool.xor_false]
  exact Nat.mod_two_eq_zero_iff_testBit_zero.symm



theorem even_adjoin (H : Nat → Prop) (r v : Nat) (hr : Even r) :
    evenPart (Adjoin H r) v ↔ Adjoin (evenPart H) r v := by
  change ((H v ∨ H (v^^^r)) ∧ Even v) ↔
    ((H v ∧ Even v) ∨ (H (v^^^r) ∧ Even (v^^^r)))
  rw [even_xor_iff v r hr]
  constructor
  · rintro ⟨q,h⟩
    rcases q with q|q
    · exact .inl ⟨q,h⟩
    · exact .inr ⟨q,h⟩
  · rintro (⟨q,h⟩|⟨q,h⟩)
    · exact ⟨.inl q,h⟩
    · exact ⟨.inr q,h⟩

theorem tail_inj_on_even {a b : Nat} (ha : Even a) (hb : Even b)
    (e : a/2=b/2) : a=b := by
  have ma := Nat.mod_add_div a 2
  have mb := Nat.mod_add_div b 2
  unfold Even at ha hb
  omega

def evens (rs : List Nat) : List Nat := rs.filter (fun x => !x.testBit 0)
def odds (rs : List Nat) : List Nat := rs.filter (fun x => x.testBit 0)
def survivor (rs : List Nat) : List Nat := (evens rs).map (fun x=>x/2)

theorem mem_evens {x : Nat} {rs : List Nat} :
    x∈evens rs ↔ x∈rs ∧ x.testBit 0=false := by simp [evens]
theorem mem_odds {x : Nat} {rs : List Nat} :
    x∈odds rs ↔ x∈rs ∧ x.testBit 0=true := by simp [odds]

theorem evens_literal (rs : List Nat) :
    evens rs = rs.filter (fun x => decide (x%2=0)) := by
  apply congrArg (fun p : Nat→Bool => rs.filter p)
  funext x
  cases e : x.testBit 0
  · change true = decide (x%2=0)
    exact (decide_eq_true (Nat.mod_two_eq_zero_iff_testBit_zero.mpr e)).symm
  · have m : x%2≠0 := fun z =>
      Bool.noConfusion (e.symm.trans (Nat.mod_two_eq_zero_iff_testBit_zero.mp z))
    change false = decide (x%2=0)
    exact (decide_eq_false m).symm

theorem parity_count (rs : List Nat) : (evens rs).length+(odds rs).length=rs.length := by
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    simp only [evens,odds] at ih ⊢
    cases z : x.testBit 0 <;>
      simp only [List.filter_cons,z,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        ite_false,ite_true,List.length_cons] <;> omega

theorem rotate_zero {p x : Nat} (hp : p.testBit 0=true) :
    (x ^^^ p).testBit 0 = !x.testBit 0 := by
  rw [Nat.testBit_xor,hp]; cases x.testBit 0 <;> rfl

theorem count_even_odd (rs : List Nat) (nd : rs.Nodup)
    (closed : ∀ a ∈ rs, ∀ b ∈ rs, a ^^^ b ∈ rs)
    (p : Nat) (pm : p∈rs) (po : p.testBit 0=true) :
    (evens rs).length=(odds rs).length := by
  have toggle : ∀ x, (x ^^^ p) ^^^ p = x := fun x => xor_cancel x p
  have inj : ∀ a b : Nat, a ^^^ p=b ^^^ p → a=b := by
    intro a b h
    simpa only [toggle] using congrArg (fun q => q^^^p) h
  have en : (evens rs).Nodup := List.filter_sublist.nodup nd
  have on : (odds rs).Nodup := List.filter_sublist.nodup nd
  have left : ((evens rs).map (fun x=>x^^^p)).Nodup :=
    List.Nodup.map (fun a b h => inj a b h) en
  have right : ((odds rs).map (fun x=>x^^^p)).Nodup :=
    List.Nodup.map (fun a b h => inj a b h) on
  have h₁ := left.length_le_of_subset (l₂:=odds rs) (by
    intro y ym
    obtain ⟨x,xm,rfl⟩ := List.mem_map.mp ym
    obtain ⟨a,b⟩ := mem_evens.mp xm
    exact mem_odds.mpr ⟨closed x a p pm,by simp [rotate_zero po,b]⟩)
  have h₂ := right.length_le_of_subset (l₂:=evens rs) (by
    intro y ym
    obtain ⟨x,xm,rfl⟩ := List.mem_map.mp ym
    obtain ⟨a,b⟩ := mem_odds.mp xm
    exact mem_evens.mpr ⟨closed x a p pm,by simp [rotate_zero po,b]⟩)
  simp only [List.length_map] at h₁ h₂
  omega

theorem even_filter_all (rs : List Nat) (h : ∀ a ∈ rs, a.testBit 0=false) :
    evens rs=rs := by
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    have hx := h x (by simp)
    simp only [evens,List.filter_cons,hx,Bool.not_false,ite_true]
    have q := ih (fun a m=>h a (by simp [m]))
    change x::evens rs=x::rs
    rw [q]



theorem cardinal_step (rs : List Nat) (nd : rs.Nodup)
    (closed : ∀ a ∈ rs, ∀ b ∈ rs, a ^^^ b ∈ rs) :
    rs.length = (if evens rs=rs then 1 else 2) * (survivor rs).length := by
  have l := parity_count rs
  by_cases h : ∃ p ∈ rs, p.testBit 0=true
  · obtain ⟨p,pm,po⟩ := h
    have equal := count_even_odd rs nd closed p pm po
    have pm' := (mem_odds (rs:=rs)).mpr ⟨pm,po⟩
    have nz : 0 < (odds rs).length := by
      cases z : odds rs with
      | nil => rw [z] at pm'; simp at pm'
      | cons => simp
    have ne : evens rs≠rs := by
      intro e; have ll := congrArg List.length e; omega
    simp only [survivor,List.length_map,ite_eq_right ne]
    omega
  · have eq := even_filter_all rs (fun a am => by
      cases ha : a.testBit 0
      · rfl
      · exact False.elim (h ⟨a,am,ha⟩))
    simp [eq,survivor]

end PEqualNP.Outside.L_meta_32570_aux.Zipper



namespace PEqualNP.Outside.L_meta_32570_aux.Projection

def adjoin (H : Nat → Prop) (r n : Nat) : Prop := H n ∨ H (n ^^^ r)
def project (t : Nat) (H : Nat → Prop) (n : Nat) : Prop :=
  ∃ x, H x ∧ x%2^t=0 ∧ x/2^t=n

theorem unxor (x r : Nat) : (x ^^^ r) ^^^ r=x := by
  rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem project_zero (H : Nat→Prop) (n : Nat) : project 0 H n ↔ H n := by
  simp [project,Nat.mod_one]



theorem project_adjoin (t : Nat) (H : Nat → Prop) (r n : Nat)
    (hr : r%2^t=0) :
    project t (adjoin H r) n ↔ adjoin (project t H) (r/2^t) n := by
  constructor
  · rintro ⟨x,m,zero,val⟩
    rcases m with m | m
    · exact .inl ⟨x,m,zero,val⟩
    · exact .inr ⟨x^^^r,m,
        by rw [Nat.xor_mod_two_pow,zero,hr,Nat.xor_zero],
        by rw [Nat.xor_div_two_pow,val]⟩
  · rintro (⟨x,m,zero,val⟩|⟨x,m,zero,val⟩)
    · exact ⟨x,.inl m,zero,val⟩
    · exact ⟨x^^^r,.inr (by rwa [unxor]),
        by rw [Nat.xor_mod_two_pow,zero,hr,Nat.xor_zero],
        by rw [Nat.xor_div_two_pow,val,unxor]⟩

theorem split_zero (x t : Nat) :
    x%2^(t+1)=0 ↔ x%2^t=0 ∧ x/2^t%2=0 := by
  rw [Nat.pow_succ,Nat.mod_mul]
  constructor
  · intro h
    obtain ⟨left,right⟩ := Nat.add_eq_zero_iff.mp h
    exact ⟨left, (Nat.mul_eq_zero.mp right).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos t))⟩
  · rintro ⟨h,r⟩; rw [h,r,Nat.mul_zero,Nat.zero_add]

theorem project_succ (t : Nat) (H : Nat → Prop) (n : Nat) :
    project (t+1) H n ↔ project 1 (project t H) n := by
  have pow : (2 : Nat)^t * 2^1 = 2^(t+1) := (Nat.pow_add 2 t 1).symm
  constructor
  · rintro ⟨x,h,z,e⟩
    obtain ⟨a,b⟩ := (split_zero x t).mp z
    refine ⟨x/2^t,⟨x,h,a,rfl⟩,b,?_⟩
    rwa [Nat.div_div_eq_div_mul,pow]
  · rintro ⟨_,⟨x,h,a,rfl⟩,b,e⟩
    exact ⟨x,h,(split_zero x t).mpr ⟨a,b⟩,
      by simpa only [Nat.div_div_eq_div_mul,pow] using e⟩



def pack (lo width n : Nat) : Nat := n%2^lo + 2^width * (n/2^lo)

theorem nested_mod (n a b : Nat) (h : a≤b) :
    n%2^b%2^a=n%2^a := by
  have e : b=a+(b-a) := by omega
  calc
    n%2^b%2^a = n%(2^a*2^(b-a))%2^a := by rw [←Nat.pow_add,←e]
    _ = n%2^a := Nat.mod_mul_right_mod n _ _

theorem pack_low (lo width n i : Nat) (h : i<lo) (hw : lo≤width) :
    (pack lo width n).testBit i=n.testBit i := by
  have hb : n%2^lo < 2^width := Nat.lt_of_lt_of_le
      (Nat.mod_lt _ (Nat.two_pow_pos lo)) (Nat.pow_le_pow_right (by decide : 0<2) hw)
  unfold pack
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ hb,ite_eq_left (by omega),Nat.testBit_mod_two_pow]
  simp [h]

theorem pack_gap (lo width n i : Nat) (hl : lo ≤ i) (hi : i<width) :
    (pack lo width n).testBit i=false := by
  have hb : n%2^lo < 2^width := Nat.lt_of_lt_of_le
      (Nat.mod_lt _ (Nat.two_pow_pos lo)) (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  unfold pack
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ hb,ite_eq_left hi,Nat.testBit_mod_two_pow]
  simp [show ¬ i<lo by omega]

theorem pack_high (lo width n i : Nat) (h : lo≤width) :
    (pack lo width n).testBit (width+i)=n.testBit (lo+i) := by
  have hb : n%2^lo < 2^width := Nat.lt_of_lt_of_le
      (Nat.mod_lt _ (Nat.two_pow_pos lo)) (Nat.pow_le_pow_right (by decide : 0<2) h)
  unfold pack
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ hb,ite_eq_right (by omega),
    show width+i-width=i by omega,Nat.testBit_div_two_pow,Nat.add_comm i lo]

theorem pack_inj (lo width : Nat) (h : lo≤width) {a b : Nat}
    (hs : pack lo width a=pack lo width b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases low : i<lo
  · rw [←pack_low lo width a i low h,←pack_low lo width b i low h,hs]
  · have eq : lo+(i-lo)=i := by omega
    rw [←eq,←pack_high lo width a _ h, ←pack_high lo width b _ h,hs]

theorem pack_xor (lo width a b : Nat) (h : lo≤width) :
    pack lo width (a^^^b) = pack lo width a ^^^ pack lo width b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  by_cases low : i<lo
  · rw [pack_low _ _ _ _ low h,pack_low _ _ a _ low h,pack_low _ _ b _ low h,
      Nat.testBit_xor]
  · by_cases gap : i<width
    · rw [pack_gap _ _ _ _ (by omega) gap,pack_gap _ _ a _ (by omega) gap,
        pack_gap _ _ b _ (by omega) gap,Bool.xor_false]
    · have eq : width+(i-width)=i := by omega
      rw [←eq,pack_high _ _ _ _ h,pack_high _ _ a _ h,pack_high _ _ b _ h,
        Nat.testBit_xor]



theorem pack_drop (lo width n : Nat) :
    pack (lo+1) (width+1) n / 2 = pack lo width (n/2) := by
  have a : n%2^(lo+1)/2=n/2%2^lo := by
    rw [Nat.pow_succ]
    exact Nat.mod_mul_left_div_self n 2 (2^lo)
  have b : n/2/2^lo=n/2^(lo+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm 2 (2^lo),←Nat.pow_succ]
  unfold pack
  rw [b, Nat.pow_succ (m:=width)]
  have e : 2^width*2*(n/2^(lo+1)) = 2*(2^width*(n/2^(lo+1))) := by
    rw [Nat.mul_comm (2^width) 2,Nat.mul_assoc]
  rw [e,Nat.add_comm (n%2^(lo+1)),Nat.mul_add_div (by decide : 0<2),a,Nat.add_comm]


theorem pack_widen (width n : Nat) :
    pack 7 width (n%64+128*(n/64)) = pack 6 width n := by
  have h : n%64<128 := by have := Nat.mod_lt n (by decide : 0<64); omega
  unfold pack
  change (n%64+128*(n/64))%128+2^width*((n%64+128*(n/64))/128)
    = n%64+2^width*(n/64)
  have d : (n%64+128*(n/64))/128=n/64 := by
    rw [Nat.add_comm,Nat.mul_add_div (by decide : 0<128),Nat.div_eq_of_lt h,Nat.add_zero]
  rw [d,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h]

end PEqualNP.Outside.L_meta_32570_aux.Projection





namespace PEqualNP.Outside.L_meta_32570_aux.RankStream
open PEqualNP.Outside.L_meta_32570_aux.Zipper

structure Rows where
  data : List Nat
  nd : data.Nodup
  zero : 0 ∈ data
  closed : ∀ a ∈ data, ∀ b ∈ data, a ^^^ b ∈ data

def Same (A B : Rows) : Prop := ∀ x, x∈A.data ↔ x∈B.data

theorem same_length {A B : Rows} (h : Same A B) : A.data.length=B.data.length := by
  have a := A.nd.length_le_of_subset (l₂:=B.data) fun _ ax=> (h _).mp ax
  have b := B.nd.length_le_of_subset (l₂:=A.data) fun _ bx=> (h _).mpr bx
  omega

theorem unxor2 (x y r : Nat) :
    (x^^^r)^^^(y^^^r) = x^^^y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases r.testBit i <;> rfl

theorem add_mixed (x y r : Nat) : (x^^^y)^^^r=x^^^(y^^^r) :=
  Nat.xor_assoc x y r

theorem adj_xor (H : Rows) (r a b : Nat)
    (ha : Adjoin (·∈H.data) r a) (hb : Adjoin (·∈H.data) r b) :
    Adjoin (·∈H.data) r (a^^^b) := by
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact .inl (H.closed a ha b hb)
  · exact .inr (by rw [add_mixed]; exact H.closed a ha _ hb)
  · apply Or.inr
    have e : (a^^^b)^^^r=(a^^^r)^^^b := by
      rw [Nat.xor_assoc,Nat.xor_assoc a r b,Nat.xor_comm b r]
    rw [e]
    exact H.closed _ ha b hb
  · exact .inl (by rw [←unxor2 a b r]; exact H.closed _ ha _ hb)

def add (H : Rows) (r : Nat) : Rows :=
  if hr : r∈H.data then H else
    let d := H.data ++ H.data.map (fun x=>x^^^r)
    have member (x : Nat) : x∈d ↔ Adjoin (·∈H.data) r x := by
      simp only [d,List.mem_append,List.mem_map]
      exact (adjoin_image _ _ _).symm
    ⟨d,by
      refine List.nodup_append.mpr ⟨H.nd,
        List.Nodup.map (fun _ _ e => by simpa only [xor_cancel] using congrArg (fun q=>q^^^r) e) H.nd,?_⟩
      intro a ha b hb e
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
      have g := H.closed a ha y hy
      have neq : a^^^y=r := by
        rw [e,Nat.xor_comm y r,xor_cancel]
      exact hr (neq ▸ g),
      (member 0).mpr (.inl H.zero),
      fun a ha b hb => (member _).mpr (adj_xor H r _ _ ((member _).mp ha) ((member _).mp hb))⟩

theorem mem_add (H : Rows) (r x : Nat) :
    x∈(add H r).data ↔ Adjoin (·∈H.data) r x := by
  unfold add
  split
  · rename_i hr
    constructor
    · exact Or.inl
    · rintro (a|a)
      · exact a
      · have k := H.closed _ a r hr
        rwa [xor_cancel] at k
  · simp only [List.mem_append,List.mem_map]
    exact (adjoin_image _ _ _).symm

def addRows (H : Rows) (rs : List Nat) : Rows := rs.foldl add H

theorem addRows_append (H : Rows) (xs ys : List Nat) :
    addRows H (xs++ys)=addRows (addRows H xs) ys := by
  simp [addRows,List.foldl_append]

theorem add_same {H G : Rows} (h : Same H G) (r : Nat) : Same (add H r) (add G r) := by
  intro x
  rw [mem_add,mem_add]
  exact or_congr (h _) (h _)

theorem map_nodup_on {α β : Type} {L : List α} {f : α→β} (nd : L.Nodup)
    (inj : ∀ a∈L, ∀ b∈L, f a=f b → a=b) : (L.map f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simp only [List.getElem_map] at eq
  exact (List.nodup_iff_eq_of_getElem_eq.mp nd) _ _ _ _
    (inj _ (List.getElem_mem _) _ (List.getElem_mem _) eq)

def tail (H : Rows) : Rows where
  data := survivor H.data
  nd := map_nodup_on (List.filter_sublist.nodup H.nd) (fun _ ha _ hb e=>
      tail_inj_on_even
        (Nat.mod_two_eq_zero_iff_testBit_zero.mpr (mem_evens.mp ha).2)
        (Nat.mod_two_eq_zero_iff_testBit_zero.mpr (mem_evens.mp hb).2) e)
  zero := by
    apply List.mem_map.mpr
    exact ⟨0,mem_evens.mpr ⟨H.zero,rfl⟩,rfl⟩
  closed := by
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    obtain ⟨hx,x0⟩ := mem_evens.mp hx
    obtain ⟨hy,y0⟩ := mem_evens.mp hy
    exact List.mem_map.mpr ⟨x^^^y,mem_evens.mpr
      ⟨H.closed x hx y hy,by rw [Nat.testBit_xor,x0,y0]; rfl⟩,Nat.xor_div_two⟩

theorem mem_tail (H : Rows) (x : Nat) :
    x∈(tail H).data ↔ PEqualNP.Outside.L_meta_32570_aux.Projection.project 1 (·∈H.data) x := by
  change x ∈ (evens H.data).map (fun n=>n/2) ↔ _
  simp only [List.mem_map,mem_evens,Projection.project]
  constructor
  · rintro ⟨y,⟨hy,ye⟩,rfl⟩
    exact ⟨y,hy,Nat.mod_two_eq_zero_iff_testBit_zero.mpr ye,rfl⟩
  · rintro ⟨y,hy,ye,rfl⟩
    exact ⟨y,⟨hy,Nat.mod_two_eq_zero_iff_testBit_zero.mp ye⟩,rfl⟩

def lifted (r : Nat) : Nat := 2*r

theorem lift_even (r : Nat) : lifted r%2=0 := by simp [lifted]
theorem lift_div (r : Nat) : lifted r/2=r := by unfold lifted; omega

theorem tail_add_lift (H : Rows) (r : Nat) :
    Same (tail (add H (lifted r))) (add (tail H) r) := by
  intro x
  have h := Projection.project_adjoin 1 (·∈H.data) (lifted r) x (lift_even r)
  change (Projection.project 1 (fun v => v∈H.data ∨ v^^^lifted r∈H.data) x ↔
    Projection.project 1 (·∈H.data) x ∨
      Projection.project 1 (·∈H.data) (x^^^(lifted r/2^1))) at h
  rw [show lifted r/2^1=r from lift_div r] at h
  simpa only [mem_tail,mem_add,Adjoin] using h

theorem addRows_same (ls : List Nat) {X Y : Rows} (h : Same X Y) :
    Same (addRows X ls) (addRows Y ls) := by
  induction ls generalizing X Y with
  | nil => exact h
  | cons z zs ind =>
    change Same (addRows (add X z) zs) (addRows (add Y z) zs)
    apply ind
    exact add_same h z

theorem tail_addRows_lift (H : Rows) (ls : List Nat) :
    Same (tail (addRows H (ls.map lifted))) (addRows (tail H) ls) := by
  induction ls generalizing H with
  | nil => exact fun _=>Iff.rfl
  | cons a ls ih =>
    change Same (tail (addRows (add H (lifted a)) (ls.map lifted)))
      (addRows (add (tail H) a) ls)
    have c := tail_add_lift H a
    exact fun n=>(ih _ n).trans (addRows_same ls c n)

def HasOdd (H : Rows) : Prop := ∃ a∈H.data, a.testBit 0=true
instance (H : Rows) : Decidable (HasOdd H) :=
  inferInstanceAs (Decidable (∃ a∈H.data, a.testBit 0=true))
def charge (H : Rows) : Nat := if HasOdd H then 1 else 0

theorem charge_eq (H : Rows) : charge H = (if evens H.data=H.data then 0 else 1) := by
  by_cases h : HasOdd H
  · obtain ⟨p,hp,odd⟩ := h
    have ng : evens H.data≠H.data := by
      intro e
      have m : p∈evens H.data := e.symm ▸ hp
      have m0 := (mem_evens.mp m).2
      rw [odd] at m0
      contradiction
    have h' : HasOdd H := ⟨p,hp,odd⟩
    simp [charge,h',ng]
  · have e := even_filter_all H.data (fun n nm=>by
      cases q : n.testBit 0
      · rfl
      · exact False.elim (h ⟨n,nm,q⟩))
    simp [charge,e,h]

theorem old_hasOdd (H : Rows) (r : Nat) :
    HasOdd (add H (lifted r)) ↔ HasOdd H := by
  constructor
  · rintro ⟨x,hx,odd⟩
    rcases (mem_add _ _ _).mp hx with p | p
    · exact ⟨x,p,odd⟩
    · exact ⟨x^^^lifted r,p,by
        rw [Nat.testBit_xor,Nat.mod_two_eq_zero_iff_testBit_zero.mp (lift_even r),
          Bool.xor_false,odd]⟩
  · rintro ⟨x,m,b⟩
    exact ⟨x,(mem_add _ _ _).mpr (.inl m),b⟩

theorem old_many (H : Rows) (rs : List Nat) :
    HasOdd (addRows H (rs.map lifted)) ↔ HasOdd H := by
  induction rs generalizing H with
  | nil => rfl
  | cons r rs ih => exact (ih (add H (lifted r))).trans (old_hasOdd H r)

theorem splitCard (H : Rows) : H.data.length = (2^charge H)*(tail H).data.length := by
  have c := cardinal_step H.data H.nd H.closed
  by_cases eq : evens H.data=H.data
  · simpa [charge_eq,eq,tail] using c
  · simpa [charge_eq,eq,tail] using c



inductive Schedule
  | close : List Nat → Schedule
  | emit : List Nat → Schedule → Schedule

def expanded : Schedule → List Nat
  | .close final => final
  | .emit now next => now ++ (expanded next).map lifted

def execute : Schedule → Rows → Nat×Rows
  | .close final,H => (0,addRows H final)
  | .emit now next,H =>
      let current := addRows H now
      let sub := execute next (tail current)
      (charge current+sub.1,sub.2)



theorem schedule_card (sch : Schedule) (H : Rows) :
    (addRows H (expanded sch)).data.length=
      2^(execute sch H).1*(execute sch H).2.data.length := by
  induction sch generalizing H with
  | close final => simp [expanded,execute]
  | emit now next ih =>
    let current := addRows H now
    let F := addRows current ((expanded next).map lifted)
    have a := splitCard F
    have b := same_length (tail_addRows_lift current (expanded next))
    have c := ih (tail current)
    have equal : charge F=charge current := by simp only [charge,F,old_many]
    change (addRows H (now++(expanded next).map lifted)).data.length =
      2^(charge current+(execute next (tail current)).1)*(execute next (tail current)).2.data.length
    rw [addRows_append]
    change F.data.length=_
    rw [a,equal,b,c,Nat.pow_add,Nat.mul_assoc]

theorem log_mul_pow (q n : Nat) (h : n≠0) :
    (2^q*n).log2=q+n.log2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have ex : 2^(q+1)*n=2*(2^q*n) := by
      rw [Nat.pow_succ,Nat.mul_comm (2^q) 2,Nat.mul_assoc]
    rw [ex,Nat.log2_two_mul (Nat.mul_ne_zero (Nat.ne_of_gt (Nat.two_pow_pos q)) h),ih]
    omega

theorem rows_nonzero (H : Rows) : H.data.length≠0 := by
  intro g
  have nl := List.eq_nil_of_length_eq_zero g
  have z := H.zero
  rw [nl] at z
  simp at z

theorem schedule_log2 (sch : Schedule) (H : Rows) :
    (addRows H (expanded sch)).data.length.log2=
      (execute sch H).1+(execute sch H).2.data.length.log2 := by
  rw [schedule_card,log_mul_pow]
  exact rows_nonzero (execute sch H).2

end PEqualNP.Outside.L_meta_32570_aux.RankStream





namespace PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule
open PEqualNP.Outside.L_meta_32570_aux.Zipper PEqualNP.Outside.L_meta_32570_aux.Projection PEqualNP.Outside.L_meta_32570_aux.RankStream

def rowsMap (R : Rows) (f : Nat→Nat) (z : f 0=0)
    (af : ∀ x y, f (x^^^y)=f x^^^f y) (inj : ∀ x y, f x=f y→x=y) : Rows where
  data := R.data.map f
  nd := map_nodup_on R.nd (fun x _ y _ h=>inj x y h)
  zero := List.mem_map.mpr ⟨0,R.zero,z⟩
  closed := by
    intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    exact List.mem_map.mpr ⟨a^^^b,R.closed a ha b hb,af a b⟩

theorem rows_eq {R S : Rows} (a : R.data=S.data) : R=S := by
  cases R
  cases S
  cases a
  rfl

theorem rowsMap_add (R : Rows) (f : Nat→Nat) (z : f 0=0)
    (af : ∀ x y, f (x^^^y)=f x^^^f y) (inj : ∀ x y, f x=f y→x=y) (r : Nat) :
    rowsMap (add R r) f z af inj=add (rowsMap R f z af inj) (f r) := by
  apply rows_eq
  have mem : f r∈(rowsMap R f z af inj).data ↔ r∈R.data := by
    change f r ∈ R.data.map f ↔ _
    constructor
    · rintro h
      obtain ⟨x,h,e⟩ := List.mem_map.mp h
      exact inj x r e ▸ h
    · exact List.mem_map_of_mem
  by_cases h : r∈R.data
  · simp only [add,dite_eq_left h,dite_eq_left (mem.mpr h)]
  · have no : ¬ f r∈R.data.map f := fun t => h (mem.mp t)
    simp only [add,dite_eq_right h,rowsMap,dite_eq_right no,List.map_append,List.map_map,Function.comp_def,af]

theorem rowsMap_addRows (R : Rows) (f : Nat→Nat) (z : f 0=0)
    (af : ∀ x y, f (x^^^y)=f x^^^f y) (inj : ∀ x y, f x=f y→x=y) (ls : List Nat) :
    rowsMap (addRows R ls) f z af inj=addRows (rowsMap R f z af inj) (ls.map f) := by
  induction ls generalizing R with
  | nil => rfl
  | cons r ls ih =>
    change rowsMap (addRows (add R r) ls) f z af inj=
      addRows (add (rowsMap R f z af inj) (f r)) (ls.map f)
    rw [ih,rowsMap_add]

def shifted (R : Rows) : Rows := rowsMap R shift rfl shift_xor (fun _ _ h=>shift_inj h)
def widened (lo width : Nat) (h : lo≤width) (R : Rows) : Rows :=
  rowsMap R (pack lo width) (by simp [pack]) (fun x y=>pack_xor _ _ x y h)
    (fun _ _ p=>pack_inj _ _ h p)

theorem widened_end (lo : Nat) (R : Rows) : widened lo lo (Nat.le_refl lo) R=R := by
  apply rows_eq
  change R.data.map (pack lo lo)=R.data
  have e : pack lo lo = id := by
    funext x
    simpa [pack] using Nat.mod_add_div x (2^lo)
  rw [e,List.map_id]

theorem widened_shift (width : Nat) (h : 7≤width) (R : Rows) :
    widened 7 width h (shifted R)=widened 6 width (by omega) R := by
  apply rows_eq
  change (R.data.map shift).map (pack 7 width)=R.data.map (pack 6 width)
  simp only [List.map_map,Function.comp_def,shift,pack_widen]

theorem widened_addRows (lo width : Nat) (h : lo≤width) (R : Rows) (ls : List Nat) :
    widened lo width h (addRows R ls)=addRows (widened lo width h R) (ls.map (pack lo width)) :=
  rowsMap_addRows _ _ _ _ _ _

theorem widened_evens (lo width : Nat) (hl : 0<lo) (h : lo≤width) (R : Rows) :
    evens (widened lo width h R).data = (evens R.data).map (pack lo width) := by
  change (R.data.map (pack lo width)).filter (fun x=>!x.testBit 0) =
    (R.data.filter (fun x=>!x.testBit 0)).map (pack lo width)
  simp only [List.filter_map,Function.comp_def,pack_low _ _ _ _ hl h]

theorem widened_charge (lo width : Nat) (hl : 0<lo) (h : lo≤width) (R : Rows) :
    charge (widened lo width h R)=charge R := by
  suffices eq : HasOdd (widened lo width h R) ↔ HasOdd R by simp only [charge,eq]
  constructor
  · rintro ⟨x,hx,xo⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact ⟨a,ha,(pack_low _ _ _ _ hl h).symm.trans xo⟩
  · rintro ⟨a,ha,ao⟩
    exact ⟨pack lo width a,List.mem_map.mpr ⟨a,ha,rfl⟩,
      (pack_low _ _ _ _ hl h).trans ao⟩

theorem widened_tail (w : Nat) (h : 6≤w) (R : Rows) :
    tail (widened 7 (w+1) (by omega) R)=widened 6 w h (tail R) := by
  apply rows_eq
  change (evens (widened 7 (w+1) (by omega) R).data).map (fun x=>x/2)=
      ((evens R.data).map (fun x=>x/2)).map (pack 6 w)
  rw [widened_evens _ _ (by decide)]
  simp only [List.map_map,Function.comp_def,pack_drop]

def schedule (batches : List (List Nat)) (endRows : List Nat) : Schedule :=
  match batches with
  | [] => .close endRows
  | sub::rest => .emit (sub.map (pack 7 (rest.length+7))) (schedule rest endRows)

def localRun : List (List Nat) → List Nat → Rows → Nat×Rows
  | [],endRows,R => (0,addRows R endRows)
  | sub::rest,endRows,R =>
    let current := addRows (shifted R) sub
    let result := localRun rest endRows (tail current)
    (charge current+result.1,result.2)

theorem transport (batches : List (List Nat)) (fin : List Nat) (R : Rows) :
    execute (schedule batches fin) (widened 6 (batches.length+6) (by omega) R) =
      localRun batches fin R := by
  induction batches generalizing R with
  | nil =>
    change (0,addRows (widened 6 6 (by decide) R) fin)=(0,addRows R fin)
    rw [widened_end]
  | cons now rest ih =>
    let cur := addRows (shifted R) now
    have hy := widened_addRows 7 (rest.length+7) (by omega) (shifted R) now
    rw [widened_shift] at hy
    have W : 6≤rest.length+6 := by omega
    have ht := widened_tail (rest.length+6) W cur
    have hz := widened_charge 7 (rest.length+7) (by decide) (by omega) cur
    have eq : rest.length+1+6=rest.length+7 := by omega
    change execute (.emit (now.map (pack 7 (rest.length+7))) (schedule rest fin))
      (widened 6 (rest.length+1+6) (by omega) R) = _
    simp only [eq,execute,localRun]
    rw [←hy,hz,ht,ih]

theorem local_rank (batches : List (List Nat)) (fin : List Nat) (R : Rows) :
    let total := addRows (widened 6 (batches.length+6) (by omega) R)
      (expanded (schedule batches fin))
    let last := localRun batches fin R
    total.data.length.log2=last.1+last.2.data.length.log2 := by
  dsimp only
  rw [schedule_log2,transport]

def rowsZero : Rows := ⟨[0],by simp,by simp,by simp⟩
def boundaryRows : List Nat := (List.range 6).map (fun i=>2^i+2^(i+6))

theorem seed_list : (addRows rowsZero boundaryRows).data =
    (List.range 64).map (fun v=>v+64*v) := by decide

end PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule




namespace PEqualNP.Outside.L_meta_32570_aux.Generators
open PEqualNP.Outside.L_meta_32570_aux.Projection PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule PEqualNP.Outside.L_meta_32570_aux.RankStream

theorem pack_raw (lo width m : Nat) (hm : m<2^lo) :
    pack lo width m=m := by
  simp [pack,Nat.mod_eq_of_lt hm,Nat.div_eq_of_lt hm]

theorem pack_high_coeffs (lo width m v : Nat) (hm : m<2^lo) :
    pack lo width (m+2^lo*v)=m+2^width*v := by
  have hmod : (m+2^lo*v)%2^lo=m := by
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hm]
  have hdiv : (m+2^lo*v)/2^lo=v := by
    rw [Nat.add_comm,Nat.mul_add_div (Nat.two_pow_pos lo),Nat.div_eq_of_lt hm,Nat.add_zero]
  rw [pack,hmod,hdiv]

theorem start_boundary (k l : Nat) (hl : l<6) :
    pack 6 (k+6) (2^l+2^(6+l))=2^l+2^(k+6+l) := by
  rw [Nat.pow_add 2 6 l,pack_high_coeffs 6 (k+6) (2^l) (2^l)
    (Nat.pow_lt_pow_right (by decide : 1<2) hl),←Nat.pow_add]

theorem stop_boundary (k l : Nat) :
    2^k*(2^l+2^(6+l))=2^(k+l)+2^(k+6+l) := by
  rw [Nat.mul_add,←Nat.pow_add,←Nat.pow_add,Nat.add_assoc]

theorem clean_absolute (k i m : Nat) (hm : m<128) :
    2^i*pack 7 (k+6-i) m=2^i*m := by
  rw [pack_raw _ _ _ hm]

theorem operand_absolute (k i j m : Nat) (hi : i<k) (hm : m<128) :
    2^i*pack 7 (k+6-i) (m+2^(13+j)) =
      2^i*m+2^(k+12+j) := by
  have hidx : 13+j=7+(6+j) := by omega
  rw [hidx,Nat.pow_add 2 7 (6+j),pack_high_coeffs 7 (k+6-i) m (2^(6+j)) hm]
  rw [Nat.mul_add,←Nat.pow_add,←Nat.pow_add]
  have e : i+(k+6-i+(6+j))=k+12+j := by omega
  rw [e]

theorem check_absolute (k m : Nat) : 2^k*(4096*m)=2^(k+12)*m := by
  change 2^k*(2^12*m)=_
  rw [←Nat.mul_assoc,←Nat.pow_add]


theorem mem_expanded (bs : List (List Nat)) (fin : List Nat) (r : Nat) :
    r∈expanded (schedule bs fin) ↔
      (∃ (i : Nat) (hi : i<bs.length) (m : Nat), m∈bs[i] ∧ r=2^i*pack 7 (bs.length+6-i) m)
      ∨ (∃ v∈fin, r=2^bs.length*v) := by
  induction bs generalizing r with
  | nil => simp [schedule,expanded]
  | cons now rest ih =>
    constructor
    · intro h
      simp only [schedule,expanded,List.mem_append,List.mem_map] at h
      rcases h with ⟨m,hm,rfl⟩ | ⟨x,hx,rfl⟩
      · refine .inl ⟨0,by simp,m,hm,?_⟩
        simp [Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]
      · rcases (ih x).mp hx with ⟨i,hi,m,hm,rfl⟩ | ⟨v,hv,rfl⟩
        · refine .inl ⟨i+1,by simp;omega,m,hm,?_⟩
          simp only [lifted,List.length_cons,Nat.pow_succ]
          have e : rest.length+1+6-(i+1)=rest.length+6-i := by omega
          rw [e,Nat.mul_comm (2^i) 2,Nat.mul_assoc]
        · refine .inr ⟨v,hv,?_⟩
          simp only [lifted,List.length_cons,Nat.pow_succ]
          rw [Nat.mul_comm (2^rest.length) 2,Nat.mul_assoc]
    · rintro (⟨i,hi,m,hm,rfl⟩|⟨v,hv,rfl⟩)
      · cases i with
        | zero =>
          simp only [schedule,expanded,List.mem_append,List.mem_map]
          refine .inl ⟨m,hm,?_⟩
          simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
        | succ i =>
          simp only [schedule,expanded,List.mem_append,List.mem_map]
          have hi' : i<rest.length := by simp at hi; omega
          let x := 2^i*pack 7 (rest.length+6-i) m
          refine .inr ⟨x,(ih x).mpr (.inl ⟨i,hi',m,hm,rfl⟩),?_⟩
          simp only [x,lifted,List.length_cons,Nat.pow_succ]
          have e : rest.length+1+6-(i+1)=rest.length+6-i := by omega
          rw [e,Nat.mul_comm (2^i) 2,Nat.mul_assoc]
      · simp only [schedule,expanded,List.mem_append,List.mem_map]
        refine .inr ⟨2^rest.length*v,(ih _).mpr (.inr ⟨v,hv,rfl⟩),?_⟩
        simp only [lifted,List.length_cons,Nat.pow_succ]
        rw [Nat.mul_comm (2^rest.length) 2,Nat.mul_assoc]

end PEqualNP.Outside.L_meta_32570_aux.Generators




namespace PEqualNP.Outside.L_meta_32570_aux.Packing

def bit (b : Bool) : Nat := if b then 1 else 0
def encode : List Bool → Nat
  | []=>0
  | b::bs=>bit b+2*encode bs

theorem length_bound (xs : List Bool) : encode xs<2^xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    rw [encode,List.length_cons,Nat.pow_succ]
    cases b <;> simp only [bit,ite_false,ite_true,Bool.false_eq_true] <;> omega

theorem lowest (b : Bool) (n : Nat) : (bit b+2*n).testBit 0=b := by
  rw [Nat.testBit_zero,Nat.add_mul_mod_self_left]
  cases b <;> decide

theorem upper (b : Bool) (n i : Nat) :
    (bit b+2*n).testBit (i+1)=n.testBit i := by
  rw [Nat.testBit_add_one]
  have e : (bit b+2*n)/2=n := by
    cases b <;> simp only [bit,ite_false,ite_true,Bool.false_eq_true] <;> omega
  rw [e]

theorem testBit_get (xs : List Bool) (i : Nat) (h : i<xs.length) :
    (encode xs).testBit i=xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => exact lowest b (encode bs)
    | succ i =>
      rw [encode,upper]
      exact ih i (by simp at h;omega)

def toMask {n : Nat} (f : Fin n→Bool) : Fin (2^n) :=
  ⟨encode (List.ofFn f),by simpa using length_bound (List.ofFn f)⟩

theorem mask_correct {n : Nat} (f : Fin n→Bool) (i : Fin n) :
    (toMask f).val.testBit i.val=f i := by
  change (encode (List.ofFn f)).testBit i.val=f i
  rw [testBit_get _ _ (by simpa using i.isLt),List.getElem_ofFn]

end PEqualNP.Outside.L_meta_32570_aux.Packing





namespace PEqualNP.Outside.L_meta_32570_aux.Replay
open PEqualNP.Outside.L_meta_32570_aux.Zipper PEqualNP.Outside.L_meta_32570_aux.RankStream PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule

def asSet (H : Rows) : Finset Nat := H.data.toFinset

theorem card (H : Rows) : (asSet H).card=H.data.length :=
  List.toFinset_card_of_nodup H.nd

def adj (s : Finset Nat) (v : Nat) := s ∪ s.image (fun u => u ^^^ v)

theorem add_set (H : Rows) (v : Nat) : asSet (add H v)=adj (asSet H) v := by
  ext x
  simp only [asSet,List.mem_toFinset,mem_add,adj,Finset.mem_union,Finset.mem_image]
  exact adjoin_image _ _ _

theorem addRows_set (H : Rows) (ls : List Nat) :
    asSet (addRows H ls)=ls.foldl adj (asSet H) := by
  induction ls generalizing H with
  | nil => rfl
  | cons v ls ih =>
    change asSet (addRows (add H v) ls)=ls.foldl adj (adj (asSet H) v)
    rw [ih,add_set]

theorem shifted_set (H : Rows) : asSet (shifted H) = (asSet H).image shift := by
  ext x
  simp [shifted,rowsMap,asSet,List.mem_map]

def evensSet (s : Finset Nat) : Finset Nat := s.filter (fun v=>v%2=0)

theorem evens_set (H : Rows) : (evens H.data).toFinset = evensSet (asSet H) := by
  ext v
  simp [evens_literal,evensSet,asSet]

theorem tail_set (H : Rows) :
    asSet (tail H)=(evensSet (asSet H)).image (fun v=>v/2) := by
  rw [←evens_set]
  ext x
  simp [tail,survivor,asSet,List.mem_map]

theorem charge_set (H : Rows) :
    charge H=(if evensSet (asSet H)=asSet H then 0 else 1) := by
  have eq : evensSet (asSet H)=asSet H ↔ ¬HasOdd H := by
    constructor
    · rintro hf ⟨v,hv,ht⟩
      have hz : v∈evensSet (asSet H) := hf.symm ▸ (List.mem_toFinset.mpr hv)
      have h := Nat.mod_two_eq_zero_iff_testBit_zero.mp (Finset.mem_filter.mp hz).2
      exact Bool.noConfusion (ht.symm.trans h)
    · intro h
      ext x
      simp only [evensSet,asSet,Finset.mem_filter,List.mem_toFinset,and_iff_left_iff_imp]
      intro hx
      apply Nat.mod_two_eq_zero_iff_testBit_zero.mpr
      cases q : x.testBit 0
      · rfl
      · exact False.elim (h ⟨x,hx,q⟩)
  by_cases h : HasOdd H <;> simp [charge,eq,h]

def stepSet (st : Nat×Finset Nat) (ls : List Nat) : Nat×Finset Nat :=
  let shifted := st.2.image shift
  let both := ls.foldl adj shifted
  let even := evensSet both
  (st.1+(if even=both then 0 else 1),even.image (fun x=>x/2))

theorem once (n : Nat) (H : Rows) (ls : List Nat) :
    stepSet (n,asSet H) ls =
      (n+charge (addRows (shifted H) ls),asSet (tail (addRows (shifted H) ls))) := by
  simp only [stepSet]
  rw [←shifted_set,←addRows_set,charge_set,tail_set]

theorem replay (bs : List (List Nat)) (fin : List Nat) (n : Nat) (H : Rows) :
    let last := bs.foldl stepSet (n,asSet H)
    let R := localRun bs fin H
    (last.1,fin.foldl adj last.2)=(n+R.1,asSet R.2) := by
  induction bs generalizing n H with
  | nil => simp [localRun,addRows_set]
  | cons now bs ih =>
    simp only [List.foldl_cons,localRun,once]
    rw [ih]
    simp [Nat.add_assoc]

def seed := (Finset.range 64).image (fun v => v+64*v)
def seedRows : Rows := addRows rowsZero boundaryRows

theorem seed_set : asSet seedRows=seed := by
  unfold asSet seedRows
  rw [seed_list]
  ext x
  simp [seed,List.mem_map]

def joinRows (a b : Finset Nat) : Finset Nat :=
  a.biUnion (fun x=>b.image (fun y=>x^^^y))

theorem join_zero (H : Finset Nat) : joinRows H {0}=H := by
  ext x
  simp [joinRows]

theorem join_adj (H S : Finset Nat) (r : Nat) :
    joinRows H (adj S r)=adj (joinRows H S) r := by
  ext x
  simp only [joinRows,adj,Finset.mem_biUnion,Finset.mem_image,Finset.mem_union]
  constructor
  · rintro ⟨a,hm,b,hb,e⟩
    rcases hb with hb|⟨c,hc,rfl⟩
    · exact .inl ⟨a,hm,b,hb,e⟩
    · exact .inr ⟨a^^^c,⟨a,hm,c,hc,rfl⟩,by rwa [Nat.xor_assoc]⟩
  · rintro (⟨a,hm,b,hb,e⟩|⟨y,⟨a,hm,b,hb,rfl⟩,e⟩)
    · exact ⟨a,hm,b,.inl hb,e⟩
    · exact ⟨a,hm,b^^^r,.inr ⟨b,hb,rfl⟩,by rwa [←Nat.xor_assoc]⟩

theorem join_fold (H S : Finset Nat) (rows : List Nat) :
    joinRows H (rows.foldl adj S) = rows.foldl adj (joinRows H S) := by
  induction rows generalizing S with
  | nil => rfl
  | cons r rs ih => simp only [List.foldl_cons,ih,join_adj]

theorem close_seed (H : Finset Nat) : joinRows H seed = boundaryRows.foldl adj H := by
  rw [←seed_set,seedRows,addRows_set,join_fold]
  have eq : asSet rowsZero={0} := rfl
  rw [eq,join_zero]

theorem literal_core (bs : List (List Nat)) (checks : List Nat) :
    let last := bs.foldl stepSet (0,seed)
    let tail := checks.foldl adj (joinRows last.2 seed)
    let rows := boundaryRows++checks
    let global := addRows (widened 6 (bs.length+6) (by omega) seedRows)
      (expanded (schedule bs rows))
    global.data.length.log2=last.1+tail.card.log2 := by
  dsimp only
  have h := local_rank bs (boundaryRows++checks) seedRows
  dsimp only at h
  have a := replay bs (boundaryRows++checks) 0 seedRows
  dsimp only [Nat.zero_add] at a
  rw [seed_set,List.foldl_append,←close_seed] at a
  rw [h]
  have b := congrArg (fun (p : Nat×Finset Nat) => p.1+p.2.card.log2) a
  dsimp only at b
  rw [card] at b
  simpa only [Nat.zero_add] using b.symm

end PEqualNP.Outside.L_meta_32570_aux.Replay




namespace PEqualNP.Outside.L_meta_32570_aux.ExactZip
open PEqualNP.Outside.L_meta_32570_aux.Zipper PEqualNP.Outside.L_meta_32570_aux.RankStream PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule
open PEqualNP.Outside.L_meta_32570_aux.Replay

structure Pattern (k j : Nat) where
  mark : Bool→Fin k→Bool
  who : Fin j→Bool×Fin k
  pick : Fin k→Bool→Fin 3

def site {k : Nat} (hk : 0<k) (i : Fin k) : Fin k :=
  ⟨(i.val+4)%k,Nat.mod_lt _ hk⟩

def leftMask (b : Bool) : Nat := if b then 21 else 56
def rightMask (b : Bool) : Nat := if b then 42 else 112

def chosenMask (b : Bool) (p : Fin 3) : Nat :=
  if p.val=0 then leftMask b else if p.val=1 then rightMask b
  else leftMask b ^^^ rightMask b

def added {j : Nat} (b : Bool) (v : Fin j) : List Nat :=
  [leftMask b+2^(13+2*v.val),rightMask b+2^(14+2*v.val)]

def localRows {k j : Nat} (p : Pattern k j) (hk : 0<k) (i : Fin k) (b : Bool) : List Nat :=
  (if p.mark b (site hk i)=true ∧ (∀ l, p.who l ≠ (b,site hk i)) then
    [chosenMask b (p.pick i b)] else []) ++
  (List.finRange j).flatMap (fun l => if p.who l=(b,site hk i) then added b l else [])

def batches {k j : Nat} (p : Pattern k j) (hk : 0<k) : List (List Nat) :=
  (List.finRange k).map (fun i=>localRows p hk i false ++ localRows p hk i true)

def put {k j : Nat} (p : Pattern k j) (hk : 0<k) (st : Finset Nat)
    (i : Fin k) (colSide : Bool) : Finset Nat :=
  let site := site hk i
  let u : Nat := if colSide then 21 else 56
  let v : Nat := if colSide then 42 else 112
  let clean := if p.mark colSide site = true ∧ (∀ l, p.who l ≠ (colSide,site))
    then adj st (if (p.pick i colSide).val = 0 then u
      else if (p.pick i colSide).val = 1 then v else u ^^^ v) else st
  (List.finRange j).foldl (fun span l => if p.who l = (colSide,site) then
    adj (adj span (u + 2^(13+2*l.val))) (v + 2^(14+2*l.val))
    else span) clean

theorem put_is_fold {k j : Nat} (p : Pattern k j) (hk : 0<k) (st : Finset Nat)
    (i : Fin k) (b : Bool) :
    put p hk st i b = (localRows p hk i b).foldl adj st := by
  unfold put localRows
  simp only [List.foldl_append,List.foldl_flatMap]
  have c : ((if p.mark b (site hk i)=true ∧ (∀ l, p.who l ≠ (b,site hk i)) then
      [chosenMask b (p.pick i b)] else []).foldl adj st) =
    (if p.mark b (site hk i)=true ∧ (∀ l, p.who l ≠ (b,site hk i)) then
      adj st (chosenMask b (p.pick i b)) else st) := by
    split <;> rfl
  rw [c]
  unfold chosenMask leftMask rightMask
  congr 1
  funext span l
  by_cases q : p.who l=(b,site hk i) <;>
    simp [q,added,leftMask,rightMask]

def last {k j : Nat} (p : Pattern k j) (hk : 0<k) : Nat×Finset Nat :=
  (List.finRange k).foldl (fun (st : Nat × Finset Nat) i =>
    let shifted := st.2.image (fun v => v % 64 + 128*(v / 64))
    let both := put p hk (put p hk shifted i false) i true
    let even := both.filter (fun v => v % 2 = 0)
    (st.1 + (if even = both then 0 else 1), even.image (fun v => v / 2))) ((0,seed) : Nat × Finset Nat)

theorem last_is_fold {k j : Nat} (p : Pattern k j) (hk : 0<k) :
    last p hk = (batches p hk).foldl stepSet (0,seed) := by
  unfold last batches
  rw [List.foldl_map]
  congr 1
  funext st i
  simp only [stepSet,evensSet,put_is_fold,List.foldl_append]
  rfl

noncomputable def codes {j : Nat} (checks : Finset (Fin (2^(2*j)))) : List Nat :=
  checks.toList.map (fun mask => 4096*mask.val)

noncomputable def finalSpan {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : Finset Nat :=
  let closed := (last p hk).2.biUnion (fun v => seed.image (fun u => v ^^^ u))
  checks.toList.foldl (fun st mask => adj st (4096*mask.val)) closed

noncomputable def globalRows {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : Rows :=
  let bs := batches p hk
  let extra := boundaryRows++codes checks
  addRows (widened 6 (bs.length+6) (by omega) seedRows)
    (expanded (schedule bs extra))

theorem global_price {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) :
    (globalRows p hk checks).data.length.log2 =
      (last p hk).1 + (finalSpan p hk checks).card.log2 := by
  have th := literal_core (batches p hk) (codes checks)
  dsimp only at th
  change (globalRows p hk checks).data.length.log2 = _ at th
  rw [←last_is_fold] at th
  simpa only [finalSpan,codes,List.foldl_map,joinRows,Function.comp_def] using th

end PEqualNP.Outside.L_meta_32570_aux.ExactZip






namespace PEqualNP.Outside.L_meta_32570_aux.Authentic

abbrev F := ZMod 2
abbrev Dual (V : Type*) [AddCommGroup V] [Module F V] := V →ₗ[F] F

def toBit (a : F) : Bool := decide (a≠0)

theorem values (a : F) : a=0 ∨ a=1 := by
  change Fin 2 at a
  obtain ⟨n,hn⟩ := a
  have h : n=0 ∨ n=1 := by omega
  rcases h with h|h
  · exact .inl (Fin.ext h)
  · exact .inr (Fin.ext h)
@[simp] theorem bit_zero : toBit (0:F)=false := by decide
@[simp] theorem bit_one : toBit (1:F)=true := by decide
@[simp] theorem one_plus_one : (1:F)+1=0 := by decide

theorem bit_add (a b : F) : toBit (a+b)=(toBit a ^^ toBit b) := by
  rcases values a with rfl|rfl <;> rcases values b with rfl|rfl <;> decide
theorem bit_mul (a b : F) : toBit (a*b)=(toBit a && toBit b) := by
  rcases values a with rfl|rfl <;> rcases values b with rfl|rfl <;> decide

theorem bit_eq_true (a : F) : toBit a=true ↔ a≠0 := by simp [toBit]

theorem list_card_toList {X : Type*} (m : Finset X) (p : X→Bool) :
    (m.toList.filter p).length=(m.filter (fun u=>p u=true)).card := by
  classical
  have rep : (m.toList.filter p).toFinset = m.filter (fun u=>p u=true) := by
    ext u
    simp
  have nd : (m.toList.filter p).Nodup := List.filter_sublist.nodup m.nodup_toList
  rw [←List.toFinset_card_of_nodup nd,rep]

section

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem some_one (a : Dual V) (h : a≠0) : ∃ x, a x=1 := by
  by_contra z
  apply h
  ext x
  rcases values (a x) with h | h
  · simpa using h
  · exact False.elim (z ⟨x,h⟩)


theorem axes (a b : Dual V) (ha : a≠0) (hb : b≠0) (hab : a≠b) :
    ∃ p q : V, a p=1 ∧ b p=0 ∧ a q=0 ∧ b q=1 := by
  have diff : ∃ x, a x≠b x := by
    by_contra h
    apply hab
    ext x
    by_contra g
    exact h ⟨x,g⟩
  obtain ⟨z,hz⟩ := diff
  obtain ⟨x,hx⟩ := some_one a ha
  obtain ⟨y,hy⟩ := some_one b hb
  rcases values (a z) with az|az <;> rcases values (b z) with bz|bz
  · exact False.elim (hz (az.trans bz.symm))
  · rcases values (b x) with bx|bx
    · exact ⟨x,z,hx,bx,az,bz⟩
    · exact ⟨x+z,z,by simp [hx,az],by simp [bx,bz],az,bz⟩
  · rcases values (a y) with ay|ay
    · exact ⟨z,y,az,bz,ay,hy⟩
    · exact ⟨z,y+z,az,bz,by simp [ay,az],by simp [hy,bz]⟩
  · exact False.elim (hz (az.trans bz.symm))

def err (a b lin : Dual V) (off : F) (x : V) : Bool :=
  toBit (a x*b x + (lin x+off))

theorem anchored_square (a b lin : Dual V) (off : F)
    (p q x : V) (ap : a p=1) (bp : b p=0) (aq : a q=0) (bq : b q=1) :
    xor4 (err a b lin off x) (err a b lin off (x+p))
      (err a b lin off (x+q)) (err a b lin off (x+(p+q))) = true := by
  have e₁ : lin (x+p)+off=(lin x+off)+lin p := by simp [add_comm,add_left_comm]
  have e₂ : lin (x+q)+off=(lin x+off)+lin q := by simp [add_comm,add_left_comm]
  have e₃ : lin (x+(p+q))+off=((lin x+off)+lin p)+lin q := by
    simp [add_comm,add_left_comm]
  unfold err
  rw [e₁,e₂,e₃]
  simp only [map_add,ap,bp,aq,bq,add_zero,zero_add,bit_one,
    bit_add,bit_mul,Bool.xor_true]
  simpa only [prodErr,bit_add] using
    quadratic_square (toBit (a x)) (toBit (b x)) (toBit (lin x) ^^ toBit off)
      (toBit (lin p)) (toBit (lin q))

theorem translated_perm [Fintype V] (t : V) :
    (((Finset.univ : Finset V).toList).map (fun x => x+t)).Perm
      (Finset.univ : Finset V).toList := by
  classical
  let s := (Finset.univ : Finset V)
  have nd : s.toList.Nodup := s.nodup_toList
  have nm : (s.toList.map (fun x=>x+t)).Nodup :=
    List.Nodup.map (fun _ _ eq=>add_right_cancel eq) nd
  apply (List.perm_ext_iff_of_nodup nm nd).mpr
  intro y
  simp only [s,Finset.mem_toList,Finset.mem_univ,List.mem_map,true_and,iff_true]
  exact ⟨y-t,sub_add_cancel y t⟩

theorem four_total [Fintype V] (a b l : Dual V) (off : F)
    (ha : a≠0) (hb : b≠0) (hab : a≠b) :
    (Fintype.card V) ≤ 4 * ((Finset.univ : Finset V).filter
      (fun x => err a b l off x = true)).card := by
  classical
  obtain ⟨p,q,ap,bp,aq,bq⟩ := axes a b ha hb hab
  let xs := (Finset.univ : Finset V).toList
  let Q := err a b l off
  have bound := quarter xs Q (fun x=>x+p) (fun x=>x+q) (fun x=>x+(p+q))
    (translated_perm p) (translated_perm q) (translated_perm (p+q))
    (fun x _=>anchored_square a b l off p q x ap bp aq bq)
  have rep : (xs.filter Q).toFinset = (Finset.univ : Finset V).filter (fun x=>Q x=true) := by
    ext x
    simp [xs]
  have nd : (xs.filter Q).Nodup :=
    List.filter_sublist.nodup (Finset.univ : Finset V).nodup_toList
  rw [sumOn_bits,←List.toFinset_card_of_nodup nd,rep] at bound
  simpa [xs,Q] using bound

noncomputable def exceptional {U : Type*} (marked : Finset U) (a b : U→Dual V) : Finset U := by
  classical
  exact marked.filter (fun u => a u≠0 ∧ b u≠0 ∧ a u≠b u)

theorem mem_exceptional {U : Type*} (marked : Finset U) (a b : U→Dual V) (u : U) :
    u ∈ exceptional marked a b ↔ u ∈ marked ∧ a u≠0 ∧ b u≠0 ∧ a u≠b u := by
  classical
  unfold exceptional
  exact Finset.mem_filter

theorem exception_count {U : Type*} [Fintype V] [DecidableEq U] (marked : Finset U)
    (a b l : U→Dual V) (c : U→F) (e : Nat)
    (h : ∀ x, (marked.filter (fun u => err (a u) (b u) (l u) (c u) x=true)).card≤e) :
    (exceptional marked a b).card≤4*e := by
  classical
  let xs := (Finset.univ : Finset V).toList
  let ys := marked.toList
  let Q (x : V) (u : U) := err (a u) (b u) (l u) (c u) x
  let bad (u : U) := decide (a u≠0 ∧ b u≠0 ∧ a u≠b u)
  have xsPositive : 0<xs.length := by
    simp only [xs,Finset.length_toList,Finset.card_univ]
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  have out := PEqualNP.Outside.L_meta_32570_aux.exception_bound xs ys Q bad e xsPositive
    (fun x _ => by
      change (marked.toList.filter (Q x)).length≤e
      rw [list_card_toList marked (Q x)]
      exact h x)
    (fun u _ hu => by
      obtain ⟨x₁,x₂,x₃⟩ := of_decide_eq_true hu
      rw [sumOn_bits]
      change (Finset.univ : Finset V).toList.length≤4*
        ((Finset.univ : Finset V).toList.filter (fun x=>Q x u)).length
      rw [list_card_toList (Finset.univ : Finset V) (fun x=>Q x u),
        Finset.length_toList,Finset.card_univ]
      exact four_total (a u) (b u) (l u) (c u) x₁ x₂ x₃)
  change (marked.toList.filter bad).length≤4*e at out
  rw [list_card_toList marked bad] at out
  apply le_of_eq_of_le ?_ out
  apply congrArg Finset.card
  ext u
  rw [mem_exceptional,Finset.mem_filter]
  simp only [bad,decide_eq_true_eq]

end

end PEqualNP.Outside.L_meta_32570_aux.Authentic





namespace PEqualNP.Outside.L_meta_32570_aux.SectionBridge

abbrev F := ZMod 2
abbrev Dual (V : Type*) [AddCommGroup V] [Module F V] := V →ₗ[F] F

theorem transport {V Z U : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup Z] [Module F Z] [DecidableEq U]
    (obs : V →ₗ[F] Z) (quota : Finset U)
    (target : Z → U → F)
    (A : U → Dual V) (b : U → F) (e : Nat)
    (h : ∀ x, (quota.filter (fun u=>target (obs x) u ≠ A u x+b u)).card≤e) :
    ∃ P : U → Dual Z, ∀ z ∈ LinearMap.range obs,
      (quota.filter (fun u=>target z u ≠ P u z+b u)).card≤e := by
  let X := LinearMap.range obs
  let rangeMap : V→ₗ[F] X := obs.rangeRestrict
  obtain ⟨lift,hlift⟩ := rangeMap.exists_rightInverse_of_surjective obs.range_rangeRestrict
  have aux (u : U) : ∃ f : Dual Z, ∀ z : X, f z = A u (lift z) := by
    obtain ⟨f,hf⟩ := ((A u).comp lift).exists_extend
    refine ⟨f,?_⟩
    intro z
    exact LinearMap.congr_fun hf z
  let P (u : U) := Classical.choose (aux u)
  have hp (u : U) := Classical.choose_spec (aux u)
  refine ⟨P,?_⟩
  intro z hz
  let w : X := ⟨z,hz⟩
  have e₁ : obs (lift w)=z := congrArg Subtype.val (LinearMap.congr_fun hlift w)
  have e₂ : ∀ u, P u z=A u (lift w) := fun u=>hp u w
  simpa only [e₁,e₂] using h (lift w)

end PEqualNP.Outside.L_meta_32570_aux.SectionBridge




namespace PEqualNP.Outside.L_meta_32570_aux.FieldRows
open scoped BigOperators

abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n→F

def fbit (b : Bool) : F := if b then 1 else 0

theorem fbit_xor (x y : Bool) : fbit (x ^^ y)=fbit x+fbit y := by
  cases x <;> cases y <;> decide

theorem scalars (c : F) : c=0 ∨ c=1 := by
  change Fin 2 at c
  obtain ⟨n,hn⟩ := c
  have h : n=0 ∨ n=1 := by omega
  rcases h with h|h
  · exact .inl (Fin.ext h)
  · exact .inr (Fin.ext h)

def evaluate (n row : Nat) : W n→ₗ[F] F where
  toFun x := ∑ i : Fin n, fbit (row.testBit i.val)*x i
  map_add' x y := by
    simp [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    rcases scalars c with rfl|rfl <;> simp

@[simp] theorem eval_apply (n row : Nat) (x : W n) :
    evaluate n row x=∑ i : Fin n, fbit (row.testBit i.val)*x i := rfl

@[simp] theorem eval_zero (n : Nat) : evaluate n 0=0 := by
  ext x
  simp [fbit]

theorem eval_xor (n a b : Nat) : evaluate n (a^^^b)=evaluate n a+evaluate n b := by
  apply LinearMap.ext
  intro x
  simp only [eval_apply,LinearMap.add_apply,Nat.testBit_xor,fbit_xor,add_mul,Finset.sum_add_distrib]

def unit {n : Nat} (j : Fin n) (i : Fin n) : F := if i=j then 1 else 0

theorem unit_eval (n row : Nat) (j : Fin n) :
    evaluate n row (unit j)=fbit (row.testBit j.val) := by
  rw [eval_apply,Finset.sum_eq_single j]
  · simp [unit]
  · intro b _ hb
    simp [unit,hb]
  · intro h
    exfalso; exact h (Finset.mem_univ _)

theorem eval_inj {n a b : Nat} (ba : a<2^n) (bb : b<2^n)
    (h : evaluate n a=evaluate n b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases lt : j<n
  · have s := congrArg (fun f : W n→ₗ[F] F=>f (unit ⟨j,lt⟩)) h
    rw [unit_eval,unit_eval] at s
    change fbit (a.testBit j)=fbit (b.testBit j) at s
    revert s
    cases a.testBit j <;> cases b.testBit j <;> decide
  · have p : 2^n≤2^j := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    rw [Nat.testBit_lt_two_pow (ba.trans_le p),Nat.testBit_lt_two_pow (bb.trans_le p)]

theorem single (n : Nat) (j : Fin n) (x : W n) :
    evaluate n (2^j.val) x=x j := by
  rw [eval_apply,Finset.sum_eq_single j]
  · simp [fbit]
  · intro b _ hb
    have e : j.val≠b.val := by
      intro h
      exact hb (Fin.ext h.symm)
    simp [fbit,Nat.testBit_two_pow_of_ne e]
  · intro h
    exfalso; exact h (Finset.mem_univ _)

theorem mul_pow_xor (i a b : Nat) :
    2^i*(a^^^b)=(2^i*a)^^^(2^i*b) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_two_pow_mul,Nat.testBit_xor]
  cases decide (j≥i) <;> rfl

theorem packed_pow {m i : Nat} (hi : m<2^i) :
    m+2^i=m^^^2^i := by
  apply Nat.eq_of_testBit_eq
  intro n
  have e := Nat.testBit_two_pow_mul_add 1 hi n
  rw [Nat.mul_one] at e
  rw [Nat.add_comm,e,Nat.testBit_xor]
  by_cases h : n < i
  · simp [h,Nat.testBit_two_pow_of_ne (by omega : i≠n)]
  · have hn : m<2^n := hi.trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
    rw [ite_eq_right h,Nat.testBit_lt_two_pow hn,Bool.false_xor]
    change (2^0).testBit (n-i) = (2^i).testBit n
    rw [Nat.testBit_two_pow,Nat.testBit_two_pow]
    simp only [decide_eq_decide]
    omega

theorem pair {n : Nat} (i j : Fin n) (h : i.val<j.val) (x : W n) :
    evaluate n (2^i.val+2^j.val) x=x i+x j := by
  rw [packed_pow (Nat.pow_lt_pow_right (by decide : 1<2) h),
    eval_xor,LinearMap.add_apply,single,single]

theorem three {n : Nat} (i a b c : Nat) (ha : i+a<n) (hb : i+b<n) (hc : i+c<n)
    (x : W n) :
    evaluate n (2^i*((2^a^^^2^b)^^^2^c)) x=x ⟨i+a,ha⟩+x ⟨i+b,hb⟩+x ⟨i+c,hc⟩ := by
  rw [mul_pow_xor,mul_pow_xor,←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
  rw [eval_xor,eval_xor,LinearMap.add_apply,LinearMap.add_apply]
  exact congrArg₂ (·+·)
    (congrArg₂ (·+·) (single n ⟨i+a,ha⟩ x) (single n ⟨i+b,hb⟩ x))
    (single n ⟨i+c,hc⟩ x)

theorem bank56 {n : Nat} (i : Nat) (h : i+6<n) (x : W n) :
    evaluate n (2^i*56) x=x ⟨i+3,by omega⟩+x ⟨i+4,by omega⟩+x ⟨i+5,by omega⟩ :=
  three i 3 4 5 (by omega) (by omega) (by omega) x

theorem bank112 {n : Nat} (i : Nat) (h : i+6<n) (x : W n) :
    evaluate n (2^i*112) x=x ⟨i+4,by omega⟩+x ⟨i+5,by omega⟩+x ⟨i+6,h⟩ :=
  three i 4 5 6 (by omega) (by omega) h x

theorem bank21 {n : Nat} (i : Nat) (h : i+6<n) (x : W n) :
    evaluate n (2^i*21) x=x ⟨i+0,by omega⟩+x ⟨i+2,by omega⟩+x ⟨i+4,by omega⟩ :=
  three i 0 2 4 (by omega) (by omega) (by omega) x

theorem bank42 {n : Nat} (i : Nat) (h : i+6<n) (x : W n) :
    evaluate n (2^i*42) x=x ⟨i+1,by omega⟩+x ⟨i+3,by omega⟩+x ⟨i+5,by omega⟩ :=
  three i 1 3 5 (by omega) (by omega) (by omega) x

theorem checks_tail (p q mask : Nat) (x : W (p+q)) :
    evaluate (p+q) (2^p*mask) x =
      ∑ i : Fin q, if mask.testBit i.val then x (Fin.natAdd p i) else 0 := by
  rw [eval_apply,Fin.sum_univ_add]
  have low : (∑ i : Fin p, fbit ((2^p*mask).testBit (Fin.castAdd q i).val) *
      x (Fin.castAdd q i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [fbit,Nat.testBit_two_pow_mul,show ¬ (p ≤ i.val) by have := i.isLt; omega]
  rw [low,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have e : (2^p*mask).testBit (Fin.natAdd p i).val=mask.testBit i.val := by
    change (2^p*mask).testBit (p+i.val)=_
    simp [Nat.testBit_two_pow_mul]
  rw [e]
  cases mask.testBit i.val <;> simp [fbit]

theorem std_expand {n : Nat} (x : W n) :
    (∑ i : Fin n, x i • unit i)=x := by
  funext j
  rw [Finset.sum_apply,Finset.sum_eq_single j]
  · simp [unit]
  · intro b _ hb
    simp [unit,Pi.smul_apply,hb.symm]
  · intro h
    exfalso; exact h (Finset.mem_univ _)

theorem fbit_round (x : F) : fbit (decide (x≠0))=x := by
  rcases scalars x with rfl|rfl <;> decide

def encodeForm {n : Nat} (f : W n→ₗ[F]F) : Fin (2^n) :=
  PEqualNP.Outside.L_meta_32570_aux.Packing.toMask (fun i=>decide (f (unit i)≠0))

theorem decodeForm {n : Nat} (f : W n→ₗ[F]F) :
    evaluate n (encodeForm f).val=f := by
  apply LinearMap.ext
  intro x
  have E : (∑ i : Fin n, x i * f (unit i))=f x := by
    have h := congrArg f (std_expand x)
    simpa only [map_sum,map_smul,smul_eq_mul] using h
  rw [eval_apply]
  refine Eq.trans ?_ E
  apply Finset.sum_congr rfl
  intro i _
  simp only [encodeForm,PEqualNP.Outside.L_meta_32570_aux.Packing.mask_correct,fbit_round]
  exact mul_comm _ _

end PEqualNP.Outside.L_meta_32570_aux.FieldRows



namespace PEqualNP.Outside.L_meta_32570_aux.Checks
open PEqualNP.Outside.L_meta_32570_aux.FieldRows
open scoped BigOperators

abbrev Z (j : Nat) := Fin j→Fin 2→F

def coord (j : Nat) : Fin j×Fin 2 ≃ Fin (2*j) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm j 2))

theorem coord_val {j : Nat} (v : Fin j) (l : Fin 2) :
    (coord j (v,l)).val=2*v.val+l.val := by
  change l.val+2*v.val=_
  omega

def flatten (j : Nat) : Z j≃ₗ[F] W (2*j) where
  toFun z i := z ((coord j).symm i).1 ((coord j).symm i).2
  invFun x v l := x (coord j (v,l))
  left_inv z := by funext v l; simp
  right_inv x := by
    funext i
    change x (coord j (((coord j).symm i).1, ((coord j).symm i).2))=x i
    have h : (((coord j).symm i).1,((coord j).symm i).2)=(coord j).symm i := by rfl
    rw [h,Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def checkForm {j : Nat} (mask : Fin (2^(2*j))) : Z j→ₗ[F]F :=
  (evaluate (2*j) mask.val).comp (flatten j).toLinearMap

theorem check_literal {j : Nat} (z : Z j) (mask : Fin (2^(2*j))) :
    checkForm mask z = ∑ v : Fin j, ∑ l : Fin 2,
      if mask.val.testBit (2*v.val+l.val) then z v l else 0 := by
  unfold checkForm
  rw [LinearMap.comp_apply,eval_apply]
  change (∑ i : Fin (2*j), fbit (mask.val.testBit i.val)*flatten j z i) = _
  have h := (coord j).sum_comp
    (fun i => fbit (mask.val.testBit i.val)*flatten j z i)
  rw [←h]
  rw [←Finset.univ_product_univ,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro l _
  rw [coord_val]
  have val : flatten j z (coord j (v,l))=z v l := by simp [flatten]
  rw [val]
  cases mask.val.testBit (2*v.val+l.val) <;> simp [fbit]

theorem all_checks {j : Nat} (f : Z j→ₗ[F]F) :
    ∃ m : Fin (2^(2*j)), checkForm m=f := by
  let g := f.comp (flatten j).symm.toLinearMap
  refine ⟨encodeForm g,?_⟩
  unfold checkForm
  rw [decodeForm]
  ext z
  simp [g]

noncomputable def ofSubspace {j : Nat} (S : Submodule F (Z j)) :
    Finset (Fin (2^(2*j))) := by
  classical
  exact Finset.univ.filter (fun m=>∀ x∈S, checkForm m x=0)

theorem test_subspace {j : Nat} (S : Submodule F (Z j)) (z : Z j) :
    (∀ m∈ofSubspace S, checkForm m z=0) ↔ z∈S := by
  classical
  constructor
  · intro h
    by_contra outside
    obtain ⟨f,zeroValue,oneValue⟩ :=
      LinearMap.exists_extend_of_notMem (0 : S→ₗ[F]F) outside (1:F)
    obtain ⟨m,hm⟩ := all_checks f
    have k : m∈ofSubspace S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun x hx => by
        rw [hm]
        exact LinearMap.congr_fun zeroValue (⟨x,hx⟩ : S)⟩
    have z0 := h m k
    rw [hm,oneValue] at z0
    exact one_ne_zero z0
  · intro hz m hm
    exact (Finset.mem_filter.mp hm).2 z hz

end PEqualNP.Outside.L_meta_32570_aux.Checks





namespace PEqualNP.Outside.L_meta_32570_aux.FiniteBinary
abbrev F := ZMod 2

noncomputable def card (V : Type*) [Finite V] : Nat :=
  @Fintype.card V (Fintype.ofFinite V)

theorem card_eq (V : Type*) [Fintype V] : card V=Fintype.card V :=
  @Fintype.card_congr V V (Fintype.ofFinite V) inferInstance (Equiv.refl V)

theorem card_congr {V W : Type*} [Finite V] [Finite W] (e : V≃W) : card V=card W :=
  @Fintype.card_congr V W (Fintype.ofFinite V) (Fintype.ofFinite W) e

theorem card_pi (n : Nat) : card (Fin n→F)=2^n := by
  rw [card_eq,Fintype.card_fun,Fintype.card_fin,ZMod.card]

theorem card_prod {V W : Type*} [Finite V] [Finite W] :
    card (V×W)=card V*card W := by
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype W := Fintype.ofFinite W
  simp only [card_eq,Fintype.card_prod]

theorem card_positive (V : Type*) [Finite V] [Nonempty V] : 0<card V := by
  letI : Fintype V := Fintype.ofFinite V
  exact (@Fintype.card_pos_iff V _).mpr inferInstance

section
variable {V : Type*} [Finite V] [AddCommGroup V] [Module F V]

structure Chart (V : Type*) [AddCommGroup V] [Module F V] where
  d : Nat
  eqv : V≃ₗ[F](Fin d→F)

noncomputable def chart (V : Type*) [Finite V] [AddCommGroup V] [Module F V] : Chart V := by
  classical
  let B := Module.Basis.ofVectorSpace F V
  let I := Module.Basis.ofVectorSpaceIndex F V
  letI : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let reindex : (I→F) ≃ₗ[F] (Fin (Fintype.card I)→F) :=
    { toFun := fun f k=>f (e.symm k)
      invFun := fun g k=>g (e k)
      left_inv := by intro f;funext k;simp
      right_inv := by intro g;funext k;simp
      map_add' := fun _ _=>rfl
      map_smul' := fun _ _=>rfl }
  exact ⟨Fintype.card I,B.equivFun.trans reindex⟩

theorem chart_card (V : Type*) [Finite V] [AddCommGroup V] [Module F V] :
    card V=2^(chart V).d :=
  (card_congr (chart V).eqv.toEquiv).trans (card_pi _)

noncomputable def logdim (V : Type*) [Finite V] : Nat := (card V).log2

theorem card_power (V : Type*) [Finite V] [AddCommGroup V] [Module F V] :
    card V=2^logdim V := by
  unfold logdim
  rw [chart_card V,Nat.log2_two_pow]

instance quotFinite (S : Submodule F V) : Finite (V ⧸ S) :=
  Finite.of_surjective S.mkQ S.mkQ_surjective

noncomputable def quotientSplit (S : Submodule F V) : V≃(V ⧸ S)×S := by
  classical
  let rep (q : V ⧸ S) := Classical.choose (S.mkQ_surjective q)
  have hp (q : V ⧸ S) : S.mkQ (rep q)=q := Classical.choose_spec (S.mkQ_surjective q)
  have m (x : V) : x-rep (S.mkQ x)∈S := by
    have e : S.mkQ (x-rep (S.mkQ x))=0 := by rw [map_sub,hp,sub_self]
    exact (Submodule.Quotient.mk_eq_zero S).mp e
  let f (x : V) : (V ⧸ S)×S := (S.mkQ x,⟨x-rep (S.mkQ x),m x⟩)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b same
    have q := congrArg Prod.fst same
    have x := congrArg (fun w : (V ⧸ S)×S=>w.2.val) same
    change S.mkQ a=S.mkQ b at q
    change a-rep (S.mkQ a)=b-rep (S.mkQ b) at x
    rw [q] at x
    have e := congrArg (fun t=>t+rep (S.mkQ b)) x
    simpa only [sub_add_cancel] using e
  · rintro ⟨q,s⟩
    refine ⟨s.val+rep q,Prod.ext ?_ ?_⟩
    · change S.mkQ (s.val+rep q)=q
      have e : S.mkQ s.val=0 := (Submodule.Quotient.mk_eq_zero S).mpr s.property
      rw [map_add,e,hp,zero_add]
    · apply Subtype.ext
      change (s.val+rep q)-rep (S.mkQ (s.val+rep q))=s.val
      have e : S.mkQ s.val=0 := (Submodule.Quotient.mk_eq_zero S).mpr s.property
      rw [map_add,e,hp,zero_add,add_sub_cancel_right]

theorem quotient_card (S : Submodule F V) :
    card V=card (V⧸S)*card S :=
  (card_congr (quotientSplit S)).trans card_prod

theorem power_inj {a b : Nat} (h : 2^a=2^b) : a=b := by
  have t := congrArg Nat.log2 h
  simpa only [Nat.log2_two_pow] using t

theorem quotient_log (S : Submodule F V) :
    logdim V=logdim (V⧸S)+logdim S := by
  apply power_inj
  rw [←card_power V,Nat.pow_add,←card_power (V⧸S),←card_power S]
  exact quotient_card S

end

end PEqualNP.Outside.L_meta_32570_aux.FiniteBinary






namespace PEqualNP.Outside.L_meta_32570_aux.Cell
open PEqualNP.Outside.L_meta_32570_aux.Credited32058
open scoped BigOperators

abbrev F := ZMod 2
abbrev Dual (V : Type*) [AddCommGroup V] [Module F V] := V→ₗ[F]F

section
variable {V O : Type*} [AddCommGroup V] [Module F V]

structure Tree (V O : Type*) [AddCommGroup V] [Module F V] where
  nodes : Finset H
  ask : H→Dual V
  shift : H→F
  P : H→O→Dual V
  off : H→O→F

def answerBit (x : F) : Bool := decide (x≠0)
def run (tr : Tree V O) (x : V) : H :=
  (List.range tr.nodes.card).foldl (fun (p : H) _ =>
    if p∈tr.nodes then p++[answerBit (tr.ask p x+tr.shift p)] else p) []
def predict (tr : Tree V O) (x : V) (o : O) : F := tr.P (run tr x) o x+tr.off (run tr x) o

theorem asBool_inj {a b : F} (h : answerBit a=answerBit b) : a=b := by
  have split (x : F) : x=0 ∨ x=1 := by
    change Fin 2 at x
    obtain ⟨n,ng⟩ := x
    have e : n=0 ∨ n=1 := by omega
    rcases e with e|e
    · exact .inl (Fin.ext e)
    · exact .inr (Fin.ext e)
  rcases split a with rfl|rfl <;> rcases split b with rfl|rfl <;> simp_all [answerBit]

theorem run_follow (tr : Tree V O) (x : V) :
    run tr x = follow tr.nodes.toList
      (fun p => answerBit (tr.ask p x+tr.shift p)) tr.nodes.card [] := by
  simpa [run,advance,Finset.mem_toList] using
    fold_follow tr.nodes.toList (fun p => answerBit (tr.ask p x+tr.shift p))
      (List.range tr.nodes.card) []

theorem cover (tr : Tree V O) :
    ∃ fs : Finset H, fs.card≤tr.nodes.card+1 ∧ ∀ x : V, run tr x∈fs := by
  obtain ⟨ls,sz,cv⟩ := exact_leaf_list tr.nodes.toList tr.nodes.card
  refine ⟨ls.toFinset, (List.toFinset_card_le ls).trans (by simpa using sz),?_⟩
  intro x
  apply List.mem_toFinset.mpr
  simpa [run,Finset.mem_toList] using cv (fun p => answerBit (tr.ask p x+tr.shift p))

theorem geometry (tr : Tree V O) (x₀ : V) :
    ∃ S : Submodule F V, ∀ x, run tr x=run tr x₀ ↔ x-x₀∈S := by
  let Q (x : V) (p : H) := answerBit (tr.ask p x+tr.shift p)
  obtain ⟨checks,eq⟩ := reachable_leaf_cell tr.nodes.toList (Q x₀) tr.nodes.card []
  let S : Submodule F V :=
    { carrier := {v | ∀ z ∈ checks, tr.ask z.1 v=0}
      zero_mem' := fun z _=>map_zero _, add_mem' := fun {a b} ha hb z hz=>by rw [map_add,ha z hz,hb z hz,add_zero],
      smul_mem' := fun a b hb z hz=>by rw [map_smul,hb z hz,smul_zero] }
  refine ⟨S,?_⟩
  intro x
  rw [run_follow,run_follow]
  change follow tr.nodes.toList (Q x) tr.nodes.card [] =
    follow tr.nodes.toList (Q x₀) tr.nodes.card [] ↔ _
  rw [eq]
  have ref := (eq (Q x₀)).mp rfl
  change (∀ z∈checks,Q x z.1=z.2) ↔ ∀ z∈checks,tr.ask z.1 (x-x₀)=0
  constructor
  · intro h z hz
    have q : Q x z.1=Q x₀ z.1 := (h z hz).trans (ref z hz).symm
    have f := asBool_inj q
    change tr.ask z.1 x+tr.shift z.1=tr.ask z.1 x₀+tr.shift z.1 at f
    rw [map_sub,sub_eq_zero]
    exact add_right_cancel f
  · intro h z hz
    have f := h z hz
    rw [map_sub,sub_eq_zero] at f
    change answerBit (tr.ask z.1 x+tr.shift z.1)=z.2
    rw [f]
    exact ref z hz

noncomputable def fibers [Fintype V] (tr : Tree V O) (p : H) : Finset V :=
  (Finset.univ : Finset V).filter (fun x=>run tr x=p)

noncomputable def cellEquiv [Fintype V] (tr : Tree V O) (x₀ : V) (S : Submodule F V)
    (geom : ∀ x, run tr x=run tr x₀ ↔ x-x₀∈S) : S ≃ ↥(fibers tr (run tr x₀)) :=
  Equiv.ofBijective (fun z => ⟨z.val+x₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (geom _).mpr (by simpa using z.property)⟩⟩)
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        exact add_right_cancel (congrArg Subtype.val h)
      · intro x
        have h := (Finset.mem_filter.mp x.property).2
        refine ⟨⟨x.val-x₀,(geom _).mp h⟩,?_⟩
        apply Subtype.ext
        exact sub_add_cancel x.val x₀)

theorem largest_card [Fintype V] (tr : Tree V O)
    (L : Nat) (h : tr.nodes.card<L) :
    ∃ x₀ : V, ∃ S : Submodule F V,
      (∀ x, run tr x=run tr x₀ ↔ x-x₀∈S) ∧ Fintype.card V≤L*(fibers tr (run tr x₀)).card := by
  classical
  obtain ⟨hs,sz,cov⟩ := cover tr
  have hn : hs.Nonempty := ⟨_,cov 0⟩
  obtain ⟨p,pm,ph⟩ := Finset.sup_mem_of_nonempty (f:=fun p=>(fibers tr p).card) hn
  change (fibers tr p).card = hs.sup (fun p=>(fibers tr p).card) at ph
  have bound (q) (hq : q∈hs) : (fibers tr q).card≤(fibers tr p).card := by
    rw [ph]
    exact Finset.le_sup (s:=hs) (f:=fun p : H => (fibers tr p).card) hq
  have eq := Finset.card_eq_sum_card_fiberwise (s:=(Finset.univ : Finset V))
    (t:=hs) (f:=run tr) (fun x _=>cov x)
  have le : Fintype.card V≤L*(fibers tr p).card := by
    rw [←Finset.card_univ,eq]
    calc
      _ ≤ ∑ q ∈ hs,(fibers tr p).card := Finset.sum_le_sum bound
      _ = hs.card*(fibers tr p).card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have pos : 0<(fibers tr p).card := by
    have hV : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨0⟩
    by_contra nh
    have zz : (fibers tr p).card=0 := by omega
    rw [zz,Nat.mul_zero] at le
    omega
  obtain ⟨x₀,hx⟩ := Finset.card_pos.mp pos
  have ex : run tr x₀=p := (Finset.mem_filter.mp hx).2
  obtain ⟨S,geom⟩ := geometry tr x₀
  rw [←ex] at le
  exact ⟨x₀,S,geom,le⟩

end
end PEqualNP.Outside.L_meta_32570_aux.Cell



namespace PEqualNP.Outside.L_meta_32570_aux.Cell
open PEqualNP.Outside.L_meta_32570_aux.Credited32058
open PEqualNP.Outside.L_meta_32570_aux.FiniteBinary

section
variable {V O : Type*} [AddCommGroup V] [Module F V]

noncomputable def codim [Finite V] (S : Submodule F V) : Nat :=
  logdim (V ⧸ S)

theorem sum_dim [Finite V] (S : Submodule F V) :
    logdim S + codim S = logdim V :=
  by simpa only [codim,Nat.add_comm] using (quotient_log S).symm

theorem largest [Fintype V] (tr : Tree V O)
    (L : Nat) (h : tr.nodes.card<L) :
    ∃ x₀ : V, ∃ S : Submodule F V,
      (∀ x, run tr x=run tr x₀ ↔ x-x₀∈S) ∧ 2^codim S≤L := by
  classical
  obtain ⟨x₀,S,geom,c⟩ := largest_card tr L h
  have cb := card_congr (cellEquiv tr x₀ S geom)
  rw [card_eq (↥(fibers tr (run tr x₀))),Fintype.card_coe] at cb
  rw [←cb,←card_eq V,quotient_card S] at c
  refine ⟨x₀,S,geom,?_⟩
  haveI : Nonempty S := ⟨0⟩
  have u := Nat.le_of_mul_le_mul_right c (card_positive S)
  unfold codim
  rwa [←card_power (V⧸S)]

noncomputable def quotientChart [Finite V] (S : Submodule F V) :
    (V⧸S)≃ₗ[F](Fin (codim S)→F) := by
  let C := chart (V⧸S)
  have e : codim S=C.d := by
    unfold codim logdim
    rw [chart_card (V⧸S),Nat.log2_two_pow]
  rw [e]
  exact C.eqv

noncomputable def query [Finite V] (S : Submodule F V)
    (i : Fin (codim S)) : Dual V where
  toFun x := quotientChart S (S.mkQ x) i
  map_add' x y := by simp [map_add,Pi.add_apply]
  map_smul' a x := by simp [map_smul,Pi.smul_apply]

theorem basis_cell [Finite V] (S : Submodule F V)
    (x : V) :
    (∀ j : Fin (codim S), query S j x=0) ↔ x∈S := by
  constructor
  · intro h
    let B := quotientChart S
    have eq : B (S.mkQ x)=0 := funext h
    have zero : S.mkQ x=0 := B.injective (by simpa only [map_zero] using eq)
    exact (Submodule.Quotient.mk_eq_zero S).mp zero
  · intro h j
    have e : S.mkQ x=0 := (Submodule.Quotient.mk_eq_zero S).mpr h
    change (quotientChart S) (S.mkQ x) j=0
    simp [e]

noncomputable def fixedAsk [Finite V] (S : Submodule F V) (p : H) : Dual V :=
  if h : p.length<codim S then query S ⟨p.length,h⟩ else 0

noncomputable def make [Finite V] (S : Submodule F V)
    (P : H→O→Dual V) (off : H→O→F) : Tree V O :=
  ⟨(Fixed.nodes (codim S)).toFinset,fixedAsk S,fun _=>0,P,off⟩

theorem fixed_count [Finite V] (S : Submodule F V)
    (P : H→O→Dual V) (off : H→O→F) :
    (make S P off).nodes.card+1=2^codim S := by
  unfold make
  rw [List.toFinset_card_of_nodup (Fixed.nodup _),Fixed.count]

theorem fixed_history_cell [Finite V] (S : Submodule F V)
    (P : H→O→Dual V) (off : H→O→F) (x y : V)
    (eq : run (make S P off) x=run (make S P off) y) : x-y∈S := by
  let d := codim S
  let tr := make S P off
  have count : d≤tr.nodes.card := by
    change d≤(Fixed.nodes d).toFinset.card
    rw [List.toFinset_card_of_nodup (Fixed.nodup _)]
    exact Fixed.depth_le d
  let A (x : V) (n : Nat) := if hp : n<d then
      answerBit (query S ⟨n,hp⟩ x) else false
  have runCap (x : V) :
      run tr x = (List.range tr.nodes.card).foldl
        (fun (p : H) _ => if p∈Fixed.nodes d then p++[A x p.length] else p) [] := by
    simp only [run,tr,make,List.mem_toFinset,add_zero]
    congr 1
    funext p _
    by_cases h : p.length<d <;> simp [fixedAsk,A,d,h,answerBit]
  apply (basis_cell S _).mp
  intro j
  have hx := (Fixed.fixed_history d (A x) tr.nodes.card count).2 j.val j.isLt
  have hy := (Fixed.fixed_history d (A y) tr.nodes.card count).2 j.val j.isLt
  rw [←runCap] at hx hy
  rw [show run tr x=run tr y from eq,hy] at hx
  have ans := asBool_inj (by simpa [A,d,j.isLt] using hx :
    answerBit (query S j y) = answerBit (query S j x))
  rw [map_sub,sub_eq_zero]
  exact ans.symm

theorem uniform [Finite V] [DecidableEq O]
    (S : Submodule F V) (target : V→O→F) (marks : Finset O) (e L : Nat)
    (bound : 2^codim S≤L)
    (cells : ∀ z : V, ∃ (P : O→Dual V) (off : O→F),
       ∀ x : V, x-z∈S → (marks.filter (fun u=>target x u≠P u x+off u)).card≤e) :
    ∃ tr : Tree V O, tr.nodes.card<L ∧
      ∀ x, (marks.filter (fun u=>target x u≠predict tr x u)).card≤e := by
  classical
  let stub : Tree V O := make S (fun _ _=>0) (fun _ _=>0)
  let anch (p : H) : V := if h : ∃ z, run stub z=p then Classical.choose h else 0
  have a_ok (x : V) : run stub (anch (run stub x))=run stub x := by
    have h : ∃ z, run stub z=run stub x := ⟨x,rfl⟩
    unfold anch
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  choose P off ok using cells
  let tr : Tree V O := make S (fun p=>P (anch p)) (fun p=>off (anch p))
  have ease : ∀ x, run tr x=run stub x := fun _=>rfl
  refine ⟨tr,?_ ,?_⟩
  · have z := fixed_count S (fun p=>P (anch p)) (fun p=>off (anch p))
    change tr.nodes.card+1=2^codim S at z
    omega
  · intro x
    let p := run stub x
    have diff : x-anch p∈S := fixed_history_cell S (fun _ _=>0) (fun _ _=>0)
      x (anch p) (a_ok x).symm
    change (marks.filter (fun u=>target x u≠tr.P (run tr x) u x+tr.off (run tr x) u)).card≤e
    rw [ease]
    exact ok (anch p) x diff

end
end PEqualNP.Outside.L_meta_32570_aux.Cell





namespace PEqualNP.Outside.L_meta_32570_aux.Quadratic

abbrev F := ZMod 2
abbrev Dual (V : Type*) [AddCommGroup V] [Module F V] := V→ₗ[F]F

structure Family (V O : Type*) [AddCommGroup V] [Module F V] where
  a : O→Dual V
  b : O→Dual V
  lin : O→Dual V
  const : O→F

section
variable {V O : Type*} [AddCommGroup V] [Module F V]

def target (Q : Family V O) (x : V) (u : O) : F :=
  Q.a u x*Q.b u x + Q.lin u x + Q.const u
def shiftLin (Q : Family V O) (x₀ : V) (u : O) : Dual V :=
  Q.lin u + (Q.a u x₀)•Q.b u + (Q.b u x₀)•Q.a u
def shiftOff (Q : Family V O) (x₀ : V) (u : O) : F :=
  Q.a u x₀*Q.b u x₀ + Q.lin u x₀+Q.const u

theorem target_shift (Q : Family V O) (x₀ d : V) (u : O) :
    target Q (x₀+d) u = Q.a u d*Q.b u d + shiftLin Q x₀ u d + shiftOff Q x₀ u := by
  simp only [target,map_add,add_mul,mul_add,shiftLin,shiftOff,LinearMap.add_apply,
    LinearMap.smul_apply,smul_eq_mul]
  ring

theorem target_shift_sub (Q : Family V O) (x₀ x : V) (u : O) :
    target Q x u = Q.a u (x-x₀)*Q.b u (x-x₀) +
      shiftLin Q x₀ u (x-x₀) + shiftOff Q x₀ u := by
  have h := target_shift Q x₀ (x-x₀) u
  rw [add_comm x₀ (x-x₀),sub_add_cancel] at h
  exact h

theorem apply_residual (Q : Family V O) (x₀ d : V) (u : O)
    (P : O→Dual V) (c : O→F) :
    target Q (x₀+d) u≠P u (x₀+d)+c u ↔
      Q.a u d*Q.b u d + ((shiftLin Q x₀ u-P u) d +
        (shiftOff Q x₀ u-(P u x₀+c u)))≠0 := by
  have e : target Q (x₀+d) u-(P u (x₀+d)+c u) =
      Q.a u d*Q.b u d + ((shiftLin Q x₀ u-P u) d +
        (shiftOff Q x₀ u-(P u x₀+c u))) := by
    rw [target_shift Q x₀ d u,LinearMap.sub_apply,map_add]
    abel
  refine sub_ne_zero.symm.trans ?_
  rw [e]

def linearChoice (a b : Dual V) (c : Fin 3) : Dual V :=
  if c.val=0 then a else if c.val=1 then b else a+b

def exactChoice (a : Dual V) (c : Fin 3) : Dual V :=
  if c.val=2 then a else 0

theorem zero_or_one (a : F) : a=0 ∨ a=1 := by
  change Fin 2 at a
  obtain ⟨n,hn⟩ := a
  have h : n=0 ∨ n=1 := by omega
  rcases h with h|h
  · exact .inl (Fin.ext h)
  · exact .inr (Fin.ext h)

theorem exact_choice (a b : Dual V) (c : Fin 3) (x : V)
    (clean : linearChoice a b c x=0) :
    a x*b x=exactChoice a c x := by
  have ix : c.val=0 ∨ c.val=1 ∨ c.val=2 := by have := c.isLt; omega
  rcases ix with ix|ix|ix
  · have q : a x=0 := by simpa [linearChoice,ix] using clean
    simp [exactChoice,ix,q]
  · have q : b x=0 := by simpa [linearChoice,ix] using clean
    simp [exactChoice,ix,q]
  · have q : a x+b x=0 := by simpa [linearChoice,ix] using clean
    simp only [exactChoice,ix,ite_true]
    have o : (1:F)+1=0 := by decide
    rcases zero_or_one (a x) with ea|ea <;> rcases zero_or_one (b x) with eb|eb <;>
      simp_all [o]



theorem lift_affine (Q : Family V O) (x₀ x : V) (u : O) (p : Dual V) (off : F) :
    target Q x u≠(p+shiftLin Q x₀ u) x +
      (off+shiftOff Q x₀ u-(p+shiftLin Q x₀ u) x₀) ↔
    Q.a u (x-x₀)*Q.b u (x-x₀)≠p (x-x₀)+off := by
  have e :
      target Q x u-((p+shiftLin Q x₀ u) x +
        (off+shiftOff Q x₀ u-(p+shiftLin Q x₀ u) x₀)) =
      Q.a u (x-x₀)*Q.b u (x-x₀)-(p (x-x₀)+off) := by
    rw [target_shift_sub Q x₀ x u]
    simp only [LinearMap.add_apply,map_sub]
    abel
  refine sub_ne_zero.symm.trans ?_
  rw [e]
  exact sub_ne_zero

end
end PEqualNP.Outside.L_meta_32570_aux.Quadratic





namespace PEqualNP.Outside.L_meta_32570_aux.Model
open PEqualNP.Outside.L_meta_32570_aux.Quadratic

abbrev W (k : Nat) := Fin k→F
abbrev Out (k : Nat) := Bool×Fin k

def idx {k : Nat} (hk : 0<k) (x : Nat) : Fin k := Operands.idx k hk x

def reindex {k : Nat} (s : Fin k→Fin k) : W k→ₗ[F]W k where
  toFun w q := w (s q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rot {k : Nat} (hk : 0<k) (s : Nat) : W k→ₗ[F]W k :=
  reindex (fun i=>idx hk (i.val+k-s%k))
def mix {k : Nat} (hk : 0<k) (g : Nat) : W k→ₗ[F]W k :=
  LinearMap.id+reindex (fun i=>idx hk (i.val+g))+reindex (fun i=>idx hk (i.val+k-g%k))

def y {k : Nat} (hk : 0<k) (b : Bool) : W k→ₗ[F]W k :=
  (mix hk (if b then 2 else 1)).comp (rot hk (if b then 3 else 1))
def base {k : Nat} (hk : 0<k) (b : Bool) : W k→ₗ[F]W k :=
  y hk b+(if b then rot hk 4 else LinearMap.id)
def named {k : Nat} (hk : 0<k) (b : Bool) (row col : W k) : W k :=
  mix hk (if b then 2 else 1) (if b then col else row)
def coord {k : Nat} (i : Fin k) : Dual (W k) where
  toFun w := w i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def a {k : Nat} (hk : 0<k) (u : Out k) : Dual (W k) :=
  (coord (idx hk (u.2.val+1))).comp (y hk u.1)
def b {k : Nat} (hk : 0<k) (u : Out k) : Dual (W k) :=
  (coord (idx hk (u.2.val+2))).comp (y hk u.1)
def ca {k : Nat} (hk : 0<k) (row col : W k) (u : Out k) : F :=
  1+named hk u.1 row col (idx hk (u.2.val+1))
def cb {k : Nat} (hk : 0<k) (row col : W k) (u : Out k) : F :=
  named hk u.1 row col (idx hk (u.2.val+2))

def family {k : Nat} (hk : 0<k) (row col c₁ c₂ : W k) : Family (W k) (Out k) where
  a := a hk
  b := b hk
  lin u := (coord u.2).comp (base hk u.1) + ca hk row col u•b hk u + cb hk row col u•a hk u
  const u := named hk u.1 row col u.2+(if u.1 then c₂ u.2 else c₁ u.2) +
    ca hk row col u*cb hk row col u

def marked {k : Nat} (mark : Bool→Fin k→Bool) : Finset (Out k) :=
  (Finset.univ : Finset (Out k)).filter (fun u=>mark u.1 u.2=true)

def output {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k)
    (x : W k) (u : Out k) : F :=
  if mark u.1 u.2 then
    let old := (rot hk (if u.1 then 3 else 1)) x+(if u.1 then col else row)
    let g := if u.1 then 2 else 1
    let ys := fun i : Fin k=>old i+old (idx hk (i.val+g))+old (idx hk (i.val+k-g%k))
    ys u.2 + (1+ys (idx hk (u.2.val+1)))*ys (idx hk (u.2.val+2)) +
      (if u.1 then rot hk 4 x u.2 else x u.2)+(if u.1 then c₂ u.2 else c₁ u.2)
  else 0

theorem branch_add {k : Nat} (hk : 0<k) (row col x : W k) (flag : Bool) (i : Fin k) :
    let old := (rot hk (if flag then 3 else 1)) x+(if flag then col else row)
    let g := if flag then 2 else 1
    old i+old (idx hk (i.val+g))+old (idx hk (i.val+k-g%k)) =
      y hk flag x i + named hk flag row col i := by
  dsimp only
  change mix hk _ ((rot hk _) x+(if flag then col else row)) i = _
  rw [map_add]
  rfl

theorem output_correct {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ x : W k)
    (u : Out k) (hu : u∈marked mark) :
    output hk mark row col c₁ c₂ x u=target (family hk row col c₁ c₂) x u := by
  have hm := (Finset.mem_filter.mp hu).2
  unfold output
  rw [hm]
  dsimp only [ite_true]
  simp only [branch_add]
  change y hk u.1 x u.2 + named hk u.1 row col u.2 +
        (1+(a hk u x+named hk u.1 row col (idx hk (u.2.val+1))))*
          (b hk u x+cb hk row col u) + _ + _ = _
  unfold target family ca
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  have br : base hk u.1 x u.2=y hk u.1 x u.2+(if u.1 then rot hk 4 x u.2 else x u.2) := by
    cases u.1 <;> rfl
  change _ = a hk u x*b hk u x+
    (base hk u.1 x u.2 + (1+named hk u.1 row col (idx hk (u.2.val+1)))*b hk u x+
      cb hk row col u*a hk u x)+_
  rw [br]
  ring

theorem site_surj {k : Nat} (hk : 0<k) : Function.Surjective (ExactZip.site hk) := by
  intro i
  let b := i.val+k-4%k
  have hm := Nat.mod_lt 4 hk
  let j := idx hk b
  refine ⟨j,Fin.ext ?_⟩
  change (b%k+4)%k=i.val
  rw [Operands.mod_left,Nat.add_comm b 4,←Operands.mod_left]
  have h : 4%k+b=i.val+k := by dsimp [b];omega
  rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

theorem site_inj {k : Nat} (hk : 0<k) : Function.Injective (ExactZip.site hk) := by
  intro i j h
  have eq := congrArg (fun z => idx hk (z.val+k-4%k)) h
  change idx hk ((idx hk (i.val+4)).val+k-4%k)=
    idx hk ((idx hk (j.val+4)).val+k-4%k) at eq
  simp only [idx] at eq
  rw [Operands.back_after,Operands.back_after] at eq
  apply Fin.ext
  have e := congrArg Fin.val eq
  simpa [idx,Operands.idx,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using e

noncomputable def whereAt {k : Nat} (hk : 0<k) : Fin k≃Fin k :=
  Equiv.ofBijective (ExactZip.site hk) ⟨site_inj hk,site_surj hk⟩


end PEqualNP.Outside.L_meta_32570_aux.Model





namespace PEqualNP.Outside.L_meta_32570_aux.Expanded
open PEqualNP.Outside.L_meta_32570_aux.FieldRows

def width (k j : Nat) : Nat := (k+6)+(6+2*j)

theorem width_eq (k j : Nat) : width k j=k+12+2*j := by unfold width;omega

def iRaw {k j : Nat} : Fin (k+6)→Fin (width k j) := Fin.castAdd (6+2*j)
def iB {k j : Nat} : Fin 6→Fin (width k j) :=
  fun q=>Fin.natAdd (k+6) (Fin.castAdd (2*j) q)
def iZ {k j : Nat} : Fin (2*j)→Fin (width k j) :=
  fun q=>Fin.natAdd (k+6) (Fin.natAdd 6 q)

def readRaw {k j : Nat} (y : W (width k j)) (i : Fin (k+6)) : F := y (iRaw i)
def readB {k j : Nat} (y : W (width k j)) (i : Fin 6) : F := y (iB i)
def readZ {k j : Nat} (y : W (width k j)) (i : Fin (2*j)) : F := y (iZ i)

def initial {k : Nat} (l : Fin 6) : Fin (k+6) := ⟨l.val,by have := l.isLt;omega⟩
def terminal {k : Nat} (l : Fin 6) : Fin (k+6) := ⟨k+l.val,by have := l.isLt;omega⟩

def baseHead {k j : Nat} (y : W (width k j)) : W k :=
  Boundary.head (readRaw y)

def expand {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j) (x : W k) :
    W (width k j) :=
  Fin.addCases (Boundary.repeatWindow hk x) (Fin.addCases
    (fun l=>Boundary.repeatWindow hk x (initial l)) ((Checks.flatten j) (obs x)))

theorem expand_raw {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j)
    (x : W k) (i : Fin (k+6)) : readRaw (expand hk obs x) i=Boundary.repeatWindow hk x i := by
  simp [readRaw,iRaw,expand]

theorem expand_b {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j)
    (x : W k) (i : Fin 6) : readB (expand hk obs x) i=
      Boundary.repeatWindow hk x (initial i) := by
  simp [readB,iB,expand]

theorem expand_z {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j)
    (x : W k) (i : Fin (2*j)) : readZ (expand hk obs x) i=Checks.flatten j (obs x) i := by
  simp [readZ,iZ,expand]

theorem head_left {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j) (x : W k) :
    baseHead (expand hk obs x)=x := by
  change Boundary.head (readRaw (expand hk obs x))=x
  have r : readRaw (expand hk obs x)=Boundary.repeatWindow hk x := by
    funext i
    exact expand_raw hk obs x i
  rw [r,Boundary.head_repeat]

def Baseline {k j : Nat} (obs : W k→ₗ[F]Checks.Z j) (y : W (width k j)) : Prop :=
  (∀ l, readRaw y (initial l)=readB y l ∧ readRaw y (terminal l)=readB y l) ∧
  readZ y = Checks.flatten j (obs (baseHead y))

theorem baseline_iff {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j)
    (y : W (width k j)) :
    Baseline obs y ↔ y=expand hk obs (baseHead y) := by
  constructor
  · rintro ⟨rb,rz⟩
    have hy : Boundary.agrees (readRaw y) :=
      fun l=>(rb l).1.trans (rb l).2.symm
    have r : Boundary.repeatWindow hk (baseHead y)=readRaw y :=
      Boundary.agrees_periodic hk (readRaw y) hy
    funext p
    refine Fin.addCases (fun a=>?_) (Fin.addCases (fun b=>?_) (fun z=>?_)) p
    · change readRaw y a=readRaw (expand hk obs (baseHead y)) a
      rw [expand_raw,r]
    · change readB y b=readB (expand hk obs (baseHead y)) b
      rw [expand_b,r,(rb b).1]
    · change readZ y z=readZ (expand hk obs (baseHead y)) z
      rw [expand_z,rz]
  · intro y_eq
    have z : Baseline obs (expand hk obs (baseHead y)) := by
      constructor
      · intro l
        rw [expand_raw,expand_raw,expand_b]
        exact ⟨rfl,(Boundary.repeat_agrees hk (baseHead y) l).symm⟩
      · funext i
        rw [head_left]
        exact expand_z hk obs (baseHead y) i
    exact y_eq.symm ▸ z

def expandLin {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j) :
    W k→ₗ[F]W (width k j) where
  toFun := expand hk obs
  map_add' a b := by
    funext p
    refine Fin.addCases (fun i=>?_) (Fin.addCases (fun l=>?_) (fun z=>?_)) p
    · change readRaw (expand hk obs (a+b)) i=
        readRaw (expand hk obs a) i+readRaw (expand hk obs b) i
      simp [expand_raw,Boundary.repeatWindow,Pi.add_apply]
    · change readB (expand hk obs (a+b)) l=
        readB (expand hk obs a) l+readB (expand hk obs b) l
      simp [expand_b,Boundary.repeatWindow,Pi.add_apply]
    · change readZ (expand hk obs (a+b)) z=
        readZ (expand hk obs a) z+readZ (expand hk obs b) z
      simp [expand_z,map_add,Pi.add_apply]
  map_smul' c x := by
    funext p
    refine Fin.addCases (fun i=>?_) (Fin.addCases (fun l=>?_) (fun z=>?_)) p
    · change readRaw (expand hk obs (c•x)) i=c•readRaw (expand hk obs x) i
      simp [expand_raw,Boundary.repeatWindow,Pi.smul_apply]
    · change readB (expand hk obs (c•x)) l=c•readB (expand hk obs x) l
      simp [expand_b,Boundary.repeatWindow,Pi.smul_apply]
    · change readZ (expand hk obs (c•x)) z=c•readZ (expand hk obs x) z
      simp [expand_z,map_smul,Pi.smul_apply]

noncomputable def glueEquiv {k j : Nat} (hk : 0<k)
    (obs : W k→ₗ[F]Checks.Z j) (S : Submodule F (W k)) (E : Submodule F (W (width k j)))
    (kernel : ∀ y, y∈E ↔ Baseline obs y ∧ baseHead y∈S) :
    S≃ₗ[F]E := by
  let lm : S→ₗ[F]E :=
    LinearMap.codRestrict E ((expandLin hk obs).comp S.subtype) (fun x => by
      apply (kernel _).mpr
      change Baseline obs (expand hk obs x.val) ∧ baseHead (expand hk obs x.val)∈S
      rw [head_left]
      exact ⟨(baseline_iff hk obs _).mpr (by rw [head_left]),x.property⟩)
  refine LinearEquiv.ofBijective lm ⟨?_,?_⟩
  · intro a b eq
    apply Subtype.ext
    have h := congrArg (fun z : E=>baseHead z.val) eq
    change baseHead (expand hk obs a.val)=baseHead (expand hk obs b.val) at h
    rw [head_left,head_left] at h
    exact h
  · intro y
    obtain ⟨base,mem⟩ := (kernel _).mp y.property
    refine ⟨⟨baseHead y.val,mem⟩, Subtype.ext ?_⟩
    exact ((baseline_iff hk obs y.val).mp base).symm


end PEqualNP.Outside.L_meta_32570_aux.Expanded





namespace PEqualNP.Outside.L_meta_32570_aux.Direction
open PEqualNP.Outside.L_meta_32570_aux.Quadratic
open scoped BigOperators

section
variable {V U : Type*} [AddCommGroup V] [Module F V] [DecidableEq U]

structure Spec (U : Type*) (j : Nat) where
  who : Fin j→U
  pick : U→Fin 3
  checks : Finset (Fin (2^(2*j)))

def obs {j : Nat} (Q : Family V U) (who : Fin j→U) : V→ₗ[F]Checks.Z j :=
  LinearMap.pi (fun v=>LinearMap.pi (fun l=>if l.val=0 then Q.a (who v) else Q.b (who v)))

@[simp] theorem obs0 {j : Nat} (Q : Family V U) (who : Fin j→U) (x : V) (v : Fin j) :
    obs Q who x v 0=Q.a (who v) x := by rfl
@[simp] theorem obs1 {j : Nat} (Q : Family V U) (who : Fin j→U) (x : V) (v : Fin j) :
    obs Q who x v 1=Q.b (who v) x := by rfl

def productTarget {j : Nat} (z : Checks.Z j) (v : Fin j) : F := z v 0*z v 1

def passes {j : Nat} (e : Nat) (sp : Spec U j)
    (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F) : Prop :=
  ∀ z : Checks.Z j, (∀ m∈sp.checks, Checks.checkForm m z=0) →
    ((Finset.univ : Finset (Fin j)).filter (fun v=>productTarget z v≠A v z+b v)).card≤e

def space {j : Nat} (Q : Family V U) (marks : Finset U) (sp : Spec U j) :
    Submodule F V := by
  let C : Set V := Set.ofPred (fun x =>
    (∀ u ∈ marks, (∀ v, sp.who v ≠ u) →
      linearChoice (Q.a u) (Q.b u) (sp.pick u) x = 0) ∧
      (∀ m ∈ sp.checks, Checks.checkForm m (obs Q sp.who x) = 0))
  refine { carrier := C, zero_mem' := ?hzero, add_mem' := ?hadd, smul_mem' := ?hsmul }
  case hzero => simp [C,Set.mem_setOf_eq,map_zero]
  case hadd =>
    rintro x y ⟨xa,xb⟩ ⟨ya,yb⟩
    constructor
    · intro u um out
      rw [map_add,xa u um out,ya u um out,add_zero]
    · intro m mm
      rw [map_add,map_add,xb m mm,yb m mm,add_zero]
  case hsmul =>
    rintro a x ⟨xa,xb⟩
    constructor
    · intro u um out
      rw [map_smul,xa u um out,smul_zero]
    · intro m mm
      rw [map_smul,map_smul,xb m mm,smul_zero]

noncomputable def predD {j : Nat} (Q : Family V U) (sp : Spec U j)
    (A : Fin j→Dual (Checks.Z j)) (u : U) : Dual V := by
  classical
  exact if h : ∃ v, sp.who v=u then (A (Classical.choose h)).comp (obs Q sp.who)
    else exactChoice (Q.a u) (sp.pick u)

noncomputable def biasD {j : Nat} (sp : Spec U j) (b : Fin j→F) (u : U) : F := by
  classical
  exact if h : ∃ v, sp.who v=u then b (Classical.choose h) else 0

theorem at_exception {j : Nat} (Q : Family V U) (sp : Spec U j)
    (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F) (hinj : Function.Injective sp.who) (v : Fin j) :
    predD Q sp A (sp.who v)=(A v).comp (obs Q sp.who) ∧
      biasD sp b (sp.who v)=b v := by
  classical
  have h : ∃ w, sp.who w=sp.who v := ⟨v,rfl⟩
  have c := hinj (Classical.choose_spec h)
  simp [predD,biasD,h,c]

theorem error_subset {j : Nat} (Q : Family V U) (marks : Finset U) (sp : Spec U j)
    (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F) (hinj : Function.Injective sp.who)
    (e : Nat) (hp : passes e sp A b) (x : V) (hx : x∈space Q marks sp) :
    (marks.filter (fun u=>Q.a u x*Q.b u x≠predD Q sp A u x+biasD sp b u)).card≤e := by
  classical
  change (∀ u∈marks,(∀ v,sp.who v≠u)→
    linearChoice (Q.a u) (Q.b u) (sp.pick u) x=0) ∧
    (∀ m∈sp.checks,Checks.checkForm m (obs Q sp.who x)=0) at hx
  let z := obs Q sp.who x
  let errs := (Finset.univ : Finset (Fin j)).filter (fun v=>productTarget z v≠A v z+b v)
  have sub : (marks.filter (fun u=>Q.a u x*Q.b u x≠predD Q sp A u x+biasD sp b u))
      ⊆ errs.image sp.who := by
    intro u um
    obtain ⟨marked,err⟩ := Finset.mem_filter.mp um
    by_cases pick : ∃ v, sp.who v=u
    · obtain ⟨v,rfl⟩ := pick
      have eq := at_exception Q sp A b hinj v
      refine Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      simpa [z,productTarget] using (by simpa only [eq.1,eq.2,LinearMap.comp_apply] using err :
        Q.a (sp.who v) x*Q.b (sp.who v) x≠A v (obs Q sp.who x)+b v)
    · have all : ∀ v, sp.who v≠u := fun v bad=>pick ⟨v,bad⟩
      have t := exact_choice (Q.a u) (Q.b u) (sp.pick u) x (hx.1 u marked all)
      exact False.elim (err (by simpa [predD,biasD,pick] using t))
  exact (Finset.card_le_card sub).trans
    ((Finset.card_image_le (s:=errs) (f:=sp.who)).trans (hp z hx.2))

theorem build_tree {j : Nat} [Finite V]
    (Q : Family V U) (marks : Finset U) (sp : Spec U j)
    (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F) (hinj : Function.Injective sp.who)
    (e L : Nat) (hp : passes e sp A b)
    (budget : 2^Cell.codim (space Q marks sp)≤L) :
    ∃ tr : Cell.Tree V U, tr.nodes.card<L ∧
      ∀ x, (marks.filter (fun u=>target Q x u≠Cell.predict tr x u)).card≤e := by
  apply Cell.uniform (space Q marks sp) (target Q) marks e L budget
  intro x₀
  let pp (u : U) := predD Q sp A u+shiftLin Q x₀ u
  let oo (u : U) := biasD sp b u+shiftOff Q x₀ u-pp u x₀
  refine ⟨pp,oo,?_⟩
  intro x hx
  have changeFilter :
      (marks.filter (fun u=>target Q x u≠pp u x+oo u))=
      (marks.filter (fun u=>Q.a u (x-x₀)*Q.b u (x-x₀)≠
        predD Q sp A u (x-x₀)+biasD sp b u)) := by
    ext u
    simp only [Finset.mem_filter]
    exact and_congr_right' (lift_affine Q x₀ x u (predD Q sp A u) (biasD sp b u))
  rw [changeFilter]
  exact error_subset Q marks sp A b hinj e hp (x-x₀) hx

end

end PEqualNP.Outside.L_meta_32570_aux.Direction





namespace PEqualNP.Outside.L_meta_32570_aux.FromCell
open PEqualNP.Outside.L_meta_32570_aux.Quadratic PEqualNP.Outside.L_meta_32570_aux.Direction

section
variable {V U : Type*} [AddCommGroup V] [Module F V] [DecidableEq U]

theorem small_exception (Q : Family V U) (marks : Finset U) (S : Submodule F V)
    [Fintype S] (x₀ : V) (P : U→Dual V) (off : U→F) (e : Nat)
    (fit : ∀ t : S, (marks.filter (fun u=>target Q (x₀+t.val) u≠P u (x₀+t.val)+off u)).card≤e) :
    (Authentic.exceptional marks (fun u=>(Q.a u).comp S.subtype) (fun u=>(Q.b u).comp S.subtype)).card≤4*e := by
  let a (u : U) := (Q.a u).comp S.subtype
  let b (u : U) := (Q.b u).comp S.subtype
  let lin (u : U) := (shiftLin Q x₀ u-P u).comp S.subtype
  let c (u : U) := shiftOff Q x₀ u-(P u x₀+off u)
  apply Authentic.exception_count marks a b lin c e
  intro t
  have same : (marks.filter (fun u=>Authentic.err (a u) (b u) (lin u) (c u) t=true)) =
      marks.filter (fun u=>target Q (x₀+t.val) u≠P u (x₀+t.val)+off u) := by
    ext u
    simp only [Finset.mem_filter, Authentic.err,Authentic.bit_eq_true, a,b,lin,c,
      LinearMap.comp_apply,Submodule.subtype_apply]
    exact and_congr_right' (apply_residual Q x₀ t.val u P off).symm
  rw [same]
  exact fit t

theorem extract (Q : Family V U) (marks : Finset U) (S : Submodule F V)
    [Fintype S] [Finite V]
    (x₀ : V) (P : U→Dual V) (off : U→F) (e : Nat)
    (fit : ∀ t : S, (marks.filter (fun u=>target Q (x₀+t.val) u≠P u (x₀+t.val)+off u)).card≤e) :
    ∃ (j : Nat) (sp : Spec U j) (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F),
      j≤4*e ∧ Function.Injective sp.who ∧
      (∀ v, sp.who v∈marks) ∧ passes e sp A b ∧ S≤space Q marks sp := by
  classical
  let lhs (u : U) := (Q.a u).comp S.subtype
  let rhs (u : U) := (Q.b u).comp S.subtype
  let E := Authentic.exceptional marks lhs rhs
  let j := E.card
  have jbound : j≤4*e := small_exception Q marks S x₀ P off e fit
  let equiv : Fin j ≃ ↥E :=
    (Fintype.equivFinOfCardEq (by simp [j] : Fintype.card ↥E=j)).symm
  let who (v : Fin j) : U := (equiv v).val
  have injective : Function.Injective who := fun _ _ eq=>equiv.injective (Subtype.ext eq)
  have allMarked (v : Fin j) : who v∈marks :=
    ((Authentic.mem_exceptional marks lhs rhs (who v)).mp (equiv v).property).1
  have cover (u : U) (hu : u∈E) : ∃v, who v=u := by
    obtain ⟨v,hv⟩ := equiv.surjective ⟨u,hu⟩
    exact ⟨v,congrArg Subtype.val hv⟩
  let chooseRel (u : U) : Fin 3 := if lhs u=0 then 0 else if rhs u=0 then 1 else 2
  have clean (u : U) (um : u∈marks) (outside : ∀v, who v≠u) (t : S) :
      linearChoice (Q.a u) (Q.b u) (chooseRel u) t.val=0 := by
    by_cases hl : lhs u=0
    · have pin := LinearMap.congr_fun hl t
      change Q.a u t.val=0 at pin
      simpa [chooseRel,hl,linearChoice] using pin
    · by_cases hr : rhs u=0
      · have pin := LinearMap.congr_fun hr t
        change Q.b u t.val=0 at pin
        simpa [chooseRel,hl,hr,linearChoice] using pin
      · have same : lhs u=rhs u := by
          by_contra ne
          have hu : u∈E := (Authentic.mem_exceptional marks lhs rhs u).mpr ⟨um,hl,hr,ne⟩
          obtain ⟨v,hv⟩ := cover u hu
          exact outside v hv
        have pin : Q.a u t.val=Q.b u t.val := LinearMap.congr_fun same t
        have zero : Q.b u t.val+Q.b u t.val=0 := by
          rcases zero_or_one (Q.b u t.val) with zz|oo
          · rw [zz,zero_add]
          · rw [oo]; decide
        simpa [chooseRel,hl,hr,linearChoice,pin] using zero
  let obsS : S→ₗ[F]Checks.Z j := (obs Q who).comp S.subtype
  let checks := Checks.ofSubspace (LinearMap.range obsS)
  let sp : Spec U j := ⟨who,chooseRel,checks⟩
  let corrected (v : Fin j) : Dual S := ((P (who v))-shiftLin Q x₀ (who v)).comp S.subtype
  let cb (v : Fin j) : F := P (who v) x₀+off (who v)-shiftOff Q x₀ (who v)
  have fitEx (t : S) :
      ((Finset.univ : Finset (Fin j)).filter
        (fun v=>productTarget (obsS t) v≠corrected v t+cb v)).card≤e := by
    let wrong := (Finset.univ : Finset (Fin j)).filter
      (fun v=>productTarget (obsS t) v≠corrected v t+cb v)
    let old := marks.filter (fun u=>target Q (x₀+t.val) u≠P u (x₀+t.val)+off u)
    have sub : wrong.image who⊆old := by
      intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      refine Finset.mem_filter.mpr ⟨allMarked v,?_⟩
      have er := (Finset.mem_filter.mp hv).2
      rw [target_shift,map_add]
      change Q.a (who v) t.val*Q.b (who v) t.val+
          shiftLin Q x₀ (who v) t.val+shiftOff Q x₀ (who v) ≠
        (P (who v) x₀+P (who v) t.val)+off (who v)
      intro eq
      apply er
      simp only [productTarget, obsS, LinearMap.comp_apply,Submodule.subtype_apply,
        obs0,obs1,corrected,cb,LinearMap.sub_apply]

      linear_combination eq
    have hb := (Finset.card_le_card sub).trans (fit t)
    rw [Finset.card_image_of_injective _ injective] at hb
    exact hb
  obtain ⟨A,Afit⟩ := SectionBridge.transport obsS (Finset.univ : Finset (Fin j))
    productTarget corrected cb e fitEx
  refine ⟨j,sp,A,cb,jbound,injective,allMarked,?_,?_⟩
  · intro z hz
    have mem := (Checks.test_subspace (LinearMap.range obsS) z).mp hz
    exact Afit z mem
  · intro x hx
    let t : S := ⟨x,hx⟩
    change (∀ u∈marks, (∀ v, who v≠u) →
        linearChoice (Q.a u) (Q.b u) (chooseRel u) x=0) ∧
      (∀ m∈checks,Checks.checkForm m (obs Q who x)=0)
    refine ⟨fun u hu outside => clean u hu outside t,?_⟩
    have mem : obsS t∈LinearMap.range obsS := ⟨t,rfl⟩
    exact (Checks.test_subspace (LinearMap.range obsS) (obsS t)).mpr mem

theorem price_mono [Finite V] {S T : Submodule F V} (h : S≤T) :
    2^Cell.codim T≤2^Cell.codim S := by
  apply Nat.pow_le_pow_right (by decide)
  have a := Cell.sum_dim S
  have b := Cell.sum_dim T
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype T := Fintype.ofFinite T
  have i : Function.Injective (Submodule.inclusion h) := by
    intro x y eq
    have e := congrArg (fun z : T=>z.val) eq
    change x.val=y.val at e
    exact Subtype.ext e
  have bound : FiniteBinary.card S≤FiniteBinary.card T := by
    rw [FiniteBinary.card_eq,FiniteBinary.card_eq]
    exact Fintype.card_le_of_injective _ i
  rw [FiniteBinary.card_power S,FiniteBinary.card_power T] at bound
  have c := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bound
  omega

end
end PEqualNP.Outside.L_meta_32570_aux.FromCell



namespace PEqualNP.Outside.L_meta_32570_aux.Model
noncomputable def directionOf {k j : Nat} (hk : 0<k) (p : ExactZip.Pattern k j)
    (checks : Finset (Fin (2^(2*j)))) : Direction.Spec (Out k) j :=
  ⟨p.who,fun u=>p.pick ((whereAt hk).symm u.2) u.1,checks⟩

noncomputable def toPattern {k j : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool)
    (sp : Direction.Spec (Out k) j) : ExactZip.Pattern k j :=
  ⟨mark,sp.who,fun i b=>sp.pick (b,ExactZip.site hk i)⟩

theorem recovered {k j : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool)
    (sp : Direction.Spec (Out k) j) :
    directionOf hk (toPattern hk mark sp) sp.checks=sp := by
  cases sp with
  | mk who pick checks =>
    change Direction.Spec.mk who (fun u=>pick (u.1,ExactZip.site hk
      ((whereAt hk).symm u.2))) checks=Direction.Spec.mk who pick checks
    congr 1
    funext u
    have e : ExactZip.site hk ((whereAt hk).symm u.2)=u.2 :=
      (whereAt hk).apply_symm_apply u.2
    rw [e]

end PEqualNP.Outside.L_meta_32570_aux.Model



namespace PEqualNP.Outside.L_meta_32570_aux.Expanded
open PEqualNP.Outside.L_meta_32570_aux.FieldRows
theorem subtract_extra {k j : Nat} (hk : 0<k) (obs : W k→ₗ[F]Checks.Z j)
    (S : Submodule F (W k)) (E : Submodule F (W (width k j))) (r : Nat)
    (kernel : ∀ y, y∈E ↔ Baseline obs y ∧ baseHead y∈S)
    (rank : r+FiniteBinary.logdim E=width k j) :
    r-(12+2*j)=Cell.codim S := by
  have eq := FiniteBinary.card_congr (glueEquiv hk obs S E kernel).toEquiv
  have logeq : FiniteBinary.logdim S=FiniteBinary.logdim E := congrArg Nat.log2 eq
  have raw := Cell.sum_dim S
  have rk : FiniteBinary.logdim (W k)=k := by
    unfold FiniteBinary.logdim
    rw [FiniteBinary.card_pi,Nat.log2_two_pow]
  rw [rk] at raw
  rw [←logeq,width_eq] at rank
  omega

end PEqualNP.Outside.L_meta_32570_aux.Expanded




namespace PEqualNP.Outside.L_meta_32570_aux.Kind
open PEqualNP.Outside.L_meta_32570_aux.ExactZip PEqualNP.Outside.L_meta_32570_aux.Generators PEqualNP.Outside.L_meta_32570_aux.RankStream
open PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule

inductive Row (k j : Nat)
  | start (i : Fin 6)
  | stop (i : Fin 6)
  | clean (i : Fin k) (bank : Bool)
  | extra (i : Fin k) (bank : Bool) (v : Fin j) (second : Bool)
  | check (m : Fin (2^(2*j)))

def legal {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : Row k j→Prop
  | .start _ | .stop _ => True
  | .clean i b => p.mark b (site hk i)=true ∧ ∀ v, p.who v≠(b,site hk i)
  | .extra i b v _ => p.who v=(b,site hk i)
  | .check m => m∈checks

def code {k j : Nat} (p : Pattern k j) : Row k j→Nat
  | .start i => 2^i.val+2^(k+6+i.val)
  | .stop i => 2^(k+i.val)+2^(k+6+i.val)
  | .clean i b => 2^i.val*chosenMask b (p.pick i b)
  | .extra i b v false => 2^i.val*leftMask b+2^(k+12+2*v.val)
  | .extra i b v true => 2^i.val*rightMask b+2^(k+13+2*v.val)
  | .check m => 2^(k+12)*m.val

theorem mleft (b : Bool) : leftMask b<128 := by cases b <;> decide
theorem mright (b : Bool) : rightMask b<128 := by cases b <;> decide
theorem mclean (b : Bool) (p : Fin 3) : chosenMask b p<128 := by
  unfold chosenMask
  split
  · exact mleft b
  · split
    · exact mright b
    · exact Nat.xor_lt_two_pow (n:=7) (mleft b) (mright b)

theorem lower_part (i s m : Nat) (mB : m<128) (ib : i+7≤s) :
    2^i*m<2^s := by
  calc
    _ < 2^i*2^7 := Nat.mul_lt_mul_of_pos_left mB (Nat.two_pow_pos _)
    _ = 2^(i+7) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^s := Nat.pow_le_pow_right (by decide : 0<2) ib

theorem two_parts (m q ext : Nat) (a : m<2^q) (b : q<ext) : m+2^q<2^ext := by
  calc
    _ < 2^q+2^q := Nat.add_lt_add_right a _
    _ = 2^(q+1) := by rw [Nat.pow_succ];omega
    _ ≤ 2^ext := Nat.pow_le_pow_right (by decide : 0<2) (by omega)

theorem bounded {k j : Nat} (p : Pattern k j) (r : Row k j) :
    code p r<2^(k+12+2*j) := by
  cases r with
  | start i =>
    apply two_parts
    · exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
    · have := i.isLt;omega
  | stop i =>
    apply two_parts
    · exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
    · have := i.isLt;omega
  | clean i b => exact lower_part _ _ _ (mclean b _) (by have := i.isLt;omega)
  | extra i b v second =>
    have hi := i.isLt
    have hv := v.isLt
    cases second
    · exact two_parts _ _ _ (lower_part _ _ _ (mleft b) (by omega)) (by omega)
    · exact two_parts _ _ _ (lower_part _ _ _ (mright b) (by omega)) (by omega)
  | check m =>
    have b := Nat.mul_lt_mul_of_pos_left m.isLt (Nat.two_pow_pos (k+12))
    simpa only [code,←Nat.pow_add] using b

noncomputable def generators {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : List Nat :=
  (boundaryRows.map (Projection.pack 6 (k+6))) ++
    expanded (schedule (batches p hk) (boundaryRows++codes checks))

theorem exact_fold {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) :
    globalRows p hk checks=addRows rowsZero (generators p hk checks) := by
  have zer : widened 6 (k+6) (by omega) rowsZero=rowsZero := by
    apply rows_eq
    simp [widened,rowsMap,rowsZero,Projection.pack]
  have b : (batches p hk).length=k := by simp [batches]
  have widthChange :
      widened 6 ((batches p hk).length+6) (by omega) (addRows rowsZero boundaryRows) =
        widened 6 (k+6) (by omega) (addRows rowsZero boundaryRows) := by
    apply rows_eq
    change ((addRows rowsZero boundaryRows).data.map
      (Projection.pack 6 ((batches p hk).length+6))) =
      ((addRows rowsZero boundaryRows).data.map (Projection.pack 6 (k+6)))
    rw [b]
  unfold globalRows generators Replay.seedRows
  dsimp only
  rw [widthChange,addRows_append,widened_addRows,zer]

theorem generator_extent (n : Nat) (H : Rows) (rs : List Nat)
    (hH : ∀x∈H.data,x<2^n) (hR : ∀x∈rs,x<2^n) :
    ∀ x∈(addRows H rs).data,x<2^n := by
  induction rs generalizing H with
  | nil => exact hH
  | cons r rs ih =>
    apply ih (H:=add H r)
    · intro x hx
      rcases (Zipper.adjoin_image (·∈H.data) r x).mp ((mem_add H r x).mp hx) with old|⟨u,hu,rfl⟩
      · exact hH x old
      · exact Nat.xor_lt_two_pow (hH u hu) (hR r (by simp))
    · intro x hx
      exact hR x (by simp [hx])



def KindCover {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : Prop :=
  ∀ r, r∈generators p hk checks ↔ ∃ w : Row k j, legal p hk checks w ∧ code p w=r

theorem local_kind {k j : Nat} (p : Pattern k j) (hk : 0<k) (i : Fin k) (b : Bool) (m : Nat) :
    m∈localRows p hk i b ↔
      (legal p hk ∅ (.clean i b) ∧ m=chosenMask b (p.pick i b)) ∨
      (∃ v : Fin j, p.who v=(b,site hk i) ∧
        (m=leftMask b+2^(13+2*v.val) ∨ m=rightMask b+2^(14+2*v.val))) := by
  unfold localRows
  simp only [List.mem_append,List.mem_flatMap,legal]
  constructor
  · rintro (h|⟨v,hv,h⟩)
    · split at h
      · rename_i t
        exact .inl ⟨t,by simpa using h⟩
      · simp at h
    · split at h
      · rename_i t
        refine .inr ⟨v,t,?_⟩
        simpa [added] using h
      · simp at h
  · rintro (⟨a,rfl⟩|⟨v,eq,rfl|rfl⟩)
    · exact .inl (by simp [a])
    · exact .inr ⟨v,List.mem_finRange v,by simp [eq,added]⟩
    · exact .inr ⟨v,List.mem_finRange v,by simp [eq,added]⟩

theorem local_codes {k j : Nat} (p : Pattern k j) (hk : 0<k) (i : Fin k)
    (b : Bool) (m : Nat) (hm : m∈localRows p hk i b)
    (checks : Finset (Fin (2^(2*j)))) :
    ∃ w : Row k j, legal p hk checks w ∧ code p w =
      2^i.val*Projection.pack 7 (k+6-i.val) m := by
  rcases (local_kind p hk i b m).mp hm with ⟨clean,rfl⟩|⟨v,same,rfl|rfl⟩
  · exact ⟨.clean i b,clean,(clean_absolute _ _ _ (mclean _ _)).symm⟩
  · exact ⟨.extra i b v false,same,(operand_absolute k i.val _ _ i.isLt (mleft b)).symm⟩
  · refine ⟨.extra i b v true,same,?_⟩
    simp only [code]
    have e1 : 14+2*v.val=13+(1+2*v.val) := by omega
    have e2 : k+12+(1+2*v.val)=k+13+2*v.val := by omega
    rw [e1,operand_absolute k i.val _ _ i.isLt (mright b),e2]

theorem coverAll {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) : KindCover p hk checks := by
  intro r
  have len : (batches p hk).length=k := by simp [batches]
  have at_i (i : Fin k) :
      (batches p hk)[i.val]'(by rw [len];exact i.isLt)=
        localRows p hk i false++localRows p hk i true := by simp [batches]
  constructor
  · intro hu
    simp only [generators,List.mem_append,List.mem_map] at hu
    rcases hu with ⟨m,hm,rfl⟩|hu
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm
      have ll : l<6 := List.mem_range.mp hl
      refine ⟨.start ⟨l,ll⟩,trivial,?_⟩
      simpa only [code,Nat.add_comm 6 l] using (start_boundary k l ll).symm
    · rcases (mem_expanded _ _ _).mp hu with ⟨i,hi,m,hm,rfl⟩|⟨v,hv,rfl⟩
      · let f : Fin k := ⟨i,by rw [len] at hi;exact hi⟩
        have hl := at_i f
        change (batches p hk)[i]'hi = _ at hl
        rw [hl,List.mem_append] at hm
        rw [len]
        rcases hm with a|a
        · exact local_codes p hk f false m a checks
        · exact local_codes p hk f true m a checks
      · rw [len]
        rcases List.mem_append.mp hv with hv|hv
        · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
          have ll := List.mem_range.mp hl
          refine ⟨.stop ⟨l,ll⟩,trivial,?_⟩
          simpa only [code,Nat.add_comm 6 l] using (stop_boundary k l).symm
        · obtain ⟨w,wM,rfl⟩ := List.mem_map.mp hv
          exact ⟨.check w,Finset.mem_toList.mp wM,(check_absolute _ _).symm⟩
  · rintro ⟨w,hw,rfl⟩
    have add (i : Fin k) (b : Bool) (m : Nat) (hm : m∈localRows p hk i b) :
        2^i.val*Projection.pack 7 (k+6-i.val) m∈generators p hk checks := by
      apply List.mem_append_right
      apply (mem_expanded _ _ _).mpr
      refine .inl ⟨i.val,by rw [len];exact i.isLt,m,?_,by rw [len]⟩
      rw [at_i i,List.mem_append]
      cases b
      · exact .inl hm
      · exact .inr hm
    have endRow (r : Nat) (hr : r∈boundaryRows++codes checks) :
        2^k*r∈generators p hk checks := by
      apply List.mem_append_right
      apply (mem_expanded _ _ _).mpr
      exact .inr ⟨r,hr,by rw [len]⟩
    cases w with
    | start l =>
      rw [code,←start_boundary k l.val l.isLt]
      apply List.mem_append_left
      apply List.mem_map_of_mem
      exact List.mem_map.mpr ⟨l.val,List.mem_range.mpr l.isLt,by rw [Nat.add_comm l.val 6]⟩
    | stop l =>
      rw [code,←stop_boundary k l.val]
      exact endRow _ (List.mem_append_left _ (List.mem_map.mpr ⟨l.val,List.mem_range.mpr l.isLt,by rw [Nat.add_comm l.val 6]⟩))
    | clean i b =>
      rw [code,←clean_absolute k i.val _ (mclean b _)]
      exact add i b _ ((local_kind p hk i b _).mpr (.inl ⟨hw,rfl⟩))
    | extra i b v second =>
      cases second
      · rw [code,←operand_absolute k i.val _ _ i.isLt (mleft b)]
        exact add i b _ ((local_kind p hk i b _).mpr (.inr ⟨v,hw,.inl rfl⟩))
      · have a : k+13+2*v.val=k+12+(1+2*v.val) := by omega
        rw [code,a,←operand_absolute k i.val _ _ i.isLt (mright b)]
        have b' : 13+(1+2*v.val)=14+2*v.val := by omega
        rw [b']
        exact add i b _ ((local_kind p hk i b _).mpr (.inr ⟨v,hw,.inr rfl⟩))
    | check m =>
      rw [code,←check_absolute k]
      exact endRow _ (List.mem_append_right _ (List.mem_map.mpr ⟨m,Finset.mem_toList.mpr hw,rfl⟩))

theorem all_rows_extent {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) (kind : KindCover p hk checks) :
    ∀ r∈(globalRows p hk checks).data,r<2^(k+12+2*j) := by
  rw [exact_fold]
  apply generator_extent
  · intro r h
    have e : r=0 := by simpa [rowsZero] using h
    rw [e]
    exact Nat.two_pow_pos _
  · intro r h
    obtain ⟨w,_,rfl⟩ := (kind r).mp h
    exact bounded p w

end PEqualNP.Outside.L_meta_32570_aux.Kind





namespace PEqualNP.Outside.L_meta_32570_aux.Integration
open PEqualNP.Outside.L_meta_32570_aux.Model PEqualNP.Outside.L_meta_32570_aux.Quadratic PEqualNP.Outside.L_meta_32570_aux.Direction PEqualNP.Outside.L_meta_32570_aux.ExactZip

noncomputable def zipRank {k j : Nat} (hk : 0<k) (p : Pattern k j)
    (checks : Finset (Fin (2^(2*j)))) : Nat :=
  (last p hk).1 + (finalSpan p hk checks).card.log2 - (12+2*j)

def TreeFit {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k)
    (e L : Nat) : Prop :=
  ∃ tr : Cell.Tree (W k) (Out k), tr.nodes.card<L ∧ ∀ x,
    ((Finset.univ : Finset (Out k)).filter (fun u=> mark u.1 u.2=true ∧
      output hk mark row col c₁ c₂ x u≠Cell.predict tr x u)).card≤e

def LiteralFit {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (e L : Nat) : Prop :=
  ∃ (j : Nat) (who : Fin j→Out k), j≤4*e ∧ Function.Injective who ∧
    (∀ v, mark (who v).1 (who v).2=true) ∧
    ∃ (checks : Finset (Fin (2^(2*j)))) (A : Fin j→Dual (Checks.Z j)) (b : Fin j→F)
        (pick : Fin k→Bool→Fin 3),
      let p : Pattern k j := ⟨mark,who,pick⟩
      passes e (directionOf hk p checks) A b ∧ 2^zipRank hk p checks≤L

def PriceLaw {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k) : Prop :=
  ∀ j (who : Fin j→Out k) (pick : Fin k→Bool→Fin 3)
    (checks : Finset (Fin (2^(2*j)))),
    Function.Injective who → (∀ v, mark (who v).1 (who v).2=true) →
    let p : Pattern k j := ⟨mark,who,pick⟩
    zipRank hk p checks=Cell.codim (space (family hk row col c₁ c₂) (marked mark)
      (directionOf hk p checks))

theorem fit_equiv {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool)
    (row col c₁ c₂ : W k) (e L : Nat) (law : PriceLaw hk mark row col c₁ c₂) :
    TreeFit hk mark row col c₁ c₂ e L ↔ LiteralFit hk mark e L := by
  classical
  let Q := family hk row col c₁ c₂
  let M := marked mark
  have fchange (tr : Cell.Tree (W k) (Out k)) (x : W k) :
      ((Finset.univ : Finset (Out k)).filter (fun u=>mark u.1 u.2=true ∧
        output hk mark row col c₁ c₂ x u≠Cell.predict tr x u)) =
      M.filter (fun u=>target Q x u≠Cell.predict tr x u) := by
    ext u
    simp only [M,marked,Finset.mem_filter,Finset.mem_univ,true_and]
    apply and_congr_right
    intro hm
    have r := output_correct hk mark row col c₁ c₂ x u
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
    rw [r]
  constructor
  · rintro ⟨tr,nt,fit⟩
    obtain ⟨x₀,S,geom,price⟩ := Cell.largest tr L nt
    letI : Fintype S := Fintype.ofFinite S
    let P := tr.P (Cell.run tr x₀)
    let off := tr.off (Cell.run tr x₀)
    have hit (t : S) : Cell.run tr (x₀+t.val)=Cell.run tr x₀ := by
      apply (geom _).mpr
      simpa [add_comm x₀ t.val] using t.property
    have fitted (t : S) :
        (M.filter (fun u=>target Q (x₀+t.val) u≠P u (x₀+t.val)+off u)).card≤e := by
      have old := fit (x₀+t.val)
      rw [fchange] at old
      simpa only [Cell.predict,hit t] using old
    obtain ⟨j,sp,A,b,jbound,inj,all,tableOK,sub⟩ :=
      FromCell.extract Q M S x₀ P off e fitted
    have markedWho (v : Fin j) : mark (sp.who v).1 (sp.who v).2=true :=
      (Finset.mem_filter.mp (all v)).2
    let p := toPattern hk mark sp
    let pick := p.pick
    refine ⟨j,sp.who,jbound,inj,markedWho,sp.checks,A,b,pick,?_⟩
    change passes e (directionOf hk p sp.checks) A b ∧ 2^zipRank hk p sp.checks≤L
    have eq := law j sp.who pick sp.checks inj markedWho
    change zipRank hk p sp.checks=Cell.codim (space Q M (directionOf hk p sp.checks)) at eq
    rw [eq,recovered]
    exact ⟨tableOK,(FromCell.price_mono sub).trans price⟩
  · rintro ⟨j,who,_,inj,markedWho,checks,A,b,pick,pass,lim⟩
    let p : Pattern k j := ⟨mark,who,pick⟩
    let sp := directionOf hk p checks
    have eq := law j who pick checks inj markedWho
    change zipRank hk p checks=Cell.codim (space Q M sp) at eq
    have bound : 2^Cell.codim (space Q M sp)≤L := by
      rw [←eq]
      exact lim
    obtain ⟨tr,nt,fit⟩ := build_tree Q M sp A b inj e L pass bound
    refine ⟨tr,nt,?_⟩
    intro x
    rw [fchange]
    exact fit x

end PEqualNP.Outside.L_meta_32570_aux.Integration





namespace PEqualNP.Outside.L_meta_32570_aux.KindField
open scoped BigOperators
open PEqualNP.Outside.L_meta_32570_aux.Kind PEqualNP.Outside.L_meta_32570_aux.FieldRows PEqualNP.Outside.L_meta_32570_aux.ExactZip
open PEqualNP.Outside.L_meta_32570_aux.Expanded PEqualNP.Outside.L_meta_32570_aux.Quadratic PEqualNP.Outside.L_meta_32570_aux.Model

abbrev Word (n : Nat) := FieldRows.W n

theorem f2_eq (a b : ZMod 2) : a+b=0 ↔ a=b := by
  rcases scalars a with rfl|rfl <;> rcases scalars b with rfl|rfl <;> decide

theorem start_eq {k j : Nat} (p : Pattern k j) (l : Fin 6) (w : Word (width k j)) :
    evaluate (width k j) (Kind.code p (.start l)) w=readRaw w (initial l)+readB w l := by
  have h : (iRaw (j:=j) (initial (k:=k) l)).val < (iB (k:=k) (j:=j) l).val := by
    change l.val<k+6+l.val
    omega
  exact pair _ _ h w

theorem stop_eq {k j : Nat} (p : Pattern k j) (l : Fin 6) (w : Word (width k j)) :
    evaluate (width k j) (Kind.code p (.stop l)) w=readRaw w (terminal l)+readB w l := by
  have h : (iRaw (j:=j) (terminal (k:=k) l)).val < (iB (k:=k) (j:=j) l).val := by
    change k+l.val<k+6+l.val
    omega
  exact pair _ _ h w

theorem bit_oper {k : Nat} (hk : 0<k) (b second : Bool) (x : Word k) (i : Fin k) :
    Authentic.toBit ((if second then Model.b hk (b,site hk i)
      else Model.a hk (b,site hk i)) x) =
    Operands.op hk b second (fun t=>Authentic.toBit (x t)) i.val := by
  have sameSite : site hk i=Operands.site hk i.val := rfl
  rw [sameSite]
  cases b <;> cases second <;>
    simp [Model.a,Model.b,Model.coord,Model.y,Model.mix,Model.rot,Model.reindex,
      Model.idx,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.id_apply,
      Pi.add_apply,Authentic.bit_add,Operands.op,Operands.site,Operands.rot,Operands.mix]

theorem operand_eq {k j : Nat} (hk : 0<k) (i : Fin k) (bank second : Bool)
    (w : Word (width k j)) (x : Word k)
    (periodic : readRaw w=Boundary.repeatWindow hk x) :
    evaluate (width k j) (2^i.val*(if second then rightMask bank else leftMask bank)) w=
      ((if second then Model.b hk (bank,site hk i) else Model.a hk (bank,site hk i)) x) := by
  have large : i.val+6<width k j := by have := i.isLt; rw [width_eq];omega
  have same (d : Nat) (hd : d≤6) :
      w ⟨i.val+d,by omega⟩ = x (idx hk (i.val+d)) := by
    let loc : Fin (k+6) := ⟨i.val+d,by have := i.isLt;omega⟩
    exact congrFun periodic loc
  have bit_inj : Function.Injective Authentic.toBit := by
    intro a b h
    rcases Authentic.values a with rfl|rfl <;> rcases Authentic.values b with rfl|rfl <;> simp_all
  have same0 : w ⟨i.val,by omega⟩=x (Operands.idx k hk i.val) := by
    simpa [Model.idx] using same 0 (by decide)
  apply bit_inj
  rw [bit_oper]
  cases bank <;> cases second
  · simp only [leftMask,Bool.false_eq_true,ite_false,bank56 _ large, same 3 (by decide),
      same 4 (by decide),same 5 (by decide),Authentic.bit_add,Operands.first_false,
      Model.idx]
  · simp only [rightMask,Bool.false_eq_true,ite_true,ite_false,bank112 _ large, same 4 (by decide),
      same 5 (by decide),same 6 (by decide),Authentic.bit_add,Operands.second_false,Model.idx]
  · simp only [leftMask,Bool.false_eq_true,ite_true,ite_false,bank21 _ large, same0,
      same 2 (by decide),same 4 (by decide),Authentic.bit_add,Operands.first_true,Model.idx,Nat.add_zero]
  · simp only [rightMask,ite_true,bank42 _ large, same 1 (by decide),
      same 3 (by decide),same 5 (by decide),Authentic.bit_add,Operands.second_true,Model.idx]

theorem clean_eq {k j : Nat} (p : Pattern k j) (hk : 0<k) (w : Word (width k j))
    (x : Word k) (i : Fin k) (b : Bool) (periodic : readRaw w=Boundary.repeatWindow hk x) :
    evaluate (width k j) (Kind.code p (.clean i b)) w =
      linearChoice (Model.a hk (b,site hk i)) (Model.b hk (b,site hk i)) (p.pick i b) x := by
  by_cases h0 : (p.pick i b).val=0
  · simpa [Kind.code,chosenMask,linearChoice,h0] using
      operand_eq hk i b false w x periodic
  · by_cases h1 : (p.pick i b).val=1
    · simpa [Kind.code,chosenMask,linearChoice,h0,h1] using
        operand_eq hk i b true w x periodic
    · simp only [Kind.code,chosenMask,linearChoice,h0,h1,ite_false,mul_pow_xor,eval_xor,
        LinearMap.add_apply]
      simpa only [Bool.false_eq_true,ite_false,ite_true] using
        congrArg₂ (·+·) (operand_eq hk i b false w x periodic)
          (operand_eq hk i b true w x periodic)

theorem extra_eq {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (w : Word (width k j)) (x : Word k) (i : Fin k) (b : Bool)
    (v : Fin j) (second : Bool) (periodic : readRaw w=Boundary.repeatWindow hk x) :
    let l : Fin 2 := if second then 1 else 0
    evaluate (width k j) (Kind.code p (.extra i b v second)) w =
      ((if second then Model.b hk (b,site hk i) else Model.a hk (b,site hk i)) x) +
        readZ w (Checks.coord j (v,l)) := by
  let l : Fin 2 := if second then 1 else 0
  let z := iZ (k:=k) (Checks.coord j (v,l))
  have zz : z.val=k+12+2*v.val+l.val := by
    change (k+6)+(6+(Checks.coord j (v,l)).val)=_
    rw [Checks.coord_val]
    omega
  let m := if second then rightMask b else leftMask b
  have zv : z.val = if second then k+13+2*v.val else k+12+2*v.val := by
    rw [zz]
    cases second <;> simp [l] <;> omega
  have cn : Kind.code p (.extra i b v second)=2^i.val*m+2^z.val := by
    rw [zv]
    cases second <;> simp [m,Kind.code]
  change evaluate (width k j) _ w=_+w z
  rw [cn,packed_pow,eval_xor,LinearMap.add_apply,single,operand_eq hk i b second w x periodic]
  apply lower_part i.val z.val m
  · cases second <;> simp [m,mleft,mright]
  · have := i.isLt
    rw [zz]
    omega


theorem check_eq {k j : Nat} (p : Pattern k j) (w : Word (width k j))
    (m : Fin (2^(2*j))) :
    evaluate (width k j) (Kind.code p (.check m)) w =
      Checks.checkForm m ((Checks.flatten j).symm (readZ w)) := by
  rw [Kind.code,eval_apply]
  unfold width
  rw [Fin.sum_univ_add (a:=k+6) (b:=6+2*j),Fin.sum_univ_add (a:=6) (b:=2*j)]
  have aux (i : Nat) (hi : i<k+12) : (2^(k+12)*m.val).testBit i=false := by
    simp [Nat.testBit_two_pow_mul,show ¬ (k+12 ≤ i) by omega]
  have a : (∑ i : Fin (k+6), fbit ((2^(k+12)*m.val).testBit (iRaw (j:=j) i).val)*w (iRaw i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have lt : (iRaw (j:=j) i).val<k+12 := by
      change i.val<k+12
      have := i.isLt;omega
    rw [aux _ lt]
    simp [fbit]
  have b' : (∑ i : Fin 6, fbit ((2^(k+12)*m.val).testBit (iB (k:=k) (j:=j) i).val)*w (iB i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have lt : (iB (k:=k) (j:=j) i).val<k+12 := by
      change k+6+i.val<k+12
      have := i.isLt;omega
    rw [aux _ lt]
    simp [fbit]
  change
    ((∑ i : Fin (k+6), fbit ((2^(k+12)*m.val).testBit (iRaw (j:=j) i).val)*w (iRaw i)) +
      ((∑ i : Fin 6, fbit ((2^(k+12)*m.val).testBit (iB (k:=k) (j:=j) i).val)*w (iB i)) +
        (∑ i : Fin (2*j), fbit ((2^(k+12)*m.val).testBit (iZ (k:=k) i).val)*w (iZ i)))) = _
  rw [a,b',zero_add,zero_add]
  change _= evaluate (2*j) m.val ((Checks.flatten j) ((Checks.flatten j).symm (readZ w)))
  rw [LinearEquiv.apply_symm_apply,eval_apply]
  apply Finset.sum_congr rfl
  intro i _
  have e : (2^(k+12)*m.val).testBit (iZ (k:=k) i).val=m.val.testBit i.val := by
    change (2^(k+12)*m.val).testBit ((k+6)+(6+i.val))=_
    rw [show (k+6)+(6+i.val)=k+12+i.val by omega]
    simp [Nat.testBit_two_pow_mul]
  simpa only [e,readZ]

end PEqualNP.Outside.L_meta_32570_aux.KindField





namespace PEqualNP.Outside.L_meta_32570_aux.RowSpace
open scoped BigOperators
open PEqualNP.Outside.L_meta_32570_aux.RankStream PEqualNP.Outside.L_meta_32570_aux.Replay

abbrev F := ZMod 2

theorem scalar_cases (r : F) : r=0 ∨ r=1 := by
  change Fin 2 at r
  obtain ⟨n,hn⟩ := r
  have h : n=0 ∨ n=1 := by omega
  rcases h with h|h
  · exact .inl (Fin.ext h)
  · exact .inr (Fin.ext h)

section
variable {V : Type*} [AddCommGroup V] [Module F V]

def decoded (R : Rows) (f : Nat → Module.Dual F V)
    (f0 : f 0=0) (fa : ∀ a b, f (a^^^b)=f a+f b) :
    Submodule F (Module.Dual F V) := by
  let C : Set (Module.Dual F V) := Set.ofPred (fun d => ∃ x ∈ R.data, f x = d)
  refine { carrier := C, zero_mem' := ⟨0,R.zero,f0⟩, add_mem' := ?hadd, smul_mem' := ?hsmul }
  case hadd =>
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a^^^b,R.closed a ha b hb,fa a b⟩
  case hsmul =>
    intro r x hx
    rcases scalar_cases r with rfl|rfl
    · exact ⟨0,R.zero,by rw [zero_smul,f0]⟩
    · simpa only [one_smul] using hx

theorem decoded_kernel (R : Rows) (f : Nat→Module.Dual F V) (f0) (fa) (x : V) :
    x∈(decoded R f f0 fa).dualCoannihilator ↔ ∀ r∈R.data, f r x=0 := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h r hr
    exact h (f r) ⟨r,hr,rfl⟩
  · rintro h _ ⟨r,hr,rfl⟩
    exact h r hr

theorem kernel_adjoin (R : Rows) (f : Nat→Module.Dual F V) (f0) (fa)
    (x : V) (r : Nat) :
    x∈(decoded (add R r) f f0 fa).dualCoannihilator ↔
      x∈(decoded R f f0 fa).dualCoannihilator ∧ f r x=0 := by
  rw [decoded_kernel,decoded_kernel]
  constructor
  · intro all
    refine ⟨fun q h=>all q ((mem_add _ _ _).mpr (.inl h)),?_⟩
    apply all
    apply (mem_add _ _ _).mpr
    exact .inr (by simpa using R.zero)
  · rintro ⟨old,hr⟩ q hq
    rcases (PEqualNP.Outside.L_meta_32570_aux.Zipper.adjoin_image (·∈R.data) r q).mp ((mem_add R r q).mp hq)
      with o|⟨z,hz,rfl⟩
    · exact old q o
    · rw [fa,LinearMap.add_apply,old z hz,hr,zero_add]

noncomputable def decodedEquiv (R : Rows) (f : Nat→Module.Dual F V) (f0) (fa)
    (inj : ∀ x∈R.data, ∀ y∈R.data, f x=f y→x=y) :
    (asSet R : Type) ≃ decoded R f f0 fa :=
  Equiv.ofBijective (fun x=>⟨f x.val,⟨x.val,List.mem_toFinset.mp x.property,rfl⟩⟩)
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        exact inj a.val (List.mem_toFinset.mp a.property) b.val
          (List.mem_toFinset.mp b.property) (congrArg Subtype.val h)
      · rintro ⟨d,⟨r,hr,rfl⟩⟩
        exact ⟨⟨r,List.mem_toFinset.mpr hr⟩,rfl⟩)

theorem abstract_rank [Finite V] (D : Submodule F (Module.Dual F V)) [Finite D] :
    FiniteBinary.card (V⧸D.dualCoannihilator)=FiniteBinary.card D := by
  classical
  let C := FiniteBinary.chart D
  let n := C.d
  let B (i : Fin n) : D := C.eqv.symm (FieldRows.unit i)
  let M : V→ₗ[F]FieldRows.W n := LinearMap.pi (fun i => (B i).val)
  have unitImage (i : Fin n) : C.eqv (B i)=FieldRows.unit i :=
    C.eqv.apply_symm_apply _
  have spread (g : D) : (∑ i : Fin n, C.eqv g i • B i)=g := by
    apply C.eqv.injective
    simp only [map_sum,map_smul,unitImage]
    exact FieldRows.std_expand (C.eqv g)
  have surj : Function.Surjective M := by
    by_contra no
    have out : ∃ y : FieldRows.W n, y∉LinearMap.range M := by
      by_contra h
      apply no
      intro y
      by_contra a
      exact h ⟨y,a⟩
    obtain ⟨y,hy⟩ := out
    obtain ⟨g,zero_on,one_y⟩ :=
      LinearMap.exists_extend_of_notMem (0 : LinearMap.range M→ₗ[F]F) hy (1:F)
    let a : Fin n→F := fun i=>g (FieldRows.unit i)
    have value (z : FieldRows.W n) : g z=∑ i : Fin n, z i*a i := by
      have h := congrArg g (FieldRows.std_expand z)
      simpa only [a,map_sum,map_smul,smul_eq_mul] using h.symm
    have comb : (∑ i : Fin n, a i • B i)=0 := by
      apply Subtype.ext
      ext x
      have zero : g (M x)=0 :=
        LinearMap.congr_fun zero_on ⟨M x,⟨x,rfl⟩⟩
      rw [value] at zero
      change (↑(∑ i : Fin n, a i • B i) : Module.Dual F V) x=0
      simp only [Submodule.coe_sum,Submodule.coe_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
        LinearMap.zero_apply]
      exact (Finset.sum_congr rfl (fun i _=>mul_comm (a i) (M x i))).trans zero
    have y_zero := congrArg C.eqv comb
    simp only [map_sum,map_smul,unitImage,map_zero,FieldRows.std_expand] at y_zero
    have coeffZero (i : Fin n) : a i=0 := congrFun y_zero i
    apply (one_ne_zero : (1:F)≠0)
    rw [←one_y,value]
    simp [coeffZero]
  have ker : LinearMap.ker M=D.dualCoannihilator := by
    ext x
    rw [LinearMap.mem_ker,Submodule.mem_dualCoannihilator]
    constructor
    · intro h g hg
      let ev : D→ₗ[F]F :=
        { toFun := fun l=>l.val x
          map_add' := fun _ _=>rfl
          map_smul' := fun _ _=>rfl }
      have hv (i : Fin n) : ev (B i)=0 := congrFun h i
      have H := congrArg ev (spread ⟨g,hg⟩)
      have z : 0=ev (⟨g,hg⟩ : D) := by
        simpa only [map_sum,map_smul,hv,smul_zero,Finset.sum_const_zero] using H
      change 0=g x at z
      exact z.symm
    · intro h
      funext i
      exact h (B i).val (B i).property
  have eq := FiniteBinary.card_congr (M.quotKerEquivOfSurjective surj).toEquiv
  rw [ker,FiniteBinary.card_pi] at eq
  exact eq.trans (FiniteBinary.chart_card D).symm

theorem decoded_rank [Finite V] (R : Rows)
    (f : Nat→Module.Dual F V) (f0) (fa)
    (inj : ∀ x∈R.data, ∀ y∈R.data, f x=f y→x=y) :
    R.data.length.log2 + FiniteBinary.logdim (decoded R f f0 fa).dualCoannihilator =
      FiniteBinary.logdim V := by
  classical
  let D := decoded R f f0 fa
  let e := decodedEquiv R f f0 fa inj
  letI : Fintype D := Fintype.ofEquiv (asSet R) e
  have h := Fintype.card_congr e
  rw [Fintype.card_coe,card,←FiniteBinary.card_eq D] at h
  have eq := abstract_rank D
  have t := (FiniteBinary.quotient_log D.dualCoannihilator).symm
  unfold FiniteBinary.logdim at t ⊢
  rw [eq,←h] at t
  exact t

end
end PEqualNP.Outside.L_meta_32570_aux.RowSpace





namespace PEqualNP.Outside.L_meta_32570_aux.Price
open PEqualNP.Outside.L_meta_32570_aux.Expanded PEqualNP.Outside.L_meta_32570_aux.KindField PEqualNP.Outside.L_meta_32570_aux.Kind PEqualNP.Outside.L_meta_32570_aux.FieldRows
open PEqualNP.Outside.L_meta_32570_aux.Quadratic PEqualNP.Outside.L_meta_32570_aux.ExactZip PEqualNP.Outside.L_meta_32570_aux.RowSpace
open PEqualNP.Outside.L_meta_32570_aux.RankStream PEqualNP.Outside.L_meta_32570_aux.LiteralSchedule

abbrev Raw (k : Nat) := Fin k→ZMod 2

theorem fold_constraints {n : Nat} (H : Rows) (rs : List Nat) (w : Raw n) :
    w∈(decoded (addRows H rs) (evaluate n) (eval_zero n) (eval_xor n)).dualCoannihilator ↔
      w∈(decoded H (evaluate n) (eval_zero n) (eval_xor n)).dualCoannihilator ∧
      (∀ r∈rs,evaluate n r w=0) := by
  induction rs generalizing H with
  | nil => simp [addRows]
  | cons r rs ih =>
    change w∈(decoded (addRows (add H r) rs) _ _ _).dualCoannihilator ↔ _
    rw [ih,kernel_adjoin]
    constructor
    · rintro ⟨⟨a,b⟩,c⟩
      exact ⟨a,fun u hu=>(List.mem_cons.mp hu).elim (fun h=>h.symm ▸ b) (c u)⟩
    · rintro ⟨a,b⟩
      exact ⟨⟨a,b r (by simp)⟩,fun u hu=>b u (by simp [hu])⟩

def RowsZero {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) (w : Raw (width k j)) : Prop :=
  ∀ d : Row k j, legal p hk checks d → evaluate (width k j) (code p d) w=0

theorem global_constraints {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (checks : Finset (Fin (2^(2*j)))) (w : Raw (width k j)) :
    w∈(decoded (globalRows p hk checks) (evaluate (width k j))
      (eval_zero _) (eval_xor _)).dualCoannihilator ↔ RowsZero p hk checks w := by
  rw [exact_fold,fold_constraints]
  have z : w∈(decoded rowsZero (evaluate (width k j)) (eval_zero _) (eval_xor _)).dualCoannihilator := by
    rw [decoded_kernel]
    intro r hr
    have eq : r=0 := by simpa [rowsZero] using hr
    rw [eq,eval_zero,LinearMap.zero_apply]
  simp only [z,true_and]
  constructor
  · intro h d hd
    exact h _ ((coverAll p hk checks (code p d)).mpr ⟨d,hd,rfl⟩)
  · intro h r hr
    obtain ⟨d,hd,rfl⟩ := (coverAll p hk checks r).mp hr
    exact h d hd

theorem at_site {k : Nat} (hk : 0<k) (i : Fin k) :
    Model.whereAt hk i=site hk i := rfl

theorem inverse_at {k : Nat} (hk : 0<k) (i : Fin k) :
    site hk ((Model.whereAt hk).symm i)=i :=
  (Model.whereAt hk).apply_symm_apply i

theorem at_inverse {k : Nat} (hk : 0<k) (i : Fin k) :
    (Model.whereAt hk).symm (site hk i)=i :=
  (Model.whereAt hk).symm_apply_apply i

theorem rows_meaning {k j : Nat} (p : Pattern k j) (hk : 0<k)
    (row col c₁ c₂ : Raw k) (ch : Finset (Fin (2^(2*j))))
    (w : Raw (width k j)) :
    let Q := Model.family hk row col c₁ c₂
    let sp := Model.directionOf hk p ch
    let x := baseHead w
    RowsZero p hk ch w ↔ Baseline (Direction.obs Q p.who) w ∧
      x∈Direction.space Q (Model.marked p.mark) sp := by
  dsimp only
  let Q := Model.family hk row col c₁ c₂
  let sp := Model.directionOf hk p ch
  let obs := Direction.obs Q p.who
  let x := baseHead w
  have translatePick (i : Fin k) (b : Bool) : sp.pick (b,site hk i)=p.pick i b := by
    simp only [sp,Model.directionOf,at_inverse]
  constructor
  · intro h
    have edges (i : Fin 6) : readRaw w (initial i)=readB w i ∧ readRaw w (terminal i)=readB w i := by
      have a := h (.start i) trivial
      have b := h (.stop i) trivial
      rw [start_eq] at a
      rw [stop_eq] at b
      exact ⟨(f2_eq _ _).mp a,(f2_eq _ _).mp b⟩
    have hper : readRaw w=Boundary.repeatWindow hk x :=
      (Boundary.agrees_periodic hk (readRaw w) (fun i=>(edges i).1.trans (edges i).2.symm)).symm
    have tailEq : readZ w=Checks.flatten j (obs x) := by
      funext q
      let q' := (Checks.coord j).symm q
      let v := q'.1
      let l := q'.2
      let i := (Model.whereAt hk).symm (p.who v).2
      let b := (p.who v).1
      have wsite : p.who v=(b,site hk i) := by
        exact Prod.ext rfl (inverse_at hk _).symm
      have b0 : l=0 ∨ l=1 := by
        have lt := l.isLt
        have h : l.val=0 ∨ l.val=1 := by omega
        rcases h with a|a
        · exact Or.inl (Fin.ext a)
        · exact Or.inr (Fin.ext a)
      have eqQ : Checks.coord j (v,l)=q := (Checks.coord j).apply_symm_apply q
      have flat : ∀ z : Fin 2, Checks.flatten j (obs x) (Checks.coord j (v,z))=obs x v z := by
        intro z
        simp [Checks.flatten]
      rcases b0 with e|e
      · have z := h (.extra i b v false) wsite
        rw [extra_eq p hk w x i b v false hper] at z
        change Model.a hk (b,site hk i) x+readZ w (Checks.coord j (v,0))=0 at z
        have z' := ((f2_eq _ _).mp z).symm
        rw [←eqQ,e,flat,Direction.obs0,wsite]
        exact z'
      · have z := h (.extra i b v true) wsite
        rw [extra_eq p hk w x i b v true hper] at z
        change Model.b hk (b,site hk i) x+readZ w (Checks.coord j (v,1))=0 at z
        have z' := ((f2_eq _ _).mp z).symm
        rw [←eqQ,e,flat,Direction.obs1,wsite]
        exact z'
    refine ⟨⟨edges,tailEq⟩,?_⟩
    change (∀ u∈Model.marked p.mark,(∀v,p.who v≠u)→
        linearChoice (Q.a u) (Q.b u) (sp.pick u) x=0) ∧
      (∀ m∈ch,Checks.checkForm m (obs x)=0)
    constructor
    · rintro ⟨b,s⟩ marked outside
      let i := (Model.whereAt hk).symm s
      have eq : site hk i=s := inverse_at hk _
      have valid : legal p hk ch (.clean i b) := by
        change p.mark b (site hk i)=true ∧ ∀ v, p.who v≠(b,site hk i)
        rw [eq]
        exact ⟨(Finset.mem_filter.mp marked).2,outside⟩
      have rowZero := h (.clean i b) valid
      rw [clean_eq p hk w x i b hper,eq] at rowZero
      have pEq := translatePick i b
      rw [eq] at pEq
      rw [pEq]
      exact rowZero
    · intro m hm
      have z := h (.check m) hm
      rwa [check_eq,tailEq,LinearEquiv.symm_apply_apply] at z
  · rintro ⟨base,hit⟩ d hd
    change (∀ u∈Model.marked p.mark,(∀v,p.who v≠u) →
        linearChoice (Q.a u) (Q.b u) (sp.pick u) x=0) ∧
      (∀ m∈ch,Checks.checkForm m (obs x)=0) at hit
    have hper : readRaw w=Boundary.repeatWindow hk x :=
      (Boundary.agrees_periodic hk (readRaw w) (fun i=>(base.1 i).1.trans (base.1 i).2.symm)).symm
    cases d with
    | start l =>
      rw [start_eq]
      exact (f2_eq _ _).mpr (base.1 l).1
    | stop l =>
      rw [stop_eq]
      exact (f2_eq _ _).mpr (base.1 l).2
    | clean i b =>
      change p.mark b (site hk i)=true ∧ (∀ v,p.who v≠(b,site hk i)) at hd
      rw [clean_eq p hk w x i b hper,←translatePick]
      exact hit.1 (b,site hk i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.1⟩) hd.2
    | extra i b v second =>
      change p.who v=(b,site hk i) at hd
      rw [extra_eq p hk w x i b v second hper]
      let l : Fin 2 := if second then 1 else 0
      have flat : readZ w (Checks.coord j (v,l))=obs x v l := by
        rw [base.2]
        simp [Checks.flatten,obs,Q,x]
      change _ + readZ w (Checks.coord j (v,l))=0
      rw [flat]
      apply (f2_eq _ _).mpr
      cases second
      · simp [l,obs,Direction.obs0,hd,Q,Model.family]
      · simp [l,obs,Direction.obs1,hd,Q,Model.family]
    | check m =>
      rw [check_eq,base.2,LinearEquiv.symm_apply_apply]
      exact hit.2 m hd

theorem law {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool)
    (row col c₁ c₂ : Raw k) : Integration.PriceLaw hk mark row col c₁ c₂ := by
  intro j who pick checks _ _
  let p : Pattern k j := ⟨mark,who,pick⟩
  let n := width k j
  let H := globalRows p hk checks
  let E := (decoded H (evaluate n) (eval_zero n) (eval_xor n)).dualCoannihilator
  let Q := Model.family hk row col c₁ c₂
  let S := Direction.space Q (Model.marked mark) (Model.directionOf hk p checks)
  have b := all_rows_extent p hk checks (coverAll p hk checks)
  rw [←width_eq] at b
  have h := decoded_rank H (evaluate n) (eval_zero _) (eval_xor _) (fun r hr t ht=>eval_inj (b r hr) (b t ht))
  have raw : FiniteBinary.logdim (W n)=n := by
    unfold FiniteBinary.logdim
    rw [FiniteBinary.card_pi,Nat.log2_two_pow]
  rw [raw] at h
  have g (w : Raw n) : w∈E ↔ Baseline (Direction.obs Q who) w ∧ baseHead w∈S :=
    (global_constraints p hk checks w).trans (rows_meaning p hk row col c₁ c₂ checks w)
  have p' := subtract_extra hk (Direction.obs Q who) S E H.data.length.log2 g h
  rw [show H.data.length.log2=(last p hk).1+(finalSpan p hk checks).card.log2 from global_price p hk checks] at p'
  exact p'

end PEqualNP.Outside.L_meta_32570_aux.Price



open scoped BigOperators



namespace PEqualNP.Outside.L_meta_32570_aux.Wrapper

abbrev F := ZMod 2
abbrev W (k : Nat) := Fin k→F
abbrev O (k : Nat) := Bool×Fin k

def literalOutput {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k)
    (x : W k) (b : Bool) (i : Fin k) : F :=
  let ix := fun j : Nat => (⟨j%k,Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W k) (i : Fin k) => x (ix (i.val+k-s%k))
  let mix := fun (g : Nat) (x : W k) (i : Fin k) => x i+x (ix (i.val+g))+x (ix (i.val+k-g%k))
  let step := fun (x : W k) (i : Fin k) => x i+(1+x (ix (i.val+1)))*x (ix (i.val+2))
  if mark b i then
    if b then step (mix 2 (rot 3 x+col)) i+rot 4 x i+c₂ i
    else step (mix 1 (rot 1 x+row)) i+x i+c₁ i
  else 0

theorem sameOutput {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k)
    (x : W k) (b : Bool) (i : Fin k) :
    literalOutput hk mark row col c₁ c₂ x b i = Model.output hk mark row col c₁ c₂ x (b,i) := by
  cases b <;> rfl

theorem sameOutputPair {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool) (row col c₁ c₂ : W k)
    (x : W k) (u : O k) :
    literalOutput hk mark row col c₁ c₂ x u.1 u.2 = Model.output hk mark row col c₁ c₂ x u := by
  obtain ⟨b,i⟩ := u
  exact sameOutput hk mark row col c₁ c₂ x b i

theorem leftPacking {k : Nat} (hk : 0<k) (mark : Bool→Fin k→Bool)
    (row col c₁ c₂ : W k) (e L : Nat) :
    (∃ (T : Finset (List Bool)) (ask : List Bool→W k→ₗ[F]F) (shift : List Bool→F)
        (P : List Bool→O k→W k→ₗ[F]F) (off : List Bool→O k→F),
      T.card<L ∧ ∀ x : W k,
        let p := (List.range T.card).foldl (fun (p : List Bool) _ =>
          if p∈T then p++[decide (ask p x+shift p≠0)] else p) []
        ((Finset.univ : Finset (O k)).filter (fun u=>mark u.1 u.2=true ∧
          literalOutput hk mark row col c₁ c₂ x u.1 u.2≠P p u x+off p u)).card≤e) ↔
    Integration.TreeFit hk mark row col c₁ c₂ e L := by
  constructor
  · rintro ⟨T,ask,shift,P,off,bound,h⟩
    let tr : Cell.Tree (W k) (O k) := ⟨T,ask,shift,P,off⟩
    refine ⟨tr,bound,?_⟩
    intro x
    apply le_of_eq_of_le ?_ (h x)
    apply congrArg Finset.card
    ext u
    repeat rw [Finset.mem_filter]
    all_goals simp only [Finset.mem_univ,true_and,sameOutputPair,Cell.predict,Cell.run,Cell.answerBit,tr]
  · rintro ⟨tr,bound,h⟩
    refine ⟨tr.nodes,tr.ask,tr.shift,tr.P,tr.off,bound,?_⟩
    intro x
    apply le_of_eq_of_le ?_ (h x)
    apply congrArg Finset.card
    ext u
    repeat rw [Finset.mem_filter]
    all_goals simp only [Finset.mem_univ,true_and,sameOutputPair,Cell.predict,Cell.run,Cell.answerBit]

end PEqualNP.Outside.L_meta_32570_aux.Wrapper



theorem PEqualNP.Outside.L_meta_32570 :
∀ (k : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val+g)) + x (ix (i.val+k-g % k))
  let step := fun (x : W) (i : Fin k) => x i + (1+x (ix (i.val+1))) * x (ix (i.val+2))
  let D := W →ₗ[F] F
  let seed := (Finset.range 64).image (fun v => v + 64*v)
  let adjoin := fun (s : Finset ℕ) (v : ℕ) => s ∪ s.image (fun u => u ^^^ v)
  ∀ (mark : Bool → Fin k → Bool) (row col c₁ c₂ : W) (e L : Nat),
    let target := fun (x : W) (b : Bool) (i : Fin k) =>
      if mark b i then
        if b then step (mix 2 (rot 3 x + col)) i + rot 4 x i + c₂ i
        else step (mix 1 (rot 1 x + row)) i + x i + c₁ i
      else 0
    let run := fun (T : Finset (List Bool)) (ask : List Bool → D)
        (shift : List Bool → F) (x : W) =>
      (List.range T.card).foldl (fun (p : List Bool) _ =>
        if p ∈ T then p ++ [decide (ask p x+shift p ≠ 0)] else p) []
    (∃ (T : Finset (List Bool)) (ask : List Bool → D) (shift : List Bool → F)
        (P : List Bool → Bool × Fin k → D) (off : List Bool → Bool × Fin k → F),
      T.card < L ∧ ∀ x : W,
        let p := run T ask shift x
        ((Finset.univ : Finset (Bool × Fin k)).filter (fun u =>
          mark u.1 u.2 = true ∧ target x u.1 u.2 ≠ P p u x+off p u)).card ≤ e) ↔
    ∃ (j : Nat) (who : Fin j → Bool × Fin k), j ≤ 4*e ∧ Function.Injective who ∧
      (∀ v, mark (who v).1 (who v).2 = true) ∧
      let Z := Fin j → Fin 2 → F
      ∃ (checks : Finset (Fin (2^(2*j)))) (A : Fin j → Z →ₗ[F] F) (b : Fin j → F)
          (pick : Fin k → Bool → Fin 3),
        (∀ z : Z, (∀ mask ∈ checks, (∑ v : Fin j, ∑ l : Fin 2,
          if mask.val.testBit (2*v.val+l.val) then z v l else 0) = 0) →
          ((Finset.univ : Finset (Fin j)).filter
            (fun v => z v 0*z v 1 ≠ A v z+b v)).card ≤ e) ∧
        let put := fun (st : Finset Nat) (i : Fin k) (colSide : Bool) =>
          let site := ix (i.val+4)
          let u : Nat := if colSide then 21 else 56
          let v : Nat := if colSide then 42 else 112
          let clean := if mark colSide site = true ∧ (∀ l, who l ≠ (colSide,site))
            then adjoin st (if (pick i colSide).val = 0 then u
              else if (pick i colSide).val = 1 then v else u ^^^ v) else st
          (List.finRange j).foldl (fun span l => if who l = (colSide,site) then
            adjoin (adjoin span (u + 2^(13+2*l.val))) (v + 2^(14+2*l.val))
            else span) clean
        let last := (List.finRange k).foldl (fun (st : Nat × Finset Nat) i =>
          let shifted := st.2.image (fun v => v % 64 + 128*(v / 64))
          let both := put (put shifted i false) i true
          let even := both.filter (fun v => v % 2 = 0)
          (st.1 + (if even = both then 0 else 1), even.image (fun v => v / 2)))
          ((0,seed) : Nat × Finset Nat)
        let closed := last.2.biUnion (fun v => seed.image (fun u => v ^^^ u))
        let finalSpan := checks.toList.foldl (fun st mask => adjoin st (4096*mask.val)) closed
        2^(last.1 + Nat.log2 finalSpan.card - (12+2*j)) ≤ L := by
  intro k hk
  dsimp only
  intro mark row col c₁ c₂ e L
  have parsed := (PEqualNP.Outside.L_meta_32570_aux.Wrapper.leftPacking hk mark row col c₁ c₂ e L).trans
    (PEqualNP.Outside.L_meta_32570_aux.Integration.fit_equiv hk mark row col c₁ c₂ e L
      (PEqualNP.Outside.L_meta_32570_aux.Price.law hk mark row col c₁ c₂))
  apply parsed.trans
  constructor
  · rintro ⟨j,who,jbound,inj,markedWho,checks,A,b,pick,table,bound⟩
    refine ⟨j,who,jbound,inj,markedWho,checks,A,b,pick,?_,?_⟩
    · intro z hz
      have q := table z (by
        intro m hm
        rw [PEqualNP.Outside.L_meta_32570_aux.Checks.check_literal]
        exact hz m hm)
      apply le_of_eq_of_le ?_ q
      apply congrArg Finset.card
      ext v
      repeat rw [Finset.mem_filter]
      all_goals simp only [Finset.mem_univ,true_and,PEqualNP.Outside.L_meta_32570_aux.Direction.productTarget]
    · exact bound
  · rintro ⟨j,who,jbound,inj,markedWho,checks,A,b,pick,table,bound⟩
    refine ⟨j,who,jbound,inj,markedWho,checks,A,b,pick,?_,?_⟩
    · intro z hz
      have q := table z (by
        intro m hm
        rw [←PEqualNP.Outside.L_meta_32570_aux.Checks.check_literal]
        exact hz m hm)
      apply le_of_eq_of_le ?_ q
      apply congrArg Finset.card
      ext v
      repeat rw [Finset.mem_filter]
      all_goals simp only [Finset.mem_univ,true_and,PEqualNP.Outside.L_meta_32570_aux.Direction.productTarget]
    · exact bound
