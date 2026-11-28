import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32042

abbrev Family (n m q : Nat) := Fin q → Fin n → Fin m → Bool

def anchor {n m q} (a : Fin n) (b : Fin m) (T : Family n m q) : Family n m q :=
  fun i x y => xor (xor (T i x y) (T i x b)) (xor (T i a y) (T i a b))

def planes (d : Nat) := ((2^d-1)*(2^d-2))/6

theorem anchored_card {n m q} (a : Fin n) (b : Fin m) (H : Finset (Family n m q)) :
    (H.image (anchor a b)).card ≤ 2 ^ (q * ((n-1)*(m-1))) := by
  classical
  let U := H.image (anchor a b)
  let project := fun (T : Family n m q) (i : Fin q) (x : {x : Fin n // x ≠ a})
    (y : {y : Fin m // y ≠ b}) => T i x.val y.val
  have inj : Set.InjOn project U := by
    intro f hf g hg h
    obtain ⟨f', _, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨g', _, rfl⟩ := Finset.mem_image.mp hg
    funext i x y
    by_cases hx : x = a
    · subst x; simp [anchor]
    by_cases hy : y = b
    · subst y; simp [anchor]
    exact congrFun (congrFun (congrFun h i) ⟨x,hx⟩) ⟨y,hy⟩
  have cardOff {k} (v : Fin k) : Fintype.card {x : Fin k // x ≠ v} = k-1 := by
    simpa using Fintype.card_subtype_compl (fun x : Fin k => x = v)
  calc
    U.card = (U.image project).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ _ := (U.image project).card_le_univ
    _ = _ := by simp [Fintype.card_fun, cardOff, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm]

theorem large_budget {n m q s} (a : Fin n) (b : Fin m) (H : Finset (Family n m q))
    (hs : (n-1)*(m-1) ≤ s) :
    (H.image (anchor a b)).card ≤ 2^(q * min s ((n-1)*(m-1))) *
      ∏ i ∈ Finset.range s, (1 + planes (min (n*m-1) (n+m-2+i))) := by
  rw [min_eq_right hs]
  apply (anchored_card a b H).trans
  have pos : 0 < ∏ i ∈ Finset.range s, (1 + planes (min (n*m-1) (n+m-2+i))) :=
    Finset.prod_pos fun i _ => by omega
  exact Nat.le_mul_of_pos_right _ pos

end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

abbrev Tab (X : Type) := X → ZMod 2
abbrev Space (X : Type) := Finset (Tab X)

def Closed {X} (W : Space X) : Prop :=
  0 ∈ W ∧ ∀ u ∈ W, ∀ v ∈ W, u + v ∈ W

theorem twoZero {X} (t : Tab X) : t + t = 0 := by
  funext i; change t i + t i = 0
  exact CharTwo.add_self_eq_zero _

theorem squareEq {X} (t : Tab X) : t*t = t := by
  have e : ∀ z : ZMod 2, z*z=z := by decide
  funext i; exact e _

section
variable {X : Type} [Fintype X] [DecidableEq X]

def extend (W : Space X) (z : Tab X) : Space X :=
  W ∪ W.image (fun t => t + z)

theorem mem_extend (W : Space X) (z t : Tab X) :
    t ∈ extend W z ↔ t ∈ W ∨ ∃ u ∈ W, u+z=t := by simp only [extend,Finset.mem_union,Finset.mem_image]

theorem add_mem_base {W : Space X} (hW : Closed W) {u v z : Tab X}
    (hu : u ∈ W) (hv : v ∈ extend W z) : u+v ∈ extend W z := by
  rcases (mem_extend ..).mp hv with hb | ⟨t,ht,rfl⟩
  · exact (mem_extend ..).mpr (.inl (hW.2 _ hu _ hb))
  · exact (mem_extend ..).mpr (.inr ⟨u+t,hW.2 _ hu _ ht,add_assoc ..⟩)

theorem extend_closed {W : Space X} (hW : Closed W) (z : Tab X) :
    Closed (extend W z) := by
  refine ⟨(mem_extend ..).mpr (.inl hW.1), ?_⟩
  intro u hu v hv
  rcases (mem_extend ..).mp hu with hb | ⟨t,ht,rfl⟩
  · exact add_mem_base hW hb hv
  rcases (mem_extend ..).mp hv with hb | ⟨s,hs,rfl⟩
  · rw [add_comm]; exact add_mem_base hW hb ((mem_extend ..).mpr (.inr ⟨_,ht,rfl⟩))
  · have e : t+z+(s+z)=t+s := by calc
          _ = (t+s)+(z+z) := by abel
          _ = _ := by rw [twoZero,add_zero]
    rw [e]; exact (mem_extend ..).mpr (.inl (hW.2 _ ht _ hs))

theorem extend_member {W : Space X} (hW : Closed W) {z : Tab X} (hz : z ∈ W) :
    extend W z = W := by
  ext t; rw [mem_extend]
  constructor
  · rintro (ht | ⟨u,hu,rfl⟩)
    · exact ht
    · exact hW.2 _ hu _ hz
  · exact Or.inl

theorem extend_shift {W : Space X} (hW : Closed W) {u : Tab X} (hu : u ∈ W) (z : Tab X) :
    extend W (u+z) = extend W z := by
  ext t; rw [mem_extend,mem_extend]
  constructor
  · rintro (ht | ⟨v,hv,rfl⟩)
    · exact .inl ht
    · exact .inr ⟨v+u,hW.2 _ hv _ hu,add_assoc ..⟩
  · rintro (ht | ⟨v,hv,rfl⟩)
    · exact .inl ht
    · refine .inr ⟨v+u,hW.2 _ hv _ hu,?_⟩
      calc
        _ = (v+z)+(u+u) := by abel
        _ = _ := by rw [twoZero,add_zero]

def pairs (W : Space X) := (W.erase 0).offDiag
def children (W : Space X) : Finset (Space X) :=
  insert W ((pairs W).image fun p => extend W (p.1*p.2))

theorem child_of_mem {W : Space X} (hW : Closed W) {u v : Tab X} (hu : u ∈ W) (hv : v ∈ W) :
    extend W (u*v) ∈ children W := by
  by_cases h : u=0 ∨ v=0 ∨ u=v
  · rcases h with rfl | rfl | rfl <;>
      simp [children, squareEq, extend_member hW hW.1, extend_member hW hu, *]
  obtain ⟨h0,h1,h2⟩ : u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by tauto
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(u,v),by simp [pairs,Finset.mem_offDiag,h0,h1,h2,hu,hv],rfl⟩

theorem child_count {W : Space X} (hW : Closed W) :
    (children W).card ≤ 1 + ((W.card-1)*(W.card-2))/6 := by
  classical
  let f := fun (p : Tab X × Tab X) => extend W (p.1*p.2)
  let T := (pairs W).image f
  have fibers (Y) (hY : Y ∈ T) : 6 ≤ ((pairs W).filter fun p => f p=Y).card := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hY
    have hh : (a≠0 ∧ a∈W) ∧ (b≠0 ∧ b∈W) ∧ a≠b := by
      simpa only [pairs,Finset.mem_offDiag,Finset.mem_erase] using hab
    obtain ⟨⟨ha,aw⟩,⟨hb,bw⟩,ab⟩ := hh
    let c := a+b
    have cw : c ∈ W := hW.2 _ aw _ bw
    have ca : c≠a := by simpa [c] using hb
    have cb : c≠b := by simpa [c] using ha
    have cz : c≠0 := by
      intro eq
      have e : c+b=a := by simp only [c,add_assoc,twoZero,add_zero]
      rw [eq,zero_add] at e
      exact ab e.symm
    have ac : extend W (a*c) = extend W (a*b) := by rw [show a*c=a+a*b by rw [show c=a+b from rfl,mul_add,squareEq],extend_shift hW aw]
    have bc : extend W (b*c) = extend W (a*b) := by rw [show b*c=b+a*b by rw [show c=a+b from rfl,mul_add,squareEq,mul_comm b a,add_comm],extend_shift hW bw]
    let S : Finset (Tab X × Tab X) := {(a,b),(b,a),(a,c),(c,a),(b,c),(c,b)}
    have sc : S.card=6 := by simp [S,ab,ab.symm,ca,ca.symm,cb,cb.symm]
    rw [← sc]
    apply Finset.card_le_card
    intro p hp
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [pairs,Finset.mem_offDiag,f,ha,hb,cz,aw,bw,cw,ab,ab.symm,ca,ca.symm,cb,cb.symm,ac,bc,mul_comm b a,mul_comm c a,mul_comm c b]
  have six : T.card*6 ≤ (pairs W).card := by
    rw [Finset.card_eq_sum_card_image f (pairs W)]
    simpa only [Finset.sum_const, smul_eq_mul] using Finset.sum_le_sum (s:=T) fibers
  have count : (pairs W).card = (W.card-1)*(W.card-2) := by
    simp only [pairs,Finset.offDiag_card,Finset.card_erase_of_mem hW.1]
    conv_rhs => rw [show W.card-2=W.card-1-1 by omega,Nat.mul_sub_left_distrib,Nat.mul_one]
  have bound := (Nat.le_div_iff_mul_le (by decide : 0<6)).mpr (six.trans_eq count)
  exact (Finset.card_insert_le ..).trans (by change T.card+1 ≤ _; omega)

end
end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

variable {X : Type} [Fintype X] [DecidableEq X]

def normalized (o : X) (t : Tab X) : Tab X := fun x => t x + t o
def vanishes (o : X) (W : Space X) := ∀ t ∈ W, t o=0

theorem ambient_card (o : X) (W : Space X) (hW : vanishes o W) :
    W.card ≤ 2^(Fintype.card X - 1) := by
  classical
  let f := fun (t : Tab X) (x : {x : X // x ≠ o}) => t x.val
  have inj : Set.InjOn f W := by
    intro u hu v hv eq
    funext x
    by_cases hx : x=o
    · subst x; rw [hW _ hu,hW _ hv]
    · exact congrFun eq ⟨x,hx⟩
  have off : Fintype.card {x : X // x≠o} = Fintype.card X - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : X => x=o)
  calc
    W.card = (W.image f).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ _ := (W.image f).card_le_univ
    _ = _ := by simp [Fintype.card_fun,off]

def leaves (W : Space X) : Nat → Finset (Space X)
  | 0 => {W}
  | i+1 => (leaves W i).biUnion children

theorem leaf_next {W V U : Space X} {i} (hV : V ∈ leaves W i)
    (hU : U ∈ children V) : U ∈ leaves W (i+1) :=
  Finset.mem_biUnion.mpr ⟨V,hV,hU⟩

theorem leaves_mono (W : Space X) {i j} (h : i ≤ j) : leaves W i ⊆ leaves W j := by
  induction h with
  | refl => exact fun _ hx => hx
  | step _ ih => exact fun _ hx => leaf_next (ih hx) (Finset.mem_insert_self ..)

theorem leaves_property {W : Space X} {P : Nat → Space X → Prop} (h0 : P 0 W)
    (hstep : ∀ i V, P i V → ∀ U ∈ children V, P (i+1) U) :
    ∀ i, ∀ V ∈ leaves W i, P i V := by
  intro i; induction i with
  | zero => simpa [leaves] using h0
  | succ i ih =>
    intro V hV
    obtain ⟨U,hU,h⟩ := Finset.mem_biUnion.mp hV
    exact hstep i U (ih _ hU) V h

theorem child_cases {W V : Space X} (h : V ∈ children W) :
    V=W ∨ ∃ u ∈ W, ∃ v ∈ W, V=extend W (u*v) := by
  rcases Finset.mem_insert.mp h with he | hm
  · exact .inl he
  · obtain ⟨⟨u,v⟩,hp,rfl⟩ := Finset.mem_image.mp hm
    have p := Finset.mem_offDiag.mp hp
    exact .inr ⟨u,Finset.mem_of_mem_erase p.1,v,Finset.mem_of_mem_erase p.2.1,rfl⟩

theorem leaf_closed {W : Space X} (hc : Closed W) {i V} (hV : V ∈ leaves W i) : Closed V := by
  apply leaves_property (P:=fun _ T => Closed T) hc _ i V hV
  intro _ U hu T ht
  rcases child_cases ht with rfl | ⟨u,_,v,_,rfl⟩
  · exact hu
  · exact extend_closed hu _

theorem leaf_norm (o : X) {W : Space X} (hc : vanishes o W) {i V} (hV : V ∈ leaves W i) :
    vanishes o V := by
  apply leaves_property (P:=fun _ T => vanishes o T) hc _ i V hV
  intro _ U hu T ht
  rcases child_cases ht with rfl | ⟨u,uu,v,uv,rfl⟩
  · exact hu
  · intro t h
    rcases (mem_extend ..).mp h with hin | ⟨w,hw,rfl⟩
    · exact hu _ hin
    · simp [Pi.add_apply,Pi.mul_apply,hu _ hw,hu _ uu,hu _ uv]

theorem extend_card (W : Space X) (z : Tab X) : (extend W z).card ≤ 2*W.card := by
  have h := Finset.card_union_le W (W.image fun t => t + z)
  have k := Finset.card_image_le (s:=W) (f:=fun t => t+z)
  change (W ∪ _).card ≤ _
  omega

theorem leaf_grow {W : Space X} {d} (hw : W.card ≤ 2^d) {i V} (hV : V ∈ leaves W i) :
    V.card ≤ 2^(d+i) := by
  apply leaves_property (P:=fun k U => U.card ≤ 2^(d+k)) (by simpa using hw) _ i V hV
  intro k U h T ht
  rw [← Nat.add_assoc,pow_succ]
  rcases child_cases ht with rfl | ⟨u,_,v,_,rfl⟩
  · omega
  · have := extend_card U (u*v); omega

theorem leaf_count {W : Space X} (o : X) {d} (hc : Closed W) (hn : vanishes o W)
    (hw : W.card ≤ 2^d) (i : Nat) :
    (leaves W i).card ≤ ∏ j ∈ Finset.range i, (1+planes (min (Fintype.card X-1) (d+j))) := by
  induction i with
  | zero => simp [leaves]
  | succ i ih =>
    rw [Finset.prod_range_succ]
    calc
      (leaves W (i+1)).card ≤ ∑ U ∈ leaves W i, (children U).card := Finset.card_biUnion_le
      _ ≤ ∑ _U ∈ leaves W i, (1+planes (min (Fintype.card X-1) (d+i))) := by
        apply Finset.sum_le_sum
        intro U h
        have h1 := ambient_card o U (leaf_norm o hn h)
        have h2 := leaf_grow hw h
        have p : U.card ≤ 2 ^ min (Fintype.card X-1) (d+i) := by
          rcases le_total (Fintype.card X-1) (d+i) with hle|hle
          · simpa [min_eq_left hle] using h1
          · simpa [min_eq_right hle] using h2
        apply (child_count (leaf_closed hc h)).trans
        exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul (Nat.sub_le_sub_right p 1) (Nat.sub_le_sub_right p 2))) _
      _ = _ := by simp [smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ ih

theorem leaf_image {Y : Type} [DecidableEq Y] [Add Y]
    (f : Tab X → Y) (add : ∀ u v, f (u+v)=f u+f v)
    {W : Space X} (hw : (W.image f).card ≤ 1) {i V} (hV : V ∈ leaves W i) :
    (V.image f).card ≤ 2^i := by
  apply leaves_property (P:=fun k U => (U.image f).card ≤ 2^k) (by simpa using hw) _ i V hV
  intro k U h T ht
  rw [pow_succ]
  rcases child_cases ht with rfl | ⟨u,_,v,_,rfl⟩
  · omega
  · let S := U.image f
    have hsub : (extend U (u*v)).image f ⊆ S ∪ S.image (fun t => t + f (u*v)) := by
      intro y hy
      obtain ⟨t,hmem,rfl⟩ := Finset.mem_image.mp hy
      rcases (mem_extend ..).mp hmem with hm | ⟨w,hw,rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f w,Finset.mem_image_of_mem _ hw,(add ..).symm⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
    have hsize : (S.image (fun t => t + f (u*v))).card ≤ S.card := Finset.card_image_le
    change S.card ≤ _ at h
    omega

end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

abbrev Grid (n m : Nat) := Fin n × Fin m
abbrev Off {n} (a : Fin n) := {x : Fin n // x ≠ a}
abbrev F := ZMod 2

def liftOff {n} (a : Fin n) (r : Off a → F) (x : Fin n) : F :=
  if hx : x=a then 0 else r ⟨x,hx⟩

def baseMap {n m} (a : Fin n) (b : Fin m)
    (rc : (Off a → F) × (Off b → F)) : Tab (Grid n m) :=
  fun p => liftOff a rc.1 p.1 + liftOff b rc.2 p.2

def base {n m} (a : Fin n) (b : Fin m) : Space (Grid n m) :=
  Finset.univ.image (baseMap a b)

theorem base_closed {n m} (a : Fin n) (b : Fin m) : Closed (base a b) := by
  constructor
  · exact Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,by
      funext p; simp only [baseMap,liftOff]; split_ifs <;> rfl⟩
  intro u hu v hv
  obtain ⟨⟨r,c⟩,_,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨⟨r',c'⟩,_,rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨(r+r',c+c'),Finset.mem_univ _,?_⟩
  funext p
  simp only [baseMap,liftOff,Pi.add_apply]; split_ifs <;> abel

theorem base_norm {n m} (a : Fin n) (b : Fin m) : vanishes (a,b) (base a b) := by
  intro t ht
  obtain ⟨rc,_,rfl⟩ := Finset.mem_image.mp ht
  simp [baseMap,liftOff]

theorem base_card {n m} (a : Fin n) (b : Fin m) : (base a b).card ≤ 2^(n+m-2) := by
  have off {k} (v : Fin k) : Fintype.card (Off v) = k-1 := by
    simpa [Off] using Fintype.card_subtype_compl (fun x : Fin k => x=v)
  have e : n+m-2 = (n-1)+(m-1) := by have := a.isLt; have := b.isLt; omega
  calc
    (base a b).card ≤ _ := Finset.card_image_le
    _ = _ := by simp [Fintype.card_fun,off,e,pow_add,F]

def delta {n m} (a : Fin n) (b : Fin m) (t : Tab (Grid n m)) : Tab (Grid n m) :=
  fun p => (t p + t (p.1,b)) + (t (a,p.2)+t (a,b))

theorem delta_add {n m} (a : Fin n) (b : Fin m) (u v : Tab (Grid n m)) :
    delta a b (u+v) = delta a b u + delta a b v := by
  funext p; simp only [delta,Pi.add_apply]; abel

theorem delta_normal {n m} (a : Fin n) (b : Fin m) (u : Tab (Grid n m)) :
    delta a b (normalized (a,b) u) = delta a b u := by
  funext p
  simp only [delta,normalized,CharTwo.add_self_eq_zero]
  calc
    _ = ((u p + u (p.1,b)) + (u (a,p.2) + u (a,b))) + (u (a,b) + u (a,b)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

theorem delta_base {n m} (a : Fin n) (b : Fin m) :
    ((base a b).image (delta a b)).card ≤ 1 := by
  apply (Finset.card_le_card (t:={0}) ?_).trans_eq (Finset.card_singleton _)
  intro y hy
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨rc,_,rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_singleton.mpr
  funext p
  simp only [delta,baseMap,liftOff, ↓reduceDIte, add_zero,zero_add,Pi.zero_apply]
  split_ifs <;> simp_all [CharTwo.add_self_eq_zero, add_assoc, add_left_comm, add_comm]

theorem normalized_separable {n m} (a : Fin n) (b : Fin m) (r : Fin n → F) (c : Fin m → F) :
    normalized (a,b) (fun p : Grid n m => r p.1+c p.2) ∈ base a b := by
  let rr := fun x : Off a => r x.val + r a
  let cc := fun y : Off b => c y.val + c b
  refine Finset.mem_image.mpr ⟨(rr,cc),Finset.mem_univ _,?_⟩
  funext p
  have e {k} (v x : Fin k) (h : Fin k → F) :
      liftOff v (fun u => h u.val+h v) x = h x+h v := by
    by_cases hx : x=v
    · subst x; simp [liftOff,CharTwo.add_self_eq_zero]
    · simp [liftOff,hx]
  simp only [baseMap,rr,cc,e,normalized]
  abel

end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

def bit (p : Bool) : ZMod 2 := if p then 1 else 0
def parity (f : Bool → Bool → Bool) := xor (xor (f false false) (f false true)) (xor (f true false) (f true true))
def truth (a b c d x y : Bool) : Bool := if x then (if y then d else c) else (if y then b else a)

theorem bit_inj {p q} (h : bit p = bit q) : p=q := by
  revert p q; decide

theorem bit_xor (p q) : bit (xor p q) = bit p + bit q := by
  cases p <;> cases q <;> decide

theorem bool_expansion (f : Bool → Bool → Bool) (p q x y : Bool) :
    bit (f x y) + bit (f p q) =
    bit (xor (f (!p) q) (f p q)) * (bit x+bit p) +
    bit (xor (f p (!q)) (f p q)) * (bit y+bit q) +
    bit (parity f) * ((bit x+bit p)*(bit y+bit q)) := by
  have tab : ∀ a b c d p q x y : Bool,
      let g := truth a b c d
      bit (g x y) + bit (g p q) =
        bit (xor (g (!p) q) (g p q)) * (bit x+bit p) +
        bit (xor (g p (!q)) (g p q)) * (bit y+bit q) +
        bit (parity g) * ((bit x+bit p)*(bit y+bit q)) := by decide +kernel
  have eq : f = truth (f false false) (f false true) (f true false) (f true true) := by
    funext i j; cases i <;> cases j <;> rfl
  simpa only [← eq] using tab (f false false) (f false true) (f true false) (f true true) p q x y

def nonlin (g : PEqualNP.CircuitLowerBounds.Gate) :=
  (g.inputs.length == 2) && parity (fun x y => g.op.eval [x,y])

end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

open PEqualNP.CircuitLowerBounds

variable {X : Type} [Fintype X] [DecidableEq X]

def normBit (o : X) (f : X → Bool) := normalized o (fun x => bit (f x))
def scaleBit (p : Bool) (u : Tab X) : Tab X := fun x => bit p * u x

theorem scale_false (u : Tab X) : scaleBit false u = 0 := by
  funext x; simp [scaleBit,bit]

theorem scale_true (u : Tab X) : scaleBit true u = u := by
  funext x; simp [scaleBit,bit]

theorem keepScale {W : Space X} (hw : Closed W) (c : Bool) {u : Tab X} (h : u∈W) :
    scaleBit c u ∈ W := by
  cases c
  · rw [scale_false]; exact hw.1
  · rw [scale_true]; exact h

theorem gate2 {W : Space X} (o : X) (hw : Closed W) (f : Bool → Bool → Bool) (u v : X → Bool)
    (hu : normBit o u ∈ W) (hv : normBit o v ∈ W) :
    ∃ V : Space X, (if parity f then V ∈ children W else V=W) ∧ W ⊆ V ∧ Closed V ∧
      normBit o (fun x => f (u x) (v x)) ∈ V := by
  let a := normBit o u
  let b := normBit o v
  let V := if parity f then extend W (a*b) else W
  have sub : W ⊆ V := by
    dsimp [V]; split
    · exact Finset.subset_union_left
    · exact Finset.Subset.refl _
  have hc : Closed V := by dsimp [V]; split; exact extend_closed hw _; exact hw
  refine ⟨V,?_,sub,hc,?_⟩
  · cases h : parity f
    · simp [V,h]
    · simpa [V,h] using child_of_mem hw hu hv
  let cx := xor (f (!(u o)) (v o)) (f (u o) (v o))
  let cy := xor (f (u o) (!(v o))) (f (u o) (v o))
  have rep : normBit o (fun x => f (u x) (v x)) =
      scaleBit cx a + scaleBit cy b + scaleBit (parity f) (a*b) := by
    funext x
    exact bool_expansion f (u o) (v o) (u x) (v x)
  rw [rep]
  apply hc.2 _ (hc.2 _ (keepScale hc cx (sub hu)) _ (keepScale hc cy (sub hv))) _
  cases h : parity f
  · rw [scale_false]; exact hc.1
  · have hmem : a*b ∈ extend W (a*b) :=
      (mem_extend ..).mpr (.inr ⟨0,hw.1,zero_add _⟩)
    rw [scale_true]; simpa [V,h] using hmem

def readWire (E : X → List Bool) (k : Nat) : X → Bool := fun x => (E x).getD k false
def outputGate (E : X → List Bool) (g : Gate) : X → Bool :=
  fun x => g.op.eval (g.inputs.map fun k => (E x).getD k false)

theorem oneGate {W : Space X} (o : X) (hw : Closed W) (g : Gate) (E : X → List Bool)
    (bound : g.inputs.length ≤ 2) (ok : ∀ k, normBit o (readWire E k) ∈ W) :
    ∃ V : Space X, (if nonlin g then V ∈ children W else V=W) ∧ W ⊆ V ∧ Closed V ∧
      normBit o (outputGate E g) ∈ V := by
  match h : g.inputs with
  | [] =>
    refine ⟨W,by simp [nonlin,h],fun _ hx => hx,hw,?_⟩
    have e : normBit o (outputGate E g) = 0 := by
      funext x; simp [normBit,normalized,outputGate,h,CharTwo.add_self_eq_zero]
    exact e ▸ hw.1
  | [a] =>
    let f := fun (x _y : Bool) => g.op.eval [x]
    have eq : parity f=false := by simp [f,parity]
    obtain ⟨V,hV,sub,hc,hn⟩ := gate2 o hw f (readWire E a) (readWire E a) (ok a) (ok a)
    have same : V=W := by simpa [eq] using hV
    subst V
    have val : outputGate E g = fun x => f (readWire E a x) (readWire E a x) := by
      funext x; simp [outputGate,h,readWire,f]
    exact ⟨W,by simp [nonlin,h],sub,hc,by rw [val]; exact hn⟩
  | [a,b] =>
    have val : outputGate E g = fun x => g.op.eval [readWire E a x,readWire E b x] := by
      funext x; simp [outputGate,h,readWire]
    rw [val]
    simpa only [nonlin,h,List.length_cons,List.length_nil,beq_self_eq_true,Bool.true_and] using
      gate2 o hw (fun x y => g.op.eval [x,y]) (readWire E a) (readWire E b) (ok a) (ok b)
  | a::b::c::l => simp [h] at bound

def runGates (gs : List Gate) (E : X → List Bool) (x : X) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) (E x)

theorem run_length (gs : List Gate) (E : X → List Bool) (x : X) :
    (runGates gs E x).length = (E x).length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runGates]
  | append_singleton gs g ih =>
    simp only [runGates,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,
      List.length_singleton]
    change (runGates gs E x).length+1 = _
    rw [ih,Nat.add_assoc]

theorem simulate {W : Space X} (o : X) (hw : Closed W) (gs : List Gate)
    (E : X → List Bool) (len : Nat) (he : ∀ x, (E x).length=len)
    (bound : ∀ g∈gs, g.inputs.length≤2) (ok : ∀ k, normBit o (readWire E k) ∈ W) :
    ∃ V ∈ leaves W (gs.countP nonlin), ∀ k, normBit o (readWire (runGates gs E) k) ∈ V := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨W,Finset.mem_singleton_self _,ok⟩
  | append_singleton gs g ih =>
    obtain ⟨U,hU,prev⟩ := ih (fun g hg => bound g (by simp [hg]))
    let D := runGates gs E
    have size (x) : (D x).length = len+gs.length := by
      rw [show D x = runGates gs E x from rfl,run_length,he]
    obtain ⟨V,vstep,sub,hV,added⟩ :=
      oneGate o (leaf_closed hw hU) g D (bound g (by simp)) prev
    have reach : V∈leaves W ((gs++[g]).countP nonlin) := by
      cases h : nonlin g
      · have eq : V=U := by simpa [h] using vstep
        simpa [List.countP_append,h,eq] using hU
      · have mem : V∈children U := by simpa [h] using vstep
        simpa [List.countP_append,h] using leaf_next hU mem
    refine ⟨V,reach,?_⟩
    intro k
    by_cases hk : k=len+gs.length
    · subst k
      have eq : readWire (runGates (gs++[g]) E) (len+gs.length) = outputGate D g := by
        funext x
        change (runGates (gs++[g]) E x).getD _ false = _
        have step : runGates (gs++[g]) E x = D x ++ [outputGate D g x] := by
          simp [runGates,D,outputGate,List.foldl_append]
        rw [step,← size x]
        simp
      simpa only [eq] using added
    · have eq : readWire (runGates (gs++[g]) E) k = readWire D k := by
        funext x
        change (runGates (gs++[g]) E x).getD _ false = _
        have step : runGates (gs++[g]) E x = D x ++ [outputGate D g x] := by
          simp [runGates,D,outputGate,List.foldl_append]
        rw [step]
        change (D x ++ [_]).getD k false = (D x).getD k false
        by_cases hlt : k < (D x).length
        · exact List.getD_append _ _ _ _ hlt
        · have hgt : (D x).length < k := by rw [size] at hlt ⊢; omega
          rw [List.getD_eq_default, List.getD_eq_default] <;> simp_all <;> omega
      simpa only [eq] using sub (prev k)

end PEqualNP.Outside.L_meta_32042

namespace PEqualNP.Outside.L_meta_32042

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def inputGrid {n m} (p : Grid n m) := oneEach p.1 p.2

theorem inputs_base {n m} (a : Fin n) (b : Fin m) (k : Nat) :
    normBit (a,b) (readWire inputGrid k) ∈ base a b := by
  by_cases hk : k<n
  · let r := fun x : Fin n => bit (decide (k=x.val))
    have e : (fun p : Grid n m => bit (readWire inputGrid k p)) = fun p => r p.1 + 0 := by
      funext p
      simp only [readWire,inputGrid,oneEach,add_zero,r]
      rw [List.getD_append _ _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_ofFn]
      simp [Fin.ext_iff]
    simpa only [normBit,e] using normalized_separable a b r (fun _ => 0)
  by_cases hm : k<n+m
  · let c := fun y : Fin m => bit (decide (k-n=y.val))
    have e : (fun p : Grid n m => bit (readWire inputGrid k p)) = fun p => 0 + c p.2 := by
      funext p
      simp only [readWire,inputGrid,oneEach,zero_add,c]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_ofFn]
      simp [Fin.ext_iff]
    simpa only [normBit,e] using normalized_separable a b (fun _ => 0) c
  · have e : normBit (a,b) (readWire (X:=Grid n m) inputGrid k) = 0 := by
      funext p
      have out (t : Grid n m) : readWire inputGrid k t=false := by
        apply List.getD_eq_default
        simp [inputGrid,oneEach]; omega
      simp [normBit,normalized,out,bit]
    rw [e]; exact (base_closed a b).1

def outputs {n m} (a : Fin n) (b : Fin m) (q : Nat) (V : Space (Grid n m)) :
    Finset (Family n m q) :=
  Finset.univ.image (fun (u : Fin q → ↥(V.image (delta a b))) (i : Fin q) (x : Fin n) (y : Fin m) =>
    decide ((u i).val (x,y) = 1))

theorem outputs_count {n m q s} (a : Fin n) (b : Fin m) {V}
    (hv : V ∈ leaves (base a b) s) :
    (outputs a b q V).card ≤ 2^(q*s) := by
  have h := leaf_image (delta a b) (delta_add a b) (delta_base a b) hv
  calc
    _ ≤ _ := Finset.card_image_le
    _ = ((V.image (delta a b)).card)^q := by
      simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin]
    _ ≤ (2^s)^q := Nat.pow_le_pow_left h q
    _ = _ := by rw [← pow_mul,Nat.mul_comm]

theorem circuit_leaf {n m q s} (a : Fin n) (b : Fin m) (T : Family n m q)
    (C : Circuit) (tap : Fin q → Nat)
    (fanin : ∀ g∈C.gates, g.inputs.length≤2) (budget : C.gates.countP nonlin ≤ s)
    (rep : ∀ i, Represents (T i) ⟨C.gates,tap i⟩) :
    ∃ V ∈ leaves (base a b) s, anchor a b T ∈ outputs a b q V := by
  obtain ⟨V,live,members⟩ := simulate (a,b) (base_closed a b) C.gates inputGrid (n+m)
    (fun p => by simp [inputGrid,oneEach]) fanin (inputs_base a b)
  refine ⟨V,leaves_mono _ budget live,?_⟩
  let t := fun (i : Fin q) (p : Grid n m) => bit (T i p.1 p.2)
  have inV (i) : normalized (a,b) (t i) ∈ V := by
    have eq : readWire (runGates C.gates inputGrid) (tap i) = fun p : Grid n m => T i p.1 p.2 := by
      funext p; exact rep i p.1 p.2
    simpa only [normBit,eq,t] using members (tap i)
  have im (i) : delta a b (t i) ∈ V.image (delta a b) := by
    rw [← delta_normal a b (t i)]
    exact Finset.mem_image_of_mem _ (inV i)
  refine Finset.mem_image.mpr ⟨fun i => ⟨delta a b (t i),im i⟩,Finset.mem_univ _,?_⟩
  funext i x y
  have hbit : ∀ z : Bool, decide (bit z=1)=z := by decide
  have h : delta a b (t i) (x,y)=bit (anchor a b T i x y) := by
    simp only [delta,t,anchor,bit_xor]
  simpa only [h] using hbit (anchor a b T i x y)

theorem count_fits {n m q s} (a : Fin n) (b : Fin m) (H : Finset (Family n m q))
    (fit : ∀ T∈H, ∃ (C : Circuit) (tap : Fin q → Nat), (∀ g∈C.gates,g.inputs.length≤2) ∧
      C.gates.countP nonlin ≤ s ∧ ∀ i, Represents (T i) ⟨C.gates,tap i⟩) :
    (H.image (anchor a b)).card ≤ 2^(q * min s ((n-1)*(m-1))) *
      ∏ i ∈ Finset.range s, (1 + planes (min (n*m-1) (n+m-2+i))) := by
  rcases le_total ((n-1)*(m-1)) s with hi|lo
  · exact large_budget a b H hi
  rw [min_eq_left lo]
  let L := leaves (base a b) s
  have inc : H.image (anchor a b) ⊆ L.biUnion (outputs a b q) := by
    intro y hy
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨C,tap,fan,h,rep⟩ := fit _ hT
    exact Finset.mem_biUnion.mpr (circuit_leaf a b T C tap fan h rep)
  have hl := leaf_count (a,b) (base_closed a b) (base_norm a b) (base_card a b) s
  simp only [Fintype.card_prod,Fintype.card_fin] at hl
  calc
    _ ≤ _ := (Finset.card_le_card inc).trans Finset.card_biUnion_le
    _ ≤ ∑ _V ∈ L, 2^(q*s) := Finset.sum_le_sum fun V hV => outputs_count a b hV
    _ = 2^(q*s)*L.card := by simp [smul_eq_mul,Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ hl

end PEqualNP.Outside.L_meta_32042

theorem PEqualNP.Outside.L_meta_32042 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  ∀ (n m q s : ℕ) (a : Fin n) (b : Fin m),
    let Family := Fin q → Fin n → Fin m → Bool
    let anchor := fun (T : Family) (i : Fin q) (x : Fin n) (y : Fin m) =>
      xor (xor (T i x y) (T i x b)) (xor (T i a y) (T i a b))
    let fits := fun (T : Family) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ s ∧
        ∀ i, PEqualNP.Represents.Represents (T i) ⟨C.gates, tap i⟩
    let planes := fun (d : ℕ) => ((2^d-1)*(2^d-2))/6
    ∀ H : Finset Family, (∀ T ∈ H, fits T) →
      (H.image anchor).card ≤ 2^(q * min s ((n-1)*(m-1))) *
        ∏ i ∈ Finset.range s, (1 + planes (min (n*m-1) (n+m-2+i))) := by
  dsimp only
  intro n m q s a b H fit
  apply PEqualNP.Outside.L_meta_32042.count_fits a b H
  intro T hT
  obtain ⟨C,tap,_,fan,budget,rep⟩ := fit T hT
  exact ⟨C,tap,fan,budget,rep⟩
